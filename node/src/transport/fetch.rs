//! One object being fetched from one peer.
//!
//! A [`Fetch`] is told the time and what arrived, and says what to ask
//! for and when to come back:
//!
//! * [`Fetch::poll`] says what to do now: ask for these chunks, wait
//!   until then, or stop because the object is here or will not be.
//! * [`Fetch::chunk`] takes a chunk that arrived.
//!
//! # What it keeps
//!
//! The object's bytes, a bit for each chunk that has arrived, and the
//! chunks asked for and not yet here, in the order they were asked: the
//! *flight*. The serving side sends in the order it is asked, so the
//! flight is also the order chunks are expected in, and its front is
//! always the chunk waited for longest.
//!
//! # Asks are numbered
//!
//! Each ask has a number, one more than the ask before, and the chunk
//! sent in answer carries it back. So when a chunk has been asked for
//! twice, it is known which ask an arrival answers: every arrival
//! measures a round trip, and every arrival shows that the asks before
//! its own were answered before it, if they were answered at all.
//!
//! # Loss
//!
//! An ask is *overtaken* when an ask numbered after it has been
//! answered. It is taken for lost, leaves the flight and is asked again
//! before anything new, when either
//!
//! * it has been overtaken by [`Path::reorder`] places or more; or
//! * it has been overtaken at all, and nothing has arrived since for
//!   [`Path::grace`]: a small window never holds enough to overtake by
//!   many.
//!
//! When nothing at all arrives for the retry time, that is a *silence*.
//! Nothing is known then of what is in the flight: lost, or only late.
//! So one chunk alone, the one waited for longest, is asked for again,
//! as a probe. If the rest were lost, the probe's answer overtakes them
//! all, and they are asked for again then. If they were only late (a
//! peer sending slowly, a long queue) they arrive before it, and
//! nothing was asked twice but the probe. A second silence running
//! probes with two chunks, a third with four: where most of everything
//! is lost, one chunk asked for is seldom one chunk answered.
//!
//! A chunk that arrives after it was taken for lost is taken all the
//! same, and shows the path to deliver further out of order than was
//! allowed for ([`Path::disordered`]).
//!
//! # Rounds
//!
//! A round is a window's worth of arrivals. If more than one chunk in
//! [`LOSS_TOLERANCE`] was lost in it, the path is told
//! ([`Path::lost`]), and brings the window down if it is full; so too
//! at a silence. Otherwise, if the window had been full of asks, it
//! grows: a window that was never filled has shown nothing about the
//! path.

use std::collections::VecDeque;

use super::path::Path;
use super::wire::{Chunk, Ranges};
use super::{CHUNK_BYTES, LOSS_TOLERANCE, MAX_RETRIES, MAX_RETRY, Micros, REFILL, SECOND, chunk_count};
use crate::error::Error;

/// What to do now.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Poll {
    /// Ask for the chunks put in the ranges, the first of them under
    /// this number ([`super::wire::Get::seq`]), and poll again.
    Ask(u32),
    /// Nothing until a chunk arrives or this time comes.
    Wait(Micros),
    /// Every chunk is here.
    Done,
    /// The object will not come from this peer.
    Failed(Why),
}

/// Why a fetch was given up.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Why {
    /// Nothing arrived, [`MAX_RETRIES`] times over.
    Silent,
    /// The peer said it does not have it.
    Gone,
    /// The peer sent a chunk no honest peer would.
    Bad,
}

/// What became of a chunk given to [`Fetch::chunk`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Taken {
    /// Its bytes were new.
    New,
    /// It was here already, or the fetch is over.
    Spare,
}

/// A chunk asked for.
#[derive(Clone, Copy, Debug)]
struct Asked {
    index: u32,
    at: Micros,
    /// How many chunks were here when it was asked for.
    got: u32,
    /// Still awaited: false once it has arrived, or was found to be
    /// past the object's end.
    flying: bool,
}

/// What a fetch did, for the tests and for whoever watches the network.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Stats {
    /// Chunks asked for, counting each time.
    pub asked: u64,
    /// Of those, asks for a chunk asked for before.
    pub asked_again: u64,
    /// Chunks that arrived and were here already.
    pub spare: u64,
    /// Chunks taken for lost because later ones arrived.
    pub overtaken: u64,
    /// Of those, ones that then turned up.
    pub disorders: u64,
    /// Silences.
    pub silences: u64,
    /// Requests sent.
    pub requests: u64,
}

pub struct Fetch {
    transfer: u64,
    max_len: u32,
    /// Zero until known.
    len: u32,
    /// Chunks of the object; before its length is known, the chunks
    /// that may be asked for blind.
    count: u32,
    buf: Vec<u8>,
    /// A bit a chunk: here.
    have: Vec<u64>,
    /// A bit a chunk: asked for at least once.
    asked: Vec<u64>,
    /// A bit a chunk: taken for lost because it was overtaken, and not
    /// yet seen to have been.
    passed: Vec<u64>,
    got: u32,
    /// For each chunk, the number of its latest ask in the flight and
    /// one; zero if it is not in the flight.
    slot: Vec<u64>,
    flight: VecDeque<Asked>,
    /// The number of the ask at the front of the flight.
    base: u64,
    /// How many in the flight are still awaited.
    flying: u32,
    /// The greatest number of an ask that has been answered, and one.
    highest: u64,
    /// Chunks taken for lost, to ask again, the first lost first.
    lost: VecDeque<u32>,
    /// The first chunk never asked for.
    fresh: u32,
    /// A silence has passed, and this many chunks are still to be
    /// asked for as its probe.
    probe: u32,
    path: Path,
    // This round.
    delivered: u32,
    losses: u32,
    filled: bool,
    cut: bool,
    disordered: bool,
    // Silence.
    last_progress: Micros,
    last_request: Micros,
    /// When a chunk last arrived, new or not.
    last_arrival: Micros,
    /// Silences since anything new arrived.
    retries: u32,
    /// Silences since an ask was answered: the retry time is doubled
    /// this many times.
    backoff: u32,
    started: Micros,
    /// Chunks here when this peer was first asked.
    got_before: u32,
    over: Option<Poll>,
    stats: Stats,
}

impl Fetch {
    /// A fetch numbered `transfer` (a number nobody else can guess) of
    /// an object of `len` bytes if that is known, and `max_len` at most
    /// in any case, over a path of which `path` has been learned.
    ///
    /// A known length that is zero or over `max_len` is no length: the
    /// fetch is of nothing, and [`Fetch::poll`] says so.
    pub fn new(transfer: u64, len: Option<u32>, max_len: u32, path: Path, now: Micros) -> Fetch {
        let mut f = Fetch {
            transfer,
            max_len,
            len: 0,
            count: 0,
            buf: Vec::new(),
            have: Vec::new(),
            asked: Vec::new(),
            passed: Vec::new(),
            got: 0,
            slot: Vec::new(),
            // (Room as it is needed: a fetch begun at a stranger's word
            // holds nothing before anything of it arrives.)
            flight: VecDeque::new(),
            base: 0,
            flying: 0,
            highest: 0,
            lost: VecDeque::new(),
            fresh: 0,
            probe: 0,
            path,
            delivered: 0,
            losses: 0,
            filled: false,
            cut: false,
            disordered: false,
            last_progress: now,
            last_request: now,
            last_arrival: now,
            retries: 0,
            backoff: 0,
            started: now,
            got_before: 0,
            over: None,
            stats: Stats::default(),
        };
        match len {
            Some(l) if l == 0 || l > max_len => f.over = Some(Poll::Failed(Why::Bad)),
            Some(l) => f.learn(l),
            // Blind: the first window's worth, of which the peer sends
            // those there are.
            None => {
                f.count = chunk_count(max_len).min(f.path.window());
                f.size(f.count);
            }
        }
        f
    }

    pub fn transfer(&self) -> u64 {
        self.transfer
    }

    /// What has been learned of the path, for the next fetch from this
    /// peer.
    pub fn path(&self) -> Path {
        self.path
    }

    pub fn stats(&self) -> Stats {
        self.stats
    }

    /// The object's length, once known.
    pub fn length(&self) -> Option<u32> {
        (self.len != 0).then_some(self.len)
    }

    /// Chunks here, and chunks in all (once the length is known).
    pub fn progress(&self) -> (u32, Option<u32>) {
        (self.got, (self.len != 0).then_some(self.count))
    }

    /// Chunks asked for and awaited.
    pub fn in_flight(&self) -> u32 {
        self.flying
    }

    /// The object, once [`Poll::Done`].
    pub fn finish(self) -> Option<Vec<u8>> {
        (self.over == Some(Poll::Done)).then_some(self.buf)
    }

    /// Bytes a second from this peer so far, counting from when it was
    /// first asked: for whoever decides whether another would do
    /// better.
    pub fn rate(&self, now: Micros) -> u64 {
        let bytes = (self.got - self.got_before) as u64 * CHUNK_BYTES as u64;
        bytes * SECOND / now.saturating_sub(self.started).max(1)
    }

    /// How long it is since anything new of the object arrived (or,
    /// if nothing has, since the peer was first asked).
    pub fn quiet(&self, now: Micros) -> Micros {
        now.saturating_sub(self.last_progress)
    }

    /// How much of the object is here, in chunks, and of how many (the
    /// second nothing while the length is not known).
    pub fn here(&self) -> (u32, u32) {
        (self.got, if self.len == 0 { 0 } else { self.count })
    }

    /// How long ago the peer was first asked.
    pub fn age(&self, now: Micros) -> Micros {
        now.saturating_sub(self.started)
    }

    /// Takes up a fetch that is not finished, keeping what has arrived:
    /// with the same peer after it was given up for silence, or with
    /// another (whose `path` this is), under a new number. Chunks sent
    /// under the old number are no longer taken.
    ///
    /// Not after a peer was found to lie ([`Why::Bad`]): what it sent
    /// may be anything, and the fetch is to be started afresh. Nothing
    /// is changed then, nor once the object is here.
    pub fn resume(&mut self, transfer: u64, path: Path, now: Micros) {
        if matches!(self.over, Some(Poll::Done | Poll::Failed(Why::Bad))) {
            return;
        }
        self.transfer = transfer;
        self.path = path;
        self.over = None;
        // Asks go on being numbered from where they were.
        self.base += self.flight.len() as u64;
        self.highest = 0;
        self.flight.clear();
        self.lost.clear();
        self.flying = 0;
        self.fresh = 0;
        self.probe = 0;
        for words in [&mut self.asked, &mut self.passed] {
            words.fill(0);
        }
        self.slot.fill(0);
        if self.len == 0 {
            // Still blind: this path's first window.
            self.count = chunk_count(self.max_len).min(self.path.window());
            self.size(self.count);
        }
        (self.delivered, self.losses, self.filled, self.cut, self.disordered) = (0, 0, false, false, false);
        (self.last_progress, self.last_request, self.last_arrival, self.started) = (now, now, now, now);
        (self.retries, self.backoff) = (0, 0);
        self.got_before = self.got;
    }

    /// The peer does not have the object.
    pub fn gone(&mut self) {
        if self.over.is_none() {
            self.over = Some(Poll::Failed(Why::Gone));
        }
    }

    fn size(&mut self, count: u32) {
        let words = (count as usize).div_ceil(64);
        self.have.resize(words, 0);
        self.asked.resize(words, 0);
        self.passed.resize(words, 0);
        self.slot.resize(count as usize, 0);
    }

    /// The length is `len`: room for it, and for a bit a chunk.
    fn learn(&mut self, len: u32) {
        self.len = len;
        self.count = chunk_count(len);
        self.buf = vec![0; len as usize];
        self.size(self.count);
        // What was asked for blind past the end is not coming, and was
        // not lost.
        for a in self.flight.iter_mut().filter(|a| a.flying && a.index >= self.count) {
            a.flying = false;
            self.flying -= 1;
        }
        self.fresh = self.fresh.min(self.count);
        let count = self.count;
        self.lost.retain(|&i| i < count);
    }

    fn has(&self, i: u32) -> bool {
        self.have[i as usize / 64] >> (i % 64) & 1 == 1
    }

    /// The time after which silence is a loss, from the later of the
    /// last arrival and the last request.
    fn silence(&self) -> Micros {
        let wait = (self.path.retry() << self.backoff.min(10)).min(MAX_RETRY);
        self.last_progress.max(self.last_request) + wait
    }

    /// Ends a round: the window is brought down if too much was lost
    /// and the path is full, and grows if nothing much was lost while
    /// it was full of asks.
    fn end_round(&mut self) {
        self.path.round();
        let sent = self.delivered + self.losses;
        if self.losses * LOSS_TOLERANCE > sent {
            self.bring_down();
        } else if self.filled && !self.cut {
            self.path.grow();
        }
        if !self.disordered {
            self.path.ordered();
        }
        self.disordered = false;
        self.cut = false;
        self.delivered = 0;
        self.losses = 0;
        self.filled = self.flying >= self.path.window();
    }

    /// Chunks were lost: the path decides whether the window comes
    /// down ([`Path::lost`]), once a round.
    fn bring_down(&mut self) {
        if !self.cut {
            self.cut = true;
            self.path.lost(self.filled);
        }
    }

    /// Whether the chunk waited for longest has been overtaken: an ask
    /// after its own has been answered.
    fn overtaken(&self) -> bool {
        self.flying > 0 && self.highest > self.base + 1
    }

    /// Takes the front of the flight, which is awaited, out of it: to
    /// be asked for again first of all (`first`) or after the others
    /// waiting to be.
    fn lose_front(&mut self, first: bool) {
        let a = self.flight.pop_front().expect("a chunk awaited");
        self.base += 1;
        self.slot[a.index as usize] = 0;
        if first {
            self.lost.push_front(a.index);
        } else {
            self.lost.push_back(a.index);
        }
        self.flying -= 1;
        self.trim();
    }

    /// Takes the front of the flight for lost, having been overtaken.
    fn overtake_front(&mut self) {
        let i = self.flight.front().expect("a chunk awaited").index;
        self.passed[i as usize / 64] |= 1 << (i % 64);
        self.losses += 1;
        self.stats.overtaken += 1;
        self.lose_front(false);
    }

    /// Drops from the front of the flight what is no longer awaited.
    fn trim(&mut self) {
        while self.flight.front().is_some_and(|a| !a.flying) {
            self.flight.pop_front();
            self.base += 1;
        }
    }

    /// What to do at `now`. On [`Poll::Ask`], `ranges` (cleared first)
    /// holds the chunks to ask for in one request; poll again at once,
    /// for there may be more than one request's worth.
    pub fn poll(&mut self, now: Micros, ranges: &mut Ranges) -> Poll {
        ranges.clear();
        if let Some(over) = self.over {
            return over;
        }
        // Overtaken, and nothing since for long enough: lost, though not
        // overtaken by many.
        if self.overtaken() && now >= self.last_arrival + self.path.grace() {
            while self.overtaken() {
                self.overtake_front();
            }
        }
        // Silence: the chunk waited for longest is asked for again, and
        // what comes of that tells of the rest.
        if self.flying > 0 && now >= self.silence() {
            self.retries += 1;
            self.backoff += 1;
            self.stats.silences += 1;
            if self.retries > MAX_RETRIES {
                return self.fail(Why::Silent);
            }
            if self.len == 0 && self.slot[0] != 0 {
                // While the length is not known, the first chunk is
                // what is wanted before any other: it is the one chunk
                // every object has, and it tells the length. (The rest
                // of what was asked for blind may be past the object's
                // end, and asking for that again brings nothing.)
                let at = (self.slot[0] - 1 - self.base) as usize;
                self.flight[at].flying = false;
                self.slot[0] = 0;
                self.flying -= 1;
                self.trim();
                self.lost.push_front(0);
                self.probe = 1;
            } else {
                // One chunk the first time; twice as many each silence
                // after, while nothing comes: where most of everything
                // is lost, one chunk asked for is seldom one chunk
                // answered.
                let probe = (1u32 << (self.retries - 1).min(6)).min(self.flying);
                let mut front = [0u32; 64];
                for slot in front[..probe as usize].iter_mut() {
                    *slot = self.flight.front().expect("a chunk awaited").index;
                    self.lose_front(true);
                }
                // (Each went to the front of those to ask again, ahead
                // of the one before it: back into the order they were
                // in.)
                for (k, i) in front[..probe as usize].iter().enumerate() {
                    self.lost[k] = *i;
                }
                self.probe = probe;
            }
            self.bring_down();
        }
        // Ask: the lost first, then what was never asked for.
        let window = self.path.window();
        // (The probe is asked for though the window is full of what is
        // still awaited.)
        let room = window.saturating_sub(self.flying).max(self.probe);
        while self.lost.front().is_some_and(|&i| self.has(i) || self.slot[i as usize] != 0) {
            self.lost.pop_front();
        }
        // Past what is here already (after a fetch is taken up again).
        while self.fresh < self.count && self.has(self.fresh) {
            self.fresh += 1;
        }
        let waiting = self.lost.len() as u64 + (self.count - self.fresh) as u64;
        // In batches: when there is room for a batch, or for all there
        // is, or when nothing is awaited at all.
        let batch = REFILL.min(window / 2).max(1);
        let now_is_time = room >= batch || waiting <= room as u64 || self.flying == 0 || self.probe > 0;
        if waiting > 0 && room > 0 && now_is_time {
            let first = self.base + self.flight.len() as u64;
            let mut n = 0;
            while n < room {
                let i = match self.lost.front() {
                    Some(&i) if self.has(i) || self.slot[i as usize] != 0 => {
                        self.lost.pop_front();
                        continue;
                    }
                    Some(&i) => i,
                    None if self.fresh < self.count && self.has(self.fresh) => {
                        self.fresh += 1;
                        continue;
                    }
                    None if self.fresh < self.count => self.fresh,
                    None => break,
                };
                if !ranges.push(i) {
                    break;
                }
                if self.lost.pop_front().is_none() {
                    self.fresh += 1;
                }
                let word = &mut self.asked[i as usize / 64];
                let again = *word >> (i % 64) & 1 == 1;
                *word |= 1 << (i % 64);
                self.slot[i as usize] = self.base + self.flight.len() as u64 + 1;
                self.flight.push_back(Asked { index: i, at: now, got: self.got, flying: true });
                self.flying += 1;
                self.stats.asked += 1;
                self.stats.asked_again += again as u64;
                n += 1;
            }
            if n > 0 {
                if self.flying >= window {
                    self.filled = true;
                }
                self.probe = 0;
                self.last_request = now;
                self.stats.requests += 1;
                return Poll::Ask(first as u32);
            }
        }
        self.probe = 0;
        // Back when silence would be a loss, or when what was overtaken
        // has had long enough.
        let mut back = self.silence();
        if self.overtaken() {
            back = back.min(self.last_arrival + self.path.grace());
        }
        Poll::Wait(back.max(now + 1))
    }

    fn fail(&mut self, why: Why) -> Poll {
        let over = Poll::Failed(why);
        self.over = Some(over);
        over
    }

    /// Takes a chunk that arrived for this fetch.
    ///
    /// An error is a chunk of another fetch's number, which changes
    /// nothing here, or one no honest peer sends (another length than
    /// before, a length over the greatest, an index past the end): then
    /// the fetch is over, and [`Fetch::poll`] says the peer is bad.
    pub fn chunk(&mut self, now: Micros, c: &Chunk<'_>) -> Result<Taken, Error> {
        const BAD: Error = Error::Malformed("chunk");
        if c.transfer != self.transfer {
            return Err(BAD);
        }
        if self.over.is_some() {
            return Ok(Taken::Spare);
        }
        let known = self.len != 0;
        if c.len == 0 || c.len > self.max_len || (known && c.len != self.len) {
            self.fail(Why::Bad);
            return Err(BAD);
        }
        if !known {
            self.learn(c.len);
        }
        // Decoding saw that the index is within the length it carries
        // and the bytes as many as that place has; a chunk built
        // otherwise is refused here.
        let i = c.index;
        let start = i as usize * CHUNK_BYTES;
        if i >= self.count || super::chunk_len(self.len, i) != Some(c.data.len()) {
            self.fail(Why::Bad);
            return Err(BAD);
        }
        self.last_arrival = now;
        // The ask it answers, if that is still in the flight: the one
        // of its number, for this chunk. (A number that is no ask's, or
        // another chunk's, answers nothing; its bytes are the chunk's
        // all the same.)
        let place = c.seq.wrapping_sub(self.base as u32) as usize;
        let answered = match self.flight.get_mut(place) {
            Some(a) if a.index == i && a.flying => {
                a.flying = false;
                Some((self.base + place as u64 + 1, *a))
            }
            _ => None,
        };
        if let Some((s, a)) = answered {
            self.flying -= 1;
            if self.slot[i as usize] == s {
                self.slot[i as usize] = 0;
            }
            // A round trip, and how many arrived while it was on its
            // way (itself among them, if it is new): the path held them
            // all at once. And every ask before its own has been
            // overtaken.
            self.path.sample(now.saturating_sub(a.at));
            self.path.carry(self.got + !self.has(i) as u32 - a.got);
            self.backoff = 0;
            self.highest = self.highest.max(s);
        }
        // The chunk is here, whichever ask brought it: a later ask for
        // it still in the flight is awaited no longer.
        if let s @ 1.. = self.slot[i as usize] {
            self.slot[i as usize] = 0;
            self.flight[(s - 1 - self.base) as usize].flying = false;
            self.flying -= 1;
        }
        // Taken for lost, and here it is: by an ask given up on, or for
        // the second time. It had only been overtaken.
        let bit = 1u64 << (i % 64);
        if self.passed[i as usize / 64] & bit != 0 && (answered.is_none() || self.has(i)) {
            self.passed[i as usize / 64] &= !bit;
            self.path.disordered();
            self.disordered = true;
            self.stats.disorders += 1;
        }
        let taken = if self.has(i) {
            self.stats.spare += 1;
            Taken::Spare
        } else {
            self.buf[start..start + c.data.len()].copy_from_slice(c.data);
            self.have[i as usize / 64] |= bit;
            self.got += 1;
            self.last_progress = now;
            self.retries = 0;
            self.delivered += 1;
            Taken::New
        };
        self.trim();
        // The front is awaited (the flight was trimmed): lost, while it
        // has been overtaken by enough.
        while self.flying > 0 && self.base + 1 + self.path.reorder() <= self.highest {
            self.overtake_front();
        }
        if self.got == self.count {
            // An object smaller than the window: what it lost counts too.
            self.end_round();
            self.over = Some(Poll::Done);
        } else if self.delivered >= self.path.window() {
            self.end_round();
        }
        Ok(taken)
    }
}
