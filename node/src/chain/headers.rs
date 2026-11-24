//! Headers: the rules one is held to, and those a node keeps.
//!
//! A header is 204 bytes and its rules need nothing of its block, so a
//! node takes headers first: it learns which branch has the most work
//! before it fetches a body, and fetches only that branch's.
//!
//! # The rules
//!
//! Of a header whose parent is known ([`check`]):
//!
//! 1. The parent is not a block found invalid, and the height is the
//!    parent's and one, no higher than the chain's last.
//! 2. Its time is after the median of the eleven blocks before it, and
//!    no more than two hours ahead of the clock.
//! 3. Its work meets the target its parent gives it
//!    ([`crate::difficulty::Asert`]).
//!
//! A header that passes is kept with the work of its whole branch, and
//! the header with the most is the best ([`Chain::best_header`]).
//!
//! # Work, checked twice or once
//!
//! That a header's work meets its target takes two permutations to
//! check from what the header claims ([`Header::quick_pow_check`]); that
//! the claim is true takes the table, tens of milliseconds from the seed
//! text. A node that takes its state from others ([`crate::store::receive`])
//! does not need the second for the headers below the block it takes
//! the state of: that block's proof attests to the work of every block
//! before it. So headers can be kept with their work pending
//! ([`Status::WorkPending`]), and [`Chain::confirm_work`] checks in full
//! those no proof will vouch for. Every header's work is checked one way
//! or the other before its block is part of the chain.
//!
//! # What to fetch
//!
//! The best header's branch, from where it leaves the chain, is kept by
//! height beside the chain's own ([`crate::store::blocks`]): the plan.
//! Which bodies to fetch next is then a walk up it from the bottom
//! ([`Chain::missing_bodies`]), with no branch held in memory, however
//! far ahead of its blocks a node's headers are.
//!
//! # What is read
//!
//! A header's median time and its target follow from the headers before
//! it. In a run of headers those are the run's own, so they are carried
//! along and the store is read once, where the run begins: taking half a
//! million headers reads the store half a million times, not six.

use crate::block::Header;
use crate::difficulty::{Asert, Target};
use crate::error::Error;
use crate::hash::Digest;
use crate::hash::{digest_from_bytes, digest_to_bytes};
use crate::store::backend::Backend;
use crate::store::blocks::{Blocks, Entry};
use crate::store::pagefile::{ReadPages, Txn};
use crate::u256::U256;

use super::Chain;
use super::params::{ChainParams, block_work};

/// What the chain knows of a block it keeps the header of.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum Status {
    /// The header's rules hold and its body is kept; not yet part of the
    /// chain.
    HeaderValid = 0,
    /// It has been part of the chain: every rule held.
    Valid = 1,
    /// Found invalid.
    Invalid = 2,
    /// A header checked on its own, kept without its body.
    HeaderOnly = 3,
    /// A block this node can never connect, though it may be valid: its
    /// branch leaves the chain below what can be undone. Treated as
    /// invalid, but no peer is at fault for it.
    Aside = 4,
    /// [`Status::HeaderOnly`] with its work pending: checked so far
    /// only that the mix it claims meets the target.
    WorkPending = 5,
}

impl Status {
    fn from_byte(b: u8) -> Option<Status> {
        Some(match b {
            0 => Status::HeaderValid,
            1 => Status::Valid,
            2 => Status::Invalid,
            3 => Status::HeaderOnly,
            4 => Status::Aside,
            5 => Status::WorkPending,
            _ => return None,
        })
    }
}

/// A header kept, with what the chain knows of it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Known {
    pub header: Header,
    /// The work of the chain ending at this block; zero once invalid.
    pub work: U256,
    pub status: Status,
}

impl Known {
    /// Never to connect: found invalid, or set aside.
    pub fn invalid(&self) -> bool {
        matches!(self.status, Status::Invalid | Status::Aside)
    }

    /// Kept as a header alone, its body not yet seen.
    pub fn header_only(&self) -> bool {
        matches!(self.status, Status::HeaderOnly | Status::WorkPending)
    }

    /// What refuses a header that descends from this one, if anything.
    fn refusal(&self, of_parent: bool) -> Option<Error> {
        match self.status {
            Status::Aside => Some(Error::SetAside),
            Status::Invalid if of_parent => Some(Error::InvalidParent),
            Status::Invalid => Some(Error::KnownInvalid),
            _ => None,
        }
    }

    /// As the store keeps it.
    pub(super) fn entry(&self) -> Entry {
        Entry { id: self.header.hash(), header: self.header.to_bytes(), work: self.work, status: self.status as u8 }
    }

    fn of(entry: &Entry) -> Result<Known, Error> {
        let status = Status::from_byte(entry.status).ok_or(Error::Malformed("block status"))?;
        Ok(Known { header: Header::from_bytes(&entry.header)?, work: entry.work, status })
    }
}

/// The times of the last blocks of a branch, newest last: what the
/// median is taken of. Carried along a run of headers.
#[derive(Clone, Copy)]
pub(super) struct Times {
    times: [u64; Times::MOST],
    n: usize,
    window: usize,
}

impl Times {
    const MOST: usize = 32;

    fn new(window: usize) -> Times {
        assert!((1..=Times::MOST).contains(&window), "the median's window fits");
        Times { times: [0; Times::MOST], n: 0, window }
    }

    /// The next block's time.
    fn push(&mut self, time: u64) {
        if self.n == self.window {
            self.times.copy_within(1..self.n, 0);
            self.n -= 1;
        }
        self.times[self.n] = time;
        self.n += 1;
    }

    pub(super) fn median(&self) -> u64 {
        let mut sorted = self.times;
        sorted[..self.n].sort_unstable();
        sorted[self.n / 2]
    }
}

/// The header rules, of `header` whose parent is `parent`: `median` is
/// the median time of the blocks ending at the parent, `target` what the
/// parent gives, `work_ok` whether the header's work meets it. Returns
/// the work of the chain ending at the header.
pub fn check(
    params: &ChainParams,
    header: &Header,
    parent: &Known,
    median: u64,
    target: &Target,
    now: u64,
    work_ok: bool,
) -> Result<U256, Error> {
    if let Some(e) = parent.refusal(true) {
        return Err(e);
    }
    let expected = parent.header.height.checked_add(1).ok_or(Error::ChainEnded)?;
    if header.height != expected {
        return Err(Error::BadHeight { expected, got: header.height });
    }
    if header.height > params.final_height() {
        return Err(Error::ChainEnded);
    }
    if header.timestamp <= median {
        return Err(Error::TimestampTooOld { median, got: header.timestamp });
    }
    let limit = now.saturating_add(params.max_future_drift);
    if header.timestamp > limit {
        return Err(Error::TimestampTooNew { limit, got: header.timestamp });
    }
    if !work_ok {
        return Err(Error::BadProofOfWork);
    }
    Ok(parent.work.saturating_add(block_work((*target).into())))
}

/// A branch of headers weighed and not kept ([`Chain::weigh`]): where
/// it has got to, and the work of the chain ending there. What the
/// rules of the next header need of those before it, and no header
/// but the last.
pub struct Weighed {
    last: Header,
    times: Times,
    /// The branch's first block, where targets are counted from it.
    first: Option<Header>,
    work: U256,
}

impl Weighed {
    /// The work of the chain ending at the last header weighed.
    pub fn work(&self) -> U256 {
        self.work
    }

    /// The last header weighed.
    pub fn last(&self) -> &Header {
        &self.last
    }
}

/// What a header's rules need of the headers before it.
#[derive(Clone, Copy)]
struct Before {
    target: Target,
    median: u64,
}

fn corrupt(what: &'static str) -> Error {
    std::io::Error::new(std::io::ErrorKind::InvalidData, what).into()
}

/// The id of the best header a root record names, if it names one.
fn best_id(blocks: &Blocks) -> Option<Digest> {
    let bytes = &blocks.chain[..32];
    bytes.iter().any(|b| *b != 0).then(|| digest_from_bytes(bytes)).flatten()
}

fn set_best(blocks: &mut Blocks, id: Option<&Digest>) {
    blocks.chain[..32].copy_from_slice(&id.map_or([0; 32], digest_to_bytes));
}

impl<B: Backend + 'static, V> Chain<B, V> {
    pub(super) fn known_in(
        &self,
        pages: &impl ReadPages,
        blocks: &Blocks,
        id: &Digest,
    ) -> Result<Option<Known>, Error> {
        blocks.entry(pages, id)?.as_ref().map(Known::of).transpose()
    }

    fn header_in(&self, pages: &impl ReadPages, blocks: &Blocks, id: &Digest) -> Result<Option<Header>, Error> {
        Ok(self.known_in(pages, blocks, id)?.map(|k| k.header))
    }

    pub(super) fn header_at_in(
        &self,
        pages: &impl ReadPages,
        blocks: &Blocks,
        height: u32,
    ) -> Result<Option<Header>, Error> {
        match blocks.at(pages, height)? {
            Some(id) => Ok(Some(
                self.header_in(pages, blocks, &id)?.ok_or_else(|| corrupt("a block of the chain has no header"))?,
            )),
            None => Ok(None),
        }
    }

    /// Whether `header` is the chain's block at its height.
    pub(super) fn is_main_in(&self, pages: &impl ReadPages, blocks: &Blocks, header: &Header) -> Result<bool, Error> {
        Ok(blocks.at(pages, header.height)? == Some(header.hash()))
    }

    /// The header a block's id names, with what is known of it.
    pub fn known(&self, id: &Digest) -> Result<Option<Known>, Error> {
        let store = self.store();
        let snap = store.view()?;
        self.known_in(snap.pages(), snap.blocks(), id)
    }

    /// [`Chain::header_at`], as of the state `snap` holds: for whoever
    /// holds one already. (To ask the chain itself while holding its
    /// state is to take what keeps it twice, which waits for ever on
    /// anyone waiting to write between the two.)
    pub fn header_at_of(
        &self,
        snap: &crate::store::state::Snapshot<'_, B>,
        height: u32,
    ) -> Result<Option<Header>, Error> {
        self.header_at_in(snap.pages(), snap.blocks(), height)
    }

    /// The header of the chain's block at `height`.
    pub fn header_at(&self, height: u32) -> Result<Option<Header>, Error> {
        let store = self.store();
        let snap = store.view()?;
        self.header_at_in(snap.pages(), snap.blocks(), height)
    }

    /// The header of the last block of the chain.
    pub fn tip(&self) -> Result<Header, Error> {
        let store = self.store();
        let snap = store.view()?;
        // (As last read, while the last block is the one it was: this
        // is asked at every turn by whoever only wants the height, and
        // is not to be a read of the store each time.)
        Ok(self.tip_kept(snap.pages(), snap.blocks(), snap.tip())?.header)
    }

    /// The chain's last block, of height and id `tip`, with its work:
    /// as last read, while it is the block it was.
    pub(super) fn tip_kept(&self, pages: &impl ReadPages, blocks: &Blocks, tip: (u32, Digest)) -> Result<Known, Error> {
        let mut last = self.tip_read.lock().unwrap_or_else(|e| e.into_inner());
        if let Some((was, known)) = *last
            && was == tip.1
        {
            return Ok(known);
        }
        let known = self.tip_in(pages, blocks, tip.0)?;
        *last = Some((tip.1, known));
        Ok(known)
    }

    /// The times of the blocks ending at `tip`, along its own branch.
    pub(super) fn times_in(&self, pages: &impl ReadPages, blocks: &Blocks, tip: &Header) -> Result<Times, Error> {
        let window = self.params.median_time_window;
        let mut newest_first = [0u64; Times::MOST];
        let (mut n, mut header) = (0, *tip);
        loop {
            newest_first[n] = header.timestamp;
            n += 1;
            if n == window || header.height == 0 {
                break;
            }
            header = self
                .header_in(pages, blocks, &header.prev_hash)?
                .ok_or_else(|| corrupt("a header's ancestor is missing"))?;
        }
        let mut times = Times::new(window);
        newest_first[..n].iter().rev().for_each(|t| times.push(*t));
        Ok(times)
    }

    /// The earliest time a block after `parent` may carry: one past the
    /// median time of the blocks ending at `parent`.
    pub fn earliest_timestamp(&self, parent: &Header) -> Result<u64, Error> {
        let store = self.store();
        let snap = store.view()?;
        Ok(self.times_in(snap.pages(), snap.blocks(), parent)?.median() + 1)
    }

    /// Block 1 of `parent`'s branch, where a schedule that starts at the
    /// first block is anchored (block 1's own target is genesis's either
    /// way); `None` for a schedule anchored at genesis.
    pub(super) fn anchor_in(
        &self,
        pages: &impl ReadPages,
        blocks: &Blocks,
        parent: &Header,
    ) -> Result<Option<Header>, Error> {
        if !self.params.schedule.from_first_block || parent.height == 0 {
            return Ok(None);
        }
        // Back to block 1, or to a header whose block 1 is known: the
        // one last asked about, or any block of the chain.
        let last = *self.anchor.lock().unwrap();
        let mut h = *parent;
        let first = loop {
            if h.height == 1 {
                break h;
            }
            if let Some((_, first)) = last.filter(|(id, _)| *id == h.hash() || *id == h.prev_hash) {
                break first;
            }
            if self.is_main_in(pages, blocks, &h)? {
                break self.header_at_in(pages, blocks, 1)?.ok_or_else(|| corrupt("the chain has no first block"))?;
            }
            h = self
                .header_in(pages, blocks, &h.prev_hash)?
                .ok_or_else(|| corrupt("a header's ancestor is missing"))?;
        };
        *self.anchor.lock().unwrap() = Some((parent.hash(), first));
        Ok(Some(first))
    }

    /// The target of the block after `parent`, whose branch's block 1 is
    /// `first` if the schedule starts there.
    pub(super) fn target_from(&self, parent: &Header, first: Option<&Header>) -> Target {
        let (p, schedule) = (&self.params, self.params.schedule);
        let asert = match first {
            Some(first) => Asert::anchored(1, first.timestamp as i64, p.genesis_target, p.max_target, schedule),
            None => Asert::anchored(0, p.genesis_timestamp as i64, p.genesis_target, p.max_target, schedule),
        };
        asert.next_target(parent.height as u64, parent.timestamp as i64).into()
    }

    /// Target the block after `parent` must meet.
    pub fn expected_target(&self, parent: &Header) -> Result<Target, Error> {
        let store = self.store();
        let snap = store.view()?;
        let first = self.anchor_in(snap.pages(), snap.blocks(), parent)?;
        Ok(self.target_from(parent, first.as_ref()))
    }

    /// Whether `header`'s work is its own and meets `target`: from the
    /// table if one is loaded for its height, else from the seed text.
    pub(super) fn full_pow(&self, header: &Header, target: &Target) -> bool {
        use crate::pow::ItemSource;
        if !header.quick_pow_check(target) {
            return false;
        }
        if self.trust_work.load(std::sync::atomic::Ordering::Relaxed) {
            return true;
        }
        #[cfg(test)]
        self.full_pow_heights.lock().unwrap().push(header.height);
        let log_items = self.seed.params().log_items_at(header.height as u64);
        let dataset = self.dataset.read().unwrap().clone().filter(|d| d.log_items() == log_items);
        match dataset {
            Some(d) => header.verify_pow(&*d, target),
            None => header.verify_pow(&self.seed.at(header.height as u64), target),
        }
    }

    /// The most-work header: the tip, or one kept ahead of it.
    fn best_in(&self, pages: &impl ReadPages, blocks: &Blocks, tip: &Known) -> Result<Known, Error> {
        let Some(id) = best_id(blocks) else { return Ok(*tip) };
        let best = self.known_in(pages, blocks, &id)?.ok_or_else(|| corrupt("the best header is missing"))?;
        Ok(if best.work > tip.work { best } else { *tip })
    }

    pub(super) fn tip_in(&self, pages: &impl ReadPages, blocks: &Blocks, height: u32) -> Result<Known, Error> {
        let id = blocks.at(pages, height)?.ok_or_else(|| corrupt("the tip is not in the chain"))?;
        self.known_in(pages, blocks, &id)?.ok_or_else(|| corrupt("the tip has no header"))
    }

    /// The most-work header known, with its work: the tip, or a header
    /// kept ahead of it.
    pub fn best_header(&self) -> Result<Known, Error> {
        let store = self.store();
        let snap = store.view()?;
        let tip = self.tip_kept(snap.pages(), snap.blocks(), snap.tip())?;
        self.best_in(snap.pages(), snap.blocks(), &tip)
    }
}

impl<B: Backend + 'static, V: Sync> Chain<B, V> {
    /// Checks a header against its parent, which must be kept, and keeps
    /// it without a body, so that its block can be fetched once its
    /// branch has the most work. Returns whether it was new.
    pub fn accept_header(&self, header: &Header, now: u64) -> Result<bool, Error> {
        match self.accept_headers(std::slice::from_ref(header), now, false) {
            (_, Some(e)) => Err(e),
            (new, None) => Ok(new == 1),
        }
    }

    /// [`Chain::accept_header`] for a run of headers, each the child of
    /// the one before or of a header kept: their work is checked on all
    /// cores, then the rest in order, and they are kept in one step.
    /// Returns how many were new and the error that stopped the run, if
    /// one did; the headers before it are kept.
    ///
    /// With `defer_work` each header's work is left pending
    /// ([`Status::WorkPending`]): checked now only that the mix it
    /// claims meets the target.
    pub fn accept_headers(&self, headers: &[Header], now: u64, defer_work: bool) -> (usize, Option<Error>) {
        self.accept_headers_above(headers, now, defer_work.then_some(0))
    }

    /// [`Chain::accept_headers`], the work left pending of the headers
    /// above the height `defer_above`, if one is said, and checked in
    /// full of the rest: a run that begins near the chain's last block
    /// and goes on far above it is checked where it is near.
    pub fn accept_headers_above(
        &self,
        headers: &[Header],
        now: u64,
        defer_above: Option<u32>,
    ) -> (usize, Option<Error>) {
        match self.accept_inner(headers, now, defer_above) {
            Ok(done) => done,
            Err(e) => (0, Some(e)),
        }
    }

    fn accept_inner(
        &self,
        headers: &[Header],
        now: u64,
        defer_above: Option<u32>,
    ) -> Result<(usize, Option<Error>), Error> {
        let deferred = |h: &Header| defer_above.is_some_and(|above| h.height > above);
        // What each header's rules need of the headers before it, and
        // whether it is kept already. `None` where the parent is neither
        // the header before in the run (itself with a known parent) nor
        // kept: the run stops there.
        let mut before: Vec<Option<Before>> = Vec::with_capacity(headers.len());
        let mut kept: Vec<bool> = Vec::with_capacity(headers.len());
        {
            let store = self.store();
            let snap = store.view()?;
            let (pages, blocks) = (snap.pages(), snap.blocks());
            // The branch as far as the header before: its times, and its
            // block 1.
            let mut carried: Option<(Digest, Times, Option<Header>)> = None;
            for (i, h) in headers.iter().enumerate() {
                kept.push(blocks.entry(pages, &h.hash())?.is_some());
                let linked = i > 0 && before[i - 1].is_some() && carried.as_ref().is_some_and(|c| c.0 == h.prev_hash);
                let parent = if linked { Some(headers[i - 1]) } else { self.header_in(pages, blocks, &h.prev_hash)? };
                let Some(parent) = parent else {
                    before.push(None);
                    carried = None;
                    continue;
                };
                let (times, first) = match carried.take().filter(|_| linked) {
                    Some((_, times, first)) => (times, first.or((parent.height == 1).then_some(parent))),
                    None => (self.times_in(pages, blocks, &parent)?, self.anchor_in(pages, blocks, &parent)?),
                };
                let first = first.filter(|_| self.params.schedule.from_first_block && parent.height > 0);
                before.push(Some(Before { target: self.target_from(&parent, first.as_ref()), median: times.median() }));
                let mut times = times;
                times.push(h.timestamp);
                carried = Some((h.hash(), times, first));
            }
        }
        let work_ok: Vec<bool> = crate::parallel::par_map_min(headers.len(), 1, |i| {
            let (h, Some(b)) = (&headers[i], before[i]) else { return false };
            kept[i] || if deferred(h) { h.quick_pow_check(&b.target) } else { self.full_pow(h, &b.target) }
        });
        let tip_height = self.store().view()?.tip().0;
        let (mut new, mut stop) = (0, None);
        self.write_blocks(|txn, blocks| {
            let tip = self.tip_in(txn, blocks, tip_height)?;
            let (mut best, mut moved) = (self.best_in(txn, blocks, &tip)?, false);
            // The header before in the run, as it is kept now.
            let mut last: Option<Known> = None;
            for (i, h) in headers.iter().enumerate() {
                let id = h.hash();
                let known = match self.known_in(txn, blocks, &id)? {
                    Some(k) => match k.refusal(false) {
                        Some(e) => {
                            stop = Some(e);
                            break;
                        }
                        None => k,
                    },
                    None => {
                        let parent = match last.filter(|l| l.header.hash() == h.prev_hash) {
                            Some(p) => Some(p),
                            None => self.known_in(txn, blocks, &h.prev_hash)?,
                        };
                        let (Some(parent), Some(b)) = (parent, before[i]) else {
                            stop = Some(Error::UnknownParent);
                            break;
                        };
                        match check(&self.params, h, &parent, b.median, &b.target, now, work_ok[i]) {
                            Ok(work) => {
                                let status = if deferred(h) { Status::WorkPending } else { Status::HeaderOnly };
                                let known = Known { header: *h, work, status };
                                blocks.put_entry(txn, &known.entry())?;
                                new += 1;
                                known
                            }
                            Err(e) => {
                                stop = Some(e);
                                break;
                            }
                        }
                    }
                };
                if known.work > best.work {
                    set_best(blocks, Some(&id));
                    best = known;
                    moved = true;
                }
                last = Some(known);
            }
            if moved {
                self.plan(txn, blocks, &best.header)?;
            }
            Ok(())
        })?;
        Ok((new, stop))
    }

    /// Checks in full the work of the headers from height `from` up to
    /// `best`, on `best`'s branch, that were kept with their work
    /// pending, on all cores, and marks them checked. A node that takes
    /// its state from others calls it for the block it takes the state
    /// of and the headers after, whose work no proof it verifies attests
    /// to.
    ///
    /// On the first header that fails, it and every header after it on
    /// the branch are marked invalid, the best header falls back to the
    /// tip, and that header's height and id are returned. Otherwise, how
    /// many were checked.
    pub fn confirm_work(&self, best: &Header, from: u32) -> Result<Result<usize, (u32, Digest)>, Error> {
        let mut pending: Vec<(Header, Target)> = Vec::new();
        {
            let store = self.store();
            let snap = store.view()?;
            let (pages, blocks) = (snap.pages(), snap.blocks());
            let mut h = *best;
            while h.height >= from && h.height > 0 {
                let known = self
                    .known_in(pages, blocks, &h.hash())?
                    .ok_or_else(|| corrupt("a header of the branch is missing"))?;
                if let Some(e) = known.refusal(false) {
                    return Err(e);
                }
                let parent = self
                    .header_in(pages, blocks, &h.prev_hash)?
                    .ok_or_else(|| corrupt("a header's parent is missing"))?;
                if known.status == Status::WorkPending {
                    let first = self.anchor_in(pages, blocks, &parent)?;
                    pending.push((h, self.target_from(&parent, first.as_ref())));
                }
                h = parent;
            }
            pending.reverse();
        }
        // (Nothing pending: nothing to write. This is asked again and
        // again by a node that waits for blocks.)
        if pending.is_empty() {
            return Ok(Ok(0));
        }
        let ok: Vec<bool> =
            crate::parallel::par_map_min(pending.len(), 1, |i| self.full_pow(&pending[i].0, &pending[i].1));
        let bad = ok.iter().position(|ok| !ok);
        self.write_blocks(|txn, blocks| {
            for (i, (h, _)) in pending.iter().enumerate() {
                let known = self
                    .known_in(txn, blocks, &h.hash())?
                    .ok_or_else(|| corrupt("a header of the branch is missing"))?;
                let failed = bad.is_some_and(|b| i >= b);
                let marked = Known {
                    work: if failed { U256::ZERO } else { known.work },
                    status: if failed { Status::Invalid } else { Status::HeaderOnly },
                    ..known
                };
                blocks.put_entry(txn, &marked.entry())?;
            }
            if let Some(b) = bad {
                // The headers above the last pending one, checked in full
                // already, descend from the failure all the same.
                let mut h = *best;
                while h.height > pending[b].0.height {
                    let invalid = Known { header: h, work: U256::ZERO, status: Status::Invalid };
                    blocks.put_entry(txn, &invalid.entry())?;
                    match self.header_in(txn, blocks, &h.prev_hash)? {
                        Some(p) => h = p,
                        None => break,
                    }
                }
                set_best(blocks, None);
                blocks.drop_planned(txn, 0, u32::MAX)?;
            }
            Ok(())
        })?;
        Ok(bad.map_or(Ok(pending.len()), |b| Err((pending[b].0.height, pending[b].0.hash()))))
    }
}

impl<B: Backend + 'static, V> Chain<B, V> {
    /// Makes the planned branch `best`'s: its blocks from the first off
    /// the chain up to it, by height. What the plan has of the same
    /// branch already stands, so a header that extends the best costs
    /// one entry.
    pub(super) fn plan(&self, txn: &Txn<'_, B>, blocks: &mut Blocks, best: &Header) -> Result<(), Error> {
        blocks.drop_planned(txn, best.height.saturating_add(1), u32::MAX)?;
        let mut h = *best;
        // Down to where the plan already has the branch, or the chain.
        let lowest = loop {
            if self.is_main_in(txn, blocks, &h)? {
                break h.height + 1;
            }
            if blocks.planned_at(txn, h.height)? == Some(h.hash()) {
                // The rest of the plan below is this branch's too.
                return Ok(());
            }
            blocks.set_planned(txn, h.height, h.hash())?;
            h = self.header_in(txn, blocks, &h.prev_hash)?.ok_or_else(|| corrupt("a header's ancestor is missing"))?;
        };
        // Another branch's, from lower down, is the plan no more.
        blocks.drop_planned(txn, 0, lowest)
    }

    /// The headers of the blocks whose bodies are still needed to reach
    /// the best header, oldest first, into `out`: those of its branch
    /// off the chain that are kept as headers alone. Returns how many.
    ///
    /// If the branch runs through a block found invalid, the headers
    /// after it are marked as it is, the best header is the tip again
    /// until another is offered, and there is nothing to fetch.
    pub fn missing_bodies(&self, out: &mut [Header]) -> Result<usize, Error> {
        let store = self.store();
        let snap = store.view()?;
        let (pages, blocks) = (snap.pages(), snap.blocks());
        let (mut n, mut at) = (0, 0u32);
        while n < out.len() {
            let Some(height) = blocks.next_planned(pages, at)? else { break };
            let id = blocks.planned_at(pages, height)?.ok_or_else(|| corrupt("the plan lacks a height it has"))?;
            let known = self.known_in(pages, blocks, &id)?.ok_or_else(|| corrupt("a planned block has no header"))?;
            if known.invalid() {
                drop(snap);
                // (And the store itself: what follows writes to it.)
                drop(store);
                self.unplan_from(height, known.status)?;
                return Ok(0);
            }
            // One that is of the chain by now needs nothing.
            if known.header_only() && !self.is_main_in(pages, blocks, &known.header)? {
                out[n] = known.header;
                n += 1;
            }
            let Some(next) = height.checked_add(1) else { break };
            at = next;
        }
        Ok(n)
    }

    /// The planned branch runs through a block that will never connect,
    /// at `height`: what is planned above it goes the same way, so that
    /// a peer offering those headers again cannot make them the best.
    fn unplan_from(&self, height: u32, status: Status) -> Result<(), Error> {
        self.write_blocks(|txn, blocks| {
            let mut at = height.saturating_add(1);
            while let Some(h) = blocks.next_planned(txn, at)? {
                let id = blocks.planned_at(txn, h)?.ok_or_else(|| corrupt("the plan lacks a height it has"))?;
                if let Some(known) = self.known_in(txn, blocks, &id)? {
                    blocks.put_entry(txn, &Known { work: U256::ZERO, status, ..known }.entry())?;
                }
                let Some(next) = h.checked_add(1) else { break };
                at = next;
            }
            set_best(blocks, None);
            blocks.drop_planned(txn, 0, u32::MAX)
        })
    }

    /// Where the branch of the header with the most work leaves the
    /// chain, if that is below what the chain can undo: the height of
    /// the last block the two share. The chain cannot go over to that
    /// branch block by block, and is on the one with the most work
    /// again only by taking the state as of a block of it.
    pub fn cut_off(&self) -> Result<Option<u32>, Error> {
        let state = self.whole()?;
        let undo = state.oldest_undo();
        let snap = state.snapshot()?;
        let (pages, blocks) = (snap.pages(), snap.blocks());
        let tip = self.tip_in(pages, blocks, snap.tip().0)?;
        let mut at = self.best_in(pages, blocks, &tip)?.header;
        // (A header above the chain's last is on another branch or
        // leads down to that block: the chain's own are above none.)
        while !self.is_main_in(pages, blocks, &at)? {
            match self.header_in(pages, blocks, &at.prev_hash)? {
                Some(parent) => at = parent,
                None => return Ok(None),
            }
        }
        let reached = at.height >= tip.header.height || undo.is_some_and(|oldest| oldest <= at.height + 1);
        Ok((!reached).then_some(at.height))
    }

    /// Begins to weigh a branch that leaves the headers kept here at
    /// the header `from`, which is one of them.
    pub fn weigh_from(&self, from: &Digest) -> Result<Weighed, Error> {
        let store = self.store();
        let snap = store.view()?;
        let (pages, blocks) = (snap.pages(), snap.blocks());
        let known = self.known_in(pages, blocks, from)?.ok_or(Error::UnknownParent)?;
        if let Some(e) = known.refusal(true) {
            return Err(e);
        }
        Ok(Weighed {
            last: known.header,
            times: self.times_in(pages, blocks, &known.header)?,
            first: self.anchor_in(pages, blocks, &known.header)?,
            work: known.work,
        })
    }

    /// Checks `headers`, which follow what was weighed so far, by every
    /// rule of a header ([`check`]), their work by what each claims of
    /// it, and adds their work: nothing is kept, and nothing is read. A
    /// branch that leaves the chain far down is weighed so before any
    /// of it is kept: headers from an old block cost whoever makes
    /// them next to nothing, there is no end of them, and only a branch
    /// with more work than the best there is is worth keeping. (Its
    /// work is claimed, as a header's is when it is kept with its work
    /// left to a proof: a branch that weighs more is kept and checked
    /// as any is.)
    pub fn weigh(&self, weighed: &mut Weighed, headers: &[Header], now: u64) -> Result<(), Error> {
        for header in headers {
            if header.prev_hash != weighed.last.hash() {
                return Err(Error::UnknownParent);
            }
            let target = self.target_from(&weighed.last, weighed.first.as_ref());
            let parent = Known { header: weighed.last, work: weighed.work, status: Status::HeaderValid };
            let median = weighed.times.median();
            let work = check(&self.params, header, &parent, median, &target, now, header.quick_pow_check(&target))?;
            if self.params.schedule.from_first_block && header.height == 1 {
                weighed.first = Some(*header);
            }
            weighed.times.push(header.timestamp);
            (weighed.last, weighed.work) = (*header, work);
        }
        Ok(())
    }

    /// The ancestor at `height` of the kept header `from`.
    pub fn ancestor(&self, from: &Header, height: u32) -> Result<Option<Header>, Error> {
        if height > from.height {
            return Ok(None);
        }
        let store = self.store();
        let snap = store.view()?;
        let mut h = *from;
        while h.height > height {
            match self.header_in(snap.pages(), snap.blocks(), &h.prev_hash)? {
                Some(p) => h = p,
                None => return Ok(None),
            }
        }
        Ok(Some(h))
    }

    /// Block ids that locate the chain for a peer: the tip and its
    /// ancestors at distances that double, then genesis. At most
    /// [`LOCATOR`] ids, written to `out`; returns how many.
    pub fn locator(&self, out: &mut [Digest; LOCATOR]) -> Result<usize, Error> {
        let store = self.store();
        let snap = store.view()?;
        let (mut n, mut step, mut h) = (0, 1u32, snap.tip().0);
        loop {
            let id = snap.blocks().at(snap.pages(), h)?.ok_or_else(|| corrupt("the chain lacks a height"))?;
            // The last place is genesis's.
            if h == 0 || n + 1 < LOCATOR {
                out[n] = id;
                n += 1;
            }
            if h == 0 {
                return Ok(n);
            }
            if n > 10 {
                step = step.saturating_mul(2);
            }
            h = h.saturating_sub(step);
        }
    }

    /// [`Chain::locator`], from the best header: it first, if it is
    /// ahead of the chain.
    pub fn header_locator(&self, out: &mut [Digest; LOCATOR]) -> Result<usize, Error> {
        let best = self.best_header()?.header.hash();
        let n = self.locator(out)?;
        if out[0] == best {
            return Ok(n);
        }
        // Genesis keeps the last place.
        let genesis = out[n - 1];
        let n = (n + 1).min(LOCATOR);
        out.copy_within(0..n - 2, 1);
        out[0] = best;
        out[n - 1] = genesis;
        Ok(n)
    }

    /// The chain's headers after the first id of `locator` that is on
    /// the chain, oldest first, into `out`: without a match, those after
    /// genesis. Returns how many.
    pub fn headers_after(&self, locator: &[Digest], out: &mut [Header]) -> Result<usize, Error> {
        let store = self.store();
        let snap = store.view()?;
        let (pages, blocks) = (snap.pages(), snap.blocks());
        let mut from = 0u32;
        for id in locator {
            if let Some(h) = self.header_in(pages, blocks, id)?
                && self.is_main_in(pages, blocks, &h)?
            {
                from = h.height;
                break;
            }
        }
        let mut n = 0;
        while n < out.len() && from < snap.tip().0 {
            from += 1;
            out[n] = self.header_at_in(pages, blocks, from)?.ok_or_else(|| corrupt("the chain lacks a height"))?;
            n += 1;
        }
        Ok(n)
    }

    /// The chain's headers from `height` on, into `out`: how many.
    pub fn headers_from(&self, height: u32, out: &mut [Header]) -> Result<usize, Error> {
        let store = self.store();
        let snap = store.view()?;
        let mut n = 0;
        while n < out.len() && height as u64 + n as u64 <= snap.tip().0 as u64 {
            let h = self.header_at_in(snap.pages(), snap.blocks(), height + n as u32)?;
            out[n] = h.ok_or_else(|| corrupt("the chain lacks a height"))?;
            n += 1;
        }
        Ok(n)
    }
}

/// The most ids a locator has.
pub const LOCATOR: usize = 32;

#[cfg(test)]
pub(crate) mod tests {
    use super::*;
    use crate::chain::verify::AcceptAllProofs;
    use crate::difficulty::Schedule;
    use crate::pow::{Dataset, PowParams, SeedText, hashimoto};
    use crate::store::testing::{Lost, MemBackend};

    type TestChain = Chain<MemBackend, AcceptAllProofs>;

    pub(crate) const T0: u64 = 1_800_000_000;
    /// Far enough ahead that no header is too new.
    pub(crate) const NOW: u64 = T0 + 1_000_000;

    /// The mix of [`easy`]'s genesis header's work.
    pub(crate) const EASY_MIX: Digest = [0; 32];

    /// A network whose every header meets its target, on the dev table.
    pub(crate) fn easy() -> ChainParams {
        ChainParams {
            pow: PowParams::DEV,
            genesis_timestamp: T0,
            genesis_nonce: [7; 32],
            genesis_mix: Some(EASY_MIX),
            genesis_target: ChainParams::MAINNET.max_target,
            ..ChainParams::MAINNET
        }
    }

    /// One whose targets ask four tries, and move with the times.
    fn hard() -> ChainParams {
        ChainParams { genesis_target: U256([0, 0, 0, 1 << 54]), ..easy() }
    }

    pub(crate) fn seed() -> SeedText<'static> {
        SeedText::new(PowParams::DEV)
    }

    /// The dev table, made once: headers are mined from it, and the
    /// chains check against it, a thousand times faster than from the
    /// seed text.
    pub(crate) fn table() -> std::sync::Arc<Dataset<'static>> {
        static TABLE: std::sync::OnceLock<std::sync::Arc<Dataset<'static>>> = std::sync::OnceLock::new();
        TABLE.get_or_init(|| std::sync::Arc::new(Dataset::generate(&seed(), 10))).clone()
    }

    fn open_on(backend: MemBackend, params: ChainParams) -> Result<TestChain, Error> {
        let chain = Chain::open(backend, 8, params, seed(), AcceptAllProofs)?;
        chain.set_dataset(table());
        Ok(chain)
    }

    fn open(params: ChainParams) -> TestChain {
        open_on(MemBackend::new(), params).unwrap()
    }

    /// A header after `parent` at `time` whose work meets `target`:
    /// `salt` tells apart two with the same parent and time.
    fn mine(parent: &Header, time: u64, target: &Target, salt: u8) -> Header {
        let mut h = Header {
            prev_hash: parent.hash(),
            height: parent.height + 1,
            timestamp: time,
            body_commitment: [salt; 32],
            state_root: parent.state_root,
            statement: parent.statement,
            aux: [0; 32],
            mix: crate::hash::EMPTY,
            nonce: [salt; 32],
        };
        loop {
            h.mix = hashimoto(&*table(), &h.pow_hash(), &h.nonce).mix;
            if h.quick_pow_check(target) {
                return h;
            }
            h.nonce[0] = h.nonce[0].wrapping_add(1);
            if h.nonce[0] == salt {
                h.nonce[1] = h.nonce[1].wrapping_add(1);
            }
        }
    }

    /// `n` headers after `parent`, ten minutes apart, on a network whose
    /// schedule is anchored at genesis.
    fn run(chain: &TestChain, parent: &Header, n: usize, salt: u8) -> Vec<Header> {
        let mut out: Vec<Header> = Vec::with_capacity(n);
        for _ in 0..n {
            let p = *out.last().unwrap_or(parent);
            out.push(mine(&p, p.timestamp + 600, &chain.target_from(&p, None), salt));
        }
        out
    }

    #[test]
    fn genesis_begins_the_chain() {
        let chain = open(easy());
        let genesis = easy().genesis().header;
        assert_eq!(chain.tip().unwrap(), genesis);
        assert_eq!(chain.header_at(0).unwrap(), Some(genesis));
        assert_eq!(chain.header_at(1).unwrap(), None);
        let known = chain.known(&genesis.hash()).unwrap().unwrap();
        assert_eq!(known, Known { header: genesis, work: U256::ZERO, status: Status::Valid });
        assert_eq!(chain.best_header().unwrap(), known);
        assert_eq!(chain.earliest_timestamp(&genesis).unwrap(), T0 + 1);
        // Opened again it is the same chain; as another network's, refused.
        let image = chain.state().file().backend().image(Lost::All);
        let again = open_on(MemBackend::from_image(image.clone()), easy()).unwrap();
        assert_eq!(again.tip().unwrap(), genesis);
        let other = ChainParams { genesis_timestamp: T0 + 1, ..easy() };
        let refused = open_on(MemBackend::from_image(image), other);
        assert_eq!(refused.err(), Some(Error::WrongGenesis));
    }

    /// A run of headers is kept in one step, each with the work of its
    /// branch; one at a time they are kept the same, so what is carried
    /// along a run is what the store would have said.
    #[test]
    fn a_run_of_headers_is_kept() {
        let chain = open(hard());
        let genesis = hard().genesis().header;
        let headers = run(&chain, &genesis, 30, 1);
        assert_eq!(chain.accept_headers(&headers, NOW, false), (30, None));
        assert_eq!(chain.full_pow_heights.lock().unwrap().len(), 30);
        let mut work = U256::ZERO;
        for (i, h) in headers.iter().enumerate() {
            let parent = if i == 0 { genesis } else { headers[i - 1] };
            work = work.saturating_add(block_work(chain.expected_target(&parent).unwrap().into()));
            let known = chain.known(&h.hash()).unwrap().unwrap();
            assert_eq!(known, Known { header: *h, work, status: Status::HeaderOnly });
            assert!(known.header_only() && !known.invalid());
        }
        assert_eq!(chain.best_header().unwrap().header, headers[29]);
        // The chain itself has not moved: these are headers.
        assert_eq!(chain.tip().unwrap(), genesis);
        // Known already: nothing is new, and no work is checked again.
        assert_eq!(chain.accept_headers(&headers, NOW, false), (0, None));
        assert_eq!(chain.accept_headers(&headers[10..], NOW, false), (0, None));
        assert_eq!(chain.full_pow_heights.lock().unwrap().len(), 30);

        // One at a time, in runs that begin anywhere, and from the seed
        // text alone, with no table.
        let other = Chain::open(MemBackend::new(), 8, hard(), seed(), AcceptAllProofs).unwrap();
        for h in &headers[..13] {
            assert_eq!(other.accept_header(h, NOW), Ok(true));
        }
        assert_eq!(other.accept_header(&headers[5], NOW), Ok(false));
        assert_eq!(other.accept_headers(&headers[9..22], NOW, false), (9, None));
        assert_eq!(other.accept_headers(&headers[22..], NOW, false), (8, None));
        for h in &headers {
            assert_eq!(other.known(&h.hash()).unwrap(), chain.known(&h.hash()).unwrap());
        }
        // The times behind a header are its branch's, however it came.
        assert_eq!(chain.earliest_timestamp(&headers[29]).unwrap(), headers[24].timestamp + 1);
        assert_eq!(chain.ancestor(&headers[29], 4).unwrap(), Some(headers[3]));
        assert_eq!(chain.ancestor(&headers[29], 0).unwrap(), Some(genesis));
        assert_eq!(chain.ancestor(&headers[3], 9).unwrap(), None);
    }

    /// Each rule refuses what breaks it, and the headers before the one
    /// refused are kept.
    #[test]
    fn headers_that_break_a_rule_are_refused() {
        let chain = open(hard());
        let genesis = hard().genesis().header;
        let headers = run(&chain, &genesis, 14, 1);
        let target = |parent: &Header| chain.target_from(parent, None);
        // A parent not known, alone and in the middle of a run.
        assert_eq!(chain.accept_header(&headers[1], NOW), Err(Error::UnknownParent));
        let mut gap = headers[..6].to_vec();
        gap.remove(3);
        assert_eq!(chain.accept_headers(&gap, NOW, false), (3, Some(Error::UnknownParent)));
        assert_eq!(chain.best_header().unwrap().header, headers[2]);
        assert_eq!(chain.accept_headers(&headers[..12], NOW, false), (9, None));
        let tip = headers[11];

        // Another height than the parent's and one.
        let off = Header { height: 14, ..mine(&tip, tip.timestamp + 600, &target(&tip), 2) };
        assert_eq!(chain.accept_header(&off, NOW), Err(Error::BadHeight { expected: 13, got: 14 }));
        // A time not after the median of the eleven before, and one just after.
        let median = headers[6].timestamp;
        let old = mine(&tip, median, &target(&tip), 2);
        assert_eq!(chain.accept_header(&old, NOW), Err(Error::TimestampTooOld { median, got: median }));
        let just = mine(&tip, median + 1, &target(&tip), 2);
        assert_eq!(chain.accept_header(&just, NOW), Ok(true));
        // A time too far ahead of the clock, and one at the limit.
        let ahead = mine(&tip, tip.timestamp + 600, &target(&tip), 3);
        let limit = ahead.timestamp - 1;
        let refused = Error::TimestampTooNew { limit, got: ahead.timestamp };
        assert_eq!(chain.accept_header(&ahead, limit - 7200), Err(refused));
        assert_eq!(chain.accept_header(&ahead, limit - 7200 + 1), Ok(true));
        // Work that does not meet the target, and work that is not the
        // header's: a mix that only looks as if it met it.
        let mut weak = mine(&tip, tip.timestamp + 600, &target(&tip), 4);
        while weak.quick_pow_check(&target(&tip)) {
            weak.nonce[5] = weak.nonce[5].wrapping_add(1);
        }
        assert_eq!(chain.accept_header(&weak, NOW), Err(Error::BadProofOfWork));
        let forged = forge(mine(&tip, tip.timestamp + 600, &target(&tip), 5), &target(&tip));
        assert_eq!(chain.accept_header(&forged, NOW), Err(Error::BadProofOfWork));
        assert_eq!(chain.known(&forged.hash()).unwrap(), None);
        // The work of another target than the parent gives: an easier one.
        let easier: Target = ChainParams::MAINNET.max_target.into();
        let mut cheap = mine(&tip, tip.timestamp + 600, &easier, 6);
        while cheap.quick_pow_check(&target(&tip)) {
            cheap = mine(&tip, tip.timestamp + 600, &easier, cheap.nonce[9].wrapping_add(1));
        }
        assert_eq!(chain.accept_header(&cheap, NOW), Err(Error::BadProofOfWork));

        // Past the last block the chain can have.
        let short = ChainParams { emission: &[(3, 50)], ..hard() };
        let ended = open(short);
        let four = run(&ended, &short.genesis().header, 4, 1);
        assert_eq!(ended.accept_headers(&four, NOW, false), (3, Some(Error::ChainEnded)));
    }

    /// `header` with a mix that is not its own but passes the quick
    /// check: what a forger grinds for at two permutations a try.
    fn forge(mut header: Header, target: &Target) -> Header {
        loop {
            header.mix[0] = header.mix[0].wrapping_add(1);
            if header.quick_pow_check(target) && !header.verify_pow(&*table(), target) {
                return header;
            }
        }
    }

    /// Headers kept with their work pending are checked in full when
    /// asked: those that hold are marked so, and a forged one takes
    /// every header after it down, and the best header with them.
    #[test]
    fn work_left_pending_is_confirmed() {
        let chain = open(hard());
        let genesis = hard().genesis().header;
        let headers = run(&chain, &genesis, 12, 1);
        assert_eq!(chain.accept_headers(&headers, NOW, true), (12, None));
        assert!(chain.full_pow_heights.lock().unwrap().is_empty());
        assert_eq!(chain.known(&headers[4].hash()).unwrap().unwrap().status, Status::WorkPending);
        // From a height up: those below are left for a proof to vouch for.
        assert_eq!(chain.confirm_work(&headers[11], 7).unwrap(), Ok(6));
        let mut checked = chain.full_pow_heights.lock().unwrap().clone();
        checked.sort_unstable();
        assert_eq!(checked, vec![7, 8, 9, 10, 11, 12]);
        for (i, h) in headers.iter().enumerate() {
            let want = if i + 1 >= 7 { Status::HeaderOnly } else { Status::WorkPending };
            assert_eq!(chain.known(&h.hash()).unwrap().unwrap().status, want);
        }
        assert_eq!(chain.confirm_work(&headers[11], 7).unwrap(), Ok(0));
        assert_eq!(chain.best_header().unwrap().header, headers[11]);

        // A branch with a forged header in it, and more work than the first.
        let target = |parent: &Header| chain.target_from(parent, None);
        let mut branch = vec![mine(&headers[3], headers[3].timestamp + 300, &target(&headers[3]), 2)];
        for i in 0..11 {
            let p = branch[i];
            let next = mine(&p, p.timestamp + 300, &target(&p), 2);
            branch.push(if i == 4 { forge(next, &target(&p)) } else { next });
        }
        // Kept with the full check, the run stops at the forgery.
        let strict = open(hard());
        strict.accept_headers(&headers, NOW, false);
        assert_eq!(strict.accept_headers(&branch, NOW, false), (5, Some(Error::BadProofOfWork)));
        // Kept with the work of those above a height left pending: the
        // forgery is found if it is at that height or under it, and
        // not if it is above.
        let near = open(hard());
        near.accept_headers(&headers, NOW, false);
        let forged = branch[5].height;
        assert_eq!(near.accept_headers_above(&branch, NOW, Some(forged)), (5, Some(Error::BadProofOfWork)));
        let far = open(hard());
        far.accept_headers(&headers, NOW, false);
        assert_eq!(far.accept_headers_above(&branch, NOW, Some(forged - 1)), (12, None));
        for (i, h) in branch.iter().enumerate() {
            let want = if i >= 5 { Status::WorkPending } else { Status::HeaderOnly };
            assert_eq!(far.known(&h.hash()).unwrap().unwrap().status, want, "header {i} of the branch");
        }
        // Kept pending, all of it, and it is the best.
        assert_eq!(chain.accept_headers(&branch[..8], NOW, true), (8, None));
        assert_eq!(chain.accept_headers(&branch[8..], NOW, false), (4, None));
        assert_eq!(chain.best_header().unwrap().header, branch[11]);
        let mut out = [genesis; 40];
        assert_eq!(chain.missing_bodies(&mut out).unwrap(), 16);
        assert_eq!((&out[..4], &out[4..16]), (&headers[..4], &branch[..]));
        let found = chain.confirm_work(&branch[11], 1).unwrap();
        assert_eq!(found, Err((branch[5].height, branch[5].hash())));
        for (i, h) in branch.iter().enumerate() {
            let known = chain.known(&h.hash()).unwrap().unwrap();
            let want = if i >= 5 { (Status::Invalid, true) } else { (Status::HeaderOnly, false) };
            assert_eq!((known.status, known.work == U256::ZERO), want, "header {i} of the branch");
        }
        // The best is the tip again until a header is offered; the
        // forgery and what descends from it stay refused.
        assert_eq!(chain.best_header().unwrap().header, genesis);
        assert_eq!(chain.missing_bodies(&mut out).unwrap(), 0);
        assert_eq!(chain.accept_header(&branch[5], NOW), Err(Error::KnownInvalid));
        let child = mine(&branch[11], branch[11].timestamp + 300, &target(&branch[11]), 3);
        assert_eq!(chain.accept_header(&child, NOW), Err(Error::InvalidParent));
        assert_eq!(chain.confirm_work(&branch[11], 1).err(), Some(Error::KnownInvalid));
        assert_eq!(chain.accept_headers(&headers[11..], NOW, false), (0, None));
        assert_eq!(chain.best_header().unwrap().header, headers[11]);
        assert_eq!(chain.missing_bodies(&mut out).unwrap(), 12);
        assert_eq!(out[..12], headers[..]);

        // A block of the plan found invalid some other way (its body,
        // when it came): what is planned above it goes with it.
        let bad = chain.known(&headers[6].hash()).unwrap().unwrap();
        let marked = Known { work: U256::ZERO, status: Status::Aside, ..bad };
        chain.state().write_blocks(|txn, blocks| blocks.put_entry(txn, &marked.entry())).unwrap();
        assert_eq!(chain.missing_bodies(&mut out).unwrap(), 0);
        assert_eq!(chain.best_header().unwrap().header, genesis);
        for (i, h) in headers.iter().enumerate() {
            // Below it they are as they were: the first four confirmed
            // with the branch that left them, two never.
            let want = match i {
                6.. => Status::Aside,
                4 | 5 => Status::WorkPending,
                _ => Status::HeaderOnly,
            };
            assert_eq!(chain.known(&h.hash()).unwrap().unwrap().status, want, "header {i}");
        }
        assert_eq!(chain.accept_header(&headers[9], NOW), Err(Error::SetAside));
        // What is below it is still good, and is the best when offered.
        assert_eq!(chain.accept_headers(&headers[..6], NOW, false), (0, None));
        assert_eq!(chain.best_header().unwrap().header, headers[5]);
        assert_eq!(chain.missing_bodies(&mut out).unwrap(), 6);
    }

    /// Between branches the best header is the one with the most work,
    /// and a locator leads with it.
    #[test]
    fn the_best_header_has_the_most_work() {
        let chain = open(easy());
        let genesis = easy().genesis().header;
        let a = run(&chain, &genesis, 5, 1);
        let b = run(&chain, &a[1], 6, 2);
        assert_eq!(chain.accept_headers(&a, NOW, false), (5, None));
        assert_eq!(chain.accept_headers(&b[..3], NOW, false), (3, None));
        // As long, and no more work: the first stays.
        assert_eq!(chain.best_header().unwrap().header, a[4]);
        let mut out = [genesis; 20];
        assert_eq!(chain.missing_bodies(&mut out).unwrap(), 5);
        assert_eq!(out[..5], a[..]);
        assert_eq!(chain.accept_headers(&b, NOW, false), (3, None));
        assert_eq!(chain.best_header().unwrap().header, b[5]);
        assert_eq!(chain.missing_bodies(&mut out).unwrap(), 8);
        assert_eq!((&out[..2], &out[2..8]), (&a[..2], &b[..]));
        assert_eq!(chain.ancestor(&b[5], 2).unwrap(), Some(a[1]));
        let more = run(&chain, &a[4], 4, 1);
        assert_eq!(chain.accept_headers(&more, NOW, false), (4, None));
        assert_eq!(chain.best_header().unwrap().header, more[3]);

        // What is to be fetched follows the best: the first branch, then
        // the second from where it leaves the first, then the first again.
        let fetch = |chain: &TestChain| {
            let mut out = [genesis; 20];
            let n = chain.missing_bodies(&mut out).unwrap();
            out[..n].to_vec()
        };
        let mut all = a.clone();
        all.extend(&more);
        assert_eq!(fetch(&chain), all);
        let mut few = [genesis; 3];
        assert_eq!(chain.missing_bodies(&mut few).unwrap(), 3);
        assert_eq!(few[..], a[..3]);

        let mut ids = [genesis.hash(); LOCATOR];
        assert_eq!(chain.locator(&mut ids).unwrap(), 1);
        assert_eq!(chain.header_locator(&mut ids).unwrap(), 2);
        assert_eq!(ids[..2], [more[3].hash(), genesis.hash()]);
        // Only genesis is of the chain yet.
        let mut out = [genesis; 4];
        assert_eq!(chain.headers_after(&[more[3].hash(), genesis.hash()], &mut out).unwrap(), 0);
        assert_eq!(chain.headers_from(0, &mut out).unwrap(), 1);
        assert_eq!(chain.headers_from(1, &mut out).unwrap(), 0);
    }

    /// A schedule that starts at the first block gives each branch the
    /// targets of its own block 1, whichever way its headers come, and
    /// when the file is opened again.
    #[test]
    fn a_schedule_from_the_first_block() {
        let schedule = Schedule { block_time: 600, half_life: 3600, from_first_block: true };
        let params = ChainParams { schedule, ..hard() };
        let genesis = params.genesis().header;
        let asert = |first: &Header| {
            Asert::anchored(1, first.timestamp as i64, params.genesis_target, params.max_target, schedule)
        };
        // Two branches, their first blocks a day apart, each then a
        // block every five minutes: ahead of its own schedule.
        let branch = |first_time: u64, salt: u8| {
            let mut out = vec![mine(&genesis, first_time, &params.genesis_target.into(), salt)];
            for i in 0..9 {
                let p = out[i];
                let target: Target = asert(&out[0]).next_target(p.height as u64, p.timestamp as i64).into();
                out.push(mine(&p, p.timestamp + 300, &target, salt));
            }
            out
        };
        let (a, b) = (branch(T0 + 50_000, 1), branch(T0 + 150_000, 2));
        let chain = open(params);
        assert_eq!(chain.accept_headers(&a, NOW, false), (10, None));
        for h in &b {
            assert_eq!(chain.accept_header(h, NOW), Ok(true));
        }
        // The targets grew harder with each block, and are each branch's own.
        let t = |h: &Header| U256::from(chain.expected_target(h).unwrap());
        assert!(t(&a[9]) < t(&a[1]) && t(&a[1]) < params.genesis_target);
        assert_eq!(t(&a[9]), asert(&a[0]).next_target(10, a[9].timestamp as i64));
        assert_eq!(t(&b[9]), asert(&b[0]).next_target(10, b[9].timestamp as i64));
        assert_eq!(t(&genesis), params.genesis_target);
        // Opened again, asked in any order.
        let image = chain.state().file().backend().image(Lost::All);
        let again = open_on(MemBackend::from_image(image), params).unwrap();
        for h in [&b[9], &a[4], &a[9], &b[0], &a[0]] {
            let first = if a.contains(h) { &a[0] } else { &b[0] };
            let want = asert(first).next_target(h.height as u64, h.timestamp as i64);
            assert_eq!(U256::from(again.expected_target(h).unwrap()), want);
        }
        // A header mined for the other branch's schedule is not this
        // one's: by the first branch's, the second is a day behind, and
        // its target far easier.
        let wrong: Target = asert(&a[0]).next_target(10, b[9].timestamp as i64).into();
        assert!(U256::from(wrong) > t(&b[9]));
        let mut stray = mine(&b[9], b[9].timestamp + 300, &wrong, 3);
        while stray.quick_pow_check(&again.expected_target(&b[9]).unwrap()) {
            stray = mine(&b[9], b[9].timestamp + 300, &wrong, stray.nonce[3].wrapping_add(9));
        }
        assert_eq!(again.accept_header(&stray, NOW), Err(Error::BadProofOfWork));
    }

    #[test]
    fn the_median_of_the_last_times() {
        let mut times = Times::new(5);
        times.push(40);
        assert_eq!(times.median(), 40);
        times.push(10);
        // Of two, the later.
        assert_eq!(times.median(), 40);
        for t in [30, 20, 50] {
            times.push(t);
        }
        assert_eq!(times.median(), 30);
        // The oldest leaves: 10, 30, 20, 50, 60.
        times.push(60);
        assert_eq!(times.median(), 30);
        times.push(70);
        times.push(80);
        assert_eq!(times.median(), 60);
    }

    #[test]
    fn a_status_is_one_byte() {
        let genesis = easy().genesis().header;
        for status in [
            Status::HeaderValid,
            Status::Valid,
            Status::Invalid,
            Status::HeaderOnly,
            Status::Aside,
            Status::WorkPending,
        ] {
            let known = Known { header: genesis, work: U256::from_u64(9), status };
            assert_eq!(Known::of(&known.entry()), Ok(known));
            assert_eq!(known.invalid(), matches!(status, Status::Invalid | Status::Aside));
        }
        let entry = Entry { status: 6, ..Known { header: genesis, work: U256::ZERO, status: Status::Valid }.entry() };
        assert_eq!(Known::of(&entry), Err(Error::Malformed("block status")));
        let aside = Known { header: genesis, work: U256::ZERO, status: Status::Aside };
        assert_eq!((aside.refusal(true), aside.refusal(false)), (Some(Error::SetAside), Some(Error::SetAside)));
    }
}
