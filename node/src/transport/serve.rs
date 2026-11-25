//! The side that holds objects: who is sent which chunk, and when.
//!
//! [`Serve`] does not hold the objects. It takes requests
//! ([`Serve::get`]) and says, a chunk at a time, what to send next
//! ([`Serve::next`]): the caller finds the object by its name and sends
//! the chunk, or says that there is none ([`Serve::cancel`]).
//!
//! # What it keeps, and its bounds
//!
//! A request waits here until its chunks are sent, and how much may
//! wait is bounded ([`Limits`]): so many requests in all, so many
//! requests and so many chunks for any one address. A request over a
//! bound is dropped. Nothing is said: the asking side sees silence,
//! takes it for loss and asks for less.
//!
//! The bounds are a node's own to set: they are how much it is willing
//! to do for others at once, and a node many others lean on (a seed)
//! sets them higher. What is here is kept by address, so that finding
//! whose turn it is costs the same however many are waiting.
//!
//! A request for more of the fetch its address asked for last is joined
//! to that one while there is room in it, so that a fetch asking a
//! little at a time, as chunks arrive, is one request here and not
//! many.
//!
//! # Order, and turns
//!
//! The chunks of one address go out in the order it asked for them, over
//! all its requests: the asking side tells what was lost by what was
//! overtaken, and that holds only if nothing here overtakes.
//! Between addresses, turns are taken a chunk at a time, in the order
//! of the addresses, so one large fetch does not hold up a small one.
//!
//! # Pace
//!
//! Chunks go out at a rate ([`Serve::new`]), with a short burst allowed
//! after idleness. A window of two megabytes written to a socket at once
//! overruns the first small buffer on the path, and the losses look to
//! the asking side like a path that carries less than it does.

use std::collections::{BTreeMap, VecDeque};
use std::net::SocketAddr;
use std::ops::Bound;

use super::token::Tokens;
use super::wire::{Get, MAX_NAME, MAX_RANGES, Range};
use super::{MAX_WINDOW, Micros, SECOND};

/// How much a node serves, and how much may wait to be served.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Limits {
    /// Chunks sent a second, to everyone together.
    pub rate: u32,
    /// Requests waiting, in all.
    pub waiting: usize,
    /// Requests of one host waiting: of every port of its address
    /// together, but for this machine's own address, where each port is
    /// its own. (A host has as many ports as it likes.)
    pub waiting_each: usize,
    /// Chunks of one host waiting. Under a full window
    /// ([`MAX_WINDOW`]) a fetch that has grown to one could never be
    /// answered whole.
    pub chunks_each: u32,
}

impl Default for Limits {
    /// Two hundred and fifty-six requests waiting, thirty-two of one
    /// host (more than a node asks one peer for at once, blocks and
    /// runs of headers together), and two full windows of chunks for
    /// it, at 8,192 chunks a second.
    fn default() -> Limits {
        Limits { rate: 8192, waiting: 256, waiting_each: 32, chunks_each: 2 * MAX_WINDOW }
    }
}

/// Chunks sent at once after idleness, before the pace holds.
pub const BURST: u64 = 32;

/// The addresses that are one host with `a`: every port of its address,
/// but of this machine's own address, where each port is its own.
fn host(a: &SocketAddr) -> (SocketAddr, SocketAddr) {
    match a.ip().is_loopback() {
        true => (*a, *a),
        false => (SocketAddr::new(a.ip(), 0), SocketAddr::new(a.ip(), u16::MAX)),
    }
}

struct Job {
    to: SocketAddr,
    transfer: u64,
    name: [u8; MAX_NAME],
    name_len: u8,
    /// The runs still to send, the first of them from where it has got
    /// to, each with the number of its first chunk's ask.
    runs: [(Range, u32); MAX_RANGES],
    n: usize,
    /// The run being sent.
    run: usize,
    /// Chunks still to send.
    left: u32,
}

impl Job {
    /// Adds a run after the others: joined to the last if it follows it
    /// both as chunks and as asks. False, and nothing added, when there
    /// is no room.
    fn push(&mut self, r: Range, seq: u32) -> bool {
        if self.n > self.run {
            let (last, last_seq) = &mut self.runs[self.n - 1];
            if last.start.checked_add(last.count as u32) == Some(r.start)
                && last_seq.wrapping_add(last.count as u32) == seq
                && let Some(count) = last.count.checked_add(r.count)
            {
                last.count = count;
                self.left += r.count as u32;
                return true;
            }
        }
        if self.n == MAX_RANGES {
            return false;
        }
        self.runs[self.n] = (r, seq);
        self.n += 1;
        self.left += r.count as u32;
        true
    }

    /// Adds a request's runs, all or none.
    fn extend(&mut self, get: &Get<'_>) -> bool {
        let before = (self.runs, self.n, self.left, self.run);
        // Sent runs make room for new ones.
        self.runs.copy_within(self.run..self.n, 0);
        (self.n, self.run) = (self.n - self.run, 0);
        let mut seq = get.seq;
        for r in get.ranges.as_slice() {
            if !self.push(*r, seq) {
                (self.runs, self.n, self.left, self.run) = before;
                return false;
            }
            seq = seq.wrapping_add(r.count as u32);
        }
        true
    }
}

/// A chunk to send.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Send {
    pub to: SocketAddr,
    pub transfer: u64,
    name: [u8; MAX_NAME],
    name_len: u8,
    pub index: u32,
    /// The number of the ask this chunk answers.
    pub seq: u32,
}

impl Send {
    /// The name the object was asked for by.
    pub fn name(&self) -> &[u8] {
        &self.name[..self.name_len as usize]
    }
}

/// What to do now.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Next {
    /// Send this chunk, and ask again.
    Send(Send),
    /// Nothing may be sent before this time.
    Wait(Micros),
    /// Nothing is waiting.
    Idle,
}

/// Why a request was not taken.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Refused {
    /// It does not carry the token its address was given.
    Token,
    /// Too much is waiting already, for this address or for all.
    Full,
}

pub struct Serve {
    limits: Limits,
    /// Each address's requests, in the order they came.
    queues: BTreeMap<SocketAddr, VecDeque<Job>>,
    /// Requests waiting, in all.
    jobs: usize,
    /// The address served last: the turn passes to the next after it.
    last: Option<SocketAddr>,
    /// The address of each host served last, by the host's first:
    /// whose turn it is among a host's addresses.
    ports: BTreeMap<SocketAddr, SocketAddr>,
    /// Microseconds a chunk.
    cost: Micros,
    /// The time the next chunk may go, were there no burst: it runs
    /// ahead of the clock by a chunk's cost for each chunk sent, and is
    /// never let fall more than a burst behind it. It may be one time
    /// for several that serve ([`Serve::sharing`]): then the rate is
    /// that of all of them together, whichever of them has the work.
    due: std::sync::Arc<std::sync::atomic::AtomicU64>,
}

impl Serve {
    /// Serving `rate` chunks a second at most, within the usual bounds
    /// on what waits.
    pub fn new(rate: u32) -> Serve {
        Serve::with(Limits { rate, ..Limits::default() })
    }

    /// Serving within `limits`.
    pub fn with(limits: Limits) -> Serve {
        assert!(limits.rate > 0 && limits.waiting > 0 && limits.waiting_each > 0);
        assert!(limits.chunks_each >= MAX_WINDOW, "room for a full window");
        Serve {
            limits,
            queues: BTreeMap::new(),
            jobs: 0,
            last: None,
            ports: BTreeMap::new(),
            cost: (SECOND / limits.rate as u64).max(1),
            due: Default::default(),
        }
    }

    /// The same, keeping its pace by `due`, which others keep theirs
    /// by too: the rate is what all of them send together. So that of
    /// the workers of a node, each with the addresses that are its
    /// own, one that has all the asking sends at the whole rate, and
    /// none of it is kept for workers nobody is asking.
    pub fn sharing(mut self, due: std::sync::Arc<std::sync::atomic::AtomicU64>) -> Serve {
        self.due = due;
        self
    }

    /// Requests waiting.
    pub fn waiting(&self) -> usize {
        self.jobs
    }

    /// Takes a request from `from`, if it carries `from`'s token and
    /// there is room.
    pub fn get(&mut self, tokens: &Tokens, from: SocketAddr, get: &Get<'_>) -> Result<(), Refused> {
        if !tokens.check(&from, get.token) {
            return Err(Refused::Token);
        }
        let l = self.limits;
        let (first, last) = host(&from);
        let (mine, chunks) = self
            .queues
            .range(first..=last)
            .fold((0, 0), |(n, chunks), (_, q)| (n + q.len(), chunks + q.iter().map(|j| j.left).sum::<u32>()));
        if chunks + get.ranges.chunks() > l.chunks_each {
            return Err(Refused::Full);
        }
        // More of a fetch its address has a request waiting for: one
        // request with it, while there is room in that one. (Whichever
        // of its requests that is: a node fetches several things of a
        // peer at once, and more of the first is asked for while the
        // last waits.)
        let same = |j: &&mut Job| j.transfer == get.transfer && j.name[..j.name_len as usize] == *get.name;
        if let Some(j) = self.queues.get_mut(&from).and_then(|q| q.iter_mut().rev().find(same))
            && j.extend(get)
        {
            return Ok(());
        }
        if self.jobs >= l.waiting || mine >= l.waiting_each {
            return Err(Refused::Full);
        }
        let mut name = [0; MAX_NAME];
        name[..get.name.len()].copy_from_slice(get.name);
        let mut job = Job {
            to: from,
            transfer: get.transfer,
            name,
            name_len: get.name.len() as u8,
            runs: [(Range::default(), 0); MAX_RANGES],
            n: 0,
            run: 0,
            left: 0,
        };
        job.extend(get);
        self.queues.entry(from).or_default().push_back(job);
        self.jobs += 1;
        Ok(())
    }

    /// Forgets what `to` is still to be sent of the fetch `transfer`:
    /// there is no such object, or no more of it.
    pub fn cancel(&mut self, to: SocketAddr, transfer: u64) {
        if let Some(q) = self.queues.get_mut(&to) {
            let before = q.len();
            q.retain(|j| j.transfer != transfer);
            self.jobs -= before - q.len();
            if q.is_empty() {
                self.queues.remove(&to);
            }
        }
    }

    /// The address whose turn it is: the next after the one served
    /// last, in the order of addresses, and round again from the first.
    /// (The next host's: a host that asks from many ports has one turn
    /// among the hosts, which its ports take one after another.)
    fn turn(&self) -> Option<SocketAddr> {
        let after =
            self.last.and_then(|last| self.queues.range((Bound::Excluded(host(&last).1), Bound::Unbounded)).next());
        let to = after.or_else(|| self.queues.iter().next()).map(|(to, _)| *to)?;
        // (The port after the one of that host served last: counted
        // by the turns of all hosts together, a port could be passed
        // over for ever.)
        let (first, last) = host(&to);
        let after = self.ports.get(&first).and_then(|served| {
            self.queues.range((Bound::Excluded(*served), Bound::Included(last))).next().map(|(to, _)| *to)
        });
        Some(after.unwrap_or(to))
    }

    /// What to send at `now`.
    pub fn next(&mut self, now: Micros) -> Next {
        let Some(to) = self.turn() else {
            return Next::Idle;
        };
        // Never more than a burst behind the clock. (Taken from the
        // others that keep this pace, if one of them took it first.)
        use std::sync::atomic::Ordering::Relaxed;
        loop {
            let was = self.due.load(Relaxed);
            let due = was.max(now.saturating_sub((BURST - 1) * self.cost));
            if due > now {
                return Next::Wait(due);
            }
            if self.due.compare_exchange(was, due + self.cost, Relaxed, Relaxed).is_ok() {
                break;
            }
        }
        let queue = self.queues.get_mut(&to).expect("its turn");
        // An address's requests one after another, the first first.
        let j = queue.front_mut().expect("no address waits with nothing");
        let (r, seq) = &mut j.runs[j.run];
        let send =
            Send { to: j.to, transfer: j.transfer, name: j.name, name_len: j.name_len, index: r.start, seq: *seq };
        // The run is what is left of it.
        r.start = r.start.wrapping_add(1);
        r.count -= 1;
        *seq = seq.wrapping_add(1);
        j.left -= 1;
        if r.count == 0 {
            j.run += 1;
        }
        if j.left == 0 {
            queue.pop_front();
            self.jobs -= 1;
            if queue.is_empty() {
                self.queues.remove(&to);
            }
        }
        self.last = Some(to);
        // (Hosts that ask no more are forgotten when they are most of
        // those remembered.)
        if self.ports.len() > 2 * self.queues.len() + 16 {
            let queues = &self.queues;
            self.ports.retain(|first, _| queues.range(*first..=host(first).1).next().is_some());
        }
        self.ports.insert(host(&to).0, to);
        Next::Send(send)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::transport::wire::Ranges;

    fn addr(n: u8) -> SocketAddr {
        SocketAddr::from(([10, 0, 0, n], 4000))
    }

    fn ranges(indexes: impl IntoIterator<Item = u32>) -> Ranges {
        let mut r = Ranges::new();
        for i in indexes {
            assert!(r.push(i));
        }
        r
    }

    fn get<'a>(tokens: &Tokens, from: SocketAddr, transfer: u64, name: &'a [u8], r: Ranges) -> Get<'a> {
        // Asks numbered as the chunks are, so that chunks that follow are
        // asks that follow.
        Get { token: tokens.issue(&from), transfer, seq: r.as_slice()[0].start, name, ranges: r }
    }

    /// Everything waiting, with the clock far enough on that the pace
    /// never holds.
    fn drain(s: &mut Serve) -> Vec<(u8, u64, u32)> {
        let mut out = Vec::new();
        let mut now = 1 << 40;
        loop {
            match s.next(now) {
                Next::Send(x) => {
                    out.push((x.to.ip().to_string().rsplit('.').next().unwrap().parse().unwrap(), x.transfer, x.index))
                }
                Next::Wait(t) => now = t,
                Next::Idle => return out,
            }
        }
    }

    #[test]
    fn a_request_without_its_token_is_not_served() {
        let tokens = Tokens::new([1; 32]);
        let mut s = Serve::new(1000);
        let g = get(&tokens, addr(1), 5, b"x", ranges(0..4));
        // The token of another address, and none.
        assert_eq!(s.get(&tokens, addr(2), &g), Err(Refused::Token));
        assert_eq!(s.get(&tokens, addr(1), &Get { token: 0, ..g }), Err(Refused::Token));
        assert_eq!((s.waiting(), s.next(0)), (0, Next::Idle));
        assert_eq!(s.get(&tokens, addr(1), &g), Ok(()));
        let sent = drain(&mut s);
        assert_eq!(sent, [(1, 5, 0), (1, 5, 1), (1, 5, 2), (1, 5, 3)]);
    }

    #[test]
    fn an_addresss_chunks_go_in_the_order_asked() {
        let tokens = Tokens::new([1; 32]);
        let mut s = Serve::new(1000);
        s.get(&tokens, addr(1), &get(&tokens, addr(1), 5, b"x", ranges([7, 8, 2, 30, 31, 32]))).unwrap();
        s.get(&tokens, addr(1), &get(&tokens, addr(1), 5, b"x", ranges([3, 4]))).unwrap();
        s.get(&tokens, addr(1), &get(&tokens, addr(1), 6, b"y", ranges([0]))).unwrap();
        let sent = drain(&mut s);
        assert_eq!(
            sent,
            [(1, 5, 7), (1, 5, 8), (1, 5, 2), (1, 5, 30), (1, 5, 31), (1, 5, 32), (1, 5, 3), (1, 5, 4), (1, 6, 0)]
        );
    }

    #[test]
    fn more_of_the_same_fetch_is_one_request() {
        let tokens = Tokens::new([1; 32]);
        let mut s = Serve::new(1000);
        // A fetch asking eight at a time, far more often than requests
        // may wait.
        s.get(&tokens, addr(1), &get(&tokens, addr(1), 5, b"x", ranges(0..64))).unwrap();
        let Next::Send(first) = s.next(1 << 40) else { panic!() };
        assert_eq!(first.index, 0);
        for k in 8..100 {
            s.get(&tokens, addr(1), &get(&tokens, addr(1), 5, b"x", ranges(8 * k..8 * k + 8))).unwrap();
            assert_eq!(s.waiting(), 1);
        }
        // Lost ones asked again among them: still in the order asked.
        s.get(&tokens, addr(1), &get(&tokens, addr(1), 5, b"x", ranges([3, 4]))).unwrap();
        // Another fetch, or another name, is another request; and what
        // comes after it does not join what came before it.
        s.get(&tokens, addr(1), &get(&tokens, addr(1), 6, b"x", ranges(0..2))).unwrap();
        s.get(&tokens, addr(1), &get(&tokens, addr(1), 6, b"y", ranges(0..2))).unwrap();
        // (More of the first, asked for after them, is of the first.)
        s.get(&tokens, addr(1), &get(&tokens, addr(1), 5, b"x", ranges([9]))).unwrap();
        assert_eq!(s.waiting(), 3);
        let sent: Vec<(u64, u32)> = drain(&mut s).iter().map(|x| (x.1, x.2)).collect();
        let mut want: Vec<(u64, u32)> = (1..800).map(|i| (5, i)).collect();
        want.extend([(5, 3), (5, 4), (5, 9), (6, 0), (6, 1), (6, 0), (6, 1)]);
        assert_eq!(sent, want);
        // Each chunk goes with the number of its ask: the request's, and
        // one more for each chunk after its first, over all its runs.
        let g = |seq, r| Get { seq, ..get(&tokens, addr(2), 1, b"x", r) };
        s.get(&tokens, addr(2), &g(100, ranges([7, 8, 3]))).unwrap();
        s.get(&tokens, addr(2), &g(103, ranges([4, 5]))).unwrap();
        // Chunks that follow, asks that do not: not one run.
        s.get(&tokens, addr(2), &g(200, ranges([6]))).unwrap();
        s.get(&tokens, addr(2), &g(u32::MAX, ranges([0, 1]))).unwrap();
        assert_eq!(s.waiting(), 1);
        let mut sent = Vec::new();
        while let Next::Send(x) = s.next(1 << 41) {
            sent.push((x.index, x.seq));
        }
        assert_eq!(sent, [(7, 100), (8, 101), (3, 102), (4, 103), (5, 104), (6, 200), (0, u32::MAX), (1, 0)]);
        // More runs than one request holds: another request.
        for k in 0..MAX_RANGES as u32 + 1 {
            s.get(&tokens, addr(3), &get(&tokens, addr(3), 1, b"x", ranges([2 * k]))).unwrap();
        }
        assert_eq!(s.waiting(), 2);
        assert_eq!(drain(&mut s).len(), MAX_RANGES + 1);
        // More of a fetch that does not all fit what is left of its
        // request, some of it sent already: the request is as it was,
        // and goes on from where it was.
        s.get(&tokens, addr(4), &get(&tokens, addr(4), 1, b"x", ranges((0..MAX_RANGES as u32).map(|k| 2 * k))))
            .unwrap();
        let Next::Send(first) = s.next(1 << 42) else { panic!() };
        assert_eq!(first.index, 0);
        s.get(&tokens, addr(4), &get(&tokens, addr(4), 1, b"x", ranges([1000, 2000]))).unwrap();
        assert_eq!(s.waiting(), 2);
        let sent: Vec<u32> = drain(&mut s).iter().map(|x| x.2).collect();
        let mut want: Vec<u32> = (1..MAX_RANGES as u32).map(|k| 2 * k).collect();
        want.extend([1000, 2000]);
        assert_eq!(sent, want);
    }

    #[test]
    fn addresses_take_turns() {
        let tokens = Tokens::new([1; 32]);
        let mut s = Serve::new(1000);
        s.get(&tokens, addr(1), &get(&tokens, addr(1), 1, b"x", ranges(0..6))).unwrap();
        s.get(&tokens, addr(2), &get(&tokens, addr(2), 2, b"x", ranges(0..2))).unwrap();
        s.get(&tokens, addr(1), &get(&tokens, addr(1), 1, b"x", ranges(6..8))).unwrap();
        s.get(&tokens, addr(3), &get(&tokens, addr(3), 3, b"x", ranges(0..3))).unwrap();
        let sent = drain(&mut s);
        let who: Vec<u8> = sent.iter().map(|x| x.0).collect();
        assert_eq!(who, [1, 2, 3, 1, 2, 3, 1, 3, 1, 1, 1, 1, 1]);
        // And each one's own are in order.
        for a in 1..=3 {
            let mine: Vec<u32> = sent.iter().filter(|x| x.0 == a).map(|x| x.2).collect();
            assert!(mine.is_sorted(), "{mine:?}");
        }
        // A host that asks from four ports has one turn in two with a
        // host that asks from one, not four in five.
        for p in 0..4u16 {
            let from = SocketAddr::from(([10, 0, 0, 7], 4000 + p));
            s.get(&tokens, from, &get(&tokens, from, p as u64, b"x", ranges(0..5))).unwrap();
        }
        s.get(&tokens, addr(9), &get(&tokens, addr(9), 1, b"x", ranges(0..10))).unwrap();
        let sent = drain(&mut s);
        let who: Vec<u8> = sent.iter().map(|x| x.0).collect();
        assert_eq!(who[..20].iter().filter(|a| **a == 9).count(), 10, "{who:?}");
        assert_eq!(who.len(), 30);
        // And its ports take that turn one after another, none of
        // them passed over while another has it twice.
        let ports: Vec<u64> = sent.iter().filter(|x| x.0 == 7).map(|x| x.1).collect();
        assert_eq!(ports[..8], [0, 1, 2, 3, 0, 1, 2, 3], "{ports:?}");
    }

    #[test]
    fn what_waits_is_bounded() {
        let tokens = Tokens::new([1; 32]);
        let l = Limits { rate: 1000, waiting: 64, waiting_each: 8, ..Limits::default() };
        let mut s = Serve::with(l);
        // Requests of one address.
        for i in 0..l.waiting_each as u64 {
            assert_eq!(s.get(&tokens, addr(1), &get(&tokens, addr(1), i, b"x", ranges(0..1))), Ok(()));
        }
        assert_eq!(s.get(&tokens, addr(1), &get(&tokens, addr(1), 99, b"x", ranges(0..1))), Err(Refused::Full));
        // Nor from another port of its address: a host is one, however
        // many ports it asks from. (But on this machine, where each
        // port is another node.)
        let port = |host: [u8; 4], port: u16| SocketAddr::from((host, port));
        let other = port([10, 0, 0, 1], 4001);
        assert_eq!(s.get(&tokens, other, &get(&tokens, other, 99, b"x", ranges(0..1))), Err(Refused::Full));
        for p in 0..2 * l.waiting_each as u16 {
            let here = port([127, 0, 0, 1], 5000 + p);
            assert_eq!(s.get(&tokens, here, &get(&tokens, here, 1, b"x", ranges(0..1))), Ok(()));
        }
        assert_eq!(drain(&mut s).len(), 3 * l.waiting_each);
        for i in 0..l.waiting_each as u64 {
            assert_eq!(s.get(&tokens, addr(1), &get(&tokens, addr(1), i, b"x", ranges(0..1))), Ok(()));
        }
        // Chunks of one address: two windows, and not one more.
        let window = ranges(0..MAX_WINDOW);
        assert_eq!(s.get(&tokens, addr(2), &get(&tokens, addr(2), 1, b"x", window)), Ok(()));
        assert_eq!(s.get(&tokens, addr(2), &get(&tokens, addr(2), 2, b"x", ranges(0..MAX_WINDOW - 1))), Ok(()));
        assert_eq!(s.get(&tokens, addr(2), &get(&tokens, addr(2), 3, b"x", ranges(0..2))), Err(Refused::Full));
        assert_eq!(s.get(&tokens, addr(2), &get(&tokens, addr(2), 3, b"x", ranges(0..1))), Ok(()));
        // Requests in all.
        let mut n = s.waiting();
        let mut a = 10;
        while n < l.waiting {
            assert_eq!(s.get(&tokens, addr(a), &get(&tokens, addr(a), 1, b"x", ranges(0..1))), Ok(()));
            n += 1;
            a += 1;
        }
        assert_eq!(s.get(&tokens, addr(200), &get(&tokens, addr(200), 1, b"x", ranges(0..1))), Err(Refused::Full));
        // Once sent, there is room again.
        let sent = drain(&mut s);
        assert_eq!(sent.len(), l.waiting_each + 2 * MAX_WINDOW as usize + (l.waiting - l.waiting_each - 3));
        assert_eq!(s.get(&tokens, addr(200), &get(&tokens, addr(200), 1, b"x", ranges(0..1))), Ok(()));
    }

    /// The bounds are the node's to set: a node many lean on holds more
    /// for more of them, and whose turn it is costs no more to find.
    #[test]
    fn a_node_that_serves_many_sets_its_bounds_higher() {
        let tokens = Tokens::new([1; 32]);
        let limits = Limits { rate: 1_000_000, waiting: 5000, waiting_each: 2, chunks_each: MAX_WINDOW };
        let mut s = Serve::with(limits);
        let who = |n: u32| SocketAddr::from(([10, (n >> 16) as u8, (n >> 8) as u8, n as u8], 4000));
        for n in 0..5000 {
            assert_eq!(s.get(&tokens, who(n), &get(&tokens, who(n), 1, b"x", ranges(0..3))), Ok(()), "{n}");
        }
        assert_eq!(s.waiting(), 5000);
        assert_eq!(s.get(&tokens, who(5000), &get(&tokens, who(5000), 1, b"x", ranges(0..3))), Err(Refused::Full));
        // Its own bounds for one address: two requests, one window.
        let again = |transfer, r| get(&tokens, who(7), transfer, b"x", r);
        assert_eq!(s.get(&tokens, who(7), &again(2, ranges(0..MAX_WINDOW))), Err(Refused::Full));
        s.cancel(who(8), 1);
        assert_eq!(s.get(&tokens, who(7), &again(2, ranges(0..3))), Ok(()));
        s.cancel(who(9), 1);
        assert_eq!(s.get(&tokens, who(7), &again(3, ranges(0..3))), Err(Refused::Full));
        // Everyone gets a chunk before anyone gets a second.
        let mut now = 1 << 40;
        let mut first_round = std::collections::BTreeSet::new();
        for _ in 0..4998 {
            match s.next(now) {
                Next::Send(x) => assert!(first_round.insert(x.to), "{} twice", x.to),
                Next::Wait(t) => now = t,
                Next::Idle => panic!(),
            }
        }
        let mut sent = first_round.len();
        loop {
            match s.next(now) {
                Next::Send(_) => sent += 1,
                Next::Wait(t) => now = t,
                Next::Idle => break,
            }
        }
        assert_eq!((sent, s.waiting()), (4998 * 3 + 3, 0));
    }

    #[test]
    fn a_cancelled_fetch_sends_no_more() {
        let tokens = Tokens::new([1; 32]);
        let mut s = Serve::new(1000);
        s.get(&tokens, addr(1), &get(&tokens, addr(1), 1, b"x", ranges(0..50))).unwrap();
        s.get(&tokens, addr(1), &get(&tokens, addr(1), 2, b"y", ranges(0..2))).unwrap();
        s.get(&tokens, addr(2), &get(&tokens, addr(2), 1, b"x", ranges(0..2))).unwrap();
        let Next::Send(first) = s.next(1 << 40) else { panic!() };
        assert_eq!((first.to, first.transfer, first.index, first.name()), (addr(1), 1, 0, b"x".as_slice()));
        s.cancel(addr(1), 1);
        let sent = drain(&mut s);
        assert_eq!(sent, [(2, 1, 0), (1, 2, 0), (2, 1, 1), (1, 2, 1)]);
    }

    #[test]
    fn chunks_go_at_the_rate_after_a_short_burst() {
        let tokens = Tokens::new([1; 32]);
        // A thousand a second: one a millisecond.
        let mut s = Serve::new(1000);
        s.get(&tokens, addr(1), &get(&tokens, addr(1), 1, b"x", ranges(0..1000))).unwrap();
        let start = 5 * SECOND;
        let mut now = start;
        let mut times = Vec::new();
        loop {
            match s.next(now) {
                Next::Send(_) => times.push(now - start),
                Next::Wait(t) => {
                    assert!(t > now);
                    now = t;
                }
                Next::Idle => break,
            }
        }
        assert_eq!(times.len(), 1000);
        // The burst at once, then one each millisecond.
        assert!(times[..BURST as usize].iter().all(|&t| t == 0));
        for (k, &t) in times.iter().enumerate().skip(BURST as usize) {
            assert_eq!(t, (k as u64 + 1 - BURST) * 1000, "chunk {k}");
        }
        // Idle for a long while earns one burst, not the whole while.
        s.get(&tokens, addr(1), &get(&tokens, addr(1), 1, b"x", ranges(0..100))).unwrap();
        let later = now + 60 * SECOND;
        let mut at_once = 0;
        while let Next::Send(_) = s.next(later) {
            at_once += 1;
        }
        assert_eq!(at_once, BURST);
        assert_eq!(s.next(later), Next::Wait(later + 1000));
        // Nor is a caller that comes late owed what it missed.
        let much_later = later + 60 * SECOND;
        let mut at_once = 0;
        while let Next::Send(_) = s.next(much_later) {
            at_once += 1;
        }
        assert_eq!(at_once, BURST);
    }
}
