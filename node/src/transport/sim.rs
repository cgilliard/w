//! Tests: a network that loses, repeats, delays and reorders as it is
//! told to, and fetches run over it.
//!
//! Every run is a seed's: the same seed loses the same datagrams.

use std::cmp::Reverse;
use std::collections::BinaryHeap;
use std::net::SocketAddr;

use super::fetch::{Fetch, Poll, Stats, Taken, Why};
use super::path::Path;
use super::serve::{Next, Serve};
use super::token::Tokens;
use super::wire::{Chunk, Get, Gone, MAX_CHUNK, MAX_GET, Ranges};
use super::*;
use crate::test_util::Rng;

/// One direction of a path.
#[derive(Clone, Copy, Debug)]
struct Link {
    /// Datagrams lost, in ten thousand.
    loss: u32,
    /// Datagrams delivered twice, in ten thousand.
    twice: u32,
    delay: Micros,
    /// Up to this much more, for each datagram alone: so they overtake.
    jitter: Micros,
    /// Datagrams a second through the narrowest place, and how many may
    /// wait there; one that finds it full is dropped. Zero: no limit.
    rate: u32,
    queue: u32,
}

const CLEAN: Link = Link { loss: 0, twice: 0, delay: 20 * MILLI, jitter: 0, rate: 0, queue: 0 };

/// An arrival: the time, a count to keep order, whether towards the
/// asking side, the bytes.
type Arrival = (Micros, u64, bool, Vec<u8>);

struct Net {
    rng: Rng,
    /// Arrivals, the soonest first.
    heap: BinaryHeap<Reverse<Arrival>>,
    n: u64,
    up: Link,
    down: Link,
    /// When the narrow place of each direction is next free.
    free: [Micros; 2],
    dropped: u64,
}

impl Net {
    fn send(&mut self, now: Micros, down: bool, bytes: &[u8]) {
        let link = if down { self.down } else { self.up };
        let mut leaves = now;
        if link.rate > 0 {
            let each = SECOND / link.rate as u64;
            let free = &mut self.free[down as usize];
            if free.saturating_sub(now) > link.queue as u64 * each {
                self.dropped += 1;
                return;
            }
            *free = (*free).max(now) + each;
            leaves = *free;
        }
        if self.rng.next_u64() % 10_000 < link.loss as u64 {
            self.dropped += 1;
            return;
        }
        let copies = 1 + (self.rng.next_u64() % 10_000 < link.twice as u64) as usize;
        for _ in 0..copies {
            let at = leaves + link.delay + self.rng.next_u64() % (link.jitter + 1);
            self.heap.push(Reverse((at, self.n, down, bytes.to_vec())));
            self.n += 1;
        }
    }
}

/// How the serving side behaves.
#[derive(Clone, Copy, Debug, PartialEq)]
enum Server {
    Honest,
    /// Says it has no such object.
    Without,
    /// Sends this many chunks and then nothing more, until the fetch is
    /// taken up again.
    Stops(u64),
    /// Sends a chunk claiming another length once this many have gone.
    Lies(u64),
    /// The first sending of each of the object's last so many chunks
    /// never arrives: the end of it is lost in one go, with nothing
    /// asked after it to show the loss.
    LosesEnd(u32),
}

struct Setup {
    object: Vec<u8>,
    /// Whether the asking side knows the length beforehand.
    known: bool,
    up: Link,
    down: Link,
    seed: u64,
    server: Server,
    /// Chunks a second the serving side sends at most.
    rate: u32,
    path: Path,
    /// Chunks a third party sends the asking side, not knowing the
    /// fetch's number: one each millisecond from the start.
    forged: u32,
    /// Times a fetch given up for silence is taken up again.
    resumes: u32,
}

impl Setup {
    fn new(len: usize, seed: u64) -> Setup {
        let mut rng = Rng::new(seed ^ 0x5eed);
        Setup {
            object: (0..len).map(|_| rng.next_u64() as u8).collect(),
            known: true,
            up: CLEAN,
            down: CLEAN,
            seed,
            server: Server::Honest,
            rate: 8192,
            path: Path::new(),
            forged: 0,
            resumes: 0,
        }
    }

    fn both(mut self, link: Link) -> Setup {
        (self.up, self.down) = (link, link);
        self
    }
}

struct Outcome {
    end: Poll,
    /// The object arrived, and is the object.
    intact: bool,
    time: Micros,
    stats: Stats,
    path: Path,
    /// Chunks the serving side sent.
    served: u64,
    /// Forged chunks that reached the fetch, and were refused by it.
    refused: u64,
    /// Times it was taken up again.
    resumed: u32,
    /// Bytes a second, as the fetch reported at its end.
    rate: u64,
}

const GET: u8 = 0;
const CHUNK: u8 = 1;
const GONE: u8 = 2;

fn run(s: &Setup) -> Outcome {
    let asker: SocketAddr = "10.0.0.1:4000".parse().unwrap();
    let tokens = Tokens::new([7; 32]);
    let token = tokens.issue(&asker);
    let mut net =
        Net { rng: Rng::new(s.seed), heap: BinaryHeap::new(), n: 0, up: s.up, down: s.down, free: [0; 2], dropped: 0 };
    let mut transfer = net.rng.next_u64();
    let mut resumed = 0;
    let mut stats = Stats::default();
    let len = s.object.len() as u32;
    let mut now: Micros = 1000 * SECOND;
    let start = now;
    let mut fetch = Fetch::new(transfer, s.known.then_some(len), 4 << 20, s.path, now);
    let mut serve = Serve::new(s.rate);
    let mut served = 0u64;
    let mut refused = 0u64;
    let mut sent_once = vec![false; chunk_count(len) as usize];
    let mut ranges = Ranges::new();
    let mut buf = [0u8; 1 + MAX_CHUNK + MAX_GET];
    // The third party's chunks: the right shape, the right place, the
    // wrong number.
    for k in 0..s.forged {
        let index = k % chunk_count(len);
        let data = vec![0xee; chunk_len(len, index).unwrap()];
        buf[0] = CHUNK;
        let n =
            Chunk { transfer: transfer ^ (1 + k as u64), seq: index, len, index, data: &data }.encode(&mut buf[1..]);
        net.heap.push(Reverse((now + k as u64 * MILLI, net.n, true, buf[..1 + n].to_vec())));
        net.n += 1;
    }
    let end = loop {
        assert!(now - start < 6 * 3600 * SECOND, "six hours, and neither here nor given up");
        // The asking side.
        let mut over = None;
        let wake = loop {
            match fetch.poll(now, &mut ranges) {
                Poll::Ask(seq) => {
                    buf[0] = GET;
                    let n = Get { token, transfer, seq, name: b"object", ranges }.encode(&mut buf[1..]);
                    net.send(now, false, &buf[..1 + n]);
                }
                Poll::Wait(t) => {
                    assert!(t > now);
                    break t;
                }
                Poll::Failed(Why::Silent) if resumed < s.resumes => {
                    resumed += 1;
                    let old = fetch.stats();
                    stats.asked += old.asked;
                    stats.asked_again += old.asked_again;
                    stats.spare += old.spare;
                    stats.silences += old.silences;
                    serve.cancel(asker, transfer);
                    transfer = net.rng.next_u64();
                    fetch.resume(transfer, fetch.path(), now);
                }
                end => {
                    over = Some(end);
                    break 0;
                }
            }
        };
        if let Some(end) = over {
            break end;
        }
        // The serving side.
        let serve_wake = loop {
            match serve.next(now) {
                Next::Send(x) => {
                    assert_eq!((x.to, x.name()), (asker, b"object".as_slice()));
                    if s.server == Server::Without {
                        buf[0] = GONE;
                        let n = Gone { transfer: x.transfer }.encode(&mut buf[1..]);
                        net.send(now, true, &buf[..1 + n]);
                        serve.cancel(x.to, x.transfer);
                        continue;
                    }
                    if matches!(s.server, Server::Stops(n) if served >= n && resumed == 0) {
                        continue;
                    }
                    let Some(data) = chunk_of(&s.object, x.index) else {
                        serve.cancel(x.to, x.transfer);
                        continue;
                    };
                    if let Server::LosesEnd(n) = s.server
                        && x.index + n >= chunk_count(len)
                        && !std::mem::replace(&mut sent_once[x.index as usize], true)
                    {
                        served += 1;
                        continue;
                    }
                    let lie = matches!(s.server, Server::Lies(n) if served == n);
                    buf[0] = CHUNK;
                    let n = if lie {
                        let data = vec![0; chunk_len(len + 1, x.index).unwrap()];
                        Chunk { transfer: x.transfer, seq: x.seq, len: len + 1, index: x.index, data: &data }
                            .encode(&mut buf[1..])
                    } else {
                        Chunk { transfer: x.transfer, seq: x.seq, len, index: x.index, data }.encode(&mut buf[1..])
                    };
                    net.send(now, true, &buf[..1 + n]);
                    served += 1;
                }
                Next::Wait(t) => break t,
                Next::Idle => break Micros::MAX,
            }
        };
        // On to whatever is first, and all that arrives then.
        let arrival = net.heap.peek().map_or(Micros::MAX, |Reverse(e)| e.0);
        now = wake.min(serve_wake).min(arrival).max(now);
        while net.heap.peek().is_some_and(|Reverse(e)| e.0 <= now) {
            let Reverse((_, _, down, bytes)) = net.heap.pop().unwrap();
            match (down, bytes[0]) {
                (false, GET) => {
                    // Refused when too much waits: the same as lost.
                    let _ = serve.get(&tokens, asker, &Get::decode(&bytes[1..]).unwrap());
                }
                (true, CHUNK) => {
                    let c = Chunk::decode(&bytes[1..]).unwrap();
                    match fetch.chunk(now, &c) {
                        Ok(Taken::New | Taken::Spare) => {}
                        Err(_) => refused += 1,
                    }
                }
                (true, GONE) => {
                    let g = Gone::decode(&bytes[1..]).unwrap();
                    if g.transfer == fetch.transfer() {
                        fetch.gone();
                    }
                }
                _ => unreachable!(),
            }
        }
    };
    let (last, path, rate) = (fetch.stats(), fetch.path(), fetch.rate(now));
    let stats = Stats {
        asked: stats.asked + last.asked,
        asked_again: stats.asked_again + last.asked_again,
        spare: stats.spare + last.spare,
        silences: stats.silences + last.silences,
        ..last
    };
    let intact = fetch.finish().is_some_and(|got| got == s.object);
    assert_eq!(intact, end == Poll::Done, "done is intact, and nothing else is");
    Outcome { end, intact, time: now - start, stats, path, served, refused, resumed, rate }
}

fn lossy(loss: u32) -> Link {
    Link { loss, ..CLEAN }
}

/// The round trip of [`CLEAN`], there and back.
const TRIP: Micros = 40 * MILLI;

#[test]
fn over_a_clean_path_nothing_is_asked_twice() {
    let c = CHUNK_BYTES;
    for len in [1, c - 1, c, c + 1, 64 * c, 64 * c + 1, 100_000, 2 << 20] {
        for known in [true, false] {
            let mut s = Setup::new(len, len as u64);
            s.known = known;
            let o = run(&s);
            let count = chunk_count(len as u32) as u64;
            assert!(o.intact, "{len} {known}");
            // Blind, the first window is asked for whether or not the
            // object has that many chunks.
            let blind = if known { 0 } else { (INITIAL_WINDOW as u64).saturating_sub(count) };
            assert_eq!(o.stats.asked, count + blind, "{len} {known}");
            assert_eq!(o.served, count, "{len} {known}");
            assert_eq!((o.stats.asked_again, o.stats.spare, o.stats.silences, o.stats.overtaken), (0, 0, 0, 0));
            // A window's worth and less: one round trip, and the time
            // the serving side spreads its chunks over.
            if count <= INITIAL_WINDOW as u64 {
                assert_eq!(o.stats.requests, 1);
                assert!(o.time <= TRIP + count * SECOND / 8192, "{len}: {}", o.time);
            }
            assert!(o.path.round_trip().is_some());
        }
    }
    // Two megabytes: the window doubles to carry it in a few round trips.
    let o = run(&Setup::new(2 << 20, 1));
    assert!(o.time < 600 * MILLI, "{}", o.time);
    assert!(!o.path.full());
    assert_eq!(o.path.window(), 1024);
    // And the next from the same peer starts where this one ended.
    let mut again = Setup::new(2 << 20, 2);
    again.path = o.path;
    let o2 = run(&again);
    assert!(o2.intact && o2.time < o.time - TRIP, "{} then {}", o.time, o2.time);
    assert_eq!(o2.stats.asked_again, 0);
}

/// Every seed's object arrives whole at these rates of loss, and what
/// is asked for is not far over what the loss itself costs.
#[test]
fn loss_is_made_up_without_much_waste() {
    // Loss in ten thousand; the most asked for, in hundredths of the
    // object's chunks; the longest a two megabyte fetch may take.
    for (loss, most, longest) in
        [(100, 106, 3 * SECOND), (500, 116, 8 * SECOND), (1000, 132, 15 * SECOND), (2000, 172, 90 * SECOND)]
    {
        for len in [1usize, 5000, 100_000, 2 << 20] {
            let seeds = if len > 1 << 20 { 6 } else { 30 };
            let (mut asked, mut time) = (0, 0);
            for seed in 0..seeds {
                let o = run(&Setup::new(len, seed).both(lossy(loss)));
                assert!(o.intact, "loss {loss}, {len} bytes, seed {seed}: {:?}", o.end);
                // Nothing arrives twice that was asked for once; and a
                // path that only loses is not taken for a full one.
                assert!(o.stats.spare <= o.stats.asked_again);
                // (Where a fifth is lost the two can look alike for a
                // round; the window is then held to what the path held,
                // and no lower.)
                assert!(loss > 500 || !o.path.full(), "loss {loss}, {len} bytes, seed {seed}");
                asked += o.stats.asked;
                time = time.max(o.time);
            }
            let count = chunk_count(len as u32) as u64 * seeds;
            if len > 1 << 20 {
                assert!(asked * 100 <= count * most, "loss {loss}: asked {asked} for {count}");
                assert!(time <= longest, "loss {loss}: {time}");
            }
            // The least it could be: each ask arrives with the chance
            // the path leaves it.
            assert!(asked >= count);
        }
    }
}

/// Half of everything lost, each way: a fetch either arrives whole or is
/// given up, and half arrive at least.
#[test]
fn at_the_worst_a_fetch_is_whole_or_given_up() {
    let mut whole = 0;
    for seed in 0..40 {
        let o = run(&Setup::new(50_000, seed).both(lossy(5000)));
        match o.end {
            Poll::Done => whole += 1,
            Poll::Failed(Why::Silent) => {}
            other => panic!("{other:?}"),
        }
    }
    assert!(whole >= 20, "{whole}");
}

/// Chunks that overtake one another by more places than is allowed for
/// are asked for again needlessly, at first; the allowance grows, is
/// kept for the peer, and the next fetch wastes no more. (Not nothing:
/// the allowance is let down a little each round, to find out whether
/// the path still needs it.)
#[test]
fn disorder_is_learned() {
    for jitter in [5 * MILLI, 40 * MILLI] {
        let link = Link { jitter, ..CLEAN };
        let o = run(&Setup::new(2 << 20, 3).both(link));
        assert!(o.intact);
        assert_eq!(o.stats.silences, 0);
        // All that was asked again had only been overtaken.
        assert!(o.stats.asked_again > 0 && o.stats.disorders > 0);
        assert!(o.stats.spare + 8 >= o.stats.asked_again, "{:?}", o.stats);
        assert!(o.stats.asked_again * 10 < o.stats.asked, "{:?}", o.stats);
        assert!(o.path.reorder() > REORDER);
        let mut next = Setup::new(2 << 20, 4).both(link);
        next.path = o.path;
        let o2 = run(&next);
        assert!(o2.intact);
        assert!(o2.stats.asked_again <= o.stats.asked_again, "{:?} then {:?}", o.stats, o2.stats);
    }
    // A path that keeps order is not thought to lose it.
    let o = run(&Setup::new(2 << 20, 3).both(lossy(300)));
    assert_eq!((o.stats.disorders, o.path.reorder()), (0, REORDER));
}

#[test]
fn what_arrives_twice_is_taken_once() {
    let o = run(&Setup::new(2 << 20, 5).both(Link { twice: 2000, ..CLEAN }));
    let count = chunk_count(2 << 20) as u64;
    assert!(o.intact);
    assert_eq!((o.stats.asked, o.stats.asked_again, o.stats.silences, o.stats.disorders), (count, 0, 0, 0));
    assert!(o.stats.spare > count / 10 && o.served >= count);
}

/// A narrow place on the path with a short queue: the window finds what
/// it carries, and the object crosses in not much more than the time
/// the narrow place needs for it.
#[test]
fn the_window_fits_a_narrow_path() {
    for (rate, queue) in [(500, 32), (2000, 64), (200, 16)] {
        let mut s = Setup::new(1 << 20, 6);
        s.down = Link { rate, queue, ..CLEAN };
        let o = run(&s);
        let count = chunk_count(1 << 20) as u64;
        assert!(o.intact);
        let least = count * SECOND / rate as u64;
        assert!(o.time <= least + least / 2 + SECOND, "{rate}/s: {} for {least}", o.time);
        // The first burst overruns the queue once; after that little is
        // lost.
        assert!(o.stats.asked * 100 <= count * 145, "{rate}/s: {:?}", o.stats);
        assert_eq!(o.stats.disorders, 0);
        assert!(o.path.window() < 256, "{}", o.path.window());
    }
}

#[test]
fn a_peer_without_the_object_says_so_and_is_believed() {
    let mut s = Setup::new(100_000, 7);
    s.server = Server::Without;
    let o = run(&s);
    assert_eq!((o.end, o.served), (Poll::Failed(Why::Gone), 0));
    assert_eq!(o.time, TRIP);
}

#[test]
fn a_peer_that_stops_is_given_up() {
    for sent in [0, 1, 50, 300] {
        let mut s = Setup::new(1 << 20, 8);
        s.server = Server::Stops(sent);
        let o = run(&s);
        assert_eq!(o.end, Poll::Failed(Why::Silent), "{sent}");
        assert_eq!(o.stats.silences, MAX_RETRIES as u64 + 1);
        // Each silence waits twice the last, up to a minute: never
        // measured, 0.4 s doubling to 51.2 s and then the minute; once
        // measured, from a tenth of a second or a little over.
        let (least, most) = if sent == 0 { (162, 163) } else { (51, 80) };
        assert!(o.time >= least * SECOND && o.time <= most * SECOND, "{sent}: {}", o.time);
    }
}

#[test]
fn a_peer_that_lies_about_the_length_ends_the_fetch() {
    for after in [0, 10] {
        let mut s = Setup::new(100_000, 9);
        s.server = Server::Lies(after);
        // Told the length or not: the first chunk's is the length.
        s.known = after != 0;
        let o = run(&s);
        if after == 0 {
            // Believed, being the first; the true ones are then the lies.
            assert_eq!(o.end, Poll::Failed(Why::Bad));
        } else {
            assert_eq!((o.end, o.refused), (Poll::Failed(Why::Bad), 1));
        }
    }
}

/// Someone who is not on the path sends chunks of the right shape for
/// the right places. They do not know the fetch's number: nothing they
/// send is taken, and the fetch goes as if they had not.
#[test]
fn a_third_partys_chunks_are_not_taken() {
    let plain = run(&Setup::new(300_000, 11));
    let mut s = Setup::new(300_000, 11);
    s.forged = 500;
    let o = run(&s);
    assert!(o.intact);
    assert_eq!(o.refused, (o.time / MILLI + 1).min(500));
    assert_eq!((o.stats, o.time, o.path), (plain.stats, plain.time, plain.path));
}

/// Paths of every kind at once, by the seed.
#[test]
fn any_path_gives_the_object_or_gives_up() {
    let (iters, seed) = crate::test_util::fuzz_params(150, 0x7ea);
    let mut rng = Rng::new(seed);
    for i in 0..iters {
        let link = |rng: &mut Rng| Link {
            loss: [0, 0, 50, 300, 1000, 3000][rng.next_u64() as usize % 6],
            twice: [0, 0, 100, 1500][rng.next_u64() as usize % 4],
            delay: [100, 5 * MILLI, 50 * MILLI, 400 * MILLI][rng.next_u64() as usize % 4],
            jitter: [0, 0, MILLI, 30 * MILLI][rng.next_u64() as usize % 4],
            rate: [0, 0, 100, 1000, 10_000][rng.next_u64() as usize % 5],
            queue: [4, 30, 500][rng.next_u64() as usize % 3],
        };
        let mut s = Setup::new(1 + rng.next_u64() as usize % 300_000, rng.next_u64());
        (s.up, s.down) = (link(&mut rng), link(&mut rng));
        s.known = rng.next_u64().is_multiple_of(2);
        s.rate = [50, 1000, 8192, 100_000][rng.next_u64() as usize % 4];
        let o = run(&s);
        let gentle = s.up.loss <= 1000 && s.down.loss <= 1000;
        match o.end {
            Poll::Done => {}
            // Given up only where the path is very bad, or slower than
            // is worth waiting for.
            Poll::Failed(Why::Silent) => assert!(!gentle, "run {i}: {:?} {:?}", s.up, s.down),
            other => panic!("run {i}: {other:?}"),
        }
    }
}

#[test]
fn a_fetch_of_nothing_or_of_too_much_is_over_before_it_starts() {
    let mut ranges = Ranges::new();
    for len in [0, 1001] {
        let mut f = Fetch::new(1, Some(len), 1000, Path::new(), 0);
        assert_eq!(f.poll(0, &mut ranges), Poll::Failed(Why::Bad));
        assert!(ranges.is_empty() && f.finish().is_none());
    }
    // Blind, no more is asked for than the greatest length has.
    let mut f = Fetch::new(1, None, 2 * CHUNK_BYTES as u32 + 1, Path::new(), 0);
    assert_eq!(f.poll(0, &mut ranges), Poll::Ask(0));
    assert_eq!(ranges.indexes().collect::<Vec<_>>(), [0, 1, 2]);
    // And a first chunk claiming more than that is refused.
    let data = [0u8; CHUNK_BYTES];
    let over = Chunk { transfer: 1, seq: 0, len: 2 * CHUNK_BYTES as u32 + 2, index: 0, data: &data };
    assert!(f.chunk(1, &over).is_err());
    assert_eq!(f.poll(1, &mut ranges), Poll::Failed(Why::Bad));
}

/// Chunks of every shape given to a fetch directly, in any order and
/// with any claims: it never takes a wrong byte for a right one's
/// place, never fails otherwise than by saying so.
#[test]
fn a_fetch_takes_anything_without_harm() {
    let (iters, seed) = crate::test_util::fuzz_params(300, 0xfe7c);
    let mut rng = Rng::new(seed);
    let mut ranges = Ranges::new();
    for _ in 0..iters {
        let len = 1 + rng.next_u64() as u32 % 40_000;
        let object: Vec<u8> = (0..len).map(|_| rng.next_u64() as u8).collect();
        let known = rng.next_u64().is_multiple_of(2);
        let honest = !rng.next_u64().is_multiple_of(3);
        let mut f = Fetch::new(9, known.then_some(len), 50_000, Path::new(), 0);
        let mut now = 0;
        let mut asked: Vec<(u32, u32)> = Vec::new();
        let end = loop {
            now += rng.next_u64() % (300 * MILLI);
            match f.poll(now, &mut ranges) {
                Poll::Ask(seq) => asked.extend(ranges.indexes().zip(seq..)),
                Poll::Wait(t) => assert!(t > now),
                over => break over,
            }
            // Some of what was asked for, in any order; things never
            // asked for; and, from a peer that is not honest, lies.
            for _ in 0..rng.next_u64() % 40 {
                let pick = rng.next_u64();
                // (With the number of its ask, or with any.)
                let (index, seq) = match pick % 4 {
                    0 if !asked.is_empty() => asked.swap_remove(pick as usize / 4 % asked.len()),
                    1 => (pick as u32 / 4 % chunk_count(len), (pick >> 40) as u32 % 64),
                    _ if !asked.is_empty() => asked[pick as usize / 4 % asked.len()],
                    _ => continue,
                };
                let lie = !honest && pick.is_multiple_of(97);
                let claimed = if lie { 1 + (pick >> 8) as u32 % 60_000 } else { len };
                let Some(n) = chunk_len(claimed, index) else { continue };
                let data = match chunk_of(&object, index) {
                    Some(d) if !lie => d.to_vec(),
                    _ => vec![0x55; n],
                };
                let _ = f.chunk(now, &Chunk { transfer: 9, seq, len: claimed, index, data: &data });
                // Another fetch's chunk changes nothing.
                assert!(f.chunk(now, &Chunk { transfer: 8, seq, len: claimed, index, data: &data }).is_err());
            }
            let (got, of) = f.progress();
            assert!(of.is_none_or(|n| got <= n) && f.in_flight() <= MAX_WINDOW);
        };
        match end {
            // Whole only if it is the object: a lie that was believed
            // (a first chunk's length, when it was not known) ends
            // otherwise.
            Poll::Done => {
                let got = f.finish().unwrap();
                assert!(got == object || !honest);
                assert!(got.len() as u32 == len || (!known && !honest));
            }
            Poll::Failed(Why::Bad) => assert!(!honest),
            Poll::Failed(Why::Silent) => {}
            other => panic!("{other:?}"),
        }
    }
}

/// The same, over the machine's own sockets and its own clock: three
/// megabytes, sent faster than the receiving socket's buffer holds, so
/// that what the machine drops is made up.
#[test]
fn over_real_sockets() {
    use std::net::UdpSocket;
    use std::sync::Arc;
    use std::sync::atomic::{AtomicBool, Ordering};
    use std::time::{Duration, Instant};
    let object: Arc<Vec<u8>> = Arc::new({
        let mut rng = Rng::new(77);
        (0..3 << 20).map(|_| rng.next_u64() as u8).collect()
    });
    let server = UdpSocket::bind("127.0.0.1:0").unwrap();
    let client = UdpSocket::bind("127.0.0.1:0").unwrap();
    let (server_addr, client_addr) = (server.local_addr().unwrap(), client.local_addr().unwrap());
    let tokens = Tokens::new([3; 32]);
    let token = tokens.issue(&client_addr);
    let clock = Instant::now();
    let stop = Arc::new(AtomicBool::new(false));
    let serving = {
        let (object, stop) = (Arc::clone(&object), Arc::clone(&stop));
        std::thread::spawn(move || {
            let mut serve = Serve::new(100_000);
            let mut buf = [0u8; 2048];
            let mut out = [0u8; MAX_CHUNK];
            let mut sent = 0u64;
            while !stop.load(Ordering::Relaxed) {
                let now = clock.elapsed().as_micros() as Micros;
                let wait = loop {
                    match serve.next(now) {
                        Next::Send(x) => {
                            let data = chunk_of(&object, x.index).unwrap();
                            let chunk = Chunk {
                                transfer: x.transfer,
                                seq: x.seq,
                                len: object.len() as u32,
                                index: x.index,
                                data,
                            };
                            let n = chunk.encode(&mut out);
                            server.send_to(&out[..n], x.to).unwrap();
                            sent += 1;
                        }
                        Next::Wait(t) => break t - now,
                        Next::Idle => break MILLI,
                    }
                };
                server.set_read_timeout(Some(Duration::from_micros(wait.clamp(50, MILLI)))).unwrap();
                while let Ok((n, from)) = server.recv_from(&mut buf) {
                    let _ = serve.get(&tokens, from, &Get::decode(&buf[..n]).unwrap());
                    server.set_read_timeout(Some(Duration::from_micros(1))).unwrap();
                }
            }
            sent
        })
    };
    let mut fetch = Fetch::new(0x1234_5678_9abc, None, 4 << 20, Path::new(), 0);
    let mut ranges = Ranges::new();
    let mut buf = [0u8; 2048];
    let mut out = [0u8; MAX_GET];
    let end = loop {
        let now = clock.elapsed().as_micros() as Micros;
        match fetch.poll(now, &mut ranges) {
            Poll::Ask(seq) => {
                let n = Get { token, transfer: fetch.transfer(), seq, name: b"object", ranges }.encode(&mut out);
                client.send_to(&out[..n], server_addr).unwrap();
            }
            Poll::Wait(t) => {
                client.set_read_timeout(Some(Duration::from_micros((t - now).clamp(1, 20 * MILLI)))).unwrap();
                // All that is waiting, before asking for more.
                while let Ok((n, from)) = client.recv_from(&mut buf) {
                    assert_eq!(from, server_addr);
                    let now = clock.elapsed().as_micros() as Micros;
                    fetch.chunk(now, &Chunk::decode(&buf[..n]).unwrap()).unwrap();
                    client.set_read_timeout(Some(Duration::from_micros(1))).unwrap();
                }
            }
            over => break over,
        }
    };
    stop.store(true, Ordering::Relaxed);
    let sent = serving.join().unwrap();
    let stats = fetch.stats();
    println!("{:?} in {:?}: {sent} chunks sent, {stats:?}, window {}", end, clock.elapsed(), fetch.path().window());
    assert_eq!(end, Poll::Done);
    assert!(fetch.finish().unwrap() == *object);
}

/// The lines a node may be at the end of. The block crosses on each, in
/// about the time the line itself needs for it, with nothing given up;
/// and what is asked for twice is little, because the window comes to
/// fit a narrow line and is left alone on a lossy one.
#[test]
fn a_block_crosses_any_line() {
    // The line (chunks a second, where it has a limit); the object; the
    // longest it may take; the most asked for, in hundredths; whether
    // the path is narrow, to be found full.
    let block = 2 << 20;
    type Row = (&'static str, Link, usize, Micros, u64, Option<bool>);
    let rows: &[Row] = &[
        (
            "satellite, 1% lost",
            Link { delay: 300 * MILLI, loss: 100, rate: 1000, queue: 100, ..CLEAN },
            block,
            60,
            110,
            Some(false),
        ),
        (
            "satellite, 5% lost",
            Link { delay: 300 * MILLI, loss: 500, rate: 1000, queue: 100, ..CLEAN },
            block,
            120,
            120,
            Some(false),
        ),
        (
            "radio, 2 s there and back, 20% lost",
            Link { delay: SECOND, loss: 2000, rate: 20, queue: 40, ..CLEAN },
            500_000,
            600,
            175,
            None,
        ),
        ("256 kbit/s", Link { delay: 50 * MILLI, rate: 26, queue: 20, ..CLEAN }, block, 80, 115, Some(true)),
        ("64 kbit/s", Link { delay: 100 * MILLI, rate: 6, queue: 10, ..CLEAN }, block, 310, 115, Some(true)),
        ("32 kbit/s", Link { delay: 100 * MILLI, rate: 3, queue: 10, ..CLEAN }, block, 620, 120, Some(true)),
        ("9.6 kbit/s", Link { delay: 200 * MILLI, rate: 1, queue: 5, ..CLEAN }, 300_000, 290, 145, Some(true)),
        (
            "9.6 kbit/s, 10% lost",
            Link { delay: 200 * MILLI, rate: 1, queue: 5, loss: 1000, ..CLEAN },
            300_000,
            420,
            165,
            Some(true),
        ),
    ];
    for (what, link, len, longest, most, narrow) in rows {
        for seed in 0..4 {
            let mut s = Setup::new(*len, seed);
            s.down = *link;
            s.up = Link { rate: 0, ..*link };
            let o = run(&s);
            let count = chunk_count(*len as u32) as u64;
            assert!(o.intact, "{what}, seed {seed}: {:?}", o.end);
            assert!(o.time <= longest * SECOND, "{what}, seed {seed}: {} s", o.time / SECOND);
            assert!(o.stats.asked * 100 <= count * most, "{what}, seed {seed}: {:?}", o.stats);
            match narrow {
                // Found full, and the window within twice what the line
                // and its queue hold.
                Some(true) => {
                    let holds = link.queue + (link.rate as u64 * 2 * link.delay / SECOND) as u32 + 2;
                    assert!(o.path.full() && o.path.window() <= 2 * holds, "{what}: {} for {holds}", o.path.window());
                }
                // Lossy, and not held to a small window for it.
                Some(false) => assert!(o.path.window() >= INITIAL_WINDOW, "{what}: {}", o.path.window()),
                None => {}
            }
        }
    }
}

/// An object of unknown length, smaller than what is asked for blind:
/// most of what was asked for is past its end and will never come, and
/// if its one chunk is lost, it is that chunk that must be asked for
/// again, not what is past the end.
#[test]
fn a_small_object_of_unknown_length_survives_loss() {
    for len in [1usize, CHUNK_BYTES, 3 * CHUNK_BYTES + 5] {
        for seed in 0..60 {
            let mut s = Setup::new(len, seed).both(lossy(2000));
            s.known = false;
            let o = run(&s);
            assert!(o.intact, "{len} bytes, seed {seed}: {:?} after {}", o.end, o.time);
            // In a few seconds: a silence or two, each asking for the
            // first chunk again, not a walk through everything that was
            // asked for blind, which ends in giving up.
            assert!(o.time <= 20 * SECOND, "{len} bytes, seed {seed}: {} {:?}", o.time, o.stats);
        }
    }
}

/// How fast a fetch goes is told, and it is not given up for it.
#[test]
fn a_slow_peer_is_reported_and_waited_for() {
    let mut s = Setup::new(100_000, 10);
    s.rate = 4;
    let o = run(&s);
    assert!(o.intact && o.time > 10 * SECOND);
    // A silence or two before the pace is known, each asking for one
    // chunk again and no more.
    assert!(o.stats.asked_again <= 4 && o.stats.asked_again == o.stats.silences, "{:?}", o.stats);
    // Four chunks a second, and a burst at the start.
    assert!((4 * CHUNK_BYTES as u64..10 * CHUNK_BYTES as u64).contains(&o.rate), "{}", o.rate);
}

/// A fetch given up for silence keeps what it has: taken up again, only
/// what is missing is asked for.
#[test]
fn a_fetch_given_up_is_taken_up_where_it_was() {
    let count = chunk_count(1 << 20) as u64;
    for sent in [1, 300, 800] {
        let mut s = Setup::new(1 << 20, 12);
        s.server = Server::Stops(sent);
        s.resumes = 1;
        let o = run(&s);
        assert!(o.intact && o.resumed == 1, "{sent}: {:?}", o.end);
        // Served once each, and the few that were on their way when it
        // stopped.
        assert_eq!(o.served, count, "{sent}");
        assert_eq!(o.stats.spare, 0);
    }
    // Still not knowing the length, it is asked for blind again.
    let mut s = Setup::new(100_000, 13);
    (s.known, s.server, s.resumes) = (false, Server::Stops(0), 1);
    assert!(run(&s).intact);
    // At the worst line there is, a fetch taken up as often as it is
    // given up arrives in the end.
    for seed in 0..5 {
        let mut s = Setup::new(60_000, seed).both(lossy(5000));
        s.resumes = 1000;
        let o = run(&s);
        assert!(o.intact, "seed {seed}: {:?} after {}", o.end, o.resumed);
    }
    // Not after a lie, and not once done.
    let mut ranges = Ranges::new();
    let mut f = Fetch::new(1, Some(5000), 5000, Path::new(), 0);
    assert_eq!(f.poll(0, &mut ranges), Poll::Ask(0));
    let data = [7u8; CHUNK_BYTES];
    assert!(f.chunk(1, &Chunk { transfer: 1, seq: 0, len: 5001, index: 0, data: &data }).is_err());
    f.resume(2, Path::new(), 2);
    assert_eq!((f.poll(2, &mut ranges), f.transfer()), (Poll::Failed(Why::Bad), 1));
    let mut f = Fetch::new(1, Some(10), 5000, Path::new(), 0);
    assert_eq!(f.poll(0, &mut ranges), Poll::Ask(0));
    assert_eq!(f.chunk(1, &Chunk { transfer: 1, seq: 0, len: 10, index: 0, data: &data[..10] }), Ok(Taken::New));
    f.resume(2, Path::new(), 2);
    assert_eq!(f.poll(2, &mut ranges), Poll::Done);
    // After the peer said it had none, with another peer.
    let mut f = Fetch::new(1, Some(10), 5000, Path::new(), 0);
    f.gone();
    assert_eq!(f.poll(0, &mut ranges), Poll::Failed(Why::Gone));
    f.resume(2, Path::new(), 2);
    assert_eq!(f.poll(2, &mut ranges), Poll::Ask(0));
    // A chunk under the old number is no longer this fetch's.
    assert!(f.chunk(3, &Chunk { transfer: 1, seq: 0, len: 10, index: 0, data: &data[..10] }).is_err());
    assert_eq!(f.chunk(3, &Chunk { transfer: 2, seq: 0, len: 10, index: 0, data: &data[..10] }), Ok(Taken::New));
    assert_eq!(f.finish().unwrap(), data[..10]);
}

/// The end of an object is lost in one go, on a path that has been
/// seen to deliver far out of order: sixty chunks, with nothing asked
/// after them to overtake them. It is had again in a few round trips,
/// not a chunk each retry time (as it once was: the answer to each
/// chunk asked again put off the moment the rest were taken for lost,
/// and a block's last chunks came at under two a second).
#[test]
fn a_lost_end_is_had_again_in_a_few_round_trips() {
    for raised in 0..=6 {
        for end in [1, 7, 60, 200] {
            for delay in [20 * MILLI, 75 * MILLI] {
                let mut s = Setup::new(350 * CHUNK_BYTES, 31 + raised).both(Link { delay, ..CLEAN });
                s.server = Server::LosesEnd(end);
                for _ in 0..raised {
                    s.path.disordered();
                }
                let o = run(&s);
                assert_eq!(o.end, Poll::Done);
                let trips = o.time / (2 * delay);
                assert!(trips < 40, "raised {raised}, the last {end}: {trips} round trips, {:?}", o.stats);
                // One silence shows the loss; the rest follows from
                // what is then asked again and comes.
                assert!(o.stats.silences <= 3, "raised {raised}, the last {end}: {:?}", o.stats);
            }
        }
    }
}
