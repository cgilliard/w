//! A node over the machine's own socket and clock, on its threads.
//!
//! Everything a node decides is in [`super::node`]; this carries
//! datagrams between it and a socket, tells it the time, and gives each
//! of its workers a thread (`docs/THREADS.md`):
//!
//! * **The receiver** (the thread that calls [`run`]) reads the port.
//!   For each datagram it finds the worker its sender's host belongs
//!   to and puts the datagram on that worker's queue. It decodes
//!   nothing and never waits: a datagram for a queue that is full is
//!   dropped, as one lost on the way would be, counted, and said in the
//!   main log (not more than once in five seconds).
//! * **Each worker** waits on its queue: for a datagram, for word that
//!   another thread has left it something, or until its own next timer
//!   is due. It handles what it takes off there and then, and sends
//!   its answers on the port itself.
//!
//! Nobody looks to see whether something has changed: whoever changes
//! it wakes whoever is to know.

use std::net::{SocketAddr, UdpSocket};
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::sync::mpsc::{Receiver, RecvTimeoutError, SyncSender, TrySendError, sync_channel};
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};

use super::MAX_DATAGRAM;
use super::node::{CHUNK, Handle, Heard, Node, Worker, socket_addr};
use crate::chain::Chain;
use crate::chain::verify::ProofVerifier;
use crate::logger::Logger;
use crate::logger::queued::Queued;
use crate::logger::stats::{Kind, Stats};
use crate::store::backend::Backend;
use crate::transport::Micros;

/// The time by the calendar, in seconds.
pub fn unix() -> u64 {
    SystemTime::now().duration_since(UNIX_EPOCH).map_or(0, |d| d.as_secs())
}

/// The numbers a node keeps of itself for its stats log, in the order
/// of their columns.
pub const STATS: &[(&str, Kind)] = &[
    ("Packets", Kind::Count),
    ("AvgLatency(us)", Kind::Average(REQUESTS)),
    ("Dropped", Kind::Count),
    ("BytesIn", Kind::Bytes),
    ("BytesSent", Kind::Bytes),
    ("Peers", Kind::Level),
    ("PeersLive", Kind::Level),
    ("Height", Kind::Level),
    ("Blocks", Kind::Count),
    ("Fetching", Kind::Level),
    ("Mined", Kind::Count),
    ("Requests", Kind::Count),
    ("HeapMB", Kind::Level),
    ("PeakHeapMB", Kind::Level),
    ("Refetched", Kind::Count),
    ("PoolMB", Kind::Level),
    ("SetupMB", Kind::Level),
    ("TableMB", Kind::Level),
    ("PeakProvingMB", Kind::Level),
];
/// The node's stats. The log shows these of them, each in a column
/// this wide; the rest are counted all the same.
///
/// ```text
/// Uptime: 0:00:00           Requests___Packets____AvgLatency(us)_HeapMB_PeakHeapMB_PoolMB_SetupMB_TableMB_PeakProvingMB_Peers_PeersLive_Height_Blocks_Refetched_Mined
/// ```
pub fn stats() -> Stats {
    Stats::new(STATS).showing(&[
        (REQUESTS, 11),
        (PACKETS, 11),
        (LATENCY, 15),
        (HEAP, 7),
        (HEAP_PEAK, 11),
        (HEAP_POOL, 7),
        (HEAP_SETUP, 8),
        (HEAP_TABLE, 8),
        (HEAP_PROVING, 14),
        (PEERS, 6),
        (PEERS_LIVE, 10),
        (HEIGHT, 7),
        (BLOCKS, 7),
        (REFETCHED, 10),
        (MINED, 6),
    ])
}

/// Sets what of `stats` is how the node stands to what `hold` says it
/// is now.
pub fn set_levels<B: Backend + 'static, V>(stats: &Stats, hold: &Handle<B, V>) {
    let now = hold.read();
    stats.set(PEERS, now.peers as u64);
    stats.set(PEERS_LIVE, now.live as u64);
    stats.set(HEIGHT, now.height as u64);
    stats.set(BLOCKS, now.blocks);
    stats.set(FETCHING, now.fetching as u64);
    stats.set(REFETCHED, now.refetched);
    // (In megabytes, of a million bytes: nothing, where the program
    // does not count what it holds.)
    stats.set(HEAP, crate::heap::now() as u64 / 1_000_000);
    stats.set(HEAP_PEAK, crate::heap::peak() as u64 / 1_000_000);
    // (Part by part: what is held now; and of proving, which comes
    // and goes within a line, the most it has held.)
    use crate::heap::Part;
    stats.set(HEAP_POOL, crate::heap::held(Part::Pool) as u64 / 1_000_000);
    stats.set(HEAP_SETUP, crate::heap::held(Part::Setup) as u64 / 1_000_000);
    stats.set(HEAP_TABLE, crate::heap::held(Part::Table) as u64 / 1_000_000);
    stats.set(HEAP_PROVING, crate::prover::most_held() as u64 / 1_000_000);
}

/// Datagrams taken, of whatever kind: the requests, and the chunks of
/// what the node itself is fetching (a block is many).
pub const PACKETS: usize = 0;
/// The microseconds taking the requests took: shown as the average of
/// one.
pub const LATENCY: usize = 1;
/// Datagrams dropped because the queue of the worker they were for was
/// full.
pub const DROPPED: usize = 2;
pub const BYTES_IN: usize = 3;
pub const BYTES_SENT: usize = 4;
pub const PEERS: usize = 5;
pub const PEERS_LIVE: usize = 6;
pub const HEIGHT: usize = 7;
/// Blocks that joined the chain here.
pub const BLOCKS: usize = 8;
/// Objects being fetched.
pub const FETCHING: usize = 9;
/// Blocks made here.
pub const MINED: usize = 10;
/// Requests taken: what the request log has a line for, each one line
/// there and one here. (Not the chunks of what the node is fetching.)
pub const REQUESTS: usize = 11;
/// The memory the program holds, and the most it has held, in
/// megabytes ([`crate::heap`]).
pub const HEAP: usize = 12;
pub const HEAP_PEAK: usize = 13;
/// Fetches that did not end with the peer they began with: given up,
/// too slow, or gone on with by another. Now and then is any network;
/// many is a peer, or a line, that is not what it should be.
pub const REFETCHED: usize = 14;
/// The memory held for the pool, the proofs' setup and the table of
/// the proof of work; and the most proving has held
/// ([`crate::heap::Part`]), in megabytes.
pub const HEAP_POOL: usize = 15;
pub const HEAP_SETUP: usize = 16;
pub const HEAP_TABLE: usize = 17;
pub const HEAP_PROVING: usize = 18;

/// What the main log says when datagrams are dropped.
pub const DROPPING: &str = "dropped requests: a worker's queue is full";
/// It is not said again for this long.
const TOLD_EVERY: Duration = Duration::from_secs(5);

/// Who is told what a node does as it runs: none need be there.
#[derive(Clone, Copy, Default)]
pub struct Watch<'a> {
    /// The request log: a line for each datagram taken
    /// ([`Heard::line`]), but for the chunks of what the node itself is
    /// fetching, which are counted only.
    pub requests: Option<&'a Queued>,
    /// The stats ([`STATS`]).
    pub stats: Option<&'a Stats>,
    /// The main log: told when datagrams are dropped.
    pub main: Option<&'a Logger>,
}

impl Watch<'_> {
    /// A datagram of `bytes` was taken in `micros`.
    fn heard(&self, heard: &Heard, bytes: usize, micros: u64) {
        // A request has a line in the request log, and is counted as
        // one; a chunk of something being fetched is a packet only.
        let request = heard.request != CHUNK;
        if let Some(stats) = self.stats {
            stats.add(PACKETS, 1);
            stats.add(BYTES_IN, bytes as u64);
            if request {
                stats.add(REQUESTS, 1);
                stats.add(LATENCY, micros);
            }
        }
        if let Some(requests) = self.requests
            && request
        {
            requests.log(&heard.line(bytes, micros));
        }
    }

    /// How the node stands.
    fn levels<B: Backend + 'static, V>(&self, gauge: &Handle<B, V>) {
        if let Some(stats) = self.stats {
            set_levels(stats, gauge);
        }
    }
}

/// What waits for a worker.
///
/// (A datagram is some 1,270 bytes and a waking none: nearly all that
/// waits is datagrams, so it is left as it is.)
#[allow(clippy::large_enum_variant)]
enum Item {
    /// A datagram, and who sent it. (One byte more than any datagram
    /// of ours: what fills it is not one.)
    Datagram { from: SocketAddr, len: u16, bytes: [u8; MAX_DATAGRAM + 1] },
    /// Something was left for it by another thread.
    Wake,
}

/// Runs `node` over `socket` until `stop` is set, then says goodbye to
/// its peers.
pub fn run<B: Backend + 'static, V: ProofVerifier + Sync>(
    node: &mut Node<B, V>,
    socket: &UdpSocket,
    stop: &AtomicBool,
) -> std::io::Result<()>
where
    Chain<B, V>: Send + Sync,
    Worker<B, V>: Send,
{
    let clock = Instant::now();
    run_until(node, socket, stop, clock, &unix)?;
    node.goodbye(clock.elapsed().as_micros() as Micros, &mut |to, bytes: &[u8]| {
        let _ = socket.send_to(bytes, socket_addr(to));
    });
    Ok(())
}

/// [`run`] without the goodbye, on a clock begun at `clock` and a
/// calendar that says `unix`: a node run in stretches, its time going
/// on from one to the next; or one whose headers are of another day.
pub fn run_until<B: Backend + 'static, V: ProofVerifier + Sync>(
    node: &mut Node<B, V>,
    socket: &UdpSocket,
    stop: &AtomicBool,
    clock: Instant,
    unix: &(dyn Fn() -> u64 + Sync),
) -> std::io::Result<()>
where
    Chain<B, V>: Send + Sync,
    Worker<B, V>: Send,
{
    run_watched(node, socket, stop, clock, unix, &Watch::default())
}

/// [`run_until`], with `watch` told of each datagram taken, of those
/// dropped, and how the node stands.
///
/// This thread is the receiver; each of the node's workers has a
/// thread of its own until this returns.
pub fn run_watched<B: Backend + 'static, V: ProofVerifier + Sync>(
    node: &mut Node<B, V>,
    socket: &UdpSocket,
    stop: &AtomicBool,
    clock: Instant,
    unix: &(dyn Fn() -> u64 + Sync),
    watch: &Watch<'_>,
) -> std::io::Result<()>
where
    Chain<B, V>: Send + Sync,
    Worker<B, V>: Send,
{
    serve(node, socket, Some(stop), clock, unix, watch)
}

/// [`run_watched`] with nothing to stop it: it returns only if the
/// port can no longer be read. No thread of it wakes to see whether it
/// is to stop, so a node with nothing to do does nothing: the receiver
/// waits for a datagram, and each worker for one or for what it has
/// next to do of itself.
pub fn run_for_ever<B: Backend + 'static, V: ProofVerifier + Sync>(
    node: &mut Node<B, V>,
    socket: &UdpSocket,
    clock: Instant,
    unix: &(dyn Fn() -> u64 + Sync),
    watch: &Watch<'_>,
) -> std::io::Result<()>
where
    Chain<B, V>: Send + Sync,
    Worker<B, V>: Send,
{
    serve(node, socket, None, clock, unix, watch)
}

fn serve<B: Backend + 'static, V: ProofVerifier + Sync>(
    node: &mut Node<B, V>,
    socket: &UdpSocket,
    stop: Option<&AtomicBool>,
    clock: Instant,
    unix: &(dyn Fn() -> u64 + Sync),
    watch: &Watch<'_>,
) -> std::io::Result<()>
where
    Chain<B, V>: Send + Sync,
    Worker<B, V>: Send,
{
    let (gauge, queue) = (node.hold(), node.request_queue());
    let (workers, shared) = node.parts();
    // (What may wait is what may wait in all, shared among the workers:
    // each queue has its room from the start, a datagram's worth for
    // each place in it.)
    let queue = (queue / workers.len().max(1)).max(queue.min(256));
    let (senders, queues): (Vec<SyncSender<Item>>, Vec<Receiver<Item>>) =
        workers.iter().map(|_| sync_channel(queue)).unzip();
    // Whoever leaves something for a worker wakes it. (If its queue is
    // full it is not waiting, and looks when it is through.)
    let wake = senders.clone();
    shared.set_waker(Some(Box::new(move |worker| {
        let _ = wake[worker].try_send(Item::Wake);
    })));
    let gauge = &gauge;
    // The receiver is through: said to the workers, whatever stopped it.
    let done = AtomicBool::new(false);
    let done = &done;
    // When each worker last looked up from what it was doing
    // ([`RESTING`] while it waits for something to do): watched, so
    // that one that waits for what is never let go is said.
    let beats: Vec<AtomicU64> = workers.iter().map(|_| AtomicU64::new(RESTING)).collect();
    let beats = &beats;
    let received = std::thread::scope(|scope| {
        for (k, (worker, queue)) in workers.iter_mut().zip(queues).enumerate() {
            // (The first of them says, now and then, how the node stands.)
            let gauge = (k == 0).then_some(gauge);
            let beat = &beats[k];
            std::thread::Builder::new()
                .name(format!("worker {k}"))
                .spawn_scoped(scope, move || work(worker, queue, socket, stop, done, clock, unix, watch, gauge, beat))
                .expect("a thread");
        }
        if let Some(main) = watch.main {
            std::thread::Builder::new()
                .name("watch".to_string())
                .spawn_scoped(scope, move || {
                    let mut said: Vec<Option<Instant>> = vec![None; beats.len()];
                    while !done.load(Ordering::Relaxed) && !stop.is_some_and(|stop| stop.load(Ordering::Relaxed)) {
                        std::thread::sleep(Duration::from_millis(200));
                        let now = clock.elapsed().as_micros() as Micros;
                        for (k, beat) in beats.iter().enumerate() {
                            let Some(seconds) = stalled(beat.load(Ordering::Relaxed), now) else {
                                said[k] = None;
                                continue;
                            };
                            // (Said when it is found, and each minute
                            // it goes on.)
                            if said[k].is_none_or(|at| at.elapsed() >= Duration::from_secs(60)) {
                                said[k] = Some(Instant::now());
                                main.log(&format!(
                                    "Error: worker {k} has not looked up for {seconds} seconds: it waits for \
                                     something another thread holds, or works at what does not end"
                                ));
                            }
                        }
                    }
                })
                .expect("a thread");
        }
        let received = receive(socket, stop, watch, |from| shared.worker_of(from), &senders);
        // The receiver is through, for whatever reason: so are they,
        // woken to see it. (One whose queue is full is not waiting.)
        done.store(true, Ordering::Relaxed);
        for sender in &senders {
            let _ = sender.try_send(Item::Wake);
        }
        received
    });
    shared.set_waker(None);
    received
}

/// What a worker's beat says while it waits for something to do.
const RESTING: u64 = u64::MAX;
/// How long a worker may go without looking up before it is said: far
/// longer than anything it does between two looks takes.
const STALLED: Micros = 60_000_000;

/// For how many seconds a worker whose beat is `beat` has not looked
/// up, at `now`, if that is too long.
fn stalled(beat: u64, now: Micros) -> Option<u64> {
    (beat != RESTING && now.saturating_sub(beat) >= STALLED).then(|| now.saturating_sub(beat) / 1_000_000)
}

/// What comes on `queue` within `wait` microseconds. Where a wait is
/// as long as the machine's clock ticks and no shorter (Windows: a
/// sixty-fourth of a second, as a rule), one of a few hundred
/// microseconds, which is what there is between two chunks served at
/// their pace, is kept by looking again and again: slept through, the
/// pace would be a burst a tick, a quarter of the rate.
fn recv_within<T>(queue: &std::sync::mpsc::Receiver<T>, wait: u64) -> Result<T, std::sync::mpsc::RecvTimeoutError> {
    use std::sync::mpsc::{RecvTimeoutError, TryRecvError};
    if cfg!(windows) && wait < 2_000 {
        let until = Instant::now() + Duration::from_micros(wait);
        loop {
            match queue.try_recv() {
                Ok(item) => return Ok(item),
                Err(TryRecvError::Disconnected) => return Err(RecvTimeoutError::Disconnected),
                Err(TryRecvError::Empty) if Instant::now() >= until => return Err(RecvTimeoutError::Timeout),
                Err(TryRecvError::Empty) => std::thread::yield_now(),
            }
        }
    }
    queue.recv_timeout(Duration::from_micros(wait))
}

/// The receiver: reads the port and hands each datagram to the worker
/// `owner` says its sender is of.
fn receive(
    socket: &UdpSocket,
    stop: Option<&AtomicBool>,
    watch: &Watch<'_>,
    owner: impl Fn(&SocketAddr) -> usize,
    queues: &[SyncSender<Item>],
) -> std::io::Result<()> {
    // (Not for ever, where it may be told to stop: so that it is seen.)
    socket.set_read_timeout(stop.map(|_| Duration::from_millis(50)))?;
    let mut told: Option<Instant> = None;
    let mut failed = 0u32;
    let mut item = Item::Datagram { from: SocketAddr::from(([0, 0, 0, 0], 0)), len: 0, bytes: [0u8; MAX_DATAGRAM + 1] };
    while !stop.is_some_and(|stop| stop.load(Ordering::Relaxed)) {
        let Item::Datagram { from, len, bytes } = &mut item else { unreachable!() };
        // Nothing in time, or the machine's own complaint about a
        // datagram we sent, is no datagram.
        let (n, sender) = match socket.recv_from(bytes) {
            Ok(read) => {
                failed = 0;
                read
            }
            Err(e) => {
                use std::io::ErrorKind::{ConnectionRefused, ConnectionReset, Interrupted, TimedOut, WouldBlock};
                // (A port that only fails, time after time, is not read
                // as fast as it fails.)
                if !matches!(e.kind(), WouldBlock | TimedOut | Interrupted | ConnectionReset | ConnectionRefused) {
                    failed += 1;
                    if failed > 16 {
                        std::thread::sleep(Duration::from_millis(10));
                    }
                }
                continue;
            }
        };
        (*from, *len) = (sender, n as u16);
        let queue = &queues[owner(&sender)];
        let next = Item::Datagram { from: sender, len: 0, bytes: [0u8; MAX_DATAGRAM + 1] };
        match queue.try_send(std::mem::replace(&mut item, next)) {
            Ok(()) => {}
            // No room: dropped, and said.
            Err(TrySendError::Full(_)) => {
                if let Some(stats) = watch.stats {
                    stats.add(DROPPED, 1);
                }
                if told.is_none_or(|at| at.elapsed() >= TOLD_EVERY) {
                    told = Some(Instant::now());
                    if let Some(main) = watch.main {
                        main.log(DROPPING);
                    }
                }
            }
            // Its worker is gone: the node is stopping.
            Err(TrySendError::Disconnected(_)) => break,
        }
    }
    Ok(())
}

/// A worker's thread: handles what comes off its queue, and looks to
/// what is due when it is.
#[allow(clippy::too_many_arguments)]
fn work<B: Backend + 'static, V: ProofVerifier + Sync>(
    worker: &mut Worker<B, V>,
    queue: Receiver<Item>,
    socket: &UdpSocket,
    stop: Option<&AtomicBool>,
    done: &AtomicBool,
    clock: Instant,
    unix: &(dyn Fn() -> u64 + Sync),
    watch: &Watch<'_>,
    gauge: Option<&Handle<B, V>>,
    beat: &AtomicU64,
) {
    let now = || clock.elapsed().as_micros() as Micros;
    // A datagram that cannot be sent is a datagram lost, as any may be.
    let mut out = |to, bytes: &[u8]| {
        if let Some(stats) = watch.stats {
            stats.add(BYTES_SENT, bytes.len() as u64);
        }
        let _ = socket.send_to(bytes, socket_addr(to));
    };
    // When how the node stands was last told: once a second is enough.
    let mut told: Option<Micros> = None;
    while !done.load(Ordering::Relaxed) && !stop.is_some_and(|stop| stop.load(Ordering::Relaxed)) {
        let t = now();
        beat.store(t, Ordering::Relaxed);
        let wake = worker.tick(t, unix(), &mut out);
        if let Some(gauge) = gauge
            && told.is_none_or(|at| t.saturating_sub(at) >= 1_000_000)
        {
            watch.levels(gauge);
            // (And a main log that has had its time is put aside,
            // though nothing is being said in it.)
            if let Some(main) = watch.main {
                main.rotate_if_due();
            }
            told = Some(t);
        }
        // Until the worker's own next timer, or something comes: and
        // where it may be told to stop, a twentieth of a second at the
        // most, to see it.
        let most = if stop.is_some() { 50_000 } else { 3_600_000_000 };
        let wait = wake.saturating_sub(t).clamp(50, most);
        let mut take = |worker: &mut Worker<B, V>, item: Item| {
            if let Item::Datagram { from, len, bytes } = item {
                let began = now();
                let heard = worker.handle(began, from, &bytes[..len as usize], &mut out);
                watch.heard(&heard, len as usize, now().saturating_sub(began));
            }
        };
        beat.store(RESTING, Ordering::Relaxed);
        let came = recv_within(&queue, wait);
        beat.store(now(), Ordering::Relaxed);
        match came {
            Ok(item) => {
                take(worker, item);
                // And whatever else is waiting, before looking to the
                // time.
                for _ in 0..64 {
                    match queue.try_recv() {
                        Ok(item) => take(worker, item),
                        Err(_) => break,
                    }
                }
            }
            Err(RecvTimeoutError::Timeout) => {}
            Err(RecvTimeoutError::Disconnected) => break,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::logger::Rotation;

    /// A datagram for a worker whose queue is full is dropped: counted
    /// every time, said in the main log once in a while, and the
    /// receiver goes on reading. What was there is still there.
    #[test]
    fn a_full_queue_drops_and_says_so() {
        let dir = std::env::temp_dir().join(format!("tabminer-dropped-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).unwrap();
        let main = Logger::open(dir.join("tabernacle.log"), Rotation::default()).unwrap();
        let stats = Stats::new(STATS);
        let watch = Watch { requests: None, stats: Some(&stats), main: Some(&main) };
        let port = UdpSocket::bind("127.0.0.1:0").unwrap();
        let to = port.local_addr().unwrap();
        // Two workers, by whether the sender's port is odd: room for
        // three datagrams each, and nobody taking them off.
        let (senders, queues): (Vec<_>, Vec<_>) = (0..2).map(|_| sync_channel::<Item>(3)).unzip();
        let stop = AtomicBool::new(false);
        let senders_of: Vec<UdpSocket> = (0..2).map(|_| UdpSocket::bind("127.0.0.1:0").unwrap()).collect();
        let odd = |s: &UdpSocket| (s.local_addr().unwrap().port() % 2) as usize;
        std::thread::scope(|scope| {
            scope.spawn(|| receive(&port, Some(&stop), &watch, |from| (from.port() % 2) as usize, &senders).unwrap());
            // Ten from the first sender, then two from the second.
            for k in 0..10u8 {
                senders_of[0].send_to(&[k; 20], to).unwrap();
            }
            let all = |n: u64| {
                let start = Instant::now();
                while stats.read()[DROPPED] < n {
                    assert!(start.elapsed() < Duration::from_secs(20), "{:?}", stats.read());
                    std::thread::sleep(Duration::from_millis(5));
                }
            };
            // Three wait; seven were dropped.
            all(7);
            senders_of[1].send_to(&[77; 30], to).unwrap();
            senders_of[1].send_to(&[78; 30], to).unwrap();
            if odd(&senders_of[0]) == odd(&senders_of[1]) {
                // (Of the same worker, as it happens: dropped as well.)
                all(9);
            } else {
                std::thread::sleep(Duration::from_millis(200));
            }
            stop.store(true, Ordering::Relaxed);
        });
        // The first three of the first sender wait, in the order sent.
        let first = &queues[odd(&senders_of[0])];
        for k in 0..3u8 {
            match first.try_recv() {
                Ok(Item::Datagram { from, len, bytes }) => {
                    assert_eq!((from, &bytes[..len as usize]), (senders_of[0].local_addr().unwrap(), &[k; 20][..]));
                }
                _ => panic!("the datagram {k} is not there"),
            }
        }
        // A full queue is one worker's: the other's took what was its.
        if odd(&senders_of[0]) != odd(&senders_of[1]) {
            assert!(first.try_recv().is_err());
            let other = &queues[odd(&senders_of[1])];
            assert!(matches!(other.try_recv(), Ok(Item::Datagram { len: 30, .. })));
            assert!(matches!(other.try_recv(), Ok(Item::Datagram { len: 30, .. })));
            assert_eq!(stats.read()[DROPPED], 7);
        }
        // Said once, for all of them.
        let said = std::fs::read_to_string(dir.join("tabernacle.log")).unwrap();
        assert_eq!(said.lines().filter(|l| l.ends_with(DROPPING)).count(), 1, "{said}");
        let _ = std::fs::remove_dir_all(&dir);
    }
}

#[cfg(test)]
mod watch_tests {
    use super::*;

    /// A worker that waits for something to do is not one that has
    /// stopped; one that began something a minute ago and has not
    /// looked up since is.
    #[test]
    fn a_worker_that_does_not_look_up_is_said() {
        let now = 500_000_000;
        assert_eq!(stalled(RESTING, now), None);
        assert_eq!(stalled(now - 59_000_000, now), None);
        assert_eq!(stalled(now - 61_500_000, now), Some(61));
        assert_eq!(stalled(now + 5, now), None);
    }
}
