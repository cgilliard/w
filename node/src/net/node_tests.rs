//! Nodes and the datagrams between them, every datagram's fate chosen.

use super::*;
use crate::block::BlockRef;
use crate::chain::apply::tests::{grow, grow_wide, next_block};
use crate::chain::headers::tests::{NOW, easy, seed, table};
use crate::chain::params::ChainParams;
use crate::chain::verify::AcceptAllProofs;
use crate::net::message::Addrs;
use crate::store::testing::MemBackend;
use crate::test_util::Rng;
use crate::transport::{MILLI, SECOND};
use std::net::Ipv4Addr;

const NET: [u8; 4] = *b"TEST";

type TestChain = Chain<MemBackend, AcceptAllProofs>;
type TestNode = Node<MemBackend, AcceptAllProofs>;

/// A chain that keeps the bodies of its last `KEEP` blocks.
const KEEP: usize = 64;

fn chain_of(params: ChainParams) -> Arc<TestChain> {
    let chain = Chain::open(MemBackend::new(), KEEP, params, seed(), AcceptAllProofs).unwrap();
    chain.set_dataset(table());
    Arc::new(chain)
}

/// Gives `chain` these blocks, made on another.
fn give(chain: &TestChain, blocks: &[Vec<u8>]) {
    for b in blocks {
        chain.apply_block(&BlockRef::from_bytes(b).unwrap(), NOW).unwrap();
    }
}

/// The address of node `n`: each a host and a network of its own.
fn at(n: usize) -> SocketAddrV4 {
    SocketAddrV4::new(Ipv4Addr::new(20 + (n / 200) as u8, (n % 200) as u8, 0, 1), 3737)
}

thread_local! {
    /// How many workers the nodes of a [`World`] have.
    static WORKERS: std::cell::Cell<usize> = const { std::cell::Cell::new(1) };
}

/// Runs `test` with nodes of several workers each.
fn several(test: fn()) {
    WORKERS.set(4);
    test();
    WORKERS.set(1);
}

/// Nodes and the datagrams between them: every one takes twenty
/// milliseconds, some are lost, and one sent to an address that is no
/// node's is kept to be looked at.
struct World {
    nodes: Vec<TestNode>,
    /// When each node wants to be called.
    wake: Vec<Micros>,
    now: Micros,
    flying: Vec<(Micros, SocketAddrV4, SocketAddrV4, Vec<u8>)>,
    /// Lost, in a thousand.
    loss: u64,
    rng: Rng,
    /// To addresses that are no node's: from, to, what.
    strays: Vec<(SocketAddrV4, SocketAddrV4, Vec<u8>)>,
    /// Nodes of which nothing but pings and pongs gets out.
    mute: Vec<usize>,
    /// Nodes whose chunks of what they serve come seconds late, each
    /// later than the one before: a peer that sends a little at a time.
    slow: Vec<usize>,
    late: Micros,
    /// A node that sends so many chunks of what it serves and then no
    /// more of them, while it goes on answering everything else.
    stops: Option<(usize, u32)>,
    /// Times the nodes were told the time.
    ticks: u64,
    /// What each datagram a node took was, and when.
    log: Vec<(Micros, &'static str)>,
}

impl World {
    fn new(n: usize, cfg: &Config) -> World {
        World::with((0..n).map(|_| chain_of(easy())).collect(), cfg)
    }

    fn with(chains: Vec<Arc<TestChain>>, cfg: &Config) -> World {
        let n = chains.len();
        // (As many workers to a node as the test is run with.)
        let cfg = &Config { workers: WORKERS.get(), ..cfg.clone() };
        let nodes = chains.into_iter().enumerate().map(|(i, c)| Node::new(cfg.clone(), NET, c, [i as u8 + 1; 32], 0));
        World {
            nodes: nodes.collect(),
            wake: vec![0; n],
            now: 0,
            flying: Vec::new(),
            loss: 0,
            rng: Rng::new(5),
            strays: Vec::new(),
            mute: Vec::new(),
            slow: Vec::new(),
            late: 0,
            stops: None,
            ticks: 0,
            log: Vec::new(),
        }
    }

    fn post(&mut self, from: SocketAddrV4, to: SocketAddrV4, bytes: &[u8]) {
        if self.rng.next_u64() % 1000 >= self.loss {
            self.flying.push((self.now + 20 * MILLI, from, to, bytes.to_vec()));
        }
    }

    /// A datagram from `from`, which may be anyone's claim.
    fn inject(&mut self, from: SocketAddrV4, to: usize, message: &Message<'_>) {
        let mut buf = [0u8; MAX_DATAGRAM];
        let n = message.encode(NET, &mut buf);
        self.flying.push((self.now, from, at(to), buf[..n].to_vec()));
    }

    /// Lets `time` pass: each node is called when it asks to be, and
    /// when a datagram has come for it.
    fn run(&mut self, time: Micros) {
        let end = self.now + time;
        loop {
            // Everything due at this moment, until nothing is.
            for round in 0.. {
                assert!(round < 100_000, "a moment that does not end");
                let mut sent = Vec::new();
                let (due, later): (Vec<_>, Vec<_>) = self.flying.drain(..).partition(|d| d.0 <= self.now);
                self.flying = later;
                let mut busy = !due.is_empty();
                for (_, from, to, bytes) in due {
                    match (0..self.nodes.len()).find(|&i| at(i) == to) {
                        Some(i) => {
                            let heard = self.nodes[i].handle(self.now, SocketAddr::V4(from), &bytes, &mut |to, b| {
                                sent.push((i, to, b.to_vec()))
                            });
                            self.log.push((self.now, heard.request));
                            self.wake[i] = self.now;
                        }
                        None => self.strays.push((from, to, bytes)),
                    }
                }
                for i in 0..self.nodes.len() {
                    if self.wake[i] <= self.now {
                        busy = true;
                        self.ticks += 1;
                        self.wake[i] = self.nodes[i].tick(self.now, NOW, &mut |to, b| sent.push((i, to, b.to_vec())));
                        // (At once means as soon as time has moved.)
                        self.wake[i] = self.wake[i].max(self.now + 1);
                    }
                }
                for (i, to, bytes) in sent {
                    let small_talk = matches!(Message::decode(NET, &bytes), Ok(Message::Ping(_) | Message::Pong(_)));
                    let chunk = matches!(Message::decode(NET, &bytes), Ok(Message::Chunk(_)));
                    if let Some((who, left)) = &mut self.stops
                        && *who == i
                        && chunk
                    {
                        if *left > 0 {
                            *left -= 1;
                            self.post(at(i), to, &bytes);
                        }
                    } else if self.slow.contains(&i) && chunk {
                        // (One chunk every three seconds.)
                        self.late = self.late.max(self.now) + 3 * SECOND;
                        self.flying.push((self.late, at(i), to, bytes.to_vec()));
                    } else if small_talk || !self.mute.contains(&i) {
                        self.post(at(i), to, &bytes);
                    }
                }
                if !busy {
                    break;
                }
            }
            let next = self.flying.iter().map(|d| d.0).chain(self.wake.iter().copied()).min().unwrap_or(end);
            if next >= end {
                self.now = end;
                return;
            }
            self.now = next.max(self.now + 1);
        }
    }

    /// Whoever drives a node has given it something to do: it is
    /// woken, as a node that waits on a thread of its own is.
    fn woken(&mut self) {
        self.wake.iter_mut().for_each(|wake| *wake = self.now);
    }

    fn live(&self, i: usize) -> Vec<SocketAddrV4> {
        self.nodes[i].tables().flat_map(|t| t.live(self.now)).map(|p| p.addr).collect()
    }

    fn best(&self, i: usize) -> Header {
        self.nodes[i].chain().best_header().unwrap().header
    }
}

/// A status as some address might claim it.
fn claim(nonce: u64, genesis: Digest) -> Status {
    Status {
        nonce,
        version: VERSION,
        token: 0,
        genesis,
        height: 1,
        oldest: 0,
        window: 0,
        tip: genesis,
        work: U256::ZERO,
        // (A node of its own: no two of these claims are one node's.)
        node: nonce.wrapping_mul(0x9e37_79b9_7f4a_7c15) | 1 << 63,
    }
}

// -- Finding and keeping peers

#[test]
fn two_nodes_that_one_knows_of_come_to_know_each_other() {
    let chains = vec![chain_of(easy()), chain_of(easy())];
    grow(&chains[1], 3, 1);
    let mut w = World::with(chains, &Config::default());
    assert!(w.nodes[0].add_peer(at(1), true, 0));
    w.run(500 * MILLI);
    assert_eq!((w.live(0), w.live(1)), (vec![at(1)], vec![at(0)]));
    // Each holds what the other says of itself, and the token the
    // other gave it; and each has timed the other.
    let (a, b) = (*w.nodes[0].table(&at(1)).get(&at(1)).unwrap(), *w.nodes[1].table(&at(0)).get(&at(0)).unwrap());
    let tip = w.nodes[1].chain().tip().unwrap();
    assert_eq!((a.status.unwrap().height, a.status.unwrap().tip, b.status.unwrap().height), (3, tip.hash(), 0));
    assert_eq!((a.status.unwrap().oldest, a.status.unwrap().window), (0, 0));
    assert_eq!(a.status.unwrap().work, w.nodes[1].chain().tip_work().unwrap());
    assert!(w.nodes[1].tokens.check(&SocketAddr::V4(at(0)), a.token().unwrap()));
    assert!(w.nodes[0].tokens.check(&SocketAddr::V4(at(1)), b.token().unwrap()));
    assert_eq!((a.path.round_trip(), b.path.round_trip()), (Some(40 * MILLI), Some(40 * MILLI)));
    assert_eq!((w.nodes[0].counts().unheard, w.nodes[0].counts().malformed), (0, 0));
}

/// Thirty nodes that know one seed between them: each comes to have
/// the peers it wants, though a fifth of all datagrams are lost.
#[test]
fn nodes_that_know_one_seed_find_each_other() {
    for loss in [0, 200] {
        let mut w = World::new(30, &Config::default());
        w.loss = loss;
        for i in 1..30 {
            assert!(w.nodes[i].add_peer(at(0), true, 0));
        }
        w.run(60 * SECOND);
        for i in 0..30 {
            assert!(w.live(i).len() >= 8, "loss {loss}: node {i} has {}", w.live(i).len());
        }
        // Having what they want, they ask no more, and only ping: a
        // ping and a pong to each peer every thirty seconds.
        let before: u64 = w.nodes.iter().map(|n| n.counts().sent).sum();
        let peers: usize = (0..30).map(|i| w.nodes[i].tables().map(|t| t.len()).sum::<usize>()).sum();
        w.run(60 * SECOND);
        let sent = w.nodes.iter().map(|n| n.counts().sent).sum::<u64>() - before;
        assert!(sent <= 2 * 2 * peers as u64 + 60, "loss {loss}: {sent} for {peers}");
    }
}

#[test]
fn a_forged_ping_costs_its_victim_no_more_than_the_forger() {
    let mut w = World::new(1, &Config::default());
    let genesis = w.nodes[0].genesis;
    w.run(10 * MILLI);
    let forged = |n: u16| SocketAddrV4::new(Ipv4Addr::new(99, (n / 4) as u8, 0, (n % 4) as u8 + 1), 1000 + n);
    // A hundred pings in one tick, each claiming another address.
    for n in 0..100 {
        w.inject(forged(n), 0, &Message::Ping(claim(n as u64, genesis)));
    }
    w.run(500 * MILLI);
    // Each got its pong; our own pings went to eight of them.
    let (mut pongs, mut pings) = (0, 0);
    for (_, _, bytes) in &w.strays {
        match Message::decode(NET, bytes).unwrap() {
            Message::Pong(_) => pongs += 1,
            Message::Ping(_) => pings += 1,
            other => panic!("{other:?}"),
        }
        assert_eq!(bytes.len(), 141, "as much as a ping, no more");
    }
    assert_eq!((pongs, pings), (100, 8));
    // The same address again and again gets pongs, and no second ping
    // until its turn.
    w.strays.clear();
    for _ in 0..50 {
        w.inject(forged(0), 0, &Message::Ping(claim(7, genesis)));
    }
    w.run(400 * MILLI);
    assert_eq!(w.strays.len(), 50);
    // None of them is anyone: none is live, none is told of, and in
    // three minutes all are gone. (Three minutes from when each was
    // first pinged, and the last had its first ping some seconds in.)
    let now = w.now;
    assert!(w.live(0).is_empty() && w.nodes[0].peers.sample(None, now).as_slice().is_empty());
    let seconds = w.now / SECOND;
    w.run(200 * SECOND);
    assert_eq!(w.nodes[0].tables().map(|t| t.len()).sum::<usize>(), 0);
    // In all that time our pings to them were rationed: eight
    // addresses a second at the most.
    let pings = w.strays.iter().filter(|s| matches!(Message::decode(NET, &s.2), Ok(Message::Ping(_)))).count() as u64;
    assert!(pings <= 8 * (200 + seconds + 2), "{pings}");
}

#[test]
fn a_pong_that_answers_no_ping_of_ours_proves_nothing() {
    let mut w = World::new(2, &Config::default());
    let genesis = w.nodes[0].genesis;
    w.nodes[0].add_peer(at(1), false, 0);
    // Before node 0 has pinged at all: a pong claiming the earth.
    let boast = Status { height: 1 << 30, work: U256::MAX, ..claim(1, genesis) };
    w.flying.clear();
    w.wake[0] = Micros::MAX;
    w.inject(at(1), 0, &Message::Pong(boast));
    w.wake[1] = Micros::MAX;
    w.run(10 * MILLI);
    assert!(!w.nodes[0].table(&at(1)).proven(&at(1)));
    assert_eq!(w.nodes[0].counts().unheard, 1);
    // Nor does anything else from an address not proven count: a list
    // of peers to try is not taken.
    let mut addrs = Addrs::new();
    addrs.push(at(7));
    w.inject(at(5), 0, &Message::Peers(addrs));
    w.wake[0] = Micros::MAX;
    w.run(10 * MILLI);
    assert!(w.nodes[0].table(&at(7)).get(&at(7)).is_none());
    assert_eq!(w.nodes[0].counts().unheard, 2);
}

#[test]
fn a_request_is_answered_only_with_its_token() {
    let mut cfg = Config::default();
    // (Content with one peer, so that nothing is sent here but pings
    // and what the test sends.)
    (cfg.serve.token_life, cfg.peers.target) = (60 * SECOND, 1);
    let mut w = World::new(3, &cfg);
    w.nodes[0].add_peer(at(1), false, 0);
    w.nodes[0].add_peer(at(2), false, 0);
    w.run(SECOND);
    let token = w.nodes[0].table(&at(1)).get(&at(1)).unwrap().token().unwrap();
    let answers = |w: &World| w.nodes[1].counts().sent;
    // The token node 1 gave node 0: answered.
    let before = answers(&w);
    w.inject(at(0), 1, &Message::GetPeers { token });
    w.run(50 * MILLI);
    assert_eq!(answers(&w), before + 1);
    // Without it, with another's, or from another address: nothing.
    let other = w.nodes[0].table(&at(2)).get(&at(2)).unwrap().token().unwrap();
    let locator = Locator::new(&[w.nodes[0].genesis]).unwrap();
    for (from, t) in [(at(0), 0), (at(0), other), (at(0), token ^ 1), (at(9), token)] {
        w.inject(from, 1, &Message::GetPeers { token: t });
        w.inject(from, 1, &Message::Goodbye { token: t });
        w.inject(from, 1, &Message::FindFork { token: t, locator });
        let mut ranges = Ranges::new();
        ranges.push(0);
        let mut name = [0u8; MAX_NAME];
        let n = Object::Headers { from: 0, count: 1, on: w.nodes[0].genesis }.encode(&mut name);
        w.inject(from, 1, &Message::Get(Get { token: t, transfer: 1, seq: 0, name: &name[..n], ranges }));
    }
    w.run(50 * MILLI);
    assert_eq!(answers(&w), before + 1);
    assert_eq!(w.nodes[1].counts().unheard, 16);
    assert!(w.nodes[1].table(&at(0)).proven(&at(0)));
    // A token lasts one change of the secret, and not two: an old one
    // kept and used long after is refused. (Pings carry the new one
    // every half minute, so a peer's is never old.)
    w.run(60 * SECOND);
    w.inject(at(0), 1, &Message::GetPeers { token });
    w.run(50 * MILLI);
    assert_eq!(w.nodes[1].counts().unheard, 16, "heard, the secret having changed once");
    w.run(70 * SECOND);
    w.inject(at(0), 1, &Message::GetPeers { token });
    w.run(50 * MILLI);
    assert_eq!(w.nodes[1].counts().unheard, 17);
    // While the one its pings have brought since is good.
    let fresh = w.nodes[0].table(&at(1)).get(&at(1)).unwrap().token().unwrap();
    assert_ne!(fresh, token);
    w.inject(at(0), 1, &Message::GetPeers { token: fresh });
    w.run(50 * MILLI);
    assert_eq!(w.nodes[1].counts().unheard, 17);
}

#[test]
fn a_node_of_another_chain_or_version_is_answered_and_left_alone() {
    // Node 1 is of another chain.
    let other = ChainParams { genesis_timestamp: easy().genesis_timestamp + 1, ..easy() };
    let mut w = World::with(vec![chain_of(easy()), chain_of(other)], &Config::default());
    let genesis = w.nodes[0].genesis;
    w.nodes[0].add_peer(at(1), false, 0);
    w.run(SECOND);
    // Each answered the other, and neither keeps the other.
    assert_eq!(
        (w.nodes[0].tables().map(|t| t.len()).sum::<usize>(), w.nodes[1].tables().map(|t| t.len()).sum::<usize>()),
        (0, 0)
    );
    assert!(w.nodes[0].counts().strangers >= 1 && w.nodes[1].counts().strangers >= 1);
    // A ping of another version: a pong, and nothing kept.
    let stranger = SocketAddrV4::new(Ipv4Addr::new(77, 1, 1, 1), 9);
    w.inject(stranger, 0, &Message::Ping(Status { version: VERSION + 1, ..claim(3, genesis) }));
    w.run(100 * MILLI);
    assert_eq!(w.strays.len(), 1);
    assert!(
        matches!(Message::decode(NET, &w.strays[0].2), Ok(Message::Pong(s)) if s.nonce == 3 && s.version == VERSION)
    );
    assert_eq!(w.nodes[0].tables().map(|t| t.len()).sum::<usize>(), 0);
    // A datagram of another network, and one that is nothing: not
    // answered at all.
    let mut buf = [0u8; MAX_DATAGRAM];
    let n = Message::Ping(claim(3, genesis)).encode(*b"ELSE", &mut buf);
    w.flying.push((w.now, stranger, at(0), buf[..n].to_vec()));
    w.flying.push((w.now, stranger, at(0), b"hello".to_vec()));
    w.run(100 * MILLI);
    assert_eq!((w.strays.len(), w.nodes[0].counts().malformed), (1, 2));
}

#[test]
fn a_node_told_its_own_address_finds_out() {
    let mut w = World::new(2, &Config::default());
    w.nodes[0].add_peer(at(0), true, 0);
    w.nodes[0].add_peer(at(1), false, 0);
    w.run(SECOND);
    assert_eq!(w.live(0), [at(1)]);
    assert!(w.nodes[0].table(&at(0)).get(&at(0)).is_none());
    // Told of again by a peer: not taken again.
    let mut addrs = Addrs::new();
    addrs.push(at(0));
    w.inject(at(1), 0, &Message::Peers(addrs));
    w.run(100 * MILLI);
    let now = w.now;
    assert!(w.nodes[0].table(&at(0)).get(&at(0)).is_none() && !w.nodes[0].add_peer(at(0), false, now));
}

#[test]
fn a_node_that_says_goodbye_is_known_at_once_to_be_gone() {
    let mut cfg = Config::default();
    cfg.peers.target = 1;
    let mut w = World::new(3, &cfg);
    w.nodes[0].add_peer(at(1), false, 0);
    w.nodes[0].add_peer(at(2), false, 0);
    w.run(SECOND);
    assert_eq!(w.live(1), [at(0)]);
    let mut sent = Vec::new();
    let now = w.now;
    w.nodes[0].goodbye(now, &mut |to, b| sent.push((to, b.to_vec())));
    assert_eq!(sent.len(), 2);
    for (to, bytes) in sent {
        w.post(at(0), to, &bytes);
    }
    w.run(30 * MILLI);
    assert!(w.live(1).is_empty() && w.live(2).is_empty());
    // Its place is kept, and when it answers a ping again it is back.
    assert!(w.nodes[1].table(&at(0)).get(&at(0)).is_some());
    w.run(31 * SECOND);
    assert_eq!(w.live(1), [at(0)]);
}

// -- Headers
//
// With `sync.blocks` at nothing where a test is of headers alone.

/// Settings under which a few dozen blocks are many runs of headers.
fn small_runs() -> Config {
    let mut cfg = Config::default();
    cfg.sync.headers = 10;
    cfg
}

#[test]
fn a_node_behind_takes_the_headers_of_one_ahead() {
    let chains = vec![chain_of(easy()), chain_of(easy())];
    grow(&chains[0], 45, 1);
    let mut w = World::with(chains, &small_runs());
    w.nodes[1].add_peer(at(0), false, 0);
    // (Headers only, for this: nobody is asked for a body.)
    w.nodes[1].cfg.sync.blocks = 0;
    w.run(10 * SECOND);
    let tip = w.nodes[0].chain().tip().unwrap();
    assert_eq!(w.best(1), tip);
    // Asked once where the chains part; five runs of headers fetched
    // (four of ten and one of five), none given up.
    let c = w.nodes[1].counts();
    assert_eq!((c.forks_asked, c.fetched, c.fetches_failed, c.headers), (1, 5, 0, 45));
    assert!(w.nodes[1].list().aim.is_none() && w.nodes[1].fetching() == 0);
    // Headers only: its chain is where it was, and the bodies are
    // what it lacks.
    assert_eq!(w.nodes[1].chain().tip().unwrap().height, 0);
    let mut missing = [tip; 8];
    assert_eq!(w.nodes[1].chain().missing_bodies(&mut missing).unwrap(), 8);
    assert_eq!(missing[0].height, 1);
    // Having them, it asks for no more; and the one ahead never asked.
    w.run(60 * SECOND);
    assert_eq!((w.nodes[1].counts().forks_asked, w.nodes[0].counts().forks_asked), (1, 0));
    assert_eq!(w.nodes[0].table(&at(1)).get(&at(1)).unwrap().delivered, 0);
    assert_eq!(w.nodes[1].table(&at(0)).get(&at(0)).unwrap().delivered, 5);
}

/// Two chains that part: the node with less work takes the headers of
/// the other's branch from where they part, and the other takes none.
#[test]
fn headers_are_taken_from_where_two_chains_part() {
    let chains = vec![chain_of(easy()), chain_of(easy())];
    let shared = grow(&chains[0], 24, 1);
    give(&chains[1], &shared);
    grow(&chains[0], 14, 2);
    grow(&chains[1], 3, 3);
    let mut w = World::with(chains, &small_runs());
    w.nodes[0].add_peer(at(1), false, 0);
    w.nodes[1].cfg.sync.blocks = 0;
    w.run(10 * SECOND);
    assert_eq!(w.best(1), w.nodes[0].chain().tip().unwrap());
    // Fourteen headers, not thirty-eight: in two runs.
    let c = w.nodes[1].counts();
    assert_eq!((c.forks_asked, c.fetched, c.headers), (1, 2, 14));
    assert_eq!((w.nodes[0].counts().forks_asked, w.best(0).height), (0, 38));
    // Its own chain is still its own, until it has the bodies.
    assert_eq!(w.nodes[1].chain().tip().unwrap().height, 27);
}

/// With several peers ahead the runs come from several of them, and
/// with a fifth of all datagrams lost they come all the same.
#[test]
fn runs_of_headers_come_from_several_peers() {
    for loss in [0, 200] {
        let chains: Vec<_> = (0..4).map(|_| chain_of(easy())).collect();
        let blocks = grow(&chains[0], 45, 1);
        give(&chains[1], &blocks);
        give(&chains[2], &blocks);
        let mut w = World::with(chains, &small_runs());
        w.loss = loss;
        for i in 0..3 {
            w.nodes[3].add_peer(at(i), false, 0);
        }
        w.nodes[3].cfg.sync.blocks = 0;
        w.run(60 * SECOND);
        assert_eq!(w.best(3).height, 45, "loss {loss}");
        assert_eq!(w.nodes[3].counts().headers, 45);
        let served: Vec<u32> = (0..3).map(|i| w.nodes[3].table(&at(i)).get(&at(i)).unwrap().delivered).collect();
        assert_eq!(served.iter().sum::<u32>(), 5, "loss {loss}");
        // From all three; where datagrams are lost, from whichever of
        // them had answered a ping by then, two at the least.
        let most_idle = if loss == 0 { 0 } else { 1 };
        assert!(served.iter().filter(|n| **n == 0).count() <= most_idle, "loss {loss}: {served:?}");
    }
}

/// A peer that claims more work than anyone and answers nothing for it
/// is doubted, and the headers come from the one that has them.
#[test]
fn a_false_claim_of_work_does_not_hold_a_node_up() {
    let chains: Vec<_> = (0..3).map(|_| chain_of(easy())).collect();
    grow(&chains[0], 12, 1);
    let mut w = World::with(chains, &small_runs());
    // Node 1 has nothing, says it has everything, and says no more.
    w.nodes[1].boast = Some(U256::MAX);
    w.mute = vec![1];
    w.nodes[2].add_peer(at(0), false, 0);
    w.nodes[2].add_peer(at(1), false, 0);
    w.nodes[2].cfg.sync.blocks = 0;
    w.run(10 * SECOND);
    // Asked first, as the one claiming most, and asked again every
    // two seconds; nothing came of it.
    assert_eq!((w.best(2).height, w.nodes[2].counts().forks_asked), (0, 5));
    assert_eq!(w.nodes[0].counts().unheard, 0, "the one that has them was not asked");
    // Fifteen seconds, and it is passed over for the one that answers.
    w.run(10 * SECOND);
    assert_eq!(w.best(2), w.nodes[0].chain().tip().unwrap());
    let now = w.now;
    assert!(!w.nodes[2].table(&at(1)).may_ask(&at(1), now) && w.nodes[2].table(&at(0)).may_ask(&at(0), now));
    // And one that answers where the chains part and then has no
    // headers to show is passed over the same.
    w.mute.clear();
    let mut w2 = World::with(vec![chain_of(easy()), chain_of(easy())], &small_runs());
    w2.nodes[0].boast = Some(U256::MAX);
    w2.nodes[1].add_peer(at(0), false, 0);
    w2.run(5 * SECOND);
    let now = w2.now;
    assert_eq!((w2.best(1).height, w2.nodes[1].counts().forks_asked), (0, 1));
    assert!(!w2.nodes[1].table(&at(0)).may_ask(&at(0), now));
}

/// A peer that serves headers that are not the chain's takes a strike
/// each time, and is refused in the end; the headers come from another.
#[test]
fn a_peer_that_serves_wrong_headers_is_struck() {
    let chains: Vec<_> = (0..3).map(|_| chain_of(easy())).collect();
    let blocks = grow(&chains[0], 12, 1);
    give(&chains[1], &blocks);
    let mut cfg = small_runs();
    // (Asked again sooner than ten minutes on, so that the strikes
    // come within the time they are counted over.)
    cfg.sync.pass_over = 2 * SECOND;
    let mut w = World::with(chains, &cfg);
    w.nodes[0].spoil = true;
    w.nodes[2].add_peer(at(0), false, 0);
    w.run(4 * SECOND);
    // One wrong run: a strike, nothing kept from it, and the aim let go.
    assert_eq!(w.best(2).height, 0);
    assert!(w.nodes[2].counts().fetched >= 1 && w.nodes[2].list().aim.is_none());
    assert!(w.nodes[2].table(&at(0)).get(&at(0)).is_some());
    // Five, and its host is refused.
    w.run(60 * SECOND);
    let now = w.now;
    assert!(w.nodes[2].table(&at(0)).get(&at(0)).is_none());
    let refusal = w.nodes[2].table(&at(0)).refusal(&at(0), false, now);
    assert_eq!(refusal, Some(crate::net::peers::Refused::Banned));
    assert_eq!(w.best(2).height, 0);
    // An honest peer turns up: from it they are taken.
    w.nodes[2].add_peer(at(1), false, now);
    w.run(10 * SECOND);
    assert_eq!(w.best(2), w.nodes[1].chain().tip().unwrap());
}

/// Where two chains part is taken only as the answer to our own
/// question, from whom it was put to; and an answer that names a block
/// we do not have, or not at that height, is a lie and a strike.
#[test]
fn where_chains_part_is_believed_only_as_an_answer() {
    let chains = vec![chain_of(easy()), chain_of(easy())];
    grow(&chains[0], 12, 1);
    let mut w = World::with(chains, &small_runs());
    let genesis = w.nodes[1].genesis;
    w.nodes[1].add_peer(at(0), false, 0);
    // Unasked, before any question; and from one who was not asked.
    w.inject(at(0), 1, &Message::Fork { height: 0, id: genesis });
    w.inject(at(9), 1, &Message::Fork { height: 0, id: genesis });
    w.wake = vec![Micros::MAX; 2];
    w.run(10 * MILLI);
    assert_eq!((w.nodes[1].counts().unheard, w.nodes[1].list().aim.is_none()), (2, true));
    // Node 0 claims much and its true answers are lost; what arrives
    // in their place names a block nobody has, or the first block at
    // a height that is not its own.
    w.wake = vec![0; 2];
    w.nodes[0].boast = Some(U256::MAX);
    w.mute = vec![0];
    for k in 0..5u32 {
        assert!(w.nodes[1].table(&at(0)).get(&at(0)).is_some() || k == 0, "after {k}");
        w.run(2100 * MILLI);
        let lie = if k % 2 == 0 {
            Message::Fork { height: 3, id: [(77 + k) as u8; 32] }
        } else {
            Message::Fork { height: 3, id: genesis }
        };
        w.inject(at(0), 1, &lie);
        w.run(50 * MILLI);
        assert!(w.nodes[1].list().aim.is_none() && w.best(1).height == 0);
    }
    let now = w.now;
    assert_eq!(w.nodes[1].peers.add(at(0), false, now), Err(crate::net::peers::Refused::Banned));
}

/// What a node serves is of one chain, by its name: headers past the
/// block named, or on a chain that block is not on, are not served.
#[test]
fn headers_are_served_only_of_the_chain_named() {
    let chains = vec![chain_of(easy()), chain_of(easy())];
    grow(&chains[0], 20, 1);
    let mut w = World::with(chains, &Config::default());
    let node = &mut w.nodes[0];
    let at_height = |n: &TestNode, h: u32| n.chain().header_at(h).unwrap().unwrap();
    let (ten, tip) = (at_height(node, 10).hash(), at_height(node, 20).hash());
    let headers = |from, count, on| Object::Headers { from, count, on };
    let made = node.make(&headers(5, 6, ten)).unwrap();
    assert_eq!(made.len(), 6 * HEADER_SIZE);
    assert_eq!(Header::from_bytes(&made[..HEADER_SIZE]).unwrap(), at_height(node, 5));
    assert_eq!(Header::from_bytes(&made[5 * HEADER_SIZE..]).unwrap(), at_height(node, 10));
    // The same bytes under the tip's name, where they overlap.
    assert_eq!(node.make(&headers(5, 6, tip)).unwrap(), made);
    // Past the block named; a block not on the chain; a block unknown.
    assert!(node.make(&headers(5, 7, ten)).is_none());
    assert!(node.make(&headers(20, 2, tip)).is_none());
    assert!(node.make(&headers(1, 1, [5u8; 32])).is_none());
    let side = chain_of(easy());
    let branch = grow(&side, 3, 9);
    // A block whose header is kept, and that is on no chain of ours.
    let stray = *BlockRef::from_bytes(&branch[0]).unwrap().header();
    assert_eq!(node.chain().accept_headers(&[stray], NOW, false), (1, None));
    assert!(node.chain().known(&stray.hash()).unwrap().is_some());
    assert!(node.make(&headers(1, 1, stray.hash())).is_none());
    // Kept while it is asked for, and the same each time.
    assert!(Arc::ptr_eq(&node.object(&headers(5, 6, ten)).unwrap(), &node.object(&headers(5, 6, ten)).unwrap()));
}

/// Two nodes on this machine's own sockets and clock: one comes to know
/// the other and takes its headers and then its blocks.
#[test]
fn over_real_sockets() {
    sockets_sync(1);
}

/// How long nodes on real sockets are given to do what is asked of
/// them. A build that is not optimized checks a block in a second or
/// more, and on a machine that runs every other test at once forty-five
/// of them have taken the minute that an optimized build does it all in
/// a dozen times over: what looked like a node stuck at block 35, or
/// 38, or 39 of 45 was one still going.
const SOCKETS_WITHIN: std::time::Duration =
    std::time::Duration::from_secs(if cfg!(debug_assertions) { 300 } else { 60 });

/// And each with four workers, every one on a thread of its own.
#[test]
fn over_real_sockets_with_several_workers() {
    sockets_sync(4);
}

fn sockets_sync(workers: usize) {
    use std::net::UdpSocket;
    use std::sync::atomic::{AtomicBool, Ordering};
    use std::time::{Duration, Instant};
    let mut cfg = small_runs();
    cfg.tick = 50 * MILLI;
    cfg.workers = workers;
    // (Fewer blocks unoptimized, where checking one takes the better
    // part of a second, more on a machine that runs every other test
    // meanwhile: the time allowed is for a fault to show in, not for
    // the checking of blocks.)
    let blocks: u32 = if cfg!(debug_assertions) { 25 } else { 45 };
    let chains = vec![chain_of(easy()), chain_of(easy())];
    grow(&chains[0], blocks as usize, 1);
    let tip = chains[0].tip().unwrap();
    let sockets: Vec<UdpSocket> = (0..2).map(|_| UdpSocket::bind("127.0.0.1:0").unwrap()).collect();
    let SocketAddr::V4(first) = sockets[0].local_addr().unwrap() else { unreachable!() };
    let stop = Arc::new(AtomicBool::new(false));
    let (ahead, behind) = (Arc::clone(&chains[0]), Arc::clone(&chains[1]));
    let threads: Vec<_> = sockets
        .into_iter()
        .zip(chains)
        .enumerate()
        .map(|(i, (socket, chain))| {
            let (cfg, stop) = (cfg.clone(), Arc::clone(&stop));
            std::thread::spawn(move || {
                let mut node = Node::new(cfg, NET, chain, [i as u8 + 1; 32], 0).threaded().by_port();
                if i == 1 {
                    node.add_peer(first, true, 0);
                }
                // (These headers' times are held against the time they
                // were made for, not this machine's.)
                crate::net::socket::run_until(&mut node, &socket, &stop, Instant::now(), &|| NOW).unwrap();
                node.counts()
            })
        })
        .collect();
    let start = Instant::now();
    // (When its headers were all in, and when its first block was: said
    // if it is too slow, so that it is known which of the two was.)
    let (mut headers, mut first) = (None, None);
    while behind.tip().unwrap() != tip {
        if headers.is_none() && behind.best_header().is_ok_and(|b| b.header.height == tip.height) {
            headers = Some(start.elapsed());
        }
        if first.is_none() && behind.tip().unwrap().height > 0 {
            first = Some(start.elapsed());
        }
        assert!(
            start.elapsed() < SOCKETS_WITHIN,
            "at {} of {}: its headers were in after {headers:?}, its first block after {first:?}; \
             the highest body it has is of block {:?}",
            behind.tip().unwrap().height,
            tip.height,
            (1..=tip.height).rev().find(|h| {
                let id = ahead.header_at(*h).unwrap().unwrap().hash();
                behind.body(&id).is_ok_and(|b| b.is_some())
            })
        );
        std::thread::sleep(Duration::from_millis(20));
    }
    // (A moment for the node to hear of the last block from the thread
    // that applied it.)
    std::thread::sleep(Duration::from_millis(300));
    stop.store(true, Ordering::Relaxed);
    let counts: Vec<Counts> = threads.into_iter().map(|t| t.join().unwrap()).collect();
    // The runs of headers, ten to a run, and a body for each block, the
    // blocks applied on a thread of their own.
    let runs = blocks.div_ceil(10);
    assert_eq!(
        (counts[1].fetched as u32, counts[1].headers as u32, counts[1].fetches_failed),
        (runs + blocks, blocks, 0)
    );
    assert_eq!((counts[1].blocks as u32, counts[1].blocks_refused), (blocks, 0));
}

/// The request log's line: who, how long, what was asked and what was
/// done, the first two in columns.
#[test]
fn a_request_is_one_line() {
    use crate::net::node::{About, Heard};
    let from = Some(at(0));
    let heard = |request, about, answer, sent, sent_bytes| Heard { from, request, about, answer, sent, sent_bytes };
    let a = heard("ping", About::Height(88_214), "pong", 1, 133).line(133, 41);
    let b = heard("get", About::Chunks { of: "block", chunks: 1712 }, "queued", 0, 0).line(96, 1_250);
    let c = heard("block", About::Block { height: 7, bytes: 1_999_000 }, "answered", 2, 300).line(250, 9);
    let d = Heard { from: None, ..heard("ipv6", About::Nothing, "malformed", 0, 0) }.line(40, 0);
    let who = at(0).to_string();
    assert_eq!(a, format!("{who:<22}41 micros       ping height 88,214 (133 bytes) -> pong (133 bytes)"));
    assert_eq!(b, format!("{who:<22}1,250 micros    get block, 1,712 chunks (96 bytes) -> queued"));
    assert_eq!(
        c,
        format!(
            "{who:<22}9 micros        block height 7 of 1,999,000 bytes (250 bytes) -> answered (2 datagrams, 300 bytes)"
        )
    );
    assert_eq!(d, format!("{:<22}0 micros        ipv6 (40 bytes) -> malformed", "-"));
}

/// What a node says of a datagram: what it was, and what it did.
#[test]
fn a_node_says_what_it_heard_and_did() {
    let mut w = World::with(vec![chain_of(easy()), chain_of(easy())], &small_runs());
    w.nodes[1].add_peer(at(0), false, 0);
    // The first thing a node sends a peer is a ping.
    let mut sent = Vec::new();
    w.nodes[1].tick(0, NOW, &mut |to, bytes: &[u8]| sent.push((to, bytes.to_vec())));
    let (to, ping) = sent.first().cloned().expect("a ping");
    assert_eq!(to, at(0));
    let mut answers = Vec::new();
    let heard =
        w.nodes[0].handle(1, SocketAddr::V4(at(1)), &ping, &mut |to, bytes: &[u8]| answers.push((to, bytes.len())));
    // (The pong, and a ping of its own to one it did not know.)
    assert_eq!((heard.from, heard.request, heard.answer, heard.sent), (Some(at(1)), "ping", "pong", 2));
    assert_eq!(heard.about, crate::net::node::About::Height(0));
    assert!(answers.iter().all(|(to, _)| *to == at(1)));
    assert_eq!(answers.iter().map(|(_, n)| n).sum::<usize>(), heard.sent_bytes as usize);
    // What is no message, and a request without its token.
    let heard = w.nodes[0].handle(2, SocketAddr::V4(at(1)), b"nothing of ours", &mut |_, _| panic!("no answer"));
    assert_eq!((heard.request, heard.answer, heard.sent), ("malformed", "malformed", 0));
    let mut buf = [0u8; crate::net::MAX_DATAGRAM];
    let n = Message::GetPeers { token: 12345 }.encode(NET, &mut buf);
    let heard = w.nodes[0].handle(3, SocketAddr::V4(at(1)), &buf[..n], &mut |_, _| panic!("no answer"));
    assert_eq!((heard.request, heard.answer), ("get-peers", "unheard"));
}

/// Over real sockets, with the logs: each request has its line in the
/// request log, and the stats count them, how long they took and what
/// went each way.
#[test]
fn over_real_sockets_requests_are_logged_and_counted() {
    use crate::logger::queued::Queued;
    use crate::logger::stats::Stats;
    use crate::logger::{Logger, Rotation};
    use crate::net::socket::{self, Watch};
    use std::net::UdpSocket;
    use std::sync::atomic::{AtomicBool, Ordering};
    use std::time::{Duration, Instant};
    let dir = std::env::temp_dir().join(format!("tabminer-watched-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    let main = Arc::new(Logger::open(dir.join("tabernacle.log"), Rotation::default()).unwrap());
    let mut cfg = small_runs();
    cfg.tick = 50 * MILLI;
    let chains = vec![chain_of(easy()), chain_of(easy())];
    grow(&chains[0], 12, 1);
    let tip = chains[0].tip().unwrap();
    let sockets: Vec<UdpSocket> = (0..2).map(|_| UdpSocket::bind("127.0.0.1:0").unwrap()).collect();
    let SocketAddr::V4(first) = sockets[0].local_addr().unwrap() else { unreachable!() };
    let SocketAddr::V4(second) = sockets[1].local_addr().unwrap() else { unreachable!() };
    let stop = Arc::new(AtomicBool::new(false));
    let behind = Arc::clone(&chains[1]);
    let threads: Vec<_> = sockets
        .into_iter()
        .zip(chains)
        .enumerate()
        .map(|(i, (socket, chain))| {
            let (cfg, stop, main, dir) = (cfg.clone(), Arc::clone(&stop), Arc::clone(&main), dir.clone());
            std::thread::spawn(move || {
                let log = Logger::open(dir.join(format!("request{i}.log")), Rotation::default()).unwrap();
                let requests = Queued::start(log, 100_000, main).unwrap();
                let stats = Stats::new(socket::STATS);
                let mut node = Node::new(cfg, NET, chain, [i as u8 + 1; 32], 0).threaded().by_port();
                if i == 1 {
                    node.add_peer(first, true, 0);
                }
                let watch = Watch { requests: Some(&requests), stats: Some(&stats), main: None };
                socket::run_watched(&mut node, &socket, &stop, Instant::now(), &|| NOW, &watch).unwrap();
                requests.flush();
                stats.read()
            })
        })
        .collect();
    let start = Instant::now();
    // (When its headers were all in, and when its first block was: said
    // if it is too slow, so that it is known which of the two was.)
    let (mut headers, mut first) = (None, None);
    while behind.tip().unwrap() != tip {
        if headers.is_none() && behind.best_header().is_ok_and(|b| b.header.height == tip.height) {
            headers = Some(start.elapsed());
        }
        if first.is_none() && behind.tip().unwrap().height > 0 {
            first = Some(start.elapsed());
        }
        assert!(
            start.elapsed() < SOCKETS_WITHIN,
            "at {} of {}: its headers were in after {headers:?}, its first block after {first:?}",
            behind.tip().unwrap().height,
            tip.height
        );
        std::thread::sleep(Duration::from_millis(20));
    }
    // (Long enough for how the nodes stand to be told once more.)
    std::thread::sleep(Duration::from_millis(1300));
    stop.store(true, Ordering::Relaxed);
    let stats: Vec<Vec<u64>> = threads.into_iter().map(|t| t.join().unwrap()).collect();
    let logs: Vec<String> =
        (0..2).map(|i| std::fs::read_to_string(dir.join(format!("request{i}.log"))).unwrap()).collect();
    // The one ahead was pinged and asked for headers and blocks, and
    // every line says who asked, how long it took and what was done.
    let served: Vec<&str> = logs[0].lines().collect();
    let asked = |what: &str| served.iter().filter(|l| l.contains(what)).count();
    assert!(asked(" ping height 0 (") >= 1 && asked(") -> pong (") >= 1, "{}", logs[0]);
    assert!(asked(" get headers, ") >= 1 && asked(" get block, ") >= 12, "{}", logs[0]);
    assert!(asked(") -> queued") >= 13, "{}", logs[0]);
    for line in &served {
        assert!(line[26..].starts_with(&format!("{:<22}", second.to_string())), "{line}");
        assert!(
            line[48..].split_once(" micros").is_some_and(|(n, _)| n.replace(',', "").parse::<u64>().is_ok()),
            "{line}"
        );
    }
    // The one behind got its answers, and a line for none of the chunks.
    assert!(logs[1].contains(" pong height 12 (") && !logs[1].contains(" chunk "), "{}", logs[1]);
    // Every datagram is counted, chunks too, with the time it took.
    use socket::{BLOCKS, BYTES_IN, BYTES_SENT, FETCHING, HEIGHT, LATENCY, PEERS, PEERS_LIVE, REQUESTS};
    assert_eq!(stats[0][REQUESTS] as usize, served.len());
    assert_eq!(stats[1][REQUESTS] as usize, logs[1].lines().count());
    // The chunks of its blocks were packets, and no requests.
    assert!(stats[1][socket::PACKETS] > stats[1][REQUESTS] && stats[0][socket::PACKETS] == stats[0][REQUESTS]);
    for s in &stats {
        assert!(s[LATENCY] > 0 && s[BYTES_IN] > 0 && s[BYTES_SENT] > 0, "{s:?}");
        assert_eq!((s[PEERS], s[PEERS_LIVE], s[HEIGHT], s[FETCHING]), (1, 1, 12, 0), "{s:?}");
    }
    // What one sent is what the other took in: but for a datagram or
    // two on its way when the nodes were stopped, sent and never taken.
    for (sent, taken) in [(stats[0][BYTES_SENT], stats[1][BYTES_IN]), (stats[1][BYTES_SENT], stats[0][BYTES_IN])] {
        assert!(taken <= sent && sent - taken <= 2 * crate::net::MAX_DATAGRAM as u64, "sent {sent}, taken {taken}");
    }
    assert_eq!((stats[0][BLOCKS], stats[1][BLOCKS]), (0, 12));
    let _ = std::fs::remove_dir_all(&dir);
}

// -- Blocks

fn tip(w: &World, i: usize) -> Header {
    w.nodes[i].chain().tip().unwrap()
}

/// A node behind takes the blocks of one ahead: its chain and its
/// state end as the other's.
#[test]
fn a_node_behind_takes_the_blocks_of_one_ahead() {
    for loss in [0, 200] {
        let chains = vec![chain_of(easy()), chain_of(easy())];
        grow(&chains[0], 30, 1);
        let mut w = World::with(chains, &small_runs());
        w.loss = loss;
        w.nodes[1].add_peer(at(0), false, 0);
        w.run(40 * SECOND);
        assert_eq!(tip(&w, 1), tip(&w, 0), "loss {loss}");
        assert_eq!(w.nodes[1].chain().state().root(), w.nodes[0].chain().state().root());
        let c = w.nodes[1].counts();
        assert_eq!((c.headers, c.blocks, c.blocks_refused), (30, 30, 0), "loss {loss}");
        assert!(
            w.nodes[1].list().held.is_empty() && w.nodes[1].list().applying.is_empty() && w.nodes[1].fetching() == 0
        );
        if loss == 0 {
            // Three runs of headers and thirty bodies, each once.
            assert_eq!((c.fetched, c.fetches_failed), (33, 0));
        }
        // It told the other of each block as it joined, and the other,
        // having them, fetched none.
        assert_eq!((w.nodes[0].counts().fetched, w.nodes[0].counts().blocks), (0, 0));
    }
}

/// A block made on one node is on all of them in a moment, fetched by
/// each once.
#[test]
fn a_new_block_crosses_the_network() {
    let mut w = World::new(8, &Config::default());
    for i in 1..8 {
        w.nodes[i].add_peer(at(0), true, 0);
    }
    w.run(20 * SECOND);
    assert!((0..8).all(|i| w.live(i).len() == 7));
    for round in 1..=3u32 {
        // Made on another node each time.
        let maker = round as usize * 2;
        let block = next_block(w.nodes[maker].chain(), round, true);
        w.nodes[maker].mined(block);
        w.wake[maker] = w.now;
        w.run(500 * MILLI);
        let made = tip(&w, maker);
        assert_eq!(made.height, round);
        for i in 0..8 {
            assert_eq!(tip(&w, i), made, "round {round}, node {i}");
        }
    }
    for i in 0..8 {
        let c = w.nodes[i].counts();
        // Three blocks joined each chain; a node fetched those it did
        // not make, each once, and announced each to the others.
        let made = [2, 4, 6].contains(&i) as u64;
        assert_eq!((c.blocks, c.blocks_refused, c.fetches_failed), (3, 0, 0), "node {i}");
        assert_eq!(c.fetched, 3 - made, "node {i}");
        assert!(c.announced >= 3 * 6 && c.announced <= 3 * 7, "node {i}: {}", c.announced);
    }
}

/// A node on a branch with less work goes over to the branch with
/// more, undoing its own blocks.
#[test]
fn a_node_goes_over_to_the_branch_with_more_work() {
    let chains = vec![chain_of(easy()), chain_of(easy())];
    let shared = grow(&chains[0], 10, 1);
    give(&chains[1], &shared);
    grow(&chains[0], 6, 2);
    let own = grow(&chains[1], 2, 3);
    let mut w = World::with(chains, &small_runs());
    w.nodes[1].add_peer(at(0), false, 0);
    w.run(10 * SECOND);
    assert_eq!((tip(&w, 1), tip(&w, 1).height), (tip(&w, 0), 16));
    assert_eq!(w.nodes[1].chain().state().root(), w.nodes[0].chain().state().root());
    // Its own two blocks are kept, off the chain; the other never
    // wanted them.
    let was = BlockRef::from_bytes(&own[1]).unwrap().header().hash();
    assert!(w.nodes[1].chain().known(&was).unwrap().is_some() && w.nodes[1].on_chain(&was).is_none());
    assert_eq!(w.nodes[0].counts().fetched, 0);
}

/// A node that hears of a block whose parent it does not know asks for
/// the headers at once, without waiting for the next ping to say how
/// far the other has got.
#[test]
fn an_announcement_from_far_ahead_is_followed_at_once() {
    let mut cfg = small_runs();
    cfg.peers.target = 1;
    let chains = vec![chain_of(easy()), chain_of(easy())];
    let mut w = World::with(chains, &cfg);
    w.nodes[1].add_peer(at(0), false, 0);
    w.run(2 * SECOND);
    // Node 0 gets seven blocks that node 1 hears nothing of.
    w.mute = vec![0];
    for k in 0..7 {
        let block = next_block(w.nodes[0].chain(), 10 + k, true);
        w.nodes[0].mined(block);
        w.wake[0] = w.now;
        w.run(10 * MILLI);
    }
    assert_eq!((tip(&w, 0).height, tip(&w, 1).height), (7, 0));
    // The eighth it hears of: within a second it has all eight, half a
    // minute before the next ping would have told it.
    w.mute.clear();
    let block = next_block(w.nodes[0].chain(), 99, true);
    w.nodes[0].mined(block);
    w.wake[0] = w.now;
    w.run(SECOND);
    assert_eq!(tip(&w, 1), tip(&w, 0));
    // Its last ping said nothing of them: it was the announcement.
    assert_eq!(w.nodes[1].table(&at(0)).get(&at(0)).unwrap().status.unwrap().work, U256::ZERO);
}

/// A peer that serves a body that is not its header's is struck, and
/// the body is taken from another.
#[test]
fn a_wrong_body_is_refused_and_fetched_elsewhere() {
    let chains: Vec<_> = (0..3).map(|_| chain_of(easy())).collect();
    let blocks = grow(&chains[0], 4, 1);
    give(&chains[1], &blocks);
    let mut w = World::with(chains, &small_runs());
    w.nodes[0].spoil = true;
    w.nodes[2].add_peer(at(0), false, 0);
    w.run(5 * SECOND);
    // Its headers were spoiled too, so nothing came of it at all.
    assert_eq!((tip(&w, 2).height, w.best(2).height), (0, 0));
    // Headers from the honest one; bodies asked of both.
    w.nodes[0].spoil = false;
    let now = w.now;
    w.nodes[2].add_peer(at(1), false, now);
    w.run(3 * SECOND);
    assert_eq!(w.best(2).height, 4);
    w.nodes[0].spoil = true;
    w.nodes[0].served.clear();
    w.run(20 * SECOND);
    assert_eq!(tip(&w, 2), tip(&w, 1));
    assert_eq!(w.nodes[2].chain().state().root(), w.nodes[1].chain().state().root());
}

/// A block that breaks a rule is refused, remembered, and held against
/// whoever served it; told of it again, a node does not fetch it again.
#[test]
fn a_block_that_breaks_a_rule_is_refused_once() {
    let mut cfg = small_runs();
    cfg.peers.target = 1;
    let mut w = World::new(2, &cfg);
    w.nodes[1].add_peer(at(0), false, 0);
    w.run(2 * SECOND);
    // Node 0 announces, and serves, a block whose state root is not
    // what its body gives: nothing its own chain would take.
    let bad = next_block(w.nodes[0].chain(), 5, false);
    let header = *BlockRef::from_bytes(&bad).unwrap().header();
    w.nodes[0].foist = Some((header.hash(), bad[HEADER_SIZE..].to_vec()));
    let announce = |w: &mut World| {
        let now = w.now;
        let mut sent = Vec::new();
        w.nodes[0]
            .announce(now, header, (bad.len() - HEADER_SIZE) as u32, None, &mut |to, b| sent.push((to, b.to_vec())));
        for (to, bytes) in sent {
            w.post(at(0), to, &bytes);
        }
    };
    announce(&mut w);
    w.run(SECOND);
    let c = w.nodes[1].counts();
    assert_eq!((c.fetched, c.blocks, c.blocks_refused, tip(&w, 1).height), (1, 0, 1, 0));
    let known = w.nodes[1].chain().known(&header.hash()).unwrap().unwrap();
    assert!(known.invalid());
    // Told again: not fetched again.
    announce(&mut w);
    w.run(SECOND);
    assert_eq!(w.nodes[1].counts().fetched, 1);
    // And a good block after it, from the same peer, is passed over
    // for a while: it has a strike, and failed us.
    let now = w.now;
    assert!(!w.nodes[1].table(&at(0)).may_ask(&at(0), now));
}

/// A block kept on a side branch has its proof looked at only when the
/// branch is tried. If it does not hold then, whoever served that block
/// answers for it, and not whoever served the block that had the branch
/// tried.
#[test]
fn a_bad_proof_on_a_side_branch_is_held_against_who_served_it() {
    let chains: Vec<_> = (0..3).map(|_| chain_of(easy())).collect();
    let blocks = grow(&chains[0], 2, 1);
    let headers: Vec<Header> = blocks.iter().map(|b| *BlockRef::from_bytes(b).unwrap().header()).collect();
    let mut w = World::with(chains, &small_runs());
    w.nodes[2].add_peer(at(0), false, 0);
    w.nodes[2].add_peer(at(1), false, 0);
    w.run(2 * SECOND);
    let now = w.now;
    assert!(w.nodes[2].table(&at(0)).may_ask(&at(0), now) && w.nodes[2].table(&at(1)).may_ask(&at(1), now));
    // The first came from node 0 and was kept beside the chain; the
    // second, from node 1, had the branch tried, and the first's proof
    // did not hold.
    let (first, second) = (headers[0], headers[1]);
    let bad = Error::BadProofBefore(Error::id_half(&first.hash()));
    w.nodes[2].with_list(|n, l| n.block_applied(l, now, first, 100, Some(at(0)), Ok(Applied::Side), &mut |_, _| {}));
    w.nodes[2].with_list(|n, l| n.block_applied(l, now, second, 100, Some(at(1)), Err(bad), &mut |_, _| {}));
    w.run(SECOND / 10);
    let now = w.now;
    assert!(!w.nodes[2].table(&at(0)).may_ask(&at(0), now), "who served the bad proof is passed over");
    assert!(w.nodes[2].table(&at(1)).may_ask(&at(1), now), "who served the good block is not");
    // It is held against them once: the block is theirs no more.
    w.nodes[2].with_list(|_, l| assert!(l.sides.is_empty()));
}

/// Bodies are kept only for the blocks that can be undone. A node says
/// from where it has them, and is asked for nothing below; one too far
/// behind for anyone's bodies has the headers and waits for the state.
#[test]
fn bodies_are_asked_only_of_those_that_hold_them() {
    let chains = vec![chain_of(easy()), chain_of(easy())];
    grow(&chains[0], KEEP + 6, 1);
    // (Set never to take a state whole, which it otherwise would.)
    let mut cfg = small_runs();
    cfg.sync.sync_point = 0;
    let mut w = World::with(chains, &cfg);
    w.nodes[1].add_peer(at(0), false, 0);
    w.run(20 * SECOND);
    let said = w.nodes[1].table(&at(0)).get(&at(0)).unwrap().status.unwrap();
    assert_eq!((said.height, said.oldest, said.window), (KEEP as u32 + 6, 7, 6));
    // Every header, no body: the first it needs is the first block's,
    // which nobody holds.
    let c = w.nodes[1].counts();
    assert_eq!((w.best(1).height, tip(&w, 1).height), (KEEP as u32 + 6, 0));
    assert_eq!((c.headers, c.blocks, c.fetches_failed), (KEEP as u64 + 6, 0, 0));
    assert_eq!(c.fetched, 7, "seven runs of headers, and nothing else");
    // What a node is asked for and does not hold, it says it has not.
    let first = w.nodes[0].chain().header_at(1).unwrap().unwrap().hash();
    assert!(w.nodes[0].make(&Object::Block(first)).is_none());
    let seventh = w.nodes[0].chain().header_at(7).unwrap().unwrap().hash();
    assert!(w.nodes[0].make(&Object::Block(seventh)).is_some());
}

// -- The state, in pieces

/// The state as of a block is served in pieces, each checked against
/// the one above it, and the pieces put together are that state: what
/// a joining node does, by hand.
#[test]
fn a_state_is_served_in_pieces_that_check_and_make_it_whole() {
    use crate::net::snapshot::{Manifest, decode_part, decode_roots};
    use crate::store::receive::{Receiving, Target};
    let mut cfg = small_runs();
    // (Nothing fetched but what the test asks for.)
    (cfg.sync.blocks, cfg.peers.target) = (0, 1);
    let chains = vec![chain_of(easy()), chain_of(easy())];
    grow(&chains[0], 20, 1);
    let mut w = World::with(chains, &cfg);
    w.nodes[1].add_peer(at(0), false, 0);
    w.run(3 * SECOND);
    // As of a block some way back, which the headers vouch for.
    let header =
        w.nodes[1].chain().known(&w.nodes[0].chain().header_at(15).unwrap().unwrap().hash()).unwrap().unwrap().header;
    let block = header.hash();
    let fetch = |w: &mut World, object: Object, most: usize| -> Option<Vec<u8>> {
        let now = w.now;
        assert!(w.nodes[1].fetch_object(now, object, at(0), most as u32));
        w.wake[1] = now;
        w.run(SECOND);
        let mut got = w.nodes[1].take_fetched();
        assert_eq!(got.len(), 1);
        let (what, from, bytes) = got.remove(0);
        assert_eq!((what, from), (object, at(0)));
        bytes
    };
    // The manifest, against the header.
    let bytes = fetch(&mut w, Object::Manifest(block), snapshot::MAX_MANIFEST).unwrap();
    let manifest = Manifest::decode(&bytes).unwrap();
    assert!(manifest.check(&header.state_root));
    assert_eq!((manifest.next, manifest.ranges.len(), manifest.name_parts.len()), (15, 1, 0));
    // Each range's roots, against the manifest.
    let mut parts = Vec::new();
    for (range, root) in &manifest.ranges {
        let bytes = fetch(&mut w, Object::Roots { block, index: *range }, snapshot::MAX_ROOTS).unwrap();
        parts.extend(decode_roots(&bytes, *range, root).unwrap());
    }
    assert_eq!(parts.len(), 1);
    // Each part, against its root: the store checks that as it keeps it.
    let target = Target { height: header.height, block, state_root: header.state_root, next: manifest.next };
    let mut receiving = Receiving::open(MemBackend::new(), target, &parts, &manifest.name_parts).unwrap();
    for index in receiving.missing() {
        let bytes = fetch(&mut w, Object::Part { block, index }, snapshot::MAX_PART).unwrap();
        let (outputs, commits) = decode_part(&bytes, index).unwrap();
        assert_eq!(outputs.len(), 15);
        // A part with an output's amount changed is not the part.
        let mut wrong = outputs.clone();
        wrong[3].1.amount += 1;
        assert_eq!(receiving.put_with(index, &wrong, &commits), Err(Error::PartRoot));
        receiving.put_with(index, &outputs, &commits).unwrap();
    }
    let state = receiving.finish(KEEP).unwrap();
    assert_eq!((state.root(), state.tip()), (header.state_root, (15, block)));
    // What there is none of, the peer says it has not: a range and a
    // part that hold nothing, a part of the names, the state as of a
    // block it does not have or that is not on its chain.
    for object in [
        Object::Roots { block, index: 1 },
        Object::Part { block, index: 1 },
        Object::Names { block, index: 0 },
        Object::Manifest([1u8; 32]),
    ] {
        assert_eq!(fetch(&mut w, object, 1 << 20), None, "{object:?}");
    }
    // And the state as of a block too old to go back to: a node says
    // how far back it can, in its pings.
    let said = w.nodes[1].table(&at(0)).get(&at(0)).unwrap().status.unwrap();
    assert_eq!((said.window, said.height), (0, 20));
}

/// A state can be handed over as of the blocks a node can still undo,
/// and it says in its pings from which.
#[test]
fn a_state_is_served_as_far_back_as_can_be_undone() {
    let chain = chain_of(easy());
    grow(&chain, KEEP + 9, 1);
    let mut w = World::with(vec![chain], &Config::default());
    let node = &mut w.nodes[0];
    let id = |n: &TestNode, h: u32| n.chain().header_at(h).unwrap().unwrap().hash();
    let said = node.status(&at(1), 0);
    assert_eq!((said.height, said.window, said.oldest), (KEEP as u32 + 9, 9, 10));
    for (height, served) in [(8, false), (9, true), (40, true), (KEEP as u32 + 9, true)] {
        let made = node.make(&Object::Manifest(id(node, height)));
        assert_eq!(made.is_some(), served, "as of {height}");
        if let Some(bytes) = made {
            let header = node.chain().header_at(height).unwrap().unwrap();
            let manifest = snapshot::Manifest::decode(&bytes).unwrap();
            assert!(manifest.check(&header.state_root));
            assert_eq!(manifest.next, height as u64);
        }
    }
    // What is kept to be served is bounded by its bytes, not its count.
    for height in 9..40 {
        let block = id(node, height);
        node.object(&Object::Manifest(block)).unwrap();
        node.object(&Object::Part { block, index: 0 }).unwrap();
    }
    assert!(node.served.len() == 62 && node.served.iter().map(|s| s.1.len()).sum::<usize>() <= SERVED_BYTES);
}

// -- The state, taken whole

/// Settings under which a state is taken as of a block ten under the
/// best header.
fn joining() -> Config {
    let mut cfg = small_runs();
    cfg.sync.sync_point = 10;
    cfg
}

/// A chain longer than its bodies reach back, with a state of several
/// parts: `blocks` blocks of 300 outputs.
fn long_chain(blocks: usize) -> (Arc<TestChain>, Vec<Vec<u8>>) {
    let chain = chain_of(easy());
    let made = grow_wide(&chain, blocks, 300, 1);
    (chain, made)
}

/// A node that starts with nothing, among nodes whose bodies no longer
/// reach back to the first block, takes the state as of a block ten
/// under the best header and the blocks from there: it ends where they
/// are, with their state.
#[test]
#[cfg_attr(debug_assertions, ignore = "builds long chains; run with --release")]
fn a_new_node_takes_the_state_and_goes_on_from_it() {
    for loss in [0, 150] {
        let (ahead, blocks) = long_chain(KEEP + 16);
        let also = chain_of(easy());
        give(&also, &blocks);
        let mut w = World::with(vec![ahead, also, chain_of(easy())], &joining());
        w.loss = loss;
        w.nodes[2].add_peer(at(0), false, 0);
        w.nodes[2].add_peer(at(1), false, 0);
        w.run(90 * SECOND);
        assert_eq!(tip(&w, 2), tip(&w, 0), "loss {loss}");
        assert_eq!(w.nodes[2].chain().state().root(), w.nodes[0].chain().state().root());
        let c = w.nodes[2].counts();
        // Eighty headers; the state once, as of block seventy; and the
        // ten blocks after it.
        assert_eq!((c.headers, c.states, c.states_moved, c.blocks, c.blocks_refused), (80, 1, 0, 10, 0), "loss {loss}");
        assert!(w.nodes[2].list().join.is_none() && !w.nodes[2].chain().receiving());
        // The state was of three parts (twenty-one thousand outputs),
        // and both peers served pieces of it.
        let served: Vec<u32> = (0..2).map(|i| w.nodes[2].table(&at(i)).get(&at(i)).unwrap().delivered).collect();
        assert!(served.iter().all(|n| *n >= 2), "loss {loss}: {served:?}");
        // It serves what it took: the block it took the state as of,
        // and the state as of its tip.
        let seventy = w.nodes[0].chain().header_at(70).unwrap().unwrap().hash();
        assert!(w.nodes[2].make(&Object::Block(seventy)).is_some());
        assert!(w.nodes[2].make(&Object::Manifest(tip(&w, 2).hash())).is_some());
    }
}

/// Among nodes that have every block, a node takes the state whole
/// when it is further behind than it is set to catch up from block by
/// block, and the blocks when it is not.
#[test]
#[cfg_attr(debug_assertions, ignore = "builds long chains; run with --release")]
fn a_node_far_behind_takes_the_state_though_the_blocks_could_be_had() {
    for (behind, states, taken) in [(30, 1, 10), (60, 0, 50), (0, 0, 50)] {
        let (ahead, _) = long_chain(50);
        // (The headers in one run: how far behind the node is is known
        // before the first block is asked for.)
        let mut cfg = Config::default();
        (cfg.sync.sync_point, cfg.sync.sync_behind) = (10, behind);
        let mut w = World::with(vec![ahead, chain_of(easy())], &cfg);
        w.nodes[1].add_peer(at(0), false, 0);
        w.run(90 * SECOND);
        assert_eq!(tip(&w, 1), tip(&w, 0), "behind {behind}");
        assert_eq!(w.nodes[1].chain().state().root(), w.nodes[0].chain().state().root());
        let c = w.nodes[1].counts();
        assert_eq!((c.states, c.blocks, c.blocks_refused), (states, taken, 0), "behind {behind}");
        assert!(w.nodes[1].list().join.is_none() && !w.nodes[1].chain().receiving());
    }
}

/// A fetch is too slow for the way in, or the way in is slow: which,
/// by how the others come.
#[test]
fn a_fetch_is_slow_against_the_others_not_by_itself() {
    use crate::net::node::too_slow;
    let least = 4096;
    // Fast enough is never too slow; nor is anything where no least is
    // asked.
    assert!(!too_slow(4096, 1 << 20, 1 << 21, least));
    assert!(!too_slow(0, 1 << 20, 1 << 20, 0));
    // Twenty-four fetches at 2 KB a second each over a way in of 48 KB
    // a second: each is under the least, none is four times faster
    // than another, and together they come well over it. Nobody's
    // fault.
    assert!(!too_slow(2000, 2000, 48_000, least));
    assert!(!too_slow(1000, 3999, 48_000, least));
    // One that trickles beside one that runs: its peer's.
    assert!(too_slow(100, 1 << 20, (1 << 20) + 100, least));
    assert!(too_slow(999, 4000, 48_000, least));
    // One alone that trickles, or all of them together under what one
    // should bring: given up, and asked of another.
    assert!(too_slow(100, 100, 100, least));
    assert!(too_slow(1000, 1000, 3000, least));
    assert!(!too_slow(1400, 1400, 4200, least));
}

/// A chain that leaves this one far down and is said to have more work
/// is weighed before any of it is kept; one that comes to no more than
/// there is leaves nothing behind it, and whoever told of it is passed
/// over.
#[test]
fn a_chain_far_down_with_no_more_work_is_not_kept() {
    // (This node can undo eight blocks and has twenty; the other has
    // ten from the first block, another ten, and says it has more work
    // than anyone.)
    let ours = Chain::open(MemBackend::new(), 8, easy(), seed(), AcceptAllProofs).unwrap();
    ours.set_dataset(table());
    let ours = Arc::new(ours);
    grow_wide(&ours, 20, 20, 2);
    let other = chain_of(easy());
    grow_wide(&other, 10, 20, 1);
    let mut w = World::with(vec![other, ours], &small_runs());
    w.nodes[0].boast = Some(U256::MAX);
    w.nodes[1].add_peer(at(0), false, 0);
    let before = (tip(&w, 1), w.best(1));
    // (The other chain's headers as they are now: that node, which
    // hears of more work than it has, goes over to this one's chain.)
    let theirs: Vec<Header> = (1..=10).map(|h| w.nodes[0].chain().header_at(h).unwrap().unwrap()).collect();
    w.run(30 * SECOND);
    let c = w.nodes[1].counts();
    assert_eq!((c.weighed, c.headers, c.states), (1, 0, 0));
    assert_eq!((tip(&w, 1), w.best(1)), before);
    // Nothing of the other chain is kept here.
    let kept = theirs.iter().filter(|h| w.nodes[1].chain().known(&h.hash()).unwrap().is_some()).count();
    assert_eq!(kept, 0);
    let now = w.now;
    assert!(!w.nodes[1].table(&at(0)).may_ask(&at(0), now));
    assert!(w.nodes[1].list().aim.is_none());
}

/// A node with one peer goes on asking it. A fetch that came to
/// nothing has its peer passed over, so that another is asked in its
/// place; with no other, the node asks that one again after a little
/// while, and does not stand still for as long as a peer is passed
/// over.
#[test]
fn a_node_with_one_peer_asks_it_again_after_a_fetch_fails() {
    let chains = vec![chain_of(easy()), chain_of(easy())];
    grow(&chains[0], 40, 1);
    let mut w = World::with(chains, &small_runs());
    w.nodes[1].add_peer(at(0), false, 0);
    // Some of its blocks are in and the rest asked for; then nothing
    // gets through, until a fetch has been given up.
    while tip(&w, 1).height < 3 {
        w.run(SECOND / 50);
    }
    assert!(tip(&w, 1).height < 40);
    w.loss = 1000;
    let mut waited = 0;
    while w.nodes[1].counts().fetches_failed == 0 {
        w.run(SECOND);
        waited += 1;
        assert!(waited < 600, "no fetch was given up");
    }
    assert!(tip(&w, 1).height < 40);
    // And then everything does: far sooner than a peer is passed over
    // for, the node has the chain.
    w.loss = 0;
    let pass_over = w.nodes[1].cfg.sync.pass_over;
    w.run(pass_over / 4);
    assert_eq!(tip(&w, 1), tip(&w, 0));
}

/// A node whose chain is not the one with the most work, and which
/// cannot undo as far as where the two part, takes the state as of a
/// block of the other: how far a node can go back is its own affair,
/// and it is not left on a chain of its own for it.
#[test]
fn a_node_that_cannot_go_back_to_the_fork_takes_the_state() {
    let ahead = chain_of(easy());
    grow_wide(&ahead, 30, 20, 1);
    // (It can undo eight blocks, and has twenty the other has not.)
    let ours = Chain::open(MemBackend::new(), 8, easy(), seed(), AcceptAllProofs).unwrap();
    ours.set_dataset(table());
    let ours = Arc::new(ours);
    grow_wide(&ours, 20, 20, 2);
    let mut w = World::with(vec![ahead, ours], &joining());
    w.nodes[1].add_peer(at(0), false, 0);
    w.run(90 * SECOND);
    assert_eq!(tip(&w, 1), tip(&w, 0));
    assert_eq!(w.nodes[1].chain().state().root(), w.nodes[0].chain().state().root());
    let c = w.nodes[1].counts();
    assert_eq!((c.states, c.blocks_refused), (1, 1));
    assert!(w.nodes[1].list().join.is_none() && !w.nodes[1].chain().receiving() && !w.nodes[1].list().cut);
    // (The other chain left this one far under what it could undo: its
    // headers were weighed whole, none kept, before they were fetched
    // again and kept, having come to more work.)
    assert_eq!((c.weighed, c.headers), (1, 30));
}

/// A state being taken waits for nothing that may never come. Its
/// block and the top of its state arrive while the work of other
/// headers is being confirmed, so that its own cannot be yet; when
/// that is done with, the taking goes on at the next turn, though
/// nothing more arrives to set it going.
#[test]
#[cfg_attr(debug_assertions, ignore = "builds long chains; run with --release")]
fn a_state_being_taken_goes_on_when_what_it_waited_for_is_done() {
    let (ahead, _) = long_chain(50);
    let mut cfg = Config::default();
    (cfg.sync.sync_point, cfg.sync.sync_behind) = (10, 30);
    let mut w = World::with(vec![ahead, chain_of(easy())], &cfg);
    w.nodes[1].add_peer(at(0), false, 0);
    // (Something else is being confirmed, for as long as the test
    // says.)
    w.nodes[1].with_list(|_, l| l.confirming = true);
    let mut waited = 0;
    while !w.nodes[1].list().join.as_ref().is_some_and(|j| j.block.is_some() && j.manifest.is_some()) {
        w.run(SECOND / 10);
        waited += 1;
        assert!(waited < 600, "the state's block and its top never came");
    }
    // It has what it asked for, and can go no further.
    w.run(5 * SECOND);
    assert!(w.nodes[1].list().join.as_ref().is_some_and(|j| !j.worked && !j.begun));
    assert_eq!(w.nodes[1].counts().states, 0);
    // The other is done with: no outcome of it is of this state, and
    // nothing more is on its way. The taking goes on all the same.
    w.nodes[1].with_list(|_, l| l.confirming = false);
    w.run(90 * SECOND);
    assert_eq!(tip(&w, 1), tip(&w, 0));
    assert_eq!(w.nodes[1].counts().states, 1);
    assert!(w.nodes[1].list().join.is_none() && !w.nodes[1].chain().receiving());
}

/// A node far enough behind to take the state, whose only peer says it
/// has the state and hands none of it over, does not wait for it for
/// ever: after a few rounds of asking it lets the state be and takes
/// the blocks, which that peer does give.
#[test]
#[cfg_attr(debug_assertions, ignore = "builds long chains; run with --release")]
fn a_state_nobody_gives_is_let_be_for_the_blocks() {
    let (ahead, _) = long_chain(50);
    let mut cfg = Config::default();
    (cfg.sync.sync_point, cfg.sync.sync_behind) = (10, 30);
    let mut w = World::with(vec![ahead, chain_of(easy())], &cfg);
    w.nodes[0].withhold = true;
    w.nodes[1].add_peer(at(0), false, 0);
    // (Three rounds of asking, each after a longer wait: some minutes.)
    w.run(600 * SECOND);
    assert_eq!(tip(&w, 1), tip(&w, 0));
    let c = w.nodes[1].counts();
    assert_eq!((c.states, c.blocks, c.blocks_refused), (0, 50, 0));
    assert!(!w.nodes[1].chain().receiving());
}

/// A node with an old state, further behind than anyone's bodies reach,
/// gives it up for the state taken whole.
#[test]
#[cfg_attr(debug_assertions, ignore = "builds long chains; run with --release")]
fn a_node_long_away_takes_the_state() {
    let (ahead, blocks) = long_chain(KEEP + 16);
    let away = chain_of(easy());
    give(&away, &blocks[..5]);
    let mut w = World::with(vec![ahead, away], &joining());
    w.nodes[1].add_peer(at(0), false, 0);
    w.run(60 * SECOND);
    assert_eq!(tip(&w, 1), tip(&w, 0));
    assert_eq!(w.nodes[1].chain().state().root(), w.nodes[0].chain().state().root());
    let c = w.nodes[1].counts();
    assert_eq!((c.headers, c.states, c.blocks), (75, 1, 10));
}

/// A node only a little behind takes blocks, not the state; and one set
/// never to take a state waits for blocks nobody holds.
#[test]
#[cfg_attr(debug_assertions, ignore = "builds long chains; run with --release")]
fn the_state_is_taken_only_when_blocks_cannot_be_had() {
    let (ahead, blocks) = long_chain(KEEP + 16);
    let near = chain_of(easy());
    give(&near, &blocks[..KEEP + 6]);
    let mut never = joining();
    never.sync.sync_point = 0;
    let mut w = World::with(vec![ahead, near, chain_of(easy())], &joining());
    w.nodes[2].cfg = never;
    w.nodes[1].add_peer(at(0), false, 0);
    w.nodes[2].add_peer(at(0), false, 0);
    w.run(30 * SECOND);
    assert_eq!(tip(&w, 1), tip(&w, 0));
    assert_eq!((w.nodes[1].counts().states, w.nodes[1].counts().blocks), (0, 10));
    assert_eq!((tip(&w, 2).height, w.best(2).height, w.nodes[2].counts().states), (0, KEEP as u32 + 16, 0));
}

/// A header whose block nobody has sends no node back: nodes that are
/// at the block before it, and hear of it from a node that then goes
/// away, keep the state they have and wait. They do not take from each
/// other the state as of a block under their own last.
#[test]
fn a_header_whose_block_nobody_has_sends_no_node_back() {
    let first = chain_of(easy());
    let made = grow_wide(&first, 30, 20, 1);
    let second = chain_of(easy());
    give(&second, &made);
    // The header of a block after their last, which neither has.
    let other = chain_of(easy());
    give(&other, &made);
    let next = next_block(&other, 7, true);
    let header = *BlockRef::from_bytes(&next).unwrap().header();
    for chain in [&first, &second] {
        assert_eq!(chain.accept_header(&header, NOW), Ok(true));
    }
    let mut w = World::with(vec![first, second], &joining());
    w.nodes[0].add_peer(at(1), false, 0);
    w.nodes[1].add_peer(at(0), false, 0);
    w.run(60 * SECOND);
    for i in 0..2 {
        assert_eq!((tip(&w, i).height, w.best(i).height), (30, 31), "node {i}");
        let c = w.nodes[i].counts();
        assert_eq!((c.states, c.states_moved), (0, 0), "node {i}");
        assert!(w.nodes[i].list().join.is_none() && !w.nodes[i].chain().receiving(), "node {i}");
        // (The work of the header waited for was looked at once, in a
        // minute of waiting: not at every turn.)
        assert_eq!(c.confirms, 1, "node {i}");
    }
}

/// Nor does a branch whose blocks nobody has, that leaves the chain
/// under its last block: the state that would be taken is as of a block
/// of the chain's own, which it is past. Its only peer is behind it,
/// and holds none of what it lacks.
#[test]
fn a_branch_whose_blocks_nobody_has_sends_no_node_back() {
    let first = chain_of(easy());
    let made = grow_wide(&first, 30, 20, 1);
    let behind = chain_of(easy());
    give(&behind, &made[..20]);
    // Three blocks on the twenty-eighth, made where nobody sees them:
    // their headers are known, and more work than the chain's.
    let other = chain_of(easy());
    give(&other, &made[..28]);
    let branch = grow(&other, 3, 9);
    let headers: Vec<Header> = branch.iter().map(|b| *BlockRef::from_bytes(b).unwrap().header()).collect();
    assert_eq!(first.accept_headers(&headers, NOW, false), (3, None));
    let mut w = World::with(vec![first, behind], &joining());
    w.nodes[0].add_peer(at(1), false, 0);
    w.nodes[1].add_peer(at(0), false, 0);
    w.run(60 * SECOND);
    assert_eq!((tip(&w, 0).height, w.best(0).height), (30, 31));
    let c = w.nodes[0].counts();
    assert_eq!((c.states, c.states_moved), (0, 0));
    assert!(w.nodes[0].list().join.is_none() && !w.nodes[0].chain().receiving());
    // (And blocks are still made on it: it is behind by blocks that may
    // never come, not by a state.)
    assert_ne!(w.nodes[0].hold().behind(), Behind::State);
    // The one behind it has its blocks from it meanwhile.
    assert_eq!(tip(&w, 1).height, 30);
}

/// A peer asked for the headers of a chain another spoke of, which it
/// has not, says so and is asked no more for them: it is not passed
/// over for that. Only whoever spoke of a chain answers for it.
#[test]
fn a_peer_asked_for_another_s_chain_is_not_passed_over() {
    let chains: Vec<_> = (0..3).map(|_| chain_of(easy())).collect();
    grow(&chains[0], 12, 1);
    grow(&chains[1], 12, 2);
    let theirs = chains[1].tip().unwrap();
    let mut w = World::with(chains, &small_runs());
    // Node 1 says its chain is the most work there is: it is the one
    // asked where the chains part, and the one aimed at. Node 0's is as
    // long, and another.
    w.nodes[1].boast = Some(U256::MAX);
    w.nodes[2].add_peer(at(0), false, 0);
    w.nodes[2].add_peer(at(1), false, 0);
    w.nodes[2].cfg.sync.blocks = 0;
    w.run(20 * SECOND);
    let now = w.now;
    assert_eq!(w.best(2), theirs);
    assert!(w.nodes[2].table(&at(0)).may_ask(&at(0), now), "the peer on another branch is passed over");
}

/// The work of headers is left to a proof only far above the chain's
/// last block: those near it are checked as they come.
#[test]
fn work_is_left_to_a_proof_only_far_above_the_chain() {
    // A node that takes no state, or whose proofs vouch for no work:
    // of none.
    assert_eq!((super::defers(0, true, Some(0)), super::defers(144, false, Some(0))), (None, None));
    // Else of those more than the sync point above the chain's last
    // block: for a new node, all but the first of them.
    assert_eq!((super::defers(144, true, Some(250)), super::defers(144, true, Some(0))), (Some(394), Some(144)));
    // While a state is being received there is no last block.
    assert_eq!(super::defers(144, true, None), Some(0));
}

/// Blocks announced from nowhere, as fast as a peer can send them, are
/// nothing given to the chain to check: each is known for what it is by
/// the worker that hears of it. And headers that are on the chain but
/// are nobody's work have their sender refused.
#[test]
fn announcements_from_nowhere_cost_the_chain_nothing() {
    let chains = vec![chain_of(easy()), chain_of(easy())];
    let made = grow(&chains[0], 3, 1);
    give(&chains[1], &made);
    let tip = chains[0].tip().unwrap();
    let mut w = World::with(chains, &small_runs());
    w.nodes[0].add_peer(at(1), false, 0);
    w.nodes[1].add_peer(at(0), false, 0);
    w.run(2 * SECOND);
    // Five hundred blocks whose parents nobody has heard of.
    for k in 0..500u32 {
        let mut prev = [0x55u8; 32];
        prev[..4].copy_from_slice(&k.to_le_bytes());
        let header = Header { prev_hash: prev, height: 900, nonce: [k as u8; 32], ..tip };
        w.inject(at(1), 0, &Message::Block { header, len: 1000 });
    }
    w.run(2 * SECOND);
    let c = w.nodes[0].counts();
    assert_eq!((c.checked, c.headers, tip.height), (0, 0, w.best(0).height));
    assert!(c.forks_asked <= 3, "asked where the chains part {} times", c.forks_asked);
    let now = w.now;
    assert!(w.nodes[0].table(&at(1)).get(&at(1)).is_some(), "an orphan is nobody's fault");
    // Blocks on the chain's last, whose work nobody did: each is
    // checked, and found out; after a few their sender is refused, and
    // the rest are not heard.
    for k in 0..200u32 {
        let header = Header { prev_hash: tip.hash(), height: tip.height + 1, nonce: [k as u8; 32], ..tip };
        w.inject(at(1), 0, &Message::Block { header, len: 1000 });
    }
    w.run(2 * SECOND);
    let c = w.nodes[0].counts();
    assert!((1..=16).contains(&c.checked), "{} checked", c.checked);
    assert_eq!(w.nodes[0].table(&at(1)).refusal(&at(1), false, now), Some(crate::net::peers::Refused::Banned));
    assert_eq!(w.best(0), tip);
}

/// A node catching up tells nobody of the blocks it takes: each of its
/// peers that is as high has had them all along. (It once told every
/// peer of every old block as it joined it to its chain.) A block that
/// is news to a peer is told to it as before.
#[test]
fn a_node_catching_up_announces_nothing_old() {
    let chains = vec![chain_of(easy()), chain_of(easy()), chain_of(easy())];
    let made = grow(&chains[1], 20, 1);
    give(&chains[2], &made);
    let mut w = World::with(chains.clone(), &small_runs());
    w.nodes[0].add_peer(at(1), false, 0);
    w.nodes[0].add_peer(at(2), false, 0);
    w.run(20 * SECOND);
    assert_eq!(tip(&w, 0), tip(&w, 1));
    assert_eq!(w.nodes[0].counts().announced, 0);
    // One more, made by the second: told to both the others, and by
    // whichever of those has it first to nobody that has it.
    let more = grow(&chains[1], 1, 2);
    let block = crate::block::BlockRef::from_bytes(&more[0]).unwrap();
    let (header, len) = (*block.header(), (more[0].len() - crate::block::HEADER_SIZE) as u32);
    w.inject(at(1), 0, &Message::Block { header, len });
    w.inject(at(1), 2, &Message::Block { header, len });
    w.run(20 * SECOND);
    assert_eq!((tip(&w, 0), tip(&w, 2)), (tip(&w, 1), tip(&w, 1)));
    assert!(w.nodes[0].counts().announced <= 1 && w.nodes[2].counts().announced <= 1);
}

/// A node is known by a number it says in every ping, whatever address
/// it is heard from. One that is a live peer already, heard of at a
/// second address (its router's, which another node told of), is not
/// a second peer; and a node that hears its own number has reached
/// itself. Neither address is asked again.
#[test]
fn a_node_heard_from_two_addresses_is_one_peer() {
    use crate::net::peers::Refused;
    let mut w = World::new(2, &Config::default());
    w.nodes[0].add_peer(at(1), false, 0);
    w.run(2 * SECOND);
    assert_eq!((w.live(0), w.live(1)), (vec![at(1)], vec![at(0)]));
    let genesis = w.nodes[0].chain().params().genesis().header.hash();
    let numbers = [w.nodes[0].hold().node_number(), w.nodes[1].hold().node_number()];
    assert_ne!(numbers[0], numbers[1]);
    // The pong to this node's ping of an address nobody is at, as the
    // node of that number would give it.
    let pong_from = |w: &mut World, alias: SocketAddrV4, node: u64| {
        w.strays.clear();
        w.nodes[0].add_peer(alias, false, w.now);
        w.woken();
        w.run(2 * SECOND);
        let ping = w.strays.iter().find_map(|(_, to, bytes)| match Message::decode(NET, bytes) {
            Ok(Message::Ping(status)) if *to == alias => Some(status),
            _ => None,
        });
        let nonce = ping.expect("the address is pinged").nonce;
        w.inject(alias, 0, &Message::Pong(Status { node, ..claim(nonce, genesis) }));
        w.run(SECOND);
    };
    // The peer it has, at another address: no second peer.
    pong_from(&mut w, at(7), numbers[1]);
    let now = w.now;
    assert_eq!(w.live(0), [at(1)]);
    assert_eq!(w.nodes[0].table(&at(7)).refusal(&at(7), false, now), Some(Refused::Itself));
    // Itself, at an address it did not know for its own.
    pong_from(&mut w, at(8), numbers[0]);
    assert_eq!(w.live(0), [at(1)]);
    assert_eq!(w.nodes[0].table(&at(8)).refusal(&at(8), false, now), Some(Refused::Itself));
    // Another node at another address is another peer.
    pong_from(&mut w, at(9), 12345);
    assert_eq!(w.live(0), [at(1), at(9)]);
    // And the first is the peer it was all along.
    w.run(40 * SECOND);
    assert!(w.live(0).contains(&at(1)) && w.live(1) == [at(0)]);
}

/// A peer that says its chain is higher than any could be by now is
/// not gone after: the runs of headers to ask for are counted from
/// what it says.
#[test]
fn a_chain_higher_than_any_could_be_is_not_gone_after() {
    let chains = vec![chain_of(easy()), chain_of(easy())];
    grow(&chains[1], 3, 1);
    let mut w = World::with(chains, &small_runs());
    w.nodes[1].boast = Some(U256::MAX);
    w.nodes[1].tall = Some(u32::MAX - 7);
    w.nodes[0].add_peer(at(1), false, 0);
    w.run(5 * SECOND);
    let now = w.now;
    assert!(w.nodes[0].list().aim.is_none());
    assert_eq!((w.best(0).height, w.nodes[0].counts().forks_asked), (0, 1));
    assert!(!w.nodes[0].table(&at(1)).may_ask(&at(1), now));
}

/// A node with nothing to do does next to nothing: with a chain, peers
/// that say nothing new and a minute gone by, it has read its store a
/// handful of times (what it says of itself in a ping), not at every
/// turn. (It once counted the votes for the consensus file afresh at
/// every turn of every worker, from the leaves of two windows of
/// blocks: seventeen thousand reads a second, of a node standing by.)
#[test]
fn a_node_with_nothing_to_do_reads_nothing() {
    let chains: Vec<_> = (0..2).map(|_| chain_of(easy())).collect();
    let made = grow(&chains[0], 20, 1);
    give(&chains[1], &made);
    let mut w = World::with(chains, &small_runs());
    w.nodes[0].add_peer(at(1), false, 0);
    w.nodes[1].add_peer(at(0), false, 0);
    // (Time for each to find the other and see there is nothing to
    // have of it.)
    w.run(30 * SECOND);
    let before: Vec<u64> = (0..2).map(|i| w.nodes[i].chain().store_reads()).collect();
    w.run(60 * SECOND);
    let after: Vec<u64> = (0..2).map(|i| w.nodes[i].chain().store_reads()).collect();
    for i in 0..2 {
        assert!(after[i] - before[i] <= 6, "node {i}: {} reads in a minute", after[i] - before[i]);
    }
}

/// A peer sends most of a block and then no more of it, while it goes
/// on answering everything else (as a peer did whose answers a fetch
/// did not take: the blocks behind that one waited on it for most of
/// a minute, whole, while two peers that had it stood by). After a few
/// seconds of nothing new the rest is asked of another peer that has
/// the block; what had come is kept; and the peer that stopped is not
/// held to have done wrong.
#[test]
fn a_block_that_stops_coming_is_gone_on_with_by_another_peer() {
    let chains: Vec<_> = (0..3).map(|_| chain_of(easy())).collect();
    let made = grow_wide(&chains[0], 6, 300, 1);
    give(&chains[1], &made);
    let mut cfg = small_runs();
    // (One block of a peer at a time: both are asked.)
    cfg.sync.blocks_per_peer = 1;
    let mut w = World::with(chains, &cfg);
    w.stops = Some((0, 10));
    w.nodes[2].add_peer(at(0), false, 0);
    w.nodes[2].add_peer(at(1), false, 0);
    w.run(20 * SECOND);
    let c = w.nodes[2].counts();
    assert_eq!(tip(&w, 2), tip(&w, 1), "{c:?}");
    assert!(c.fetches_moved >= 1 && c.fetches_slow == 0, "{c:?}");
    let now = w.now;
    assert!(w.nodes[2].table(&at(0)).may_ask(&at(0), now) && w.nodes[2].table(&at(1)).may_ask(&at(1), now));
}

/// A peer that sends what it was asked for a little at a time is given
/// up, and the rest is had from another: one such is not all a node
/// hears from for as long as it cares to go on.
#[test]
fn a_peer_that_sends_a_little_at_a_time_is_given_up() {
    let chains: Vec<_> = (0..3).map(|_| chain_of(easy())).collect();
    let made = grow_wide(&chains[0], 12, 300, 1);
    give(&chains[1], &made);
    let mut cfg = small_runs();
    // (One block of a peer at a time: both are asked.)
    cfg.sync.blocks_per_peer = 1;
    let mut w = World::with(chains, &cfg);
    w.slow = vec![0];
    w.nodes[2].add_peer(at(0), false, 0);
    w.nodes[2].add_peer(at(1), false, 0);
    w.run(150 * SECOND);
    let c = w.nodes[2].counts();
    assert_eq!(tip(&w, 2), tip(&w, 1), "{c:?}");
    // (Given up as too slow; or, sooner, for bringing nothing new for
    // seconds at a time, its blocks gone on with by the other.)
    assert!(c.fetches_slow + c.fetches_moved >= 1, "{c:?}");
    let now = w.now;
    assert!(w.nodes[2].table(&at(1)).may_ask(&at(1), now));
}

/// A peer that serves pieces of the state that are not the state is
/// struck for each, and the pieces come from another.
#[test]
#[cfg_attr(debug_assertions, ignore = "builds long chains; run with --release")]
fn wrong_pieces_of_a_state_are_refused() {
    let (ahead, blocks) = long_chain(KEEP + 16);
    let liar = chain_of(easy());
    give(&liar, &blocks);
    let mut w = World::with(vec![ahead, liar, chain_of(easy())], &joining());
    w.nodes[2].add_peer(at(0), false, 0);
    w.nodes[2].add_peer(at(1), false, 0);
    // Headers first, from either; then one of the two begins to spoil
    // everything it serves.
    w.nodes[2].cfg.sync.sync_point = 0;
    w.run(8 * SECOND);
    assert_eq!(w.best(2).height, KEEP as u32 + 16);
    w.nodes[1].spoil = true;
    w.nodes[2].cfg.sync.sync_point = 10;
    w.run(90 * SECOND);
    assert_eq!(tip(&w, 2), tip(&w, 0));
    assert_eq!(w.nodes[2].chain().state().root(), w.nodes[0].chain().state().root());
    assert_eq!(w.nodes[2].counts().states, 1);
    // The liar is out, or passed over; the honest one is neither.
    let now = w.now;
    assert!(!w.nodes[2].table(&at(1)).may_ask(&at(1), now) && w.nodes[2].table(&at(0)).may_ask(&at(0), now));
}

/// The peers go on past the block a state is being taken as of, until
/// none can go back to it: the state is taken as of a later block, and
/// the node ends where they are.
#[test]
#[cfg_attr(debug_assertions, ignore = "builds long chains; run with --release")]
fn a_state_is_gone_on_with_as_of_a_later_block() {
    let (ahead, _) = long_chain(KEEP + 16);
    let mut w = World::with(vec![ahead, chain_of(easy())], &joining());
    w.nodes[1].add_peer(at(0), false, 0);
    // Until it has begun to receive, and then nothing of the state
    // reaches it for a while.
    for _ in 0..400 {
        w.run(50 * MILLI);
        if w.nodes[1].chain().receiving() {
            break;
        }
    }
    assert_eq!(w.nodes[1].chain().receiving_as_of().map(|t| t.0), Some(70));
    w.mute = vec![0];
    // The other makes blocks meanwhile, until it can no longer go back
    // to block seventy.
    grow(w.nodes[0].chain(), 60, 2);
    assert!(w.nodes[0].make(&Object::Manifest(w.nodes[0].chain().header_at(70).unwrap().unwrap().hash())).is_none());
    w.mute.clear();
    w.run(120 * SECOND);
    assert_eq!(tip(&w, 1), tip(&w, 0));
    assert_eq!(w.nodes[1].chain().state().root(), w.nodes[0].chain().state().root());
    let c = w.nodes[1].counts();
    assert_eq!((c.states, c.states_moved), (1, 1));
    // The headers of the blocks made meanwhile were taken while the
    // state was being received.
    assert_eq!(c.headers, 140);
}

/// Each piece of a state is held to the piece above it as it arrives:
/// one that is not what it should be is not kept, and its sender is
/// not asked again while another can be.
#[test]
#[cfg_attr(debug_assertions, ignore = "builds long chains; run with --release")]
fn each_piece_of_a_state_is_checked_as_it_arrives() {
    let (ahead, _) = long_chain(KEEP + 16);
    let mut w = World::with(vec![ahead, chain_of(easy())], &joining());
    w.nodes[1].add_peer(at(0), false, 0);
    // Headers, and the block to take the state as of chosen; nothing of
    // the state fetched yet.
    w.nodes[1].cfg.sync.parts = 0;
    w.run(10 * SECOND);
    let now = w.now;
    let (id, target) = {
        let list = w.nodes[1].list();
        let join = list.join.as_ref().unwrap();
        (join.id, join.target)
    };
    assert_eq!(target.height, 70);
    let (liar, honest) = (at(7), at(0));
    let made = |w: &mut World, object: Object| w.nodes[0].make(&object).unwrap();
    let unserved = |w: &World| w.nodes[1].list().join.as_ref().unwrap().unserved.clone();
    // A manifest of another block's state, well formed: not this one's.
    let other = w.nodes[0].chain().header_at(71).unwrap().unwrap().hash();
    let wrong = made(&mut w, Object::Manifest(other));
    w.nodes[1].with_list(|n, l| n.piece_arrived(l, now, Object::Manifest(id), liar, &wrong));
    w.nodes[1].with_list(|n, l| n.applied(l, now, &mut |_, _| {}));
    assert!(w.nodes[1].list().join.as_ref().unwrap().manifest.is_none());
    assert_eq!(unserved(&w), [liar]);
    // The block with another's body.
    let body = w.nodes[0].chain().body(&other).unwrap().unwrap();
    w.nodes[1].with_list(|n, l| n.piece_arrived(l, now, Object::Block(id), liar, &body));
    w.nodes[1].with_list(|n, l| n.applied(l, now, &mut |_, _| {}));
    assert!(w.nodes[1].list().join.as_ref().unwrap().block.is_none());
    // The true ones: the block's proof is checked, and the roots are
    // what is wanted next.
    let (manifest, body) = (made(&mut w, Object::Manifest(id)), w.nodes[0].chain().body(&id).unwrap().unwrap());
    w.nodes[1].with_list(|n, l| n.piece_arrived(l, now, Object::Manifest(id), honest, &manifest));
    w.nodes[1].with_list(|n, l| n.applied(l, now, &mut |_, _| {}));
    w.nodes[1].with_list(|n, l| n.piece_arrived(l, now, Object::Block(id), honest, &body));
    w.nodes[1].with_list(|n, l| n.applied(l, now, &mut |_, _| {}));
    assert!(w.nodes[1].list().join.as_ref().unwrap().checked && !w.nodes[1].chain().receiving());
    // Roots of another block's range: not this manifest's.
    let wrong = made(&mut w, Object::Roots { block: other, index: 0 });
    w.nodes[1].with_list(|n, l| n.piece_arrived(l, now, Object::Roots { block: id, index: 0 }, liar, &wrong));
    w.nodes[1].with_list(|n, l| n.applied(l, now, &mut |_, _| {}));
    assert!(w.nodes[1].list().join.as_ref().unwrap().roots.is_empty());
    assert_eq!(unserved(&w).len(), 3);
    let roots = made(&mut w, Object::Roots { block: id, index: 0 });
    w.nodes[1].with_list(|n, l| n.piece_arrived(l, now, Object::Roots { block: id, index: 0 }, honest, &roots));
    w.nodes[1].with_list(|n, l| n.applied(l, now, &mut |_, _| {}));
    assert!(w.nodes[1].chain().receiving());
    let (missing, _) = w.nodes[1].chain().missing_parts().unwrap();
    assert_eq!(missing, [0, 1, 2]);
    // A part of another block's state; a part with a byte changed; a
    // part that is no part at all.
    let wrong = made(&mut w, Object::Part { block: other, index: 2 });
    w.nodes[1].with_list(|n, l| n.piece_arrived(l, now, Object::Part { block: id, index: 2 }, liar, &wrong));
    w.nodes[1].with_list(|n, l| n.applied(l, now, &mut |_, _| {}));
    let mut part = made(&mut w, Object::Part { block: id, index: 1 });
    part[100] ^= 1;
    w.nodes[1].with_list(|n, l| n.piece_arrived(l, now, Object::Part { block: id, index: 1 }, liar, &part));
    w.nodes[1].with_list(|n, l| n.applied(l, now, &mut |_, _| {}));
    w.nodes[1].with_list(|n, l| n.piece_arrived(l, now, Object::Part { block: id, index: 0 }, liar, b"nothing"));
    w.nodes[1].with_list(|n, l| n.applied(l, now, &mut |_, _| {}));
    assert_eq!(w.nodes[1].chain().missing_parts().unwrap().0, [0, 1, 2]);
    assert_eq!(unserved(&w).len(), 6);
    assert!(unserved(&w).iter().all(|a| *a == liar));
    // The true parts: the state is whole, at the block.
    for index in [0u64, 1, 2] {
        let part = made(&mut w, Object::Part { block: id, index });
        w.nodes[1].with_list(|n, l| n.piece_arrived(l, now, Object::Part { block: id, index }, honest, &part));
        w.nodes[1].with_list(|n, l| n.applied(l, now, &mut |_, _| {}));
    }
    assert!(w.nodes[1].list().join.is_none() && !w.nodes[1].chain().receiving());
    assert_eq!((tip(&w, 1), w.nodes[1].chain().state().root()), (target, target.state_root));
    assert_eq!(w.nodes[1].counts().states, 1);
}

/// A node that stops while it is taking a state and starts again goes
/// on from what it had: as of the same block, asking again for nothing
/// it had received.
#[test]
#[cfg_attr(debug_assertions, ignore = "builds long chains; run with --release")]
fn a_node_restarted_while_taking_a_state_goes_on() {
    let (ahead, _) = long_chain(KEEP + 16);
    let mut w = World::with(vec![ahead, chain_of(easy())], &joining());
    w.nodes[1].add_peer(at(0), false, 0);
    // Until one of the state's three parts is in, and the others are
    // on their way.
    w.nodes[1].cfg.sync.parts = 1;
    for _ in 0..2000 {
        w.run(5 * MILLI);
        if w.nodes[1].chain().missing_parts().is_ok_and(|m| m.0.len() == 2) {
            break;
        }
    }
    assert_eq!(w.nodes[1].chain().missing_parts().unwrap().0.len(), 2);
    let had = w.nodes[1].chain().receiving_as_of();
    // It stops: what was on its way is lost, and what it knew of its
    // peers. It starts again on what its store holds.
    let image = w.nodes[1].chain().image();
    let chain = Chain::open(MemBackend::from_image(image), KEEP, easy(), seed(), AcceptAllProofs).unwrap();
    chain.set_dataset(table());
    assert!(chain.receiving());
    let now = w.now;
    w.flying.clear();
    w.nodes[1] = Node::new(joining(), NET, Arc::new(chain), [9; 32], now);
    w.nodes[1].add_peer(at(0), false, now);
    w.wake[1] = now;
    w.run(60 * SECOND);
    assert_eq!(tip(&w, 1), tip(&w, 0));
    assert_eq!(w.nodes[1].chain().state().root(), w.nodes[0].chain().state().root());
    let c = w.nodes[1].counts();
    // The same block; the block, the manifest and the roots again (they
    // are not kept), the two parts it lacked, and the ten blocks after:
    // not the part it had.
    assert_eq!((c.states, c.states_moved, c.blocks), (1, 0, 10));
    assert_eq!(had.map(|t| t.0), Some(70));
    assert_eq!(c.fetched, 1 + 1 + 1 + 2 + 10, "{c:?}");
}

/// Over this machine's own sockets and clock, with the work on the
/// chain done on a thread of its own: a new node takes the state from
/// one ahead, and the blocks after it.
#[test]
#[cfg_attr(debug_assertions, ignore = "builds long chains; run with --release")]
fn over_real_sockets_a_state_is_taken() {
    sockets_state(1);
    sockets_state(4);
}

fn sockets_state(workers: usize) {
    use std::net::UdpSocket;
    use std::sync::atomic::{AtomicBool, Ordering};
    use std::time::{Duration, Instant};
    let mut cfg = joining();
    cfg.tick = 50 * MILLI;
    cfg.workers = workers;
    let (ahead, _) = long_chain(KEEP + 16);
    let chains = vec![ahead, chain_of(easy())];
    let (target, root) = (chains[0].tip().unwrap(), chains[0].state().root());
    let sockets: Vec<UdpSocket> = (0..2).map(|_| UdpSocket::bind("127.0.0.1:0").unwrap()).collect();
    let SocketAddr::V4(first) = sockets[0].local_addr().unwrap() else { unreachable!() };
    let stop = Arc::new(AtomicBool::new(false));
    let behind = Arc::clone(&chains[1]);
    let threads: Vec<_> = sockets
        .into_iter()
        .zip(chains)
        .enumerate()
        .map(|(i, (socket, chain))| {
            let (cfg, stop) = (cfg.clone(), Arc::clone(&stop));
            std::thread::spawn(move || {
                let mut node = Node::new(cfg, NET, chain, [i as u8 + 1; 32], 0).threaded().by_port();
                if i == 1 {
                    node.add_peer(first, true, 0);
                }
                crate::net::socket::run_until(&mut node, &socket, &stop, Instant::now(), &|| NOW).unwrap();
                node.counts()
            })
        })
        .collect();
    let start = Instant::now();
    while behind.receiving() || behind.tip().unwrap() != target {
        assert!(start.elapsed() < SOCKETS_WITHIN, "receiving: {}", behind.receiving());
        std::thread::sleep(Duration::from_millis(20));
    }
    std::thread::sleep(Duration::from_millis(300));
    stop.store(true, Ordering::Relaxed);
    let counts: Vec<Counts> = threads.into_iter().map(|t| t.join().unwrap()).collect();
    assert_eq!(behind.state().root(), root);
    assert_eq!((counts[1].headers, counts[1].states, counts[1].blocks, counts[1].blocks_refused), (80, 1, 10, 0));
}

/// What happens to a node is said, in order, to whoever keeps its
/// log: a peer found, its headers wanted and kept, each block as it
/// joins the chain, and that the chain has been caught up with.
#[test]
fn a_node_says_what_happens_to_it() {
    use crate::net::node::Event;
    let chains = vec![chain_of(easy()), chain_of(easy())];
    let blocks = grow(&chains[0], 12, 1);
    let mut w = World::with(chains, &small_runs());
    let said = Arc::new(std::sync::Mutex::new(Vec::new()));
    let heard = Arc::clone(&said);
    w.nodes[1].hold().on_event(Box::new(move |event| heard.lock().unwrap().push(event.clone())));
    w.nodes[1].add_peer(at(0), false, 0);
    w.run(20 * SECOND);
    let mut wanted = vec![
        Event::PeerConnected { peer: at(0), height: 12 },
        Event::HeadersWanted { from: 1, to: 12, peer: at(0) },
        Event::HeadersKept { height: 12 },
    ];
    for block in &blocks {
        let header = *BlockRef::from_bytes(block).unwrap().header();
        let len = (block.len() - crate::block::HEADER_SIZE) as u32;
        wanted.push(Event::Block { header, len, from: Some(at(0)), undone: 0, taken: 1 });
    }
    wanted.push(Event::Synced { height: 12 });
    assert_eq!(*said.lock().unwrap(), wanted);
    // A block of its own is said as made here; and when its peer says
    // goodbye, that it is lost.
    said.lock().unwrap().clear();
    let mine = next_block(w.nodes[1].chain(), 7, true);
    let header = *BlockRef::from_bytes(&mine).unwrap().header();
    let len = (mine.len() - crate::block::HEADER_SIZE) as u32;
    w.nodes[1].mined(mine);
    w.run(SECOND);
    assert_eq!(*said.lock().unwrap(), [Event::Block { header, len, from: None, undone: 0, taken: 1 }]);
    let now = w.now;
    let mut sent = Vec::new();
    w.nodes[0].goodbye(now, &mut |to, bytes: &[u8]| sent.push((to, bytes.to_vec())));
    sent.iter().for_each(|(to, bytes)| w.post(at(0), *to, bytes));
    w.run(2 * SECOND);
    // (It is still there, in fact, and is soon found again.)
    assert!(said.lock().unwrap().contains(&Event::PeerLost { peer: at(0) }));
}

/// A block of no more work than the chain's is kept on a side branch,
/// and said to be: the chain is as it was. One made here that comes to
/// that is heard of all the same, so that whoever made it does not
/// wait for the chain to move. And a node with one block of a rival
/// branch to come is not behind: it goes on making its own.
#[test]
fn a_block_on_a_side_branch_is_said_and_holds_nobody_up() {
    use crate::net::node::{Behind, Event};
    let chains = vec![chain_of(easy()), chain_of(easy())];
    // Two blocks at the first height: the node has one, and makes the other.
    let rival = next_block(&chains[1], 1, true);
    let ours = next_block(&chains[0], 2, true);
    give(&chains[0], std::slice::from_ref(&rival));
    let mut w = World::with(chains, &small_runs());
    let said = Arc::new(std::sync::Mutex::new(Vec::new()));
    let heard = Arc::clone(&said);
    let hold = w.nodes[0].hold();
    hold.on_event(Box::new(move |event| heard.lock().unwrap().push(event.clone())));
    assert_eq!((hold.moves(), hold.settled(), hold.behind()), (0, 0, Behind::No));
    hold.mined(ours.clone(), NOW);
    w.run(SECOND);
    let header = *BlockRef::from_bytes(&ours).unwrap().header();
    assert_eq!(*said.lock().unwrap(), [Event::Side { header, from: None }]);
    // Heard of, though the chain did not move.
    assert_eq!((hold.moves(), hold.settled()), (0, 1));
    assert_eq!(tip(&w, 0), *BlockRef::from_bytes(&rival).unwrap().header());
    // The other node, at the first block still, is told of a block at
    // the first height by a peer: one block to come is not being behind.
    let far = w.nodes[1].hold();
    assert_eq!(far.behind(), Behind::No);
    w.nodes[1].chain().accept_header(&header, NOW).unwrap();
    assert_eq!(far.behind(), Behind::No);
}

/// A node that learns nothing from asking whom its peer knows asks
/// less and less often, down to as seldom as it pings.
#[test]
fn asking_whom_a_peer_knows_backs_off_while_nothing_comes_of_it() {
    let mut w = World::new(2, &Config::default());
    w.nodes[1].add_peer(at(0), true, 0);
    // The nodes know only each other: every answer is of nobody new.
    let asked = |w: &World, from: Micros, to: Micros| {
        w.log.iter().filter(|(at, kind)| *kind == "get-peers" && (from..to).contains(at)).count()
    };
    w.run(240 * SECOND);
    // Each of the two asks: at 1, 2, 4, 8, 16 seconds apart, then 30.
    let (early, late) = (asked(&w, 0, 30 * SECOND), asked(&w, 120 * SECOND, 240 * SECOND));
    assert!((8..=14).contains(&early), "{early}");
    assert!((6..=10).contains(&late), "{late}");
}

/// A node is behind, for whoever makes blocks, only by what it has
/// checked: a peer's word that its chain has more work stops nobody,
/// and nor does asking for its headers. Headers kept that show a chain
/// two blocks ahead do, until its blocks are here.
#[test]
fn a_node_is_behind_only_by_headers_it_has_checked() {
    use crate::net::node::Behind;
    let chains = vec![chain_of(easy()), chain_of(easy())];
    let blocks = grow(&chains[0], 5, 1);
    let mut w = World::with(chains, &small_runs());
    let hold = w.nodes[1].hold();
    // A peer that claims the most work there can be, and sends nothing
    // for it: asked where its chain leaves ours, and its headers asked
    // for; and all the while the node is behind nothing.
    w.nodes[0].boast = Some(U256::MAX);
    w.mute.push(0);
    w.nodes[1].add_peer(at(0), false, 0);
    let mut asked = false;
    for _ in 0..40 {
        w.run(500 * MILLI);
        asked |= w.nodes[1].counts().forks_asked > 0;
        assert_eq!(hold.behind(), Behind::No);
    }
    assert!(asked);
    // Its headers, checked and kept: five blocks ahead, none here yet.
    let headers: Vec<Header> = blocks.iter().map(|b| *BlockRef::from_bytes(b).unwrap().header()).collect();
    let (kept, refused) = w.nodes[1].chain().accept_headers(&headers, NOW, false);
    assert!(kept == 5 && refused.is_none());
    assert_eq!(hold.behind(), Behind::Blocks { best: headers[4].hash(), height: 5 });
    // Its blocks come in: with one to go the node is behind no longer.
    give(w.nodes[1].chain(), &blocks[..3]);
    assert_eq!(hold.behind(), Behind::Blocks { best: headers[4].hash(), height: 5 });
    give(w.nodes[1].chain(), &blocks[3..4]);
    assert_eq!(hold.behind(), Behind::No);
}

// -- Several workers

/// What nodes of one worker do, nodes of several do: each worker with
/// the hosts that are its own, and what is about all of them shared.
#[test]
fn several_workers_find_peers() {
    several(nodes_that_know_one_seed_find_each_other);
    several(a_node_that_says_goodbye_is_known_at_once_to_be_gone);
}

#[test]
fn several_workers_take_headers() {
    several(a_node_behind_takes_the_headers_of_one_ahead);
    several(headers_are_taken_from_where_two_chains_part);
    several(runs_of_headers_come_from_several_peers);
    several(a_false_claim_of_work_does_not_hold_a_node_up);
    several(a_peer_that_serves_wrong_headers_is_struck);
}

#[test]
fn several_workers_take_blocks() {
    several(a_node_behind_takes_the_blocks_of_one_ahead);
    several(a_new_block_crosses_the_network);
    several(a_node_goes_over_to_the_branch_with_more_work);
    several(an_announcement_from_far_ahead_is_followed_at_once);
    several(a_wrong_body_is_refused_and_fetched_elsewhere);
    several(a_block_that_breaks_a_rule_is_refused_once);
    several(bodies_are_asked_only_of_those_that_hold_them);
}

#[test]
#[cfg_attr(debug_assertions, ignore = "builds long chains; run with --release")]
fn several_workers_take_a_state() {
    several(a_new_node_takes_the_state_and_goes_on_from_it);
    several(a_node_long_away_takes_the_state);
    several(the_state_is_taken_only_when_blocks_cannot_be_had);
    several(wrong_pieces_of_a_state_are_refused);
    several(a_state_is_gone_on_with_as_of_a_later_block);
}

/// A host is one worker's, whatever the port; hosts are spread over
/// the workers; and the limits that are of the whole node (peers in
/// all, peers of one network) hold over all of them.
#[test]
fn a_host_is_one_workers_and_the_nodes_limits_hold_over_all() {
    let mut cfg = Config { workers: 4, ..Config::default() };
    cfg.peers.max = 40;
    let mut node: TestNode = Node::new(cfg, NET, chain_of(easy()), [7; 32], 0);
    let sizes = |node: &TestNode| node.tables().map(|t| t.len()).collect::<Vec<usize>>();
    // Four ports of one host: all in one table, and a fifth refused
    // there (four to a host).
    let port = |p: u16| SocketAddrV4::new(Ipv4Addr::new(30, 1, 2, 3), p);
    assert!((1..=4).all(|p| node.add_peer(port(p), false, 0)) && !node.add_peer(port(5), false, 0));
    assert_eq!(sizes(&node).iter().filter(|n| **n > 0).count(), 1);
    assert_eq!(node.table(&port(1)).len(), 4);
    // Hosts of twenty networks: on every worker.
    let host = |k: u8| SocketAddrV4::new(Ipv4Addr::new(40, k, 0, 1), 3737);
    assert!((0..20).all(|k| node.add_peer(host(k), false, 0)));
    assert!(sizes(&node).iter().all(|n| *n > 0), "{:?}", sizes(&node));
    // Twenty hosts of one network, on several workers: eight are taken.
    let near = |k: u8| SocketAddrV4::new(Ipv4Addr::new(50, 7, k, 1), 3737);
    let taken: Vec<u8> = (0..20).filter(|k| node.add_peer(near(*k), false, 0)).collect();
    assert_eq!(taken.len(), 8);
    let mut of: Vec<usize> = taken.iter().map(|k| node.shared.owner(&near(*k))).collect();
    of.dedup();
    assert!(of.len() > 1, "{of:?}");
    // Thirty-two in all; and never more than forty, however many more
    // are told of (none of those there has been tried yet, so none
    // gives way: eight more are taken, and no more).
    assert_eq!(sizes(&node).iter().sum::<usize>(), 32);
    let far = |k: u8| SocketAddrV4::new(Ipv4Addr::new(60, k, 0, 1), 3737);
    assert_eq!((0..100).filter(|k| node.add_peer(far(*k), false, 0)).count(), 8);
    assert_eq!((sizes(&node).iter().sum::<usize>(), node.peer_counts(0)), (40, (40, 0)));
}

/// Several nodes ahead and one behind, over real sockets, four workers
/// to each on threads of their own: the one behind takes its blocks of
/// all of them, each block once.
#[test]
fn over_real_sockets_blocks_come_from_several_peers_of_several_workers() {
    use std::net::UdpSocket;
    use std::sync::atomic::{AtomicBool, Ordering};
    use std::time::{Duration, Instant};
    let mut cfg = small_runs();
    (cfg.tick, cfg.workers) = (50 * MILLI, 4);
    let chains: Vec<_> = (0..5).map(|_| chain_of(easy())).collect();
    let blocks = grow(&chains[0], 45, 1);
    (1..4).for_each(|i| give(&chains[i], &blocks));
    let tip = chains[0].tip().unwrap();
    let sockets: Vec<UdpSocket> = (0..5).map(|_| UdpSocket::bind("127.0.0.1:0").unwrap()).collect();
    let ahead: Vec<SocketAddrV4> = sockets[..4]
        .iter()
        .map(|s| match s.local_addr().unwrap() {
            SocketAddr::V4(a) => a,
            _ => unreachable!(),
        })
        .collect();
    let stop = Arc::new(AtomicBool::new(false));
    let behind = Arc::clone(&chains[4]);
    let threads: Vec<_> = sockets
        .into_iter()
        .zip(chains)
        .enumerate()
        .map(|(i, (socket, chain))| {
            let (cfg, stop, ahead) = (cfg.clone(), Arc::clone(&stop), ahead.clone());
            std::thread::spawn(move || {
                let mut node = Node::new(cfg, NET, chain, [i as u8 + 1; 32], 0).threaded().by_port();
                if i == 4 {
                    ahead.iter().for_each(|a| assert!(node.add_peer(*a, true, 0)));
                }
                crate::net::socket::run_until(&mut node, &socket, &stop, Instant::now(), &|| NOW).unwrap();
                (node.counts(), node.tables().filter(|t| !t.is_empty()).count())
            })
        })
        .collect();
    let start = Instant::now();
    // (When its headers were all in, and when its first block was: said
    // if it is too slow, so that it is known which of the two was.)
    let (mut headers, mut first) = (None, None);
    while behind.tip().unwrap() != tip {
        if headers.is_none() && behind.best_header().is_ok_and(|b| b.header.height == tip.height) {
            headers = Some(start.elapsed());
        }
        if first.is_none() && behind.tip().unwrap().height > 0 {
            first = Some(start.elapsed());
        }
        assert!(
            start.elapsed() < SOCKETS_WITHIN,
            "at {} of {}: its headers were in after {headers:?}, its first block after {first:?}",
            behind.tip().unwrap().height,
            tip.height
        );
        std::thread::sleep(Duration::from_millis(20));
    }
    std::thread::sleep(Duration::from_millis(300));
    stop.store(true, Ordering::Relaxed);
    let ended: Vec<(Counts, usize)> = threads.into_iter().map(|t| t.join().unwrap()).collect();
    let (c, _) = ended[4];
    assert_eq!((c.headers, c.blocks, c.blocks_refused), (45, 45, 0));
    // Five runs of headers and forty-five bodies: each fetched once,
    // though four workers were fetching. (A fetch that failed over
    // real sockets, on a machine doing much else, was asked for again
    // and is no fault: what is held to is that nothing came twice.)
    assert_eq!(c.fetched, 50);
    assert!(c.fetches_failed <= 2, "{} fetches failed", c.fetches_failed);
}

/// A transaction given to one node is in every node's pool in a moment,
/// fetched by each once; and one that spends what a block has spent is
/// in none.
#[test]
fn a_transaction_crosses_the_network() {
    use crate::chain::apply::tests::extend_with;
    use crate::chain::params::COIN;
    use crate::mempool::Reject;
    use crate::output::Output;
    use crate::transaction::UnsignedTransaction;
    let chains: Vec<Arc<TestChain>> = (0..4).map(|_| chain_of(easy())).collect();
    // An output of a key of ours, made by a block every node has.
    let mut key = crate::xmss::SecretKey::generate(&[7; 32]);
    let paid = Output::new(&key.public_key(), 1500 * COIN);
    let block = extend_with(&chains[0], &[paid.block_output()]);
    chains[1..].iter().for_each(|c| give(c, std::slice::from_ref(&block)));
    let position = {
        let state = chains[0].state();
        let snapshot = state.snapshot().unwrap();
        (0..64).find(|p| snapshot.output(*p).unwrap().is_some_and(|(r, _)| r.commitment == paid.commitment)).unwrap()
    };
    let mut w = World::with(chains, &Config::default());
    for i in 1..4 {
        w.nodes[i].add_peer(at(0), true, 0);
    }
    w.run(20 * SECOND);
    assert!((0..4).all(|i| w.live(i).len() == 3));
    // Spent, all but a fee, to the same key.
    let tx = UnsignedTransaction::new(
        vec![(key.public_key(), 1500 * COIN)],
        vec![Output::new(&key.public_key(), 1499 * COIN)],
    )
    .at(&[position])
    .sign(|_, _, m| key.sign(m))
    .unwrap();
    let bytes = tx.to_bytes();
    let fetched: Vec<u64> = (0..4).map(|i| w.nodes[i].counts().fetched).collect();
    let id = w.nodes[2].hold().submit(&bytes, NOW).unwrap();
    assert_eq!(id, tx.txid());
    w.wake.iter_mut().for_each(|at| *at = w.now);
    w.run(2 * SECOND);
    for (i, before) in fetched.iter().enumerate() {
        assert!(w.nodes[i].hold().pooled(&id), "node {i}");
        assert_eq!(w.nodes[i].hold().pool_size(), (1, bytes.len()), "node {i}");
        // Each fetched it once, but the one it was given to.
        assert_eq!(w.nodes[i].counts().fetched - before, (i != 2) as u64, "node {i}");
    }
    assert_eq!(w.nodes[0].hold().submit(&bytes, NOW), Err(Reject::Known));
    // One that is not signed by the output's key is in nobody's pool.
    let mut other = crate::xmss::SecretKey::generate(&[8; 32]);
    let forged = UnsignedTransaction::new(
        vec![(key.public_key(), 1500 * COIN)],
        vec![Output::new(&other.public_key(), 1498 * COIN)],
    )
    .at(&[position])
    .sign(|_, _, m| other.sign(m));
    let forged = forged.unwrap();
    assert_eq!(w.nodes[1].hold().submit(&forged.to_bytes(), NOW), Err(Reject::BadSignature));
}

/// A node with the wallet of this seed: a relay is known by its key.
fn relay_of(w: &World, i: usize) -> (Digest, SocketAddrV4) {
    let key = crate::mldsa::keygen(&[i as u8; 32]);
    let id = crate::address::id_of(key.public_key());
    w.nodes[i].hold().participate(crate::net::sessions::Participant::new(key, &[i as u8; 64], 0));
    (id, at(i))
}

/// A way is opened from one node through three others, which are
/// nothing to it but addresses and keys; what is said to the last
/// comes back from it; and a relay knows only its neighbours.
fn a_way_through(loss: u64) {
    let mut w = World::new(5, &Config { relay: true, ..Config::default() });
    w.loss = loss;
    let path: Vec<_> = (1..=3).map(|i| relay_of(&w, i)).collect();
    let me = w.nodes[0].hold();
    let way = me.open_way(path.clone()).unwrap();
    assert_eq!(me.way(way), Some(false));
    let began = w.now;
    while me.way(way) != Some(true) {
        assert!(w.now - began < 60 * SECOND, "the way does not open: {:?}", me.way(way));
        w.run(10 * MILLI);
    }
    println!("a way of three relays opened in {} ms, of every thousand datagrams {loss} lost", (w.now - began) / MILLI);
    use crate::net::circuits::{PING, PONG};
    let began = w.now;
    me.say_along(way, vec![PING, 7, 8, 9]);
    w.woken();
    let mut said = Vec::new();
    while said.is_empty() {
        assert!(w.now - began < 60 * SECOND, "nothing comes back");
        w.run(10 * MILLI);
        said = me.take_said();
    }
    println!("and what was said along it was answered in {} ms", (w.now - began) / MILLI);
    assert_eq!(said, [(way, vec![PONG, 7, 8, 9])]);
    // Nobody talked to anybody but a neighbour: no datagram went
    // between the opener and the second or third, or the first and the
    // third. (None is a node's peer: there were no others to send.)
    assert!(w.strays.is_empty());
    assert!((0..5).all(|i| w.live(i).is_empty()));
    // A way through a relay that is another than was named does not
    // open, and is given up.
    let mut wrong = path;
    wrong[1].0 = wrong[2].0;
    let way = me.open_way(wrong).unwrap();
    w.run(40 * SECOND);
    assert_eq!(me.way(way), None);
    // And one through a node that ways do not go through: nor that.
    let way = me.open_way(vec![relay_of(&w, 4), (Digest::default(), at(9))]).unwrap();
    w.run(40 * SECOND);
    assert_eq!(me.way(way), None);
}

#[test]
fn a_way_is_opened_through_relays() {
    a_way_through(0);
}

#[test]
fn a_way_is_opened_through_relays_that_lose_datagrams() {
    a_way_through(100);
}

#[test]
fn several_workers_open_a_way_through_relays() {
    several(|| a_way_through(0));
}

/// While relays are in force a wallet is reached at the end of a way
/// through them, and sends by another: a message goes from one wallet
/// to another and is answered, between nodes that never say a word to
/// each other, by way of relays none of which knows both ends.
fn wallets_by_ways(loss: u64) {
    use crate::net::sessions::Posted;
    let mut w = World::new(7, &Config { relay: true, ..Config::default() });
    w.loss = loss;
    // Five relays, and two wallets that are no relays.
    let ids: Vec<(Digest, SocketAddrV4)> = (0..7).map(|i| relay_of(&w, i)).collect();
    let relays = ids[2..].iter().map(|(id, at)| crate::consensus::Relay { id: *id, addr: at.to_string() }).collect();
    let file = crate::consensus::File { mode: crate::consensus::Mode::Onion, relays };
    let hold: Vec<_> = w.nodes.iter().map(|n| n.hold()).collect();
    hold.iter().for_each(|h| h.force_consensus(&file));
    let began = w.now;
    while !(hold[0].reached() && hold[1].reached()) {
        assert!(w.now - began < 120 * SECOND, "the wallets are not reached: {:?}", hold[0].sessions());
        w.run(50 * MILLI);
    }
    println!(
        "two wallets were reached by ways in {} ms, of every thousand datagrams {loss} lost",
        (w.now - began) / MILLI
    );
    // From the first to the second.
    let began = w.now;
    hold[0].post(ids[1].0, crate::msg::KIND_SLATE, [7; 32], b"a slate".to_vec());
    w.woken();
    let mut came = Vec::new();
    while came.is_empty() {
        assert!(w.now - began < 120 * SECOND, "nothing comes");
        w.run(20 * MILLI);
        came = hold[1].take_messages();
    }
    println!("a message crossed in {} ms", (w.now - began) / MILLI);
    // (It says nothing of who sent it: no key of the sender's, nor
    // anything its address could be had from.)
    assert_eq!((came.len(), came[0].from, &came[0].body[..]), (1, None, &b"a slate"[..]));
    let key = crate::mldsa::keygen(&[0u8; 32]);
    assert!(!came[0].reply.windows(32).any(|w| w == &key.public_key()[..32]));
    // And its answer, sealed to what it carried.
    assert!(hold[1].answer(&came[0], crate::msg::KIND_SLATE, [8; 32], b"its answer".to_vec()));
    w.woken();
    let mut back = Vec::new();
    while back.is_empty() {
        assert!(w.now - began < 240 * SECOND, "no answer comes");
        w.run(20 * MILLI);
        back = hold[0].take_messages();
    }
    println!("and its answer was back in {} ms from the first", (w.now - began) / MILLI);
    // (Who answers is known, by a key that was checked: it is the
    // wallet the message was sent to.)
    assert_eq!((back[0].from, &back[0].body[..]), (Some(ids[1].0), &b"its answer"[..]));
    assert_eq!(back[0].answers, Some(came[0].id));
    w.run(5 * SECOND);
    assert_eq!(hold[0].take_posted(), [(ids[1].0, crate::msg::KIND_SLATE, [7; 32], Posted::Passed)]);
    assert_eq!(hold[1].take_posted(), [(Digest::default(), crate::msg::KIND_SLATE, [8; 32], Posted::Passed)]);
    // Each came once.
    assert!(hold[0].take_messages().is_empty() && hold[1].take_messages().is_empty());
    // The two wallets' nodes never said anything to each other.
    let said = |a: usize, b: usize| w.strays.iter().any(|s| (s.0, s.1) == (at(a), at(b)));
    assert!(!said(0, 1) && !said(1, 0));
    // A relay falls silent: what is sent still crosses, by the others,
    // and from then on as soon as before. (Each relay in turn, so that
    // whichever the wallets are reached at is among them.)
    // Ways opened from nowhere, thousands of them to each relay, by
    // whoever can write an address on a datagram: a relay goes after a
    // few hundred at once and no more, and the ways of those that are
    // there open as they did.
    for k in 0..3000u32 {
        let nowhere = SocketAddrV4::new([10, 9, (k >> 8) as u8, k as u8].into(), 9);
        for relay in 2..7 {
            let open = Message::Carry {
                grant: k as u64,
                name: k as u64,
                circuit: k as u64,
                kind: crate::net::circuits::OPEN,
                count: 0,
                len: crate::onion::HELLO_LEN as u32,
            };
            w.inject(nowhere, relay, &open);
        }
    }
    w.run(SECOND / 100);
    for relay in 2..7 {
        let going = w.nodes[relay].fetches.len();
        assert!((UNASKED..=UNASKED + 64).contains(&going), "{going} fetches");
        assert!(w.nodes[relay].carried.len() <= UNASKED + 64);
    }
    for silent in 2..7 {
        w.mute = vec![silent];
        let mut took = Vec::new();
        for nth in 0..3u8 {
            // (What is not passed on in a minute is given up, and is
            // sent again by whoever sent it: once, at the most, and
            // only of the first, while the ways that went by the
            // silent relay are found out.)
            let began = w.now;
            let mut came = Vec::new();
            for again in 0..2 {
                assert!(again == 0 || nth == 0, "with relay {silent} silent, nothing comes ({nth})");
                hold[0].post(ids[1].0, crate::msg::KIND_SLATE, [20 + nth; 32], vec![nth]);
                w.woken();
                let sent = w.now;
                while came.is_empty() && w.now - sent < 62 * SECOND {
                    w.run(50 * MILLI);
                    came = hold[1].take_messages();
                }
                if !came.is_empty() {
                    break;
                }
            }
            assert!(!came.is_empty(), "with relay {silent} silent, nothing comes ({nth})");
            assert_eq!(came[0].body, [nth]);
            took.push((w.now - began) / MILLI);
        }
        println!("with relay {silent} silent, messages crossed in {took:?} ms");
        w.mute.clear();
        w.run(40 * SECOND);
        hold[0].take_posted();
    }
    // To a wallet that is nowhere: said to be so.
    let nobody = crate::address::id_of(crate::mldsa::keygen(&[99; 32]).public_key());
    hold[0].post(nobody, crate::msg::KIND_SLATE, [9; 32], b"x".to_vec());
    let began = w.now;
    let mut posted = Vec::new();
    while posted.is_empty() {
        assert!(w.now - began < 120 * SECOND, "nothing is said of it");
        w.run(100 * MILLI);
        posted = hold[0].take_posted();
    }
    assert_eq!(posted, [(nobody, crate::msg::KIND_SLATE, [9; 32], Posted::Offline)]);
}

/// A node does not decide which consensus file is in force while it
/// could be otherwise: while the votes of blocks are missing that
/// could change the count, or the file with the votes is not held. It
/// says that it does not know, sends nothing by the message layer if
/// it never knew, and asks its peers; kept from the votes and the
/// file, it goes on not knowing, and does not take up init mode for
/// want of them. When it has them, it knows.
#[test]
fn what_is_in_force_is_not_decided_without_the_votes_and_the_file() {
    use crate::consensus::{Mode, WINDOW};
    let chains = vec![chain_of(easy()), chain_of(easy())];
    // The first makes a window of blocks that vote for a file it has.
    let relays: String =
        (1..=3u8).map(|i| format!("relay {} 10.0.0.{i}:3737\n", crate::address::encode(&[i; 32]))).collect();
    let file = format!("mode onion\n{relays}");
    let vote = chains[0].put_consensus_file(file.as_bytes()).unwrap();
    chains[0].set_aux_leaf(0, vote).unwrap();
    let leaves = chains[0].aux_leaves().unwrap();
    let made = grow(&chains[0], WINDOW as usize + 1, 1);
    for block in &made {
        let id = crate::block::BlockRef::from_bytes(block).unwrap().header().hash();
        chains[0].put_aux_leaves(&id, &leaves).unwrap();
    }
    assert_eq!(chains[0].consensus().unwrap().0.mode, Mode::Onion);
    // The second has the blocks, and neither their votes nor the file.
    give(&chains[1], &made);
    let mut w = World::with(chains.clone(), &Config::default());
    w.nodes[1].add_peer(at(0), false, 0);
    w.nodes[0].add_peer(at(1), false, 0);
    // Its one peer says nothing of them.
    w.mute = vec![0];
    w.run(60 * SECOND);
    let hold = w.nodes[1].hold();
    assert_eq!(hold.consensus_lacking(), Some((vec![], WINDOW, false)));
    // (Left to itself it would have counted nobody as voting, and
    // taken up init mode: which here is to be wrong for as long as a
    // peer cares to say nothing.)
    assert_eq!(chains[1].consensus().unwrap().0.mode, Mode::Init);
    // The peer gives: the votes, then the file they are for.
    w.mute.clear();
    let began = w.now;
    while hold.consensus_lacking().is_some() {
        assert!(w.now - began < 300 * SECOND, "still not known: {:?}", hold.consensus_lacking());
        w.run(SECOND);
    }
    // (As soon as the votes still missing could not change it: with
    // more for the file than there are left to come.)
    let (current, votes) = chains[1].consensus().unwrap();
    let (file, for_it) = current.winner.unwrap();
    assert_eq!((current.mode, file), (Mode::Onion, vote));
    assert!(for_it > votes.missing.len() as u32 && for_it >= crate::consensus::Current::needed(WINDOW));
    // And the rest of the votes come all the same.
    w.run(60 * SECOND);
    assert_eq!(chains[1].consensus().unwrap().1.missing.len(), 0);
}

/// One consensus file gives way to the next at a block, and each node
/// goes over when it has that block: not all at the same moment. So
/// for a few blocks a wallet is reached by the relays of both, and
/// whoever sends goes by the old ones for the first two blocks and the
/// new ones after. A message crosses whichever of the two nodes has
/// gone over, and at every block of the change; and when the change is
/// over the wallet is reached by the new relays alone.
#[test]
fn a_wallet_is_reached_by_both_files_while_one_gives_way_to_the_next() {
    let chains: Vec<_> = (0..8).map(|_| chain_of(easy())).collect();
    let made = grow(&chains[0], 10, 1);
    chains[1..].iter().for_each(|chain| give(chain, &made));
    let mut w = World::with(chains.clone(), &Config { relay: true, ..Config::default() });
    // Two wallets that are no relays; three relays of one file, and
    // three others of the next.
    let ids: Vec<(Digest, SocketAddrV4)> = (0..8).map(|i| relay_of(&w, i)).collect();
    let file = |of: &[(Digest, SocketAddrV4)]| crate::consensus::File {
        mode: crate::consensus::Mode::Onion,
        relays: of.iter().map(|(id, at)| crate::consensus::Relay { id: *id, addr: at.to_string() }).collect(),
    };
    let (old, new) = (file(&ids[2..5]), file(&ids[5..8]));
    let hold: Vec<_> = w.nodes.iter().map(|n| n.hold()).collect();
    hold.iter().for_each(|h| h.force_consensus(&old));
    let reached = |w: &mut World, who: usize, at: usize, what: &str| {
        let began = w.now;
        while hold[who].sessions().1 != at {
            assert!(w.now - began < 240 * SECOND, "{what}: {:?}", hold[who].sessions());
            w.run(50 * MILLI);
        }
    };
    let mut nth = 0u8;
    let mut crosses = |w: &mut World, what: &str| {
        nth += 1;
        let began = w.now;
        hold[0].post(ids[1].0, crate::msg::KIND_SLATE, [nth; 32], vec![nth]);
        w.woken();
        let mut came = Vec::new();
        while came.is_empty() {
            assert!(w.now - began < 240 * SECOND, "{what}: nothing comes");
            w.run(20 * MILLI);
            came = hold[1].take_messages();
        }
        assert_eq!(came[0].body, [nth], "{what}");
    };
    reached(&mut w, 0, 3, "the first is not reached");
    reached(&mut w, 1, 3, "the second is not reached");
    crosses(&mut w, "before any change");
    // The wallet that is to be paid has the block that decides (the
    // tenth, say), and the one that pays has not: reached by the
    // relays of both files, it is found where the old file says.
    hold[1].change_consensus(&new, 10);
    reached(&mut w, 1, 6, "not reached by the relays of both");
    crosses(&mut w, "the one that is paid has gone over");
    // Both have it: whoever sends still goes by the old relays.
    hold[0].change_consensus(&new, 10);
    crosses(&mut w, "both have gone over, at the block that decided");
    // Two blocks on: by the new ones, where the wallet is too.
    let more = grow(&chains[0], 2, 2);
    chains[1..].iter().for_each(|chain| give(chain, &more));
    crosses(&mut w, "two blocks on");
    assert_eq!(hold[1].sessions().1, 6);
    // And the other way about: the one that pays is two blocks on, and
    // the one that is paid has only now the block that decided.
    // (Here: gone over as of the twelfth.)
    hold[1].force_consensus(&old);
    hold[1].change_consensus(&new, 12);
    crosses(&mut w, "the one that is paid goes over later");
    // The change over: the old relays are let go of, and the wallet
    // is where the new file says, and nowhere else.
    let more = grow(&chains[0], 6, 3);
    chains[1..].iter().for_each(|chain| give(chain, &more));
    reached(&mut w, 1, 3, "still reached by the old relays");
    crosses(&mut w, "after the change");
}

/// The first file to come into force: until it does, wallets are
/// reached at the seeds, with no ways; after, by ways to its relays,
/// which may be those same seeds. In the blocks of the change a wallet
/// that has gone over is reached both ways, and one that has not finds
/// it at a seed as before: a relay passes on what comes for a wallet
/// whichever way it came, and whichever way the wallet is held.
#[test]
fn a_wallet_is_reached_at_the_seeds_while_the_first_file_comes_into_force() {
    let chains: Vec<_> = (0..7).map(|_| chain_of(easy())).collect();
    let made = grow(&chains[0], 10, 1);
    chains[1..].iter().for_each(|chain| give(chain, &made));
    let mut w = World::with(chains.clone(), &Config { relay: true, ..Config::default() });
    let ids: Vec<(Digest, SocketAddrV4)> = (0..7).map(|i| relay_of(&w, i)).collect();
    // Two seeds; and a file of three relays, one of which is a seed.
    for i in 0..7 {
        (2..4).filter(|seed| *seed != i).for_each(|seed| {
            w.nodes[i].add_seed(at(seed), 0);
        });
    }
    let relays = ids[3..6].iter().map(|(id, at)| crate::consensus::Relay { id: *id, addr: at.to_string() });
    let file = crate::consensus::File { mode: crate::consensus::Mode::Onion, relays: relays.collect() };
    let hold: Vec<_> = w.nodes.iter().map(|n| n.hold()).collect();
    let reached = |w: &mut World, who: usize, at: usize, what: &str| {
        let began = w.now;
        while hold[who].sessions().1 != at {
            assert!(w.now - began < 240 * SECOND, "{what}: {:?}", hold[who].sessions());
            w.run(50 * MILLI);
        }
    };
    let mut nth = 0u8;
    let mut crosses = |w: &mut World, what: &str| {
        nth += 1;
        let began = w.now;
        hold[0].post(ids[1].0, crate::msg::KIND_SLATE, [nth; 32], vec![nth]);
        w.woken();
        let mut came = Vec::new();
        while came.is_empty() {
            assert!(w.now - began < 240 * SECOND, "{what}: nothing comes");
            w.run(20 * MILLI);
            came = hold[1].take_messages();
        }
        assert_eq!(came[0].body, [nth], "{what}");
    };
    reached(&mut w, 0, 2, "the first is not reached at the seeds");
    reached(&mut w, 1, 2, "the second is not reached at the seeds");
    crosses(&mut w, "before any file");
    // The wallet to be paid goes over: by ways to the three relays,
    // and still at the seed that is no relay.
    hold[1].change_consensus(&file, 10);
    reached(&mut w, 1, 4, "not reached by the relays and the seed");
    crosses(&mut w, "the one that is paid has gone over");
    hold[0].change_consensus(&file, 10);
    crosses(&mut w, "both have gone over, at the block that decided");
    let more = grow(&chains[0], 2, 2);
    chains[1..].iter().for_each(|chain| give(chain, &more));
    crosses(&mut w, "two blocks on");
    // The change over: by the relays alone.
    let more = grow(&chains[0], 6, 3);
    chains[1..].iter().for_each(|chain| give(chain, &more));
    reached(&mut w, 1, 3, "still reached at the seeds");
    crosses(&mut w, "after the change");
}

#[test]
fn wallets_are_reached_and_send_by_ways_through_relays() {
    wallets_by_ways(0);
}

#[test]
fn wallets_are_reached_by_ways_that_lose_datagrams() {
    wallets_by_ways(50);
}

#[test]
fn several_workers_reach_wallets_by_ways() {
    several(|| wallets_by_ways(0));
}

/// A wallet that is a name under a name is reached by that name: it
/// shows the nodes the full name is reached at the certificate by
/// which it is, and whoever sends to the name is shown it there, with
/// what the wallet announces. The same whether wallets are reached at
/// the seeds or by ways through relays. A certificate that is not the
/// name's, by the chain, is nobody's.
fn a_name_under_a_name(relays: bool) {
    use crate::net::sessions::Posted;
    use crate::{msg::KIND_SLATE, subnames};
    let mut w = World::new(7, &Config { relay: true, ..Config::default() });
    let ids: Vec<(Digest, SocketAddrV4)> = (0..7).map(|i| relay_of(&w, i)).collect();
    let hold: Vec<_> = w.nodes.iter().map(|n| n.hold()).collect();
    match relays {
        true => {
            let relays = ids[2..].iter().map(|(id, at)| crate::consensus::Relay { id: *id, addr: at.to_string() });
            let file = crate::consensus::File { mode: crate::consensus::Mode::Onion, relays: relays.collect() };
            hold.iter().for_each(|h| h.force_consensus(&file));
        }
        false => {
            for i in 0..7 {
                (2..7).filter(|seed| *seed != i).for_each(|seed| {
                    w.nodes[i].add_seed(at(seed), 0);
                });
            }
        }
    }
    // `mailhub` is held by a key that is no node's here; `alice` under
    // it is the second wallet, and `mallory` says it is `bob`.
    let owner = crate::mldsa::keygen(&[50; 32]);
    let mallory = crate::mldsa::keygen(&[51; 32]);
    hold.iter().for_each(|h| h.name_says(b"mailhub", crate::address::id_of(owner.public_key())));
    let until = NOW + subnames::HOLDS;
    let alice = subnames::bundle(&subnames::certify(&owner, b"alice", b"mailhub", &ids[1].0, 4, until), None);
    let bob = subnames::bundle(&subnames::certify(&mallory, b"bob", b"mailhub", &ids[1].0, 4, until), None);
    let (to_alice, to_bob) = (subnames::point(b"alice", b"mailhub"), subnames::point(b"bob", b"mailhub"));
    hold[1].set_names(vec![(to_alice, 4, alice), (to_bob, 4, bob)]);
    let began = w.now;
    while !(hold[0].reached() && hold[1].name_reached(&to_alice) == 3) {
        assert!(w.now - began < 120 * SECOND, "not reached by the name: {}", hold[1].name_reached(&to_alice));
        w.run(50 * MILLI);
    }
    println!("a wallet was reached by a name under a name in {} ms (relays: {relays})", (w.now - began) / MILLI);
    assert_eq!(hold[1].name_reached(&to_bob), 0, "a certificate that is not the name's is nobody's");
    // Sent to the name: it comes to the wallet the name is, and whose
    // it turned out to be is said.
    let began = w.now;
    hold[0].post_to_name(to_alice, KIND_SLATE, [7; 32], b"to alice".to_vec());
    w.woken();
    let mut came = Vec::new();
    while came.is_empty() {
        assert!(w.now - began < 120 * SECOND, "nothing comes");
        w.run(20 * MILLI);
        came = hold[1].take_messages();
    }
    println!("and a message to the name crossed in {} ms", (w.now - began) / MILLI);
    assert_eq!((came[0].from, &came[0].body[..]), (None, &b"to alice"[..]));
    w.run(3 * SECOND);
    assert_eq!(hold[0].take_resolved(), [([7; 32], ids[1].0)]);
    assert_eq!(hold[0].take_posted(), [(ids[1].0, KIND_SLATE, [7; 32], Posted::Passed)]);
    // To a name nobody is, and to one a wallet only says it is.
    for (name, tag) in [(subnames::point(b"carol", b"mailhub"), [8; 32]), (to_bob, [9; 32])] {
        hold[0].post_to_name(name, KIND_SLATE, tag, b"x".to_vec());
        w.woken();
        let began = w.now;
        let mut posted = Vec::new();
        while posted.is_empty() {
            assert!(w.now - began < 120 * SECOND, "nothing is said of it");
            w.run(100 * MILLI);
            posted = hold[0].take_posted();
        }
        assert_eq!(posted, [(name, KIND_SLATE, tag, Posted::Offline)]);
    }
    assert!(hold[0].take_resolved().is_empty() && hold[1].take_messages().is_empty());
    // The name is given to another wallet, by a newer certificate: it
    // is that wallet's from then on, and the first is told no.
    let newer = subnames::bundle(&subnames::certify(&owner, b"alice", b"mailhub", &ids[0].0, 5, until), None);
    hold[0].set_names(vec![(to_alice, 5, newer)]);
    let began = w.now;
    while hold[0].name_reached(&to_alice) != 3 || hold[1].name_reached(&to_alice) != 0 {
        assert!(
            w.now - began < 240 * SECOND,
            "{} {}",
            hold[0].name_reached(&to_alice),
            hold[1].name_reached(&to_alice)
        );
        w.run(SECOND);
    }
}

#[test]
fn a_wallet_is_reached_by_a_name_under_a_name_at_the_seeds() {
    a_name_under_a_name(false);
}

#[test]
fn a_wallet_is_reached_by_a_name_under_a_name_by_ways() {
    a_name_under_a_name(true);
}

#[test]
fn several_workers_reach_a_wallet_by_a_name_under_a_name() {
    several(|| a_name_under_a_name(true));
    several(|| a_name_under_a_name(false));
}
