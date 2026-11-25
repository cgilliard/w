//! A node's settings: how many peers, how many fetches at once, how
//! long to wait.
//!
//! Every one has a default, and the defaults are what a node runs with
//! unless told otherwise. They are a node's own business: two nodes
//! with different settings talk to each other as well as two with the
//! same. What both ends must agree on is not here but with what it
//! concerns: the datagram's size ([`super::MAX_DATAGRAM`]), a chunk's
//! ([`crate::transport::CHUNK_BYTES`]), a part's
//! ([`crate::store::outputs::PART_LEVEL`]), the most headers in an
//! object ([`super::object::MAX_HEADERS`]).
//!
//! Nor are the transport's own numbers here (its windows, its retry
//! times; how much a node serves is here): they are how it works, and a node that set them badly would
//! hurt its peers as well as itself.

use crate::error::Error;
use crate::transport::{MILLI, Micros, SECOND};

const MINUTE: Micros = 60 * SECOND;

/// The settings. See each group.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Config {
    /// How often a node looks to what passes with time: whom to ping,
    /// whom to drop, what to fetch next.
    pub tick: Micros,
    /// Workers: each has the hosts that are its own, and is given
    /// their datagrams (`docs/THREADS.md`).
    pub workers: usize,
    /// Datagrams that may wait for one worker: one that comes when so
    /// many do is dropped.
    pub request_queue: usize,
    /// Bytes of transactions the pool holds at the most.
    pub pool: usize,
    /// What the pool asks of a transaction beyond its being valid, and
    /// what of a block this node mines is for the oldest.
    pub policy: crate::mempool::Policy,
    /// Whether the node stands between wallets on the message layer:
    /// holds sessions for them, and passes on what is sealed to them
    /// ([`super::sessions`]). Only a node told to does.
    pub relay: bool,
    /// How the sessions it holds are bounded.
    pub sessions: super::sessions::Limits,
    /// And how the ways through it are ([`super::circuits`]).
    pub circuits: super::circuits::Limits,
    /// How often a wallet says, to a node it is reached at, that it is
    /// there.
    pub keepalive: Micros,
    /// For how many blocks from the one at which another consensus
    /// file comes into force a wallet goes on being reached by the
    /// nodes of the one before as well
    /// ([`crate::consensus::GRACE`], unless said: never fewer than
    /// whoever sends takes to go over to the new ones,
    /// [`crate::consensus::SWITCH`], and one more).
    pub grace: u32,
    pub peers: Peers,
    pub sync: Sync,
    pub serve: Serve,
}

/// Whom a node knows, and when it gives up on them.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Peers {
    /// Peers kept in the table.
    pub max: usize,
    /// Below this many live peers, more are looked for.
    pub target: usize,
    /// Peers of one host, over all its ports: several nodes behind one
    /// address (a household, an office) without one host filling the
    /// table.
    pub per_host: usize,
    /// Peers of one network (a /16): so that whoever holds one network's
    /// addresses cannot surround a node.
    pub per_network: usize,
    /// Addresses not yet shown to be there that are pinged each tick: a
    /// forged ping costs its victim at most this much.
    pub unproven_pings: usize,
    /// Between pings of a peer.
    pub ping: Micros,
    /// Before the second ping of a peer that has not answered the
    /// first; twice as long before each one after, up to `ping`.
    pub first_ping_retry: Micros,
    /// A peer silent this long is not counted as live.
    pub live_silence: Micros,
    /// A peer silent this long is dropped.
    pub drop_silence: Micros,
    /// A host's peer silent this long gives its place to a new port of
    /// that host: a node there that restarted behind a translator.
    pub host_stale: Micros,
    /// While live peers are fewer than `target`: how often one of them
    /// is asked whom else it knows.
    pub discover: Micros,
    /// Bad answers before a peer is dropped and its host refused.
    pub strikes: u32,
    /// A peer's strikes are forgotten this long after the last.
    pub strike_decay: Micros,
    /// How long a host is refused.
    pub ban: Micros,
}

/// How a node catches up and keeps up.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Sync {
    /// Headers asked for in one object: [`super::object::MAX_HEADERS`]
    /// at most.
    pub headers: u16,
    /// Objects of headers fetched at once, each from another peer.
    pub header_fetches: usize,
    /// A peer that claims more work than ours and sends no header we
    /// lack within this is not believed.
    pub header_wait: Micros,
    /// How long a peer that was not believed, or that a fetch failed
    /// from, is passed over.
    pub pass_over: Micros,
    /// Between requests for headers to one peer, at the least.
    pub header_spacing: Micros,
    /// Blocks fetched at once.
    pub blocks: usize,
    /// Blocks fetched at once from one peer.
    pub blocks_per_peer: usize,
    /// How far past the first block missing blocks are fetched.
    pub lookahead: usize,
    /// How many blocks under the best header the block is whose state a
    /// joining node takes whole. Zero: every block from the first is
    /// applied instead.
    pub sync_point: u32,
    /// How many blocks under the best header the chain may be and still
    /// be caught up block by block: further behind, the state is taken
    /// whole though the blocks could be had (of nodes that keep every
    /// block, a node would else never take it). Zero: only when the
    /// blocks cannot be had. Twice the sync point at the least: a node
    /// that has just taken the state is the sync point behind.
    pub sync_behind: u32,
    /// Parts of that state fetched at once.
    pub parts: usize,
    /// What is fetched for the chain (headers, a block, a piece of a
    /// state) comes at this many bytes a second at the least, counted
    /// once it has been asked for this long: slower, it is given up
    /// and asked of another. A peer that says first that it has a
    /// block, and then sends it a little at a time, would else be the
    /// only one asked for it for as long as it cared to. Zero: however
    /// slowly.
    pub fetch_rate: u64,
    pub fetch_grace: Micros,
    /// How long a block's fetch may bring nothing new before another
    /// peer that has the block is asked for the rest of it (four of
    /// the path's retry times at the least: on a slow line nothing new
    /// for seconds is the line).
    pub fetch_quiet: Micros,
    /// Attempts at taking a state before every block is applied
    /// instead.
    pub snapshot_attempts: u32,
    /// Between requests for a block's aux leaves, and how many are made
    /// before giving up.
    pub leaves_retry: Micros,
    pub leaves_tries: u32,
}

/// What a node does for those that ask.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Serve {
    /// Chunks sent a second, to everyone together.
    pub rate: u32,
    /// Requests for chunks that may wait to be answered, in all. One
    /// over is dropped, and looks to its sender like loss.
    pub waiting: usize,
    /// Requests of one address that may wait.
    pub waiting_each: usize,
    /// Chunks of one address that may wait: a full window
    /// ([`crate::transport::MAX_WINDOW`]) at the least.
    pub chunks_each: u32,
    /// How often the secret behind the tokens is replaced. A token is
    /// honoured for this long at least and twice it at most.
    pub token_life: Micros,
}

impl Default for Peers {
    fn default() -> Peers {
        Peers {
            max: 64,
            target: 8,
            per_host: 4,
            per_network: 8,
            unproven_pings: 8,
            ping: 30 * SECOND,
            first_ping_retry: 2 * SECOND,
            live_silence: 65 * SECOND,
            drop_silence: 180 * SECOND,
            host_stale: 60 * SECOND,
            discover: SECOND,
            strikes: 5,
            strike_decay: 10 * MINUTE,
            ban: 60 * MINUTE,
        }
    }
}

impl Default for Sync {
    fn default() -> Sync {
        Sync {
            headers: super::object::MAX_HEADERS,
            header_fetches: 16,
            header_wait: 15 * SECOND,
            pass_over: 10 * MINUTE,
            header_spacing: 2 * SECOND,
            blocks: 24,
            blocks_per_peer: 8,
            lookahead: 32,
            sync_point: 144,
            sync_behind: 1008,
            parts: 32,
            fetch_rate: 4096,
            fetch_grace: 30 * SECOND,
            fetch_quiet: 3 * SECOND,
            snapshot_attempts: 4,
            leaves_retry: 2 * SECOND,
            leaves_tries: 16,
        }
    }
}

impl Serve {
    /// The transport's part of these.
    pub fn limits(&self) -> crate::transport::serve::Limits {
        crate::transport::serve::Limits {
            rate: self.rate,
            waiting: self.waiting,
            waiting_each: self.waiting_each,
            chunks_each: self.chunks_each,
        }
    }
}

impl Default for Serve {
    fn default() -> Serve {
        let l = crate::transport::serve::Limits::default();
        Serve {
            rate: l.rate,
            waiting: l.waiting,
            waiting_each: l.waiting_each,
            chunks_each: l.chunks_each,
            token_life: 10 * MINUTE,
        }
    }
}

#[allow(clippy::derivable_impls)]
impl Default for Config {
    fn default() -> Config {
        Config {
            tick: SECOND,
            workers: 1,
            request_queue: 4096,
            pool: crate::mempool::DEFAULT_CAPACITY,
            policy: crate::mempool::Policy::MAINNET,
            relay: false,
            sessions: super::sessions::Limits::default(),
            circuits: super::circuits::Limits::default(),
            keepalive: 30 * SECOND,
            grace: crate::consensus::GRACE,
            peers: Peers::default(),
            sync: Sync::default(),
            serve: Serve::default(),
        }
    }
}

impl Config {
    /// Whether a node can run with these: [`Error::Setting`] names the
    /// first that it cannot. Settings that are merely unwise pass.
    pub fn check(&self) -> Result<(), Error> {
        let (p, s) = (&self.peers, &self.sync);
        let need = |ok: bool, what: &'static str| if ok { Ok(()) } else { Err(Error::Setting(what)) };
        need(self.tick >= 10 * MILLI && self.tick <= 10 * SECOND, "tick is not between 10 ms and 10 s")?;
        need(self.workers >= 1 && self.workers <= 1024, "workers is not between 1 and 1024")?;
        need(self.request_queue >= 1, "request_queue is zero")?;
        need(p.max >= 1, "peers.max is zero")?;
        need(p.target >= 1 && p.target <= p.max, "peers.target is not between one and peers.max")?;
        need(p.per_host >= 1, "peers.per_host is zero")?;
        need(p.per_network >= p.per_host, "peers.per_network is under peers.per_host")?;
        need(p.ping >= SECOND, "peers.ping is under a second")?;
        need(p.first_ping_retry >= 100 * MILLI, "peers.first_ping_retry is under a tenth of a second")?;
        // Two pings unanswered at the least before a peer is thought gone.
        need(p.live_silence >= 2 * p.ping, "peers.live_silence is under two pings")?;
        need(p.drop_silence >= p.live_silence, "peers.drop_silence is under peers.live_silence")?;
        need(p.discover >= 100 * MILLI, "peers.discover is under a tenth of a second")?;
        need(p.strikes >= 1, "peers.strikes is zero")?;
        need(s.headers >= 1 && s.headers <= super::object::MAX_HEADERS, "sync.headers is not between 1 and 512")?;
        need(s.header_fetches >= 1, "sync.header_fetches is zero")?;
        need(s.blocks >= 1 && s.blocks_per_peer >= 1, "sync.blocks or sync.blocks_per_peer is zero")?;
        need(s.lookahead >= 1, "sync.lookahead is zero")?;
        need(s.parts >= 1, "sync.parts is zero")?;
        // (A node that has taken the state is as far under the best
        // header as the sync point says, with those blocks to apply
        // while more are made: were that "far behind", it would take
        // the state again, and again.)
        need(
            s.sync_point == 0 || s.sync_behind == 0 || s.sync_behind as u64 >= 2 * s.sync_point as u64,
            "sync.sync_behind is under twice sync.sync_point",
        )?;
        need(self.serve.rate >= 1, "serve.rate is zero")?;
        need(self.serve.waiting_each >= 1, "serve.waiting_each is zero")?;
        need(self.serve.waiting >= self.serve.waiting_each, "serve.waiting is under serve.waiting_each")?;
        need(
            self.serve.chunks_each >= crate::transport::MAX_WINDOW,
            "serve.chunks_each is under a full window (2048)",
        )?;
        need(self.serve.token_life >= MINUTE, "serve.token_life is under a minute")?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_defaults_are_what_the_document_says_and_can_be_run_with() {
        let c = Config::default();
        assert_eq!(c.check(), Ok(()));
        assert_eq!(c.tick, SECOND);
        let (p, s) = (&c.peers, &c.sync);
        assert_eq!((p.max, p.target, p.per_host, p.per_network, p.unproven_pings), (64, 8, 4, 8, 8));
        assert_eq!((p.ping, p.first_ping_retry), (30 * SECOND, 2 * SECOND));
        assert_eq!((p.live_silence, p.drop_silence, p.host_stale), (65 * SECOND, 180 * SECOND, 60 * SECOND));
        assert_eq!((p.strikes, p.strike_decay, p.ban, p.discover), (5, 600 * SECOND, 3600 * SECOND, SECOND));
        assert_eq!((s.headers, s.header_fetches, s.header_wait, s.pass_over), (512, 16, 15 * SECOND, 600 * SECOND));
        assert_eq!((s.blocks, s.blocks_per_peer, s.lookahead, s.header_spacing), (24, 8, 32, 2 * SECOND));
        assert_eq!((s.sync_point, s.parts, s.snapshot_attempts), (144, 32, 4));
        assert_eq!((s.leaves_retry, s.leaves_tries), (2 * SECOND, 16));
        assert_eq!((c.serve.rate, c.serve.token_life), (8192, 600 * SECOND));
        assert_eq!((c.serve.waiting, c.serve.waiting_each, c.serve.chunks_each), (256, 32, 4096));
        // What it hands the transport is what the transport would take.
        let _ = crate::transport::serve::Serve::with(c.serve.limits());
    }

    #[test]
    fn settings_a_node_cannot_run_with_are_named() {
        let bad = |change: fn(&mut Config)| {
            let mut c = Config::default();
            change(&mut c);
            match c.check() {
                Err(Error::Setting(what)) => what,
                other => panic!("{other:?}"),
            }
        };
        assert!(bad(|c| c.tick = 0).contains("tick"));
        assert!(bad(|c| c.peers.max = 0).contains("peers.max"));
        assert!(bad(|c| c.peers.target = 65).contains("peers.target"));
        assert!(bad(|c| c.peers.target = 0).contains("peers.target"));
        assert!(bad(|c| c.peers.per_network = 3).contains("peers.per_network"));
        assert!(bad(|c| c.peers.ping = 0).contains("peers.ping"));
        assert!(bad(|c| c.peers.live_silence = 59 * SECOND).contains("peers.live_silence"));
        assert!(bad(|c| c.peers.drop_silence = 64 * SECOND).contains("peers.drop_silence"));
        assert!(bad(|c| c.peers.strikes = 0).contains("peers.strikes"));
        assert!(bad(|c| c.sync.headers = 0).contains("sync.headers"));
        assert!(bad(|c| c.sync.headers = 513).contains("sync.headers"));
        assert!(bad(|c| c.sync.header_fetches = 0).contains("sync.header_fetches"));
        assert!(bad(|c| c.sync.sync_behind = 287).contains("sync.sync_behind"));
        assert!(bad(|c| c.sync.sync_point = 505).contains("sync.sync_behind"));
        assert!(bad(|c| c.sync.blocks_per_peer = 0).contains("sync.blocks"));
        assert!(bad(|c| c.sync.parts = 0).contains("sync.parts"));
        assert!(bad(|c| c.serve.rate = 0).contains("serve.rate"));
        assert!(bad(|c| c.serve.waiting_each = 0).contains("serve.waiting_each"));
        assert!(bad(|c| c.serve.waiting = 7).contains("serve.waiting"));
        assert!(bad(|c| c.serve.chunks_each = 2047).contains("serve.chunks_each"));
        assert!(bad(|c| c.serve.token_life = SECOND).contains("serve.token_life"));
        // Unwise, and a node's own business: no snapshot, one peer.
        let mut c = Config::default();
        (c.sync.sync_point, c.peers.max, c.peers.target, c.peers.per_host, c.peers.per_network) = (0, 1, 1, 1, 1);
        assert_eq!(c.check(), Ok(()));
    }
}
