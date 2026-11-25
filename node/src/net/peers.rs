//! The peers a node knows: who they are, which have shown they are
//! where they say, and whom to ask for what.
//!
//! An address gets into the table by being told of (a seed, a peer's
//! list, a saved file) or by pinging us. It is then only an address to
//! try. It becomes a peer to be believed when it answers one of our
//! pings with that ping's number: it is *proven*, since whoever answers
//! received what we sent there. A proven peer heard from lately is
//! *live*. Only live peers are told things, asked things, or believed
//! about the work of their chain.
//!
//! # What keeps the table honest
//!
//! Addresses cost nothing to make up, so the table is bounded every way
//! one party could fill it ([`super::config::Peers`]): so many in all,
//! so many of one host, so many of one network. When it is full a new
//! address takes the place of one that never proved itself, and of no
//! other: forged pings and invented lists cannot push out real peers.
//!
//! A peer that answers what we asked with something wrong takes a
//! *strike*; enough of them and its host is refused for a while. Only
//! answers count. Anything that arrives unasked may carry a forged
//! address, and is held against nobody.
//!
//! Seeds, and peers given by hand, are kept whatever they do: they are
//! what a node starts from.
//!
//! # No clock, no socket
//!
//! The time is given to everything here that needs it, and nothing is
//! sent: [`Peers::pings_due`] says whom to ping, and the caller does
//! it.

use std::collections::BTreeMap;
use std::net::{Ipv4Addr, SocketAddrV4};
use std::sync::Arc;
use std::sync::atomic::{AtomicU32, AtomicUsize, Ordering};

use super::config;
use super::message::{Addrs, Status};
use crate::transport::Micros;
use crate::transport::path::Path;
use crate::u256::U256;

/// Why an address is not taken into the table.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Refused {
    /// No address at all: no host, or no port.
    Unusable,
    /// This node's own address.
    Itself,
    /// Its host is refused for now, for what a peer there did.
    Banned,
    /// Its host has as many peers as one host may, none of them silent
    /// long enough to give way.
    Host,
    /// Its network has as many peers as one network may.
    Network,
    /// The table is full of peers that have proven themselves.
    Full,
}

/// A peer.
#[derive(Clone, Copy, Debug)]
pub struct Peer {
    pub addr: SocketAddrV4,
    /// A seed, or given by hand: kept whatever it does.
    pub seed: bool,
    /// It answered one of our pings: it is at its address.
    pub proven: bool,
    /// What it last said of itself.
    pub status: Option<Status>,
    /// When something well-formed last came from it.
    pub last_seen: Option<Micros>,
    /// What has been learned of the path to it, for fetches from it.
    pub path: Path,
    /// Objects it has delivered whole and right.
    pub delivered: u32,
    last_ping: Option<Micros>,
    /// When it was first pinged: one that never answers is dropped from
    /// then, however often it is pinged again.
    first_ping: Option<Micros>,
    /// The number of the ping awaiting its pong.
    pending: Option<u64>,
    /// Pings repeated before its first pong.
    repeats: u32,
    strikes: u32,
    last_strike: Option<Micros>,
    /// When a fetch from it last failed, or it last claimed work it did
    /// not back with headers.
    failed: Option<Micros>,
    /// Since when headers we lack have been awaited from it.
    headers_asked: Option<Micros>,
}

impl Peer {
    /// The token it gave us for our requests to it: none before its
    /// status.
    pub fn token(&self) -> Option<u64> {
        self.status.map(|s| s.token)
    }
}

/// The table.
/// How many peers a node has in all, and of each network: counted over
/// every table of the node, where its peers are kept in several, each
/// by a thread of its own (`docs/THREADS.md`, 4.1). Counts only, each
/// one number changed in one step: nothing is locked.
pub struct Totals {
    peers: AtomicUsize,
    /// Peers that are not seeds, by the first two bytes of the address:
    /// one count for each network there can be.
    networks: Box<[AtomicU32]>,
}

impl Totals {
    pub fn new() -> Totals {
        Totals { peers: AtomicUsize::new(0), networks: (0..1 << 16).map(|_| AtomicU32::new(0)).collect() }
    }

    /// Peers in all.
    pub fn peers(&self) -> usize {
        self.peers.load(Ordering::Relaxed)
    }

    fn of_network(&self, addr: &SocketAddrV4) -> &AtomicU32 {
        let [a, b, _, _] = addr.ip().octets();
        &self.networks[(a as usize) << 8 | b as usize]
    }

    /// Peers of `addr`'s network that are not seeds.
    pub fn network(&self, addr: &SocketAddrV4) -> usize {
        self.of_network(addr).load(Ordering::Relaxed) as usize
    }
}

impl Default for Totals {
    fn default() -> Totals {
        Totals::new()
    }
}

pub struct Peers {
    cfg: config::Peers,
    /// The node's peers in all, this table's among them.
    totals: Arc<Totals>,
    /// How long a peer that failed us is passed over.
    pass_over: Micros,
    /// How long a peer may take to send a header we lack.
    header_wait: Micros,
    /// By address, so that a peer is found, and the peers of a host or
    /// of a network counted, without going through the table: a node
    /// many others lean on may keep thousands.
    peers: BTreeMap<SocketAddrV4, Peer>,
    /// Addresses found to be this node's own.
    selves: Vec<SocketAddrV4>,
    /// Hosts refused, and since when. (A host is its address with no
    /// port; on this machine, where many nodes may run, the address
    /// with its port.)
    banned: BTreeMap<SocketAddrV4, Micros>,
    /// How many in the table are neither proven nor seeds: the ones a
    /// full table gives up.
    unproven: usize,
    /// The state of the generator peers are sampled with.
    random: u64,
}

/// What a ban is of: the host, whatever the port (a new port would get
/// around it otherwise); on this machine, the address with its port.
fn ban_key(addr: &SocketAddrV4) -> SocketAddrV4 {
    if addr.ip().is_loopback() { *addr } else { SocketAddrV4::new(*addr.ip(), 0) }
}

/// The most addresses remembered as this node's own, and hosts as
/// refused, for each peer the table holds.
const SELVES: usize = 16;
const BANS_EACH: usize = 4;

impl Peers {
    /// An empty table with these settings. `seed` starts the generator
    /// peers are sampled with: from the operating system's random
    /// source, so that which peers a node tells of cannot be foretold.
    pub fn new(cfg: &config::Config, seed: u64) -> Peers {
        Peers::sharing(cfg, seed, Arc::new(Totals::new()))
    }

    /// [`Peers::new`], for one of a node's several tables: the limits
    /// on peers in all and on those of one network hold over all of
    /// them, by `totals`. (A host's peers are all in one table.)
    pub fn sharing(cfg: &config::Config, seed: u64, totals: Arc<Totals>) -> Peers {
        Peers {
            totals,
            cfg: cfg.peers.clone(),
            pass_over: cfg.sync.pass_over,
            header_wait: cfg.sync.header_wait,
            peers: BTreeMap::new(),
            selves: Vec::new(),
            banned: BTreeMap::new(),
            unproven: 0,
            random: seed | 1,
        }
    }

    pub fn len(&self) -> usize {
        self.peers.len()
    }

    pub fn is_empty(&self) -> bool {
        self.peers.is_empty()
    }

    pub fn get(&self, addr: &SocketAddrV4) -> Option<&Peer> {
        self.peers.get(addr)
    }

    fn get_mut(&mut self, addr: &SocketAddrV4) -> Option<&mut Peer> {
        self.peers.get_mut(addr)
    }

    /// Every peer in the table, in the order of their addresses.
    pub fn all(&self) -> impl Iterator<Item = &Peer> {
        self.peers.values()
    }

    /// The peers whose addresses' first `bits` bits are `addr`'s: of
    /// its host (32) or of its network (16). They lie together in the
    /// order of addresses.
    fn of(&self, addr: &SocketAddrV4, bits: u32) -> impl Iterator<Item = &Peer> {
        let ip = u32::from(*addr.ip());
        let mask = u32::MAX << (32 - bits);
        let first = SocketAddrV4::new(Ipv4Addr::from(ip & mask), 0);
        let last = SocketAddrV4::new(Ipv4Addr::from(ip | !mask), u16::MAX);
        self.peers.range(first..=last).map(|(_, p)| p)
    }

    fn is_banned(&self, addr: &SocketAddrV4, now: Micros) -> bool {
        self.banned.get(&ban_key(addr)).is_some_and(|since| now.saturating_sub(*since) < self.cfg.ban)
    }

    /// Why `addr` would not be taken into the table now, if it would
    /// not be. An address already in it is not refused.
    pub fn refusal(&self, addr: &SocketAddrV4, seed: bool, now: Micros) -> Option<Refused> {
        if addr.ip().is_unspecified() || addr.ip().is_broadcast() || addr.ip().is_multicast() || addr.port() == 0 {
            return Some(Refused::Unusable);
        }
        if self.selves.contains(addr) {
            return Some(Refused::Itself);
        }
        if self.is_banned(addr, now) {
            return Some(Refused::Banned);
        }
        if self.get(addr).is_some() {
            return None;
        }
        // Seeds are a node's own choice, and this machine is one host
        // however many nodes run on it: neither is counted.
        if !seed && !addr.ip().is_loopback() {
            let of_host = self.of(addr, 32).count();
            if of_host >= self.cfg.per_host && self.stale_of_host(addr, now).is_none() {
                return Some(Refused::Host);
            }
            let of_network = self.totals.network(addr);
            // (One of the host's own may be about to give way to it.)
            let leaving = (of_host >= self.cfg.per_host) as usize;
            if of_network - leaving.min(of_network) >= self.cfg.per_network {
                return Some(Refused::Network);
            }
        }
        if self.totals.peers() >= self.cfg.max && self.unproven == 0 {
            return Some(Refused::Full);
        }
        None
    }

    /// Takes `addr` into the table as an address to try. `Ok(true)` if
    /// it is new, `Ok(false)` if it was there already (and is a seed
    /// from now on, if `seed`).
    pub fn add(&mut self, addr: SocketAddrV4, seed: bool, now: Micros) -> Result<bool, Refused> {
        if let Some(why) = self.refusal(&addr, seed, now) {
            return Err(why);
        }
        if let Some(p) = self.peers.get_mut(&addr) {
            // A seed from now on, and so not one a full table gives up.
            self.unproven -= (seed && !p.seed && !p.proven) as usize;
            if seed && !p.seed {
                self.totals.of_network(&addr).fetch_sub(1, Ordering::Relaxed);
            }
            p.seed |= seed;
            return Ok(false);
        }
        if !seed && !addr.ip().is_loopback() && self.of(&addr, 32).count() >= self.cfg.per_host {
            // The host's longest silent peer gives way.
            let old = self.stale_of_host(&addr, now).expect("or it was refused");
            self.remove(&old);
        }
        if self.totals.peers() >= self.cfg.max {
            // One that never proved itself gives way, and no other: the
            // one that has left a ping unanswered longest. One not yet
            // tried does not: it was learned of honestly as likely as
            // not, and whoever writes addresses on pings would else
            // have every such address out of the table before it was
            // asked anything.
            let tried = self.peers.values().filter(|p| !p.proven && !p.seed && p.first_ping.is_some());
            let Some(old) = tried.min_by_key(|p| p.first_ping).map(|p| p.addr) else {
                return Err(Refused::Full);
            };
            self.remove(&old);
        }
        self.unproven += !seed as usize;
        self.totals.peers.fetch_add(1, Ordering::Relaxed);
        if !seed {
            self.totals.of_network(&addr).fetch_add(1, Ordering::Relaxed);
        }
        self.peers.insert(
            addr,
            Peer {
                addr,
                seed,
                proven: false,
                status: None,
                last_seen: None,
                path: Path::new(),
                delivered: 0,
                last_ping: None,
                first_ping: None,
                pending: None,
                repeats: 0,
                strikes: 0,
                last_strike: None,
                failed: None,
                headers_asked: None,
            },
        );
        Ok(true)
    }

    /// Takes a peer out of the table.
    pub fn remove(&mut self, addr: &SocketAddrV4) {
        if let Some(p) = self.peers.remove(addr) {
            self.unproven -= (!p.proven && !p.seed) as usize;
            self.totals.peers.fetch_sub(1, Ordering::Relaxed);
            if !p.seed {
                self.totals.of_network(addr).fetch_sub(1, Ordering::Relaxed);
            }
        }
    }

    /// The peer of `addr`'s host (not a seed) silent longest, if silent
    /// long enough to give its place to a new address of that host:
    /// since it last answered or, never having answered, since it was
    /// first pinged. One not yet pinged does not give way, or addresses
    /// from a list would push each other out.
    fn stale_of_host(&self, addr: &SocketAddrV4, now: Micros) -> Option<SocketAddrV4> {
        self.of(addr, 32)
            .filter(|p| !p.seed)
            .filter_map(|p| p.last_seen.or(p.first_ping).map(|t| (t, p.addr)))
            .filter(|(t, _)| now.saturating_sub(*t) >= self.cfg.host_stale)
            .min_by_key(|(t, _)| *t)
            .map(|(_, a)| a)
    }

    /// Something well-formed came from `addr`.
    pub fn seen(&mut self, addr: &SocketAddrV4, now: Micros) {
        if let Some(p) = self.get_mut(addr) {
            p.last_seen = Some(now);
        }
    }

    /// What `addr` says of itself, in a ping: kept if it is a peer.
    pub fn set_status(&mut self, addr: &SocketAddrV4, status: Status) {
        if let Some(p) = self.get_mut(addr) {
            p.status = Some(status);
        }
    }

    /// `addr` has announced a block of this height: its chain reaches
    /// there, though its last ping said less.
    pub fn reaches(&mut self, addr: &SocketAddrV4, height: u32, tip: crate::hash::Digest) {
        if let Some(status) = self.get_mut(addr).and_then(|p| p.status.as_mut())
            && status.height < height
        {
            (status.height, status.tip) = (height, tip);
        }
    }

    /// Whether `addr` has answered a ping of ours.
    pub fn proven(&self, addr: &SocketAddrV4) -> bool {
        self.get(addr).is_some_and(|p| p.proven)
    }

    /// Whom to ping now: `ping(addr, number)` is called for each, and
    /// the caller sends it. A peer is pinged every
    /// [`config::Peers::ping`]; one that has not answered yet sooner,
    /// with the same number again, waiting twice as long each time. Of
    /// addresses not yet proven, at most
    /// [`config::Peers::unproven_pings`] a call: were our pings sent
    /// wherever a forged ping or an invented list said, they would be
    /// a flood of someone else's making.
    pub fn pings_due(&mut self, now: Micros, mut number: impl FnMut() -> u64, mut ping: impl FnMut(SocketAddrV4, u64)) {
        let mut budget = self.cfg.unproven_pings;
        for p in self.peers.values_mut() {
            let every = if p.proven {
                self.cfg.ping
            } else {
                (self.cfg.first_ping_retry << p.repeats.min(16)).min(self.cfg.ping)
            };
            if p.last_ping.is_some_and(|t| now.saturating_sub(t) < every) {
                continue;
            }
            if !p.proven && !p.seed {
                if budget == 0 {
                    continue;
                }
                budget -= 1;
            }
            // Before the first pong, the same ping again: a slow pong to
            // an earlier copy still counts.
            let n = match p.pending {
                Some(n) if !p.proven => {
                    p.repeats += 1;
                    n
                }
                _ => number(),
            };
            p.last_ping = Some(now);
            p.first_ping.get_or_insert(now);
            p.pending = Some(n);
            ping(p.addr, n);
        }
    }

    /// Whether to ping `addr` at once, outside its turn, with `number`:
    /// it pinged us and has not proven itself. True if it is a peer
    /// not proven, with no ping awaiting an answer; it is then marked
    /// pinged.
    pub fn ping_now(&mut self, addr: &SocketAddrV4, number: u64, now: Micros) -> bool {
        match self.get_mut(addr) {
            Some(p) if p.pending.is_none() && !p.proven => {
                p.last_ping = Some(now);
                p.first_ping.get_or_insert(now);
                p.pending = Some(number);
                true
            }
            _ => false,
        }
    }

    /// Whether a ping from `addr` with this number is our own ping to
    /// `addr`, come back: then `addr` is this node.
    pub fn is_own_ping(&self, addr: &SocketAddrV4, number: u64) -> bool {
        self.get(addr).is_some_and(|p| p.pending == Some(number))
    }

    /// `addr` is this node: out of the table, and never in it again.
    pub fn mark_self(&mut self, addr: SocketAddrV4) {
        self.remove(&addr);
        if !self.selves.contains(&addr) {
            if self.selves.len() == SELVES {
                self.selves.remove(0);
            }
            self.selves.push(addr);
        }
    }

    /// A pong from `addr`. False, and nothing changed, unless it
    /// carries the number of a ping of ours to that address that awaits
    /// its answer; then the peer is proven, and its status kept.
    ///
    /// A ping sent once and answered measures the round trip to the
    /// peer, which the path to it starts from.
    pub fn pong(&mut self, addr: &SocketAddrV4, status: Status, now: Micros) -> bool {
        let Some(p) = self.get_mut(addr) else {
            return false;
        };
        if p.pending != Some(status.nonce) {
            return false;
        }
        p.pending = None;
        p.status = Some(status);
        let newly = !p.proven && !p.seed;
        p.proven = true;
        p.last_seen = Some(now);
        if p.repeats == 0
            && let Some(sent) = p.last_ping
        {
            p.path.sample(now.saturating_sub(sent));
        }
        p.repeats = 0;
        self.unproven -= newly as usize;
        true
    }

    /// `addr` said it is going: not live, nor asked anything, until it
    /// answers a ping again. Its place is kept, for when it is back.
    pub fn gone(&mut self, addr: &SocketAddrV4) {
        if let Some(p) = self.peers.get_mut(addr) {
            self.unproven += (p.proven && !p.seed) as usize;
            p.proven = false;
            p.status = None;
            p.pending = None;
            p.repeats = 0;
            p.headers_asked = None;
        }
    }

    /// `addr` answered what we asked with something wrong. True if that
    /// was one strike too many: it is out of the table, with every
    /// other peer of its host, and the host refused for
    /// [`config::Peers::ban`]. A seed takes no strikes.
    pub fn strike(&mut self, addr: &SocketAddrV4, now: Micros) -> bool {
        let (decay, most) = (self.cfg.strike_decay, self.cfg.strikes);
        let Some(p) = self.get_mut(addr) else {
            return false;
        };
        if p.seed {
            return false;
        }
        if p.last_strike.is_some_and(|t| now.saturating_sub(t) >= decay) {
            p.strikes = 0;
        }
        p.strikes += 1;
        p.last_strike = Some(now);
        if p.strikes < most {
            return false;
        }
        let key = ban_key(addr);
        if self.banned.len() >= BANS_EACH * self.cfg.max && !self.banned.contains_key(&key) {
            // No room: the oldest ban is let go.
            let oldest = *self.banned.iter().min_by_key(|(_, since)| **since).expect("it is full").0;
            self.banned.remove(&oldest);
        }
        self.banned.insert(key, now);
        // Every peer of the host goes with it (on this machine, the one).
        let bits = if addr.ip().is_loopback() { None } else { Some(32) };
        let out: Vec<SocketAddrV4> = match bits {
            Some(bits) => self.of(addr, bits).filter(|p| !p.seed).map(|p| p.addr).collect(),
            None => vec![*addr],
        };
        for a in out {
            self.remove(&a);
        }
        true
    }

    /// Drops the peers silent too long: since they were last heard from
    /// or, never having answered, since they were first pinged. Seeds
    /// stay. `dropped` is called with each that never answered at all.
    pub fn prune(&mut self, now: Micros, mut dropped: impl FnMut(SocketAddrV4)) {
        let (silence, ban) = (self.cfg.drop_silence, self.cfg.ban);
        self.banned.retain(|_, since| now.saturating_sub(*since) < ban);
        let mut unproven = self.unproven;
        let totals = Arc::clone(&self.totals);
        self.peers.retain(|_, p| {
            if p.seed {
                return true;
            }
            let keep = match (p.last_seen, p.first_ping) {
                (Some(seen), _) => now.saturating_sub(seen) < silence,
                (None, Some(pinged)) => {
                    let keep = now.saturating_sub(pinged) < silence;
                    if !keep {
                        dropped(p.addr);
                    }
                    keep
                }
                (None, None) => true,
            };
            if !keep && !p.proven {
                unproven -= 1;
            }
            if !keep {
                totals.peers.fetch_sub(1, Ordering::Relaxed);
                totals.of_network(&p.addr).fetch_sub(1, Ordering::Relaxed);
            }
            keep
        });
        self.unproven = unproven;
    }

    /// The peers that are proven and were heard from lately: the only
    /// ones told things, asked things, or believed.
    pub fn live(&self, now: Micros) -> impl Iterator<Item = &Peer> {
        let silence = self.cfg.live_silence;
        self.peers.values().filter(move |p| p.proven && p.last_seen.is_some_and(|t| now.saturating_sub(t) < silence))
    }

    /// Whether more peers are to be looked for.
    pub fn wants_more(&self, now: Micros) -> bool {
        self.live(now).count() < self.cfg.target
    }

    /// Live peers other than `except`, picked at random: as many as fit
    /// one message. What a node answers "whom else do you know?" with.
    pub fn sample(&mut self, except: Option<SocketAddrV4>, now: Micros) -> Addrs {
        // (Never an address of the machine itself: it is this
        // machine's to whoever is told it, wherever they are.)
        let tellable = |a: &SocketAddrV4| Some(*a) != except && !a.ip().is_loopback();
        let mut all: Vec<SocketAddrV4> = self.live(now).map(|p| p.addr).filter(tellable).collect();
        let mut out = Addrs::new();
        // A random few, not the table's first.
        for i in 0..all.len() {
            let j = i + (self.next_random() % (all.len() - i) as u64) as usize;
            all.swap(i, j);
            if !out.push(all[i]) {
                break;
            }
        }
        out
    }

    fn next_random(&mut self) -> u64 {
        let mut x = self.random;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.random = x;
        x
    }

    fn passed_over(&self, p: &Peer, now: Micros) -> bool {
        p.failed.is_some_and(|t| now.saturating_sub(t) < self.pass_over)
    }

    /// A fetch from `addr` failed, or it did not back the work it
    /// claims: passed over for [`config::Sync::pass_over`].
    pub fn failed(&mut self, addr: &SocketAddrV4, now: Micros) {
        if let Some(p) = self.get_mut(addr) {
            p.failed = Some(now);
        }
    }

    /// `addr` delivered an object whole and right, over this path.
    pub fn delivered(&mut self, addr: &SocketAddrV4, path: Path) {
        if let Some(p) = self.get_mut(addr) {
            p.delivered = p.delivered.saturating_add(1);
            p.path = path;
        }
    }

    /// What a fetch learned of the path to `addr`, whether or not it
    /// delivered.
    pub fn set_path(&mut self, addr: &SocketAddrV4, path: Path) {
        if let Some(p) = self.get_mut(addr) {
            p.path = path;
        }
    }

    /// The live peers that claim more work than `work`, but for those
    /// passed over.
    pub fn claimants(&self, work: U256, now: Micros) -> impl Iterator<Item = &Peer> {
        self.live(now).filter(move |p| !self.passed_over(p, now) && p.status.is_some_and(|s| s.work > work))
    }

    /// The peer to ask for headers, among those claiming more than
    /// `work`: one that holds the body at `next` (the first height we
    /// lack) before one that does not, then the one claiming most.
    pub fn best_source(&self, work: U256, next: u32, now: Micros) -> Option<&Peer> {
        self.claimants(work, now).max_by_key(|p| {
            let s = p.status.expect("a claimant has a status");
            (s.oldest <= next, s.work)
        })
    }

    /// The live peers, not passed over, whose chain reaches `height`
    /// with every body from there up: whom to ask for that block.
    pub fn holders(&self, height: u32, now: Micros) -> impl Iterator<Item = &Peer> {
        self.live(now).filter(move |p| {
            !self.passed_over(p, now) && p.status.is_some_and(|s| s.oldest <= height && height <= s.height)
        })
    }

    /// The live peers whose chain holds the body at `height` and that
    /// are passed over, each for longer than `rested`: whom to ask
    /// when nobody else has it. A peer is passed over so that another
    /// is asked in its place; where there is no other, not asking it
    /// is not asking anyone, and a node with one peer that was slow
    /// once would stand still for as long as a peer is passed over.
    pub fn holders_rested(&self, height: u32, now: Micros, rested: Micros) -> impl Iterator<Item = &Peer> {
        self.live(now).filter(move |p| {
            p.failed.is_some_and(|t| self.passed_over(p, now) && now.saturating_sub(t) >= rested)
                && p.status.is_some_and(|s| s.oldest <= height && height <= s.height)
        })
    }

    /// The live peers, not passed over, whose chain reaches `height`:
    /// whom to ask for a header there.
    pub fn reaching(&self, height: u32, now: Micros) -> impl Iterator<Item = &Peer> {
        self.live(now).filter(move |p| !self.passed_over(p, now) && p.status.is_some_and(|s| height <= s.height))
    }

    /// The live peers, not passed over, that can hand over the state as
    /// of `height` in parts, and the block of that height with it.
    pub fn servers_of_state(&self, height: u32, now: Micros) -> impl Iterator<Item = &Peer> {
        self.live(now).filter(move |p| {
            !self.passed_over(p, now)
                && p.status.is_some_and(|s| s.window <= height && s.oldest <= height && height <= s.height)
        })
    }

    /// The lowest height any live peer can hand the state over as of.
    pub fn state_reach(&self, now: Micros) -> Option<u32> {
        self.live(now)
            .filter(|p| !self.passed_over(p, now))
            .filter_map(|p| p.status)
            .map(|s| s.window.max(s.oldest))
            .filter(|reach| *reach <= self.live(now).filter_map(|p| p.status).map(|s| s.height).max().unwrap_or(0))
            .min()
    }

    /// The live peers that are not passed over: whom anything may be
    /// asked of.
    pub fn able(&self, now: Micros) -> impl Iterator<Item = &Peer> {
        self.live(now).filter(move |p| !self.passed_over(p, now))
    }

    /// Whether `addr` may be asked for something: live, and not passed
    /// over.
    pub fn may_ask(&self, addr: &SocketAddrV4, now: Micros) -> bool {
        self.live(now).any(|p| p.addr == *addr && !self.passed_over(p, now))
    }

    /// `addr` was asked for headers we lack: it has
    /// [`config::Sync::header_wait`] to send one, from the first time
    /// it was asked.
    pub fn asked_headers(&mut self, addr: &SocketAddrV4, now: Micros) {
        if let Some(p) = self.get_mut(addr) {
            p.headers_asked.get_or_insert(now);
        }
    }

    /// `addr` sent a header we lacked.
    pub fn headers_arrived(&mut self, addr: &SocketAddrV4) {
        if let Some(p) = self.get_mut(addr) {
            p.headers_asked = None;
        }
    }

    /// The peers asked for headers too long ago that have sent none we
    /// lacked and still claim more than `ours`: `doubted` is called
    /// with each, and each is passed over. One whose claim we have
    /// since reached, from it or from another, is not to blame.
    pub fn doubt_silent_claimants(&mut self, ours: U256, now: Micros, mut doubted: impl FnMut(SocketAddrV4)) {
        let wait = self.header_wait;
        for p in self.peers.values_mut() {
            if p.headers_asked.is_some_and(|t| now.saturating_sub(t) >= wait) {
                p.headers_asked = None;
                if p.status.is_some_and(|s| s.work > ours) {
                    p.failed = Some(now);
                    doubted(p.addr);
                }
            }
        }
    }

    /// The addresses worth keeping for the next start: of peers that
    /// have ever answered.
    pub fn worth_saving(&self) -> impl Iterator<Item = SocketAddrV4> + '_ {
        self.peers.values().filter(|p| p.last_seen.is_some()).map(|p| p.addr)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::transport::{MILLI, SECOND};

    const T0: Micros = 1_000_000 * SECOND;

    fn addr(a: u8, b: u8, c: u8, d: u8, port: u16) -> SocketAddrV4 {
        SocketAddrV4::new(Ipv4Addr::new(a, b, c, d), port)
    }

    /// An address of a host and network of its own.
    fn nth(n: u16) -> SocketAddrV4 {
        addr(1 + (n / 250) as u8, (n % 250) as u8, 0, 1, 4000)
    }

    fn table() -> Peers {
        Peers::new(&config::Config::default(), 7)
    }

    fn status(nonce: u64, work: u64) -> Status {
        Status {
            nonce,
            version: 1,
            token: nonce ^ 0xff,
            genesis: [0; 32],
            height: 100,
            oldest: 0,
            window: 90,
            tip: [0; 32],
            work: U256::from_u64(work),
            // (Each its own node.)
            node: nonce,
        }
    }

    /// Pings whoever is due and answers for each, as a peer claiming
    /// `work` would.
    fn prove_all(t: &mut Peers, now: Micros, work: u64) {
        let mut due = Vec::new();
        let mut n = now;
        t.pings_due(
            now,
            || {
                n += 1;
                n
            },
            |a, number| due.push((a, number)),
        );
        for (a, number) in due {
            assert!(t.pong(&a, status(number, work), now));
        }
    }

    #[test]
    fn an_address_is_a_peer_once_it_answers_our_ping() {
        let mut t = table();
        let a = nth(1);
        assert_eq!(t.add(a, false, T0), Ok(true));
        assert_eq!(t.add(a, false, T0), Ok(false));
        assert!(!t.proven(&a) && t.live(T0).count() == 0);
        let mut pinged = Vec::new();
        t.pings_due(T0, || 77, |a, n| pinged.push((a, n)));
        assert_eq!(pinged, [(a, 77)]);
        // A pong with another number, or from another address, proves
        // nothing.
        assert!(!t.pong(&a, status(78, 5), T0 + 1));
        assert!(!t.pong(&nth(2), status(77, 5), T0 + 1));
        assert!(!t.proven(&a));
        // Its own does, and the round trip is the path's first measure.
        assert!(t.pong(&a, status(77, 5), T0 + 30 * MILLI));
        assert!(t.proven(&a));
        assert_eq!(t.live(T0 + SECOND).map(|p| p.addr).collect::<Vec<_>>(), [a]);
        let p = t.get(&a).unwrap();
        assert_eq!((p.token(), p.path.round_trip()), (Some(77 ^ 0xff), Some(30 * MILLI)));
        // The same pong again answers nothing.
        assert!(!t.pong(&a, status(77, 5), T0 + 40 * MILLI));
    }

    #[test]
    fn pings_go_at_the_interval_and_sooner_to_one_not_yet_answering() {
        let mut t = table();
        let a = nth(1);
        t.add(a, false, T0).unwrap();
        let mut number = 0;
        let mut sent: Vec<(Micros, u64)> = Vec::new();
        // A second at a time for two minutes, never answered.
        for s in 0..120 {
            let now = T0 + s * SECOND;
            t.pings_due(
                now,
                || {
                    number += 1;
                    number
                },
                |_, n| sent.push((s, n)),
            );
        }
        // At once, then after 2 s, 4, 8, 16, and every 30 from there;
        // the same number each time.
        let times: Vec<Micros> = sent.iter().map(|x| x.0).collect();
        assert_eq!(times, [0, 2, 6, 14, 30, 60, 90]);
        assert!(sent.iter().all(|x| x.1 == 1));
        // A ping sent more than once measures nothing when answered.
        assert!(t.pong(&a, status(1, 5), T0 + 120 * SECOND));
        assert_eq!(t.get(&a).unwrap().path.round_trip(), None);
        // Proven: every thirty seconds, a new number each time.
        sent.clear();
        for s in 120..240 {
            let now = T0 + s * SECOND;
            let mut due = Vec::new();
            t.pings_due(
                now,
                || {
                    number += 1;
                    number
                },
                |_, n| due.push(n),
            );
            for n in due {
                sent.push((s, n));
                assert!(t.pong(&a, status(n, 5), now + MILLI));
            }
        }
        assert_eq!(sent, [(120, 2), (150, 3), (180, 4), (210, 5)]);
        assert_eq!(t.get(&a).unwrap().path.round_trip(), Some(MILLI));
    }

    #[test]
    fn few_unproven_addresses_are_pinged_at_a_time() {
        let mut t = table();
        for n in 0..40 {
            t.add(nth(n), false, T0).unwrap();
        }
        let seed = addr(9, 9, 9, 9, 1);
        t.add(seed, true, T0).unwrap();
        let mut pinged = Vec::new();
        t.pings_due(T0, || 1, |a, _| pinged.push(a));
        // Eight of the forty, and the seed, which is our own choice.
        assert_eq!(pinged.len(), 9);
        assert!(pinged.contains(&seed));
        // The rest get their turn in later calls.
        let mut all = pinged.clone();
        for k in 1..5 {
            t.pings_due(T0 + k, || 1, |a, _| all.push(a));
        }
        all.sort();
        all.dedup();
        assert_eq!(all.len(), 41);
    }

    #[test]
    fn one_host_and_one_network_hold_only_so_many() {
        let mut t = table();
        // Four ports of one host; the fifth is refused.
        for port in 1..=4 {
            assert_eq!(t.add(addr(5, 5, 5, 5, port), false, T0), Ok(true));
        }
        assert_eq!(t.add(addr(5, 5, 5, 5, 5), false, T0), Err(Refused::Host));
        // Other hosts of its network, up to eight in all.
        for host in 6..=9 {
            assert_eq!(t.add(addr(5, 5, 0, host, 1), false, T0), Ok(true));
        }
        assert_eq!(t.add(addr(5, 5, 200, 1, 1), false, T0), Err(Refused::Network));
        // Another network is another matter.
        assert_eq!(t.add(addr(5, 6, 0, 1, 1), false, T0), Ok(true));
        // A seed is our own choice, whatever its host and network.
        assert_eq!(t.add(addr(5, 5, 5, 5, 99), true, T0), Ok(true));
        // This machine is not counted: many nodes run on it in tests.
        for port in 1..=20 {
            assert_eq!(t.add(addr(127, 0, 0, 1, port), false, T0), Ok(true));
        }
    }

    #[test]
    fn a_hosts_silent_peer_gives_way_to_its_new_port() {
        let mut t = table();
        for port in 1..=4 {
            t.add(addr(5, 5, 5, 5, port), false, T0).unwrap();
        }
        // None pinged yet: none gives way.
        assert_eq!(t.add(addr(5, 5, 5, 5, 5), false, T0 + 120 * SECOND), Err(Refused::Host));
        prove_all(&mut t, T0, 1);
        // Port 1 goes on answering; the others fall silent.
        t.seen(&addr(5, 5, 5, 5, 1), T0 + 50 * SECOND);
        assert_eq!(t.add(addr(5, 5, 5, 5, 5), false, T0 + 59 * SECOND), Err(Refused::Host));
        assert_eq!(t.add(addr(5, 5, 5, 5, 5), false, T0 + 61 * SECOND), Ok(true));
        assert!(t.get(&addr(5, 5, 5, 5, 1)).is_some() && t.len() == 4);
        // Its place in the network's count goes with it: a network at
        // its limit still takes the new port.
        let mut t = table();
        for port in 1..=4 {
            t.add(addr(5, 5, 5, 5, port), false, T0).unwrap();
        }
        for host in 6..=9 {
            t.add(addr(5, 5, 0, host, 1), false, T0).unwrap();
        }
        prove_all(&mut t, T0, 1);
        assert_eq!(t.add(addr(5, 5, 5, 5, 5), false, T0 + 61 * SECOND), Ok(true));
        assert_eq!(t.len(), 8);
    }

    #[test]
    fn a_full_table_gives_up_only_what_never_proved_itself() {
        let mut t = table();
        for n in 0..64 {
            t.add(nth(n), false, T0).unwrap();
        }
        // Full of addresses to try, none tried yet: no room for one
        // more. Once some have been asked and have not answered, a new
        // one takes the place of the one silent longest.
        assert_eq!(t.add(nth(100), false, T0), Err(Refused::Full));
        let mut pinged = Vec::new();
        t.pings_due(T0, || 1, |a, _| pinged.push(a));
        assert_eq!(t.add(nth(100), false, T0 + 1), Ok(true));
        assert_eq!(t.len(), 64);
        assert_eq!(pinged.iter().filter(|a| t.get(a).is_none()).count(), 1);
        // (The rest of those asked answer.)
        for a in &pinged {
            let _ = t.pong(a, status(1, 1), T0 + 1);
        }
        // All proven (eight a call, as unproven addresses are pinged).
        for k in 0..8 {
            prove_all(&mut t, T0 + k, 1);
        }
        assert_eq!(t.live(T0 + 10).count(), 64);
        assert_eq!(t.add(nth(200), false, T0 + 10), Err(Refused::Full));
        // Not even for a seed, which is added by hand before any of this.
        assert_eq!(t.add(nth(201), true, T0 + 10), Err(Refused::Full));
    }

    #[test]
    fn what_is_no_address_and_what_is_our_own_are_not_taken() {
        let mut t = table();
        for a in [addr(0, 0, 0, 0, 5), addr(1, 2, 3, 4, 0), addr(255, 255, 255, 255, 5), addr(224, 0, 0, 1, 5)] {
            assert_eq!(t.add(a, false, T0), Err(Refused::Unusable), "{a}");
        }
        // Our own ping come back: that address is us.
        let me = nth(1);
        t.add(me, false, T0).unwrap();
        t.pings_due(T0, || 55, |_, _| {});
        assert!(t.is_own_ping(&me, 55) && !t.is_own_ping(&me, 56) && !t.is_own_ping(&nth(2), 55));
        t.mark_self(me);
        assert_eq!(
            (t.len(), t.add(me, false, T0), t.add(me, true, T0)),
            (0, Err(Refused::Itself), Err(Refused::Itself))
        );
    }

    #[test]
    fn strikes_refuse_a_host_and_are_forgotten_in_time() {
        let mut t = table();
        let (a, b, other) = (addr(5, 5, 5, 5, 1), addr(5, 5, 5, 5, 2), nth(3));
        for x in [a, b, other] {
            t.add(x, false, T0).unwrap();
        }
        // Four strikes, and then nothing for ten minutes: forgotten.
        for k in 0..4 {
            assert!(!t.strike(&a, T0 + k));
        }
        assert!(!t.strike(&a, T0 + 601 * SECOND));
        // Five within the time: its host is out, every port of it, and
        // refused under any port.
        for k in 1..4 {
            assert!(!t.strike(&a, T0 + 601 * SECOND + k));
        }
        assert!(t.strike(&a, T0 + 602 * SECOND));
        assert!(t.get(&a).is_none() && t.get(&b).is_none() && t.get(&other).is_some());
        let later = T0 + 602 * SECOND;
        assert_eq!(t.add(addr(5, 5, 5, 5, 77), false, later + 3599 * SECOND), Err(Refused::Banned));
        assert_eq!(t.add(addr(5, 5, 5, 5, 77), false, later + 3600 * SECOND), Ok(true));
        // A seed takes none; nor does an address not in the table.
        let seed = nth(9);
        t.add(seed, true, T0).unwrap();
        for k in 0..20 {
            assert!(!t.strike(&seed, T0 + k) && !t.strike(&nth(10), T0 + k));
        }
        assert!(t.get(&seed).is_some());
        // On this machine a ban is of the one port.
        let (l1, l2) = (addr(127, 0, 0, 1, 1), addr(127, 0, 0, 1, 2));
        t.add(l1, false, T0).unwrap();
        t.add(l2, false, T0).unwrap();
        for k in 0..5 {
            t.strike(&l1, T0 + k);
        }
        assert!(t.get(&l1).is_none() && t.get(&l2).is_some());
    }

    #[test]
    fn the_silent_are_not_live_and_then_are_dropped() {
        let mut t = table();
        let (a, never, seed, untried) = (nth(1), nth(2), nth(3), nth(4));
        t.add(a, false, T0).unwrap();
        t.add(seed, true, T0).unwrap();
        prove_all(&mut t, T0, 1);
        t.add(never, false, T0).unwrap();
        t.pings_due(T0, || 9, |_, _| {});
        // One never pinged is no trouble to keep.
        t.add(untried, false, T0).unwrap();
        // Live for sixty-five seconds of silence, and no longer.
        assert_eq!(t.live(T0 + 64 * SECOND).count(), 2);
        assert_eq!(t.live(T0 + 65 * SECOND).count(), 0);
        // Kept for three minutes of it.
        let mut dropped = Vec::new();
        t.prune(T0 + 179 * SECOND, |a| dropped.push(a));
        assert_eq!((t.len(), dropped.len()), (4, 0));
        t.prune(T0 + 180 * SECOND, |a| dropped.push(a));
        // The one that answered once goes quietly; the one that never
        // did is named; the seed and the untried stay.
        assert_eq!(dropped, [never]);
        assert!(t.get(&a).is_none() && t.get(&seed).is_some() && t.get(&untried).is_some());
        // Heard from again, a peer is live again.
        t.seen(&seed, T0 + 500 * SECOND);
        assert_eq!(t.live(T0 + 501 * SECOND).count(), 1);
    }

    #[test]
    fn a_peer_that_says_it_is_going_is_asked_nothing_until_it_is_back() {
        let mut t = table();
        let a = nth(1);
        t.add(a, false, T0).unwrap();
        prove_all(&mut t, T0, 1);
        t.gone(&a);
        assert!(t.get(&a).is_some() && !t.proven(&a) && t.live(T0 + 1).count() == 0);
        assert_eq!(t.get(&a).unwrap().token(), None);
        // Back: it answers a ping, and is live.
        prove_all(&mut t, T0 + 31 * SECOND, 1);
        assert_eq!(t.live(T0 + 32 * SECOND).count(), 1);
    }

    #[test]
    fn a_sample_is_of_live_peers_and_differs_from_call_to_call() {
        let mut t = table();
        for n in 0..50 {
            t.add(nth(n), false, T0).unwrap();
        }
        for k in 0..7 {
            prove_all(&mut t, T0 + k, 1);
        }
        t.add(nth(60), false, T0).unwrap();
        let asker = nth(0);
        let first = t.sample(Some(asker), T0 + 10);
        let second = t.sample(Some(asker), T0 + 10);
        for s in [&first, &second] {
            assert_eq!(s.as_slice().len(), 32);
            assert!(!s.as_slice().contains(&asker) && !s.as_slice().contains(&nth(60)));
            let mut unique = s.as_slice().to_vec();
            unique.sort();
            unique.dedup();
            assert_eq!(unique.len(), 32);
        }
        assert_ne!(first, second);
        // Every live peer turns up over enough calls.
        let mut seen = std::collections::BTreeSet::new();
        for _ in 0..50 {
            seen.extend(t.sample(None, T0 + 10).as_slice().iter().copied());
        }
        assert_eq!(seen.len(), 50);
        // None live: none told of.
        assert!(t.sample(None, T0 + 1000 * SECOND).as_slice().is_empty());
        assert!(t.wants_more(T0 + 1000 * SECOND) && !t.wants_more(T0 + 10));
    }

    #[test]
    fn whom_to_ask_for_headers_and_for_blocks() {
        let mut t = table();
        let (most, holds, behind, unproven) = (nth(1), nth(2), nth(3), nth(4));
        for a in [most, holds, behind] {
            t.add(a, false, T0).unwrap();
        }
        let mut n = 0;
        let mut due = Vec::new();
        t.pings_due(
            T0,
            || {
                n += 1;
                n
            },
            |a, number| due.push((a, number)),
        );
        for (a, number) in due {
            // `most` claims most work but holds bodies only from 50 up;
            // `holds` claims less and holds everything; `behind` claims
            // less than we have.
            let s = match a {
                x if x == most => Status { work: U256::from_u64(900), oldest: 50, ..status(number, 0) },
                x if x == holds => Status { work: U256::from_u64(800), ..status(number, 0) },
                _ => Status { work: U256::from_u64(10), height: 20, window: 15, ..status(number, 0) },
            };
            assert!(t.pong(&a, s, T0));
        }
        // An address that claims the earth and has proven nothing.
        t.add(unproven, false, T0).unwrap();
        t.set_status(&unproven, status(0, u64::MAX));
        let now = T0 + SECOND;
        let ours = U256::from_u64(100);
        let claim: Vec<_> = t.claimants(ours, now).map(|p| p.addr).collect();
        assert!(claim.len() == 2 && claim.contains(&most) && claim.contains(&holds));
        // The one that holds the next body, though another claims more.
        assert_eq!(t.best_source(ours, 10, now).unwrap().addr, holds);
        assert_eq!(t.best_source(ours, 60, now).unwrap().addr, most);
        assert_eq!(t.best_source(U256::from_u64(900), 60, now).map(|p| p.addr), None);
        // Who holds which block, and who can hand over which state.
        let at = |h| t.holders(h, now).map(|p| p.addr).collect::<Vec<_>>();
        assert_eq!(at(101), []);
        assert_eq!(at(10).len(), 2);
        assert_eq!(at(40), [holds]);
        assert_eq!(t.servers_of_state(17, now).map(|p| p.addr).collect::<Vec<_>>(), [behind]);
        assert_eq!(t.servers_of_state(95, now).count(), 2);
        // One that can go back to a block's state, and no longer holds
        // the block, is not asked for the two.
        assert_eq!(t.servers_of_state(16, now).count(), 1);
        assert_eq!(t.state_reach(now), Some(15));
        // One that failed us is passed over for ten minutes.
        t.failed(&holds, now);
        assert_eq!(t.best_source(ours, 10, now).unwrap().addr, most);
        t.seen(&holds, now + 599 * SECOND);
        assert!(t.live(now + 599 * SECOND).any(|p| p.addr == holds) && !t.may_ask(&holds, now + 599 * SECOND));
        t.seen(&holds, now + 600 * SECOND);
        assert!(t.may_ask(&holds, now + 600 * SECOND) && !t.may_ask(&unproven, now));
    }

    #[test]
    fn a_claim_not_backed_by_headers_is_doubted() {
        let mut t = table();
        let (a, b) = (nth(1), nth(2));
        t.add(a, false, T0).unwrap();
        t.add(b, false, T0).unwrap();
        prove_all(&mut t, T0, 500);
        let ours = U256::from_u64(100);
        t.asked_headers(&a, T0);
        t.asked_headers(&b, T0);
        // Asked again: the wait is from the first time.
        t.asked_headers(&a, T0 + 10 * SECOND);
        t.headers_arrived(&b);
        let mut doubted = Vec::new();
        t.doubt_silent_claimants(ours, T0 + 14 * SECOND, |x| doubted.push(x));
        assert!(doubted.is_empty());
        t.doubt_silent_claimants(ours, T0 + 15 * SECOND, |x| doubted.push(x));
        assert_eq!(doubted, [a]);
        assert_eq!(t.claimants(ours, T0 + 16 * SECOND).map(|p| p.addr).collect::<Vec<_>>(), [b]);
        // One whose claim we have reached meanwhile is not to blame.
        t.asked_headers(&b, T0 + 20 * SECOND);
        t.doubt_silent_claimants(U256::from_u64(500), T0 + 40 * SECOND, |x| doubted.push(x));
        assert_eq!(doubted, [a]);
    }

    /// A table of thousands, as a node many lean on keeps: everything
    /// done to it at random, and its bounds and its count of the
    /// unproven hold throughout.
    #[test]
    fn a_large_table_keeps_its_bounds_through_anything() {
        use crate::test_util::Rng;
        let mut cfg = config::Config::default();
        (cfg.peers.max, cfg.peers.target, cfg.peers.unproven_pings) = (3000, 100, 500);
        assert_eq!(cfg.check(), Ok(()));
        let mut t = Peers::new(&cfg, 3);
        let mut rng = Rng::new(0x9ee5);
        // Addresses crowded into few hosts and networks, so that every
        // bound is met.
        let pick = |rng: &mut Rng| {
            let r = rng.next_u64();
            addr(
                10 + (r % 3) as u8,
                (r >> 8) as u8 % 120,
                (r >> 16) as u8 % 4,
                (r >> 24) as u8 % 6,
                1 + (r >> 32) as u16 % 8,
            )
        };
        let mut now = T0;
        let mut number = 0u64;
        for round in 0..400 {
            now += rng.next_u64() % (3 * SECOND);
            for _ in 0..40 {
                let a = pick(&mut rng);
                match rng.next_u64() % 10 {
                    0..=4 => {
                        let _ = t.add(a, rng.next_u64().is_multiple_of(50), now);
                    }
                    5 => t.gone(&a),
                    6 => {
                        t.strike(&a, now);
                    }
                    7 => t.seen(&a, now),
                    8 => t.mark_self(a),
                    _ => t.failed(&a, now),
                }
            }
            // Pings, most of them answered.
            let mut due = Vec::new();
            t.pings_due(
                now,
                || {
                    number += 1;
                    number
                },
                |a, n| due.push((a, n)),
            );
            for (a, n) in due {
                if !rng.next_u64().is_multiple_of(4) {
                    assert!(t.pong(&a, status(n, 5), now));
                }
            }
            if round % 7 == 0 {
                t.prune(now, |_| {});
            }
            // The bounds.
            assert!(t.len() <= 3000);
            assert_eq!(t.unproven, t.all().filter(|p| !p.proven && !p.seed).count(), "round {round}");
            let mut hosts = BTreeMap::new();
            let mut networks = BTreeMap::new();
            for p in t.all().filter(|p| !p.seed) {
                *hosts.entry(*p.addr.ip()).or_insert(0) += 1;
                *networks.entry(u32::from(*p.addr.ip()) >> 16).or_insert(0) += 1;
            }
            assert!(hosts.values().all(|n| *n <= 4) && networks.values().all(|n| *n <= 8), "round {round}");
            assert!(t.sample(None, now).as_slice().len() <= 32);
        }
        assert!(t.len() > 500, "{}", t.len());
    }

    #[test]
    fn what_is_saved_is_who_has_answered() {
        let mut t = table();
        t.add(nth(1), false, T0).unwrap();
        prove_all(&mut t, T0, 1);
        t.add(nth(2), false, T0).unwrap();
        assert_eq!(t.worth_saving().collect::<Vec<_>>(), [nth(1)]);
        // What a fetch learned of a path is kept with the peer.
        let mut path = Path::new();
        path.grow();
        t.delivered(&nth(1), path);
        assert_eq!((t.get(&nth(1)).unwrap().delivered, t.get(&nth(1)).unwrap().path.window()), (1, path.window()));
    }
}
