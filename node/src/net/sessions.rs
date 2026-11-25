//! Who is to be reached where: the sessions a node holds for wallets,
//! and the sessions a wallet keeps at nodes.
//!
//! A wallet that is to be reached says so to the nodes it is reached at
//! ([`crate::msg::points`]), now and then, for as long as it is to be:
//! "I am the wallet of this id, and what I last announced has this
//! number" ([`crate::net::message::Message::Session`]). A node that
//! holds sessions ([`Sessions`]) asks for the announcement if it has
//! not got it, checks it, and from then on knows where that wallet is:
//! what is offered for it is passed on there, and whoever asks is
//! given its announcement. A wallet that stops saying so is forgotten.
//! Nothing is kept for a wallet that is not there.
//!
//! A node holds only so many sessions, and only so many of one host:
//! ids cost nothing to make, and room for them is not given away to
//! whoever asks for most.

use std::collections::BTreeMap;
use std::net::SocketAddrV4;
use std::sync::Arc;

use crate::hash::Digest;
use crate::hash::digest_to_bytes;
use crate::msg::{self, Announced};
use crate::transport::{Micros, SECOND};
use crate::{mldsa, mlkem};

/// How a node that holds sessions is bounded.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Limits {
    /// Sessions held in all.
    pub most: usize,
    /// Sessions of one host.
    pub each_host: usize,
    /// How long a wallet may say nothing before it is forgotten.
    pub idle: Micros,
}

impl Default for Limits {
    fn default() -> Limits {
        Limits { most: 10_000, each_host: 16, idle: 90 * SECOND }
    }
}

/// How many wallets are held at the end of one way.
const EACH_WAY: usize = 2;

/// Where a wallet a session is held for is: at an address, which it
/// says so from; or at the far end of a way through relays that ends
/// at this node, known by who is before this node on it
/// ([`super::circuits`]), and then this node does not know where.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Where {
    Addr(SocketAddrV4),
    Way(SocketAddrV4, u64),
}

impl From<SocketAddrV4> for Where {
    fn from(addr: SocketAddrV4) -> Where {
        Where::Addr(addr)
    }
}

/// A wallet a node holds a session for.
#[derive(Clone, Debug)]
pub struct Session {
    pub at: Where,
    pub seq: u64,
    /// What it announced, as it said it.
    pub announce: Arc<Vec<u8>>,
    /// When it last said it was there.
    pub seen: Micros,
}

/// Why an announcement was not taken.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Refused {
    /// Not an announcement, not signed by its key, or past its time.
    Unsound,
    /// Not made for this node to take from that address.
    NotBound,
    /// Older than the one held.
    Stale,
    /// No room: of that host, or at all.
    Full,
}

/// The sessions a node holds.
pub struct Sessions {
    limits: Limits,
    held: BTreeMap<[u8; 32], Session>,
    /// The full names wallets held here are reached by
    /// ([`crate::subnames`]), by the id each is reached at.
    aliases: BTreeMap<[u8; 32], Alias>,
}

/// A full name a wallet that is held here is reached by: for as long
/// as the wallet is, and its certificate holds.
#[derive(Clone, Debug)]
pub struct Alias {
    pub holder: Digest,
    pub seq: u64,
    pub expires: u64,
    /// The certificate, with what goes with it, as it was shown.
    pub bundle: Arc<Vec<u8>>,
}

/// Full names one wallet may be reached by at one node.
pub const ALIASES_EACH: usize = 16;

impl Sessions {
    pub fn new(limits: Limits) -> Sessions {
        Sessions { limits, held: BTreeMap::new(), aliases: BTreeMap::new() }
    }

    pub fn len(&self) -> usize {
        self.held.len()
    }

    pub fn is_empty(&self) -> bool {
        self.held.is_empty()
    }

    /// The wallet of id `id` says, from `addr`, that it is there and
    /// what it last announced has the number `seq`. True if that is the
    /// announcement held, from that address: the session goes on. If
    /// not, the announcement is to be asked for.
    pub fn seen(&mut self, id: &Digest, at: impl Into<Where>, seq: u64, now: Micros) -> bool {
        let at = at.into();
        match self.held.get_mut(&digest_to_bytes(id)) {
            Some(session) if session.at == at && session.seq == seq => {
                session.seen = now;
                true
            }
            _ => false,
        }
    }

    /// Takes an announcement that came from `addr`: at `unix` by the
    /// calendar, `now` by the clock. `bound` says whether a token is
    /// this node's for that address. The id of the wallet whose session
    /// it opens, or goes on with.
    pub fn admit(
        &mut self,
        announce: Vec<u8>,
        at: impl Into<Where>,
        bound: impl FnOnce(u64) -> bool,
        unix: u64,
        now: Micros,
    ) -> Result<Digest, Refused> {
        let at = at.into();
        let said = Announced::read(&announce, unix).ok_or(Refused::Unsound)?;
        if !bound(said.bind()) {
            return Err(Refused::NotBound);
        }
        let (id, seq) = (said.id(), said.seq());
        let key = digest_to_bytes(&id);
        self.prune(now);
        match self.held.get(&key) {
            Some(held) if held.seq >= seq => return Err(Refused::Stale),
            Some(_) => {}
            None => {
                // (Of one host: of those that say so from an address.
                // Who is at the end of a way is of no host this node
                // knows, and the ways are bounded where they are made.)
                let host = |at: &Where| match at {
                    Where::Addr(addr) => Some(*addr.ip()),
                    Where::Way(..) => None,
                };
                // (And of one way: a wallet or two, as of one address a
                // few. One way could else say it was every wallet the
                // node has room for.)
                let of_host = match host(&at) {
                    Some(ip) => self.held.values().filter(|s| host(&s.at) == Some(ip)).count(),
                    None => {
                        self.held.values().filter(|s| s.at == at).count() * (self.limits.each_host / EACH_WAY).max(1)
                    }
                };
                if self.held.len() >= self.limits.most || of_host >= self.limits.each_host {
                    return Err(Refused::Full);
                }
            }
        }
        self.held.insert(key, Session { at, seq, announce: Arc::new(announce), seen: now });
        Ok(id)
    }

    /// The session held for the wallet of id `id`, if it has said it
    /// was there lately enough.
    pub fn get(&self, id: &Digest, now: Micros) -> Option<&Session> {
        self.held.get(&digest_to_bytes(id)).filter(|s| now.saturating_sub(s.seen) < self.limits.idle)
    }

    /// Forgets the wallets that have said nothing for too long, and
    /// the names they were reached by.
    pub fn prune(&mut self, now: Micros) {
        let idle = self.limits.idle;
        self.held.retain(|_, s| now.saturating_sub(s.seen) < idle);
        let held = &self.held;
        self.aliases.retain(|_, a| held.contains_key(&digest_to_bytes(&a.holder)));
    }

    /// A wallet held here, at `at`, shows that it is a full name: a
    /// certificate that was read, and found to be the name's by
    /// whoever reads the chain. Taken if the wallet is the one it
    /// names and no newer certificate says the name is another's: the
    /// certificate's number; and where the wallet is that was reached
    /// by the name until now, if it is another, which is to be told.
    pub fn alias(
        &mut self,
        checked: &crate::subnames::Checked,
        bundle: Vec<u8>,
        at: impl Into<Where>,
        now: Micros,
    ) -> Result<(u64, Option<Where>), Refused> {
        let at = at.into();
        self.prune(now);
        if !self.get(&checked.holder, now).is_some_and(|s| s.at == at) {
            return Err(Refused::NotBound);
        }
        let key = digest_to_bytes(&checked.point());
        let before = self.aliases.get(&key).filter(|held| held.holder != checked.holder);
        let before = before.and_then(|held| self.get(&held.holder, now)).map(|session| session.at);
        match self.aliases.get(&key) {
            Some(held) if held.seq > checked.seq || (held.seq == checked.seq && held.holder != checked.holder) => {
                return Err(Refused::Stale);
            }
            Some(_) => {}
            None => {
                let of_it = self.aliases.values().filter(|a| a.holder == checked.holder).count();
                if of_it >= ALIASES_EACH || self.aliases.len() >= 4 * self.limits.most {
                    return Err(Refused::Full);
                }
            }
        }
        let (holder, seq, expires) = (checked.holder, checked.seq, checked.expires);
        self.aliases.insert(key, Alias { holder, seq, expires, bundle: Arc::new(bundle) });
        Ok((seq, before))
    }

    /// The wallet that is reached by the full name of id `n`, and the
    /// certificate that says so: if the wallet is here, and the
    /// certificate holds at `unix`.
    pub fn aliased(&self, n: &Digest, unix: u64, now: Micros) -> Option<(&Session, &Alias)> {
        let alias = self.aliases.get(&digest_to_bytes(n)).filter(|a| a.expires > unix)?;
        Some((self.get(&alias.holder, now)?, alias))
    }

    /// What is announced under the id `id`, for whoever asks: what the
    /// wallet of that id announced; or, of the id of a full name, what
    /// the wallet it is announced, and after it the certificate.
    pub fn announced(&self, id: &Digest, unix: u64, now: Micros) -> Option<Vec<u8>> {
        if let Some(session) = self.get(id, now) {
            return Some(session.announce.to_vec());
        }
        let (session, alias) = self.aliased(id, unix, now)?;
        Some([&session.announce[..], &alias.bundle[..]].concat())
    }
}

/// How long a wallet's Kyber key is announced for before another is
/// made, and how long the one before it still opens what was sealed to
/// it.
const KEY_LIFE: Micros = 3600 * SECOND;
const KEY_GRACE: Micros = 600 * SECOND;
/// How long an announcement holds, in seconds: past a key's life, so
/// that what was sealed just before another was made is still answered.
const ANNOUNCE_HOLDS: u64 = 2 * 3600;
/// Between sayings to a node that does not yet hold the announcement.
const UNHELD_RETRY: Micros = 2 * SECOND;

/// A wallet's side: its keys, and what it has announced to each node it
/// is reached at.
pub struct Participant {
    identity: mldsa::SecretKey,
    id: Digest,
    kyber: mlkem::SecretKey,
    made: Micros,
    /// The key before, and until when it still opens.
    before: Option<(mlkem::SecretKey, Micros)>,
    /// To each node: the announcement made for it, the token it was
    /// bound to, its number, and the number that node last said it
    /// holds.
    said: BTreeMap<SocketAddrV4, Said>,
    /// The number of the last announcement made: the next is higher.
    last: u64,
    /// The full names this wallet is reached by.
    aliases: Vec<Aliased>,
    /// A node that holds, for this wallet, an announcement newer than
    /// any this node made for it: another node is saying it is this
    /// wallet ([`Participant::take_twin`]).
    twin: Option<SocketAddrV4>,
}

/// A full name this wallet is reached by: the id it is reached at, its
/// certificate, and what each node it is shown to has said of it.
struct Aliased {
    n: Digest,
    seq: u64,
    bundle: Arc<Vec<u8>>,
    /// To each node: the number it says it holds ([`ALIAS_ASKED`]
    /// before it has said, none if it would not), and when it was
    /// last shown.
    at: BTreeMap<SocketAddrV4, (u64, Micros)>,
}

const ALIAS_ASKED: u64 = u64::MAX;
/// How long before a node that would not take a certificate is shown
/// it again.
const ALIAS_REFUSED_RETRY: Micros = 60 * SECOND;

struct Said {
    /// The node's token for this wallet's node: none (zero) until the
    /// node has said it.
    bind: u64,
    seq: u64,
    announce: Arc<Vec<u8>>,
    held: u64,
    asked: Micros,
    /// How many times it has been said to since it last said anything
    /// back: a node that says nothing is not one the wallet is reached
    /// at, whatever it held.
    unanswered: u8,
}

/// How many sayings a node may leave unanswered before the wallet is
/// taken not to be reached there.
const UNANSWERED: u8 = 3;

impl Participant {
    /// The wallet whose Dilithium key is `identity`, at `now`. `chance`
    /// is 64 random bytes, for its first Kyber key.
    pub fn new(identity: mldsa::SecretKey, chance: &[u8; 64], now: Micros) -> Participant {
        let id = crate::address::id_of(identity.public_key());
        let kyber = mlkem::keygen(chance);
        Participant {
            identity,
            id,
            kyber,
            made: now,
            before: None,
            said: BTreeMap::new(),
            last: 0,
            aliases: Vec::new(),
            twin: None,
        }
    }

    pub fn id(&self) -> Digest {
        self.id
    }

    pub fn identity(&self) -> &mldsa::SecretKey {
        &self.identity
    }

    /// Makes another Kyber key if the one there is has been announced
    /// long enough: every announcement is then to be made again.
    /// `chance` is 64 random bytes.
    pub fn rotate(&mut self, chance: &[u8; 64], now: Micros) -> bool {
        if now.saturating_sub(self.made) < KEY_LIFE {
            return false;
        }
        let old = std::mem::replace(&mut self.kyber, mlkem::keygen(chance));
        self.before = Some((old, now + KEY_GRACE));
        self.made = now;
        self.said.clear();
        true
    }

    /// Whether it is time to say again to the node at `node` that this
    /// wallet is there: every `keepalive` while the node holds what was
    /// announced to it, and sooner until it does.
    pub fn due(&self, node: &SocketAddrV4, now: Micros, keepalive: Micros) -> bool {
        match self.said.get(node) {
            Some(said) if said.seq != 0 && said.held == said.seq && said.unanswered < UNANSWERED => {
                now.saturating_sub(said.asked) >= keepalive
            }
            Some(said) => now.saturating_sub(said.asked) >= UNHELD_RETRY,
            None => true,
        }
    }

    /// The token the node at `node` gave for this wallet's node: none
    /// (zero) before it has given one.
    pub fn token(&self, node: &SocketAddrV4) -> u64 {
        self.said.get(node).map_or(0, |s| s.bind)
    }

    /// The node at `node` is asked for its token, having given none
    /// yet: so that it is not asked again at once.
    pub fn greet(&mut self, node: SocketAddrV4, now: Micros) {
        let (announce, unanswered) = (Arc::new(Vec::new()), 0);
        let none = Said { bind: 0, seq: 0, announce, held: u64::MAX, asked: now, unanswered };
        self.said.entry(node).or_insert(none).asked = now;
    }

    /// What is to be said to the node at `node`, whose token for this
    /// wallet is `token`: the number of the announcement made for it,
    /// which is made now if there is none, or if the token is another
    /// than it was bound to. `unix` is the time by the calendar, in
    /// seconds: a number that only rises is made of it (so that it
    /// rises from one run of the node to the next, too).
    pub fn say(&mut self, node: SocketAddrV4, token: u64, unix: u64, now: Micros) -> u64 {
        let fresh = self.said.get(&node).is_none_or(|s| s.bind != token || s.seq == 0);
        if fresh {
            let stamp = (unix << 20).max(self.last + 1);
            self.last = stamp;
            let ek: [u8; mlkem::EK_LEN] = self.kyber.public_key().try_into().expect("a key's length");
            let announce = msg::announce(&self.identity, &ek, stamp, unix + ANNOUNCE_HOLDS, token);
            let announce = Arc::new(announce);
            let said = Said { bind: token, seq: stamp, announce, held: 0, asked: now, unanswered: 0 };
            self.said.insert(node, said);
            // (What the node held of the names the wallet is, it held
            // with the announcement before: shown again.)
            self.aliases.iter_mut().for_each(|a| {
                a.at.remove(&node);
            });
        }
        let said = self.said.get_mut(&node).expect("it was put there");
        said.asked = now;
        said.unanswered = said.unanswered.saturating_add(1);
        said.seq
    }

    /// The announcement of the number `seq`, for whoever asks: one made
    /// for some node, and still the one for it.
    pub fn announced(&self, seq: u64) -> Option<Arc<Vec<u8>>> {
        self.said.values().find(|s| s.seq == seq && seq != 0).map(|s| Arc::clone(&s.announce))
    }

    /// An announcement of this wallet's that holds now: what a message
    /// it sends carries, for the answer to be sealed to.
    pub fn announced_any(&self) -> Option<Arc<Vec<u8>>> {
        self.said.values().filter(|s| s.seq != 0).max_by_key(|s| s.seq).map(|s| Arc::clone(&s.announce))
    }

    /// The announcement made for the node at `node`, if one was.
    pub fn announced_to(&self, node: &SocketAddrV4) -> Option<Arc<Vec<u8>>> {
        self.said.get(node).filter(|s| s.seq != 0).map(|s| Arc::clone(&s.announce))
    }

    /// The node at `node` says it holds the announcement of number
    /// `seq` for this wallet, and that its token for this wallet's node
    /// is `token`. True if that token is another than it was known to
    /// have: it is then to be told again at once, with that one.
    pub fn held(&mut self, node: &SocketAddrV4, seq: u64, token: u64) -> bool {
        let Some(said) = self.said.get_mut(node) else { return false };
        said.unanswered = 0;
        // (It holds one newer than this node ever made for it: made by
        // another, with this wallet's key. One left from before this
        // node was last started is older, and is nothing.)
        if said.seq != 0 && seq > said.seq {
            self.twin = Some(*node);
        }
        // (A node that does not hold the announcement holds nothing of
        // the names the wallet is reached by either.)
        if seq != said.seq || said.seq == 0 {
            self.aliases.iter_mut().for_each(|a| {
                a.at.remove(node);
            });
        }
        // (Of an announcement made for another token it holds nothing
        // that counts.)
        said.held = if said.seq == 0 { u64::MAX } else { seq };
        let other = token != 0 && said.bind != token;
        if other {
            (said.bind, said.seq, said.held) = (token, 0, u64::MAX);
        }
        other
    }

    /// The full names this wallet is reached by are these: the id each
    /// is reached at, its certificate's number, and the certificate
    /// with what goes with it. (What a node has said of one that is
    /// unchanged stands.)
    pub fn set_aliases(&mut self, all: Vec<(Digest, u64, Vec<u8>)>) {
        let mut before = std::mem::take(&mut self.aliases);
        for (n, seq, bundle) in all {
            let was = before.iter().position(|a| a.n == n && a.seq == seq).map(|at| before.swap_remove(at));
            let at = was.map(|a| a.at).unwrap_or_default();
            self.aliases.push(Aliased { n, seq, bundle: Arc::new(bundle), at });
        }
    }

    /// The ids of the full names this wallet is reached by, and each
    /// certificate's number.
    pub fn aliases(&self) -> Vec<(Digest, u64)> {
        self.aliases.iter().map(|a| (a.n, a.seq)).collect()
    }

    /// The certificate of the full name of id `n`, with what goes with
    /// it.
    pub fn alias_bundle(&self, n: &Digest) -> Option<Arc<Vec<u8>>> {
        self.aliases.iter().find(|a| a.n == *n).map(|a| Arc::clone(&a.bundle))
    }

    /// Whether the certificate of the full name of id `n` is to be
    /// shown to the node at `node` now: a node that holds what the
    /// wallet announced, and has not said it holds the certificate.
    pub fn alias_due(&self, n: &Digest, node: &SocketAddrV4, now: Micros) -> bool {
        let Some(alias) = self.aliases.iter().find(|a| a.n == *n).filter(|_| self.is_held(node)) else { return false };
        match alias.at.get(node) {
            None => true,
            Some((held, _)) if *held == alias.seq => false,
            Some((0, shown)) => now.saturating_sub(*shown) >= ALIAS_REFUSED_RETRY,
            Some((_, shown)) => now.saturating_sub(*shown) >= UNHELD_RETRY,
        }
    }

    /// It is shown to that node now.
    pub fn alias_shown(&mut self, n: &Digest, node: SocketAddrV4, now: Micros) {
        if let Some(alias) = self.aliases.iter_mut().find(|a| a.n == *n) {
            alias.at.entry(node).or_insert((ALIAS_ASKED, now)).1 = now;
        }
    }

    /// The node at `node` says it holds the certificate of number
    /// `seq` for the full name of id `n`, or none (zero).
    pub fn alias_held(&mut self, n: &Digest, node: &SocketAddrV4, seq: u64) {
        if let Some(shown) = self.aliases.iter_mut().find(|a| a.n == *n).and_then(|a| a.at.get_mut(node)) {
            shown.0 = seq;
        }
    }

    /// At how many nodes the full name of id `n` is reached.
    pub fn alias_reached(&self, n: &Digest) -> usize {
        let alias = self.aliases.iter().find(|a| a.n == *n);
        alias.map_or(0, |a| a.at.iter().filter(|(node, held)| held.0 == a.seq && self.is_held(node)).count())
    }

    /// The wallet is not reached at the node at `node` any more, by
    /// what this node can tell: there is no way there that goes
    /// anywhere. (What was announced to it stands, to be said again.)
    pub fn unreached(&mut self, node: &SocketAddrV4) {
        if let Some(said) = self.said.get_mut(node) {
            said.held = 0;
            self.aliases.iter_mut().for_each(|a| {
                a.at.remove(node);
            });
        }
    }

    /// A node at which another node has announced this wallet since
    /// this one did, if one has since this was last asked: two copies
    /// of one wallet are running at once.
    pub fn take_twin(&mut self) -> Option<SocketAddrV4> {
        self.twin.take()
    }

    /// Whether the node at `node` holds what was last announced to it.
    pub fn is_held(&self, node: &SocketAddrV4) -> bool {
        self.said.get(node).is_some_and(|s| s.seq != 0 && s.held == s.seq && s.unanswered < UNANSWERED)
    }

    /// The nodes this wallet is reached at now: those that hold what it
    /// last announced to them.
    pub fn reached_at(&self) -> impl Iterator<Item = SocketAddrV4> + '_ {
        self.said.iter().filter(|(node, _)| self.is_held(node)).map(|(node, _)| *node)
    }

    /// The nodes it has said it is there to, whether or not they hold
    /// its announcement.
    pub fn said_to(&self) -> usize {
        self.said.len()
    }

    /// No longer says anything to the nodes that are not of `points`.
    pub fn keep(&mut self, points: &[SocketAddrV4]) {
        self.aliases.iter_mut().for_each(|a| a.at.retain(|node, _| points.contains(node)));
        self.said.retain(|node, _| points.contains(node));
    }

    /// Opens a message sealed to this wallet, at `unix` by the calendar
    /// and `now` by the clock: with the key it announces, or the one
    /// before while that still opens.
    pub fn open(&self, sealed: &[u8], now: Micros) -> Option<msg::Opened> {
        let before = self.before.as_ref().filter(|(_, until)| now < *until).map(|(key, _)| key);
        [Some(&self.kyber), before].into_iter().flatten().find_map(|key| msg::open(key, &self.id, sealed))
    }
}

/// How long a message is tried before it is given up, and how long
/// between tries.
pub const POST_HOLDS: Micros = 60 * SECOND;
pub const POST_RETRY: Micros = SECOND;
/// How long a node that passes a message on keeps it for the wallet it
/// is for to ask for, and how many bytes of such it keeps at the most.
const PASSING_HOLDS: Micros = 60 * SECOND;
const PASSING_BYTES: usize = 32 << 20;

/// What became of a message sent.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Posted {
    /// Still being tried.
    Waiting,
    /// Passed on to the wallet it is for, by a node it is reached at.
    Passed,
    /// That wallet is not there to take it.
    Offline,
    /// No node it is reached at took it, in the time there was.
    Unsent,
}

/// A message this node's wallet is sending.
pub struct Post {
    pub to: Digest,
    /// The id of the full name it was sent to, where it was sent to
    /// one ([`crate::subnames::point`]): the nodes that name is
    /// reached at are asked, and `to` is not known until one of them
    /// has shown whose the name is.
    pub via: Option<Digest>,
    pub kind: u8,
    pub body: Vec<u8>,
    /// What whoever posted it knows it by (a slate's id): given back
    /// with what became of it.
    pub tag: [u8; 32],
    /// What it answers, if it is the answer to a message that came
    /// for this wallet: it goes back by the node that message came by,
    /// to whoever sent it, of whom nothing else is known.
    pub answers: Option<Answering>,
    /// Sealed, once it is: its id and its bytes.
    pub sealed: Option<(Digest, Arc<Vec<u8>>)>,
    /// When it was first looked to: not known to whoever posted it.
    pub began: Option<Micros>,
    /// When it was last tried, and of which of the wallet's nodes next.
    pub tried: Option<Micros>,
    pub turn: usize,
    /// Of how many of the wallet's nodes it has been asked what the
    /// wallet announced, and they had nothing.
    pub missed: usize,
    pub state: Posted,
}

/// What an answer answers: the message's id, the key that message
/// carried for its answer, and the node it came by.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Answering {
    pub of: Digest,
    pub key: Vec<u8>,
    pub by: SocketAddrV4,
}

/// A message this wallet sent, while its answer may still come: its
/// id, the key its answer is sealed to, whom it was sent to (and whom
/// alone its answer is taken from), and when it was sealed.
pub struct Awaited {
    pub id: Digest,
    pub key: mlkem::SecretKey,
    pub to: Digest,
    pub since: Micros,
}

/// How long the answer to a message sent is waited for.
pub const ANSWER_HOLDS: Micros = 180 * SECOND;

/// The messages of a node: those its wallet sends, those it passes on
/// for others, and those that have come for its wallet.
#[derive(Default)]
pub struct Mail {
    pub posts: Vec<Post>,
    /// The messages sent whose answers may still come.
    pub awaited: Vec<Awaited>,
    /// Sealed messages being passed on: id, whom for, the bytes, when
    /// taken.
    passing: std::collections::VecDeque<(Digest, Digest, Arc<Vec<u8>>, Micros)>,
    /// What has come for this node's wallet, opened.
    pub inbox: Vec<msg::Opened>,
    /// The ids of the sealed messages that have come, so that one is
    /// taken once.
    seen: std::collections::VecDeque<Digest>,
    /// What became of the messages sent, for whoever sent them.
    pub posted: Vec<(Digest, u8, [u8; 32], Posted)>,
    /// Whose the full names messages were sent to turned out to be:
    /// what whoever posted each knows it by, and the wallet.
    pub resolved: Vec<([u8; 32], Digest)>,
}

impl Post {
    /// The id whose nodes are asked for the wallet it is for.
    pub fn asked(&self) -> Digest {
        self.via.unwrap_or(self.to)
    }
}

impl Mail {
    /// A message to send.
    pub fn post(&mut self, to: Digest, kind: u8, tag: [u8; 32], body: Vec<u8>) {
        // (Of the nodes the wallet is reached at, one by chance first:
        // the others if that one does not answer.)
        let mut chance = [0u8; 1];
        let _ = crate::random::fill(&mut chance);
        let (sealed, tried, turn, state, via) = (None, None, chance[0] as usize, Posted::Waiting, None);
        let answers = None;
        self.posts.push(Post { to, via, kind, body, tag, answers, sealed, began: None, tried, turn, missed: 0, state });
    }

    /// The answer to a message that came for this wallet: to go back
    /// by the node the message came by. Nothing, of a message that
    /// carries no key to answer to, or came by no node.
    pub fn answer(&mut self, to: &msg::Opened, kind: u8, tag: [u8; 32], body: Vec<u8>) -> bool {
        let Some(by) = to.by.filter(|_| !to.reply.is_empty()) else { return false };
        // (Whom it is for is not known, and is nobody's to say.)
        self.post(Digest::default(), kind, tag, body);
        let post = self.posts.last_mut().expect("it was put there");
        post.answers = Some(Answering { of: to.id, key: to.reply.clone(), by });
        true
    }

    /// The message sent of id `id`, if its answer may still come.
    pub fn awaited(&self, id: &Digest) -> Option<&Awaited> {
        self.awaited.iter().find(|a| a.id == *id)
    }

    /// A message to send to whichever wallet the full name of id `n`
    /// is.
    pub fn post_to_name(&mut self, n: Digest, kind: u8, tag: [u8; 32], body: Vec<u8>) {
        self.post(n, kind, tag, body);
        self.posts.last_mut().expect("it was put there").via = Some(n);
    }

    /// What is announced under the id that was asked has come:
    /// `announced`, at `unix`. The messages waiting for it now know
    /// whom they are for, and are to be sealed to what that wallet
    /// announces: which of them, and that announcement. Of a full
    /// name, the certificate that came with it is checked: it is the
    /// name's if `value_of` its name, on the chain, is the id it is
    /// signed by.
    pub fn announced(
        &mut self,
        announced: &[u8],
        unix: u64,
        value_of: impl FnOnce(&[u8]) -> Option<Digest>,
    ) -> Option<(Digest, Vec<usize>)> {
        let (announce, bundle) = announced.split_at_checked(msg::ANNOUNCE_LEN)?;
        let holder = Announced::read(announce, unix)?.id();
        let asked = match bundle.is_empty() {
            true => holder,
            false => {
                let checked = crate::subnames::read(bundle, unix).filter(|c| c.holder == holder)?;
                if value_of(&checked.name) != Some(checked.by) {
                    return None;
                }
                checked.point()
            }
        };
        let mut which = Vec::new();
        for (at, post) in self.posts.iter_mut().enumerate() {
            let other = post.answers.is_some() || post.asked() != asked || post.via.is_some() == bundle.is_empty();
            if post.sealed.is_some() || other {
                continue;
            }
            if post.via.is_some() && post.to != holder {
                post.to = holder;
                self.resolved.push((post.tag, holder));
            }
            which.push(at);
        }
        Some((asked, which))
    }

    /// Says what became of the post at `at`, and lets it go.
    pub fn settle(&mut self, at: usize, state: Posted) {
        let post = self.posts.swap_remove(at);
        self.posted.push((post.to, post.kind, post.tag, state));
    }

    /// Gives up the messages that have been tried for long enough.
    pub fn expire(&mut self, now: Micros) {
        self.posts.iter_mut().for_each(|p| p.began = p.began.or(Some(now)));
        let old = |p: &Post| p.began.is_some_and(|began| now.saturating_sub(began) >= POST_HOLDS);
        while let Some(at) = self.posts.iter().position(old) {
            self.settle(at, Posted::Unsent);
        }
        while self.passing.front().is_some_and(|p| now.saturating_sub(p.3) >= PASSING_HOLDS) {
            self.passing.pop_front();
        }
        self.awaited.retain(|a| now.saturating_sub(a.since) < ANSWER_HOLDS);
    }

    /// Keeps a sealed message to pass on to the wallet of id `to`.
    pub fn pass(&mut self, id: Digest, to: Digest, sealed: Vec<u8>, now: Micros) {
        if self.passing.iter().any(|p| p.0 == id) {
            return;
        }
        self.passing.push_back((id, to, Arc::new(sealed), now));
        while self.passing.iter().map(|p| p.2.len()).sum::<usize>() > PASSING_BYTES {
            self.passing.pop_front();
        }
    }

    /// The sealed message of id `id`: one this node sends, or passes on.
    pub fn sealed(&self, id: &Digest) -> Option<Arc<Vec<u8>>> {
        let own = self.posts.iter().filter_map(|p| p.sealed.as_ref()).find(|s| s.0 == *id).map(|s| Arc::clone(&s.1));
        own.or_else(|| self.passing.iter().find(|p| p.0 == *id).map(|p| Arc::clone(&p.2)))
    }

    /// Whether the sealed message of id `id` has come before.
    pub fn has_seen(&self, id: &Digest) -> bool {
        self.seen.contains(id)
    }

    /// Whether the sealed message of id `id` has come before; it has
    /// now.
    pub fn seen(&mut self, id: Digest) -> bool {
        if self.seen.contains(&id) {
            return true;
        }
        self.seen.push_back(id);
        if self.seen.len() > 1024 {
            self.seen.pop_front();
        }
        false
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn at(host: u8, port: u16) -> SocketAddrV4 {
        SocketAddrV4::new([10, 0, 0, host].into(), port)
    }

    fn wallet(seed: u8) -> Participant {
        Participant::new(mldsa::keygen(&[seed; 32]), &[seed; 64], 0)
    }

    /// One way is a wallet's, or two's: not every wallet's the node has
    /// room for.
    #[test]
    fn one_way_is_not_every_wallet() {
        let mut sessions = Sessions::new(Limits::default());
        let way = Where::Way(at(1, 5000), 7);
        let said = |seed: u8| {
            let mut w = wallet(seed);
            let seq = w.say(at(9, 3737), 9, 100, 0);
            w.announced(seq).unwrap().to_vec()
        };
        let mut held = 0;
        for seed in 1..=6u8 {
            match sessions.admit(said(seed), way, |bind| bind == 9, 100, 0) {
                Ok(_) => held += 1,
                Err(e) => assert_eq!(e, Refused::Full),
            }
        }
        assert_eq!(held, EACH_WAY);
        // (Another way has its own.)
        assert!(sessions.admit(said(7), Where::Way(at(1, 5000), 8), |bind| bind == 9, 100, 0).is_ok());
    }

    /// A node holds a session for a wallet once it has its announcement,
    /// made for that node and come from where the wallet is; goes on
    /// with it while the wallet says it is there; takes a newer
    /// announcement, never an older; and forgets a wallet that has
    /// said nothing for too long.
    #[test]
    fn a_session_is_opened_gone_on_with_and_forgotten() {
        let mut sessions = Sessions::new(Limits { most: 3, each_host: 2, idle: 90 * SECOND });
        let mut alice = wallet(1);
        let (node, home) = (at(9, 3737), at(1, 4000));
        let seq = alice.say(node, 77, 1000, 0);
        assert_eq!(alice.say(node, 77, 1001, SECOND), seq, "the same token: the same announcement");
        assert!(!alice.due(&node, 2 * SECOND, 30 * SECOND) && alice.due(&node, 3 * SECOND, 30 * SECOND));
        let said = alice.announced(seq).unwrap();
        // Not held yet: asked for, then taken.
        assert!(!sessions.seen(&alice.id(), home, seq, 0));
        assert_eq!(sessions.admit(said.to_vec(), home, |bind| bind == 77, 1000, 0), Ok(alice.id()));
        assert!(sessions.seen(&alice.id(), home, seq, 10 * SECOND));
        assert_eq!(sessions.get(&alice.id(), 20 * SECOND).unwrap().at, Where::Addr(home));
        assert_eq!(sessions.get(&alice.id(), 20 * SECOND).unwrap().announce, said);
        // From another address, or of another number: not that session.
        assert!(!sessions.seen(&alice.id(), at(2, 4000), seq, 20 * SECOND));
        assert!(!sessions.seen(&alice.id(), home, seq + 1, 20 * SECOND));
        // Not made for this node; said again, the same; past its time;
        // or changed: not taken.
        let taken = |sessions: &mut Sessions, bytes: &[u8], bind: u64, unix: u64| {
            sessions.admit(bytes.to_vec(), home, |b| b == bind, unix, 20 * SECOND)
        };
        assert_eq!(taken(&mut sessions, &said, 78, 1000), Err(Refused::NotBound));
        assert_eq!(taken(&mut sessions, &said, 77, 1000), Err(Refused::Stale));
        assert_eq!(taken(&mut sessions, &said, 77, 1000 + ANNOUNCE_HOLDS), Err(Refused::Unsound));
        assert_eq!(taken(&mut sessions, &said[1..], 77, 1000), Err(Refused::Unsound));
        // The node's token for it is another (the wallet moved, or the
        // node's tokens did): announced again, with a higher number,
        // and taken in place of the first.
        let again = alice.say(node, 80, 1100, 30 * SECOND);
        assert!(again > seq);
        let newer = alice.announced(again).unwrap();
        assert_eq!(taken(&mut sessions, &newer, 80, 1100), Ok(alice.id()));
        assert!(sessions.seen(&alice.id(), home, again, 30 * SECOND) && sessions.len() == 1);
        // Said nothing for too long: forgotten.
        assert!(sessions.get(&alice.id(), 119 * SECOND).is_some());
        assert!(sessions.get(&alice.id(), 120 * SECOND).is_none());
        sessions.prune(120 * SECOND);
        assert!(sessions.is_empty());
    }

    /// Room is not given away: so many sessions of one host, and so
    /// many in all; a wallet already there is not turned out by it.
    #[test]
    fn sessions_are_bounded_by_host_and_in_all() {
        let mut sessions = Sessions::new(Limits { most: 3, each_host: 2, idle: 90 * SECOND });
        let node = at(9, 3737);
        let open = |sessions: &mut Sessions, seed: u8, from: SocketAddrV4, unix: u64| {
            let mut w = wallet(seed);
            let seq = w.say(node, 1, unix, 0);
            sessions.admit(w.announced(seq).unwrap().to_vec(), from, |_| true, unix, 0).map(|_| ())
        };
        assert_eq!(open(&mut sessions, 1, at(1, 1), 1000), Ok(()));
        assert_eq!(open(&mut sessions, 2, at(1, 2), 1000), Ok(()));
        assert_eq!(open(&mut sessions, 3, at(1, 3), 1000), Err(Refused::Full), "a third of one host");
        assert_eq!(open(&mut sessions, 3, at(2, 3), 1000), Ok(()));
        assert_eq!(open(&mut sessions, 4, at(3, 1), 1000), Err(Refused::Full), "a fourth in all");
        // One that is there announces again: it has its place.
        assert_eq!(open(&mut sessions, 1, at(1, 1), 1001), Ok(()));
        assert_eq!(sessions.len(), 3);
    }

    /// A wallet opens what is sealed to the key it announces; makes
    /// another key in time, and still opens, for a while, what was
    /// sealed to the one before.
    #[test]
    fn a_wallet_opens_what_is_sealed_to_its_keys() {
        let (mut alice, mut bob) = (wallet(1), wallet(2));
        let node = at(9, 3737);
        bob.say(node, 1, 1000, 0);
        let seq = alice.say(node, 2, 1000, 0);
        let to = alice.announced(seq).unwrap();
        let reply = mlkem::keygen(&[6; 64]);
        let sealed =
            msg::seal(&Announced::read(&to, 1000).unwrap(), reply.public_key(), 1, b"hello", &[3; 32]).unwrap();
        assert_eq!(alice.open(&sealed, 0).unwrap().body, b"hello");
        assert_eq!(bob.open(&sealed, 0), None);
        // Not yet time for another key; then it is, and everything is
        // announced again.
        assert!(!alice.rotate(&[9; 64], KEY_LIFE - 1));
        assert!(alice.rotate(&[9; 64], KEY_LIFE));
        assert_eq!((alice.said_to(), alice.announced(seq)), (0, None));
        assert_ne!(alice.say(node, 2, 5000, KEY_LIFE), seq);
        assert_eq!(alice.open(&sealed, KEY_LIFE + KEY_GRACE - 1).unwrap().body, b"hello");
        assert_eq!(alice.open(&sealed, KEY_LIFE + KEY_GRACE), None);
        // Which nodes hold what it last said; and one that does is told
        // again only now and then.
        assert_eq!(alice.reached_at().count(), 0);
        let now = alice.say(node, 2, 5000, KEY_LIFE);
        assert!(!alice.held(&node, now, 2));
        assert_eq!(alice.reached_at().collect::<Vec<_>>(), [node]);
        assert!(!alice.due(&node, KEY_LIFE + 29 * SECOND, 30 * SECOND));
        assert!(alice.due(&node, KEY_LIFE + 30 * SECOND, 30 * SECOND));
        // The node's token for it is another: what it holds counts for
        // nothing until it has an announcement made for that one.
        assert!(alice.held(&node, now, 3));
        assert_eq!((alice.token(&node), alice.reached_at().count()), (3, 0));
        assert!(alice.due(&node, KEY_LIFE + 40 * SECOND, 30 * SECOND));
        let again = alice.say(node, 3, 5000, KEY_LIFE + 40 * SECOND);
        assert!(again > now && !alice.held(&node, again, 3));
        assert_eq!(alice.reached_at().collect::<Vec<_>>(), [node]);
        // And a node not yet heard from: asked for its token, and not
        // again at once.
        let (mut carol, far) = (wallet(3), at(8, 3737));
        assert!(carol.due(&far, 0, 30 * SECOND) && carol.token(&far) == 0);
        carol.greet(far, 0);
        assert!(!carol.due(&far, SECOND, 30 * SECOND) && carol.due(&far, 2 * SECOND, 30 * SECOND));
        assert_eq!((carol.said_to(), carol.reached_at().count(), carol.announced(0)), (1, 0, None));
        assert!(carol.held(&far, 0, 9));
        assert_eq!(carol.token(&far), 9);
        alice.keep(&[]);
        assert_eq!(alice.said_to(), 0);
    }
}
