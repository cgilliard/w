//! Ways through relays: what a relay keeps of those that pass through
//! it, and what whoever opened one keeps of it.
//!
//! A way is opened a relay at a time ([`crate::onion`]). Whoever
//! opens it ([`Way`]) agrees a key with the first relay; then tells it,
//! under that key, to go on to a second, and through it agrees a key
//! with the second, of which the first learns nothing; and so on to the
//! last. A relay ([`Relayed`]) keeps, of each way through it, who is
//! before it and who after, and the key of its own: it takes its
//! wrapping off what goes out and passes that on, puts its wrapping on
//! what comes back and passes that on, and reads only what is said to
//! it while it is the last.
//!
//! Nothing here sends anything: each thing done says what is to be
//! sent, to whom ([`Step`]), and the node sends it, as an object asked
//! for like any other. So the whole of it runs in a test with no
//! network at all.

use std::net::SocketAddrV4;

use crate::hash::Digest;
use crate::mldsa;
use crate::onion::{self as circuit, Hop, Opening};
use crate::transport::{Micros, SECOND};

/// What is sent along a way, from one node of it to the next.
pub const OPEN: u8 = 1;
/// A relay's answer to an opening: to whoever asked it.
pub const OPENED: u8 = 2;
/// Something going out: wrapped for the relays still to come.
pub const FORWARD: u8 = 3;
/// Something coming back.
pub const BACK: u8 = 4;
/// "This way is no more": said by whoever opened it, and passed on by
/// each relay to the next, which forget it. (A relay that is never
/// told forgets a way nothing passes along, a while later.)
pub const CLOSE: u8 = 5;

/// What the last relay of a way is told, as the first byte of what is
/// said to it: to go on to another relay, at this address, with this
/// hello.
pub const TELL_EXTEND: u8 = 1;
/// And what it says back of that: the other relay's answer.
pub const SAID_EXTENDED: u8 = 1;
/// The first byte of anything else said either way: what follows is
/// for whoever uses the way, not for the way itself.
pub const SAID: u8 = 0x80;

/// What whoever opened a way says to its last relay to know that the
/// way still goes there, as the first byte of what is said; and what
/// the relay says back, with whatever followed it.
pub const PING: u8 = 1;
pub const PONG: u8 = 2;
/// What a wallet says to the node it is reached at, at the end of a
/// way: "here I am, and this is what I announce" (the announcement,
/// made for this way: [`Way::bind`]); or "still here" (its id, and the
/// number of what it announced). And what that node says back: the id,
/// and the number of the announcement it holds for it, or none (zero).
pub const HERE: u8 = 3;
pub const STILL: u8 = 4;
pub const HELD: u8 = 5;
/// (The same as [`HELD`], said in answer to [`HERE`]: filled out as
/// that is.)
pub const HERE_HELD: u8 = 12;
/// What a wallet held at the end of a way says there to be reached by
/// a full name as well: the certificate that it is that name, with
/// what goes with it ([`crate::subnames`]). And what is said back: the
/// id the name is reached by, and the number of the certificate held
/// for it, or none (zero).
pub const HERE_AS: u8 = 13;
pub const AS_HELD: u8 = 14;
/// What a wallet says back to the node it is reached at when a sealed
/// message has come to it down its way: the message's id. Only then
/// is whoever gave the message told that it was passed on.
pub const TAKEN: u8 = 15;
/// What a wallet says to the node it is reached at to answer a
/// message that came to it there: the answer, sealed, which names the
/// message it answers. The node passes it back to whoever gave it that
/// message, of whom the wallet knows nothing: [`ANSWER`], said to them
/// along the way they gave it by.
pub const REPLY: u8 = 16;
pub const ANSWER: u8 = 17;
/// How long a way may leave what was said along it unanswered before
/// it is taken to go nowhere any more: a relay of it is gone. Several
/// times what an answer takes there and back over three relays with a
/// slow link among them (a hop by satellite is more than half a second
/// each way): a way given up too soon is made again over the same
/// links. What it costs is how soon a relay that is gone is known to
/// be.
pub const ANSWERED_WITHIN: Micros = 10 * SECOND;
/// What whoever sends to a wallet says to a node that wallet is
/// reached at: "what does the wallet of this id announce?", answered
/// with the announcement, or with the id if the wallet is not there;
/// and "pass this on" (a sealed message), answered with the message's
/// id and what became of it ([`super::message::NOTICE_PASSED`] and the
/// rest).
pub const ASK: u8 = 6;
pub const ANNOUNCED: u8 = 7;
pub const ABSENT: u8 = 8;
pub const GIVE: u8 = 9;
pub const NOTICE: u8 = 10;
/// And what that node says to the wallet, along the wallet's way:
/// a sealed message for it.
pub const TAKE: u8 = 11;

/// What this node opened a way for.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Default)]
pub enum Purpose {
    /// Whoever drives the node asked for it.
    #[default]
    Asked,
    /// Kept open through relays drawn by chance, to go on from to
    /// wherever a message is next to go: one relay more is sooner
    /// added than a whole way opened.
    Spare,
    /// Its wallet is reached at the end of it.
    Session,
    /// Its wallet sends to another by it. (Never the way it is itself
    /// reached by: the node at the end would know who sends to whom.)
    Send,
}

/// The lengths of what is carried along a way, before it is sealed:
/// whatever is said is filled out to the least of them that holds it,
/// so that a relay that passes it on learns from its length only
/// which of these few it is. The least is what one datagram holds;
/// the next holds a key agreed or what a wallet announces; the rest,
/// sealed messages by their length.
pub const SIZES: [usize; 6] =
    [super::message::MAX_STEPPED - circuit::SEAL, 8 << 10, 16 << 10, 32 << 10, 48 << 10, 80 << 10];
/// The length what opens a way, what a wallet announces, and what is
/// asked and answered of it are all filled out to, both ways: so that
/// going on to another relay, saying a wallet is there and asking
/// after one look alike to the relays between.
const MIDDLE: usize = SIZES[1];
const _: () = assert!(SIZES[5] >= crate::msg::MAX_SEALED + 8);

/// The longest thing carried along a way.
pub const MAX_STEP: usize = SIZES[5] + circuit::SEAL;

/// `whole` filled out to the least of [`SIZES`] that holds it and is
/// no less than `least`: its length, itself, and nothing.
fn filled(whole: &[u8], least: usize) -> Vec<u8> {
    let needs = (4 + whole.len()).max(least);
    let size = SIZES.iter().copied().find(|size| *size >= needs).unwrap_or(needs);
    let mut out = Vec::with_capacity(size + circuit::SEAL);
    out.extend_from_slice(&(whole.len() as u32).to_le_bytes());
    out.extend_from_slice(whole);
    out.resize(size, 0);
    out
}

/// What was filled out: none if it is not of one of the lengths, or
/// does not hold what it says it does.
fn emptied(filled: &[u8]) -> Option<&[u8]> {
    let (len, rest) = filled.split_first_chunk::<4>().filter(|_| SIZES.contains(&filled.len()))?;
    rest.get(..u32::from_le_bytes(*len) as usize)
}

/// The least length what is said along a way is filled out to, by
/// what it is.
fn least(said: &[u8]) -> usize {
    match said.first() {
        Some(&(HERE | HERE_HELD | HERE_AS | AS_HELD | ASK | ANNOUNCED | ABSENT)) => MIDDLE,
        _ => 0,
    }
}

/// Where a relay's count of what it says back begins: a number of the
/// hello it answered, so that no two relays of a way count alike, and
/// none knows by its count how far along the way it is.
fn base(hello: &[u8]) -> u64 {
    let at = crate::mlkem::EK_LEN;
    (u32::from_le_bytes(hello[at..at + 4].try_into().expect("four bytes")) as u64) << 32
}

/// Something to send to a neighbour on a way.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Step {
    pub to: SocketAddrV4,
    /// The number the two neighbours know the way by.
    pub circuit: u64,
    pub kind: u8,
    pub count: u64,
    pub bytes: Vec<u8>,
}

/// A way through this relay: who is before it, who after, its key.
struct Through {
    before: (SocketAddrV4, u64),
    after: Option<(SocketAddrV4, u64)>,
    hop: Hop,
    /// The highest count of anything that has gone out through here,
    /// and which of the 64 up to it have: what has been here before
    /// does not pass again, and what overtook another on the way does.
    out: u64,
    window: u64,
    /// How many things this relay itself has said back.
    said: u64,
    seen: Micros,
}

/// How a relay is bounded in the ways through it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Limits {
    pub most: usize,
    /// Ways that may come to this relay from one host.
    pub each_host: usize,
    /// How long nothing may pass along a way before it is forgotten.
    pub idle: Micros,
}

impl Default for Limits {
    fn default() -> Limits {
        // (A way that is in use has something pass along it every half
        // minute: one that has had nothing for five times that is no
        // longer anybody's.)
        Limits { most: 50_000, each_host: 256, idle: 150 * SECOND }
    }
}

/// What came of something going out through a relay.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Out {
    /// Passed on, or an opening sent on to the next relay.
    Step(Step),
    /// Said to this relay, which is the last: for whoever uses the way,
    /// which is known by who is before this relay on it.
    Said { way: (SocketAddrV4, u64), said: Vec<u8> },
    /// Not of a way through here, or not in its turn: nothing.
    Nothing,
}

impl Through {
    /// Whether nothing of this count has gone out through here before;
    /// after which something has.
    fn fresh(&mut self, count: u64) -> bool {
        if count > self.out {
            let ahead = count - self.out;
            self.window = if ahead >= 64 { 1 } else { self.window << ahead | 1 };
            self.out = count;
            return true;
        }
        let behind = self.out - count;
        if behind >= 64 || self.window >> behind & 1 == 1 {
            return false;
        }
        self.window |= 1 << behind;
        true
    }
}

/// The ways through a relay.
pub struct Relayed {
    limits: Limits,
    through: Vec<Through>,
    /// Who opened a way lately, and when: each opening is answered
    /// with a signature, and one host is answered [`OPENS_EACH`] times
    /// a second and no more, however often it opens and closes.
    opened: std::collections::VecDeque<(std::net::Ipv4Addr, Micros)>,
}

/// How many ways one host, not a relay of the list, opens in a second.
const OPENS_EACH: usize = 8;

impl Relayed {
    pub fn new(limits: Limits) -> Relayed {
        Relayed { limits, through: Vec::new(), opened: Default::default() }
    }

    pub fn len(&self) -> usize {
        self.through.len()
    }

    pub fn is_empty(&self) -> bool {
        self.through.is_empty()
    }

    fn of_before(&mut self, from: SocketAddrV4, circuit: u64) -> Option<&mut Through> {
        self.through.iter_mut().find(|t| t.before == (from, circuit))
    }

    /// Whoever is at `from` opens a way through this relay, known
    /// between the two as `circuit`, with `hello`: the answer, to be
    /// sent back. `identity` is the relay's key, `chance` 32 random
    /// bytes. None if it is no hello, the way is open already, or
    /// there is no room.
    #[allow(clippy::too_many_arguments)]
    pub fn open(
        &mut self,
        identity: &mldsa::SecretKey,
        from: SocketAddrV4,
        circuit: u64,
        hello: &[u8],
        chance: &[u8; 32],
        listed: bool,
        now: Micros,
    ) -> Option<Step> {
        self.prune(now);
        // (So many of one host, unless it is a relay of the list: the
        // ways of everybody come through those.)
        let of_host = self.through.iter().filter(|t| t.before.0.ip() == from.ip()).count();
        let room = self.through.len() < self.limits.most && (listed || of_host < self.limits.each_host);
        if !room || self.of_before(from, circuit).is_some() {
            return None;
        }
        while self.opened.front().is_some_and(|o| now.saturating_sub(o.1) >= SECOND) {
            self.opened.pop_front();
        }
        if !listed && self.opened.iter().filter(|o| o.0 == *from.ip()).count() >= OPENS_EACH {
            return None;
        }
        self.opened.push_back((*from.ip(), now));
        let (hop, answer) = circuit::answer(identity, hello, chance)?;
        let (before, said) = ((from, circuit), base(hello));
        self.through.push(Through { before, after: None, hop, out: 0, window: 1, said, seen: now });
        Some(Step { to: from, circuit, kind: OPENED, count: 0, bytes: answer })
    }

    /// Something going out has come from `from` on `circuit`, the
    /// `count`-th of its way. Passed on to the next relay, less this
    /// one's wrapping; or, of a way this relay is the last of, opened:
    /// and gone on with to another relay, if that is what it says
    /// (`fresh` is a number to know that stretch by), or given to
    /// whoever uses the way.
    pub fn forward(
        &mut self,
        from: SocketAddrV4,
        circuit: u64,
        count: u64,
        mut bytes: Vec<u8>,
        fresh: u64,
        now: Micros,
    ) -> Out {
        let Some(way) = self.of_before(from, circuit) else { return Out::Nothing };
        if !way.fresh(count) {
            return Out::Nothing;
        }
        way.seen = now;
        if let Some((to, circuit)) = way.after {
            way.hop.peel(count, &mut bytes);
            return Out::Step(Step { to, circuit, kind: FORWARD, count, bytes });
        }
        let Some(said) = circuit::open(&way.hop, count, &bytes) else { return Out::Nothing };
        let Some(said) = emptied(&said) else { return Out::Nothing };
        match said.split_first() {
            Some((&TELL_EXTEND, rest)) if rest.len() == 6 + circuit::HELLO_LEN => {
                let ip: [u8; 4] = rest[..4].try_into().expect("four bytes");
                let to = SocketAddrV4::new(ip.into(), u16::from_le_bytes([rest[4], rest[5]]));
                // (Not back the way it came, nor to itself.)
                if to == from {
                    return Out::Nothing;
                }
                way.after = Some((to, fresh));
                Out::Step(Step { to, circuit: fresh, kind: OPEN, count: 0, bytes: rest[6..].to_vec() })
            }
            Some((&SAID, rest)) => Out::Said { way: (from, circuit), said: rest.to_vec() },
            _ => Out::Nothing,
        }
    }

    /// The relay this one went on to, at `from` on `circuit`, has
    /// answered the opening: its answer, said back along the way.
    pub fn opened(&mut self, from: SocketAddrV4, circuit: u64, answer: &[u8], now: Micros) -> Option<Step> {
        let way = self.through.iter_mut().find(|t| t.after == Some((from, circuit)))?;
        let mut said = Vec::with_capacity(1 + answer.len());
        said.push(SAID_EXTENDED);
        said.extend_from_slice(answer);
        way.said += 1;
        way.seen = now;
        let bytes = circuit::seal_back(&way.hop, way.said, &filled(&said, MIDDLE));
        Some(Step { to: way.before.0, circuit: way.before.1, kind: BACK, count: way.said, bytes })
    }

    /// Something coming back has come from `from` on `circuit`: passed
    /// on towards whoever opened the way, with this relay's wrapping.
    pub fn back(
        &mut self,
        from: SocketAddrV4,
        circuit: u64,
        count: u64,
        mut bytes: Vec<u8>,
        now: Micros,
    ) -> Option<Step> {
        let way = self.through.iter_mut().find(|t| t.after == Some((from, circuit)))?;
        way.seen = now;
        way.hop.cover(count, &mut bytes);
        Some(Step { to: way.before.0, circuit: way.before.1, kind: BACK, count, bytes })
    }

    /// This relay, the last of the way known by who is before it, says
    /// `said` back to whoever opened it.
    pub fn say(&mut self, way: (SocketAddrV4, u64), said: &[u8], now: Micros) -> Option<Step> {
        let way = self.of_before(way.0, way.1).filter(|t| t.after.is_none())?;
        let mut whole = Vec::with_capacity(1 + said.len());
        whole.push(SAID);
        whole.extend_from_slice(said);
        way.said += 1;
        way.seen = now;
        let bytes = circuit::seal_back(&way.hop, way.said, &filled(&whole, least(said)));
        Some(Step { to: way.before.0, circuit: way.before.1, kind: BACK, count: way.said, bytes })
    }

    /// Whether the way known by who is before this relay on it is still
    /// here.
    pub fn holds(&self, way: &(SocketAddrV4, u64)) -> bool {
        self.through.iter().any(|t| t.before == *way)
    }

    /// The number the way known by who is before this relay on it is
    /// bound by ([`Hop::bind`]).
    pub fn bind_of(&self, way: &(SocketAddrV4, u64)) -> Option<u64> {
        self.through.iter().find(|t| t.before == *way).map(|t| t.hop.bind())
    }

    /// Whether a way through here goes on to `after`, known between the
    /// two by that number.
    pub fn goes_on_to(&self, after: &(SocketAddrV4, u64)) -> bool {
        self.through.iter().any(|t| t.after == Some(*after))
    }

    /// Whoever is before this relay on a way says the way is no more:
    /// forgotten, and the relay after told the same.
    pub fn close(&mut self, from: SocketAddrV4, circuit: u64) -> Option<Step> {
        let at = self.through.iter().position(|t| t.before == (from, circuit))?;
        let (to, circuit) = self.through.swap_remove(at).after?;
        Some(Step { to, circuit, kind: CLOSE, count: 0, bytes: vec![0] })
    }

    /// Forgets the ways nothing has passed along for too long.
    pub fn prune(&mut self, now: Micros) {
        let idle = self.limits.idle;
        self.through.retain(|t| now.saturating_sub(t.seen) < idle);
    }
}

/// What came back along a way, to whoever opened it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Came {
    /// The way is a relay longer, and goes on: this is to be sent.
    Step(Step),
    /// The way is open to its end.
    Ready,
    /// Its last relay says this.
    Said(Vec<u8>),
    /// Something its last relay but one said, to what the way asked of
    /// it before it went on from there (a ping's answer, say): nothing
    /// to the way as it is now, which waits as it did.
    Late,
    /// Not what this way was waiting for: the way is to be given up.
    Bad,
}

/// Something on its way to a neighbour, until that neighbour has asked
/// for it: it is told that it is there, again if it does not ask.
pub struct Leaving {
    /// What the neighbour asks for it by.
    pub name: u64,
    pub step: Step,
    pub bytes: std::sync::Arc<Vec<u8>>,
    pub told: Option<Micros>,
    pub asked: bool,
    pub since: Micros,
}

/// How often a neighbour that does not ask is told again, and how long
/// a thing is kept for it.
pub const TELL_AGAIN: Micros = SECOND * 2 / 5;
pub const KEPT: Micros = 30 * SECOND;
/// How long a way may take to open.
pub const OPENING: Micros = 10 * SECOND;
/// And how long its first relay may take to answer: that is one
/// asking and one answer, and a relay that leaves it so long is not
/// there.
pub const FIRST_ANSWER: Micros = 5 * SECOND;

/// The ways this node opened, and what has come back along them.
#[derive(Default)]
pub struct Ways {
    pub open: Vec<Way>,
    /// What the last relay of a way said: the way, and what.
    pub said: Vec<(u64, Vec<u8>)>,
    /// Ways asked for and not yet begun: the number each is to be
    /// known by, and its relays.
    pub wanted: Vec<(u64, Vec<(Digest, SocketAddrV4)>)>,
    /// What is to be said along a way, and has not yet been sent.
    pub to_say: Vec<(u64, Vec<u8>)>,
    /// Ways given up, of which the first relay is still to be told:
    /// where it is, and the number it knows the way by.
    pub closed: Vec<(SocketAddrV4, u64)>,
}

impl Ways {
    /// Gives up the ways of which `gone` says so: their relays are to
    /// be told. How many.
    pub fn give_up(&mut self, mut gone: impl FnMut(&Way) -> bool) -> usize {
        let before = self.open.len();
        let closed = &mut self.closed;
        self.open.retain(|way| {
            let goes = gone(way);
            if goes {
                closed.push((way.first(), way.circuit()));
            }
            !goes
        });
        before - self.open.len()
    }
}

/// A way, as whoever opened it has it.
pub struct Way {
    circuit: u64,
    /// The relays of it, nearest first: each one's id and where it is.
    path: Vec<(Digest, SocketAddrV4)>,
    hops: Vec<Hop>,
    /// The opening of the relay being added, until it has answered.
    opening: Option<Opening>,
    /// How many things have been sent out along it.
    sent: u64,
    pub purpose: Purpose,
    /// Since when something said along it is unanswered: none while
    /// nothing is.
    waiting: Option<Micros>,
    pub began: Micros,
    /// When something last came back along it.
    pub seen: Micros,
    /// What came back along it lately, each by a few of its bytes: what
    /// comes a second time is not taken a second time.
    heard: std::collections::VecDeque<u64>,
}

/// How many of the things that came back along a way are kept count of.
const HEARD: usize = 128;

impl Way {
    /// Begins a way through `path` (nearest first, not empty), known to
    /// its first relay as `circuit`: the opening to send it. `chance`
    /// is 96 random bytes.
    pub fn begin(circuit: u64, path: Vec<(Digest, SocketAddrV4)>, chance: &[u8; 96], now: Micros) -> (Way, Step) {
        let opening = Opening::new(chance);
        let step = Step { to: path[0].1, circuit, kind: OPEN, count: 0, bytes: opening.hello().to_vec() };
        let hops = Vec::with_capacity(path.len());
        let purpose = Purpose::Asked;
        let (opening, waiting) = (Some(opening), Some(now));
        let heard = Default::default();
        (Way { circuit, path, hops, opening, sent: 0, purpose, waiting, began: now, seen: now, heard }, step)
    }

    pub fn circuit(&self) -> u64 {
        self.circuit
    }

    /// Where its first relay is.
    pub fn first(&self) -> SocketAddrV4 {
        self.path[0].1
    }

    /// The relay it ends at.
    pub fn end(&self) -> &(Digest, SocketAddrV4) {
        self.path.last().expect("a way has a relay")
    }

    /// Whether it is open to its end.
    pub fn ready(&self) -> bool {
        self.hops.len() == self.path.len()
    }

    /// The number this way and its last relay know, and nobody else:
    /// none (zero) until it is open.
    pub fn bind(&self) -> u64 {
        self.hops.last().filter(|_| self.ready()).map_or(0, Hop::bind)
    }

    /// The relay being added has answered with `answer`: the way is a
    /// relay longer, and goes on to the next if there is one.
    fn grown(&mut self, answer: &[u8], chance: &[u8; 96]) -> Came {
        let relay = self.path[self.hops.len()].0;
        let Some(hop) = self.opening.take().and_then(|o| o.agreed(&relay, answer)) else { return Came::Bad };
        self.hops.push(hop);
        if self.ready() {
            return Came::Ready;
        }
        self.waiting = Some(self.seen);
        Came::Step(self.reach(chance))
    }

    /// Tells the last relay there is to go on to the next of the path.
    fn reach(&mut self, chance: &[u8; 96]) -> Step {
        let opening = Opening::new(chance);
        let next = self.path[self.hops.len()].1;
        let mut tell = Vec::with_capacity(7 + circuit::HELLO_LEN);
        tell.push(TELL_EXTEND);
        tell.extend_from_slice(&next.ip().octets());
        tell.extend_from_slice(&next.port().to_le_bytes());
        tell.extend_from_slice(opening.hello());
        self.opening = Some(opening);
        self.wrapped(&tell, MIDDLE)
    }

    /// Something that is to be answered is said along it at `now`.
    pub fn awaits(&mut self, now: Micros) {
        self.waiting = self.waiting.or(Some(now));
    }

    /// Whether what was said along it has gone unanswered too long at
    /// `now`: the way goes nowhere any more.
    pub fn gone(&self, now: Micros) -> bool {
        self.waiting.is_some_and(|since| now.saturating_sub(since) >= ANSWERED_WITHIN)
    }

    /// Whether its first relay has not yet answered.
    pub fn unanswered(&self) -> bool {
        self.hops.is_empty()
    }

    /// Whether the relay of id `id` is one of the way's.
    pub fn passes(&self, id: &Digest) -> bool {
        self.path.iter().any(|relay| relay.0 == *id)
    }

    /// Goes on from a way that is open to one relay more: what is to
    /// be sent. The way is open again when that relay has answered.
    pub fn extend(&mut self, to: (Digest, SocketAddrV4), chance: &[u8; 96], now: Micros) -> Option<Step> {
        if !self.ready() || self.passes(&to.0) {
            return None;
        }
        self.path.push(to);
        (self.began, self.waiting) = (now, Some(now));
        Some(self.reach(chance))
    }

    fn wrapped(&mut self, whole: &[u8], least: usize) -> Step {
        self.sent += 1;
        let bytes = circuit::wrap(&self.hops, self.sent, &filled(whole, least));
        Step { to: self.path[0].1, circuit: self.circuit, kind: FORWARD, count: self.sent, bytes }
    }

    /// The first relay has answered the opening.
    pub fn opened(&mut self, answer: &[u8], chance: &[u8; 96], now: Micros) -> Came {
        // (Only what is the answer counts as one: what is not leaves
        // the way waiting as it was.)
        let before = (self.seen, self.waiting);
        (self.seen, self.waiting) = (now, None);
        let came = match self.hops.is_empty() {
            true => self.grown(answer, chance),
            false => Came::Bad,
        };
        if matches!(came, Came::Bad) {
            (self.seen, self.waiting) = before;
        }
        came
    }

    /// Something has come back along the way, the `count`-th of
    /// whichever relay said it.
    pub fn back(&mut self, count: u64, bytes: &[u8], chance: &[u8; 96], now: Micros) -> Came {
        // (Only what a relay of the way said counts as heard: what is
        // not, or what was heard before and is sent again by whoever
        // kept it, leaves the way waiting as it was, to be given up in
        // its time if nothing else comes.)
        let before = (self.seen, self.waiting);
        let Some(said) = circuit::unwrap(&self.hops, count, bytes).and_then(|said| emptied(&said).map(<[u8]>::to_vec))
        else {
            return Came::Bad;
        };
        let mut mark = [0u8; 8];
        let tail = &bytes[bytes.len().saturating_sub(8)..];
        mark[..tail.len()].copy_from_slice(tail);
        let mark = u64::from_le_bytes(mark) ^ count.rotate_left(32);
        if self.heard.contains(&mark) {
            return Came::Late;
        }
        self.heard.push_back(mark);
        if self.heard.len() > HEARD {
            self.heard.pop_front();
        }
        (self.seen, self.waiting) = (now, None);
        match said.split_first() {
            Some((&SAID_EXTENDED, answer)) if !self.ready() => {
                let came = self.grown(answer, chance);
                if matches!(came, Came::Bad) {
                    (self.seen, self.waiting) = before;
                }
                came
            }
            Some((&SAID, rest)) if self.ready() => Came::Said(rest.to_vec()),
            // (An answer to what was asked before the way went on: it
            // is not the relay it goes on to that answered, and the way
            // still waits for that one.)
            Some((&SAID, _)) => {
                self.waiting = before.1;
                Came::Late
            }
            _ => {
                (self.seen, self.waiting) = before;
                Came::Bad
            }
        }
    }

    /// Says `said` to the last relay of the way, which is open: what is
    /// to be sent.
    pub fn say(&mut self, said: &[u8]) -> Option<Step> {
        if !self.ready() {
            return None;
        }
        let mut whole = Vec::with_capacity(1 + said.len());
        whole.push(SAID);
        whole.extend_from_slice(said);
        Some(self.wrapped(&whole, least(said)))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::address::id_of;

    fn at(host: u8) -> SocketAddrV4 {
        SocketAddrV4::new([10, 0, 0, host].into(), 3737)
    }

    /// Three relays and whoever opens a way through them, with nothing
    /// between them but what each says is to be sent.
    struct World {
        keys: Vec<mldsa::SecretKey>,
        relays: Vec<Relayed>,
        /// What each relay was given, as it was given: to see what each
        /// could know.
        given: Vec<Vec<Vec<u8>>>,
        fresh: u64,
    }

    const ME: u8 = 100;

    impl World {
        fn new() -> World {
            let keys: Vec<_> = (1..=3u8).map(|seed| mldsa::keygen(&[seed; 32])).collect();
            let relays = (0..3).map(|_| Relayed::new(Limits::default())).collect();
            World { keys, relays, given: vec![Vec::new(); 3], fresh: 1000 }
        }

        fn path(&self) -> Vec<(Digest, SocketAddrV4)> {
            (0..3).map(|i| (id_of(self.keys[i].public_key()), at(i as u8 + 1))).collect()
        }

        /// Carries `step`, sent by the node at `from`, to where it goes,
        /// and on, until something is for whoever opened the way (a
        /// step to `ME`) or for the last relay's user, or nothing is.
        #[allow(clippy::type_complexity)]
        fn carry(
            &mut self,
            mut from: SocketAddrV4,
            mut step: Step,
        ) -> (Option<Step>, Option<((SocketAddrV4, u64), Vec<u8>)>) {
            loop {
                if step.to == at(ME) {
                    return (Some(step), None);
                }
                let i = (step.to.ip().octets()[3] - 1) as usize;
                self.given[i].push(step.bytes.clone());
                self.fresh += 1;
                let (here, relay) = (step.to, &mut self.relays[i]);
                let next = match step.kind {
                    OPEN => relay.open(&self.keys[i], from, step.circuit, &step.bytes, &[i as u8; 32], false, 0),
                    OPENED => relay.opened(from, step.circuit, &step.bytes, 0),
                    BACK => relay.back(from, step.circuit, step.count, step.bytes, 0),
                    CLOSE => relay.close(from, step.circuit),
                    FORWARD => match relay.forward(from, step.circuit, step.count, step.bytes, self.fresh, 0) {
                        Out::Step(step) => Some(step),
                        Out::Said { way, said } => return (None, Some((way, said))),
                        Out::Nothing => None,
                    },
                    _ => None,
                };
                match next {
                    Some(next) => (from, step) = (here, next),
                    None => return (None, None),
                }
            }
        }

        /// Opens a way through all three.
        fn open(&mut self) -> Way {
            let (mut way, mut step) = Way::begin(7, self.path(), &[50; 96], 0);
            let mut chance = 51u8;
            loop {
                let (came, _) = self.carry(at(ME), step);
                let came = came.expect("an answer comes back");
                chance += 1;
                let next = match came.kind {
                    OPENED => way.opened(&came.bytes, &[chance; 96], 0),
                    _ => way.back(came.count, &came.bytes, &[chance; 96], 0),
                };
                match next {
                    Came::Step(next) => step = next,
                    Came::Ready => return way,
                    other => panic!("{other:?}"),
                }
            }
        }
    }

    /// A way is opened through three relays, each added through those
    /// before it; what is said along it reaches the last and nobody
    /// before it; and what the last says comes back to whoever opened
    /// the way.
    #[test]
    fn a_way_is_opened_and_said_along() {
        let mut world = World::new();
        let mut way = world.open();
        assert!(way.ready() && way.first() == at(1) && way.end().1 == at(3));
        assert_eq!(world.relays.iter().map(Relayed::len).collect::<Vec<_>>(), [1, 1, 1]);
        // Said to the last.
        let secret = b"what is said to the node the wallet is reached at";
        world.given.iter_mut().for_each(Vec::clear);
        let step = way.say(secret).unwrap();
        let (_, said) = world.carry(at(ME), step);
        let (known_by, said) = said.expect("it reaches the last relay");
        assert_eq!((known_by.0, &said[..]), (at(2), &secret[..]));
        // Each relay was given something else, and none of it reads.
        let given: Vec<&Vec<u8>> = world.given.iter().map(|g| &g[0]).collect();
        assert!(given[0] != given[1] && given[1] != given[2] && given[0] != given[2]);
        assert!(given.iter().all(|g| !g.windows(secret.len()).any(|w| w == secret)));
        // Said back by the last: through the second and the first.
        let answer = b"and what it says back";
        let step = world.relays[2].say(known_by, answer, 0).unwrap();
        let (came, _) = world.carry(at(3), step);
        let came = came.unwrap();
        assert_eq!((came.to, came.circuit, came.kind), (at(ME), 7, BACK));
        assert_eq!(way.back(came.count, &came.bytes, &[0; 96], 0), Came::Said(answer.to_vec()));
        // Again, and again: each in its turn.
        for round in 0..3u8 {
            let step = way.say(&[round; 40]).unwrap();
            assert_eq!(world.carry(at(ME), step).1.unwrap().1, [round; 40]);
            let step = world.relays[2].say(known_by, &[round; 9], 0).unwrap();
            let came = world.carry(at(3), step).0.unwrap();
            assert_eq!(way.back(came.count, &came.bytes, &[0; 96], 0), Came::Said(vec![round; 9]));
        }
    }

    /// What goes along a way is of a few lengths, whatever it is: a
    /// word is one datagram; and going on to another relay, saying a
    /// wallet is there and asking after one are of one length, both
    /// ways.
    #[test]
    fn what_goes_along_a_way_is_of_few_lengths() {
        let mut world = World::new();
        let mut way = world.open();
        // Opening it: but for the first word of each relay, which is
        // what it is, everything was of the middle length.
        let seal = circuit::SEAL;
        let opening: Vec<usize> = world.given.iter().flatten().map(Vec::len).collect();
        let (hello, answer) = (circuit::HELLO_LEN, circuit::ANSWER_LEN);
        assert!(opening.iter().all(|len| [hello, answer, MIDDLE + seal].contains(len)), "{opening:?}");
        // What is said, each way, by what it is.
        let mut lengths = |said: &[u8], answer: &[u8]| {
            world.given.iter_mut().for_each(Vec::clear);
            let step = way.say(said).unwrap();
            let out = step.bytes.len();
            let (known_by, got) = world.carry(at(ME), step).1.unwrap();
            assert_eq!(got, said);
            assert!(world.given.iter().all(|g| g.len() == 1 && g[0].len() == out), "the same at each relay");
            let step = world.relays[2].say(known_by, answer, 0).unwrap();
            let back = step.bytes.len();
            let came = world.carry(at(3), step).0.unwrap();
            assert_eq!(
                (came.bytes.len(), way.back(came.count, &came.bytes, &[0; 96], 0)),
                (back, Came::Said(answer.to_vec()))
            );
            (out - seal, back - seal)
        };
        let (id, announce) = ([1u8; 33], [2u8; 1 + crate::msg::ANNOUNCE_LEN]);
        let with = |code: u8, bytes: &[u8]| [&[code][..], &bytes[1..]].concat();
        // A word: one datagram each way.
        assert_eq!(lengths(&with(PING, &[0; 9]), &with(PONG, &[0; 9])), (SIZES[0], SIZES[0]));
        assert_eq!(lengths(&with(STILL, &[0; 41]), &with(HELD, &[0; 41])), (SIZES[0], SIZES[0]));
        assert!(SIZES[0] + seal <= crate::net::message::MAX_STEPPED);
        // A wallet says it is there; one is asked after, and is or is
        // not there: as going on to another relay.
        assert_eq!(lengths(&with(HERE, &announce), &with(HERE_HELD, &[0; 41])), (MIDDLE, MIDDLE));
        assert_eq!(lengths(&with(ASK, &id), &with(ANNOUNCED, &announce)), (MIDDLE, MIDDLE));
        assert_eq!(lengths(&with(ASK, &id), &with(ABSENT, &id)), (MIDDLE, MIDDLE));
        // A sealed message, by its length: one that says a few thousand
        // bytes is of the length of a wallet's saying it is there, and
        // the greatest holds the longest there is.
        let sealed = |body: usize| vec![GIVE; 1 + crate::msg::OVERHEAD + body];
        assert_eq!(lengths(&sealed(100), &with(NOTICE, &[0; 34])), (SIZES[1], SIZES[0]));
        assert_eq!(lengths(&sealed(5_000), &with(NOTICE, &[0; 34])), (SIZES[1], SIZES[0]));
        assert_eq!(lengths(&sealed(6_000), &with(NOTICE, &[0; 34])), (SIZES[2], SIZES[0]));
        assert_eq!(lengths(&sealed(20_000), &with(NOTICE, &[0; 34])), (SIZES[3], SIZES[0]));
        assert_eq!(lengths(&sealed(crate::msg::MAX_BODY), &with(NOTICE, &[0; 34])).0, SIZES[5]);
        // What is not of one of the lengths says nothing.
        assert_eq!(emptied(&filled(b"abc", 0)), Some(&b"abc"[..]));
        assert_eq!(emptied(&filled(b"abc", 0)[1..]), None);
        assert_eq!(emptied(&[0xff; SIZES[0]]), None);
    }

    /// What does not belong on a way does nothing: said again, it has
    /// been here before; from elsewhere, it is of no way; changed, it
    /// opens to nothing. And a relay that is not the one named is not
    /// gone through.
    #[test]
    fn what_is_not_of_a_way_does_nothing() {
        let mut world = World::new();
        let mut way = world.open();
        let step = way.say(b"once").unwrap();
        assert!(world.carry(at(ME), step.clone()).1.is_some());
        // The same again: the first relay has seen that count.
        assert_eq!(world.carry(at(ME), step.clone()), (None, None));
        // One that overtook another: both pass, each once.
        let (first, second) = (way.say(b"a").unwrap(), way.say(b"b").unwrap());
        assert_eq!(world.carry(at(ME), second.clone()).1.unwrap().1, b"b");
        assert_eq!(world.carry(at(ME), first.clone()).1.unwrap().1, b"a");
        assert_eq!(world.carry(at(ME), first), (None, None));
        assert_eq!(world.carry(at(ME), second), (None, None));
        // From another address, or on another number.
        let later = way.say(b"twice").unwrap();
        assert_eq!(world.carry(at(99), later.clone()), (None, None));
        assert_eq!(world.carry(at(ME), Step { circuit: 8, ..later.clone() }), (None, None));
        // Changed on the way: the last relay opens nothing. (And the
        // count is spent: the true one, sent after, is too late.)
        let mut changed = later.clone();
        changed.bytes[0] ^= 1;
        assert_eq!(world.carry(at(ME), changed), (None, None));
        assert_eq!(world.carry(at(ME), later), (None, None));
        let after = way.say(b"thrice").unwrap();
        assert!(world.carry(at(ME), after).1.is_some());
        // The same way opened twice: once.
        let (_, again) = Way::begin(7, world.path(), &[50; 96], 0);
        assert_eq!(world.carry(at(ME), again), (None, None));
        // A way through a relay that is another than the list names:
        // its answer is not taken.
        let mut wrong = world.path();
        wrong[0].0 = id_of(world.keys[1].public_key());
        let (mut way, step) = Way::begin(9, wrong, &[60; 96], 0);
        let came = world.carry(at(ME), step).0.unwrap();
        assert_eq!(way.opened(&came.bytes, &[61; 96], 0), Came::Bad);
        // What comes back that is not of the way.
        let mut way = world.open_other(11);
        assert_eq!(way.back(1, b"nothing", &[0; 96], 0), Came::Bad);
        assert_eq!(way.say(b"x").map(|s| s.kind), Some(FORWARD));
        // A way that is open goes on to one relay more, and what is
        // said along it then is said to that one.
        let fourth = (id_of(world.keys[0].public_key()), at(1));
        assert_eq!(way.extend(fourth, &[80; 96], 0), None, "not to a relay it passes already");
        let mut two = {
            let (mut way, mut step) = Way::begin(21, world.path()[..2].to_vec(), &[81; 96], 0);
            loop {
                let came = world.carry(at(ME), step).0.unwrap();
                let next = match came.kind {
                    OPENED => way.opened(&came.bytes, &[82; 96], 0),
                    _ => way.back(came.count, &came.bytes, &[83; 96], 0),
                };
                match next {
                    Came::Step(next) => step = next,
                    Came::Ready => break way,
                    other => panic!("{other:?}"),
                }
            }
        };
        let third = world.path()[2];
        let step = two.extend(third, &[84; 96], 5).unwrap();
        assert!(!two.ready() && two.say(b"x").is_none());
        let came = world.carry(at(ME), step).0.unwrap();
        assert_eq!(two.back(came.count, &came.bytes, &[85; 96], 0), Came::Ready);
        assert_eq!(two.end().1, at(3));
        let step = two.say(b"to the third").unwrap();
        let (known_by, said) = world.carry(at(ME), step).1.unwrap();
        assert_eq!((known_by.0, &said[..]), (at(2), &b"to the third"[..]));
        // A way that is no more is forgotten by each relay of it, told
        // by the one before.
        let (way, held) = (world.open_other(31), world.relays.iter().map(Relayed::len).collect::<Vec<_>>());
        let step = Step { to: way.first(), circuit: way.circuit(), kind: CLOSE, count: 0, bytes: vec![0] };
        world.carry(at(ME), step);
        let after: Vec<usize> = world.relays.iter().map(Relayed::len).collect();
        assert_eq!(after, held.iter().map(|n| n - 1).collect::<Vec<_>>());
        // A relay forgets a way nothing passes along.
        world.relays[0].prune(Limits::default().idle);
        assert!(world.relays[0].is_empty());
        assert!(!world.relays[0].holds(&(at(ME), 7)));
    }

    impl World {
        fn open_other(&mut self, circuit: u64) -> Way {
            let (mut way, mut step) = Way::begin(circuit, self.path(), &[70; 96], 0);
            loop {
                let came = self.carry(at(ME), step).0.expect("an answer comes back");
                let next = match came.kind {
                    OPENED => way.opened(&came.bytes, &[71; 96], 0),
                    _ => way.back(came.count, &came.bytes, &[72; 96], 0),
                };
                match next {
                    Came::Step(next) => step = next,
                    Came::Ready => return way,
                    other => panic!("{other:?}"),
                }
            }
        }
    }
}
