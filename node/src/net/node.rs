//! A node among its peers: what it does with each datagram that
//! arrives, and what it does as time passes.
//!
//! Like the layers under it, [`Node`] touches no socket and reads no
//! clock. It is given the time and each datagram, and hands back the
//! datagrams to send: over a socket ([`super::socket`]), or over the
//! network of its tests, where every datagram's fate is chosen.
//!
//! # Who is listened to
//!
//! A datagram says where it is from, and can lie. So (`docs/WIRE.md`,
//! 1.2):
//!
//! 1. A ping is answered whoever sends it, with a pong of the same
//!    size: answering a forged one sends its victim no more than the
//!    forger spent. Pings of our own to an address that has not proven
//!    itself are rationed, so that forged pings cannot make this node
//!    ping at the forger's pace.
//! 2. A request is answered only if it carries the token this node gave
//!    its address.
//! 3. Anything else is taken only from a peer that has answered one of
//!    our pings, and a chunk only for a fetch of ours, by its number.
//!
//! # Headers
//!
//! Every peer says in its pings how much work its chain has. While a
//! live peer claims more than the best header here, its headers are
//! fetched:
//!
//! 1. The peer is asked which of our blocks is the newest on its chain
//!    ([`Message::FindFork`]): from there its chain is news to us.
//! 2. From there to its tip, its headers are fetched as objects of up
//!    to [`super::config::Sync::headers`] each, several at once, each
//!    from another peer whose chain reaches that far. Every one is
//!    named with the tip aimed at, so that all are of one chain.
//! 3. They are checked and kept in order ([`Chain::accept_headers`]).
//!    A peer whose headers are refused takes a strike.
//!
//! A peer that claims work and does not answer for it within
//! [`super::config::Sync::header_wait`] is passed over for a while, so
//! that a false claim cannot hold a node up.
//!
//! # Blocks
//!
//! The headers kept say which bodies are wanted: those of the best
//! header's branch that the chain does not have
//! ([`Chain::missing_bodies`]). They are fetched several at once, from
//! whoever announced each or from a peer whose chain holds it, and
//! join the chain in order; one that arrives before the block below it
//! waits. A block that joins the chain is announced to every live
//! peer but the one it came from ([`Message::Block`]): each checks the
//! header, fetches the body, and announces it in turn, so that a new
//! block crosses the network in a few hops.
//!
//! A peer that serves a body that is not its header's, or a block that
//! breaks a rule, takes a strike.
//!
//! # The state, taken whole
//!
//! A node keeps bodies only for the blocks it can undo. One that is
//! further behind than its peers' bodies reach cannot be given the
//! blocks it lacks, and takes the state instead, as of a block a little
//! under the best header: that block and the top of its state, the
//! block's proof, then the state's parts, several at once from every
//! peer that can serve them, each checked against the header's root
//! before it is kept ([`crate::chain::receive`], [`super::snapshot`]).
//! Headers go on being taken throughout. If the peers can no longer go
//! back to the block, a later one is taken in its place, and the parts
//! that are the same are kept.

use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::net::{SocketAddr, SocketAddrV4};
use std::sync::atomic::{AtomicBool, AtomicU64, AtomicUsize, Ordering};
use std::sync::{Arc, Mutex, RwLock, RwLockReadGuard, RwLockWriteGuard};

use super::config::Config;
use super::message::{Locator, Message, Status};
use super::object::{MAX_NAME, Object};
use super::peers::{Peers, Totals};
use super::snapshot::{self, Manifest};
use super::{MAX_DATAGRAM, VERSION};
use crate::block::{BlockRef, BodyRef, HEADER_SIZE, Header};
use crate::chain::Chain;
use crate::chain::apply::{Applied, condemns};
use crate::chain::headers::LOCATOR;
use crate::chain::verify::ProofVerifier;
use crate::error::Error;
use crate::hash::Digest;
use crate::mempool::{Mempool, Reject};
use crate::sha256::Sha256;
use crate::store::backend::Backend;
use crate::transport::fetch::{Fetch, Poll, Why};
use crate::transport::serve::{Next, Serve};
use crate::transport::token::Tokens;
use crate::transport::wire::{Chunk, Get, Gone, Ranges};
use crate::transport::{Micros, chunk_of};
use crate::u256::U256;

/// What has happened, for whoever watches a node.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Counts {
    /// Datagrams that were no message of this network.
    pub malformed: u64,
    /// Messages not listened to: a request without its token, or
    /// something unasked from an address that has not proven itself.
    pub unheard: u64,
    /// Pings from a node of another version, or of another chain.
    pub strangers: u64,
    /// Datagrams sent.
    pub sent: u64,
    /// Times a peer was asked where its chain leaves ours.
    pub forks_asked: u64,
    /// Times the work of a best header whose block is waited for was
    /// given to be confirmed in full.
    pub confirms: u64,
    /// Objects fetched whole, and fetches given up.
    pub fetched: u64,
    pub fetches_failed: u64,
    /// Fetches given up for coming too slowly.
    pub fetches_slow: u64,
    /// Blocks' fetches that brought nothing new for too long and were
    /// gone on with by another peer.
    pub fetches_moved: u64,
    /// Chains that left ours far down and were weighed whole before
    /// any of them was kept.
    pub weighed: u64,
    /// Headers kept that were new.
    pub headers: u64,
    /// Blocks that joined the chain here, and blocks refused.
    pub blocks: u64,
    pub blocks_refused: u64,
    /// Announcements of a block sent.
    pub announced: u64,
    /// Headers announced that were given to the chain to be checked.
    pub checked: u64,
    /// States taken whole from other nodes, and times the block one was
    /// being taken as of was given up for another.
    pub states: u64,
    pub states_moved: u64,
}

impl Counts {
    fn add(&mut self, o: &Counts) {
        self.malformed += o.malformed;
        self.unheard += o.unheard;
        self.strangers += o.strangers;
        self.sent += o.sent;
        self.forks_asked += o.forks_asked;
        self.confirms += o.confirms;
        self.fetched += o.fetched;
        self.fetches_failed += o.fetches_failed;
        self.fetches_slow += o.fetches_slow;
        self.fetches_moved += o.fetches_moved;
        self.weighed += o.weighed;
        self.checked += o.checked;
        self.headers += o.headers;
        self.blocks += o.blocks;
        self.blocks_refused += o.blocks_refused;
        self.announced += o.announced;
        self.states += o.states;
        self.states_moved += o.states_moved;
    }
}

/// Objects made to be served are kept while they are being asked for:
/// so many bytes of them, the latest made or asked for first. Every
/// chunk is asked for by its object's name, and a part of the state
/// takes reading back through the blocks since to make.
const SERVED_BYTES: usize = 32 << 20;
/// And so many of them at the most, however small: each is looked for
/// among them all, for every chunk.
const SERVED_MOST: usize = 256;
/// How many states as of another block than those lately asked for are
/// made in a second: for one host, and for all. Each is made by reading
/// back through every block since; whoever takes a state asks for one,
/// and for thousands of its parts.
/// Rounds of asking every peer that says it has a state, and getting
/// it from none, after which a node that could take blocks instead
/// does ([`Worker::sync_state`]).
const FAR_ROUNDS: u32 = 3;
const PASTS_EACH: usize = 2;
const PASTS: usize = 8;
/// Chunks sent in one go before the node looks to what else there is.
const SERVE_BATCH: usize = 256;

/// An object being fetched.
struct Fetching {
    object: Object,
    from: SocketAddrV4,
    fetch: Fetch,
}

/// The height above which the work of headers is left to a proof, if
/// any is: where a node takes its state whole (`point` blocks under the
/// best header, if not 0) and its blocks' proofs vouch for the work
/// under them, those further above the chain's last block (`tip`; none
/// while a state is being received) than a state is taken under the
/// best.
fn defers(point: u32, attests: bool, tip: Option<u32>) -> Option<u32> {
    (point > 0 && attests).then(|| tip.map_or(0, |tip| tip.saturating_add(point)))
}

/// Announcements remembered: who said it had which block.
const ANNOUNCED: usize = 256;
/// Headers announced that wait to be checked at once, of one worker's
/// peers.
const ANNOUNCING: usize = 16;
/// Peers remembered to have said they lack a block they were asked for.
const LACKING: usize = 256;
/// Transactions being fetched at once by one worker, and of one peer:
/// what a peer can have a node fetch by announcing is bounded by these.
const TX_FETCHES: usize = 64;
const TX_FETCHES_EACH: usize = 8;
/// Transactions announced that wait their turn to be fetched, by one
/// worker: when there are so many, the one that has waited longest is
/// forgotten.
const TX_WANTED: usize = 1024;
/// Pooled transactions a peer new to the node is told of, the best
/// paying first: it missed their announcement.
const POOL_CATCHUP: usize = 256;
/// Blocks back from the chain's last whose outputs the pool is told
/// of, when the chain has gone over to another branch.
const POOL_LOOKS_BACK: u32 = 64;
/// How many blocks kept on side branches have who served them
/// remembered: more than branches run to between two blocks that try one.
const SIDES: usize = 256;

/// Work on the chain that takes time: given to be done, and what came
/// of it heard later ([`Applier`]).
enum Job {
    /// A block to apply: whole, and who it came from (nobody, if it
    /// was made here).
    Block { block: Vec<u8>, from: Option<SocketAddrV4>, unix: u64 },
    /// A run of headers to check and keep: from the height `first`.
    /// With `defer` their work is checked only by what each claims,
    /// and in full later, or vouched for by a proof
    /// ([`Chain::accept_headers`]).
    Headers { first: u32, headers: Vec<Header>, from: SocketAddrV4, unix: u64, defer: Option<u32> },
    /// The work of the headers from the height `from` to `best`, to
    /// check in full where it was left to a proof
    /// ([`Chain::confirm_work`]): for the state to be taken as of
    /// `target`, if for one. It is as many headers' work as lie between,
    /// and is not done by whoever holds what the workers share.
    Confirm { best: Header, from: u32, target: Option<Digest> },
    /// The block a state is to be taken as of, to check by its proof.
    Check { block: Vec<u8>, next: u64, roots: (Digest, Digest) },
    /// A state to begin to receive, as of the block of `target`.
    Begin { target: Header, next: u64, parts: Vec<(u64, Digest)>, name_parts: Vec<(u32, crate::store::trie::Part)> },
    /// A part of the outputs or of the names of that state, as it
    /// arrived, to check and keep.
    Piece { object: Object, bytes: Vec<u8>, from: SocketAddrV4 },
    /// The state, every part of it in, to make whole: with the body of
    /// its block.
    Finish { target: Digest, body: Vec<u8> },
    /// The leaves a block's header commits to, as a peer gave them when
    /// asked: to check against the header and keep. (Keeping them is a
    /// change to the file, which waits its turn behind a block being
    /// applied: not a thing to wait for between datagrams.)
    Leaves { id: Digest, leaves: Box<[[u8; 32]; crate::chain::leaves::AUX_LEAVES]>, from: SocketAddrV4 },
    /// The header of a block a peer announced, to check and keep: its
    /// work is in it, and checking that is not done between datagrams.
    Announced { header: Header, len: u32, from: SocketAddrV4, unix: u64 },
}

/// What became of one.
enum Outcome {
    Block {
        header: Header,
        /// The length of its body.
        len: u32,
        from: Option<SocketAddrV4>,
        result: Result<Applied, Error>,
    },
    Headers {
        first: u32,
        count: u32,
        /// The id of the last of them.
        last: Digest,
        from: SocketAddrV4,
        /// How many were new, and what stopped the run, if anything.
        new: usize,
        error: Option<Error>,
    },
    /// The headers' work was checked in full: whether it held.
    Confirmed {
        target: Option<Digest>,
        held: bool,
    },
    Checked {
        target: Digest,
        result: Result<(), Error>,
    },
    Begun {
        target: Digest,
        result: Result<(), Error>,
    },
    Piece {
        object: Object,
        from: SocketAddrV4,
        result: Result<(), Error>,
    },
    Finished {
        target: Digest,
        result: Result<(), Error>,
    },
    /// The header of a block announced, checked.
    Announced {
        header: Header,
        len: u32,
        from: SocketAddrV4,
        verdict: Verdict,
    },
    /// Leaves a peer gave were not what the header commits to.
    BadLeaves {
        from: SocketAddrV4,
    },
    /// Work that was no work: nothing came of it.
    Nothing,
}

/// What the header of a block announced was found to be.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Verdict {
    /// Kept: its body is wanted.
    Good,
    /// Its parent is not known here.
    Orphan,
    /// Not kept, and not the announcer's fault (or not yet known to be).
    Harmless,
    /// It breaks a rule.
    Bad,
}

fn apply<B: Backend + 'static, V: ProofVerifier + Sync>(chain: &Chain<B, V>, job: Job) -> Option<Outcome> {
    Some(match job {
        Job::Block { block, from, unix } => {
            let view = BlockRef::from_bytes(&block).ok()?;
            let result = chain.apply_block(&view, unix);
            Outcome::Block { header: *view.header(), len: (block.len() - HEADER_SIZE) as u32, from, result }
        }
        Job::Headers { first, headers, from, unix, defer } => {
            let (new, error) = chain.accept_headers_above(&headers, unix, defer);
            Outcome::Headers { first, count: headers.len() as u32, last: headers.last()?.hash(), from, new, error }
        }
        Job::Confirm { best, from, target } => {
            Outcome::Confirmed { target, held: matches!(chain.confirm_work(&best, from), Ok(Ok(_))) }
        }
        Job::Leaves { id, leaves, from } => match chain.put_aux_leaves(&id, &leaves) {
            Err(Error::AuxMismatch) => Outcome::BadLeaves { from },
            _ => Outcome::Nothing,
        },
        Job::Check { block, next, roots } => {
            let view = BlockRef::from_bytes(&block).ok()?;
            Outcome::Checked { target: view.header().hash(), result: chain.check_state_block(&view, next, &roots) }
        }
        Job::Begin { target, next, parts, name_parts } => {
            Outcome::Begun { target: target.hash(), result: chain.begin_receiving(&target, next, &parts, &name_parts) }
        }
        Job::Piece { object, bytes, from } => {
            let result = match object {
                Object::Part { index, .. } => snapshot::decode_part(&bytes, index)
                    .and_then(|(outputs, commits)| chain.put_part(index, &outputs, &commits)),
                Object::Names { index, .. } => {
                    snapshot::decode_names(&bytes).and_then(|records| chain.put_names(index, &records))
                }
                _ => return None,
            };
            Outcome::Piece { object, from, result }
        }
        Job::Finish { target, body } => Outcome::Finished { target, result: chain.finish_receiving(&body) },
        Job::Announced { header, len, from, unix } => {
            let verdict = match chain.accept_header(&header, unix) {
                Ok(_) => Verdict::Good,
                Err(Error::UnknownParent) => Verdict::Orphan,
                Err(Error::KnownInvalid | Error::SetAside | Error::TimestampTooNew { .. } | Error::Io(_)) => {
                    Verdict::Harmless
                }
                Err(_) => Verdict::Bad,
            };
            Outcome::Announced { header, len, from, verdict }
        }
    })
}

/// Whether a fetch that comes at `own` bytes a second comes too slowly
/// for the way in, where the fastest fetch comes at `fastest`, all of
/// them together at `together`, and `least` is the least asked of one
/// (none asked, if nothing): under the least, and either another comes
/// four times as fast, or all of them together come under that least.
/// Many fetches at once over a slow way in are each slow, and that is
/// no peer's fault; one that is slow while another is fast is its
/// peer's.
fn too_slow(own: u64, fastest: u64, together: u64, least: u64) -> bool {
    least > 0 && own < least && (own.saturating_mul(4) < fastest || together < least)
}

/// Tokens of those that are no peers kept at the most
/// ([`Worker::fetch_granted`]).
const GRANTS: usize = 256;
/// How many fetches begun at the word of whoever sent a datagram, with
/// nothing to show it came from where it says (the opening of a way,
/// a message offered to this node's wallet), go on at once: one more,
/// and the oldest is given up. One that is what it says is done in the
/// time a datagram takes there and back; those of a sender that is not
/// there never are.
const UNASKED: usize = 256;
/// How many messages offered to be passed on are kept count of.
const OFFERED: usize = 1024;
/// The relays of a consensus file: each one's id, and where it is.
type Relays = Vec<(Digest, Option<SocketAddrV4>)>;

/// Where the relays of `file` are: none of a file of init mode. (An
/// address written as numbers is read; a name is looked up, once.)
fn relays_of(file: Option<&crate::consensus::File>) -> Relays {
    use std::net::ToSocketAddrs;
    let Some(file) = file.filter(|f| f.mode == crate::consensus::Mode::Onion) else { return Vec::new() };
    let at = |addr: &str| {
        let looked_up = || match addr.to_socket_addrs().ok()?.find(|a| a.is_ipv4())? {
            SocketAddr::V4(a) => Some(a),
            SocketAddr::V6(_) => None,
        };
        addr.parse::<SocketAddrV4>().ok().or_else(looked_up)
    };
    file.relays.iter().map(|relay| (relay.id, at(&relay.addr))).collect()
}

/// How long a way a wallet sent by is kept with nothing coming back
/// along it.
const SEND_WAY_IDLE: Micros = 120 * crate::transport::SECOND;
/// How long a way to a node a message is to go by may take to open
/// before another of the wallet's nodes is tried.
/// How long a way kept to go on from is kept before another is made.
const SPARE_WAY_LIFE: Micros = 600 * crate::transport::SECOND;
const SPARE_WAYS: usize = 2;
/// Of how many messages passed on it is kept who gave each.
const GIVERS: usize = 65_536;
/// How long a relay that did not answer is not gone by.
const SUSPECT_FOR: Micros = 60 * crate::transport::SECOND;
/// How long a wallet has to say that a message sent down its way came,
/// before whoever gave the message is told it did not. Long enough for
/// a way of three relays over slow links there and back (a hop by
/// satellite is more than half a second each way): told too soon, the
/// giver sends again by another node what had come.
const DELIVERED_WITHIN: Micros = 5 * crate::transport::SECOND;
/// How long a way to one of a wallet's nodes may take to open before
/// another of its nodes is tried meanwhile: less than the time a way
/// that is not answered is given up after
/// ([`super::circuits::ANSWERED_WITHIN`]), with the second between two
/// looks at the ways to spare. (At that or more, a message whose turn
/// came to a node that does not answer never left it: each way there
/// was given up before it was slow, and the next begun to the same.)
const SEND_WAY_SLOW: Micros = 2 * crate::transport::SECOND;
/// The most that is kept on its way to neighbours on ways, that is
/// being asked of them at once by one worker, and that a worker
/// remembers having taken.
const LEAVING: usize = 4096;
const CARRIED: usize = 1024;
const TAKEN: usize = 1024;

/// Blocks whose leaves are asked for at one looking.
const LEAVES_AT_ONCE: usize = 16;
/// How many peers a consensus file that is voted for and not held is
/// asked of at once.
const FILE_ASKED_OF: usize = 3;

/// Parts of a state put together at the most.
const PARTS_AT_ONCE: usize = 64;

/// Puts parts of a state that arrived together (`jobs`, each a
/// [`Job::Piece`] of a part) in one step, and says of each what became
/// of it. If they are not put so, one of them not being its part, each
/// is put by itself: so that the one at fault is known.
fn apply_parts<B: Backend + 'static, V: ProofVerifier + Sync>(chain: &Chain<B, V>, jobs: Vec<Job>) -> Vec<Outcome> {
    let mut decoded = Vec::with_capacity(jobs.len());
    for job in &jobs {
        if let Job::Piece { object: Object::Part { index, .. }, bytes, .. } = job
            && let Ok((outputs, commits)) = snapshot::decode_part(bytes, *index)
        {
            decoded.push((*index, outputs, commits));
        }
    }
    decoded.sort_unstable_by_key(|d| d.0);
    let distinct = decoded.windows(2).all(|w| w[0].0 < w[1].0);
    let together: Vec<_> =
        decoded.iter().map(|(index, outputs, commits)| (*index, &outputs[..], &commits[..])).collect();
    if decoded.len() == jobs.len() && distinct && chain.put_parts(&together).is_ok() {
        let put = |job| match job {
            Job::Piece { object, from, .. } => Outcome::Piece { object, from, result: Ok(()) },
            _ => Outcome::Nothing,
        };
        return jobs.into_iter().map(put).collect();
    }
    jobs.into_iter().map(|job| apply(chain, job).unwrap_or(Outcome::Nothing)).collect()
}

/// Where work on the chain is done. Applying a block takes as long as
/// checking its proof does; a run of headers, their proofs of work; a
/// part of a state, a write to the store. A node that did any of it
/// between datagrams would answer nobody meanwhile: so a node over a
/// socket gives it to a thread of its own ([`Node::threaded`]), one
/// piece of work after another in the order given. In the tests it is
/// done in place, so that a run is the same every time.
enum Applier {
    Here(VecDeque<Outcome>),
    Thread(Mutex<std::sync::mpsc::Sender<Job>>, Mutex<std::sync::mpsc::Receiver<Outcome>>),
}

/// A state being taken whole from other nodes, in place of the blocks
/// nobody holds any more ([`crate::chain::receive`]).
pub(crate) struct Join {
    /// The block it is the state after.
    target: Header,
    id: Digest,
    /// That block, whole, once fetched, and who served it: its body is
    /// its header's, its proof is whatever they sent.
    block: Option<(Vec<u8>, SocketAddrV4)>,
    /// The top of the state in parts, checked against the block's
    /// header, and who served it.
    manifest: Option<(Manifest, SocketAddrV4)>,
    /// The block's proof has been checked, with what the manifest says
    /// of where its outputs end; or is being.
    checked: bool,
    checking: bool,
    /// The best header when it was chosen, and whether the work of the
    /// headers from the block to that one has been checked in full: no
    /// proof to come vouches for it, and nothing of the state is
    /// believed before.
    best: Header,
    worked: bool,
    /// It was begun though the blocks could be had, the chain being so
    /// far behind: no more of them are asked for.
    far: bool,
    /// The roots of the parts of each range fetched so far.
    roots: BTreeMap<u32, Vec<(u64, Digest)>>,
    /// The chain has begun to receive the state; or is beginning to.
    begun: bool,
    beginning: bool,
    /// Pieces that have arrived and are being checked and kept.
    putting: Vec<Object>,
    /// Every part is in, and the state is being made whole.
    finishing: bool,
    /// Peers that did not serve something of it: asked again only if
    /// no other can be.
    unserved: Vec<SocketAddrV4>,
    /// Which peer is asked next.
    turn: usize,
    /// How many parts the state is of, once known; and when it was
    /// last said how many are kept.
    parts: u64,
    told: Micros,
    /// Manifests that the block's proof refused.
    refused: u32,
    /// Everyone that can serve it has failed to: when they are asked
    /// again, and how many times that has come about.
    again: Option<Micros>,
    rounds: u32,
    /// Since when no peer has been able to serve it.
    orphaned: Option<Micros>,
}

/// The chain being caught up with: a tip some peer has, and its headers
/// from where its chain leaves ours.
pub(crate) struct Aim {
    /// The tip, and its height.
    tip: Digest,
    height: u32,
    /// The first heights of the runs of headers not yet asked for.
    todo: BTreeSet<u32>,
    /// Runs fetched and waiting for those before them: by first height,
    /// with who served each.
    done: BTreeMap<u32, (Vec<Header>, SocketAddrV4)>,
    /// The first height not yet kept.
    next: u32,
    /// A run is with the applier, being checked and kept.
    keeping: bool,
    /// Who told us of it: asked for its headers though its last ping
    /// said its chain was shorter.
    source: SocketAddrV4,
    /// Peers that said they have no such headers: not asked again for
    /// this, and not held to blame for it. Their chains reach the
    /// height, on another branch: only whoever told us of this one
    /// answers for it.
    refused: Vec<SocketAddrV4>,
    /// Where its chain leaves ours.
    fork: u32,
    /// A chain that leaves ours far down is weighed before any of it
    /// is kept ([`Chain::weigh`]): its headers are fetched and checked
    /// one run after another, none kept, and if it comes to more work
    /// than the best there is they are fetched again and kept. What it
    /// has come to so far, while that is being done.
    weighing: Option<crate::chain::headers::Weighed>,
}

/// What the node is after, and what is being done about it: the chain
/// being caught up with, the bodies in hand, the state being taken,
/// and the work given to be done on the chain.
///
/// This is all that is about no one peer (`docs/THREADS.md`, 4.2). It
/// is behind a lock, taken where a decision about what to fetch is
/// made or what came of one is heard: not to answer a ping, take a
/// chunk or serve one.
pub(crate) struct List {
    /// The peer asked where its chain leaves ours, when, and the block
    /// it announced that made us ask, with its height: its tip, as far
    /// as we know, though its last ping said less.
    #[allow(clippy::type_complexity)]
    probe: Option<(SocketAddrV4, Micros, Option<(Digest, u32)>)>,
    pub(crate) aim: Option<Aim>,
    applier: Applier,
    /// Work given to be done and not yet heard of.
    outstanding: usize,
    /// Blocks given to be applied and not yet heard of.
    pub(crate) applying: Vec<Digest>,
    /// Who served each block kept on a side branch, the newest last:
    /// such a block's proof is not looked at until its branch is tried,
    /// and if it does not hold then, it is they who answer for it
    /// ([`SIDES`] of them, the oldest forgotten first).
    sides: VecDeque<(Digest, SocketAddrV4)>,
    /// Bodies fetched and waiting for the blocks before them: the
    /// block whole, and who served it.
    pub(crate) held: Vec<(Digest, Vec<u8>, SocketAddrV4)>,
    /// The state being taken whole from others, if one is.
    pub(crate) join: Option<Join>,
    /// When a state may next be begun to be taken, a taking having come
    /// to nothing; and how many have, one after another. A node that is
    /// not served asks again later and later, not as fast as it is told
    /// no.
    pub(crate) rejoin: (Micros, u32),
    /// Until when no chain that leaves ours under where ours can be
    /// undone to is gone into: one was, lately.
    pub(crate) deep: Micros,
    /// What is being fetched, and of whom: whoever begins a fetch of
    /// something the node is after says so here, so that nobody else
    /// fetches the same, and so that how many are under way is known
    /// to all.
    fetching: Vec<(Object, SocketAddrV4)>,
    /// How each worker's peers stand, as that worker last said: what a
    /// decision about all of them is made on (whether anyone holds a
    /// block, how far back anyone can hand the state over).
    views: Vec<View>,
    /// A chain ahead of ours is being caught up with: said when it is
    /// begun, and when it has been.
    syncing: bool,
    /// The work of headers is being checked in full, by whoever does
    /// what takes time ([`Job::Confirm`]): one such at a time.
    confirming: bool,
    /// A block of the branch with the most work was refused because
    /// the chain cannot undo so far ([`Chain::cut_off`]): looked into
    /// before blocks are asked for, until it is so no longer.
    cut: bool,
    /// The best header whose work was last confirmed while its block
    /// was waited for ([`Worker::begin_join`]).
    waited: Option<Digest>,
}

impl List {
    fn new(workers: usize) -> List {
        List {
            probe: None,
            aim: None,
            applier: Applier::Here(VecDeque::new()),
            outstanding: 0,
            applying: Vec::new(),
            sides: VecDeque::new(),
            held: Vec::new(),
            join: None,
            rejoin: (0, 0),
            deep: 0,
            fetching: Vec::new(),
            views: vec![View::default(); workers],
            syncing: false,
            confirming: false,
            cut: false,
            waited: None,
        }
    }
}

/// How one worker's peers stand.
#[derive(Clone, Default)]
struct View {
    /// How many are live.
    live: usize,
    /// The greatest height any of them says its chain has.
    top: u32,
    /// What each that may be asked says of itself.
    able: Vec<Status>,
}

impl View {
    /// Whether one of them holds the body at `height`.
    fn holds(&self, height: u32) -> bool {
        self.able.iter().any(|s| s.oldest <= height && height <= s.height)
    }

    /// Whether one of them can hand over the state as of `height`.
    fn serves(&self, height: u32) -> bool {
        self.able.iter().any(|s| s.window <= height && s.oldest <= height && height <= s.height)
    }

    /// Whether the chain of one of them reaches `height`.
    fn reaches(&self, height: u32) -> bool {
        self.able.iter().any(|s| height <= s.height)
    }
}

/// The lowest height any peer can hand the state over as of.
fn state_reach(views: &[View]) -> Option<u32> {
    let top = views.iter().map(|v| v.top).max().unwrap_or(0);
    views.iter().flat_map(|v| &v.able).map(|s| s.window.max(s.oldest)).filter(|reach| *reach <= top).min()
}

/// What one worker leaves for another: about a peer that is the
/// other's, or for every worker to do for its own.
#[derive(Clone)]
enum Notice {
    /// An address to try.
    Try(SocketAddrV4),
    /// This peer sent what no honest peer sends.
    Strike(SocketAddrV4),
    /// A fetch from this peer failed: it is passed over a while.
    Failed(SocketAddrV4),
    /// This peer sent headers we lacked.
    SentHeaders(SocketAddrV4),
    /// This block is not to be had from this peer, though it said so.
    NotFrom(Digest, SocketAddrV4),
    /// A block joined the chain: every peer is told, but `except`.
    Announce { header: Header, len: u32, except: Option<SocketAddrV4> },
    /// What the node is after has changed: there may be something on
    /// the list that a peer of yours can serve.
    Work,
    /// The header of a block this peer of yours announced was checked.
    Announced { header: Header, len: u32, from: SocketAddrV4, verdict: Verdict },
    /// A transaction joined the pool: every peer is told, but `except`.
    Tx { id: Digest, len: u32, except: Option<SocketAddrV4> },
}

/// What the workers of a node share besides the list.
/// The states as of blocks before the last that were lately asked for
/// ([`Shared::pasts`]).
#[derive(Default)]
struct Pasts {
    /// The blocks, the latest asked for first.
    of: VecDeque<Digest>,
    /// Who asked for the state as of another, and when.
    asked: VecDeque<(std::net::Ipv4Addr, Micros)>,
}

pub(crate) struct Shared {
    /// What is left for each worker by the others.
    mail: Vec<Mutex<Vec<Notice>>>,
    /// The pace the workers serve at, all together
    /// ([`Serve::sharing`]).
    pace: Arc<AtomicU64>,
    /// The sessions this node holds for wallets, if it is one that
    /// does ([`Config::relay`]).
    sessions: Mutex<super::sessions::Sessions>,
    /// The wallet this node is the node of, on the message layer: none
    /// unless it was given one ([`Handle::participate`]).
    participant: Mutex<Option<super::sessions::Participant>>,
    /// The messages of the node: those its wallet sends, those it
    /// passes on, those that have come for its wallet.
    letters: Mutex<super::sessions::Mail>,
    /// The nodes wallets are reached at while no consensus file names
    /// others: the seeds, which all of a network have the same.
    seeds: Mutex<BTreeSet<SocketAddrV4>>,
    /// The consensus file last said to be in force: its mode, and the
    /// file's hash if there is one.
    consensus: Mutex<Option<(crate::consensus::Mode, Option<crate::consensus::Hash>)>>,
    /// What is still wanted before it is known which consensus file is
    /// in force, while that is not known: the files voted for and not
    /// held, and how many blocks' votes are missing
    /// ([`crate::consensus::Current::undecided`]).
    undecided: Mutex<Option<(Vec<crate::consensus::Hash>, u32)>>,
    /// The peers of each worker that have answered it, as it last
    /// said: for whoever keeps them from one run to the next
    /// ([`Handle::answered`]).
    answered: Vec<Mutex<Vec<SocketAddrV4>>>,
    /// Every peer of each worker, as it last stood: for whoever asks
    /// what the node sees ([`Handle::peer_list`]).
    listed: Vec<Mutex<Vec<PeerSeen>>>,
    /// The ways through relays that pass through this node, if it is
    /// one they do ([`Config::relay`]); those it opened itself; and
    /// what is on its way to a neighbour on either
    /// ([`super::circuits`]).
    relayed: Mutex<super::circuits::Relayed>,
    ways: Mutex<super::circuits::Ways>,
    /// The relays of the consensus file in force, in the file's order,
    /// each with where it is if that could be found: none while the
    /// mode is init. Wallets are then reached at the end of ways
    /// through them, and no longer at the seeds.
    relays: Mutex<Arc<Relays>>,
    /// The relays of the file that was in force before this one (none,
    /// of a time of no file), and the height of the block at which
    /// this one came into force: while the change lasts
    /// ([`Worker::changing`]).
    relays_before: Mutex<Option<(Arc<Relays>, u32)>>,
    /// Relays that did not answer the opening of a way, and when: ways
    /// go by others for a while.
    suspect: Mutex<Vec<(SocketAddrV4, Micros)>>,
    /// Sealed messages sent down a wallet's way, of which the wallet
    /// has not yet said that they came: the message, the way it went
    /// down, the way of whoever gave it, and when.
    #[allow(clippy::type_complexity)]
    delivering: Mutex<Vec<([u8; 32], (SocketAddrV4, u64), (SocketAddrV4, u64), Micros)>>,
    /// Who gave this node each message it passed on to a wallet, for
    /// a while: the message's id, and the way (or the address) it was
    /// given by. The wallet's answer goes back there, and the wallet
    /// is told nothing of it.
    givers: Mutex<VecDeque<([u8; 32], super::sessions::Where, Micros)>>,
    /// Whether those were given by whoever drives the node, and are
    /// not the chain's to change ([`Handle::force_consensus`]).
    forced: AtomicBool,
    leaving: Mutex<Vec<super::circuits::Leaving>>,
    /// What a host's address is mixed with to find its worker: so that
    /// nobody outside can choose addresses that are all one worker's.
    key: u64,
    /// What the tokens of every worker are made under: one for the
    /// node, so that a token one worker gives an address is one the
    /// worker that address belongs to honours. (What passes between
    /// wallets comes in at one worker and goes out by another.)
    token_secret: [u8; 32],
    /// The number this node is known by, whatever address it is heard
    /// from ([`Status::node`]): taken by chance at each start.
    node: u64,
    /// The nodes that are live peers, each by its number, and the
    /// address it is a peer at: a node heard of at a second address is
    /// not a second peer.
    nodes: Mutex<Vec<(u64, SocketAddrV4)>>,
    /// The node's peers in all.
    totals: Arc<Totals>,
    /// How many of each worker's peers are live, as it last counted;
    /// and which, for telling others whom the node knows.
    live: Vec<AtomicUsize>,
    known: Vec<Mutex<Vec<SocketAddrV4>>>,
    /// Work on the chain that is done and not yet heard of: so that
    /// nobody takes the list to find there is nothing.
    ready: AtomicUsize,
    /// Whether that work is done on a thread of its own.
    threaded: AtomicBool,
    /// Blocks that have joined the chain here.
    blocks: AtomicU64,
    /// Fetches that did not end with the peer they began with: given
    /// up (silent, refused, gone), too slow, or gone on with by
    /// another for bringing nothing new.
    refetched: AtomicU64,
    /// Blocks made here of which what came of them has been heard.
    settled: AtomicU64,
    /// Wakes a worker that is waiting, where each waits on a thread of
    /// its own ([`super::socket`]): called when something is left for
    /// it, so that nobody has to look to see whether anything was.
    waker: RwLock<Option<Waker>>,
    /// Whose turn it is to hear of work done on the chain.
    turn: AtomicUsize,
    /// Told of each thing that happens that a log would say.
    told: RwLock<Option<Told>>,
    /// Told whenever the chain has a new last block (`blocks` counts
    /// them): for whoever waits for that.
    moved: (Mutex<()>, std::sync::Condvar),
    /// The blocks whose states were last asked for, and who asked for
    /// the state as of another, when ([`PASTS`]). Of all the workers:
    /// the states kept made are the chain's, a few for all of them.
    pasts: Mutex<Pasts>,
    /// The transactions waiting to be mined. (Taken after the chain's
    /// state, by whoever takes both.)
    pool: Mutex<Mempool>,
    #[cfg(test)]
    by_port: AtomicBool,
    /// What names say, where a test says so in the chain's place.
    #[cfg(test)]
    pub(crate) names: Mutex<BTreeMap<Vec<u8>, Digest>>,
}

/// A peer as the node sees it: for whoever asks.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PeerSeen {
    pub addr: SocketAddrV4,
    /// A seed, or given by hand: kept whatever it does.
    pub seed: bool,
    /// Whether it has ever answered: it is at its address.
    pub answered: bool,
    /// Whether it answers now.
    pub live: bool,
    /// How high it says its chain is, if it has said.
    pub height: Option<u32>,
    /// How long ago anything came from it, if anything has.
    pub silent: Option<Micros>,
}

/// Something that happened to a node that whoever keeps its log would
/// say: a peer come or gone, the chain being caught up with, a block.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Event {
    /// A peer is live: it answered, and says its chain is this high.
    PeerConnected { peer: SocketAddrV4, height: u32 },
    /// A peer is live no longer: silent too long, gone, or refused.
    PeerLost { peer: SocketAddrV4 },
    /// A peer's host is refused: it sent what no honest peer sends
    /// once too often.
    Banned { peer: SocketAddrV4 },
    /// A chain ahead of ours is being caught up with: these headers
    /// are wanted, as this peer has them.
    HeadersWanted { from: u32, to: u32, peer: SocketAddrV4 },
    /// Those headers are kept, to this height.
    HeadersKept { height: u32 },
    /// This peer's headers were not what they should be.
    HeadersRefused { peer: SocketAddrV4 },
    /// A block's fetch from `from` brought nothing new for `quiet`
    /// microseconds, with `here` of its `of` chunks here: the rest is
    /// asked of `to`.
    FetchMoved { height: u32, from: SocketAddrV4, to: SocketAddrV4, quiet: Micros, here: u32, of: u32 },
    /// A block is the chain's new last: from this peer, or made here.
    /// If the chain went over to its branch to take it, `undone` blocks
    /// of ours gave way, and `taken` of that branch are the chain's
    /// now (this one the last of them); else none and one.
    Block { header: Header, len: u32, from: Option<SocketAddrV4>, undone: u32, taken: u32 },
    /// A block was kept on a branch with no more work than the chain's:
    /// the chain is as it was. From this peer, or made here.
    Side { header: Header, from: Option<SocketAddrV4> },
    /// A block was refused, and why: from this peer, or made here.
    BlockRefused { header: Header, from: Option<SocketAddrV4>, why: String },
    /// The chain that was being caught up with has been.
    Synced { height: u32 },
    /// The state is being taken whole, as of this block; `again` if in
    /// place of an earlier one that nobody can serve any more.
    StateWanted { height: u32, id: Digest, again: bool },
    /// A message has come for this node's wallet
    /// ([`Handle::take_messages`]).
    Mail,
    /// Which consensus file is in force is not known yet: these files
    /// are voted for and not held, and the votes of so many blocks are
    /// missing. The node keeps to what it knew.
    ConsensusUnknown { files: Vec<crate::consensus::Hash>, votes: u32 },
    /// Another consensus file is in force, or none: the mode the
    /// message layer is in from here on.
    Consensus { mode: crate::consensus::Mode, file: Option<crate::consensus::Hash> },
    /// How far the taking of the state has come: said now and then,
    /// of a state that takes long. `parts` of its `of` parts are kept.
    StateProgress { parts: u64, of: u64 },
    /// The state has been taken, as of the block of this height.
    StateTaken { height: u32 },
}

/// Told of each [`Event`].
pub type Told = Box<dyn Fn(&Event) + Send + Sync>;

/// Wakes the worker of this number.
pub(crate) type Waker = Box<dyn Fn(usize) + Send + Sync>;

impl Shared {
    /// Whether the node has a consensus file to go by (or knows there
    /// is none): what it decided, or, while that is not decided, what
    /// it knew before. Not, of a node that has never known.
    fn knows_consensus(&self) -> bool {
        let undecided = self.undecided.lock().unwrap_or_else(|e| e.into_inner()).is_some();
        !undecided || self.consensus.lock().unwrap_or_else(|e| e.into_inner()).is_some()
    }

    /// The worker `addr` belongs to: by its host, whatever the port.
    fn owner(&self, addr: &SocketAddrV4) -> usize {
        if self.mail.len() == 1 {
            return 0;
        }
        // (A mix in which every bit of the address tells on every bit
        // of the result.)
        let host = u32::from(*addr.ip()) as u64;
        // (Tests on one machine, where every node is of one host: by
        // the port too, so that its nodes are spread over the workers.)
        #[cfg(test)]
        let host = host | (addr.port() as u64 * self.by_port.load(Ordering::Relaxed) as u64) << 32;
        let mut x = (host ^ self.key).wrapping_mul(0x9e37_79b9_7f4a_7c15);
        x = (x ^ (x >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        x = (x ^ (x >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        ((x ^ (x >> 31)) % self.mail.len() as u64) as usize
    }

    /// The pool, held.
    fn pool(&self) -> std::sync::MutexGuard<'_, Mempool> {
        self.pool.lock().unwrap_or_else(|e| e.into_inner())
    }

    /// A transaction has joined the pool: every worker is to tell its
    /// peers, but the one it came from.
    fn relay(&self, id: Digest, len: u32, except: Option<SocketAddrV4>) {
        for worker in 0..self.mail.len() {
            self.post(worker, Notice::Tx { id, len, except });
        }
    }

    fn post(&self, worker: usize, notice: Notice) {
        self.mail[worker].lock().unwrap_or_else(|e| e.into_inner()).push(notice);
        self.wake(worker);
    }

    /// Says what happened, to whoever keeps a record.
    fn say(&self, event: Event) {
        if let Some(told) = &*self.told.read().unwrap_or_else(|e| e.into_inner()) {
            told(&event);
        }
    }

    /// Wakes `worker`, if workers wait.
    fn wake(&self, worker: usize) {
        if let Some(waker) = &*self.waker.read().unwrap_or_else(|e| e.into_inner()) {
            waker(worker);
        }
    }

    /// How workers are woken, or that they no longer wait.
    pub(crate) fn set_waker(&self, waker: Option<Waker>) {
        *self.waker.write().unwrap_or_else(|e| e.into_inner()) = waker;
    }

    /// The worker `addr` belongs to, as [`Shared::owner`]: for whoever
    /// hands datagrams out.
    pub(crate) fn worker_of(&self, addr: &SocketAddr) -> usize {
        match addr {
            SocketAddr::V4(a) => self.owner(a),
            SocketAddr::V6(a) => a.ip().to_ipv4_mapped().map_or(0, |ip| self.owner(&SocketAddrV4::new(ip, a.port()))),
        }
    }

    /// Tells every worker but `but` that what the node is after has
    /// changed: once, however often it is said before they look.
    fn work(&self, but: usize) {
        for worker in (0..self.mail.len()).filter(|w| *w != but) {
            let mut mail = self.mail[worker].lock().unwrap_or_else(|e| e.into_inner());
            if !mail.iter().any(|n| matches!(n, Notice::Work)) {
                mail.push(Notice::Work);
                drop(mail);
                self.wake(worker);
            }
        }
    }

    fn post_others(&self, but: usize, notice: Notice) {
        for worker in (0..self.mail.len()).filter(|w| *w != but) {
            self.post(worker, notice.clone());
        }
    }

    fn waiting(&self) -> bool {
        self.mail.iter().any(|m| !m.lock().unwrap_or_else(|e| e.into_inner()).is_empty())
    }
}

/// A run of headers.
fn headers(object: &Object) -> bool {
    matches!(object, Object::Headers { .. })
}

/// A piece of a state, but for its block.
fn of_state(object: &Object) -> bool {
    matches!(object, Object::Manifest(_) | Object::Roots { .. } | Object::Part { .. } | Object::Names { .. })
}

/// Takes `object` of `from` off what is being fetched.
fn fetched(fetching: &mut Vec<(Object, SocketAddrV4)>, object: &Object, from: &SocketAddrV4) {
    if let Some(at) = fetching.iter().position(|(o, a)| o == object && a == from) {
        fetching.swap_remove(at);
    }
}

/// What a datagram was, and what was done about it: for whoever keeps
/// a record of what a node is asked ([`Node::handle`]).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Heard {
    /// Who sent it, if its address is of a kind we speak to.
    pub from: Option<SocketAddrV4>,
    /// The message, by its name: `ping`, `get`, `block`; or
    /// `malformed`, for a datagram that was none.
    pub request: &'static str,
    /// What of it is worth a word.
    pub about: About,
    /// What was done: the answer's name where one was sent (`pong`,
    /// `peers`, `fork`); `queued` for chunks asked for, which are sent
    /// as the node's pace allows; `taken` for what needs no answer;
    /// `unheard`, `stranger` or `malformed` for what was not listened
    /// to.
    pub answer: &'static str,
    /// Datagrams sent in answering, and their bytes.
    pub sent: u32,
    pub sent_bytes: u32,
}

/// What is said of a request besides its name.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum About {
    Nothing,
    /// The height of the sender's chain, or of the block spoken of.
    Height(u32),
    /// How many addresses.
    Peers(usize),
    /// A block announced: its height, and its body's length.
    Block {
        height: u32,
        bytes: u32,
    },
    /// Chunks asked for, and of what kind of object.
    Chunks {
        of: &'static str,
        chunks: u32,
    },
}

/// A chunk of something this node is fetching: by far the most of what
/// arrives while it is, and each much like the last.
pub const CHUNK: &str = "chunk";

impl Heard {
    /// The line of the request log: who asked, how long answering took
    /// in microseconds, what was asked (in a datagram of `bytes`), and
    /// what was done.
    ///
    /// ```text
    /// 203.0.113.7:3737      41 micros       ping height 88,214 (133 bytes) -> pong (133 bytes)
    /// ```
    pub fn line(&self, bytes: usize, micros: u64) -> String {
        use crate::logger::fmt::{column, commas};
        let from = self.from.map_or_else(|| "-".to_string(), |a| a.to_string());
        let about = match self.about {
            About::Nothing => String::new(),
            About::Height(height) => format!(" height {}", commas(height as u64)),
            About::Peers(n) => format!(" of {}", commas(n as u64)),
            About::Block { height, bytes } => {
                format!(" height {} of {} bytes", commas(height as u64), commas(bytes as u64))
            }
            About::Chunks { of, chunks } => format!(" {of}, {} chunks", commas(chunks as u64)),
        };
        let sent = match self.sent {
            0 => String::new(),
            1 => format!(" ({} bytes)", commas(self.sent_bytes as u64)),
            n => format!(" ({} datagrams, {} bytes)", commas(n as u64), commas(self.sent_bytes as u64)),
        };
        format!(
            "{}{}{}{about} ({} bytes) -> {}{sent}",
            column(&from, 22, ' '),
            column(&format!("{} micros", commas(micros)), 16, ' '),
            self.request,
            commas(bytes as u64),
            self.answer
        )
    }
}

/// One of a node's workers: everything the node knows and does about
/// the hosts that are this worker's (`docs/THREADS.md`). It is given the
/// datagrams of those hosts and nobody else's.
pub struct Worker<B: Backend + 'static, V> {
    /// Which of the node's workers this is.
    me: usize,
    shared: Arc<Shared>,
    cfg: Config,
    /// The network's four bytes.
    network: [u8; 4],
    /// Its genesis block's id.
    genesis: Digest,
    chain: Arc<Chain<B, V>>,
    peers: Peers,
    tokens: Tokens,
    /// What the tokens' secrets, the pings' numbers and the fetches'
    /// are made from.
    secret: [u8; 32],
    /// How many of each have been made.
    secrets: u64,
    numbers: u64,
    /// When the tokens' secret was last replaced.
    rotated: Micros,
    /// Pings to unproven addresses still allowed before the next tick.
    budget: usize,
    /// When a peer was last asked whom else it knows.
    asked: Option<Micros>,
    /// How long until it is asked again, and how many peers the node
    /// knew when it last was.
    ask_gap: Micros,
    ask_knew: usize,
    /// The time by the calendar, in seconds: what a header's time is
    /// held against.
    unix: u64,
    /// When what passes with time is next looked to.
    due: Micros,
    serve: Serve,
    /// Objects lately made to be served, the latest first.
    served: VecDeque<(Object, Arc<Vec<u8>>)>,
    /// The object last asked for could not be read, which is not to say
    /// there is none.
    unread: std::cell::Cell<bool>,
    fetches: Vec<Fetching>,
    /// The peers that were live when that was last looked to.
    was_live: Vec<SocketAddrV4>,
    /// Tokens given to this node by those that are not its peers, to
    /// ask them for what they offered: the newest last.
    grants: VecDeque<(SocketAddrV4, u64)>,
    /// The last fetches begun at a stranger's word ([`UNASKED`]).
    unasked: VecDeque<(Object, SocketAddrV4)>,
    /// The time by the clock, as last told.
    now: Micros,
    /// What is to be said to whom when there is next a way to say it:
    /// of what was found where there was none.
    to_say: Vec<(SocketAddrV4, Message<'static>)>,
    /// Sealed messages offered to this node to pass on, being asked
    /// for: the message, whom it is for, and who offered it.
    offered: Vec<(Digest, Digest, SocketAddrV4)>,
    /// What a neighbour on a way said it has for this node, being
    /// asked for: its name, the neighbour, and the way, kind and count
    /// it was said to be of.
    carried: Vec<(u64, SocketAddrV4, u64, u8, u64)>,
    /// And what has come of those lately: what is said to be there
    /// again is not asked for again.
    taken: VecDeque<(SocketAddrV4, u64)>,
    /// What is to be said to a neighbour on a way with what it is:
    /// whom, its name, way, kind and count, and the bytes.
    #[allow(clippy::type_complexity)]
    stepping: Vec<(SocketAddrV4, u64, u64, u8, u64, Arc<Vec<u8>>)>,
    /// When a neighbour that has not taken something is next told.
    tell_due: Micros,
    /// The leaves asked for and not yet here: of which block, of whom.
    leaves_asked: Vec<(Digest, SocketAddrV4)>,
    /// When the votes were last looked to ([`Worker::follow_votes`]),
    /// and which peer is asked next.
    votes_looked: Micros,
    votes_turn: usize,
    /// The votes as last counted: what they were counted from (how
    /// often the chain had moved, and the count of changes to the
    /// leaves and files kept), the blocks whose leaves are missing, and
    /// a file voted for that is not held.
    #[allow(clippy::type_complexity)]
    votes: Option<((u64, u64), Vec<Digest>, Option<crate::consensus::Hash>)>,
    /// What is about no one peer.
    list: Arc<RwLock<List>>,
    /// Who announced which block, and how long its body is: the newest
    /// last.
    announced: VecDeque<(Digest, SocketAddrV4, u32)>,
    /// Who said it has not a block it was asked for, having never said
    /// it had: not asked for that block again.
    lacking: Vec<(Digest, SocketAddrV4)>,
    /// The peers a block's fetch was last moved from, for having
    /// brought nothing new, and when: one it happens to again while
    /// that is remembered is passed over.
    quieted: Vec<(SocketAddrV4, Micros)>,
    /// Headers announced that were given to be checked, and are not
    /// yet heard of.
    announcing: usize,
    /// What came of the fetches asked for from outside
    /// ([`Node::fetch_object`]).
    inbox: Vec<(Object, SocketAddrV4, Option<Vec<u8>>)>,
    /// Transactions announced and not yet fetched: which, by whom, and
    /// how long each is. The first to wait is the first fetched.
    tx_wanted: VecDeque<(Digest, SocketAddrV4, u32)>,
    counts: Counts,
    /// Tests: a chain's work claimed that is not there; objects served
    /// with a byte wrong.
    #[cfg(test)]
    pub(crate) boast: Option<U256>,
    #[cfg(test)]
    pub(crate) spoil: bool,
    /// Tests: nothing of a state is handed over, though the node says
    /// it can.
    #[cfg(test)]
    pub(crate) withhold: bool,
    /// Tests: a height claimed that the chain has not.
    #[cfg(test)]
    pub(crate) tall: Option<u32>,
    /// Tests: a block served that is on no chain here.
    #[cfg(test)]
    pub(crate) foist: Option<(Digest, Vec<u8>)>,
}

/// A datagram to send goes to this.
pub type Out<'a> = &'a mut dyn FnMut(SocketAddrV4, &[u8]);

impl<B: Backend + 'static, V: ProofVerifier + Sync> Worker<B, V> {
    /// A node of the network `network` keeping `chain`, with these
    /// settings. `secret` is from the operating system's random source:
    /// the tokens this node gives, the numbers of its pings and those
    /// of its fetches come of it, and nobody is to foretell any.
    #[allow(clippy::too_many_arguments)]
    fn new(
        cfg: Config,
        network: [u8; 4],
        chain: Arc<Chain<B, V>>,
        secret: [u8; 32],
        now: Micros,
        me: usize,
        shared: Arc<Shared>,
        list: Arc<RwLock<List>>,
    ) -> Worker<B, V> {
        let seed = u64::from_le_bytes(derive(&secret, b's', 0)[..8].try_into().unwrap());
        let pace = Arc::clone(&shared.pace);
        let tokens = Tokens::new(derive(&shared.token_secret, b't', now / cfg.serve.token_life.max(1)));
        let lives = now / cfg.serve.token_life.max(1);
        Worker {
            me,
            peers: Peers::sharing(&cfg, seed, Arc::clone(&shared.totals)),
            shared,
            budget: cfg.peers.unproven_pings,
            serve: Serve::with(cfg.serve.limits()).sharing(pace),
            cfg,
            network,
            genesis: chain.params().genesis().header.hash(),
            chain,
            tokens,
            secret,
            secrets: lives,
            numbers: 0,
            rotated: now,
            asked: None,
            ask_gap: 0,
            ask_knew: 0,
            unix: 0,
            due: now,
            served: VecDeque::new(),
            unread: std::cell::Cell::new(false),
            fetches: Vec::new(),
            was_live: Vec::new(),
            grants: VecDeque::new(),
            unasked: VecDeque::new(),
            now,
            to_say: Vec::new(),
            offered: Vec::new(),
            carried: Vec::new(),
            taken: VecDeque::new(),
            stepping: Vec::new(),
            tell_due: Micros::MAX,
            leaves_asked: Vec::new(),
            votes_looked: 0,
            votes_turn: 0,
            votes: None,
            list,
            announced: VecDeque::new(),
            lacking: Vec::new(),
            quieted: Vec::new(),
            announcing: 0,
            inbox: Vec::new(),
            tx_wanted: VecDeque::new(),
            counts: Counts::default(),
            #[cfg(test)]
            boast: None,
            #[cfg(test)]
            withhold: false,
            #[cfg(test)]
            tall: None,
            #[cfg(test)]
            spoil: false,
            #[cfg(test)]
            foist: None,
        }
    }

    /// A block made here: applied, and if it joins the chain, announced.
    fn mined(&mut self, block: Vec<u8>) {
        let list = Arc::clone(&self.list);
        self.give(&mut write(&list), block, None);
    }

    /// Tells whichever worker `addr` is of what is to be done about it:
    /// done here and now, if it is this one's.
    fn tell(&mut self, now: Micros, addr: SocketAddrV4, notice: Notice) {
        match self.shared.owner(&addr) {
            owner if owner == self.me => self.told(now, notice),
            owner => self.shared.post(owner, notice),
        }
    }

    /// Live peers other than `except`, picked at random, as many as fit
    /// one message: of the whole node's, whichever worker is asked.
    fn sample(&mut self, except: SocketAddrV4, now: Micros) -> super::message::Addrs {
        if self.shared.known.len() == 1 {
            return self.peers.sample(Some(except), now);
        }
        // This worker's as they are now; the others' as each last said.
        let mut all: Vec<SocketAddrV4> = self.peers.live(now).map(|p| p.addr).collect();
        for (_, known) in self.shared.known.iter().enumerate().filter(|(w, _)| *w != self.me) {
            all.extend_from_slice(&known.lock().unwrap_or_else(|e| e.into_inner()));
        }
        all.retain(|a| *a != except);
        let mut out = super::message::Addrs::new();
        for i in 0..all.len() {
            let j = i + (Self::number(&self.secret, &mut self.numbers) % (all.len() - i) as u64) as usize;
            all.swap(i, j);
            if !out.push(all[i]) {
                break;
            }
        }
        out
    }

    /// A strike against a peer of this worker's: and if it was one too
    /// many, its host is refused, and that is said.
    fn strike(&mut self, addr: &SocketAddrV4, now: Micros) -> bool {
        let banned = self.peers.strike(addr, now);
        if banned {
            self.shared.say(Event::Banned { peer: *addr });
        }
        banned
    }

    /// Does what a notice says, of a peer of this worker's.
    fn told(&mut self, now: Micros, notice: Notice) {
        match notice {
            Notice::Try(addr) => {
                let _ = self.peers.add(addr, false, now);
            }
            Notice::Strike(addr) => {
                self.strike(&addr, now);
            }
            Notice::Failed(addr) => self.peers.failed(&addr, now),
            Notice::SentHeaders(addr) => self.peers.headers_arrived(&addr),
            Notice::NotFrom(id, addr) => self.announced.retain(|(told, from, _)| !(*told == id && *from == addr)),
            // (Seen to where there is somewhere to send: `mail`.)
            Notice::Announce { .. } | Notice::Work | Notice::Announced { .. } | Notice::Tx { .. } => {}
        }
    }

    /// What other workers have left for this one.
    fn mail(&mut self, now: Micros, out: Out<'_>) {
        let notices = std::mem::take(&mut *self.shared.mail[self.me].lock().unwrap_or_else(|e| e.into_inner()));
        for notice in notices {
            match notice {
                Notice::Announce { header, len, except } => self.announce(now, header, len, except, out),
                Notice::Tx { id, len, except } => self.announce_tx(now, id, len, except, out),
                Notice::Announced { header, len, from, verdict } => {
                    self.announcing = self.announcing.saturating_sub(1);
                    let list = Arc::clone(&self.list);
                    self.header_checked(&mut write(&list), now, header, len, from, verdict, out);
                }
                Notice::Work => {
                    let list = Arc::clone(&self.list);
                    let l = &mut *write(&list);
                    self.fetch_headers(l, now);
                    self.sync_blocks(l, now);
                    self.advance_join(l, now);
                }
                other => self.told(now, other),
            }
        }
    }

    /// How this worker's peers stand, for the others to see.
    fn view(&self, l: &mut List, now: Micros) {
        let view = &mut l.views[self.me];
        view.live = self.peers.live(now).count();
        view.top = self.peers.live(now).filter_map(|p| p.status).map(|s| s.height).max().unwrap_or(0);
        view.able.clear();
        view.able.extend(self.peers.able(now).filter_map(|p| p.status));
    }

    /// Gives a block to be applied.
    fn give(&mut self, l: &mut List, block: Vec<u8>, from: Option<SocketAddrV4>) {
        let Ok(header) = BlockRef::from_bytes(&block).map(|b| *b.header()) else {
            return;
        };
        l.applying.push(header.hash());
        self.work(l, Job::Block { block, from, unix: self.unix });
    }

    /// Gives work to be done on the chain: what comes of it is heard
    /// in [`Node::applied`].
    fn work(&mut self, l: &mut List, job: Job) {
        work(&self.chain, &self.shared, l, job);
    }

    /// Whether work given to be done on the chain is still to be heard
    /// of: whoever drives the node then looks to it again soon, without
    /// waiting for a datagram.
    /// A number nobody can foretell: for a ping, since a pong that
    /// carries it is taken to show its sender received the ping; for a
    /// fetch, since a chunk that carries it is taken to be its answer.
    fn number(secret: &[u8; 32], numbers: &mut u64) -> u64 {
        *numbers += 1;
        u64::from_le_bytes(derive(secret, b'n', *numbers)[..8].try_into().unwrap())
    }

    /// What this node says of itself to `to`, answering or asking with
    /// `nonce`.
    fn status(&self, to: &SocketAddrV4, nonce: u64) -> Status {
        // A store that cannot be read says the least there is to say.
        let tip = self.chain.tip().unwrap_or_else(|_| self.chain.params().genesis().header);
        let work = self.chain.tip_work().unwrap_or(U256::ZERO);
        #[cfg(test)]
        let work = self.boast.unwrap_or(work);
        // Bodies are kept for the blocks that can be undone, and no
        // further back: below those a node has headers only. And no
        // further back than they are in fact kept, and can in fact be
        // undone: a node that took its state whole has nothing from
        // under that block, and one that said it had would be asked
        // for it, and those who asked would take it that someone has.
        let keep = self.chain.keep() as u32;
        let (bodies, undo) = self.chain.held().unwrap_or((None, None));
        // (The first block there is a body of is the chain's first: a
        // node that has that has them all.)
        let bodies = bodies.map(|lowest| if lowest <= 1 { 0 } else { lowest });
        let oldest = (tip.height + 1).saturating_sub(keep).max(bodies.unwrap_or(tip.height + 1));
        let window = tip.height.saturating_sub(keep).max(undo.map_or(tip.height, |first| first.saturating_sub(1)));
        Status {
            nonce,
            version: VERSION,
            token: self.tokens.issue(&SocketAddr::V4(*to)),
            genesis: self.genesis,
            #[cfg(test)]
            height: self.tall.unwrap_or(tip.height),
            #[cfg(not(test))]
            height: tip.height,
            oldest,
            window,
            tip: tip.hash(),
            work,
            node: self.shared.node,
        }
    }

    /// Whether the node of number `node`, heard from `from`, is one
    /// this node has as a live peer at another address already: then
    /// that address is the peer, and this one is not. (The first it
    /// was live at: which is the one it was given, of a node told its
    /// peers.) If not, `from` is where that node is a peer from here
    /// on.
    fn peer_elsewhere(&self, node: u64, from: SocketAddrV4) -> bool {
        let mut nodes = self.shared.nodes.lock().unwrap_or_else(|e| e.into_inner());
        let live = |addr: &SocketAddrV4| {
            let known = |of: &Mutex<Vec<SocketAddrV4>>| of.lock().unwrap_or_else(|e| e.into_inner()).contains(addr);
            self.was_live.binary_search(addr).is_ok() || self.shared.known.iter().any(known)
        };
        match nodes.iter_mut().find(|known| known.0 == node) {
            Some((_, at)) if *at != from && live(at) => true,
            Some((_, at)) => {
                *at = from;
                false
            }
            None => {
                // (No more remembered than there can be peers of.)
                if nodes.len() >= 4096 {
                    nodes.remove(0);
                }
                nodes.push((node, from));
                false
            }
        }
    }

    fn send(&mut self, to: SocketAddrV4, message: &Message<'_>, out: Out<'_>) {
        let mut buf = [0u8; MAX_DATAGRAM];
        let n = message.encode(self.network, &mut buf);
        self.counts.sent += 1;
        out(to, &buf[..n]);
    }

    /// [`Node::fetch_granted`], at the word of a sender that has shown
    /// nothing of where it is: one of [`UNASKED`] at the most.
    fn fetch_unasked(&mut self, now: Micros, object: Object, from: SocketAddrV4, most: u32, grant: u64) {
        if self.unasked.len() >= UNASKED
            && let Some((old, whom)) = self.unasked.pop_front()
        {
            self.fetches.retain(|f| !(f.object == old && f.from == whom));
            if let Object::Step(name) = old {
                self.carried.retain(|c| (c.0, c.1) != (name, whom));
            }
        }
        self.unasked.push_back((object, from));
        self.fetch_granted(now, object, from, most, grant);
    }

    /// Asks `from`, which is no peer but gave this node the token
    /// `grant` to ask it with, for `object`, of `most` bytes at the
    /// most.
    fn fetch_granted(&mut self, now: Micros, object: Object, from: SocketAddrV4, most: u32, grant: u64) {
        self.grants.retain(|g| g.0 != from);
        self.grants.push_back((from, grant));
        if self.grants.len() > GRANTS {
            self.grants.pop_front();
        }
        let path = self.peers.get(&from).map(|p| p.path).unwrap_or_default();
        let transfer = Self::number(&self.secret, &mut self.numbers);
        self.fetches.push(Fetching { object, from, fetch: Fetch::new(transfer, None, most, path, now) });
    }

    /// Keeps this node's wallet reached: says to each of the nodes it
    /// is reached at that it is there, as often as is due; makes it
    /// another key in time; and lets the nodes it is no longer reached
    /// at forget it.
    ///
    /// The nodes are the seeds, while no consensus file names others:
    /// all of them, where they are two or three, as they are meant to
    /// be (of more, three chosen by the wallet's id and the epoch).
    /// Whoever sends to the wallet tries one of them by chance, and
    /// another if that one does not answer. A node the wallet is
    /// reached at need not be a peer of this one, and nothing here asks
    /// whether it is: it is an address, which gives its own token to
    /// whoever says to it that a wallet is there. (Whichever worker
    /// comes to it first says so: what is due is due once.)
    fn keep_sessions(&mut self, now: Micros, out: Out<'_>) {
        let relays = self.relays();
        // While a change of consensus file lasts, the wallet is
        // reached by the nodes of both files: by ways to the relays of
        // whichever names relays, and at the seeds for whichever names
        // none. (A node that is both is reached by a way: it passes on
        // what comes for the wallet whichever way that came.)
        let before = self.changing().map(|c| c.0);
        let named: Vec<Arc<Relays>> =
            [Some(Arc::clone(&relays)), before.clone()].into_iter().flatten().filter(|list| !list.is_empty()).collect();
        let seeds_too = relays.is_empty() || before.as_ref().is_some_and(|list| list.is_empty());
        let seeds: Vec<SocketAddrV4> =
            self.shared.seeds.lock().unwrap_or_else(|e| e.into_inner()).iter().copied().collect();
        let height = self.chain.tip().map_or(0, |tip| tip.height);
        let ids: Vec<Digest> = {
            let wallet = self.shared.participant.lock().unwrap_or_else(|e| e.into_inner());
            let Some(own) = wallet.as_ref() else { return };
            [own.id()].into_iter().chain(own.aliases().into_iter().map(|alias| alias.0)).collect()
        };
        // Where each of them has the wallet: the relays' addresses,
        // and the seeds that are none of those.
        let mut by_ways: Vec<SocketAddrV4> = Vec::new();
        for list in &named {
            for id in &ids {
                for epoch in crate::msg::reached_epochs(height) {
                    by_ways.extend(Self::points_among(id, epoch, list).into_iter().map(|point| point.1));
                }
            }
        }
        let at_seeds: Vec<SocketAddrV4> = match seeds_too {
            true => ids
                .iter()
                .flat_map(|id| crate::msg::reached_points(id, height, seeds.len()))
                .map(|i| seeds[i])
                .filter(|seed| !by_ways.contains(seed))
                .collect(),
            false => Vec::new(),
        };
        if !named.is_empty() {
            self.keep_sessions_by_ways(now, &named, &at_seeds);
        }
        if !seeds_too {
            return;
        }
        // (No way is kept of a time when wallets were reached by them.)
        if named.is_empty() {
            let mut ways = self.shared.ways.lock().unwrap_or_else(|e| e.into_inner());
            ways.give_up(|w| w.purpose != super::circuits::Purpose::Asked);
        }
        let mut wallet = self.shared.participant.lock().unwrap_or_else(|e| e.into_inner());
        let Some(own) = wallet.as_mut() else { return };
        // (The nodes the wallet is reached at: by its id, and by the id
        // of each full name it is. At every one of them it says it is
        // there; at those of a name, that it is that name too.)
        let at = |id: &Digest| -> Vec<SocketAddrV4> {
            let points = crate::msg::reached_points(id, height, seeds.len()).into_iter().map(|i| seeds[i]);
            points.filter(|seed| !by_ways.contains(seed)).collect()
        };
        let mut points = at(&own.id());
        let names: Vec<(Digest, u64, Vec<SocketAddrV4>)> =
            own.aliases().into_iter().map(|(n, seq)| (n, seq, at(&n))).collect();
        for node in names.iter().flat_map(|name| &name.2) {
            if !points.contains(node) {
                points.push(*node);
            }
        }
        // (Kept at those, and at the relays it is reached at by ways.)
        let kept: Vec<SocketAddrV4> = points.iter().chain(&by_ways).copied().collect();
        own.keep(&kept);
        let mut chance = [0u8; 64];
        if crate::random::fill(&mut chance).is_ok() {
            own.rotate(&chance, now);
        }
        let mut due = Vec::new();
        for node in points {
            if self.shared.owner(&node) != self.me || !own.due(&node, now, self.cfg.keepalive) {
                continue;
            }
            // (Before the node has said its token: asked for it.)
            match own.token(&node) {
                0 => {
                    own.greet(node, now);
                    due.push((node, 0, 0));
                }
                token => due.push((node, token, own.say(node, token, self.unix, now))),
            }
        }
        let mut shown = Vec::new();
        for (n, seq, nodes) in &names {
            for node in nodes.iter().filter(|node| self.shared.owner(node) == self.me) {
                if own.alias_due(n, node, now) {
                    own.alias_shown(n, *node, now);
                    shown.push((*node, own.token(node), *n, *seq));
                }
            }
        }
        let id = own.id();
        drop(wallet);
        for (node, token, seq) in due {
            let grant = self.tokens.issue(&SocketAddr::V4(node));
            self.send(node, &Message::Session { token, grant, id, seq }, out);
        }
        for (node, token, n, seq) in shown {
            let grant = self.tokens.issue(&SocketAddr::V4(node));
            self.send(node, &Message::Alias { token, grant, n, seq }, out);
        }
        if self.cfg.relay {
            self.shared.sessions.lock().unwrap_or_else(|e| e.into_inner()).prune(now);
        }
    }

    /// Puts `step` on its way to the neighbour it is for: kept until
    /// that neighbour asks for it, which it is told to.
    fn carry(&mut self, now: Micros, mut step: super::circuits::Step) {
        let mut leaving = self.shared.leaving.lock().unwrap_or_else(|e| e.into_inner());
        if leaving.len() >= LEAVING {
            return;
        }
        let name = Self::number(&self.secret, &mut self.numbers);
        let bytes = Arc::new(std::mem::take(&mut step.bytes));
        match Self::said_whole(&step, bytes.len()) {
            true => self.stepping.push((step.to, name, step.circuit, step.kind, step.count, Arc::clone(&bytes))),
            false => self.to_say.push((step.to, self.carrying(name, &step, bytes.len()))),
        }
        self.tell_due = self.tell_due.min(now + super::circuits::TELL_AGAIN);
        leaving.push(super::circuits::Leaving { name, step, bytes, told: Some(now), asked: false, since: now });
    }

    /// Whether a thing is said to the neighbour with what it is, and
    /// not left to be asked for: what is small, of a way the two know
    /// already. (What opens a way is asked for: whoever asks is where
    /// it says it is, and a way is not made for whoever is not.)
    fn said_whole(step: &super::circuits::Step, len: usize) -> bool {
        use super::circuits::{BACK, FORWARD};
        matches!(step.kind, FORWARD | BACK | super::circuits::CLOSE) && len <= super::message::MAX_STEPPED
    }

    /// What a neighbour is told of something that is there for it.
    fn carrying(&self, name: u64, step: &super::circuits::Step, len: usize) -> Message<'static> {
        let grant = self.tokens.issue(&SocketAddr::V4(step.to));
        Message::Carry { grant, name, circuit: step.circuit, kind: step.kind, count: step.count, len: len as u32 }
    }

    /// Looks to the ways of this node: begins those asked for, sends
    /// what is to be said along them, and tells again the neighbours
    /// that have not asked for what is there for them.
    fn drive_ways(&mut self, now: Micros) {
        use super::circuits::{KEPT, TELL_AGAIN, Way};
        let mut steps = Vec::new();
        let mut ways = self.shared.ways.lock().unwrap_or_else(|e| e.into_inner());
        for (circuit, path) in std::mem::take(&mut ways.wanted) {
            let mut chance = [0u8; 96];
            if crate::random::fill(&mut chance).is_ok() {
                let (way, step) = Way::begin(circuit, path, &chance, now);
                ways.open.push(way);
                steps.push(step);
            }
        }
        for (circuit, said) in std::mem::take(&mut ways.to_say) {
            let way = ways.open.iter_mut().find(|w| w.circuit() == circuit);
            steps.extend(way.and_then(|way| way.say(&said)));
        }
        // (The first relay of each way given up is told it is no more.)
        for (to, circuit) in std::mem::take(&mut ways.closed) {
            steps.push(super::circuits::Step { to, circuit, kind: super::circuits::CLOSE, count: 0, bytes: vec![0] });
        }
        drop(ways);
        for step in steps {
            self.carry(now, step);
        }
        let mut leaving = self.shared.leaving.lock().unwrap_or_else(|e| e.into_inner());
        leaving.retain(|l| now.saturating_sub(l.since) < KEPT);
        let mut again = Vec::new();
        self.tell_due = Micros::MAX;
        for l in leaving.iter_mut().filter(|l| !l.asked) {
            if self.shared.owner(&l.step.to) != self.me {
                continue;
            }
            if l.told.is_none_or(|told| now.saturating_sub(told) >= TELL_AGAIN) {
                l.told = Some(now);
                match Self::said_whole(&l.step, l.bytes.len()) {
                    true => {
                        let step = &l.step;
                        self.stepping.push((
                            step.to,
                            l.name,
                            step.circuit,
                            step.kind,
                            step.count,
                            Arc::clone(&l.bytes),
                        ));
                    }
                    false => again.push((l.step.to, self.carrying(l.name, &l.step, l.bytes.len()))),
                }
            }
            self.tell_due = self.tell_due.min(l.told.unwrap_or(now) + TELL_AGAIN);
        }
        drop(leaving);
        self.to_say.extend(again);
    }

    /// Something carried along a way has come from the neighbour at
    /// `from`. Of a way through this node: passed on, as the way has
    /// it. Of a way this node opened: taken as what came back.
    fn step_arrived(&mut self, now: Micros, from: SocketAddrV4, name: u64, bytes: &[u8]) {
        let Some(at) = self.carried.iter().position(|c| c.0 == name && c.1 == from) else { return };
        let (_, _, circuit, kind, count) = self.carried.swap_remove(at);
        self.taken.push_back((from, name));
        if self.taken.len() > TAKEN {
            self.taken.pop_front();
        }
        self.step_taken(now, from, circuit, kind, count, bytes);
    }

    /// The same, of whatever way it came by: asked for, or said whole.
    fn step_taken(&mut self, now: Micros, from: SocketAddrV4, circuit: u64, kind: u8, count: u64, bytes: &[u8]) {
        use super::circuits::{BACK, FORWARD, OPEN, OPENED, Out};
        let mut chance = [0u8; 96];
        if crate::random::fill(&mut chance).is_err() {
            return;
        }
        let fresh = Self::number(&self.secret, &mut self.numbers);
        let link = (from, circuit);
        let mut relayed = self.shared.relayed.lock().unwrap_or_else(|e| e.into_inner());
        let step = match kind {
            OPEN => {
                let wallet = self.shared.participant.lock().unwrap_or_else(|e| e.into_inner());
                let Some(own) = wallet.as_ref() else { return };
                let chance: &[u8; 32] = chance[..32].try_into().expect("32 bytes");
                // (Of the file in force, or of the one before while
                // the change lasts.)
                let before = self.changing().map(|c| c.0);
                let listed =
                    self.relays().iter().chain(before.iter().flat_map(|b| b.iter())).any(|r| r.1 == Some(from));
                relayed.open(own.identity(), from, circuit, bytes, chance, listed, now)
            }
            FORWARD => match relayed.forward(from, circuit, count, bytes.to_vec(), fresh, now) {
                Out::Step(step) => Some(step),
                // Said to this node, the last of the way.
                Out::Said { way, said } => {
                    drop(relayed);
                    return self.said_to_point(now, way, &said);
                }
                Out::Nothing => None,
            },
            super::circuits::CLOSE => relayed.close(from, circuit),
            OPENED if relayed.goes_on_to(&link) => relayed.opened(from, circuit, bytes, now),
            BACK if relayed.goes_on_to(&link) => relayed.back(from, circuit, count, bytes.to_vec(), now),
            _ => {
                drop(relayed);
                return self.came_back(now, link, kind, count, bytes, &chance);
            }
        };
        drop(relayed);
        if let Some(step) = step {
            self.carry(now, step);
        }
    }

    /// Something has come back along a way this node opened, known to
    /// its first relay as `link`.
    fn came_back(
        &mut self,
        now: Micros,
        link: (SocketAddrV4, u64),
        kind: u8,
        count: u64,
        bytes: &[u8],
        chance: &[u8; 96],
    ) {
        use super::circuits::{Came, OPENED};
        let mut ways = self.shared.ways.lock().unwrap_or_else(|e| e.into_inner());
        let Some(at) = ways.open.iter().position(|w| (w.first(), w.circuit()) == link) else { return };
        let came = match kind {
            OPENED => ways.open[at].opened(bytes, chance, now),
            _ => ways.open[at].back(count, bytes, chance, now),
        };
        match came {
            Came::Step(step) => {
                drop(ways);
                self.carry(now, step);
            }
            Came::Said(said) => {
                let (purpose, point) = (ways.open[at].purpose, ways.open[at].end().1);
                drop(ways);
                self.said_by_point(now, link.1, purpose, point, said);
            }
            Came::Ready | Came::Late => {}
            // (A way being opened that is answered wrongly is no way.
            // One that is open stays so: what does not open on it is
            // nothing.)
            Came::Bad if !ways.open[at].ready() => drop(ways.give_up(|w| (w.first(), w.circuit()) == link)),
            Came::Bad => {}
        }
    }

    /// The token the node at `node` gave this one: as a peer, or when
    /// it was last said to that a wallet is there.
    fn token_of(&self, node: &SocketAddrV4) -> Option<u64> {
        let granted = || self.grants.iter().rev().find(|g| g.0 == *node).map(|g| g.1);
        self.peers.get(node).and_then(|p| p.token()).or_else(granted)
    }

    /// What the name `name` says on the chain: the id of whoever
    /// holds it.
    fn name_value(&self, name: &[u8]) -> Option<Digest> {
        #[cfg(test)]
        if let Some(value) = self.shared.names.lock().unwrap().get(name) {
            return Some(*value);
        }
        let key = crate::name::name_key(name).ok()?;
        let state = self.chain.whole().ok()?;
        let snap = state.snapshot().ok()?;
        snap.name(key).ok()?.filter(|record| record.name.as_bytes() == name).map(|record| record.value)
    }

    /// The relays that lately did not answer the opening of a way.
    fn suspects(&self) -> Vec<SocketAddrV4> {
        self.shared.suspect.lock().unwrap_or_else(|e| e.into_inner()).iter().map(|s| s.0).collect()
    }

    /// The relays in force: none in init mode.
    fn relays(&self) -> Arc<Relays> {
        Arc::clone(&self.shared.relays.lock().unwrap_or_else(|e| e.into_inner()))
    }

    /// While a change of consensus file lasts: the relays of the file
    /// before (none, if there was no file), and whether whoever sends
    /// still goes by those.
    ///
    /// A file comes into force at a block `B`, and each node goes over
    /// to it when it has that block, which is not the same moment for
    /// all. So for a few blocks a wallet is reached by the nodes of
    /// both files (from `B` until `B + grace - 2`), and whoever sends
    /// goes by the old ones until `B +` [`crate::consensus::SWITCH`]
    /// and by the new ones after: whichever of two nodes is a block or
    /// two ahead, the one looks where the other is.
    fn changing(&self) -> Option<(Arc<Relays>, bool)> {
        use crate::consensus::SWITCH;
        let mut before = self.shared.relays_before.lock().unwrap_or_else(|e| e.into_inner());
        let (was, at) = before.clone()?;
        let height = self.chain.tip().map_or(0, |tip| tip.height);
        let grace = self.cfg.grace.max(SWITCH + 1);
        // (Over; or the chain has gone back under the block that
        // decided it, and what is in force is decided afresh.)
        if height + 2 > at + grace || height < at {
            *before = None;
            return None;
        }
        Some((was, height < at + SWITCH))
    }

    /// The relays whoever sends goes by: those in force, or, in the
    /// first blocks of a change, those of the file before
    /// ([`Worker::changing`]).
    fn relays_to_send_by(&self) -> Arc<Relays> {
        match self.changing() {
            Some((before, true)) => before,
            _ => self.relays(),
        }
    }

    /// Which of `relays` the wallet of id `id` is reached at in the
    /// epoch `epoch`: those of them that are known where they are.
    fn points_among(id: &Digest, epoch: u32, relays: &Relays) -> Vec<(Digest, SocketAddrV4)> {
        let chosen = crate::msg::points(id, epoch, relays.len()).into_iter();
        chosen.filter_map(|i| Some((relays[i].0, relays[i].1?))).collect()
    }

    /// Begins a way to the relay `point` for `purpose`, through two
    /// others of `relays` drawn by chance (or as many as there are):
    /// not `own`, which is this node's wallet, if it is a relay too.
    /// What is to be sent to begin it.
    fn begin_way(
        &mut self,
        ways: &mut super::circuits::Ways,
        purpose: super::circuits::Purpose,
        relays: &Relays,
        point: Option<(Digest, SocketAddrV4)>,
        own: &Digest,
        now: Micros,
    ) -> Option<super::circuits::Step> {
        let mut chance = [0u8; 96 + 16];
        crate::random::fill(&mut chance).ok()?;
        let not_it = |id: &Digest| point.is_none_or(|p| p.0 != *id) && id != own;
        let mut others: Vec<(Digest, SocketAddrV4)> =
            relays.iter().filter(|r| not_it(&r.0)).filter_map(|r| Some((r.0, r.1?))).collect();
        // (Not by relays that lately did not answer, while there are
        // others: by one relay rather than by two of which one is not
        // there.)
        let suspect = self.suspects();
        if others.iter().any(|relay| !suspect.contains(&relay.1)) {
            others.retain(|relay| !suspect.contains(&relay.1));
        }
        let mut path = Vec::with_capacity(3);
        for draw in chance[96..].chunks(8).take(others.len().min(2)) {
            let at = u64::from_le_bytes(draw.try_into().expect("eight bytes")) as usize % others.len();
            path.push(others.swap_remove(at));
        }
        path.extend(point);
        if path.is_empty() {
            return None;
        }
        let circuit = Self::number(&self.secret, &mut self.numbers);
        let (mut way, step) = super::circuits::Way::begin(circuit, path, chance[..96].try_into().expect("96"), now);
        way.purpose = purpose;
        ways.open.push(way);
        Some(step)
    }

    /// Keeps this node's wallet reached while relays are in force: at
    /// the end of a way to each of the relays it is reached at, opened
    /// if there is none, said along as often as is due, and opened
    /// again if nothing comes back along it. (Whichever worker comes
    /// to it: what the ways are is the node's.)
    ///
    /// `lists` are the relays of the file in force and, while a change
    /// lasts, of the one before, whichever of them names any; `also`
    /// the seeds the wallet is reached at besides, as before relays
    /// were in force, which are kept by whoever keeps those.
    fn keep_sessions_by_ways(&mut self, now: Micros, lists: &[Arc<Relays>], also: &[SocketAddrV4]) {
        use super::circuits::{HERE, Purpose, STILL};
        // (Ways go through the relays of either.)
        let mut all: Relays = Vec::new();
        for relay in lists.iter().flat_map(|list| list.iter()) {
            if !all.iter().any(|r| r.0 == relay.0) {
                all.push(*relay);
            }
        }
        let relays = &all;
        let shared = Arc::clone(&self.shared);
        let height = self.chain.tip().map_or(0, |tip| tip.height);
        let mut wallet = shared.participant.lock().unwrap_or_else(|e| e.into_inner());
        let Some(own) = wallet.as_mut() else { return };
        let id = own.id();
        // (Of the epoch the chain is in; and where one gives way to
        // the next, of both.)
        // (And of the id of each full name the wallet is: at every
        // one of them it says it is there; at those of a name, that it
        // is that name too.)
        let mut points: Vec<(Digest, SocketAddrV4)> = Vec::new();
        let mut names: Vec<(Digest, Vec<SocketAddrV4>)> = Vec::new();
        let ids = [id].into_iter().chain(own.aliases().into_iter().map(|alias| alias.0));
        for (nth, of) in ids.enumerate() {
            let mut its = Vec::new();
            for epoch in crate::msg::reached_epochs(height) {
                for point in lists.iter().flat_map(|list| Self::points_among(&of, epoch, list)) {
                    its.push(point.1);
                    if !points.contains(&point) {
                        points.push(point);
                    }
                }
            }
            if nth > 0 {
                names.push((of, its));
            }
        }
        let at: Vec<SocketAddrV4> = points.iter().map(|p| p.1).collect();
        let kept: Vec<SocketAddrV4> = at.iter().chain(also).copied().collect();
        own.keep(&kept);
        let mut chance = [0u8; 64];
        if crate::random::fill(&mut chance).is_ok() {
            own.rotate(&chance, now);
        }
        let silent = 3 * self.cfg.keepalive;
        let mut ways = shared.ways.lock().unwrap_or_else(|e| e.into_inner());
        ways.give_up(|w| !match w.purpose {
            Purpose::Session => at.contains(&w.end().1) && (!w.ready() || now.saturating_sub(w.seen) < silent),
            // (And one that says nothing back when asked whether it
            // still goes anywhere.)
            Purpose::Spare if now.saturating_sub(w.seen) >= silent => false,
            Purpose::Send => now.saturating_sub(w.seen) < SEND_WAY_IDLE,
            // (One kept to go on from: a fresh one now and then, so
            // that what is sent this hour does not all go by the
            // relays of the last.)
            Purpose::Spare => now.saturating_sub(w.began) < SPARE_WAY_LIFE,
            Purpose::Asked => true,
        });
        let mut steps = Vec::new();
        // (Two: one of them mostly does not pass the relay a message
        // is next to go to.)
        for _ in ways.open.iter().filter(|w| w.purpose == Purpose::Spare).count()..SPARE_WAYS {
            steps.extend(self.begin_way(&mut ways, Purpose::Spare, relays, None, &id, now));
        }
        for point in points {
            match ways.open.iter_mut().find(|w| w.purpose == Purpose::Session && w.end().1 == point.1) {
                // (No way there: not reached there, until there is.)
                None => {
                    own.unreached(&point.1);
                    steps.extend(self.begin_way(&mut ways, Purpose::Session, relays, Some(point), &id, now))
                }
                Some(way) if way.ready() && own.due(&point.1, now, self.cfg.keepalive) => {
                    let seq = own.say(point.1, way.bind(), self.unix, now);
                    let mut said = Vec::new();
                    match (own.is_held(&point.1), own.announced_to(&point.1)) {
                        (false, Some(announce)) => {
                            said.push(HERE);
                            said.extend_from_slice(&announce);
                        }
                        _ => {
                            said.push(STILL);
                            said.extend_from_slice(&crate::hash::digest_to_bytes(&id));
                            said.extend_from_slice(&seq.to_le_bytes());
                        }
                    }
                    way.awaits(now);
                    steps.extend(way.say(&said));
                }
                // Held there: and shown to be each full name that is
                // reached there, until the node says it holds that.
                Some(way) if way.ready() => {
                    for (n, _) in names.iter().filter(|name| name.1.contains(&point.1)) {
                        if own.alias_due(n, &point.1, now)
                            && let Some(bundle) = own.alias_bundle(n)
                        {
                            own.alias_shown(n, point.1, now);
                            let mut said = vec![super::circuits::HERE_AS];
                            said.extend_from_slice(&bundle);
                            steps.extend(way.say(&said));
                        }
                    }
                }
                Some(_) => {}
            }
        }
        drop(ways);
        drop(wallet);
        for step in steps {
            self.carry(now, step);
        }
        if self.cfg.relay {
            self.shared.sessions.lock().unwrap_or_else(|e| e.into_inner()).prune(now);
        }
    }

    /// Sends on the messages this node's wallet is sending while relays
    /// are in force: each by a way to a relay the wallet it is for is
    /// reached at, which is not the way this wallet is itself reached
    /// by.
    fn send_posts_by_ways(&mut self, now: Micros, relays: &Relays) {
        use super::circuits::{ASK, GIVE, Purpose};
        use super::sessions::POST_RETRY;
        let shared = Arc::clone(&self.shared);
        let wallet = shared.participant.lock().unwrap_or_else(|e| e.into_inner());
        let Some(own) = wallet.as_ref() else { return };
        let mut mail = shared.letters.lock().unwrap_or_else(|e| e.into_inner());
        mail.expire(now);
        if mail.posts.is_empty() {
            return;
        }
        let epoch = self.chain.tip().map_or(0, |tip| tip.height / crate::consensus::EPOCH);
        let suspect = self.suspects();
        let mut ways = shared.ways.lock().unwrap_or_else(|e| e.into_inner());
        let mut steps = Vec::new();
        let mut awaited = Vec::new();
        for post in mail.posts.iter_mut() {
            if post.tried.is_some_and(|tried| now.saturating_sub(tried) < POST_RETRY) {
                continue;
            }
            // An answer: back by the way to the node the message came
            // by, which knows who gave it the message.
            if let Some(answer) = post.answers.clone() {
                if post.sealed.is_none() {
                    post.sealed = Self::seal_answer(own, post);
                }
                let back = |w: &&mut super::circuits::Way| w.purpose == Purpose::Session && w.end().1 == answer.by;
                if let (Some((_, bytes)), Some(way)) =
                    (&post.sealed, ways.open.iter_mut().find(back).filter(|w| w.ready()))
                {
                    post.tried = Some(now);
                    let mut said = vec![super::circuits::REPLY];
                    said.extend_from_slice(bytes);
                    way.awaits(now);
                    steps.extend(way.say(&said));
                }
                continue;
            }
            let points = Self::points_among(&post.asked(), epoch, relays);
            if points.is_empty() {
                continue;
            }
            let point = points[post.turn % points.len()];
            // (Not by a relay that lately did not answer, while the
            // wallet is reached at another.)
            if suspect.contains(&point.1) && points.iter().any(|p| !suspect.contains(&p.1)) {
                post.turn += 1;
                continue;
            }
            match ways.open.iter_mut().find(|w| w.purpose == Purpose::Send && w.end().1 == point.1) {
                // No way there: the one kept to go on from goes on to
                // it, if it is open and does not pass that relay
                // already; or one is opened.
                None => {
                    let spare =
                        ways.open.iter_mut().find(|w| w.purpose == Purpose::Spare && w.ready() && !w.passes(&point.0));
                    let mut chance = [0u8; 96];
                    match spare.filter(|_| crate::random::fill(&mut chance).is_ok()) {
                        Some(way) => {
                            way.purpose = Purpose::Send;
                            steps.extend(way.extend(point, &chance, now));
                        }
                        None => {
                            steps.extend(self.begin_way(&mut ways, Purpose::Send, relays, Some(point), &own.id(), now))
                        }
                    }
                }
                Some(way) if way.ready() => {
                    (post.tried, post.turn) = (Some(now), post.turn + 1);
                    let mut said = Vec::new();
                    match &post.sealed {
                        Some((_, bytes)) => {
                            said.push(GIVE);
                            said.extend_from_slice(bytes);
                        }
                        None => {
                            said.push(ASK);
                            said.extend_from_slice(&crate::hash::digest_to_bytes(&post.asked()));
                        }
                    }
                    way.awaits(now);
                    steps.extend(way.say(&said));
                }
                // (A way that is slow to open: another of the wallet's
                // nodes is tried meanwhile.)
                Some(way) if now.saturating_sub(way.began) >= SEND_WAY_SLOW && points.len() > 1 => {
                    post.turn += 1;
                }
                Some(_) => {}
            }
        }
        drop(ways);
        mail.awaited.append(&mut awaited);
        drop(mail);
        drop(wallet);
        for step in steps {
            self.carry(now, step);
        }
    }

    /// Who gave this node the message of id `id` to pass on, if that
    /// was lately.
    fn giver_of(&self, id: &Digest) -> Option<super::sessions::Where> {
        let id = crate::hash::digest_to_bytes(id);
        self.shared.givers.lock().unwrap_or_else(|e| e.into_inner()).iter().find(|g| g.0 == id).map(|g| g.1)
    }

    /// The message of id `id` was given to this node to pass on, by
    /// `giver`: kept, for its answer to go back by.
    fn given_by(&self, id: [u8; 32], giver: super::sessions::Where, now: Micros) {
        let mut givers = self.shared.givers.lock().unwrap_or_else(|e| e.into_inner());
        while givers.front().is_some_and(|g| now.saturating_sub(g.2) >= super::sessions::ANSWER_HOLDS)
            || givers.len() >= GIVERS
        {
            givers.pop_front();
        }
        if !givers.iter().any(|g| g.0 == id) {
            givers.push_back((id, giver, now));
        }
    }

    /// Something was said to this node as the last relay of the way
    /// known by `link`: by a wallet that is reached here, or by
    /// whoever sends to one that is.
    fn said_to_point(&mut self, now: Micros, link: (SocketAddrV4, u64), said: &[u8]) {
        use super::circuits::{ABSENT, ANNOUNCED, ASK, GIVE, HELD, HERE, HERE_HELD, NOTICE, PING, PONG, STILL, TAKE};
        use super::message::{NOTICE_OFFLINE, NOTICE_PASSED};
        use super::sessions::{Refused, Where};
        use crate::hash::{digest_from_bytes, digest_to_bytes};
        let shared = Arc::clone(&self.shared);
        let here = Where::Way(link.0, link.1);
        let made = |code: u8, parts: &[&[u8]]| {
            let mut bytes = vec![code];
            parts.iter().for_each(|part| bytes.extend_from_slice(part));
            bytes
        };
        let mut back: Vec<((SocketAddrV4, u64), Vec<u8>)> = Vec::new();
        let mut sessions = shared.sessions.lock().unwrap_or_else(|e| e.into_inner());
        match said.split_first() {
            Some((&PING, rest)) => back.push((link, made(PONG, &[rest]))),
            Some((&HERE, announce)) => {
                let bind = shared.relayed.lock().unwrap_or_else(|e| e.into_inner()).bind_of(&link);
                let taken = sessions.admit(announce.to_vec(), here, |b| Some(b) == bind, self.unix, now);
                // (Said again, as when the answer to the first was
                // lost: it is held, and that is said again too.)
                let id = match taken {
                    Ok(id) => Some(id),
                    Err(Refused::Stale) => Some(crate::address::id_of(&announce[..crate::mldsa::PK_LEN])),
                    Err(_) => None,
                };
                if let Some(id) = id
                    && let Some(seq) = sessions.get(&id, now).filter(|s| s.at == here || taken.is_err()).map(|s| s.seq)
                {
                    back.push((link, made(HERE_HELD, &[&digest_to_bytes(&id), &seq.to_le_bytes()])));
                }
            }
            Some((&STILL, rest)) if rest.len() == 40 => {
                if let Some(id) = digest_from_bytes(&rest[..32]) {
                    let seq = u64::from_le_bytes(rest[32..].try_into().expect("eight bytes"));
                    let held = match sessions.seen(&id, here, seq, now) {
                        true => seq,
                        false => sessions.get(&id, now).map_or(0, |s| s.seq),
                    };
                    back.push((link, made(HELD, &[&rest[..32], &held.to_le_bytes()])));
                }
            }
            Some((&ASK, rest)) if rest.len() == 32 => {
                if let Some(id) = digest_from_bytes(rest) {
                    back.push((
                        link,
                        match sessions.announced(&id, self.unix, now) {
                            Some(announced) => made(ANNOUNCED, &[&announced]),
                            None => made(ABSENT, &[rest]),
                        },
                    ));
                }
            }
            // A wallet held at the end of this way shows that it is a
            // full name: taken if the certificate is the name's, by
            // the chain, and the wallet is the one it names.
            Some((&super::circuits::HERE_AS, bundle)) => {
                let Some(checked) = crate::subnames::read(bundle, self.unix) else { return };
                let n = digest_to_bytes(&checked.point());
                let sound = self.name_value(&checked.name) == Some(checked.by);
                let taken = sound.then(|| sessions.alias(&checked, bundle.to_vec(), here, now).ok()).flatten();
                let seq = taken.map_or(0, |taken| taken.0);
                back.push((link, made(super::circuits::AS_HELD, &[&n, &seq.to_le_bytes()])));
                // (The wallet that was reached by the name until now
                // is told it no longer is.)
                match taken.and_then(|taken| taken.1) {
                    Some(Where::Way(before, circuit)) => {
                        back.push(((before, circuit), made(super::circuits::AS_HELD, &[&n, &[0; 8]])));
                    }
                    Some(Where::Addr(addr)) => {
                        self.to_say.push((addr, Message::AliasState { n: checked.point(), seq: 0 }));
                    }
                    None => {}
                }
            }
            // The wallet at the end of this way says a message came.
            Some((&super::circuits::TAKEN, id)) if id.len() == 32 => {
                let mut delivering = shared.delivering.lock().unwrap_or_else(|e| e.into_inner());
                delivering.retain(|d| {
                    let it = d.0 == id && d.1 == link;
                    if it {
                        back.push((d.2, made(NOTICE, &[id, &[NOTICE_PASSED]])));
                    }
                    !it
                });
            }
            // A wallet reached here answers a message that came to it
            // here: back to whoever gave that message, by the way (or
            // to the address) they gave it by.
            Some((&super::circuits::REPLY, sealed)) => {
                let (sealed_id, id) = (crate::msg::sealed_id(sealed), digest_to_bytes(&crate::msg::sealed_id(sealed)));
                let Some(of) = crate::msg::sealed_answers(sealed) else { return };
                let what = match self.giver_of(&of) {
                    Some(Where::Way(before, circuit)) => {
                        back.push(((before, circuit), made(super::circuits::ANSWER, &[sealed])));
                        NOTICE_PASSED
                    }
                    Some(Where::Addr(addr)) => {
                        let mut mail = shared.letters.lock().unwrap_or_else(|e| e.into_inner());
                        mail.pass(sealed_id, of, sealed.to_vec(), now);
                        let grant = self.tokens.issue(&SocketAddr::V4(addr));
                        let len = sealed.len() as u32;
                        self.to_say.push((addr, Message::Offer { token: 0, grant, to: of, id: sealed_id, len }));
                        NOTICE_PASSED
                    }
                    None => NOTICE_OFFLINE,
                };
                back.push((link, made(NOTICE, &[&id, &[what]])));
            }
            Some((&GIVE, sealed)) => {
                let id = digest_to_bytes(&crate::msg::sealed_id(sealed));
                let Some(to) = crate::msg::sealed_to(sealed) else { return };
                self.given_by(id, here, now);
                match sessions.get(&to, now).map(|s| s.at) {
                    None => back.push((link, made(NOTICE, &[&id, &[NOTICE_OFFLINE]]))),
                    // (Sent down the wallet's way; and whoever gave it
                    // is told it was passed on when the wallet says it
                    // came, or that it was not if the wallet does not.)
                    Some(Where::Way(before, circuit)) => {
                        let mut delivering = shared.delivering.lock().unwrap_or_else(|e| e.into_inner());
                        // (No room to keep count of one more: whoever
                        // gave it is told it did not go, and gives it
                        // to another of the wallet's nodes; told
                        // nothing, it would take it for passed on.)
                        if delivering.len() < LEAVING {
                            delivering.push((id, (before, circuit), link, now));
                            back.push(((before, circuit), made(TAKE, &[sealed])));
                        } else {
                            back.push((link, made(NOTICE, &[&id, &[NOTICE_OFFLINE]])));
                        }
                    }
                    // (A wallet that says it is here from an address,
                    // as before relays were in force: offered there.)
                    Some(Where::Addr(addr)) => {
                        let sealed_id = crate::msg::sealed_id(sealed);
                        shared.letters.lock().unwrap_or_else(|e| e.into_inner()).pass(
                            sealed_id,
                            to,
                            sealed.to_vec(),
                            now,
                        );
                        let grant = self.tokens.issue(&SocketAddr::V4(addr));
                        let len = sealed.len() as u32;
                        self.to_say.push((addr, Message::Offer { token: 0, grant, to, id: sealed_id, len }));
                        back.push((link, made(NOTICE, &[&id, &[NOTICE_PASSED]])));
                    }
                }
            }
            _ => {}
        }
        drop(sessions);
        let mut relayed = shared.relayed.lock().unwrap_or_else(|e| e.into_inner());
        let steps: Vec<_> = back.into_iter().filter_map(|(way, said)| relayed.say(way, &said, now)).collect();
        drop(relayed);
        for step in steps {
            self.carry(now, step);
        }
    }

    /// The last relay of a way this node's wallet is reached by, or
    /// sends by, has said something: the relay at `point`.
    fn said_by_point(
        &mut self,
        now: Micros,
        circuit: u64,
        purpose: super::circuits::Purpose,
        point: SocketAddrV4,
        said: Vec<u8>,
    ) {
        use super::circuits::{ABSENT, ANNOUNCED, GIVE, HELD, HERE_HELD, NOTICE, Purpose, TAKE};
        use crate::hash::digest_from_bytes;
        let shared = Arc::clone(&self.shared);
        match (purpose, said.split_first()) {
            (Purpose::Asked, _) => shared.ways.lock().unwrap_or_else(|e| e.into_inner()).said.push((circuit, said)),
            // The node holds this of the wallet, or nothing.
            (Purpose::Session, Some((&(HELD | HERE_HELD), rest))) if rest.len() == 40 => {
                let seq = u64::from_le_bytes(rest[32..].try_into().expect("eight bytes"));
                let mut wallet = shared.participant.lock().unwrap_or_else(|e| e.into_inner());
                if let Some(own) = wallet.as_mut().filter(|w| Some(w.id()) == digest_from_bytes(&rest[..32])) {
                    own.held(&point, seq, 0);
                }
            }
            (Purpose::Session, Some((&super::circuits::AS_HELD, rest))) if rest.len() == 40 => {
                let seq = u64::from_le_bytes(rest[32..].try_into().expect("eight bytes"));
                let mut wallet = shared.participant.lock().unwrap_or_else(|e| e.into_inner());
                if let (Some(own), Some(n)) = (wallet.as_mut(), digest_from_bytes(&rest[..32])) {
                    own.alias_held(&n, &point, seq);
                }
            }
            // A sealed message for the wallet.
            (Purpose::Session, Some((&TAKE, sealed))) => {
                let wallet = shared.participant.lock().unwrap_or_else(|e| e.into_inner());
                let Some(own) = wallet.as_ref().filter(|w| Some(w.id()) == crate::msg::sealed_to(sealed)) else {
                    return;
                };
                let mut mail = shared.letters.lock().unwrap_or_else(|e| e.into_inner());
                let id = crate::msg::sealed_id(sealed);
                if !mail.seen(id)
                    && let Some(mut opened) = own.open(sealed, now)
                {
                    // (Its answer goes back by this node.)
                    opened.by = Some(point);
                    mail.inbox.push(opened);
                    shared.say(Event::Mail);
                }
                drop((mail, wallet));
                // (It came: said back, each time it does.)
                let mut taken = vec![super::circuits::TAKEN];
                taken.extend_from_slice(&crate::hash::digest_to_bytes(&id));
                let mut ways = shared.ways.lock().unwrap_or_else(|e| e.into_inner());
                let step = ways.open.iter_mut().find(|w| w.circuit() == circuit).and_then(|way| way.say(&taken));
                drop(ways);
                step.into_iter().for_each(|step| self.carry(now, step));
            }
            // What the wallet a message is for announces: the message
            // is sealed to it, and given to be passed on.
            (Purpose::Send, Some((&ANNOUNCED, announced))) => {
                let mut mail = shared.letters.lock().unwrap_or_else(|e| e.into_inner());
                let Some((_, which)) = mail.announced(announced, self.unix, |name| self.name_value(name)) else {
                    return;
                };
                let announce = &announced[..crate::msg::ANNOUNCE_LEN];
                let mut ways = shared.ways.lock().unwrap_or_else(|e| e.into_inner());
                let Some(way) = ways.open.iter_mut().find(|w| w.circuit() == circuit) else { return };
                let mut steps = Vec::new();
                let mut awaited = Vec::new();
                for at in which {
                    let post = &mut mail.posts[at];
                    let Some((sealed, wait)) = Self::seal_for(announce, post, self.unix, now) else { continue };
                    let mut give = vec![GIVE];
                    give.extend_from_slice(&sealed.1);
                    steps.extend(way.say(&give));
                    (post.sealed, post.tried) = (Some(sealed), Some(now));
                    awaited.push(wait);
                }
                mail.awaited.append(&mut awaited);
                drop((ways, mail));
                for step in steps {
                    self.carry(now, step);
                }
            }
            (Purpose::Send, Some((&ABSENT, rest))) => {
                if let Some(id) = digest_from_bytes(rest) {
                    self.absent(&id);
                }
            }
            // (Of a message this wallet sent, or of an answer it gave.)
            (Purpose::Send | Purpose::Session, Some((&NOTICE, rest))) if rest.len() == 33 => {
                if let Some(id) = digest_from_bytes(&rest[..32]) {
                    self.noticed(&id, rest[32]);
                }
            }
            // The answer to a message this wallet sent, back by the way
            // it was sent by.
            (Purpose::Send, Some((&super::circuits::ANSWER, sealed))) => self.answer_arrived(sealed),
            _ => {}
        }
    }

    /// A node the wallet of id `id` is reached at has nothing of it:
    /// the wallet is not there, by that node's account. When each of
    /// its nodes has said so, what waits for it is given up as for a
    /// wallet that is not there.
    fn absent(&mut self, id: &Digest) {
        let nodes = self.points_of(id).len();
        let mut mail = self.shared.letters.lock().unwrap_or_else(|e| e.into_inner());
        for post in mail.posts.iter_mut().filter(|p| p.asked() == *id && p.sealed.is_none()) {
            (post.missed, post.tried) = (post.missed + 1, None);
        }
        let gone = |p: &super::sessions::Post| p.asked() == *id && p.sealed.is_none() && p.missed >= nodes;
        while let Some(at) = mail.posts.iter().position(gone) {
            mail.settle(at, super::sessions::Posted::Offline);
        }
    }

    /// What became of the sealed message of id `id`, by the node it
    /// was given to. True if it is a message of this node's wallet.
    fn noticed(&mut self, id: &Digest, what: u8) -> bool {
        use super::message::{NOTICE_OFFLINE, NOTICE_PASSED};
        let mut mail = self.shared.letters.lock().unwrap_or_else(|e| e.into_inner());
        let Some(at) = mail.posts.iter().position(|p| p.sealed.as_ref().is_some_and(|s| s.0 == *id)) else {
            return false;
        };
        match what {
            NOTICE_PASSED => mail.settle(at, super::sessions::Posted::Passed),
            // (Not there, by one node's account: another of its nodes
            // is tried, while there is time.)
            NOTICE_OFFLINE => mail.posts[at].tried = None,
            _ => {}
        }
        true
    }

    /// The nodes the wallet of id `id` is reached at now.
    fn points_of(&self, id: &Digest) -> Vec<SocketAddrV4> {
        let relays = self.relays_to_send_by();
        if !relays.is_empty() {
            let epoch = self.chain.tip().map_or(0, |tip| tip.height / crate::consensus::EPOCH);
            return Self::points_among(id, epoch, &relays).into_iter().map(|p| p.1).collect();
        }
        let seeds: Vec<SocketAddrV4> =
            self.shared.seeds.lock().unwrap_or_else(|e| e.into_inner()).iter().copied().collect();
        let epoch = self.chain.tip().map_or(0, |tip| tip.height / crate::consensus::EPOCH);
        crate::msg::points(id, epoch, seeds.len()).into_iter().map(|i| seeds[i]).collect()
    }

    /// Sends on the messages this node's wallet is sending: each to a
    /// node the wallet it is for is reached at, one after another until
    /// one passes it on. A message not yet sealed is sealed first, to
    /// what the wallet it is for announced, which is asked of such a
    /// node if it is not known.
    fn send_posts(&mut self, now: Micros, out: Out<'_>) {
        use super::sessions::POST_RETRY;
        // (Not while it is not known by which nodes to send: a node
        // that has never known which consensus file is in force. What
        // waits to be sent waits.)
        if !self.shared.knows_consensus() {
            return;
        }
        let relays = self.relays_to_send_by();
        if !relays.is_empty() {
            return self.send_posts_by_ways(now, &relays);
        }
        let wallet = self.shared.participant.lock().unwrap_or_else(|e| e.into_inner());
        let Some(own) = wallet.as_ref() else { return };
        let mut mail = self.shared.letters.lock().unwrap_or_else(|e| e.into_inner());
        mail.expire(now);
        let mut say: Vec<(SocketAddrV4, Message<'static>)> = Vec::new();
        let mut ask: Vec<(Digest, SocketAddrV4, u64)> = Vec::new();
        for at in 0..mail.posts.len() {
            if mail.posts[at].tried.is_some_and(|tried| now.saturating_sub(tried) < POST_RETRY) {
                continue;
            }
            // An answer: back to the node the message came by, which
            // knows who gave it the message.
            if let Some(answer) = mail.posts[at].answers.clone() {
                let node = answer.by;
                if self.shared.owner(&node) != self.me {
                    continue;
                }
                let grant = self.tokens.issue(&SocketAddr::V4(node));
                let token = self.token_of(&node).or(Some(own.token(&node)).filter(|token| *token != 0));
                let Some(token) = token else { continue };
                if mail.posts[at].sealed.is_none() {
                    mail.posts[at].sealed = Self::seal_answer(own, &mail.posts[at]);
                }
                mail.posts[at].tried = Some(now);
                if let Some((id, bytes)) = &mail.posts[at].sealed {
                    let len = bytes.len() as u32;
                    say.push((node, Message::Offer { token, grant, to: answer.of, id: *id, len }));
                }
                continue;
            }
            let (to, asked) = (mail.posts[at].to, mail.posts[at].asked());
            let points = self.points_of(&asked);
            if points.is_empty() {
                continue;
            }
            let node = points[mail.posts[at].turn % points.len()];
            // (Of the worker that node's answers come to: what it says
            // back is this worker's to hear.)
            if self.shared.owner(&node) != self.me {
                continue;
            }
            let grant = self.tokens.issue(&SocketAddr::V4(node));
            // A node that has not yet said its token is asked for it.
            let Some(token) = self.token_of(&node) else {
                mail.posts[at].tried = Some(now);
                // (Asked as nobody: whoever sends says nothing of
                // itself, to this node either.)
                say.push((node, Message::Session { token: 0, grant, id: Digest::default(), seq: 0 }));
                continue;
            };
            mail.posts[at].tried = Some(now);
            mail.posts[at].turn += 1;
            match &mail.posts[at].sealed {
                Some((id, bytes)) => {
                    let len = bytes.len() as u32;
                    say.push((node, Message::Offer { token, grant, to, id: *id, len }));
                }
                None => ask.push((asked, node, token)),
            }
        }
        drop(mail);
        drop(wallet);
        for (node, message) in say {
            self.send(node, &message, out);
        }
        for (to, node, token) in ask {
            let object = Object::Announce { id: to, seq: 0 };
            // (Of this node, whatever is still asked of another that
            // does not answer.)
            if !self.fetches.iter().any(|f| f.object == object && f.from == node) {
                let most = crate::msg::ANNOUNCE_LEN + crate::subnames::MAX_BUNDLE;
                self.fetch_granted(now, object, node, most as u32, token);
            }
        }
    }

    /// Seals `post` to the wallet that announced `to`, with a key made
    /// for its answer and nothing of this wallet: none if that is not
    /// an announcement of the wallet the post is for. With it, what is
    /// kept while the answer may come.
    #[allow(clippy::type_complexity)]
    fn seal_for(
        to: &[u8],
        post: &super::sessions::Post,
        unix: u64,
        now: Micros,
    ) -> Option<((Digest, Arc<Vec<u8>>), super::sessions::Awaited)> {
        let said = crate::msg::Announced::read(to, unix).filter(|said| said.id() == post.to)?;
        let mut chance = [0u8; 96];
        crate::random::fill(&mut chance).ok()?;
        let key = crate::mlkem::keygen(chance[..64].try_into().expect("64 bytes"));
        let seal_chance: &[u8; 32] = chance[64..].try_into().expect("32 bytes");
        let sealed = crate::msg::seal(&said, key.public_key(), post.kind, &post.body, seal_chance)?;
        let id = crate::msg::sealed_id(&sealed);
        Some(((id, Arc::new(sealed)), super::sessions::Awaited { id, key, to: post.to, since: now }))
    }

    /// Seals `post`, the answer to a message that came for this node's
    /// wallet: to the key that message carried, under the wallet's
    /// signature.
    fn seal_answer(own: &super::sessions::Participant, post: &super::sessions::Post) -> Option<(Digest, Arc<Vec<u8>>)> {
        let answer = post.answers.as_ref()?;
        let mut chance = [0u8; 32];
        crate::random::fill(&mut chance).ok()?;
        let sealed = crate::msg::seal_answer(own.identity(), &answer.key, &answer.of, post.kind, &post.body, &chance)?;
        Some((crate::msg::sealed_id(&sealed), Arc::new(sealed)))
    }

    /// The answer to a message this node's wallet sent has come: taken
    /// if it is sealed to the key that message carried, and signed by
    /// the wallet the message was sent to.
    fn answer_arrived(&mut self, sealed: &[u8]) {
        let Some(of) = crate::msg::sealed_answers(sealed) else { return };
        let mut mail = self.shared.letters.lock().unwrap_or_else(|e| e.into_inner());
        let opened = mail.awaited(&of).and_then(|wait| {
            crate::msg::open_answer(&wait.key, &of, sealed).filter(|opened| opened.from == Some(wait.to))
        });
        // (Taken once: a message has one answer, and is waited for no
        // longer when it has come.)
        if let Some(opened) = opened {
            mail.awaited.retain(|wait| wait.id != of);
            mail.inbox.push(opened);
            self.shared.say(Event::Mail);
        }
    }

    /// What a wallet announced has come, from a node it is reached at:
    /// the messages waiting for it are sealed to it, and offered to
    /// that node.
    fn announce_arrived(&mut self, now: Micros, from: SocketAddrV4, id: Digest, bytes: &[u8]) {
        let mut mail = self.shared.letters.lock().unwrap_or_else(|e| e.into_inner());
        let Some(token) = self.token_of(&from) else { return };
        let grant = self.tokens.issue(&SocketAddr::V4(from));
        // (Of the id that was asked, and of no other.)
        let Some((asked, which)) = mail.announced(bytes, self.unix, |name| self.name_value(name)) else { return };
        if asked != id {
            return;
        }
        let announce = &bytes[..crate::msg::ANNOUNCE_LEN];
        let mut awaited = Vec::new();
        for at in which {
            let post = &mut mail.posts[at];
            let Some((sealed, wait)) = Self::seal_for(announce, post, self.unix, now) else { continue };
            let len = sealed.1.len() as u32;
            self.to_say.push((from, Message::Offer { token, grant, to: post.to, id: sealed.0, len }));
            (post.sealed, post.tried) = (Some(sealed), Some(now));
            awaited.push(wait);
        }
        mail.awaited.append(&mut awaited);
    }

    /// A sealed message has come. For this node's wallet: opened, and
    /// kept for whoever takes what comes for it. Or offered to this
    /// node to pass on: kept a while, and offered to the wallet it is
    /// for, where that wallet is.
    fn sealed_arrived(&mut self, now: Micros, from: SocketAddrV4, id: Digest, bytes: &[u8]) {
        use super::message::{NOTICE_OFFLINE, NOTICE_PASSED};
        if crate::msg::sealed_id(bytes) != id {
            return self.tell(now, from, Notice::Strike(from));
        }
        let (to, answers) = (crate::msg::sealed_to(bytes), crate::msg::sealed_answers(bytes));
        let wallet = self.shared.participant.lock().unwrap_or_else(|e| e.into_inner());
        if let Some(own) = wallet.as_ref().filter(|w| Some(w.id()) == to) {
            let mut mail = self.shared.letters.lock().unwrap_or_else(|e| e.into_inner());
            if let Some(mut opened) = own.open(bytes, now)
                && !mail.seen(id)
            {
                // (Its answer goes back by the node it came by.)
                opened.by = Some(from);
                mail.inbox.push(opened);
                self.shared.say(Event::Mail);
            }
            return;
        }
        drop(wallet);
        // The answer to a message this node's wallet sent.
        let awaited = |of: &Digest| self.shared.letters.lock().unwrap_or_else(|e| e.into_inner()).awaited(of).is_some();
        if answers.is_some_and(|of| awaited(&of)) {
            return self.answer_arrived(bytes);
        }
        let Some(at) = self.offered.iter().position(|o| o.0 == id && o.2 == from) else { return };
        let (_, whom, sender) = self.offered.swap_remove(at);
        // An answer, given by the wallet that answers: back to whoever
        // gave the message it answers.
        if answers == Some(whom) {
            let what = match self.giver_of(&whom) {
                Some(super::sessions::Where::Way(before, circuit)) => {
                    let mut answer = vec![super::circuits::ANSWER];
                    answer.extend_from_slice(bytes);
                    let step = self.shared.relayed.lock().unwrap_or_else(|e| e.into_inner()).say(
                        (before, circuit),
                        &answer,
                        now,
                    );
                    let passed = step.is_some();
                    step.into_iter().for_each(|step| self.carry(now, step));
                    if passed { NOTICE_PASSED } else { NOTICE_OFFLINE }
                }
                Some(super::sessions::Where::Addr(addr)) => {
                    self.shared.letters.lock().unwrap_or_else(|e| e.into_inner()).pass(id, whom, bytes.to_vec(), now);
                    let grant = self.tokens.issue(&SocketAddr::V4(addr));
                    self.to_say.push((addr, Message::Offer { token: 0, grant, to: whom, id, len: bytes.len() as u32 }));
                    NOTICE_PASSED
                }
                None => NOTICE_OFFLINE,
            };
            return self.to_say.push((sender, Message::Notice { id, what }));
        }
        if Some(whom) != to {
            return self.tell(now, from, Notice::Strike(from));
        }
        self.given_by(crate::hash::digest_to_bytes(&id), super::sessions::Where::Addr(sender), now);
        let there = self.shared.sessions.lock().unwrap_or_else(|e| e.into_inner()).get(&whom, now).map(|s| s.at);
        // (At the end of a way: given to it there.)
        if let Some(super::sessions::Where::Way(before, circuit)) = there {
            let mut take = vec![super::circuits::TAKE];
            take.extend_from_slice(bytes);
            let step = self.shared.relayed.lock().unwrap_or_else(|e| e.into_inner()).say((before, circuit), &take, now);
            let what = if step.is_some() { NOTICE_PASSED } else { NOTICE_OFFLINE };
            step.into_iter().for_each(|step| self.carry(now, step));
            return self.to_say.push((sender, Message::Notice { id, what }));
        }
        let Some(super::sessions::Where::Addr(addr)) = there else {
            return self.to_say.push((sender, Message::Notice { id, what: NOTICE_OFFLINE }));
        };
        self.shared.letters.lock().unwrap_or_else(|e| e.into_inner()).pass(id, whom, bytes.to_vec(), now);
        let grant = self.tokens.issue(&SocketAddr::V4(addr));
        self.to_say.push((addr, Message::Offer { token: 0, grant, to: whom, id, len: bytes.len() as u32 }));
        self.to_say.push((sender, Message::Notice { id, what: NOTICE_PASSED }));
    }

    /// Looks to what the chain's blocks vote for, now and then: asks
    /// for the leaves of the blocks of the window that are not kept
    /// (a block's leaves are not in the block), and for the files they
    /// vote for that are not held; lets go of the files nobody votes
    /// for any more; and says so when another file is in force.
    ///
    /// Each worker of its own peers. (What two of them ask for at once
    /// is kept once; and what changed is said once, by whichever sees
    /// it first.)
    fn follow_votes(&mut self, now: Micros, out: Out<'_>) {
        use crate::consensus::{MAX_CONSENSUS, WINDOW, file_id};
        if now.saturating_sub(self.votes_looked) < self.cfg.sync.leaves_retry {
            return;
        }
        self.votes_looked = now;
        // (What was asked for and never came is asked for again, of
        // another.)
        self.leaves_asked.clear();
        if self.chain.receiving() {
            return;
        }
        // The votes are counted afresh only when something they are
        // counted from is other than it was: the chain's last block,
        // or the leaves and files kept. Counting reads the leaves of
        // two windows of blocks from the store; done at every turn by
        // every worker, a node with nothing to do read its store
        // seventeen thousand times a second.
        let key = (self.shared.blocks.load(Ordering::Relaxed), self.chain.votes_epoch());
        if self.votes.as_ref().is_none_or(|v| v.0 != key) {
            let Ok((current, decided)) = self.chain.consensus() else { return };
            let Ok(running) = self.chain.consensus_votes(WINDOW) else { return };
            // Not known, while a file that would be in force is not
            // held or votes are missing that could change the count:
            // the node keeps to what it knew, and says so, and what it
            // lacks is asked for below. (To decide without them would
            // be to go by another file than the rest do, or by none,
            // for as long as a peer cared to keep them back.)
            let lacking = match self.shared.forced.load(Ordering::Relaxed) {
                true => None,
                false => current.undecided(&decided, WINDOW),
            };
            let was = std::mem::replace(
                &mut *self.shared.undecided.lock().unwrap_or_else(|e| e.into_inner()),
                lacking.clone(),
            );
            if lacking.is_some() && was != lacking {
                let (files, votes) = lacking.clone().expect("it is some");
                self.shared.say(Event::ConsensusUnknown { files, votes });
            }
            // What is in force, said when it is another than was last said.
            let now_is = (current.mode, current.winner.map(|w| w.0));
            let mut said = self.shared.consensus.lock().unwrap_or_else(|e| e.into_inner());
            if lacking.is_none() && *said != Some(now_is) {
                let changed = said.is_some();
                // (Not of a node that has only just started, in init mode
                // like every other: that is no news.)
                if said.is_some() || now_is != (crate::consensus::Mode::Init, None) {
                    self.shared.say(Event::Consensus { mode: current.mode, file: now_is.1 });
                }
                *said = Some(now_is);
                if !self.shared.forced.load(Ordering::Relaxed) {
                    let relays = Arc::new(relays_of(current.file.as_ref()));
                    let before = std::mem::replace(
                        &mut *self.shared.relays.lock().unwrap_or_else(|e| e.into_inner()),
                        Arc::clone(&relays),
                    );
                    // Another file than the one this node was going by
                    // (not what a node finds in force when it starts):
                    // the nodes of the one before go on being used for
                    // a few blocks, since not every node has the block
                    // that decided it at the same moment.
                    if changed && *before != *relays {
                        let at = crate::consensus::boundary(self.chain.tip().map_or(0, |tip| tip.height));
                        *self.shared.relays_before.lock().unwrap_or_else(|e| e.into_inner()) = Some((before, at));
                    }
                }
            }
            drop(said);
            // The leaves that are missing, the newest first; and the
            // first file voted for that is not held.
            let missing: Vec<Digest> = running.missing.iter().chain(&decided.missing).rev().map(|m| m.0).collect();
            let voted: Vec<crate::consensus::Hash> =
                running.counts.iter().chain(&decided.counts).map(|c| c.0).collect();
            let wanted = voted.iter().find(|hash| !matches!(self.chain.consensus_file(hash), Ok(Some(_)))).copied();
            // And those held that nobody votes for any more go: but never
            // the one this node itself votes for, which it is to hand over
            // from the first block that says so.
            if let Ok(own) = self.chain.aux_leaves() {
                let keep: Vec<crate::consensus::Hash> = voted.iter().copied().chain([own[0]]).collect();
                let _ = self.chain.keep_consensus_files(&keep);
            }
            // (As the store is after that, which may have let files go.)
            let key = (key.0, self.chain.votes_epoch());
            self.votes = Some((key, missing, wanted));
        }
        let Some((_, missing, wanted)) = &self.votes else { return };
        if missing.is_empty() && wanted.is_none() {
            return;
        }
        let (missing, wanted) = (missing.clone(), *wanted);
        let peers: Vec<(SocketAddrV4, u64)> = self.peers.able(now).filter_map(|p| Some((p.addr, p.token()?))).collect();
        if peers.is_empty() {
            return;
        }
        // The leaves that are missing: a few at a time, each of the
        // next peer in turn.
        for id in missing.iter().take(LEAVES_AT_ONCE) {
            self.votes_turn = self.votes_turn.wrapping_add(1);
            let (peer, token) = peers[self.votes_turn % peers.len()];
            self.leaves_asked.push((*id, peer));
            self.send(peer, &Message::GetLeaves { token, id: *id }, out);
        }
        // The files voted for that are not held: one at a time.
        // (Of a few peers at once, each in its turn: one that keeps it
        // back, or does not have it, does not hold the others up.)
        if let Some(hash) = wanted {
            let object = Object::File(file_id(&hash));
            for _ in 0..FILE_ASKED_OF.min(peers.len()) {
                self.votes_turn = self.votes_turn.wrapping_add(1);
                let peer = peers[self.votes_turn % peers.len()].0;
                let asked = self.fetches.iter().filter(|f| f.object == object);
                if asked.clone().count() < FILE_ASKED_OF && !asked.clone().any(|f| f.from == peer) {
                    self.fetch_object(now, object, peer, MAX_CONSENSUS as u32);
                }
            }
        }
    }

    /// A consensus file asked for has arrived: kept, if it is one that
    /// is voted for. (Whether it is sound is for whoever counts the
    /// votes: an unsound file is held, and counts for nothing.)
    fn file_arrived(&mut self, now: Micros, from: SocketAddrV4, id: Digest, bytes: &[u8]) {
        use crate::consensus::{WINDOW, file_id, file_matches};
        let voted = self.chain.consensus_votes(2 * WINDOW).map(|v| v.counts).unwrap_or_default();
        match voted.iter().find(|c| file_id(&c.0) == id) {
            Some((hash, _, _)) if file_matches(hash, bytes) => {
                let _ = self.chain.put_consensus_file(bytes);
            }
            // Not the file of its name: its sender's doing.
            Some(_) => self.tell(now, from, Notice::Strike(from)),
            None => {}
        }
    }

    /// Whether a request from `from` carries the token `from` was given.
    fn asked_rightly(&mut self, from: &SocketAddrV4, token: u64) -> bool {
        let ok = self.tokens.check(&SocketAddr::V4(*from), token);
        self.counts.unheard += !ok as u64;
        ok
    }

    /// Looks to everything that is due at `now`, and says when to be
    /// called again at the latest: sooner if a datagram arrives.
    /// `unix` is the time by the calendar, in seconds.
    ///
    /// Every [`Config::tick`]: pings whoever is due, drops whoever has
    /// been silent too long, looks for more peers while there are too
    /// few, replaces the tokens' secret when it has had its time, and
    /// sees whether there are headers to catch up with. Every call:
    /// what the fetches under way and the chunks being served want
    /// done.
    pub(crate) fn tick(&mut self, now: Micros, unix: u64, out: Out<'_>) -> Micros {
        self.unix = unix;
        self.now = now;
        self.mail(now, out);
        // (What the wallet sends is looked to whenever the worker is
        // woken, not only when time is: a payment does not wait for
        // the second to turn.)
        self.send_posts(now, out);
        self.drive_ways(now);
        if now >= self.due {
            self.due = now + self.cfg.tick;
            self.periodic(now, out);
        }
        self.pump(now, out).min(self.due).min(self.tell_due)
    }

    fn periodic(&mut self, now: Micros, out: Out<'_>) {
        // (The same secret at the same time in every worker: by how
        // many lives of a token have passed, not by when each began.)
        let lives = now / self.cfg.serve.token_life.max(1);
        if lives != self.secrets {
            // (More than one life gone by, of a machine that slept: the
            // secret before this one is the life before's, not one of
            // however long ago.)
            if lives > self.secrets.saturating_add(1) {
                self.tokens.rotate(derive(&self.shared.token_secret, b't', lives - 1));
            }
            self.secrets = lives;
            self.tokens.rotate(derive(&self.shared.token_secret, b't', lives));
            self.rotated = now;
        }
        self.peers.prune(now, |_| {});
        // Which have answered, for whoever keeps them: said when it is
        // other than it was. (In the order of their addresses.)
        let answered: Vec<SocketAddrV4> = self.peers.all().filter(|p| p.proven).map(|p| p.addr).collect();
        let mut said = self.shared.answered[self.me].lock().unwrap_or_else(|e| e.into_inner());
        if *said != answered {
            *said = answered;
        }
        drop(said);
        // And how each stands, for whoever asks what the node sees.
        let live: Vec<SocketAddrV4> = self.peers.live(now).map(|p| p.addr).collect();
        let listed: Vec<PeerSeen> = self
            .peers
            .all()
            .map(|p| PeerSeen {
                addr: p.addr,
                seed: p.seed,
                answered: p.proven,
                live: live.contains(&p.addr),
                height: p.status.map(|s| s.height),
                silent: p.last_seen.map(|seen| now.saturating_sub(seen)),
            })
            .collect();
        *self.shared.listed[self.me].lock().unwrap_or_else(|e| e.into_inner()) = listed;
        self.budget = self.cfg.peers.unproven_pings;
        self.follow_votes(now, out);
        self.keep_sessions(now, out);
        if self.cfg.relay {
            self.shared.relayed.lock().unwrap_or_else(|e| e.into_inner()).prune(now);
        }
        // (A way that does not open is given up.)
        let mut ways = self.shared.ways.lock().unwrap_or_else(|e| e.into_inner());
        // (And a relay that does not answer the opening of one is not
        // gone by for a while: the next way goes by others.)
        let silent =
            |w: &super::circuits::Way| w.unanswered() && now.saturating_sub(w.began) >= super::circuits::FIRST_ANSWER;
        let dead: Vec<SocketAddrV4> = ways.open.iter().filter(|w| silent(w)).map(|w| w.first()).collect();
        // (Nor is one kept that leaves what was said along it
        // unanswered: a relay of it is gone, and another way is
        // opened in its place by whoever needs one.)
        let gone = ways.give_up(|w| silent(w) || w.gone(now));
        let slow = ways.give_up(|w| !w.ready() && now.saturating_sub(w.began) >= super::circuits::OPENING);
        // (Where one went nowhere, a relay is gone, and the others may
        // go by it too: each is asked at once whether it still goes
        // anywhere, and not when it is next due.)
        let lost = gone + slow > 0;
        // (A way kept to go on from is asked now and then whether it
        // still goes anywhere.)
        let mut pings = Vec::new();
        let asked = |w: &super::circuits::Way| w.purpose != super::circuits::Purpose::Asked && w.ready();
        for way in ways.open.iter_mut().filter(|w| asked(w)) {
            // (As is the way a wallet is reached by, and sooner: while
            // a relay of it is gone and that is not known, what is sent
            // down it comes to nothing, and whoever sent it is told the
            // wallet is not there.)
            let quiet = match way.purpose {
                super::circuits::Purpose::Spare => self.cfg.keepalive,
                super::circuits::Purpose::Session => self.cfg.keepalive / 3,
                _ => Micros::MAX,
            };
            if now.saturating_sub(way.seen) >= quiet || (lost && !way.gone(now)) {
                way.awaits(now);
                pings.extend(way.say(&[super::circuits::PING]));
            }
        }
        drop(ways);
        for step in pings {
            self.carry(now, step);
        }
        // What was sent down a wallet's way and not said to have come:
        // whoever gave it is told it was not passed on.
        if self.cfg.relay {
            let mut late = Vec::new();
            let mut delivering = self.shared.delivering.lock().unwrap_or_else(|e| e.into_inner());
            delivering.retain(|d| {
                let is = now.saturating_sub(d.3) >= DELIVERED_WITHIN;
                if is {
                    late.push((d.2, d.0));
                }
                !is
            });
            drop(delivering);
            let mut relayed = self.shared.relayed.lock().unwrap_or_else(|e| e.into_inner());
            let mut steps = Vec::new();
            for (giver, id) in late {
                let mut notice = vec![super::circuits::NOTICE];
                notice.extend_from_slice(&id);
                notice.push(super::message::NOTICE_OFFLINE);
                steps.extend(relayed.say(giver, &notice, now));
            }
            drop(relayed);
            for step in steps {
                self.carry(now, step);
            }
        }
        let mut suspect = self.shared.suspect.lock().unwrap_or_else(|e| e.into_inner());
        suspect.retain(|s| now.saturating_sub(s.1) < SUSPECT_FOR && !dead.contains(&s.0));
        suspect.extend(dead.into_iter().map(|relay| (relay, now)));
        drop(suspect);
        let mut due = Vec::new();
        let (secret, numbers) = (&self.secret, &mut self.numbers);
        self.peers.pings_due(now, || Self::number(secret, numbers), |addr, number| due.push((addr, number)));
        for (addr, number) in due {
            let ping = Message::Ping(self.status(&addr, number));
            self.send(addr, &ping, out);
        }
        // (Too few live peers: of the node, over all its workers.)
        let mine: Vec<SocketAddrV4> = self.peers.live(now).map(|p| p.addr).collect();
        // Who is live that was not, and who was that is not: said.
        // (Both in the order of their addresses.)
        for peer in mine.iter().filter(|a| self.was_live.binary_search(a).is_err()) {
            let height = self.peers.get(peer).and_then(|p| p.status).map_or(0, |s| s.height);
            self.shared.say(Event::PeerConnected { peer: *peer, height });
        }
        for peer in self.was_live.iter().filter(|a| mine.binary_search(a).is_err()) {
            self.shared.say(Event::PeerLost { peer: *peer });
            // (Its node may be a peer at another address from now.)
            self.shared.nodes.lock().unwrap_or_else(|e| e.into_inner()).retain(|known| known.1 != *peer);
        }
        self.was_live.clone_from(&mine);
        self.shared.live[self.me].store(mine.len(), Ordering::Relaxed);
        if self.shared.live.len() > 1 {
            *self.shared.known[self.me].lock().unwrap_or_else(|e| e.into_inner()) = mine;
        }
        let live: usize = self.shared.live.iter().map(|n| n.load(Ordering::Relaxed)).sum();
        if live < self.cfg.peers.target && self.asked.is_none_or(|t| now.saturating_sub(t) >= self.ask_gap) {
            let one = self.peers.sample(None, now).as_slice().first().copied();
            if let Some(addr) = one
                && let Some(token) = self.peers.get(&addr).and_then(|p| p.token())
            {
                // Asked again half as soon each time nothing came of
                // the asking (the node knows no more peers than it
                // did), down to as seldom as it pings; and as soon as
                // at first once something does.
                let knows = self.shared.totals.peers();
                self.ask_gap = match self.asked.is_some() && knows == self.ask_knew {
                    true => (2 * self.ask_gap).min(self.cfg.peers.ping.max(self.cfg.peers.discover)),
                    false => self.cfg.peers.discover,
                };
                self.ask_knew = knows;
                self.asked = Some(now);
                self.send(addr, &Message::GetPeers { token }, out);
            }
        }
        // What there is to catch up with: with the list in hand.
        let list = Arc::clone(&self.list);
        let l = &mut *write(&list);
        self.sync_headers(l, now, out);
        self.sync_blocks(l, now);
        self.advance_join(l, now);
    }

    /// Takes a datagram that arrived from `from`, and says what it was
    /// and what was done about it. Call [`Node::tick`] after it.
    pub(crate) fn handle(&mut self, now: Micros, from: SocketAddr, bytes: &[u8], out: Out<'_>) -> Heard {
        let unheard =
            |from, request| Heard { from, request, about: About::Nothing, answer: "malformed", sent: 0, sent_bytes: 0 };
        // Addresses of the older kind only (`docs/WIRE.md`, 1.1).
        let from = match from {
            SocketAddr::V4(a) => a,
            SocketAddr::V6(a) => match a.ip().to_ipv4_mapped() {
                Some(ip) => SocketAddrV4::new(ip, a.port()),
                None => return unheard(None, "ipv6"),
            },
        };
        let Ok(message) = Message::decode(self.network, bytes) else {
            self.counts.malformed += 1;
            return unheard(Some(from), "malformed");
        };
        let (request, about, answers) = match &message {
            Message::Ping(theirs) => ("ping", About::Height(theirs.height), "pong"),
            Message::Pong(theirs) => ("pong", About::Height(theirs.height), "answered"),
            Message::GetPeers { .. } => ("get-peers", About::Nothing, "peers"),
            Message::Peers(addrs) => ("peers", About::Peers(addrs.as_slice().len()), "answered"),
            Message::Goodbye { .. } => ("goodbye", About::Nothing, "answered"),
            Message::FindFork { .. } => ("find-fork", About::Nothing, "fork"),
            Message::Fork { height, .. } => ("fork", About::Height(*height), "answered"),
            Message::Block { header, len } => {
                ("block", About::Block { height: header.height, bytes: *len }, "answered")
            }
            Message::Get(get) => {
                let of = Object::decode(get.name).map_or("nothing", |o| o.kind());
                ("get", About::Chunks { of, chunks: get.ranges.chunks() }, "answered")
            }
            Message::Chunk(_) => (CHUNK, About::Nothing, "answered"),
            Message::Gone(_) => ("gone", About::Nothing, "answered"),
            Message::Tx { .. } => ("tx", About::Nothing, "answered"),
            Message::GetLeaves { .. } => ("get-leaves", About::Nothing, "answered"),
            Message::Leaves { .. } => ("leaves", About::Nothing, "answered"),
            Message::Session { .. } => ("session", About::Nothing, "session-state"),
            Message::SessionState { .. } => ("session-state", About::Nothing, "answered"),
            Message::Offer { .. } => ("offer", About::Nothing, "answered"),
            Message::Carry { .. } => ("carry", About::Nothing, "answered"),
            Message::Alias { .. } => ("alias", About::Nothing, "alias-state"),
            Message::AliasState { .. } => ("alias-state", About::Nothing, "answered"),
            Message::Stepped { .. } => ("stepped", About::Nothing, "carried"),
            Message::Carried { .. } => ("carried", About::Nothing, "answered"),
            Message::Notice { .. } => ("notice", About::Nothing, "answered"),
        };
        // What was done is read off what it left behind: what was sent,
        // and what was counted as not listened to.
        let before = self.counts;
        let (mut sent, mut sent_bytes) = (0u32, 0u32);
        self.act(now, from, message, &mut |to, bytes: &[u8]| {
            sent += 1;
            sent_bytes += bytes.len() as u32;
            out(to, bytes)
        });
        let answer = match () {
            () if self.counts.malformed > before.malformed => "malformed",
            () if self.counts.unheard > before.unheard => "unheard",
            () if self.counts.strangers > before.strangers => "stranger",
            () if sent > 0 => answers,
            () if request == "get" => "queued",
            () => "taken",
        };
        Heard { from: Some(from), request, about, answer, sent, sent_bytes }
    }

    fn act(&mut self, now: Micros, from: SocketAddrV4, message: Message<'_>, out: Out<'_>) {
        match message {
            Message::Ping(theirs) => self.on_ping(now, from, theirs, out),
            Message::Pong(theirs) => self.on_pong(now, from, theirs, out),
            Message::GetPeers { token } => {
                if self.asked_rightly(&from, token) {
                    self.peers.seen(&from, now);
                    let sample = self.sample(from, now);
                    self.send(from, &Message::Peers(sample), out);
                }
            }
            Message::Peers(addrs) => {
                // Unasked, as far as its sender can show: only from a
                // peer, and each is only an address to try.
                if !self.peers.proven(&from) {
                    self.counts.unheard += 1;
                    return;
                }
                self.peers.seen(&from, now);
                // (But an address of the machine itself, which is
                // whoever said it and nobody else's to try.)
                for a in addrs.as_slice().iter().filter(|a| !a.ip().is_loopback()) {
                    self.tell(now, *a, Notice::Try(*a));
                }
            }
            Message::Goodbye { token } => {
                if self.asked_rightly(&from, token) {
                    self.peers.gone(&from);
                }
            }
            Message::FindFork { token, locator } => {
                if self.asked_rightly(&from, token) {
                    self.peers.seen(&from, now);
                    let (height, id) = self.newest_of_ours(&locator);
                    self.send(from, &Message::Fork { height, id }, out);
                }
            }
            Message::Fork { height, id } => {
                let list = Arc::clone(&self.list);
                self.on_fork(&mut write(&list), now, from, height, id)
            }
            Message::Block { header, len } => {
                let list = Arc::clone(&self.list);
                self.on_block(&mut write(&list), now, from, header, len, out)
            }
            Message::Get(get) => self.on_get(now, from, &get),
            Message::Chunk(chunk) => self.on_chunk(now, from, &chunk),
            Message::Gone(gone) => {
                match self.fetches.iter_mut().find(|f| f.from == from && f.fetch.transfer() == gone.transfer) {
                    Some(f) => f.fetch.gone(),
                    None => self.counts.unheard += 1,
                }
            }
            Message::Tx { id, len } => self.on_tx(now, from, id, len),
            // A wallet says it is there, to a node that holds sessions:
            // the session goes on, or its announcement is asked for.
            Message::Session { token, grant, id, seq } => {
                if !self.cfg.relay {
                    self.counts.unheard += 1;
                    return;
                }
                // Whoever says so is told this node's token for where it
                // says it from: nothing is kept of the asking, and the
                // answer is no longer than it. Only an asking that
                // carries that token is gone into.
                let ours = self.tokens.issue(&SocketAddr::V4(from));
                if seq == 0 || !self.tokens.check(&SocketAddr::V4(from), token) {
                    return self.send(from, &Message::SessionState { id, seq: 0, token: ours, echo: grant }, out);
                }
                let held = self.shared.sessions.lock().unwrap_or_else(|e| e.into_inner()).seen(&id, from, seq, now);
                let object = Object::Announce { id, seq };
                if !held && !self.fetches.iter().any(|f| f.object == object && f.from == from) {
                    self.fetch_granted(now, object, from, crate::msg::ANNOUNCE_LEN as u32, grant);
                }
                // (What it holds for that wallet, where that is another
                // announcement than was said: the wallet knows by it
                // that something else announces as it.)
                let other =
                    || self.shared.sessions.lock().unwrap_or_else(|e| e.into_inner()).get(&id, now).map(|s| s.seq);
                let seq = if held { seq } else { other().unwrap_or(0) };
                self.send(from, &Message::SessionState { id, seq, token: ours, echo: grant }, out);
            }
            // And a node says what it holds for this node's wallet.
            // (With its token for this node, which the next saying is to
            // carry: told at once, if that is news.)
            Message::SessionState { id, seq, token, echo } => {
                // (The answer to what this node asked of that address,
                // or nothing: anyone can write the address of a node
                // wallets are reached at on a datagram.)
                if !self.tokens.check(&SocketAddr::V4(from), echo) {
                    self.counts.unheard += 1;
                    return;
                }
                // (Its token is kept whether or not the wallet is reached
                // there: it is what the node is asked anything with.)
                if token != 0 {
                    self.grants.retain(|g| g.0 != from);
                    self.grants.push_back((from, token));
                    if self.grants.len() > GRANTS {
                        self.grants.pop_front();
                    }
                }
                // (And what waited for it is tried again at once.)
                if token != 0 {
                    let mut mail = self.shared.letters.lock().unwrap_or_else(|e| e.into_inner());
                    mail.posts.iter_mut().filter(|p| p.sealed.is_none()).for_each(|p| p.tried = None);
                    drop(mail);
                    self.send_posts(now, out);
                }
                let mut wallet = self.shared.participant.lock().unwrap_or_else(|e| e.into_inner());
                let Some(own) = wallet.as_mut().filter(|w| w.id() == id) else {
                    return;
                };
                if own.held(&from, seq, token) {
                    let seq = own.say(from, token, self.unix, now);
                    drop(wallet);
                    let grant = self.tokens.issue(&SocketAddr::V4(from));
                    self.send(from, &Message::Session { token, grant, id, seq }, out);
                }
            }
            // A sealed message is offered. To a node that stands between
            // wallets, with its token, to pass on: asked for, if the
            // wallet it is for is here to take it. Or by such a node to
            // this node's wallet, which it is for: asked for, once.
            Message::Offer { token, grant, to, id, len } => {
                let (most, object) = (crate::msg::MAX_SEALED as u32, Object::Sealed(id));
                let fetching = self.fetches.iter().any(|f| f.object == object);
                let own = self.shared.participant.lock().unwrap_or_else(|e| e.into_inner()).as_ref().map(|w| w.id());
                // (For this node's wallet; or the answer to a message
                // it sent, which `to` then is.)
                let awaited = self.shared.letters.lock().unwrap_or_else(|e| e.into_inner()).awaited(&to).is_some();
                if own == Some(to) || awaited {
                    // (Come before only once it has come: one offered
                    // and never had is offered again, and taken then.)
                    let known = self.shared.letters.lock().unwrap_or_else(|e| e.into_inner()).has_seen(&id);
                    if !known && !fetching && len <= most {
                        self.fetch_unasked(now, object, from, len, grant);
                    }
                } else if self.cfg.relay && self.tokens.check(&SocketAddr::V4(from), token) && len <= most {
                    // (For a wallet that is here; or the answer to a
                    // message this node passed on, for whoever gave it.)
                    let there = self.shared.sessions.lock().unwrap_or_else(|e| e.into_inner()).get(&to, now).is_some();
                    match there || self.giver_of(&to).is_some() {
                        false => self.send(from, &Message::Notice { id, what: super::message::NOTICE_OFFLINE }, out),
                        true if fetching => {}
                        true => {
                            self.offered.retain(|o| o.0 != id);
                            if self.offered.len() >= OFFERED {
                                self.offered.remove(0);
                            }
                            self.offered.push((id, to, from));
                            self.fetch_granted(now, object, from, len, grant);
                        }
                    }
                } else {
                    self.counts.unheard += 1;
                }
            }
            // A neighbour on a way has something for this node: asked
            // for, if it is of a way that is here, or opens one through
            // a node that ways go through.
            Message::Carry { grant, name, circuit, kind, count, len } => {
                use super::circuits::{BACK, FORWARD, MAX_STEP, OPEN, OPENED};
                let link = (from, circuit);
                let known =
                    self.taken.contains(&(from, name)) || self.carried.iter().any(|c| (c.0, c.1) == (name, from));
                let relayed = self.shared.relayed.lock().unwrap_or_else(|e| e.into_inner());
                let wanted = match kind {
                    _ if known || len as usize > MAX_STEP || self.carried.len() >= CARRIED => false,
                    OPEN => self.cfg.relay && len as usize == crate::onion::HELLO_LEN && !relayed.holds(&link),
                    FORWARD => relayed.holds(&link),
                    OPENED | BACK => {
                        let own = || {
                            let ways = self.shared.ways.lock().unwrap_or_else(|e| e.into_inner());
                            ways.open.iter().any(|w| (w.first(), w.circuit()) == link)
                        };
                        relayed.goes_on_to(&link) || own()
                    }
                    _ => false,
                };
                drop(relayed);
                if wanted {
                    self.carried.push((name, from, circuit, kind, count));
                    // (A way's opening is from anyone; the rest is of a
                    // way that is here.)
                    match kind {
                        OPEN => self.fetch_unasked(now, Object::Step(name), from, len, grant),
                        _ => self.fetch_granted(now, Object::Step(name), from, len, grant),
                    }
                } else if !known {
                    self.counts.unheard += 1;
                }
            }
            // A wallet held here says it is a full name, by a
            // certificate of this number: held already, or asked for.
            Message::Alias { token, grant, n, seq } => {
                if !self.cfg.relay || !self.tokens.check(&SocketAddr::V4(from), token) {
                    self.counts.unheard += 1;
                    return;
                }
                let sessions = self.shared.sessions.lock().unwrap_or_else(|e| e.into_inner());
                let at = super::sessions::Where::Addr(from);
                let held = sessions.aliased(&n, self.unix, now).is_some_and(|(s, a)| s.at == at && a.seq == seq);
                drop(sessions);
                let object = Object::Alias(n);
                if held {
                    self.send(from, &Message::AliasState { n, seq }, out);
                } else if !self.fetches.iter().any(|f| f.object == object && f.from == from) {
                    self.fetch_granted(now, object, from, crate::subnames::MAX_BUNDLE as u32, grant);
                }
            }
            Message::AliasState { n, seq } => {
                let mut wallet = self.shared.participant.lock().unwrap_or_else(|e| e.into_inner());
                match wallet.as_mut() {
                    Some(own) => own.alias_held(&n, &from, seq),
                    None => self.counts.unheard += 1,
                }
            }
            // The same, said whole: of a way that is here, taken, once;
            // and said to have come, each time it is said.
            Message::Stepped { name, circuit, kind, count, bytes } => {
                use super::circuits::{BACK, FORWARD};
                let link = (from, circuit);
                let known = self.taken.contains(&(from, name));
                let of_a_way = || {
                    let relayed = self.shared.relayed.lock().unwrap_or_else(|e| e.into_inner());
                    match kind {
                        FORWARD | super::circuits::CLOSE => relayed.holds(&link),
                        BACK => {
                            let ways = self.shared.ways.lock().unwrap_or_else(|e| e.into_inner());
                            relayed.goes_on_to(&link) || ways.open.iter().any(|w| (w.first(), w.circuit()) == link)
                        }
                        _ => false,
                    }
                };
                if !known && !of_a_way() {
                    self.counts.unheard += 1;
                    return;
                }
                self.send(from, &Message::Carried { name }, out);
                if !known {
                    self.taken.push_back((from, name));
                    if self.taken.len() > TAKEN {
                        self.taken.pop_front();
                    }
                    self.step_taken(now, from, circuit, kind, count, bytes);
                }
            }
            Message::Carried { name } => {
                let mut leaving = self.shared.leaving.lock().unwrap_or_else(|e| e.into_inner());
                let before = leaving.len();
                leaving.retain(|l| (l.name, l.step.to) != (name, from));
                if leaving.len() == before {
                    self.counts.unheard += 1;
                }
            }
            // What became of a message this node's wallet sent.
            Message::Notice { id, what } => {
                use super::message::{NOTICE_OFFLINE, NOTICE_PASSED};
                use super::sessions::Posted;
                let mut mail = self.shared.letters.lock().unwrap_or_else(|e| e.into_inner());
                let at = mail.posts.iter().position(|p| p.sealed.as_ref().is_some_and(|s| s.0 == id));
                match (at, what) {
                    (Some(at), NOTICE_PASSED) => mail.settle(at, Posted::Passed),
                    // (Not there, by one node's account: another of
                    // its nodes is tried, while there is time.)
                    (Some(at), NOTICE_OFFLINE) => mail.posts[at].tried = None,
                    (Some(_), _) => {}
                    (None, _) => self.counts.unheard += 1,
                }
                drop(mail);
                self.shared.work(self.me);
            }
            // A block's leaves, if they are kept here: to whoever asks
            // with the token it was given.
            Message::GetLeaves { token, id } => {
                if self.asked_rightly(&from, token)
                    && let Ok(Some(leaves)) = self.chain.aux_leaves_of(&id)
                {
                    self.send(from, &Message::Leaves { id, leaves }, out);
                }
            }
            // And those asked for: kept if they are what the block's
            // header commits to, and their sender struck if not.
            Message::Leaves { id, leaves } => match self.leaves_asked.iter().position(|a| *a == (id, from)) {
                Some(at) => {
                    self.leaves_asked.swap_remove(at);
                    let list = Arc::clone(&self.list);
                    self.work(&mut write(&list), Job::Leaves { id, leaves: Box::new(leaves), from });
                }
                None => self.counts.unheard += 1,
            },
        }
    }

    fn on_ping(&mut self, now: Micros, from: SocketAddrV4, theirs: Status, out: Out<'_>) {
        // Another version, another chain: answered, so that the other
        // side can see why, and nothing more. (It is its pong to a ping
        // of ours, which shows it is there, that drops it.)
        if theirs.version != VERSION || theirs.genesis != self.genesis {
            self.counts.strangers += 1;
            let pong = Message::Pong(self.status(&from, theirs.nonce));
            return self.send(from, &pong, out);
        }
        // Our own ping to this address, come back: the address is ours.
        // (Or anything of this node's own, by whatever way it came.)
        if self.peers.is_own_ping(&from, theirs.nonce) || theirs.node == self.shared.node {
            return self.peers.mark_self(from);
        }
        if self.peers.proven(&from) {
            self.peers.seen(&from, now);
            self.peers.set_status(&from, theirs);
        } else {
            // An address to try, if there is room for it.
            let _ = self.peers.add(from, false, now);
        }
        let pong = Message::Pong(self.status(&from, theirs.nonce));
        self.send(from, &pong, out);
        // And our own ping at once, so that it need not wait its turn
        // to be proven: within what unproven addresses are allowed.
        if self.budget > 0 && !self.peers.proven(&from) {
            let number = Self::number(&self.secret, &mut self.numbers);
            if self.peers.ping_now(&from, number, now) {
                self.budget -= 1;
                let ping = Message::Ping(self.status(&from, number));
                self.send(from, &ping, out);
            }
        }
    }

    fn on_pong(&mut self, now: Micros, from: SocketAddrV4, theirs: Status, out: Out<'_>) {
        // Only the answer to a ping of ours counts for anything.
        if !self.peers.pong(&from, theirs, now) {
            self.counts.unheard += 1;
            return;
        }
        // It is there, and it is no peer of ours.
        if theirs.version != VERSION || theirs.genesis != self.genesis {
            self.counts.strangers += 1;
            self.peers.remove(&from);
            return;
        }
        // This node itself, reached at an address it did not know for
        // its own; or a node that is a peer already, at another: no
        // peer, and not asked again.
        if theirs.node == self.shared.node || self.peer_elsewhere(theirs.node, from) {
            return self.peers.mark_self(from);
        }
        // Live from now, if it was not: said at once, before anything
        // that is done because it is.
        if let Err(place) = self.was_live.binary_search(&from) {
            self.was_live.insert(place, from);
            self.shared.say(Event::PeerConnected { peer: from, height: theirs.height });
            self.announce_pool_to(from, out);
        }
    }

    /// "I am going", to every live peer: when a node stops, so that
    /// they need not find it out by its silence.
    fn goodbye(&mut self, now: Micros, out: Out<'_>) {
        let mut all = Vec::new();
        all.extend(self.peers.live(now).filter_map(|p| p.token().map(|t| (p.addr, t))));
        for (addr, token) in all {
            self.send(addr, &Message::Goodbye { token }, out);
        }
    }

    // -- Headers

    /// The header of the block `id`, if it is on the chain here.
    fn on_chain(&self, id: &Digest) -> Option<Header> {
        let known = self.chain.known(id).ok()??;
        (self.chain.header_at(known.header.height).ok()? == Some(known.header)).then_some(known.header)
    }

    /// The newest block of `locator` that is on the chain here: the
    /// first block of all, if none is.
    fn newest_of_ours(&self, locator: &Locator) -> (u32, Digest) {
        locator.as_slice().iter().find_map(|id| self.on_chain(id).map(|h| (h.height, *id))).unwrap_or((0, self.genesis))
    }

    /// Whether there are headers to catch up with, and the next step
    /// towards them.
    fn sync_headers(&mut self, l: &mut List, now: Micros, out: Out<'_>) {
        let Ok(best) = self.chain.best_header() else {
            return;
        };
        // Those that claimed work and have sent nothing for it.
        self.peers.doubt_silent_claimants(best.work, now, |_| {});
        // (Whoever was asked is its own worker's to give up on.)
        if let Some((addr, _, _)) = l.probe
            && self.shared.owner(&addr) == self.me
            && !self.peers.may_ask(&addr, now)
        {
            l.probe = None;
        }
        if l.aim.is_some() {
            return self.fetch_headers(l, now);
        }
        if l.probe.is_some_and(|(_, at, _)| now.saturating_sub(at) < self.cfg.sync.header_spacing) {
            return;
        }
        // Ask whoever claims most where its chain leaves ours.
        let next = self.chain.tip().map_or(0, |t| t.height + 1);
        let Some(source) = self.peers.best_source(best.work, next, now) else {
            return;
        };
        let addr = source.addr;
        self.ask_fork(l, now, addr, None, out);
    }

    /// Asks `addr` where its chain leaves ours. `tip` is the block it
    /// announced, if that is why.
    fn ask_fork(&mut self, l: &mut List, now: Micros, addr: SocketAddrV4, tip: Option<(Digest, u32)>, out: Out<'_>) {
        let Some(token) = self.peers.get(&addr).and_then(|p| p.token()) else {
            return;
        };
        let mut ids = [self.genesis; LOCATOR];
        let Ok(n) = self.chain.header_locator(&mut ids) else {
            return;
        };
        let Some(locator) = Locator::new(&ids[..n]) else {
            return;
        };
        l.probe = Some((addr, now, tip));
        self.peers.asked_headers(&addr, now);
        self.counts.forks_asked += 1;
        self.send(addr, &Message::FindFork { token, locator }, out);
    }

    fn on_fork(&mut self, l: &mut List, now: Micros, from: SocketAddrV4, height: u32, id: Digest) {
        // Only the answer to our question, from whom it was put to.
        let Some((_, _, announced)) = l.probe.filter(|p| p.0 == from && self.peers.proven(&from)) else {
            self.counts.unheard += 1;
            return;
        };
        l.probe = None;
        self.peers.seen(&from, now);
        // A block we hold, at the height it says: or it is no answer.
        let ours = self.chain.known(&id).ok().flatten();
        if ours.is_none_or(|k| k.header.height != height) {
            self.strike(&from, now);
            return;
        }
        // Its tip: the block it announced, or what its last ping said.
        let Some(tip) = announced.or_else(|| self.peers.get(&from).and_then(|p| p.status).map(|s| (s.tip, s.height)))
        else {
            return;
        };
        if tip.1 <= height {
            // Nothing past what we share: its claim was of nothing.
            self.peers.failed(&from, now);
            return;
        }
        // Nor a chain higher than any could be by now: what a peer says
        // of its height is its own word, and the runs of headers to
        // ask for are counted from it.
        let params = self.chain.params();
        let since = self.unix.saturating_add(params.max_future_drift).saturating_sub(params.genesis_timestamp);
        let most = params.final_height().min(since.saturating_mul(8).min(u32::MAX as u64) as u32);
        if tip.1 > most {
            self.peers.failed(&from, now);
            return;
        }
        // A chain that leaves ours under where ours can be undone to is
        // one this node could only take whole, and its headers are kept
        // whatever becomes of it: one such is gone into at a time, and
        // not another for as long as a peer is passed over. (Headers
        // from an old block cost whoever makes them next to nothing,
        // and there is no end of them.)
        //
        // And none of it is kept before it is known to come to more
        // work than the best there is: it is weighed first.
        let ours = self.chain.tip().map_or(0, |tip| tip.height);
        let mut weighing = None;
        if height.saturating_add(self.chain.keep() as u32) < ours {
            if now < l.deep {
                self.peers.failed(&from, now);
                return;
            }
            l.deep = now.saturating_add(self.cfg.sync.pass_over);
            match self.chain.weigh_from(&id) {
                Ok(weighed) => weighing = Some(weighed),
                Err(_) => return self.peers.failed(&from, now),
            }
        }
        l.aim = Some(self.aim(tip, height, from, weighing));
        l.syncing = true;
        self.shared.say(Event::HeadersWanted { from: height + 1, to: tip.1, peer: from });
        self.shared.work(self.me);
        self.fetch_headers(l, now);
    }

    /// The headers of the chain with the tip `tip`, from where it leaves
    /// ours at `fork`: all of them still to be asked for.
    fn aim(
        &self,
        tip: (Digest, u32),
        fork: u32,
        source: SocketAddrV4,
        weighing: Option<crate::chain::headers::Weighed>,
    ) -> Aim {
        Aim {
            tip: tip.0,
            height: tip.1,
            todo: (fork + 1..=tip.1).step_by(self.cfg.sync.headers as usize).collect(),
            done: BTreeMap::new(),
            next: fork + 1,
            keeping: false,
            source,
            refused: Vec::new(),
            fork,
            weighing,
        }
    }

    /// Asks for the runs of headers not yet asked for, as many at once
    /// as may be, each of another peer.
    fn fetch_headers(&mut self, l: &mut List, now: Micros) {
        let Some(aim) = l.aim.as_mut() else {
            return;
        };
        let (most, run) = (self.cfg.sync.header_fetches, self.cfg.sync.headers as u32);
        // No further ahead of what is kept than can wait in memory.
        let ahead = aim.next.saturating_add(2 * most as u32 * run);
        loop {
            let busy = l.fetching.iter().filter(|f| headers(&f.0)).count();
            let Some(&from) = aim.todo.iter().next().filter(|h| **h < ahead && busy < most) else {
                break;
            };
            let count = run.min(aim.height - from + 1) as u16;
            // A peer whose chain reaches the tip aimed at, and that is
            // not at a run of headers for us already.
            let idle = |addr: &SocketAddrV4| {
                !self.fetches.iter().any(|f| f.from == *addr && matches!(f.object, Object::Headers { .. }))
            };
            // Whoever told us of it first: it answers for the chain it
            // spoke of. Then the others whose chains reach as high, but
            // for those that have said theirs is another.
            let source = self.peers.get(&aim.source).filter(|p| self.peers.may_ask(&p.addr, now) && idle(&p.addr));
            let others =
                || self.peers.reaching(aim.height, now).find(|p| idle(&p.addr) && !aim.refused.contains(&p.addr));
            let Some(peer) = source.or_else(others) else {
                break;
            };
            aim.todo.remove(&from);
            let transfer = Self::number(&self.secret, &mut self.numbers);
            let len = count as u32 * HEADER_SIZE as u32;
            let object = Object::Headers { from, count, on: aim.tip };
            l.fetching.push((object, peer.addr));
            self.fetches.push(Fetching {
                object,
                from: peer.addr,
                fetch: Fetch::new(transfer, Some(len), len, peer.path, now),
            });
        }
        // Nothing under way, and nobody to ask, of any worker's peers:
        // the aim is let go, and another is taken from whoever claims
        // most then. (Whoever told us of it is its own worker's to ask,
        // and so that worker's to give up on.)
        if !l.fetching.iter().any(|f| headers(&f.0)) && !aim.todo.is_empty() {
            let (height, source, refused) = (aim.height, aim.source, aim.refused.clone());
            self.view(l, now);
            // (Or nobody of this worker's that has not said it has no
            // such chain, its source no longer to be asked.)
            let nobody = !self.peers.may_ask(&source, now)
                && self.peers.reaching(height, now).all(|p| refused.contains(&p.addr));
            if (!l.views.iter().any(|v| v.reaches(height)) || nobody) && self.shared.owner(&source) == self.me {
                l.aim = None;
            }
        }
    }

    /// A run of headers has arrived whole from `from`.
    fn headers_arrived(&mut self, l: &mut List, now: Micros, from: SocketAddrV4, first: u32, bytes: &[u8]) {
        let Some(aim) = l.aim.as_mut() else {
            return;
        };
        // Headers, of the heights asked for, each the child of the one
        // before: or its sender made them up.
        let mut headers = Vec::with_capacity(bytes.len() / HEADER_SIZE);
        for (k, b) in bytes.chunks(HEADER_SIZE).enumerate() {
            match Header::from_bytes(b) {
                Ok(h)
                    if h.height == first + k as u32
                        && headers.last().is_none_or(|p: &Header| h.prev_hash == p.hash()) =>
                {
                    headers.push(h)
                }
                _ => return self.headers_refused(l, now, from),
            }
        }
        aim.done.insert(first, (headers, from));
        self.keep_headers(l);
        self.fetch_headers(l, now);
    }

    /// Gives the next run of headers to be checked and kept, if it is
    /// here and none is being: in order, one at a time.
    fn keep_headers(&mut self, l: &mut List) {
        let Some(aim) = l.aim.as_mut().filter(|aim| !aim.keeping) else {
            return;
        };
        // A chain being weighed: the run is checked and its work added,
        // here and now (a hash a header), and nothing is kept.
        if aim.weighing.is_some() {
            return self.weigh_headers(l);
        }
        if let Some((headers, from)) = aim.done.remove(&aim.next) {
            aim.keeping = true;
            let first = aim.next;
            // A chain being caught up with, by a node that takes its
            // state whole where it can, and whose blocks' proofs vouch
            // for the work of the blocks under them: the work of each
            // header is left to the proof of the block the state is
            // taken as of, and checked in full from that block up
            // ([`Chain::confirm_work`]), or when its block is applied.
            // From the seed text a header's work is tens of
            // milliseconds, and a year of headers most of an hour.
            //
            // Only of headers further above the chain here than a
            // state is taken under the best: those are the ones a
            // state taken, and the proof of its block, will vouch for.
            // The work of headers nearer is checked as they come: they
            // are what a node goes by from one block to the next, and
            // headers whose work nobody did (a claim costs a sixtieth
            // of the work) would else be its best for as long as their
            // blocks did not come.
            let tip = self.chain.tip().ok().map(|tip| tip.height);
            let defer = defers(self.cfg.sync.sync_point, self.chain.verifier().attests_work(), tip);
            self.work(l, Job::Headers { first, headers, from, unix: self.unix, defer });
        }
    }

    /// The runs of a chain being weighed that are here, in order: each
    /// checked and its work added. At its tip, the chain is fetched
    /// again to be kept if it has more work than the best there is,
    /// and let go if not, whoever told of it having said what was not
    /// so.
    fn weigh_headers(&mut self, l: &mut List) {
        let now = self.now;
        loop {
            let Some(aim) = l.aim.as_mut() else { return };
            let Some(weighed) = aim.weighing.as_mut() else { return };
            let Some((headers, from)) = aim.done.remove(&aim.next) else { return };
            if self.chain.weigh(weighed, &headers, self.unix).is_err() {
                return self.headers_refused(l, now, from);
            }
            aim.next += headers.len() as u32;
            if aim.next <= aim.height {
                continue;
            }
            let (tip, fork, source) = ((aim.tip, aim.height), aim.fork, aim.source);
            let best = self.chain.best_header().map(|k| k.work);
            let heavier = weighed.last().hash() == tip.0 && best.is_ok_and(|best| weighed.work() > best);
            self.counts.weighed += 1;
            if !heavier {
                // (Not what was said, or no more than there is: its
                // source is passed over, and nothing was kept.)
                l.aim = None;
                self.tell(now, source, Notice::Failed(source));
                return;
            }
            l.aim = Some(self.aim(tip, fork, source, None));
            return self.fetch_headers(l, now);
        }
    }

    /// A run of headers has been checked and kept, or refused.
    #[allow(clippy::too_many_arguments)]
    fn headers_kept(
        &mut self,
        l: &mut List,
        now: Micros,
        first: u32,
        count: u32,
        last: Digest,
        from: SocketAddrV4,
        error: bool,
    ) {
        // Of the aim there is now, at the place it has got to: or it
        // was let go meanwhile, and this is of no account.
        let Some(aim) = l.aim.as_mut().filter(|aim| aim.keeping && aim.next == first) else {
            return;
        };
        aim.keeping = false;
        if error {
            return self.headers_refused(l, now, from);
        }
        self.tell(now, from, Notice::SentHeaders(from));
        let Some(aim) = l.aim.as_mut() else {
            return;
        };
        aim.next += count;
        // The last of them is the tip that was aimed at, or the peers
        // that served them are of two minds.
        if aim.next > aim.height {
            if last != aim.tip {
                return self.headers_refused(l, now, from);
            }
            self.shared.say(Event::HeadersKept { height: aim.height });
            l.aim = None;
            return self.sync_blocks(l, now);
        }
        self.keep_headers(l);
        self.fetch_headers(l, now);
    }

    /// `from` served headers that are not what was asked for, or that
    /// the chain refuses: a strike, and the aim is let go. What was
    /// kept stays kept.
    fn headers_refused(&mut self, l: &mut List, now: Micros, from: SocketAddrV4) {
        self.tell(now, from, Notice::Strike(from));
        self.tell(now, from, Notice::Failed(from));
        self.shared.say(Event::HeadersRefused { peer: from });
        l.aim = None;
        self.fetches.retain(|f| !headers(&f.object));
        l.fetching.retain(|f| !headers(&f.0));
    }

    // -- Blocks

    /// "Here is a new block", from `from`.
    fn on_block(&mut self, l: &mut List, now: Micros, from: SocketAddrV4, header: Header, len: u32, out: Out<'_>) {
        // Unasked: only from a peer.
        if !self.peers.proven(&from) {
            self.counts.unheard += 1;
            return;
        }
        self.peers.seen(&from, now);
        let id = header.hash();
        // Its chain reaches there, whatever its last ping said.
        self.peers.reaches(&from, header.height, id);
        // (And every worker is to know it at once: whether anybody
        // holds a block is asked of what each last said of its peers.)
        self.view(l, now);
        // One we have, body and all, is no news.
        if self.chain.known(&id).ok().flatten().is_some_and(|k| !k.header_only()) || l.applying.contains(&id) {
            return;
        }
        // A header kept already is checked already.
        if self.chain.known(&id).ok().flatten().is_some() {
            return self.header_checked(l, now, header, len, from, Verdict::Good, out);
        }
        // One whose parent is not known is known for that here, with
        // nothing given to be done: a peer that speaks of blocks from
        // nowhere, as fast as it can, costs the chain nothing.
        if self.chain.known(&header.prev_hash).ok().flatten().is_none() {
            return self.header_checked(l, now, header, len, from, Verdict::Orphan, out);
        }
        // A new header's work is to be checked, which takes as long as
        // hashing does where there is no table to check it against:
        // given to be done, and heard of later ([`Worker::header_checked`]).
        // No more at once than a few: what waits to be checked is what
        // a peer can have a node hold, and holds up the blocks behind
        // it.
        if self.announcing >= ANNOUNCING {
            self.counts.unheard += 1;
            return;
        }
        self.announcing += 1;
        self.counts.checked += 1;
        self.work(l, Job::Announced { header, len, from, unix: self.unix });
    }

    /// The header of a block `from` announced has been checked: what
    /// follows from what it was found to be.
    #[allow(clippy::too_many_arguments)]
    fn header_checked(
        &mut self,
        l: &mut List,
        now: Micros,
        header: Header,
        len: u32,
        from: SocketAddrV4,
        verdict: Verdict,
        out: Out<'_>,
    ) {
        let id = header.hash();
        match verdict {
            Verdict::Good => {
                if self.announced.len() == ANNOUNCED {
                    self.announced.pop_front();
                }
                self.announced.push_back((id, from, len));
                self.sync_blocks(l, now);
            }
            // Its parent is unknown: we are more than a block behind it.
            // Its headers are asked for now, without waiting for its
            // next ping to say how far it has got.
            Verdict::Orphan => {
                let lately = l.probe.is_some_and(|(_, at, _)| now.saturating_sub(at) < self.cfg.sync.header_spacing);
                if l.aim.is_none() && !lately && self.peers.may_ask(&from, now) {
                    self.ask_fork(l, now, from, Some((id, header.height)), out);
                }
            }
            // Not the announcer's fault, or not yet known to be.
            Verdict::Harmless => {}
            // A header that breaks a rule.
            Verdict::Bad => {
                self.strike(&from, now);
            }
        }
    }

    /// Tells every live peer but `except` of a block: its header, and
    /// how long its body is.
    fn announce(&mut self, now: Micros, header: Header, len: u32, except: Option<SocketAddrV4>, out: Out<'_>) {
        let mut all = Vec::new();
        // (Not to a peer whose chain is as high already, by what it
        // last said of it: a node catching up would tell every peer of
        // every old block as it joined it to its chain, and each of
        // them has had that block for as long as it has been one.)
        let has = |p: &super::peers::Peer| p.status.is_some_and(|theirs| theirs.height >= header.height);
        all.extend(self.peers.live(now).filter(|p| !has(p)).map(|p| p.addr).filter(|a| Some(*a) != except));
        for addr in all {
            self.counts.announced += 1;
            self.send(addr, &Message::Block { header, len }, out);
        }
    }

    /// A peer says it has a transaction: fetched, unless it is here, or
    /// the node is catching up (checked against an old state it would
    /// mostly fail), or as many are being fetched as may be.
    fn on_tx(&mut self, now: Micros, from: SocketAddrV4, id: Digest, len: u32) {
        // Unasked: only from a peer.
        if !self.peers.proven(&from) {
            self.counts.unheard += 1;
            return;
        }
        self.peers.seen(&from, now);
        if len == 0 || len as usize > self.cfg.policy.max_tx_size {
            return;
        }
        let behind = self.chain.receiving() || self.list.read().unwrap_or_else(|e| e.into_inner()).syncing;
        if behind || self.shared.pool().contains(&id) {
            return;
        }
        // It waits its turn, behind what was announced before it.
        if !self.tx_wanted.iter().any(|(wanted, by, _)| *wanted == id && *by == from) {
            if self.tx_wanted.len() >= TX_WANTED {
                self.tx_wanted.pop_front();
            }
            self.tx_wanted.push_back((id, from, len));
        }
        self.fetch_txs(now);
    }

    /// Fetches the transactions that wait to be, the longest waiting
    /// first, as many at once as may be in all and of each peer. One
    /// that is pooled by now, or being fetched, or whose peer is not
    /// to be asked, waits no longer.
    fn fetch_txs(&mut self, now: Micros) {
        let mut later = VecDeque::new();
        while let Some((id, from, len)) = self.tx_wanted.pop_front() {
            let fetching = |f: &&Fetching| matches!(f.object, Object::Tx(_));
            if self.fetches.iter().filter(fetching).count() >= TX_FETCHES {
                later.push_back((id, from, len));
                later.append(&mut self.tx_wanted);
                break;
            }
            if self.shared.pool().contains(&id) {
                continue;
            }
            // Being fetched of another that said it had it: this one
            // waits, and is asked if nothing the pool takes comes of
            // that. (Whoever says first that it has a transaction, and
            // then sends none, or one the pool refuses, would else be
            // the only one ever asked for it.)
            if self.fetches.iter().any(|f| f.object == Object::Tx(id)) {
                later.push_back((id, from, len));
                continue;
            }
            if self.fetches.iter().filter(fetching).filter(|f| f.from == from).count() >= TX_FETCHES_EACH {
                later.push_back((id, from, len));
                continue;
            }
            self.fetch_object(now, Object::Tx(id), from, len);
        }
        self.tx_wanted = later;
    }

    /// A peer new to the node is told of what the node pools, the best
    /// paying first, [`POOL_CATCHUP`] at the most: it was not there
    /// when they were announced.
    fn announce_pool_to(&mut self, to: SocketAddrV4, out: Out<'_>) {
        let mut best: Vec<(u128, Digest, u32)> = {
            let pool = self.shared.pool();
            let rate = |e: &crate::mempool::Entry| ((e.fee as u128) << 32) / e.size().max(1) as u128;
            // (What is held whole: only that can be given.)
            pool.entries().filter(|e| e.whole()).map(|e| (rate(e), e.txid, e.size() as u32)).collect()
        };
        best.sort_unstable_by_key(|b| std::cmp::Reverse(b.0));
        for (_, id, len) in best.into_iter().take(POOL_CATCHUP) {
            self.send(to, &Message::Tx { id, len }, out);
        }
    }

    /// The transaction `id`, of `len` bytes, is told to every peer of
    /// this worker's but `except`.
    fn announce_tx(&mut self, now: Micros, id: Digest, len: u32, except: Option<SocketAddrV4>, out: Out<'_>) {
        let all: Vec<SocketAddrV4> = self.peers.live(now).map(|p| p.addr).filter(|a| Some(*a) != except).collect();
        for addr in all {
            self.send(addr, &Message::Tx { id, len }, out);
        }
    }

    /// A transaction fetched from `from` as the one of id `id`: pooled
    /// if the pool takes it, and then told to everyone else. One that
    /// is not what it was asked for as, or that no honest peer would
    /// have pooled whatever the state, is held against who served it.
    fn tx_arrived(&mut self, now: Micros, from: SocketAddrV4, id: Digest, bytes: &[u8]) {
        let named = crate::transaction::TransactionRef::from_bytes(bytes).is_ok_and(|tx| tx.txid() == id);
        if !named {
            self.strike(&from, now);
            return;
        }
        match pool_tx(&self.chain, &self.shared, bytes, self.unix) {
            Some(Ok(id)) => self.shared.relay(id, bytes.len() as u32, Some(from)),
            Some(Err(Reject::BadSignature | Reject::NoInputs | Reject::NegativeFee)) => {
                self.strike(&from, now);
            }
            // Refused for what this node's pool or state is: no fault
            // of the peer's.
            _ => {}
        }
        // (There is room for another to be fetched.)
        self.fetch_txs(now);
    }

    /// The chain has a new last block, `tip`, and `taken` blocks more
    /// than it had of the branch it is on: the pool is looked over
    /// against the state as it now is, and told what those blocks
    /// made. When each output was made, by its block's time: a
    /// transaction whose outputs are all there has confirmed. And
    /// where each is, which the pool holds against the state before it
    /// believes it: a transaction set aside when the chain went over to
    /// this branch may spend the same output where it is now.
    ///
    /// `over`: the chain went over to this branch, blocks undone. Only
    /// then is anything where it was not: where the chain has only
    /// gone on, what a transaction spent is spent, and an output made
    /// since with the same commitment is another, which that
    /// transaction (its signatures say nothing of where) is not to
    /// spend in its turn.
    fn pool_follows(&self, tip: &Header, taken: u32, over: bool) {
        let Ok(state) = self.chain.whole() else { return };
        let Ok(snapshot) = state.snapshot() else { return };
        let height = snapshot.tip().0 + 1;
        let mut moved: std::collections::HashMap<Digest, Vec<u64>> = std::collections::HashMap::new();
        let mut created: std::collections::HashMap<Digest, u64> = std::collections::HashMap::new();
        // The newest block's outputs are the last before the next
        // position, and each block's before those of the one after it.
        // (If the state has moved on since, the positions are not
        // these: none is said.)
        let mut end = (snapshot.tip().1 == tip.hash()).then_some(snapshot.outputs().next);
        let mut header = Some(*tip);
        for _ in 0..taken.min(POOL_LOOKS_BACK) {
            let Some(h) = header else { break };
            // (Read from the state held: not from the chain again.)
            let Ok(Some(body)) = self.chain.body_of(&snapshot, &h.hash()) else { break };
            let Ok(body) = BodyRef::from_bytes(&body) else { break };
            let outputs = body.outputs();
            // (A block's commits of names take the positions after its
            // outputs.)
            let made = (outputs.len() + body.commits()) as u64;
            let first = end.map(|end| end.saturating_sub(made));
            for (k, o) in outputs.enumerate() {
                created.insert(o.commitment, h.timestamp);
                if let Some(first) = first {
                    moved.entry(o.commitment).or_default().push(first + k as u64);
                }
            }
            end = first;
            header = h.height.checked_sub(1).and_then(|below| self.chain.header_at_of(&snapshot, below).ok().flatten());
        }
        if !over {
            moved.clear();
        }
        let mut pool = self.shared.pool();
        let _ = pool.revalidate(&snapshot, height, &moved, &created, self.unix);
        pool.expire(self.unix);
        // What a block undone has given back to the pool is told to
        // every peer: those on the branch the chain has gone over to
        // never had it.
        let back = pool.take_returned();
        drop(pool);
        for (id, len) in back {
            self.shared.relay(id, len as u32, None);
        }
    }

    /// The bodies the best header's branch still lacks: fetches those
    /// not yet asked for, as many at once as may be, and gives the
    /// first to be applied once it is here. Blocks join the chain in
    /// order, so a body that arrives before the one below it waits.
    fn sync_blocks(&mut self, l: &mut List, now: Micros) {
        // While the state is being taken, no block can join. Nor is one
        // asked for once it is to be: what was asked for is let come.
        // (And where the chain is so far behind that the state is to be
        // taken, that is seen to before a block is asked for.)
        if l.join.is_none() && now >= l.rejoin.0 && self.far_behind(l) {
            self.sync_state(l, now);
        }
        // (Nor is a block asked for that the chain cannot go over to:
        // it would be refused as the last one was, and asked for
        // again.)
        if self.chain.receiving() || l.join.as_ref().is_some_and(|j| j.far) || self.cut_off(l).is_some() {
            return;
        }
        let mut need = vec![self.chain.params().genesis().header; self.cfg.sync.lookahead];
        let n = self.chain.missing_bodies(&mut need).unwrap_or(0);
        let ids: Vec<Digest> = need[..n].iter().map(Header::hash).collect();
        // What is held and no longer wanted is let go.
        l.held.retain(|(id, _, _)| ids.contains(id));
        if l.applying.is_empty()
            && let Some(first) = ids.first()
            && let Some(at) = l.held.iter().position(|(id, _, _)| id == first)
        {
            let (_, block, from) = l.held.swap_remove(at);
            self.give(l, block, Some(from));
        }
        let most = (self.chain.params().max_block_size - HEADER_SIZE) as u32;
        for (id, header) in ids.iter().zip(&need[..n]) {
            let fetching = |f: &Fetching| matches!(f.object, Object::Block(_));
            if l.fetching.iter().filter(|f| matches!(f.0, Object::Block(_))).count() >= self.cfg.sync.blocks {
                break;
            }
            let wanted = Object::Block(*id);
            if l.applying.contains(id)
                || l.held.iter().any(|(held, _, _)| held == id)
                || l.fetching.iter().any(|f| f.0 == wanted)
            {
                continue;
            }
            let free = |addr: &SocketAddrV4| {
                self.fetches.iter().filter(|f| fetching(f) && f.from == *addr).count() < self.cfg.sync.blocks_per_peer
            };
            // Whoever announced it, with the length it gave; else a peer
            // whose chain holds that height, the length to be learned.
            let told = self
                .announced
                .iter()
                .rev()
                .find(|(told, addr, _)| told == id && self.peers.may_ask(addr, now) && free(addr));
            let source = match told {
                Some((_, addr, len)) => Some((*addr, Some(*len).filter(|l| *l > 0 && *l <= most))),
                None => self
                    .peers
                    .holders(header.height, now)
                    .find(|p| free(&p.addr) && !self.lacking.contains(&(*id, p.addr)))
                    .map(|p| (p.addr, None)),
            };
            // Nobody: then one that is passed over, if it has been so
            // for a little while, rather than nobody at all. (Nobody
            // of any worker's: another's peer that can be asked is
            // that worker's to ask.)
            let nobody = source.is_none() && !l.views.iter().any(|v| v.holds(header.height));
            let source = source.or_else(|| {
                let rested = self.cfg.sync.header_wait;
                let again = self.peers.holders_rested(header.height, now, rested);
                again
                    .filter(|_| nobody)
                    .find(|p| free(&p.addr) && !self.lacking.contains(&(*id, p.addr)))
                    .map(|p| (p.addr, None))
            });
            // In order: a body nobody holds is not to be had, and those
            // above it could not join the chain without it.
            let Some((addr, len)) = source else {
                break;
            };
            let path = self.peers.get(&addr).map(|p| p.path).unwrap_or_default();
            let transfer = Self::number(&self.secret, &mut self.numbers);
            l.fetching.push((wanted, addr));
            self.fetches.push(Fetching {
                object: wanted,
                from: addr,
                fetch: Fetch::new(transfer, len, most, path, now),
            });
        }
    }

    /// A body has arrived whole from `from`.
    fn body_arrived(&mut self, l: &mut List, now: Micros, from: SocketAddrV4, id: Digest, body: &[u8]) {
        let Some(known) = self.chain.known(&id).ok().flatten() else {
            return;
        };
        let mut block = Vec::with_capacity(HEADER_SIZE + body.len());
        block.extend_from_slice(&known.header.to_bytes());
        block.extend_from_slice(body);
        l.held.push((id, block, from));
        self.sync_blocks(l, now);
    }

    /// What became of the blocks given to be applied.
    fn applied(&mut self, l: &mut List, now: Micros, out: Out<'_>) {
        loop {
            let outcome = match &mut l.applier {
                Applier::Here(done) => done.pop_front(),
                Applier::Thread(_, done) => done.get_mut().unwrap_or_else(|e| e.into_inner()).try_recv().ok(),
            };
            let Some(outcome) = outcome else {
                return;
            };
            // (One fewer waiting to be heard of: never below none.)
            let mut ready = self.shared.ready.load(Ordering::Relaxed);
            while ready > 0 {
                match self.shared.ready.compare_exchange_weak(ready, ready - 1, Ordering::Relaxed, Ordering::Relaxed) {
                    Ok(_) => break,
                    Err(now) => ready = now,
                }
            }
            self.shared.work(self.me);
            l.outstanding = l.outstanding.saturating_sub(1);
            match outcome {
                Outcome::Block { header, len, from, result } => {
                    self.block_applied(l, now, header, len, from, result, out)
                }
                Outcome::Headers { first, count, last, from, new, error } => {
                    self.counts.headers += new as u64;
                    self.headers_kept(l, now, first, count, last, from, error.is_some());
                }
                Outcome::Nothing => {}
                Outcome::BadLeaves { from } => self.tell(now, from, Notice::Strike(from)),
                // What follows is of the peer that announced it: its own
                // worker's to do.
                Outcome::Announced { header, len, from, verdict } => match self.shared.owner(&from) {
                    owner if owner == self.me => {
                        self.announcing = self.announcing.saturating_sub(1);
                        self.header_checked(l, now, header, len, from, verdict, out)
                    }
                    owner => self.shared.post(owner, Notice::Announced { header, len, from, verdict }),
                },
                Outcome::Confirmed { target, held } => {
                    l.confirming = false;
                    if let Some(join) = l.join.as_mut().filter(|j| Some(j.id) == target) {
                        if held {
                            join.worked = true;
                            self.advance_join(l, now);
                        } else {
                            // Headers that were nobody's work: they are
                            // the best no longer, and nothing is taken
                            // as of a block under them.
                            l.join = None;
                            self.fetches.retain(|f| !of_state(&f.object));
                            l.fetching.retain(|f| !of_state(&f.0));
                            self.join_failed(l, now);
                        }
                    } else {
                        // (What was confirmed was not what is being
                        // taken now, which waited for it to be done.)
                        self.advance_join(l, now);
                    }
                }
                Outcome::Checked { target, result } => self.state_block_checked(l, now, target, result),
                Outcome::Begun { target, result } => {
                    if let Some(join) = l.join.as_mut().filter(|j| j.id == target) {
                        join.beginning = false;
                        match result {
                            Ok(()) => join.begun = true,
                            Err(_) => {
                                l.join = None;
                                self.join_failed(l, now);
                            }
                        }
                    }
                    self.advance_join(l, now);
                }
                Outcome::Piece { object, from, result } => {
                    if self.of_join(l, &object)
                        && let Some(join) = l.join.as_mut()
                    {
                        join.putting.retain(|o| *o != object);
                        // Not the part of its root, or no part at all:
                        // its sender's doing. Anything else is ours.
                        if matches!(result, Err(Error::PartRoot | Error::Malformed(_))) {
                            join.unserved.push(from);
                            self.tell(now, from, Notice::Strike(from));
                        }
                    }
                    self.advance_join(l, now);
                }
                Outcome::Finished { target, result } => {
                    if l.join.as_ref().is_some_and(|j| j.id == target) {
                        // Whole, or not: either way this taking is over.
                        // (Not whole, the chain is receiving still, and
                        // another is begun when time is next looked to.)
                        let height = l.join.as_ref().map_or(0, |j| j.target.height);
                        l.join = None;
                        match result.is_ok() {
                            true => l.rejoin = (0, 0),
                            false => self.join_failed(l, now),
                        }
                        if result.is_ok() {
                            self.counts.states += 1;
                            // (The chain has a new last block by it,
                            // for whoever goes by that.)
                            self.shared.blocks.fetch_add(1, Ordering::Relaxed);
                            self.shared.say(Event::StateTaken { height });
                        }
                    }
                    self.sync_blocks(l, now);
                }
            }
        }
    }

    /// What became of a block given to be applied.
    #[allow(clippy::too_many_arguments)]
    fn block_applied(
        &mut self,
        l: &mut List,
        now: Micros,
        header: Header,
        len: u32,
        from: Option<SocketAddrV4>,
        result: Result<Applied, Error>,
        out: Out<'_>,
    ) {
        let id = header.hash();
        l.applying.retain(|a| *a != id);
        match result {
            // The chain's new last block: every peer is told, but the
            // one it came from.
            Ok(Applied::Extended | Applied::Reorganized { .. }) => {
                self.counts.blocks += 1;
                self.shared.blocks.fetch_add(1, Ordering::Relaxed);
                let (undone, taken) = match result {
                    Ok(Applied::Reorganized { fork_height, unwound }) => (unwound, header.height - fork_height),
                    _ => (0, 1),
                };
                // The pool first: whoever waits for the chain to move
                // makes the next block of what the pool then holds, and
                // would else make it of what this block has just taken.
                self.pool_follows(&header, taken, undone > 0);
                // (Whoever waits for the chain to move is told.)
                drop(self.shared.moved.0.lock().unwrap_or_else(|e| e.into_inner()));
                self.shared.moved.1.notify_all();
                self.shared.say(Event::Block { header, len, from, undone, taken });
                // Caught up, if a chain ahead was being caught up with.
                let mut first = [header];
                if l.syncing
                    && l.aim.is_none()
                    && l.join.is_none()
                    && self.chain.missing_bodies(&mut first).unwrap_or(0) == 0
                {
                    l.syncing = false;
                    self.shared.say(Event::Synced { height: header.height });
                }
                self.announce(now, header, len, from, out);
                self.shared.post_others(self.me, Notice::Announce { header, len, except: from });
            }
            Ok(Applied::Side) => {
                if let Some(from) = from {
                    if l.sides.len() == SIDES {
                        l.sides.pop_front();
                    }
                    l.sides.push_back((id, from));
                }
                self.shared.say(Event::Side { header, from })
            }
            Ok(Applied::Known) => {}
            Err(e) => {
                self.counts.blocks_refused += 1;
                self.shared.say(Event::BlockRefused { header, from, why: e.to_string() });
                l.cut |= e == Error::NoUndoRecord;
                // A body that is not the header's, a proof that does
                // not hold (the block may be good, and is asked of
                // another), or a block that breaks a rule: whoever
                // served it answers for it.
                if let Some(from) = from
                    && (e == Error::BadBodyCommitment || e == Error::BadProof || condemns(&e))
                {
                    self.tell(now, from, Notice::Strike(from));
                    self.tell(now, from, Notice::Failed(from));
                    self.tell(now, from, Notice::NotFrom(id, from));
                }
                // A block kept earlier on the branch, whose proof did
                // not hold now that it was looked at: whoever served
                // that one answers for it, and it is not asked of them
                // again.
                if let Error::BadProofBefore(bad) = e
                    && let Some(at) = l.sides.iter().position(|(side, _)| Error::id_half(side) == bad)
                    && let Some((side, served)) = l.sides.remove(at)
                {
                    self.tell(now, served, Notice::Strike(served));
                    self.tell(now, served, Notice::Failed(served));
                    self.tell(now, served, Notice::NotFrom(side, served));
                }
            }
        }
        // What came of a block made here, whatever it was: whoever made
        // it is waiting to know. (Said last: so that the chain is seen
        // to have moved, if it has, by whoever is woken by this.)
        if from.is_none() {
            self.shared.settled.fetch_add(1, Ordering::Relaxed);
            drop(self.shared.moved.0.lock().unwrap_or_else(|e| e.into_inner()));
            self.shared.moved.1.notify_all();
        }
        // (A state that waited for this block to be done with before
        // it began to be received goes on.)
        if l.join.is_some() && l.applying.is_empty() {
            self.advance_join(l, now);
        }
        self.sync_blocks(l, now);
    }

    // -- The state, taken whole

    /// Whether `object` is a piece of the state being taken.
    fn of_join(&self, l: &List, object: &Object) -> bool {
        let Some(join) = &l.join else {
            return false;
        };
        match object {
            Object::Block(id) | Object::Manifest(id) => *id == join.id,
            Object::Roots { block, .. } | Object::Part { block, .. } | Object::Names { block, .. } => *block == join.id,
            _ => false,
        }
    }

    /// Takes the state whole when the blocks cannot be had: the bodies
    /// the chain needs next are held by nobody, and some peer can still
    /// go back to a block [`super::config::Sync::sync_point`] under the
    /// best header. Then, step by step: that block and the top of its
    /// state; the block's proof; the roots of the state's parts; the
    /// parts. Each piece from whichever peer's turn it is, several at
    /// once, each checked before the next is believed.
    fn sync_state(&mut self, l: &mut List, now: Micros) {
        self.view(l, now);
        if l.join.is_none() {
            if now < l.rejoin.0 || !self.begin_join(l) {
                return;
            }
            if let Some(j) = &l.join {
                self.shared.say(Event::StateWanted { height: j.target.height, id: j.id, again: false });
            }
        }
        let Some(join) = l.join.as_mut() else {
            return;
        };
        // Who can serve it: those that can still go back to its block.
        let mut servers: Vec<SocketAddrV4> =
            self.peers.servers_of_state(join.target.height, now).map(|p| p.addr).collect();
        // None of this worker's, but another's: theirs to ask.
        if servers.is_empty() && l.views.iter().any(|v| v.serves(join.target.height)) {
            return;
        }
        if servers.is_empty() {
            // Nobody, for long enough: the block is given up for a
            // later one, and what was taken of its state that is the
            // same in the later one's is kept.
            let since = *join.orphaned.get_or_insert(now);
            if now.saturating_sub(since) >= self.cfg.sync.header_wait {
                l.join = None;
                self.fetches.retain(|f| !of_state(&f.object));
                l.fetching.retain(|f| !of_state(&f.0));
                // (Begun anew, the chain goes on with what it has
                // received: `Chain::begin_receiving`.)
                if self.begin_join(l) {
                    self.counts.states_moved += 1;
                    if let Some(j) = &l.join {
                        self.shared.say(Event::StateWanted { height: j.target.height, id: j.id, again: true });
                    }
                }
            }
            return;
        }
        join.orphaned = None;
        // Those that have not failed us in this first, while there are.
        if servers.iter().any(|a| !join.unserved.contains(a)) {
            servers.retain(|a| !join.unserved.contains(a));
        } else {
            // Every one of them has: all are asked again, but later,
            // and later each time. (Peers that say they can serve a
            // state and do not would else be asked as fast as they
            // answer, for ever.)
            let wait = self.cfg.sync.header_wait.saturating_mul(1 << join.rounds.min(6)).min(self.cfg.sync.pass_over);
            match *join.again.get_or_insert(now.saturating_add(wait)) {
                at if now < at => return,
                _ => {
                    join.unserved.clear();
                    join.again = None;
                    join.rounds += 1;
                }
            }
            // A state taken though blocks could be had, which those
            // that say they have it do not give, round after round: it
            // is let be for a while, and blocks are taken meanwhile.
            // (Not once the state here is given up for it; nor where
            // the chain cannot go on by blocks at all.)
            if join.far && !join.begun && !join.beginning && join.rounds >= FAR_ROUNDS && !l.cut {
                l.join = None;
                self.fetches.retain(|f| !of_state(&f.object));
                l.fetching.retain(|f| !of_state(&f.0));
                l.rejoin = (now.saturating_add(self.cfg.sync.pass_over), l.rejoin.1.saturating_add(1));
                return;
            }
        }
        // What is wanted now, in order of need.
        let id = join.id;
        let mut wanted: Vec<(Object, u32)> = Vec::new();
        if join.block.is_none() {
            wanted.push((Object::Block(id), (self.chain.params().max_block_size - HEADER_SIZE) as u32));
        }
        match &join.manifest {
            None => wanted.push((Object::Manifest(id), snapshot::MAX_MANIFEST as u32)),
            Some((manifest, _)) if join.checked && !join.begun => {
                for (range, _) in &manifest.ranges {
                    if !join.roots.contains_key(range) {
                        wanted.push((Object::Roots { block: id, index: *range }, snapshot::MAX_ROOTS as u32));
                    }
                }
            }
            Some(_) => {}
        }
        if join.begun
            && let Ok((parts, lacking, names)) =
                self.chain.missing_parts_first(self.cfg.sync.parts + join.putting.len() + l.fetching.len())
        {
            // How far it has come is said every half minute.
            let missing = (lacking + names.len()) as u64;
            join.parts = join.parts.max(missing);
            if join.told == 0 {
                join.told = now;
            } else if now.saturating_sub(join.told) >= 30 * crate::transport::SECOND && missing > 0 {
                join.told = now;
                self.shared.say(Event::StateProgress { parts: join.parts - missing, of: join.parts });
            }
            wanted.extend(parts.iter().map(|i| (Object::Part { block: id, index: *i }, snapshot::MAX_PART as u32)));
            wanted.extend(names.iter().map(|i| (Object::Names { block: id, index: *i }, snapshot::MAX_NAMES as u32)));
            // (But for those that are here, and being kept.)
            wanted.retain(|(object, _)| !join.putting.contains(object));
        }
        for (object, most) in wanted {
            let under_way = l.fetching.iter().filter(|f| f.0 != object && of_state(&f.0));
            if under_way.count() >= self.cfg.sync.parts {
                break;
            }
            if l.fetching.iter().any(|f| f.0 == object) {
                continue;
            }
            // From the next of them that is not asked for as much as one
            // peer is asked for at once: a peer answers only so many
            // requests of one address at a time, and what it is asked
            // beyond that is as good as lost.
            let most_each = self.cfg.sync.blocks_per_peer;
            let free = (1..=servers.len())
                .map(|k| servers[join.turn.wrapping_add(k) % servers.len()])
                .position(|peer| self.fetches.iter().filter(|f| f.from == peer).count() < most_each);
            let Some(free) = free else { break };
            join.turn = join.turn.wrapping_add(free + 1);
            let from = servers[join.turn % servers.len()];
            let path = self.peers.get(&from).map(|p| p.path).unwrap_or_default();
            let transfer = Self::number(&self.secret, &mut self.numbers);
            l.fetching.push((object, from));
            self.fetches.push(Fetching { object, from, fetch: Fetch::new(transfer, None, most, path, now) });
        }
    }

    /// A taking of the state came to nothing: the next is not begun at
    /// once, and each one after waits longer, up to as long as a peer
    /// is passed over.
    fn join_failed(&mut self, l: &mut List, now: Micros) {
        let wait = self.cfg.sync.header_wait.saturating_mul(1 << l.rejoin.1.min(6)).min(self.cfg.sync.pass_over);
        l.rejoin = (now.saturating_add(wait), l.rejoin.1.saturating_add(1));
    }

    /// Whether the chain is further under the best header than a node
    /// catches up from block by block
    /// ([`super::config::Sync::sync_behind`]).
    /// Where the branch with the most work leaves the chain, if the
    /// chain cannot undo so far and a block was refused for it.
    fn cut_off(&self, l: &mut List) -> Option<u32> {
        if !l.cut {
            return None;
        }
        match self.chain.cut_off() {
            Ok(Some(fork)) => Some(fork),
            // (While the state is being taken there is nothing to
            // undo, and what it will be cut off from is not known.)
            Err(Error::Receiving) => None,
            _ => {
                l.cut = false;
                None
            }
        }
    }

    /// Whether the state is to be taken though blocks could be had:
    /// the chain is further behind than it is set to catch up from, or
    /// cannot go back to where the branch with the most work leaves
    /// it.
    fn far_behind(&self, l: &mut List) -> bool {
        let (point, behind) = (self.cfg.sync.sync_point, self.cfg.sync.sync_behind);
        if point == 0 || self.chain.receiving() {
            return false;
        }
        if self.cut_off(l).is_some() {
            return true;
        }
        if behind == 0 {
            return false;
        }
        match (self.chain.best_header(), self.chain.tip()) {
            (Ok(best), Ok(tip)) => best.header.height.saturating_sub(tip.height) > behind,
            _ => false,
        }
    }

    /// Chooses the block to take the state as of, if it is to be taken
    /// at all. True if one was chosen.
    fn begin_join(&mut self, l: &mut List) -> bool {
        let point = self.cfg.sync.sync_point;
        // (So far behind that the state is taken though the blocks
        // could be had: whatever is being done with blocks goes on
        // until the chain begins to receive it.)
        let far = self.far_behind(l);
        if point == 0 || l.aim.is_some() || (!far && !l.applying.is_empty()) {
            return false;
        }
        let Ok(best) = self.chain.best_header().map(|k| k.header) else {
            return false;
        };
        // Already receiving (and the block it was as of given up): on,
        // as of another. Else only where blocks cannot be had: the
        // first body wanted is held by nobody that is there to ask.
        if !self.chain.receiving() && !far {
            let mut first = [best];
            if self.chain.missing_bodies(&mut first).unwrap_or(0) == 0
                || !l.views.iter().any(|v| v.live > 0)
                || l.views.iter().any(|v| v.holds(first[0].height))
                || l.fetching.iter().any(|f| matches!(f.0, Object::Block(_)))
                || !l.held.is_empty()
            {
                return false;
            }
        }
        // As far under the best header as is asked, if anyone can go
        // back so far; else as far back as anyone can.
        let Some(reach) = state_reach(&l.views) else {
            return false;
        };
        // (And of the branch the chain cannot go over to, if it is cut
        // off from one: above where that branch leaves it.)
        let above = self.cut_off(l).map_or(0, |fork| fork + 1);
        let height = best.height.saturating_sub(point).max(reach).max(above).max(1);
        if height > best.height {
            return false;
        }
        let Ok(Some(mut target)) = self.chain.ancestor(&best, height) else {
            return false;
        };
        // Never back: that block is the chain's own, at its last or
        // under it. The state here is later than the one that would be
        // taken, and what the chain lacks is the blocks after where the
        // best header's branch leaves it, which it waits for. (A header
        // whose block nobody has, announced by a node that then went
        // away, would else send every node of a network back by that
        // many blocks, each taking from the others the state they all
        // had before.)
        if !self.chain.receiving()
            && let Ok(tip) = self.chain.tip()
            && tip.height >= height
            && matches!(self.chain.header_at(height), Ok(Some(ours)) if ours.hash() == target.hash())
        {
            // (And the work of what it waits for is checked in full, if
            // any of it was left to a proof: headers that are nobody's
            // work are the best no longer.)
            // (Once for a header: asked again at every turn and by
            // every worker told of the answer, it would be all the
            // node did while the block is not to be had.)
            if !l.confirming && l.waited != Some(best.hash()) {
                (l.confirming, l.waited) = (true, Some(best.hash()));
                self.counts.confirms += 1;
                self.work(l, Job::Confirm { best, from: height.saturating_add(1), target: None });
            }
            return false;
        }
        // A state that was being received already (the node stopped
        // and started while it was): as of the same block, if that can
        // still be had, so that nothing received is asked for again.
        if let Some((was, id)) = self.chain.receiving_as_of()
            && (reach..=best.height).contains(&was)
            && let Ok(Some(same)) = self.chain.ancestor(&best, was)
            && same.hash() == id
        {
            target = same;
        }
        // (The work of that header and of those after it is checked in
        // full before anything of the state is believed: the first step
        // of taking it, [`Node::advance_join`].)
        l.syncing = true;
        l.join = Some(Join {
            id: target.hash(),
            target,
            block: None,
            manifest: None,
            checked: false,
            checking: false,
            best,
            worked: false,
            far,
            roots: BTreeMap::new(),
            begun: false,
            beginning: false,
            putting: Vec::new(),
            finishing: false,
            unserved: Vec::new(),
            turn: 0,
            parts: 0,
            told: 0,
            refused: 0,
            orphaned: None,
            again: None,
            rounds: 0,
        });
        true
    }

    /// A piece of the state being taken has arrived whole from `from`.
    fn piece_arrived(&mut self, l: &mut List, now: Micros, object: Object, from: SocketAddrV4, bytes: &[u8]) {
        let Some(join) = l.join.as_mut() else {
            return;
        };
        // What a piece is checked against, and what is done with one
        // that is not what it should be: its sender is struck, and it
        // is asked of another.
        let good = match object {
            Object::Block(_) => {
                let mut block = join.target.to_bytes().to_vec();
                block.extend_from_slice(bytes);
                let good = BlockRef::from_bytes(&block).is_ok_and(|b| b.body_commitment_matches());
                if good {
                    join.block = Some((block, from));
                }
                good
            }
            Object::Manifest(_) => match Manifest::decode(bytes) {
                Ok(manifest) if manifest.check(&join.target.state_root) => {
                    join.manifest = Some((manifest, from));
                    true
                }
                _ => false,
            },
            Object::Roots { index, .. } => {
                let want =
                    join.manifest.as_ref().and_then(|(m, _)| m.ranges.iter().find(|r| r.0 == index)).map(|r| r.1);
                match want.map(|root| snapshot::decode_roots(bytes, index, &root)) {
                    Some(Ok(parts)) => {
                        join.roots.insert(index, parts);
                        true
                    }
                    Some(Err(_)) => false,
                    None => true,
                }
            }
            // Checked where it is kept, which takes a write to the store:
            // given to be done, and heard of later.
            Object::Part { .. } | Object::Names { .. } => {
                join.putting.push(object);
                self.work(l, Job::Piece { object, bytes: bytes.to_vec(), from });
                return;
            }
            _ => true,
        };
        if !good {
            self.strike(&from, now);
            join.unserved.push(from);
        }
        self.advance_join(l, now);
    }

    /// The next step of the state being taken that waits for nothing,
    /// given to whoever does what takes time; and what is still wanted
    /// of it asked for ([`Worker::sync_state`]). Asked at every turn,
    /// and whenever something it waited for is done: each step is
    /// begun once, and none is left for an arrival that may never come.
    fn advance_join(&mut self, l: &mut List, now: Micros) {
        // The work of the headers from its block on, in full: no proof
        // to come vouches for it.
        if let Some((best, from, id)) = l.join.as_ref().filter(|j| !j.worked).map(|j| (j.best, j.target.height, j.id))
            && !l.confirming
        {
            l.confirming = true;
            self.work(l, Job::Confirm { best, from, target: Some(id) });
        }
        let Some(join) = l.join.as_mut() else {
            return self.sync_state(l, now);
        };
        // The block and the top of its state: the block's proof, held to
        // where the manifest says its outputs end.
        if join.worked
            && !join.checked
            && !join.checking
            && let (Some((block, _)), Some((manifest, _))) = (&join.block, &join.manifest)
        {
            join.checking = true;
            let job = Job::Check { block: block.clone(), next: manifest.next, roots: manifest.roots() };
            return self.work(l, job);
        }
        // Every range's roots: the state can begin to be received. (With
        // no block on its way to the chain: the state there is is given
        // up for it.)
        if join.checked
            && !join.begun
            && !join.beginning
            && l.applying.is_empty()
            && let Some((manifest, _)) = &join.manifest
            && manifest.ranges.iter().all(|(range, _)| join.roots.contains_key(range))
        {
            join.beginning = true;
            let job = Job::Begin {
                target: join.target,
                next: manifest.next,
                parts: join.roots.values().flatten().copied().collect(),
                name_parts: manifest.name_parts.clone(),
            };
            return self.work(l, job);
        }
        // Every part: the chain is to be made whole, at the block.
        if join.begun
            && !join.finishing
            && join.putting.is_empty()
            && self.chain.missing_parts_first(1).is_ok_and(|(_, lacking, names)| lacking == 0 && names.is_empty())
            && let Some((block, _)) = &join.block
        {
            join.finishing = true;
            let job = Job::Finish { target: join.id, body: block[HEADER_SIZE..].to_vec() };
            return self.work(l, job);
        }
        self.sync_state(l, now);
    }

    /// The block a state is to be taken as of has been checked by its
    /// proof, or refused.
    fn state_block_checked(&mut self, l: &mut List, now: Micros, target: Digest, result: Result<(), Error>) {
        let Some(join) = l.join.as_mut().filter(|j| j.id == target && j.checking) else {
            return;
        };
        join.checking = false;
        match result {
            Ok(()) => join.checked = true,
            // The block's body is its header's, but its proof is not
            // under the header, and where its outputs end is the
            // manifest's word: one of the two failed, and which is not
            // known. Both are asked for again, of others. Whoever
            // served both is struck, the fault being its own; where two
            // served them neither is, for one of them did nothing
            // wrong, and a peer that served one false piece would else
            // have those that served the true ones struck beside it,
            // time after time, until they were refused.
            Err(_) => {
                let mut served: Vec<SocketAddrV4> = join.manifest.take().map(|(_, from)| from).into_iter().collect();
                served.extend(join.block.take().map(|(_, from)| from).filter(|from| !served.contains(from)));
                let alone = served.len() == 1;
                for from in served {
                    join.unserved.push(from);
                    if alone {
                        self.tell(now, from, Notice::Strike(from));
                    }
                }
                join.refused += 1;
                if join.refused >= self.cfg.sync.snapshot_attempts {
                    l.join = None;
                    self.join_failed(l, now);
                    return;
                }
            }
        }
        self.advance_join(l, now);
    }

    // -- Objects

    fn on_get(&mut self, now: Micros, from: SocketAddrV4, get: &Get<'_>) {
        // A name of nothing is asked for by nobody honest.
        if Object::decode(get.name).is_err() {
            self.counts.malformed += 1;
            return;
        }
        match self.serve.get(&self.tokens, SocketAddr::V4(from), get) {
            Ok(()) => self.peers.seen(&from, now),
            // Without its token, or more than may wait: not heard.
            Err(_) => self.counts.unheard += 1,
        }
    }

    fn on_chunk(&mut self, now: Micros, from: SocketAddrV4, chunk: &Chunk<'_>) {
        // For a fetch of ours, from whom it was asked of, by its number.
        let Some(f) = self.fetches.iter_mut().find(|f| f.from == from && f.fetch.transfer() == chunk.transfer) else {
            self.counts.unheard += 1;
            return;
        };
        self.peers.seen(&from, now);
        // (A chunk no honest peer sends ends the fetch, and the fetch
        // says so when it is next looked to.)
        let _ = f.fetch.chunk(now, chunk);
    }

    /// The bytes of the object named, if this node has it. Kept a
    /// while, since every chunk of it is asked for by name.
    fn object(&mut self, object: &Object) -> Option<Arc<Vec<u8>>> {
        if let Some(at) = self.served.iter().position(|(o, _)| o == object) {
            let hit = self.served.remove(at).expect("it is there");
            self.served.push_front(hit);
            return Some(Arc::clone(&self.served[0].1));
        }
        self.unread.set(false);
        let bytes = self.make(object)?;
        // (What a name is of for good is kept: not the newest a wallet
        // announced, nor the certificate it is a name by, which are
        // another's tomorrow under the same name.)
        if matches!(object, Object::Announce { seq: 0, .. } | Object::Alias(_)) {
            return Some(Arc::new(bytes));
        }
        #[cfg(test)]
        let bytes = if self.spoil {
            let mut b = bytes;
            let at = b.len() / 2;
            b[at] ^= 1;
            b
        } else {
            bytes
        };
        self.served.push_front((*object, Arc::new(bytes)));
        // The oldest go, down to what may be kept: but never the one
        // just made.
        let mut kept = 0;
        let fit = self.served.iter().take_while(|(_, b)| {
            kept += b.len();
            kept <= SERVED_BYTES
        });
        let keep = fit.count().clamp(1, SERVED_MOST);
        self.served.truncate(keep);
        Some(Arc::clone(&self.served[0].1))
    }

    fn make(&self, object: &Object) -> Option<Vec<u8>> {
        #[cfg(test)]
        if self.withhold && of_state(object) && !matches!(object, Object::Block(_)) {
            return None;
        }
        #[cfg(test)]
        if let (Object::Block(id), Some((foisted, body))) = (object, &self.foist)
            && id == foisted
        {
            return Some(body.clone());
        }
        match *object {
            Object::Headers { from, count, on } => {
                // Of the chain `on` is on, and no higher than it: so
                // that the name is of the same bytes whoever serves it.
                let top = self.on_chain(&on)?;
                if from.checked_add(count as u32 - 1)? > top.height {
                    return None;
                }
                let mut headers = vec![top; count as usize];
                if self.chain.headers_from(from, &mut headers).ok()? != count as usize {
                    return None;
                }
                // (Read of the chain `on` was on a moment ago: if it is
                // on it no longer, these may be another's.)
                if self.on_chain(&on) != Some(top) {
                    return None;
                }
                let mut bytes = Vec::with_capacity(count as usize * HEADER_SIZE);
                headers.iter().for_each(|h| bytes.extend_from_slice(&h.to_bytes()));
                Some(bytes)
            }
            Object::Block(id) => match self.chain.body(&id) {
                Ok(body) => body,
                // (Not read is not "not here": said to be gone, the
                // block would not be asked of this node again.)
                Err(_) => {
                    self.unread.set(true);
                    None
                }
            },
            // (Held whole; one only known of is not here to be given,
            // which whoever asks takes for that and no more.)
            Object::Tx(id) => self.shared.pool().entry(&id).and_then(|e| e.bytes().map(<[u8]>::to_vec)),
            Object::File(id) => self.chain.consensus_file_by_id(&id).ok().flatten(),
            // What a wallet announced: this node's own wallet's, by its
            // number, to the node it was made for; or, of a node that
            // holds sessions, the newest it has of the wallet asked of.
            Object::Announce { id, seq } if seq != 0 => {
                let wallet = self.shared.participant.lock().unwrap_or_else(|e| e.into_inner());
                let own = wallet.as_ref().filter(|w| w.id() == id)?;
                own.announced(seq).map(|a| a.to_vec())
            }
            Object::Announce { id, .. } if self.cfg.relay => {
                let sessions = self.shared.sessions.lock().unwrap_or_else(|e| e.into_inner());
                sessions.announced(&id, self.unix, self.now)
            }
            // The certificate by which this node's wallet is a full
            // name: for the node that name is reached at.
            Object::Alias(n) => {
                let wallet = self.shared.participant.lock().unwrap_or_else(|e| e.into_inner());
                wallet.as_ref()?.alias_bundle(&n).map(|bundle| bundle.to_vec())
            }
            // A sealed message: one this node's wallet sends, or one it
            // passes on.
            Object::Sealed(id) => {
                let mail = self.shared.letters.lock().unwrap_or_else(|e| e.into_inner());
                mail.sealed(&id).map(|s| s.to_vec())
            }
            // Something on its way to a neighbour on a way, which now
            // asks for it.
            Object::Step(name) => {
                let mut leaving = self.shared.leaving.lock().unwrap_or_else(|e| e.into_inner());
                let leaving = leaving.iter_mut().find(|l| l.name == name)?;
                leaving.asked = true;
                Some(leaving.bytes.to_vec())
            }
            // The state as of a block of the chain that can still be
            // gone back to, in its pieces (`super::snapshot`).
            Object::Manifest(block) => self.past(&block, |past| Some(Manifest::of(past).encode())),
            Object::Roots { block, index } => self.past(&block, |past| snapshot::encode_roots(past, index)),
            Object::Part { block, index } => self.past(&block, |past| {
                let outputs = past.part(index).ok().filter(|o| !o.is_empty())?;
                Some(snapshot::encode_part(&outputs, &past.commits(index).ok()?))
            }),
            Object::Names { block, index } => self.past(&block, |past| {
                let records = past.names_part(index).ok().filter(|r| !r.is_empty())?;
                Some(snapshot::encode_names(&records))
            }),
            // Nothing else is served yet.
            _ => None,
        }
    }

    /// What `make` makes of the state as of the block `block`, if that
    /// is a block of the chain here recent enough to go back to, and
    /// the state here is whole.
    fn past<T>(&self, block: &Digest, make: impl FnOnce(&crate::store::state::Past<'_, B>) -> Option<T>) -> Option<T> {
        let height = self.on_chain(block)?.height;
        let state = self.chain.whole().ok()?;
        // (The state as of that block, and of no other the chain went
        // over to at that height meanwhile.)
        let past = state.past(height).ok()?;
        (past.tip() == (height, *block)).then(|| make(&past)).flatten()
    }

    /// Fetches `object`, of `most` bytes at the most, from `from`: what
    /// comes of it is in [`Node::take_fetched`] when it has. False if
    /// `from` is no peer to ask.
    fn fetch_object(&mut self, now: Micros, object: Object, from: SocketAddrV4, most: u32) -> bool {
        if !self.peers.may_ask(&from, now) {
            return false;
        }
        let path = self.peers.get(&from).map(|p| p.path).unwrap_or_default();
        let transfer = Self::number(&self.secret, &mut self.numbers);
        self.fetches.push(Fetching { object, from, fetch: Fetch::new(transfer, None, most, path, now) });
        true
    }

    /// The objects asked for with [`Node::fetch_object`] that have come
    /// whole, or been given up (no bytes), since this was last called.
    fn take_fetched(&mut self) -> Vec<(Object, SocketAddrV4, Option<Vec<u8>>)> {
        std::mem::take(&mut self.inbox)
    }

    /// Does what the fetches under way and the chunks being served want
    /// done at `now`, and says when either next wants doing.
    fn pump(&mut self, now: Micros, out: Out<'_>) -> Micros {
        let mut wake = self.fetch(now, out);
        for (to, message) in std::mem::take(&mut self.to_say) {
            self.send(to, &message, out);
        }
        for (to, name, circuit, kind, count, bytes) in std::mem::take(&mut self.stepping) {
            self.send(to, &Message::Stepped { name, circuit, kind, count, bytes: &bytes }, out);
        }
        // A body that arrived may have been applied in place, and what
        // came of that may want more fetched: until nothing does.
        while !self.shared.threaded.load(Ordering::Relaxed) && self.shared.ready.load(Ordering::Relaxed) > 0 {
            wake = self.fetch(now, out);
        }
        self.serve_some(now, out).min(wake)
    }

    /// What became of blocks applied, and what the fetches under way
    /// want done: when a fetch next wants looking to.
    ///
    /// The list is taken only if there is something to say to it: work
    /// on the chain that is done, a fetch that has come whole or been
    /// given up. A fetch that only wants its next chunks asked for, or
    /// to wait, does not touch it.
    fn fetch(&mut self, now: Micros, out: Out<'_>) -> Micros {
        let list = Arc::clone(&self.list);
        let mut held: Option<RwLockWriteGuard<'_, List>> = None;
        if self.shared.ready.load(Ordering::Relaxed) > 0 {
            let l = &mut **held.get_or_insert_with(|| write(&list));
            self.applied(l, now, out);
        }
        let mut wake = Micros::MAX;
        let mut ranges = Ranges::new();
        let mut name = [0u8; MAX_NAME];
        // (How fast everything comes together, and the fastest of it:
        // many fetches at once over a slow way in are each slow, and
        // no peer's fault.)
        let rates = self.fetches.iter().map(|f| f.fetch.rate(now));
        let (together, fastest) = rates.fold((0u64, 0u64), |(sum, most), r| (sum.saturating_add(r), most.max(r)));
        let mut i = 0;
        while i < self.fetches.len() {
            let (object, from) = (self.fetches[i].object, self.fetches[i].from);
            // What is fetched for the chain, and comes too slowly, is
            // given up as if nothing had come: asked of another, and
            // this peer passed over. Too slowly for the way in: under
            // the least asked, and either another comes four times as
            // fast or all of them together come under that least.
            // A block whose fetch has brought nothing new for a while,
            // where another peer has the block and is free: the rest
            // of it is asked of that one. (What has come is kept. The
            // blocks after it wait for it, however fast they came; and
            // a peer may answer everything else and not this.)
            if let Object::Block(id) = object {
                let fetch = &self.fetches[i].fetch;
                let quiet = fetch.quiet(now);
                let long = self.cfg.sync.fetch_quiet.max(4 * fetch.path().retry());
                let height = (quiet >= long).then(|| self.chain.known(&id).ok().flatten()).flatten();
                let other = height.and_then(|known| {
                    let busy = |addr: &SocketAddrV4| {
                        let blocks = |f: &&Fetching| matches!(f.object, Object::Block(_)) && f.from == *addr;
                        self.fetches.iter().filter(blocks).count() >= self.cfg.sync.blocks_per_peer
                    };
                    let free = |p: &&super::peers::Peer| {
                        p.addr != from && !busy(&p.addr) && !self.lacking.contains(&(id, p.addr))
                    };
                    let other = self.peers.holders(known.header.height, now).find(free)?;
                    Some((known.header.height, other.addr, other.path))
                });
                if let Some((height, to, path)) = other {
                    let l = &mut **held.get_or_insert_with(|| write(&list));
                    fetched(&mut l.fetching, &object, &from);
                    l.fetching.push((object, to));
                    let (here, of) = self.fetches[i].fetch.here();
                    self.peers.set_path(&from, self.fetches[i].fetch.path());
                    let transfer = Self::number(&self.secret, &mut self.numbers);
                    self.fetches[i].fetch.resume(transfer, path, now);
                    self.fetches[i].from = to;
                    self.counts.fetches_moved += 1;
                    self.shared.refetched.fetch_add(1, Ordering::Relaxed);
                    self.shared.say(Event::FetchMoved { height, from, to, quiet, here, of });
                    // Once is anyone's line; a peer it happens to
                    // again is passed over, as one too slow is.
                    let recent = self.cfg.sync.pass_over;
                    self.quieted.retain(|q| now.saturating_sub(q.1) < recent);
                    match self.quieted.iter().any(|q| q.0 == from) {
                        true => self.peers.failed(&from, now),
                        false if self.quieted.len() < LACKING => self.quieted.push((from, now)),
                        false => {}
                    }
                    continue;
                }
            }
            let slow = {
                let (rate, grace) = (self.cfg.sync.fetch_rate, self.cfg.sync.fetch_grace);
                let fetch = &self.fetches[i].fetch;
                let of_chain = matches!(
                    object,
                    Object::Headers { .. }
                        | Object::Block(_)
                        | Object::Manifest(_)
                        | Object::Roots { .. }
                        | Object::Part { .. }
                        | Object::Names { .. }
                );
                of_chain && fetch.age(now) >= grace && too_slow(fetch.rate(now), fastest, together, rate)
            };
            if slow {
                let l = &mut **held.get_or_insert_with(|| write(&list));
                let failed = self.fetches.swap_remove(i);
                fetched(&mut l.fetching, &object, &from);
                self.peers.set_path(&from, failed.fetch.path());
                self.counts.fetches_slow += 1;
                // (Of a block or headers, passed over whether it said
                // it had them or not: it began to send them.)
                if matches!(object, Object::Headers { .. } | Object::Block(_)) {
                    self.peers.failed(&from, now);
                }
                self.fetch_failed(l, now, object, from, false);
                continue;
            }
            match self.fetches[i].fetch.poll(now, &mut ranges) {
                Poll::Ask(seq) => {
                    // Asked with the token the peer gave us: one that has
                    // given none, or is gone, is not asked.
                    let granted = || self.grants.iter().rev().find(|g| g.0 == from).map(|g| g.1);
                    let Some(token) = self.peers.get(&from).and_then(|p| p.token()).or_else(granted) else {
                        let l = &mut **held.get_or_insert_with(|| write(&list));
                        self.fetches.swap_remove(i);
                        fetched(&mut l.fetching, &object, &from);
                        self.fetch_failed(l, now, object, from, false);
                        continue;
                    };
                    let n = object.encode(&mut name);
                    let transfer = self.fetches[i].fetch.transfer();
                    let get = Get { token, transfer, seq, name: &name[..n], ranges };
                    self.send(from, &Message::Get(get), out);
                    // (Again at once: there may be more to ask.)
                    continue;
                }
                Poll::Wait(at) => wake = wake.min(at),
                Poll::Done => {
                    let l = &mut **held.get_or_insert_with(|| write(&list));
                    let done = self.fetches.swap_remove(i);
                    fetched(&mut l.fetching, &object, &from);
                    self.counts.fetched += 1;
                    self.peers.delivered(&from, done.fetch.path());
                    let bytes = done.fetch.finish().expect("it is done");
                    self.arrived(l, now, object, from, &bytes);
                    continue;
                }
                Poll::Failed(why) => {
                    let l = &mut **held.get_or_insert_with(|| write(&list));
                    let failed = self.fetches.swap_remove(i);
                    fetched(&mut l.fetching, &object, &from);
                    self.peers.set_path(&from, failed.fetch.path());
                    if why == Why::Bad {
                        self.strike(&from, now);
                    }
                    self.fetch_failed(l, now, object, from, why == Why::Gone);
                    continue;
                }
            }
            i += 1;
        }
        wake
    }

    /// Sends some of the chunks asked of us, and says when there are
    /// more to send.
    fn serve_some(&mut self, now: Micros, out: Out<'_>) -> Micros {
        for _ in 0..SERVE_BATCH {
            match self.serve.next(now) {
                Next::Send(x) => {
                    let SocketAddr::V4(to) = x.to else { continue };
                    let object = Object::decode(x.name()).ok();
                    // The state as of another block than the last asked
                    // for: so many a second, and what is over is not
                    // answered now.
                    if let Some(
                        Object::Manifest(block)
                        | Object::Roots { block, .. }
                        | Object::Part { block, .. }
                        | Object::Names { block, .. },
                    ) = object
                    {
                        let mut pasts = self.shared.pasts.lock().unwrap_or_else(|e| e.into_inner());
                        let Pasts { of, asked } = &mut *pasts;
                        match of.iter().position(|b| *b == block) {
                            Some(at) => of.swap(0, at),
                            None => {
                                asked.retain(|p| now.saturating_sub(p.1) < crate::transport::SECOND);
                                let own = asked.iter().filter(|p| p.0 == *to.ip()).count();
                                if !to.ip().is_loopback() && (own >= PASTS_EACH || asked.len() >= PASTS) {
                                    drop(pasts);
                                    self.serve.cancel(x.to, x.transfer);
                                    continue;
                                }
                                asked.push_back((*to.ip(), now));
                                of.push_front(block);
                                of.truncate(crate::store::state::PASTS_KEPT);
                            }
                        }
                    }
                    // (A name that is no object's was not looked for.)
                    self.unread.set(false);
                    let bytes = object.and_then(|o| self.object(&o));
                    if bytes.is_none() && self.unread.get() {
                        self.serve.cancel(x.to, x.transfer);
                        continue;
                    }
                    match bytes.as_deref().map(|b| chunk_of(b, x.index).map(|data| (b.len() as u32, data))) {
                        Some(Some((len, data))) => {
                            let chunk = Chunk { transfer: x.transfer, seq: x.seq, len, index: x.index, data };
                            self.send(to, &Message::Chunk(chunk), out);
                        }
                        // No such chunk: asked for before its length was
                        // known, past its end. The rest of what was
                        // asked is past it too.
                        Some(None) => self.serve.cancel(x.to, x.transfer),
                        // No such object.
                        None => {
                            self.serve.cancel(x.to, x.transfer);
                            self.send(to, &Message::Gone(Gone { transfer: x.transfer }), out);
                        }
                    }
                }
                Next::Wait(at) => return at,
                Next::Idle => return Micros::MAX,
            }
        }
        // More to send: at once.
        now
    }

    /// An object fetched whole from `from`.
    fn arrived(&mut self, l: &mut List, now: Micros, object: Object, from: SocketAddrV4, bytes: &[u8]) {
        self.shared.work(self.me);
        if self.of_join(l, &object) {
            return self.piece_arrived(l, now, object, from, bytes);
        }
        match object {
            Object::Headers { from: first, .. } => self.headers_arrived(l, now, from, first, bytes),
            Object::Block(id) => self.body_arrived(l, now, from, id, bytes),
            Object::Tx(id) => self.tx_arrived(now, from, id, bytes),
            Object::File(id) => self.file_arrived(now, from, id, bytes),
            // An announcement this node asked a wallet for, to hold a
            // session for it: taken if it is that wallet's, made for
            // this node, and come from where it says it is.
            Object::Announce { id, seq } if seq != 0 && self.cfg.relay => {
                let tokens = &self.tokens;
                let bound = |bind: u64| tokens.check(&SocketAddr::V4(from), bind);
                let mut sessions = self.shared.sessions.lock().unwrap_or_else(|e| e.into_inner());
                let taken = sessions.admit(bytes.to_vec(), from, bound, self.unix, now);
                drop(sessions);
                if taken.is_ok_and(|whose| whose != id) || taken == Err(super::sessions::Refused::Unsound) {
                    self.tell(now, from, Notice::Strike(from));
                }
            }
            // What a wallet announced, asked of a node it is reached
            // at: the messages waiting for it are sealed to it.
            Object::Announce { id, .. } => self.announce_arrived(now, from, id, bytes),
            Object::Sealed(id) => self.sealed_arrived(now, from, id, bytes),
            Object::Step(name) => self.step_arrived(now, from, name, bytes),
            // A certificate this node asked a wallet it holds for: the
            // wallet is reached by that full name too, if the
            // certificate is the name's, by the chain.
            Object::Alias(n) if self.cfg.relay => {
                let checked = crate::subnames::read(bytes, self.unix).filter(|c| c.point() == n);
                let sound = checked.as_ref().is_some_and(|c| self.name_value(&c.name) == Some(c.by));
                let mut sessions = self.shared.sessions.lock().unwrap_or_else(|e| e.into_inner());
                let taken = checked.filter(|_| sound).and_then(|c| sessions.alias(&c, bytes.to_vec(), from, now).ok());
                drop(sessions);
                self.to_say.push((from, Message::AliasState { n, seq: taken.map_or(0, |taken| taken.0) }));
                // (The wallet that was reached by the name until now
                // is told it no longer is.)
                match taken.and_then(|taken| taken.1) {
                    Some(super::sessions::Where::Addr(addr)) => {
                        self.to_say.push((addr, Message::AliasState { n, seq: 0 }));
                    }
                    Some(super::sessions::Where::Way(before, circuit)) => {
                        let mut said = vec![super::circuits::AS_HELD];
                        said.extend_from_slice(&crate::hash::digest_to_bytes(&n));
                        said.extend_from_slice(&[0; 8]);
                        let step = self.shared.relayed.lock().unwrap_or_else(|e| e.into_inner()).say(
                            (before, circuit),
                            &said,
                            now,
                        );
                        step.into_iter().for_each(|step| self.carry(now, step));
                    }
                    None => {}
                }
            }
            Object::Alias(_) => {}
            // Asked for by whoever drives this node.
            _ => self.inbox.push((object, from, Some(bytes.to_vec()))),
        }
    }

    /// A fetch from `from` was given up. Of headers or a body: the peer
    /// is passed over, and what was wanted is wanted again, of another.
    /// Of anything else: whoever asked for it is told, and decides.
    ///
    /// `gone`: the peer said it does not have it. Of headers or a body
    /// it never said it had (it was asked because its chain is as
    /// long), that is no failing of its own: it is on another branch,
    /// and is not asked for this again. Else one peer speaking of a
    /// chain nobody has would have a node pass over every honest peer
    /// it then asked.
    fn fetch_failed(&mut self, l: &mut List, now: Micros, object: Object, from: SocketAddrV4, gone: bool) {
        self.counts.fetches_failed += 1;
        self.shared.refetched.fetch_add(1, Ordering::Relaxed);
        self.shared.work(self.me);
        // Of the state being taken: asked of another, and this peer
        // not again while another can be.
        if self.of_join(l, &object) {
            if let Some(join) = l.join.as_mut() {
                join.unserved.push(from);
            }
            // (Asked again when time is next looked to, not at once: if
            // nobody has it, asking as fast as they can say so helps
            // nobody.)
            return;
        }
        // What a wallet announced, asked of a node it is reached at
        // that has nothing of it: the wallet is not there, by that
        // node's account. When each of its nodes has said so, what
        // waits for it is given up as for a wallet that is not there.
        if let Object::Announce { id, seq: 0 } = object {
            return self.absent(&id);
        }
        if let Object::Step(name) = object {
            self.carried.retain(|c| (c.0, c.1) != (name, from));
            return;
        }
        // (A message offered to be passed on that never came is kept
        // count of no longer.)
        if let Object::Sealed(id) = object {
            self.offered.retain(|o| !(o.0 == id && o.2 == from));
        }
        let claimed = match object {
            Object::Headers { .. } => l.aim.as_ref().is_none_or(|aim| aim.source == from),
            Object::Block(id) => self.announced.iter().any(|(told, addr, _)| *told == id && *addr == from),
            _ => false,
        };
        match object {
            Object::Headers { .. } | Object::Block(_) if claimed || !gone => self.peers.failed(&from, now),
            Object::Headers { .. } => {
                if let Some(aim) = l.aim.as_mut().filter(|aim| !aim.refused.contains(&from)) {
                    aim.refused.push(from);
                }
            }
            Object::Block(id) => {
                // (No more remembered than could be asked about.)
                if self.lacking.len() >= LACKING {
                    self.lacking.remove(0);
                }
                self.lacking.push((id, from));
            }
            _ => {}
        }
        match (object, l.aim.as_mut()) {
            (Object::Headers { from: first, .. }, Some(aim)) => {
                aim.todo.insert(first);
                self.fetch_headers(l, now);
            }
            (Object::Block(id), _) => {
                self.announced.retain(|(told, addr, _)| !(*told == id && *addr == from));
                self.sync_blocks(l, now);
            }
            (Object::Headers { .. }, None) => {}
            // (Whoever else has it will say so.)
            (Object::Tx(_), _) => self.fetch_txs(now),
            _ => self.inbox.push((object, from, None)),
        }
    }
}

/// A node: its workers, each with the hosts that are its own, and what
/// they share. Every datagram is given to the worker its sender's host
/// belongs to. (All on the caller's thread, one after another: a node
/// of one worker is as a node always was.)
pub struct Node<B: Backend + 'static, V> {
    workers: Vec<Worker<B, V>>,
    shared: Arc<Shared>,
    list: Arc<RwLock<List>>,
}

impl<B: Backend + 'static, V: ProofVerifier + Sync> Node<B, V> {
    /// A node of the network `network` keeping `chain`, with these
    /// settings. `secret` is from the operating system's random source:
    /// the tokens this node gives, the numbers of its pings and those
    /// of its fetches come of it, and nobody is to foretell any.
    pub fn new(cfg: Config, network: [u8; 4], chain: Arc<Chain<B, V>>, secret: [u8; 32], now: Micros) -> Node<B, V> {
        let n = cfg.workers.max(1);
        let shared = Arc::new(Shared {
            mail: (0..n).map(|_| Mutex::new(Vec::new())).collect(),
            pace: Arc::default(),
            sessions: Mutex::new(super::sessions::Sessions::new(cfg.sessions)),
            participant: Mutex::new(None),
            letters: Mutex::new(super::sessions::Mail::default()),
            seeds: Mutex::new(BTreeSet::new()),
            consensus: Mutex::new(None),
            answered: (0..n).map(|_| Mutex::new(Vec::new())).collect(),
            listed: (0..n).map(|_| Mutex::new(Vec::new())).collect(),
            relayed: Mutex::new(super::circuits::Relayed::new(cfg.circuits)),
            ways: Mutex::default(),
            relays: Mutex::default(),
            relays_before: Mutex::default(),
            suspect: Mutex::default(),
            delivering: Mutex::default(),
            givers: Mutex::default(),
            forced: AtomicBool::new(false),
            undecided: Mutex::default(),
            leaving: Mutex::default(),
            key: u64::from_le_bytes(derive(&secret, b'h', 0)[..8].try_into().unwrap()),
            token_secret: derive(&secret, b'T', 0),
            node: u64::from_le_bytes(derive(&secret, b'I', 0)[..8].try_into().expect("eight bytes")),
            nodes: Mutex::default(),
            totals: Arc::new(Totals::new()),
            live: (0..n).map(|_| AtomicUsize::new(0)).collect(),
            known: (0..n).map(|_| Mutex::new(Vec::new())).collect(),
            ready: AtomicUsize::new(0),
            threaded: AtomicBool::new(false),
            blocks: AtomicU64::new(0),
            refetched: AtomicU64::new(0),
            settled: AtomicU64::new(0),
            waker: RwLock::new(None),
            turn: AtomicUsize::new(0),
            moved: (Mutex::new(()), std::sync::Condvar::new()),
            pasts: Mutex::default(),
            pool: Mutex::new(Mempool::with_policy(cfg.pool, cfg.policy)),
            told: RwLock::new(None),
            #[cfg(test)]
            by_port: AtomicBool::new(false),
            #[cfg(test)]
            names: Mutex::default(),
        });
        let list = Arc::new(RwLock::new(List::new(n)));
        // What is of the whole node is divided among its workers: but
        // for the rate it serves at, which they keep together, so that
        // a worker with all the asking has all of it.
        let mut each = cfg;
        if n > 1 {
            each.serve.waiting = (each.serve.waiting / n).max(each.serve.waiting_each);
        }
        let workers = (0..n).map(|me| {
            // (One worker has the node's secret as it is.)
            let secret = if n == 1 { secret } else { derive(&secret, b'w', me as u64) };
            let (shared, list) = (Arc::clone(&shared), Arc::clone(&list));
            Worker::new(each.clone(), network, Arc::clone(&chain), secret, now, me, shared, list)
        });
        Node { workers: workers.collect(), shared, list }
    }

    /// Has blocks applied on a thread of their own from here on: for a
    /// node over a socket.
    pub fn threaded(self) -> Node<B, V>
    where
        Chain<B, V>: Send + Sync,
        V: 'static,
    {
        let (jobs, todo) = std::sync::mpsc::channel::<Job>();
        let (done, outcomes) = std::sync::mpsc::channel();
        let (chain, shared) = (Arc::clone(&self.workers[0].chain), Arc::clone(&self.shared));
        shared.threaded.store(true, Ordering::Relaxed);
        std::thread::Builder::new()
            .name("applier".into())
            .spawn(move || {
                // (A node whose blocks are no longer applied answers its
                // peers and its prompt and stands still for ever, saying
                // nothing: if this thread fails, the node ends, as it
                // does when a worker fails.)
                struct Ends;
                impl Drop for Ends {
                    fn drop(&mut self) {
                        if std::thread::panicking() {
                            eprintln!("Error: the thread that applies blocks failed: the node cannot go on");
                            std::process::abort();
                        }
                    }
                }
                let _ends = Ends;
                // Until the node is dropped, and its end of either with it.
                let mut next: Option<Job> = None;
                'jobs: while let Some(job) = next.take().or_else(|| todo.recv().ok()) {
                    // Parts of a state that have come in while the last
                    // was put are put together: many take little longer
                    // than one ([`Chain::put_parts`]).
                    let mut jobs = vec![job];
                    while jobs.len() < PARTS_AT_ONCE
                        && matches!(jobs[0], Job::Piece { object: Object::Part { .. }, .. })
                    {
                        match todo.try_recv() {
                            Ok(job @ Job::Piece { object: Object::Part { .. }, .. }) => jobs.push(job),
                            Ok(other) => {
                                next = Some(other);
                                break;
                            }
                            Err(_) => break,
                        }
                    }
                    let outcomes = match jobs.len() {
                        1 => vec![apply(&chain, jobs.pop().expect("one")).unwrap_or(Outcome::Nothing)],
                        _ => apply_parts(&chain, jobs),
                    };
                    for outcome in outcomes {
                        // (Something is always said of a job, so that
                        // the node knows it is done with. Said to be
                        // ready before it is, never after: so that it
                        // is not there and nobody looks.)
                        shared.ready.fetch_add(1, Ordering::Relaxed);
                        if done.send(outcome).is_err() {
                            break 'jobs;
                        }
                    }
                    // One worker hears of it, each in turn.
                    shared.wake(shared.turn.fetch_add(1, Ordering::Relaxed) % shared.mail.len());
                }
            })
            .expect("a thread");
        write(&self.list).applier = Applier::Thread(Mutex::new(jobs), Mutex::new(outcomes));
        self
    }

    /// Tests: what is set on the first worker to make a node misbehave
    /// holds for every worker.
    #[cfg(test)]
    fn hooks(&mut self) {
        let (first, rest) = self.workers.split_first_mut().expect("a worker");
        for w in rest {
            (w.boast, w.spoil, w.foist, w.tall) = (first.boast, first.spoil, first.foist.clone(), first.tall);
            w.withhold = first.withhold;
            if w.cfg != first.cfg {
                w.cfg = first.cfg.clone();
            }
        }
    }

    /// Tests on one machine: a peer is its worker's by its port too.
    #[cfg(test)]
    pub(crate) fn by_port(self) -> Self {
        self.shared.by_port.store(true, Ordering::Relaxed);
        self
    }

    /// Tests: tells every live peer of a block.
    #[cfg(test)]
    pub(crate) fn announce(
        &mut self,
        now: Micros,
        header: Header,
        len: u32,
        except: Option<SocketAddrV4>,
        out: Out<'_>,
    ) {
        self.workers.iter_mut().for_each(|w| w.announce(now, header, len, except, out));
    }

    /// Tests: the peers of the worker `addr` belongs to.
    #[cfg(test)]
    pub(crate) fn table(&self, addr: &SocketAddrV4) -> &Peers {
        &self.workers[self.shared.owner(addr)].peers
    }

    /// Tests: every worker's peers.
    #[cfg(test)]
    pub(crate) fn tables(&self) -> impl Iterator<Item = &Peers> {
        self.workers.iter().map(|w| &w.peers)
    }

    /// The workers, and what they share: for whoever runs each on a
    /// thread of its own.
    pub(crate) fn parts(&mut self) -> (&mut [Worker<B, V>], &Arc<Shared>) {
        (&mut self.workers, &self.shared)
    }

    /// Tests: the messages given to be sent that are not sent yet: whom
    /// each is for, its kind, and what it says.
    /// (Not yet used here: the console's tests, which are to come, do.)
    #[cfg(test)]
    #[allow(dead_code)]
    pub(crate) fn posts(&self) -> Vec<(Digest, u8, Vec<u8>)> {
        let letters = self.shared.letters.lock().unwrap_or_else(|e| e.into_inner());
        letters.posts.iter().map(|post| (post.to, post.kind, post.body.clone())).collect()
    }

    /// Tests: has the pool look to the chain's last block, as a worker
    /// does when the chain takes one, `taken` blocks having joined.
    /// (Not yet used here: the console's tests, which are to come, do.)
    #[cfg(test)]
    #[allow(dead_code)]
    pub(crate) fn pool_follows(&self, taken: u32) {
        if let Ok(tip) = self.workers[0].chain.tip() {
            self.workers[0].pool_follows(&tip, taken, false);
        }
    }

    /// How the node stands, to be asked while its workers run.
    pub fn hold(&self) -> Handle<B, V> {
        Handle {
            shared: Arc::clone(&self.shared),
            list: Arc::clone(&self.list),
            chain: Arc::clone(&self.workers[0].chain),
        }
    }

    /// Datagrams that may wait for one worker.
    pub fn request_queue(&self) -> usize {
        self.workers[0].cfg.request_queue
    }

    /// The worker `addr` belongs to.
    fn of(&mut self, addr: &SocketAddrV4) -> &mut Worker<B, V> {
        let owner = self.shared.owner(addr);
        &mut self.workers[owner]
    }

    /// A block made here: applied, and if it joins the chain, announced.
    pub fn mined(&mut self, block: Vec<u8>) {
        self.workers[0].mined(block);
    }

    /// The list, to look at.
    pub(crate) fn list(&self) -> RwLockReadGuard<'_, List> {
        self.list.read().unwrap_or_else(|e| e.into_inner())
    }

    /// Tests: does `f` with the list in hand, as a worker itself does
    /// what it does about what to fetch.
    #[cfg(test)]
    pub(crate) fn with_list<T>(&mut self, f: impl FnOnce(&mut Worker<B, V>, &mut List) -> T) -> T {
        let list = Arc::clone(&self.list);
        f(&mut self.workers[0], &mut write(&list))
    }

    /// Whether work given to be done on the chain is still to be heard
    /// of: whoever drives the node then looks to it again soon, without
    /// waiting for a datagram.
    pub fn busy(&self) -> bool {
        self.list().outstanding > 0
    }

    /// The peers of the node's first worker: all there are, of a node
    /// of one.
    pub fn peers(&self) -> &Peers {
        &self.workers[0].peers
    }

    /// How many peers the node has, and how many of them are live.
    pub fn peer_counts(&self, now: Micros) -> (usize, usize) {
        self.workers.iter().fold((0, 0), |(all, live), w| (all + w.peers.len(), live + w.peers.live(now).count()))
    }

    pub fn chain(&self) -> &Arc<Chain<B, V>> {
        &self.workers[0].chain
    }

    pub fn counts(&self) -> Counts {
        let mut all = Counts::default();
        self.workers.iter().for_each(|w| all.add(&w.counts));
        all
    }

    /// Objects being fetched now.
    pub fn fetching(&self) -> usize {
        self.workers.iter().map(|w| w.fetches.len()).sum()
    }

    /// Takes `addr` as an address to try: a seed, a peer given by hand
    /// (both kept whatever they do), or one saved from an earlier run.
    pub fn add_peer(&mut self, addr: SocketAddrV4, seed: bool, now: Micros) -> bool {
        self.of(&addr).peers.add(addr, seed, now).is_ok()
    }

    /// Takes `addr` as a seed: an address to try, and, while no
    /// consensus file names relays, a node wallets are reached at. All
    /// of a network are to have the same seeds: where a wallet is
    /// reached is found by everyone from them. (A peer given by hand is
    /// one node's own, and is nowhere wallets are looked for.)
    pub fn add_seed(&mut self, addr: SocketAddrV4, now: Micros) -> bool {
        self.shared.seeds.lock().unwrap_or_else(|e| e.into_inner()).insert(addr);
        self.add_peer(addr, true, now)
    }

    /// Looks to everything that is due at `now`, and says when to be
    /// called again at the latest: sooner if a datagram arrives.
    /// `unix` is the time by the calendar, in seconds.
    pub fn tick(&mut self, now: Micros, unix: u64, out: Out<'_>) -> Micros {
        #[cfg(test)]
        self.hooks();
        let mut wake = Micros::MAX;
        for worker in &mut self.workers {
            wake = wake.min(worker.tick(now, unix, out));
        }
        // What one worker left for another is seen to at once.
        if self.shared.waiting() { now } else { wake }
    }

    /// Takes a datagram that arrived from `from`, and says what it was
    /// and what was done about it. Call [`Node::tick`] after it.
    pub fn handle(&mut self, now: Micros, from: SocketAddr, bytes: &[u8], out: Out<'_>) -> Heard {
        let host = match from {
            SocketAddr::V4(a) => Some(a),
            SocketAddr::V6(a) => a.ip().to_ipv4_mapped().map(|ip| SocketAddrV4::new(ip, a.port())),
        };
        let owner = host.map_or(0, |a| self.shared.owner(&a));
        self.workers[owner].handle(now, from, bytes, out)
    }

    /// "I am going", to every live peer: when a node stops, so that
    /// they need not find it out by its silence.
    pub fn goodbye(&mut self, now: Micros, out: Out<'_>) {
        self.workers.iter_mut().for_each(|w| w.goodbye(now, out));
    }

    /// Fetches `object`, of `most` bytes at the most, from `from`: what
    /// comes of it is in [`Node::take_fetched`] when it has. False if
    /// `from` is no peer to ask.
    pub fn fetch_object(&mut self, now: Micros, object: Object, from: SocketAddrV4, most: u32) -> bool {
        self.of(&from).fetch_object(now, object, from, most)
    }

    /// The objects asked for with [`Node::fetch_object`] that have come
    /// whole, or been given up (no bytes), since this was last called.
    pub fn take_fetched(&mut self) -> Vec<(Object, SocketAddrV4, Option<Vec<u8>>)> {
        self.workers.iter_mut().flat_map(|w| w.take_fetched()).collect()
    }
}

/// Tests look into a node of one worker as into that worker.
#[cfg(test)]
impl<B: Backend + 'static, V> std::ops::Deref for Node<B, V> {
    type Target = Worker<B, V>;
    fn deref(&self) -> &Worker<B, V> {
        &self.workers[0]
    }
}

#[cfg(test)]
impl<B: Backend + 'static, V> std::ops::DerefMut for Node<B, V> {
    fn deref_mut(&mut self) -> &mut Worker<B, V> {
        &mut self.workers[0]
    }
}

/// A hold on a node while its workers run, for whoever watches it or
/// makes blocks for it: all by what the workers share, so that none of
/// them is held up.
pub struct Handle<B: Backend + 'static, V> {
    shared: Arc<Shared>,
    list: Arc<RwLock<List>>,
    chain: Arc<Chain<B, V>>,
}

impl<B: Backend + 'static, V> Clone for Handle<B, V> {
    fn clone(&self) -> Self {
        Handle { shared: Arc::clone(&self.shared), list: Arc::clone(&self.list), chain: Arc::clone(&self.chain) }
    }
}

/// How a node stands to the best chain it knows of, for whoever makes
/// blocks ([`Handle::behind`]).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Behind {
    /// Not behind, or by one block that is still to come.
    No,
    /// Headers that have been checked, their work in them, show a
    /// chain two blocks or more ahead of ours, whose blocks are still
    /// to come: its last header, and how high it is.
    Blocks { best: Digest, height: u32 },
    /// The state is being taken whole: there is no chain here to
    /// build on until it has been.
    State,
}

/// What a [`Handle`] reads.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Standing {
    /// Peers known, and those of them heard from lately (as each
    /// worker last counted).
    pub peers: usize,
    pub live: usize,
    /// The chain's height.
    pub height: u32,
    /// Blocks that have joined the chain here.
    pub blocks: u64,
    /// Objects the node is after that are being fetched.
    pub fetching: usize,
    /// Fetches that did not end with the peer they began with.
    pub refetched: u64,
}

impl<B: Backend + 'static, V: ProofVerifier + Sync> Handle<B, V> {
    /// A block made here: applied, and if it joins the chain, announced
    /// to every peer. `unix` is the time by the calendar, in seconds.
    pub fn mined(&self, block: Vec<u8>, unix: u64) {
        let Ok(header) = BlockRef::from_bytes(&block).map(|b| *b.header()) else {
            return;
        };
        {
            let l = &mut *write(&self.list);
            l.applying.push(header.hash());
            work(&self.chain, &self.shared, l, Job::Block { block, from: None, unix });
        }
        // (Where it was applied in place, someone is to hear of it.)
        self.shared.wake(0);
    }

    /// Whether the node is behind a chain it knows of, as far as that
    /// matters to whoever makes blocks ([`Behind`]).
    ///
    /// Only what has been checked counts. A peer that says its chain
    /// has more work has said so and no more: it is asked for its
    /// headers, and until headers with their work in them are here the
    /// node is behind nothing. Else whoever cared to say so could stop
    /// a node from making blocks.
    pub fn behind(&self) -> Behind {
        // (While a state is only being asked for the chain is still
        // whole, and blocks are made on it: a node that asks, and is
        // never served, is not to stand still for that.)
        if self.chain.receiving() {
            return Behind::State;
        }
        // One block known of and not yet here is no reason to stop: it
        // may take long to arrive, it may not be what its header says,
        // and a block of no more work than ours (another found at the
        // same height) replaces nothing.
        let mut next = [self.chain.params().genesis().header; 2];
        match (self.chain.missing_bodies(&mut next), self.chain.best_header()) {
            (Ok(n), Ok(best)) if n > 1 => Behind::Blocks { best: best.header.hash(), height: best.header.height },
            _ => Behind::No,
        }
    }

    /// The peers that have answered the node: those it knows to be
    /// where they say, as its workers last said. In the order of their
    /// addresses.
    pub fn answered(&self) -> Vec<SocketAddrV4> {
        let mut all: Vec<SocketAddrV4> = Vec::new();
        for worker in &self.shared.answered {
            all.extend(worker.lock().unwrap_or_else(|e| e.into_inner()).iter());
        }
        all.sort_unstable();
        all
    }

    /// Every peer the node knows, as its workers last saw them (within
    /// a tick): in the order of their addresses.
    pub fn peer_list(&self) -> Vec<PeerSeen> {
        let mut all: Vec<PeerSeen> = Vec::new();
        for worker in &self.shared.listed {
            all.extend(worker.lock().unwrap_or_else(|e| e.into_inner()).iter().cloned());
        }
        all.sort_unstable_by_key(|p| p.addr);
        all
    }

    /// Makes this node the node of a wallet on the message layer: the
    /// wallet is said to be there, to the nodes it is reached at, for
    /// as long as the node runs.
    pub fn participate(&self, wallet: super::sessions::Participant) {
        *self.shared.participant.lock().unwrap_or_else(|e| e.into_inner()) = Some(wallet);
    }

    /// Sends a message of `kind` saying `body` to the wallet of id
    /// `to`: sealed to what that wallet announces, which is asked for.
    /// The message says nothing of who sends it; its answer comes back
    /// the way it went. What becomes of it is said later
    /// ([`Handle::take_posted`]).
    pub fn post(&self, to: Digest, kind: u8, tag: [u8; 32], body: Vec<u8>) {
        self.shared.letters.lock().unwrap_or_else(|e| e.into_inner()).post(to, kind, tag, body);
        (0..self.shared.mail.len()).for_each(|w| self.shared.wake(w));
    }

    /// Answers `message`, which came for this node's wallet: `body`,
    /// of `kind`, under the wallet's signature, back by the node the
    /// message came by to whoever sent it. False of a message that
    /// cannot be answered.
    pub fn answer(&self, message: &crate::msg::Opened, kind: u8, tag: [u8; 32], body: Vec<u8>) -> bool {
        let posted = self.shared.letters.lock().unwrap_or_else(|e| e.into_inner()).answer(message, kind, tag, body);
        (0..self.shared.mail.len()).for_each(|w| self.shared.wake(w));
        posted
    }

    /// Opens a way through the relays of `path`, nearest first: each
    /// by its id and where it is. The number the way is known by here,
    /// to ask after it by ([`Handle::way`]).
    pub fn open_way(&self, path: Vec<(Digest, SocketAddrV4)>) -> Option<u64> {
        let mut number = [0u8; 8];
        crate::random::fill(&mut number).ok().filter(|_| !path.is_empty())?;
        let circuit = u64::from_le_bytes(number);
        self.shared.ways.lock().unwrap_or_else(|e| e.into_inner()).wanted.push((circuit, path));
        (0..self.shared.mail.len()).for_each(|w| self.shared.wake(w));
        Some(circuit)
    }

    /// Puts the consensus file `file` in force here whatever the chain
    /// has decided, and keeps it so: for trying what a file does
    /// without waiting for one to be voted for.
    pub fn force_consensus(&self, file: &crate::consensus::File) {
        self.shared.forced.store(true, Ordering::Relaxed);
        *self.shared.relays.lock().unwrap_or_else(|e| e.into_inner()) = Arc::new(relays_of(Some(file)));
    }

    /// Puts `file` in force here in the place of the one that is, as
    /// decided at the block of height `at`: as a node does when the
    /// chain's votes decide another, for the tests of the blocks in
    /// which one file gives way to the next.
    #[cfg(test)]
    pub(crate) fn change_consensus(&self, file: &crate::consensus::File, at: u32) {
        self.shared.forced.store(true, Ordering::Relaxed);
        let now = Arc::new(relays_of(Some(file)));
        let before = std::mem::replace(&mut *self.shared.relays.lock().unwrap(), now);
        *self.shared.relays_before.lock().unwrap() = Some((before, at));
    }

    /// The number this node is known by ([`Status::node`]).
    #[cfg(test)]
    pub(crate) fn node_number(&self) -> u64 {
        self.shared.node
    }

    /// What is still wanted before it is known which consensus file is
    /// in force, if it is not known: the files voted for and not held,
    /// how many blocks' votes are missing, and whether the node has
    /// something to go by meanwhile (what it knew before).
    pub fn consensus_lacking(&self) -> Option<(Vec<crate::consensus::Hash>, u32, bool)> {
        let lacking = self.shared.undecided.lock().unwrap_or_else(|e| e.into_inner()).clone();
        lacking.map(|(files, votes)| (files, votes, self.shared.knows_consensus()))
    }

    /// Says what a name says, in the chain's place.
    #[cfg(test)]
    pub(crate) fn name_says(&self, name: &[u8], value: Digest) {
        self.shared.names.lock().unwrap().insert(name.to_vec(), value);
    }

    /// The nodes this node's wallet is to be reached at now, and
    /// whether it is reached at each: the relays of the file in force
    /// that its address and the chain's height choose, by ways through
    /// the others (true); or, while no file names relays, the seeds
    /// (false). None of a node that is no wallet's.
    pub fn rendezvous(&self) -> Option<(bool, Vec<(SocketAddrV4, bool)>)> {
        let relays = Arc::clone(&self.shared.relays.lock().unwrap_or_else(|e| e.into_inner()));
        let seeds: Vec<SocketAddrV4> =
            self.shared.seeds.lock().unwrap_or_else(|e| e.into_inner()).iter().copied().collect();
        let height = self.chain.tip().map_or(0, |tip| tip.height);
        let wallet = self.shared.participant.lock().unwrap_or_else(|e| e.into_inner());
        let own = wallet.as_ref()?;
        let by_ways = !relays.is_empty();
        let of = if by_ways { relays.len() } else { seeds.len() };
        let mut nodes: Vec<SocketAddrV4> = Vec::new();
        for epoch in crate::msg::reached_epochs(height) {
            for i in crate::msg::points(&own.id(), epoch, of) {
                let node = if by_ways { relays[i].1 } else { Some(seeds[i]) };
                nodes.extend(node.filter(|node| !nodes.contains(node)));
            }
        }
        Some((by_ways, nodes.into_iter().map(|node| (node, own.is_held(&node))).collect()))
    }

    /// A node at which another node has announced this node's wallet
    /// since this one did, if one has since this was last asked: two
    /// copies of one wallet are running at once.
    pub fn take_twin(&self) -> Option<SocketAddrV4> {
        self.shared.participant.lock().unwrap_or_else(|e| e.into_inner()).as_mut().and_then(|own| own.take_twin())
    }

    /// How the way of this number stands: open to its end, or not yet;
    /// none if there is none, or it was given up.
    pub fn way(&self, circuit: u64) -> Option<bool> {
        let ways = self.shared.ways.lock().unwrap_or_else(|e| e.into_inner());
        let open = ways.open.iter().find(|w| w.circuit() == circuit).map(|w| w.ready());
        open.or_else(|| ways.wanted.iter().any(|w| w.0 == circuit).then_some(false))
    }

    /// Says `said` to the last relay of a way that is open.
    pub fn say_along(&self, circuit: u64, said: Vec<u8>) {
        self.shared.ways.lock().unwrap_or_else(|e| e.into_inner()).to_say.push((circuit, said));
        (0..self.shared.mail.len()).for_each(|w| self.shared.wake(w));
    }

    /// What the last relays of this node's ways have said since this
    /// was last asked: the way, and what.
    pub fn take_said(&self) -> Vec<(u64, Vec<u8>)> {
        std::mem::take(&mut self.shared.ways.lock().unwrap_or_else(|e| e.into_inner()).said)
    }

    /// Sends a message of `kind` saying `body` from this node's wallet
    /// to whichever wallet the full name of id `n` is
    /// ([`crate::subnames::point`]): the nodes that name is reached at
    /// are asked, and show whose it is. Whose, is said when it is
    /// known ([`Handle::take_resolved`]).
    pub fn post_to_name(&self, n: Digest, kind: u8, tag: [u8; 32], body: Vec<u8>) {
        self.shared.letters.lock().unwrap_or_else(|e| e.into_inner()).post_to_name(n, kind, tag, body);
        (0..self.shared.mail.len()).for_each(|w| self.shared.wake(w));
    }

    /// Whose the full names messages were sent to turned out to be,
    /// since this was last asked: what each message was posted with,
    /// and the wallet.
    pub fn take_resolved(&self) -> Vec<([u8; 32], Digest)> {
        std::mem::take(&mut self.shared.letters.lock().unwrap_or_else(|e| e.into_inner()).resolved)
    }

    /// The full names this node's wallet is reached by are these: the
    /// id each is reached at, its certificate's number, and the
    /// certificate with what goes with it.
    pub fn set_names(&self, all: Vec<(Digest, u64, Vec<u8>)>) {
        if let Some(own) = self.shared.participant.lock().unwrap_or_else(|e| e.into_inner()).as_mut() {
            own.set_aliases(all);
        }
    }

    /// At how many nodes this node's wallet is reached by the full
    /// name of id `n`.
    pub fn name_reached(&self, n: &Digest) -> usize {
        let wallet = self.shared.participant.lock().unwrap_or_else(|e| e.into_inner());
        wallet.as_ref().map_or(0, |own| own.alias_reached(n))
    }

    /// The messages that have come for this node's wallet since this
    /// was last asked.
    pub fn take_messages(&self) -> Vec<crate::msg::Opened> {
        std::mem::take(&mut self.shared.letters.lock().unwrap_or_else(|e| e.into_inner()).inbox)
    }

    /// What became of the messages sent, since this was last asked:
    /// whom each was for, its kind, and what became of it.
    pub fn take_posted(&self) -> Vec<(Digest, u8, [u8; 32], super::sessions::Posted)> {
        std::mem::take(&mut self.shared.letters.lock().unwrap_or_else(|e| e.into_inner()).posted)
    }

    /// Whether this node's wallet is reached anywhere.
    pub fn reached(&self) -> bool {
        self.sessions().1 > 0
    }

    /// How the node stands on the message layer: the sessions it holds
    /// for wallets; and, of its own wallet, the nodes it is reached at
    /// and those it has said it is there to.
    pub fn sessions(&self) -> (usize, usize, usize) {
        let held = self.shared.sessions.lock().unwrap_or_else(|e| e.into_inner()).len();
        let wallet = self.shared.participant.lock().unwrap_or_else(|e| e.into_inner());
        let (reached, said) = wallet.as_ref().map_or((0, 0), |w| (w.reached_at().count(), w.said_to()));
        (held, reached, said)
    }

    /// Whether a chain ahead of ours is being caught up with: from when
    /// its headers are first asked for until its last block is here.
    pub fn syncing(&self) -> bool {
        self.list.read().unwrap_or_else(|e| e.into_inner()).syncing
    }

    /// How many times the chain has had a new last block here.
    pub fn moves(&self) -> u64 {
        self.shared.blocks.load(Ordering::Relaxed)
    }

    /// Waits until the chain has moved more than `seen` times, or for
    /// `most`.
    pub fn wait_moved(&self, seen: u64, most: std::time::Duration) {
        let guard = self.shared.moved.0.lock().unwrap_or_else(|e| e.into_inner());
        let _ = self.shared.moved.1.wait_timeout_while(guard, most, |_| self.moves() == seen);
    }

    /// How many blocks made here have been heard of: joined the chain,
    /// kept on a side branch, or refused.
    pub fn settled(&self) -> u64 {
        self.shared.settled.load(Ordering::Relaxed)
    }

    /// Waits until more than `seen` blocks made here have been heard
    /// of, or for `most`.
    pub fn wait_settled(&self, seen: u64, most: std::time::Duration) {
        let guard = self.shared.moved.0.lock().unwrap_or_else(|e| e.into_inner());
        let _ = self.shared.moved.1.wait_timeout_while(guard, most, |_| self.settled() == seen);
    }

    pub fn chain(&self) -> &Arc<Chain<B, V>> {
        &self.chain
    }

    /// Pools a transaction of this node's own making (a wallet's), as
    /// of `unix`, and has every peer told of it. Its id; or why the
    /// pool does not take it.
    pub fn submit(&self, bytes: &[u8], unix: u64) -> Result<Digest, Reject> {
        let id = pool_tx(&self.chain, &self.shared, bytes, unix).unwrap_or(Err(Reject::Store(Error::Receiving)))?;
        self.shared.relay(id, bytes.len() as u32, None);
        Ok(id)
    }

    /// Gives the pool, held, to `f`: for whoever chooses a block's
    /// transactions. (Whoever takes the chain's state as well takes it
    /// first.)
    pub fn pool(&self, f: &mut dyn FnMut(&Mempool)) {
        f(&self.shared.pool())
    }

    /// Takes into the pool what a run before this one kept of its own
    /// ([`Mempool::saved`]): how many transactions were taken. They are
    /// not told of to anyone: whoever has not got them is told when
    /// they are next sent again, or has them of whoever sent them.
    pub fn load_pool(&self, saved: &[u8], unix: u64) -> usize {
        let Ok(state) = self.chain.whole() else { return 0 };
        let Ok(snapshot) = state.snapshot() else { return 0 };
        let height = snapshot.tip().0 + 1;
        self.shared.pool().load(saved, &snapshot, height, unix)
    }

    /// Whether the transaction `id` is in the pool.
    pub fn pooled(&self, id: &Digest) -> bool {
        self.shared.pool().contains(id)
    }

    /// The pool: how many transactions it holds, and their bytes.
    pub fn pool_size(&self) -> (usize, usize) {
        let pool = self.shared.pool();
        (pool.len(), pool.bytes())
    }

    /// Has `told` called with each thing that happens to the node that
    /// a log would say. (On the thread of the worker it happens to: it
    /// is to be quick.)
    pub fn on_event(&self, told: Told) {
        *self.shared.told.write().unwrap_or_else(|e| e.into_inner()) = Some(told);
    }
}

impl<B: Backend + 'static, V> Handle<B, V> {
    pub fn read(&self) -> Standing {
        Standing {
            peers: self.shared.totals.peers(),
            live: self.shared.live.iter().map(|n| n.load(Ordering::Relaxed)).sum(),
            height: self.chain.tip().map_or(0, |tip| tip.height),
            blocks: self.shared.blocks.load(Ordering::Relaxed),
            fetching: self.list.read().unwrap_or_else(|e| e.into_inner()).fetching.len(),
            refetched: self.shared.refetched.load(Ordering::Relaxed),
        }
    }
}

/// Gives work to be done on the chain: done where the list says, and
/// what comes of it heard by a worker.
fn work<B: Backend + 'static, V: ProofVerifier + Sync>(chain: &Chain<B, V>, shared: &Shared, l: &mut List, job: Job) {
    l.outstanding += 1;
    match &mut l.applier {
        Applier::Here(done) => match apply(chain, job) {
            Some(outcome) => {
                done.push_back(outcome);
                shared.ready.fetch_add(1, Ordering::Relaxed);
            }
            None => l.outstanding -= 1,
        },
        Applier::Thread(jobs, _) => {
            let _ = jobs.get_mut().unwrap_or_else(|e| e.into_inner()).send(job);
        }
    }
}

/// The list, to change: whoever held it and failed left it as it was.
/// Puts the transaction `bytes` are in the pool, against the chain's
/// state as it is, at `unix`: what the pool says of it. Nothing while
/// there is no state to hold it against.
fn pool_tx<B: Backend + 'static, V>(
    chain: &Chain<B, V>,
    shared: &Shared,
    bytes: &[u8],
    unix: u64,
) -> Option<Result<Digest, Reject>> {
    let state = chain.whole().ok()?;
    let snapshot = state.snapshot().ok()?;
    let height = snapshot.tip().0 + 1;
    Some(shared.pool().insert(bytes, &snapshot, height, unix))
}

fn write(list: &RwLock<List>) -> RwLockWriteGuard<'_, List> {
    list.write().unwrap_or_else(|e| e.into_inner())
}

/// Thirty-two bytes from the node's secret, for a purpose and a count:
/// what one such shows tells nothing of another.
fn derive(secret: &[u8; 32], purpose: u8, count: u64) -> [u8; 32] {
    let mut h = Sha256::new();
    h.update(secret);
    h.update(&[purpose]);
    h.update(&count.to_le_bytes());
    h.finish()
}

/// The address a datagram is sent to, as the socket wants it.
pub fn socket_addr(addr: SocketAddrV4) -> SocketAddr {
    SocketAddr::V4(addr)
}

#[cfg(test)]
#[path = "node_tests.rs"]
mod tests;
