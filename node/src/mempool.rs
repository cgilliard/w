//! The memory pool: valid, unconfirmed transactions waiting to be mined.
//!
//! A transaction enters the pool ([`Mempool::insert`]) only if it decodes,
//! spends at least one input, has a non-negative balance (its fee), carries a
//! valid signature on every input, spends outputs the state holds unspent at
//! the positions its inputs give, and conflicts with nothing already pooled.
//! The proof cannot tell a user transaction from a block reward, so the
//! non-negative fee is this policy rule, not consensus: a negative-balance
//! transaction would be paid out of the miner's reward.
//!
//! A transaction that spends an output a pooled one already spends
//! replaces it (and any other it conflicts with) if its fee is at least
//! theirs together plus [`REPLACEMENT_FEE_PER_UNIT`] a unit of its own
//! weight; that is how a wallet cancels a payment. The bump keeps a sender
//! from churning the network with free replacements.
//!
//! A fee is by a transaction's weight ([`Weights`]), in which an output
//! counts for more than an input: the set of outputs is what every node
//! keeps. When the pool is full, a new transaction with a higher fee for
//! its weight evicts the lowest, and the pool's admission minimum rises to the
//! evicted rate plus the increment, decaying back to the floor with a
//! half-life ([`Mempool::admission_fee`]). The oldest transactions, up to
//! [`Policy::protect_bytes`], are never evicted and are admitted whatever
//! that minimum: they are the aged reserve's candidates.
//! After every change of the chain's last block the pool is revalidated
//! ([`Mempool::revalidate`]): transactions whose inputs are now spent leave
//! the pool but are shelved for a while, and return if a reorganization
//! makes their inputs unspent again. Blocks carry no transactions, so this
//! shelf is the only way a reorganized-out transaction can come back.
//!
//! The miner takes transactions with [`Mempool::select`]: the aged
//! reserve's share of the block to the longest-waiting, the rest by fee
//! rate; it pays itself the subsidy plus their fees.
//!
//! # Name operations
//!
//! A transaction's name operations (see [`crate::name`]) are checked
//! against the registry as the chain would check them, less what only the
//! proof knows: a reveal's commit must be at the position it names, with
//! the hash the name, salt and owner give, and not past its window (one
//! not yet in it is pooled and mined once it is); the name must be free
//! for a reveal and registered for an update, whose signature the current
//! owner must have made. A name and a commit position are claimed by at
//! most one pooled transaction: a second claim is refused rather than
//! replacing the first, since no fee rule makes the two comparable.
//! Revalidation drops transactions whose claims the chain has settled
//! otherwise. The miner takes operations within the block's caps, skipping
//! what does not fit and reveals whose window has not opened.
//!
//! # What it holds, and what it reads
//!
//! A pooled transaction is kept as its encoding and read through a
//! [`TransactionRef`]: nothing of it is decoded to the heap. The pool's
//! bytes are bounded by its capacity, and the tables beside them by the
//! number of transactions that fit it.
//!
//! The pool does not know the store. What it asks of the chain's state it
//! asks through a [`Ledger`], which a snapshot of the state is; and the
//! time is given to it, so that nothing here reads a clock.

use std::collections::{BTreeMap, BTreeSet, HashMap, VecDeque};

use crate::error::Error;
use crate::fees::MAX_BLOCK_SIZE;
// What a transaction pays and what a node asks of one: with what the
// four programs share, a wallet going by them too. By the names they
// had here.
pub use crate::fees::{
    DUST, EXPIRY_SECS, HALF_LIFE_SECS, MAX_TX_SIZE, MIN_FEE_PER_UNIT, PROOF_BYTES, PROTECT_BYTES, Policy,
    REPLACEMENT_FEE_PER_UNIT, RESERVE_BYTES, RESERVE_PERCENT, TARGET_BLOCK, TARGET_DAY, TARGET_HOUR, WHOLE_OLDER,
    WHOLE_RECENT, Weights, reserve_bytes,
};
use crate::hash::Digest;
use crate::name::{Key, MAX_REVEAL, MAX_SWEEPS, NameOp, OpKind, Record, commit_hash, count_ops, in_window};
use crate::output::Commitment;
use crate::store::backend::Backend;
use crate::store::state::Snapshot;
use crate::transaction::TransactionRef;

/// What the pool asks of the chain's state.
pub trait Ledger {
    /// The output at `position`: its commitment, the height of the block
    /// that made it, and whether it is unspent.
    fn output(&self, position: u64) -> Result<Option<(Commitment, u32, bool)>, Error>;
    /// The commit of a name at `position`: its hash, and the height of the
    /// block that made it.
    fn commit(&self, position: u64) -> Result<Option<(Digest, u32)>, Error>;
    /// The record registered at `key`.
    fn name(&self, key: Key) -> Result<Option<Record>, Error>;
    /// The positions of the commits made at `height` or before, ascending.
    fn commits_up_to(&self, height: u32) -> Result<Vec<u64>, Error>;
}

impl<B: Backend + 'static> Ledger for Snapshot<'_, B> {
    fn output(&self, position: u64) -> Result<Option<(Commitment, u32, bool)>, Error> {
        Ok(Snapshot::output(self, position)?.map(|(r, live)| (r.commitment, r.height, live)))
    }

    fn commit(&self, position: u64) -> Result<Option<(Digest, u32)>, Error> {
        Ok(self.commits().at(self.pages(), position)?.map(|c| (c.hash, c.height)))
    }

    fn name(&self, key: Key) -> Result<Option<Record>, Error> {
        Ok(Snapshot::name(self, key)?)
    }

    fn commits_up_to(&self, height: u32) -> Result<Vec<u64>, Error> {
        Ok(self.commits().up_to(self.pages(), height)?.into_iter().map(|(p, _)| p).collect())
    }
}

/// Whether `ledger` holds, unspent at `position`, an output of `commitment`.
fn holds(ledger: &impl Ledger, position: u64, commitment: &Commitment) -> Result<bool, Error> {
    Ok(ledger.output(position)?.is_some_and(|(c, _, live)| live && c == *commitment))
}

/// The height the output at `position` was made at, for a policy input's
/// timelocks.
fn made_at(ledger: &impl Ledger, position: u64) -> Option<u32> {
    ledger.output(position).ok().flatten().map(|(_, height, _)| height)
}

/// Why the registry refuses a name operation (the storage errors apart).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum NameReject {
    /// No commit at the position, or not this reveal's.
    NoCommit,
    /// The commit (made at this height) is past its window.
    Expired(u32),
    Registered,
    NotRegistered,
    /// Not signed by the current owner, or keeping it.
    BadOwner,
}

impl core::fmt::Display for NameReject {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            NameReject::NoCommit => f.write_str("no such commit"),
            NameReject::Expired(h) => write!(f, "the commit at height {h} is past its window"),
            NameReject::Registered => f.write_str("the name is registered"),
            NameReject::NotRegistered => f.write_str("the name is not registered"),
            NameReject::BadOwner => f.write_str("not signed by the current owner, or the owner is unchanged"),
        }
    }
}

/// What a pooled name operation holds for itself: a name, or a commit's
/// position.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Claim {
    Name(Key),
    Commit(u64),
}

/// Default pool capacity in bytes.
pub const DEFAULT_CAPACITY: usize = 1 << 30;
/// The most transactions a pool knows of, by default, whatever their
/// bytes: what a node keeps of each is bounded by this and by nothing
/// else, a transaction held whole or not. Every node's the same, as
/// the capacity is, so that every node takes and lets go alike. A full
/// block is some 12,300 transactions of one input and two outputs:
/// this is sixteen blocks waiting.
pub const DEFAULT_COUNT: usize = 200_000;
/// Shelved transactions kept, at most.
const SHELF: usize = 1024;
/// And, by their size, no more than this part of the pool's capacity.
const SHELF_PART: usize = 4;
/// Transactions in a row that a block being chosen has no room for
/// before it is taken to be full ([`Mempool::select`]).
const MISFITS: usize = 32;

/// Rows of a proof a policy's input may take
/// ([`crate::segment::policy_rows`]): an input is within one run of a
/// block's transactions, whatever else of its transaction is, and the
/// smallest run a block is made of has room for this many.
pub const MAX_TX_ROWS: usize = (1 << 15) - 512;

/// Expired ids a pool remembers, at most: the oldest are forgotten first.
const MAX_EXPIRED: usize = 100_000;
/// Confirmations a pool remembers for its fee estimates.
const CONFIRMED_KEPT: usize = 5000;
/// How long a confirmation counts for estimates.
const CONFIRMED_FOR: u64 = 7 * 86400;
/// Transactions an estimate needs at or above its rate, else none.
const MIN_SAMPLES: usize = 20;
/// The share of those that must have confirmed in time.
const SUCCESS: f64 = 0.85;
/// The waits estimates are made for: about a block, an hour, a day.
/// What a saved pool begins with ([`Mempool::saved`]).
const SAVED_TAG: &[u8; 8] = b"tabpool1";

/// Why a transaction is not pooled.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Reject {
    /// Already in the pool.
    Known,
    /// Expired from this pool lately: refused for as long again.
    Expired,
    /// No inputs: only a block reward looks like that.
    NoInputs,
    TooLarge(usize),
    /// Outputs exceed inputs.
    NegativeFee,
    /// Not a transaction; or one with a zero-amount output, a duplicate
    /// input, or name operations past their caps.
    Malformed,
    /// Pays less than the minimum.
    FeeTooLow {
        min: u64,
    },
    /// An output below the pool's dust limit.
    Dust {
        min: u64,
    },
    BadSignature,
    /// A policy input's leaf is not satisfied.
    Policy(Error),
    /// The transaction takes more trace rows than one segment holds: a
    /// policy spend is proven whole, so its signatures are bounded.
    TooManyRows(usize),
    /// The output at this position is not unspent, or not the input's.
    UnknownInput(u64),
    /// Spends an output pooled transactions spend, without paying enough
    /// to replace them.
    ReplacementFee {
        min: u64,
    },
    /// The pool is full of better-paying transactions.
    Full,
    /// A name operation the registry refuses.
    Name(NameReject),
    /// A name or commit another pooled transaction already claims.
    NameConflict,
    /// The state could not be read.
    Store(Error),
}

impl core::fmt::Display for Reject {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Reject::Known => f.write_str("already in the pool"),
            Reject::Expired => f.write_str("expired from the pool lately"),
            Reject::NoInputs => f.write_str("no inputs"),
            Reject::TooLarge(n) => write!(f, "{n} bytes exceeds the transaction size limit"),
            Reject::NegativeFee => f.write_str("outputs exceed inputs"),
            Reject::FeeTooLow { min } => write!(f, "fee below the minimum of {min} base units"),
            Reject::Dust { min } => write!(f, "an output is below the dust limit of {min} base units"),
            Reject::Malformed => f.write_str("malformed transaction"),
            Reject::BadSignature => f.write_str("invalid signature"),
            Reject::Policy(e) => write!(f, "policy input: {e}"),
            Reject::TooManyRows(n) => write!(f, "a policy's input of {n} rows is more than a run of a proof holds"),
            Reject::UnknownInput(p) => write!(f, "spends an output that is not unspent (position {p})"),
            Reject::ReplacementFee { min } => {
                write!(f, "conflicts with a pooled transaction; a replacement must pay at least {min}")
            }
            Reject::Full => f.write_str("pool is full"),
            Reject::Name(e) => write!(f, "name operation: {e}"),
            Reject::NameConflict => f.write_str("a pooled transaction already claims the name or commit"),
            Reject::Store(e) => write!(f, "the state could not be read: {e}"),
        }
    }
}

/// The positions of the outputs a transaction spends: one, of most
/// transactions, which is kept in the record itself; or more.
#[derive(Clone, Debug)]
enum Spent {
    One(u64),
    Many(Box<[u64]>),
}

impl Spent {
    fn of(positions: Vec<u64>) -> Spent {
        match positions[..] {
            [one] => Spent::One(one),
            _ => Spent::Many(positions.into_boxed_slice()),
        }
    }

    fn all(&self) -> &[u64] {
        match self {
            Spent::One(position) => std::slice::from_ref(position),
            Spent::Many(positions) => positions,
        }
    }
}

/// A pooled transaction: held whole; or only known of, by what a node
/// that makes no blocks needs of it (its id, its size and what it
/// pays, when it came, what it spends and what names it claims).
///
/// Every transaction is whole when it comes, and is checked whole.
/// The most recent are held whole by every node, which is when they
/// are passed on; of the older ones each node holds its own share,
/// chosen by a hash under a secret of its own, so that any one of
/// them is to be had from some peers and no one can tell or arrange
/// which a node holds. What is only known of cannot be given to a
/// peer that asks, nor put in a block, nor looked at again after the
/// chain goes another way; it is there to refuse another that spends
/// the same, to say what a payment should pay, and to be let go when
/// a block spends what it spends.
#[derive(Clone, Debug)]
pub struct Entry {
    /// Its encoding: a transaction, checked when it was pooled. Empty,
    /// of one only known of.
    bytes: Box<[u8]>,
    /// Its size, in bytes, whole or not.
    size: u32,
    /// Whether it is among the most recent, which are all held whole.
    recent: bool,
    /// The positions of the outputs it spends.
    spent: Spent,
    pub txid: Digest,
    pub fee: u64,
    /// What it weighs, by the pool's policy ([`Weights`]).
    pub weight: u64,
    /// When it reached this node, in Unix seconds: its age, kept across
    /// restarts in the saved pool.
    pub arrived: u64,
    /// Its place in the order this pool took transactions: the last tie
    /// breaker, arrival times being whole seconds.
    pub order: u64,
    /// What its name operations claim.
    pub claims: Box<[Claim]>,
}

impl Entry {
    /// The transaction, if it is held whole.
    pub fn tx(&self) -> Option<TransactionRef<'_>> {
        match self.bytes.is_empty() {
            true => None,
            false => Some(TransactionRef::from_bytes(&self.bytes).expect("a pooled transaction decodes")),
        }
    }

    /// Its encoding, if it is held whole.
    pub fn bytes(&self) -> Option<&[u8]> {
        (!self.bytes.is_empty()).then_some(&self.bytes[..])
    }

    /// Whether it is held whole.
    pub fn whole(&self) -> bool {
        !self.bytes.is_empty()
    }

    /// Its size, in bytes, held whole or not.
    pub fn size(&self) -> usize {
        self.size as usize
    }

    /// The positions of the outputs it spends.
    pub fn spent(&self) -> &[u64] {
        self.spent.all()
    }

    /// Fee per unit of weight, scaled by 2^16 for integer comparison.
    fn rate(&self) -> u128 {
        rate(self.fee, self.weight)
    }

    fn age_key(&self) -> (u64, u64) {
        (self.arrived, self.order)
    }
}

/// Fee per unit of weight, scaled by 2^16.
fn rate(fee: u64, weight: u64) -> u128 {
    ((fee as u128) << 16) / weight.max(1) as u128
}

/// A scaled rate per unit of weight, rounded up to base units.
fn per_unit(rate: u128) -> u64 {
    rate.div_ceil(1 << 16).min(u64::MAX as u128) as u64
}

pub struct Mempool {
    txs: HashMap<Digest, Entry>,
    /// Spent position to the pooled transaction spending it: the chain
    /// spends by position, and two unspent outputs may share a commitment.
    spends: HashMap<u64, Digest>,
    /// Name or commit to the pooled transaction claiming it.
    claims: HashMap<Claim, Digest>,
    bytes: usize,
    capacity: usize,
    /// The most transactions known of ([`DEFAULT_COUNT`]).
    most: usize,
    /// Transactions dropped for spent inputs, oldest first, in case a
    /// reorganization brings their inputs back.
    shelf: Vec<Entry>,
    policy: Policy,
    /// Ids expired here, and until when they are refused: so one a peer
    /// still holds does not come back with a fresh age.
    expired: HashMap<Digest, u64>,
    /// The next entry's [`Entry::order`].
    next_order: u64,
    /// Pooled transactions oldest first, by [`Entry::age_key`].
    by_age: BTreeMap<(u64, u64), Digest>,
    /// The rolling admission minimum (a scaled rate) when last settled,
    /// and when, in Unix seconds.
    rolling: u128,
    rolling_at: u64,
    /// Transactions seen confirmed: their rate (base units a byte), how
    /// long they waited here, and when, oldest first.
    confirmed: VecDeque<(u64, u64, u64)>,
    /// Transactions that came back from the shelf and have not been
    /// told of since ([`Mempool::take_returned`]).
    returned: Vec<Digest>,
    /// The bytes of the transactions held whole; of those, the bytes
    /// of the most recent, and of the older ones.
    held: usize,
    recent_bytes: usize,
    older_bytes: usize,
    /// The most recent, in the order they came: each held whole until
    /// newer ones have pushed it out. (An id that is here and no
    /// longer among them is passed over.)
    recent: VecDeque<Digest>,
    /// The older ones held whole, each by its draw
    /// ([`Mempool::draw`]): the highest is the first let go. (Empty,
    /// of a pool that holds everything.)
    older: BTreeSet<(u64, Digest)>,
    /// What says which of the older ones this node holds whole: a
    /// secret of its own, taken when the pool is made.
    secret: [u8; 32],
}

/// The cheap checks of a transaction on its own: all but its signatures,
/// which [`Mempool::insert`] checks last, the pool and the state.
fn check_static(tx: &TransactionRef<'_>, policy: &Policy) -> Result<(u64, u64), Reject> {
    let n = tx.counts();
    if n.inputs == 0 && n.policy_inputs == 0 {
        return Err(Reject::NoInputs);
    }
    if n.policy_inputs > 1 {
        return Err(Reject::Malformed);
    }
    if n.policy_inputs > 0 {
        // (Said the one way there is, before anything is made of it.)
        if !tx.policy_inputs().all(|input| input.canonical()) {
            return Err(Reject::Malformed);
        }
        let rule = tx.to_transaction().rule(|_| ([0; 20], 0));
        let rows = rule.policy.iter().map(crate::segment::policy_rows).max().unwrap_or(0);
        if rows > MAX_TX_ROWS {
            return Err(Reject::TooManyRows(rows));
        }
    }
    let size = tx.size();
    if size > policy.max_tx_size {
        return Err(Reject::TooLarge(size));
    }
    if tx.outputs().iter().any(|o| o.amount == 0) {
        return Err(Reject::Malformed);
    }
    // Name operations: within the caps. (Well formed by their decoding.)
    if count_ops(tx.ops().map(|op| op.kind())).is_err() {
        return Err(Reject::Malformed);
    }
    if tx.outputs().iter().any(|o| o.amount < policy.dust) {
        return Err(Reject::Dust { min: policy.dust });
    }
    let mut spent: Vec<u64> = tx.spent_positions().collect();
    spent.sort_unstable();
    if spent.windows(2).any(|w| w[0] == w[1]) {
        return Err(Reject::Malformed);
    }
    let fee = tx.balance();
    if fee < 0 {
        return Err(Reject::NegativeFee);
    }
    let fee = fee.min(u64::MAX as i128) as u64;
    let weight = policy.weights.weigh(tx);
    let min = policy.min_fee_for(weight);
    if fee < min {
        return Err(Reject::FeeTooLow { min });
    }
    Ok((fee, weight))
}

/// The name operations of `tx` against the registry, for a block at
/// `height` or later: returns what they claim, distinct within the
/// transaction.
fn check_ops(tx: &TransactionRef<'_>, ledger: &impl Ledger, height: u32) -> Result<Vec<Claim>, Reject> {
    let mut claims = Vec::with_capacity(2 * tx.counts().ops);
    for op in tx.ops() {
        match &op {
            NameOp::Commit { .. } => {}
            NameOp::Reveal { record, salt, commit } => {
                let nh = record.name.hash();
                match ledger.commit(*commit).map_err(Reject::Store)? {
                    Some((hash, made)) if hash == commit_hash(&nh, salt, &record.owner) => {
                        if made.saturating_add(MAX_REVEAL) < height {
                            return Err(Reject::Name(NameReject::Expired(made)));
                        }
                    }
                    _ => return Err(Reject::Name(NameReject::NoCommit)),
                }
                let key = record.key();
                if ledger.name(key).map_err(Reject::Store)?.is_some() {
                    return Err(Reject::Name(NameReject::Registered));
                }
                claims.push(Claim::Name(key));
                claims.push(Claim::Commit(*commit));
            }
            NameOp::Update { record, .. } => {
                let key = record.key();
                let current =
                    ledger.name(key).map_err(Reject::Store)?.ok_or(Reject::Name(NameReject::NotRegistered))?;
                if !op.verify_owner(&current.owner) {
                    return Err(Reject::Name(NameReject::BadOwner));
                }
                claims.push(Claim::Name(key));
            }
        }
    }
    let mut sorted = claims.clone();
    sorted.sort_unstable();
    if sorted.windows(2).any(|w| w[0] == w[1]) {
        return Err(Reject::Malformed);
    }
    Ok(claims)
}

/// Whether every reveal of `tx` is in its window at `height`.
fn reveals_open(tx: &TransactionRef<'_>, ledger: &impl Ledger, height: u32, min_reveal: u32) -> bool {
    tx.ops().all(|op| match op {
        NameOp::Reveal { commit, .. } => {
            matches!(ledger.commit(commit), Ok(Some((_, made))) if in_window(height, made, min_reveal))
        }
        _ => true,
    })
}

impl Mempool {
    /// A pool of `capacity` bytes with the mainnet policy.
    pub fn new(capacity: usize) -> Mempool {
        Self::with_policy(capacity, Policy::MAINNET)
    }

    pub fn with_policy(capacity: usize, policy: Policy) -> Mempool {
        let _in = crate::heap::enter(crate::heap::Part::Pool);
        Mempool {
            txs: HashMap::new(),
            spends: HashMap::new(),
            claims: HashMap::new(),
            bytes: 0,
            capacity,
            most: DEFAULT_COUNT,
            shelf: Vec::new(),
            policy,
            expired: HashMap::new(),
            next_order: 0,
            by_age: BTreeMap::new(),
            rolling: 0,
            rolling_at: 0,
            confirmed: VecDeque::new(),
            returned: Vec::new(),
            held: 0,
            recent_bytes: 0,
            older_bytes: 0,
            recent: VecDeque::new(),
            older: BTreeSet::new(),
            // (Chance, where there is any to be had; and without it a
            // share all the same, which is what matters.)
            secret: {
                let mut secret = [0x5a; 32];
                let _ = crate::random::fill(&mut secret);
                secret
            },
        }
    }

    /// The same pool, knowing of `count` transactions at the most.
    pub fn knowing(mut self, count: usize) -> Mempool {
        self.most = count;
        self
    }

    /// The most transactions the pool knows of.
    pub fn most(&self) -> usize {
        self.most
    }

    /// The bytes of the transactions held whole.
    pub fn held(&self) -> usize {
        self.held
    }

    /// How many transactions are held whole.
    pub fn whole(&self) -> usize {
        self.txs.values().filter(|e| e.whole()).count()
    }

    /// A transaction's draw: a hash of its id under the node's own
    /// secret. Of the older ones a node holds whole those of the
    /// lowest draws that fit, so what it holds is a share of them at
    /// random, however many there are: the same each time it is asked,
    /// with nothing to keep; each node's its own; and nobody else can
    /// tell or arrange which a node holds.
    fn draw(&self, txid: &Digest) -> u64 {
        let mut both = [0u8; 64];
        both[..32].copy_from_slice(&self.secret);
        both[32..].copy_from_slice(&crate::hash::digest_to_bytes(txid));
        let hash = crate::sha256::sha256(&both);
        u64::from_le_bytes(hash[..8].try_into().expect("eight bytes"))
    }

    /// Makes room among the older ones held whole for one of `size`
    /// whose place among them is `place` (its draw, and its id): by
    /// letting go those after it, the last first, if that is room
    /// enough. Those are only known of from here on. Says whether
    /// there is room: where there is not, nothing is let go.
    fn older_room(&mut self, place: (u64, Digest), size: usize) -> bool {
        let mut room = self.policy.whole_older.saturating_sub(self.older_bytes);
        let mut out = Vec::new();
        for other in self.older.iter().rev() {
            if room >= size || *other < place {
                break;
            }
            room += self.txs[&other.1].size();
            out.push(*other);
        }
        if room < size {
            return false;
        }
        for other in out {
            self.older.remove(&other);
            let e = self.txs.get_mut(&other.1).expect("what is held is known of");
            e.bytes = Box::default();
            self.held -= e.size();
            self.older_bytes -= e.size();
        }
        true
    }

    /// Lets the oldest of the most recent go from among them while
    /// they are more than is held whole of those: each is held whole
    /// still, if its draw is among the lowest of the older ones that
    /// fit their room; or is only known of from here on.
    fn age(&mut self) {
        while self.recent_bytes > self.policy.whole_recent {
            let Some(id) = self.recent.pop_front() else { break };
            let Some(e) = self.txs.get_mut(&id).filter(|e| e.recent) else { continue };
            e.recent = false;
            let size = e.size();
            self.recent_bytes -= size;
            // (A pool that holds everything keeps no draws.)
            if self.policy.holds_all() {
                self.older_bytes += size;
                continue;
            }
            let place = (self.draw(&id), id);
            if self.older_room(place, size) {
                self.older.insert(place);
                self.older_bytes += size;
            } else {
                self.held -= size;
                self.txs.get_mut(&id).expect("looked up above").bytes = Box::default();
            }
        }
    }

    pub fn policy(&self) -> &Policy {
        &self.policy
    }

    /// The rolling minimum's scaled rate at `now`, at least the floor:
    /// what it was raised to, decayed by half each half-life (a half or a
    /// quarter of it while the pool is under half or a quarter full, as
    /// Bitcoin's), and back at the floor once within half the increment.
    fn rolling_rate(&self, now: u64) -> u128 {
        let floor = (self.policy.min_fee_per_unit as u128) << 16;
        if self.rolling <= floor {
            return floor;
        }
        let mut half_life = self.policy.half_life_secs as f64;
        // (How full, by its bytes or by how many it knows of.)
        let under = |part: usize| self.bytes < self.capacity / part && self.txs.len().saturating_mul(part) < self.most;
        if under(4) {
            half_life /= 4.0;
        } else if under(2) {
            half_life /= 2.0;
        }
        let elapsed = now.saturating_sub(self.rolling_at) as f64;
        let excess =
            if half_life > 0.0 { (self.rolling - floor) as f64 * 0.5f64.powf(elapsed / half_life) } else { 0.0 };
        if excess < ((self.policy.replacement_per_unit as u128) << 15) as f64 {
            return floor;
        }
        floor + excess as u128
    }

    /// Settles the rolling minimum's decay to `now`, so the pool's fill
    /// from here on sets its pace.
    fn settle(&mut self, now: u64) {
        self.rolling = self.rolling_rate(now);
        self.rolling_at = now;
    }

    /// The pool's admission minimum at `now`, base units a byte: the floor,
    /// or above it while the rolling minimum is up after evictions. Peers
    /// are told it, so they do not send what it would refuse; the aged
    /// reserve's candidates are admitted whatever it is.
    pub fn admission_fee(&self, now: u64) -> u64 {
        per_unit(self.rolling_rate(now))
    }

    /// The bytes kept from eviction: [`Policy::protect_bytes`], at most
    /// half the pool. (And no more transactions than half of those it
    /// knows of at the most: [`Mempool::protected_until`].)
    fn protect_budget(&self) -> usize {
        self.policy.protect_bytes.min(self.capacity / 2)
    }

    /// The age key of the youngest protected transaction: the oldest are
    /// protected while their bytes together fit the budget.
    fn protected_until(&self) -> Option<(u64, u64)> {
        let budget = self.protect_budget();
        let mut used = 0;
        let mut last = None;
        for (key, id) in self.by_age.iter().take(self.most / 2) {
            used += self.txs[id].size();
            if used > budget {
                break;
            }
            last = Some(*key);
        }
        last
    }

    /// Whether a transaction of `size` with age key `key` would be among
    /// the protected: what is older and it fit the budget.
    fn would_protect(&self, key: (u64, u64), size: usize) -> bool {
        let budget = self.protect_budget();
        let mut used = size;
        for (before, id) in self.by_age.range(..key).map(|(_, id)| id).enumerate() {
            used += self.txs[id].size();
            if used > budget || before + 1 >= self.most / 2 {
                return false;
            }
        }
        used <= budget && self.most >= 2
    }

    /// Whether a pooled transaction is kept from eviction: one of the aged
    /// reserve's candidates, relayed whatever a peer's admission minimum.
    pub fn is_protected(&self, txid: &Digest) -> bool {
        match (self.txs.get(txid), self.protected_until()) {
            (Some(e), Some(until)) => e.age_key() <= until,
            _ => false,
        }
    }

    /// A pooled transaction's entry.
    pub fn entry(&self, txid: &Digest) -> Option<&Entry> {
        self.txs.get(txid)
    }

    /// The lowest rate, base units a byte, at which this pool has seen
    /// transactions confirm within `target` seconds: of those it saw at
    /// or above that rate, confirmed lately or still waiting past the
    /// target, [`SUCCESS`] of them in time. `None` until it has seen
    /// enough (a new node).
    pub fn estimate(&self, target: u64, now: u64) -> Option<u64> {
        let mut samples: Vec<(u64, bool)> = self
            .confirmed
            .iter()
            .filter(|(_, _, at)| now.saturating_sub(*at) < CONFIRMED_FOR)
            .map(|(rate, waited, _)| (*rate, *waited <= target))
            .collect();
        samples.extend(
            self.txs.values().filter(|e| now.saturating_sub(e.arrived) > target).map(|e| (per_unit(e.rate()), false)),
        );
        samples.sort_unstable_by_key(|b| std::cmp::Reverse(b.0));
        let (mut total, mut ok, mut best) = (0usize, 0usize, None);
        for (i, (rate, in_time)) in samples.iter().enumerate() {
            total += 1;
            ok += usize::from(*in_time);
            // Only once every sample at this rate is counted.
            if samples.get(i + 1).is_some_and(|next| next.0 == *rate) || total < MIN_SAMPLES {
                continue;
            }
            if (ok as f64) < SUCCESS * total as f64 {
                break;
            }
            best = Some(*rate);
        }
        best
    }

    /// The rate, base units a unit of weight, to suggest for a transaction
    /// of `size` bytes to confirm within `target` seconds: the admission minimum while the
    /// pool would fit one block with it (nothing ahead to wait for), else
    /// the estimate, the admission minimum until there is one.
    pub fn suggest(&self, target: u64, size: usize, now: u64) -> u64 {
        let admission = self.admission_fee(now);
        let space = MAX_BLOCK_SIZE - PROOF_BYTES;
        if self.bytes + size <= space {
            return admission;
        }
        self.estimate(target, now).map_or(admission, |r| r.max(admission))
    }

    /// Blocks a transaction of `size` arriving now waits at most for the
    /// aged reserve, if miners keep what this node does: everything
    /// pooled is older and ahead of it. Nothing, if there is no
    /// reserve: then nothing but its fee brings it into a block.
    pub fn reserve_wait(&self, size: usize) -> Option<u64> {
        let reserve = reserve_bytes(MAX_BLOCK_SIZE, self.policy.reserve_percent);
        (reserve > 0).then(|| (self.bytes + size).div_ceil(reserve) as u64)
    }

    /// The confirmations the estimates use, oldest first: rate (base
    /// units a byte), wait and when, as the saved pool keeps them.
    pub fn confirmed(&self) -> impl Iterator<Item = &(u64, u64, u64)> {
        self.confirmed.iter()
    }

    /// A confirmation seen before a restart, or just now.
    pub fn remember_confirmed(&mut self, rate: u64, waited: u64, at: u64) {
        let _in = crate::heap::enter(crate::heap::Part::Pool);
        self.confirmed.push_back((rate, waited, at));
        if self.confirmed.len() > CONFIRMED_KEPT {
            self.confirmed.pop_front();
        }
    }

    /// Drops the transactions that have waited [`Policy::expiry_secs`] by
    /// `now`, remembering their ids for as long again, and forgets the ids
    /// whose time is up; returns those dropped.
    pub fn expire(&mut self, now: u64) -> Vec<Digest> {
        let _in = crate::heap::enter(crate::heap::Part::Pool);
        self.settle(now);
        let limit = self.policy.expiry_secs;
        let old: Vec<Digest> =
            self.txs.values().filter(|e| now.saturating_sub(e.arrived) >= limit).map(|e| e.txid).collect();
        for id in &old {
            self.remove(id);
            self.expired.insert(*id, now.saturating_add(limit));
        }
        self.expired.retain(|_, until| *until > now);
        if self.expired.len() > MAX_EXPIRED {
            let mut by_time: Vec<(u64, Digest)> = self.expired.iter().map(|(id, u)| (*u, *id)).collect();
            by_time.sort_unstable_by_key(|(u, _)| *u);
            for (_, id) in &by_time[..self.expired.len() - MAX_EXPIRED] {
                self.expired.remove(id);
            }
        }
        old
    }

    /// The ids expired here and until when they are refused, as the saved
    /// pool keeps them.
    pub fn expired(&self) -> impl Iterator<Item = (&Digest, &u64)> {
        self.expired.iter()
    }

    /// An id expired before a restart, refused until `until`.
    pub fn remember_expired(&mut self, id: Digest, until: u64) {
        let _in = crate::heap::enter(crate::heap::Part::Pool);
        if self.expired.len() < MAX_EXPIRED {
            self.expired.insert(id, until);
        }
    }

    pub fn len(&self) -> usize {
        self.txs.len()
    }

    pub fn is_empty(&self) -> bool {
        self.txs.is_empty()
    }

    pub fn bytes(&self) -> usize {
        self.bytes
    }

    pub fn contains(&self, txid: &Digest) -> bool {
        self.txs.contains_key(txid)
    }

    pub fn get(&self, txid: &Digest) -> Option<TransactionRef<'_>> {
        self.txs.get(txid).and_then(Entry::tx)
    }

    pub fn entries(&self) -> impl Iterator<Item = &Entry> {
        self.txs.values()
    }

    /// The pool as it is kept from one run of a node to the next: its
    /// transactions, each with when it arrived; the ids of those that
    /// waited too long, with until when each is remembered; and the
    /// confirmations the fee estimates go by.
    pub fn saved(&self) -> Vec<u8> {
        let mut out = SAVED_TAG.to_vec();
        // (Those held whole: what is only known of is known again
        // when it is told of again, or is in a block.)
        // (In the order they were taken: so they are taken again.)
        let mut entries: Vec<(&Entry, &[u8])> = self.entries().filter_map(|e| Some((e, e.bytes()?))).collect();
        entries.sort_by_key(|(e, _)| (e.arrived, e.order));
        out.extend_from_slice(&(entries.len() as u32).to_le_bytes());
        for (e, bytes) in entries {
            out.extend_from_slice(&e.arrived.to_le_bytes());
            out.extend_from_slice(&(bytes.len() as u32).to_le_bytes());
            out.extend_from_slice(bytes);
        }
        let expired: Vec<_> = self.expired().collect();
        out.extend_from_slice(&(expired.len() as u32).to_le_bytes());
        for (id, until) in expired {
            out.extend_from_slice(&crate::hash::digest_to_bytes(id));
            out.extend_from_slice(&until.to_le_bytes());
        }
        out.extend_from_slice(&(self.confirmed.len() as u32).to_le_bytes());
        for (rate, waited, at) in &self.confirmed {
            for v in [rate, waited, at] {
                out.extend_from_slice(&v.to_le_bytes());
            }
        }
        out
    }

    /// Takes what [`Mempool::saved`] kept: each transaction checked
    /// again, as any is, against the chain as it now is, and keeping
    /// its age. Returns how many were taken. What is of another form,
    /// or cut short, is passed over from there on.
    pub fn load(&mut self, saved: &[u8], ledger: &impl Ledger, height: u32, now: u64) -> usize {
        let _in = crate::heap::enter(crate::heap::Part::Pool);
        let Some(rest) = saved.strip_prefix(SAVED_TAG) else { return 0 };
        let mut r = crate::codec::Reader(rest);
        let mut taken = 0;
        for _ in 0..r.u32().unwrap_or(0) {
            let (Some(arrived), Some(len)) = (r.u64(), r.u32()) else { return taken };
            let Some(tx) = r.take(len as usize) else { return taken };
            taken += self.insert_at(tx, ledger, height, arrived, now).is_ok() as usize;
        }
        for _ in 0..r.u32().unwrap_or(0) {
            let (Some(id), Some(until)) = (r.take(32), r.u64()) else { return taken };
            let Some(id) = crate::hash::digest_from_bytes(id) else { return taken };
            self.remember_expired(id, until);
        }
        for _ in 0..r.u32().unwrap_or(0) {
            let (Some(rate), Some(waited), Some(at)) = (r.u64(), r.u64(), r.u64()) else { return taken };
            self.remember_confirmed(rate, waited, at);
        }
        taken
    }

    /// Validates and adds the transaction `bytes` are, arrived at `now`
    /// (Unix seconds), for a block at `height` or later; returns its id.
    pub fn insert(&mut self, bytes: &[u8], ledger: &impl Ledger, height: u32, now: u64) -> Result<Digest, Reject> {
        self.insert_at(bytes, ledger, height, now, now)
    }

    /// [`Mempool::insert`], for a transaction that arrived at `arrived`:
    /// one loaded from the saved pool keeps its age.
    pub fn insert_at(
        &mut self,
        bytes: &[u8],
        ledger: &impl Ledger,
        height: u32,
        arrived: u64,
        now: u64,
    ) -> Result<Digest, Reject> {
        let _in = crate::heap::enter(crate::heap::Part::Pool);
        // (Before it is read at all: what is too large is not read.)
        // (Nor what is larger than a record says the size of.)
        if bytes.len() > self.policy.max_tx_size || u32::try_from(bytes.len()).is_err() {
            return Err(Reject::TooLarge(bytes.len()));
        }
        let tx = TransactionRef::from_bytes(bytes).map_err(|_| Reject::Malformed)?;
        let txid = tx.txid();
        if self.txs.contains_key(&txid) {
            return Err(Reject::Known);
        }
        if self.expired.get(&txid).is_some_and(|until| *until > now) {
            return Err(Reject::Expired);
        }
        let (fee, weight) = check_static(&tx, &self.policy)?;
        let size = bytes.len();
        self.settle(now);
        let order = self.next_order;
        let admission = self.rolling_rate(now);
        if rate(fee, weight) < admission && !self.would_protect((arrived, order), size) {
            return Err(Reject::FeeTooLow { min: per_unit(admission).saturating_mul(weight) });
        }
        let mut conflicts: Vec<Digest> = Vec::new();
        for (c, p) in tx.spent_commitments().zip(tx.spent_positions()) {
            if let Some(other) = self.spends.get(&p)
                && !conflicts.contains(other)
            {
                conflicts.push(*other);
            }
            if !holds(ledger, p, &c).map_err(Reject::Store)? {
                return Err(Reject::UnknownInput(p));
            }
        }
        let claims = check_ops(&tx, ledger, height)?;
        // Claims held by the transactions this one replaces are free.
        if claims.iter().any(|c| self.claims.get(c).is_some_and(|holder| !conflicts.contains(holder))) {
            return Err(Reject::NameConflict);
        }
        // What it pays to take the place of others, before its
        // signatures are looked at: one that pays too little is turned
        // away for an addition, however often it is sent.
        if !conflicts.is_empty() {
            let replaced: u64 = conflicts.iter().map(|id| self.txs[id].fee).sum();
            let min = replaced.saturating_add(self.policy.replacement_per_unit.saturating_mul(weight));
            if fee < min {
                return Err(Reject::ReplacementFee { min });
            }
        }
        // (And one the pool could never hold.)
        if size > self.capacity {
            return Err(Reject::Full);
        }
        // Signatures last: they are most of the cost, and an input naming
        // an output the state does not hold, which anyone can sign with a
        // key of their own, is turned away above for a lookup.
        if !tx.verify_signatures() {
            return Err(Reject::BadSignature);
        }
        tx.check_policy_inputs(height, |p| made_at(ledger, p)).map_err(Reject::Policy)?;
        self.next_order += 1;
        let entry = Entry {
            bytes: bytes.into(),
            size: size as u32,
            recent: false,
            spent: Spent::of(tx.spent_positions().collect()),
            txid,
            fee,
            weight,
            arrived,
            order,
            claims: claims.into_boxed_slice(),
        };
        // Replaced transactions go first, so their room counts; they are
        // put back if the new one still does not fit.
        let removed: Vec<Entry> = conflicts.iter().filter_map(|id| self.remove(id)).collect();
        if let Err(e) = self.make_room(entry.size(), entry.rate(), now) {
            for e in removed {
                self.add(e);
            }
            return Err(e);
        }
        self.add(entry);
        Ok(txid)
    }

    /// Evicts the lowest-rate transactions but the protected until one of
    /// `size` fits, raising the rolling minimum past each, or refuses if
    /// it pays (at `paying`, a scaled rate) less than what it would evict.
    /// It fits when the pool has the bytes for it, and knows of fewer
    /// than the most it may.
    fn make_room(&mut self, size: usize, paying: u128, now: u64) -> Result<(), Reject> {
        if size > self.capacity || self.most == 0 {
            return Err(Reject::Full);
        }
        if self.bytes + size <= self.capacity && self.txs.len() < self.most {
            return Ok(());
        }
        // Evicting the unprotected, all younger than the protected, leaves
        // the protected as they are.
        let until = self.protected_until();
        let mut victims: Vec<&Entry> = self.txs.values().filter(|e| until.is_none_or(|u| e.age_key() > u)).collect();
        victims.sort_unstable_by_key(|e| (e.rate(), std::cmp::Reverse(e.age_key())));
        let mut room = self.capacity - self.bytes;
        let mut known = self.txs.len();
        let mut evict = Vec::new();
        for v in victims {
            if room >= size && known < self.most {
                break;
            }
            if v.rate() >= paying {
                return Err(Reject::Full);
            }
            room += v.size();
            known -= 1;
            evict.push((v.txid, v.rate()));
        }
        if room < size || known >= self.most {
            return Err(Reject::Full);
        }
        self.settle(now);
        for (id, r) in evict {
            self.remove(&id);
            self.rolling = self.rolling.max(r + ((self.policy.replacement_per_unit as u128) << 16));
        }
        Ok(())
    }

    fn add(&mut self, mut entry: Entry) {
        for p in entry.spent() {
            self.spends.insert(*p, entry.txid);
        }
        for c in entry.claims.iter() {
            self.claims.insert(*c, entry.txid);
        }
        self.bytes += entry.size();
        // (Whole, it is among the most recent from here: and the
        // oldest of those may be so no longer.)
        entry.recent = entry.whole();
        if entry.recent {
            self.held += entry.size();
            self.recent_bytes += entry.size();
            self.recent.push_back(entry.txid);
        }
        self.by_age.insert(entry.age_key(), entry.txid);
        self.txs.insert(entry.txid, entry);
        self.age();
    }

    /// Removes a transaction; returns it if it was pooled.
    pub fn remove(&mut self, txid: &Digest) -> Option<Entry> {
        let entry = self.txs.remove(txid)?;
        for p in entry.spent() {
            self.spends.remove(p);
        }
        for c in entry.claims.iter() {
            self.claims.remove(c);
        }
        self.bytes -= entry.size();
        match (entry.whole(), entry.recent) {
            (true, true) => {
                (self.held, self.recent_bytes) = (self.held - entry.size(), self.recent_bytes - entry.size())
            }
            (true, false) => {
                (self.held, self.older_bytes) = (self.held - entry.size(), self.older_bytes - entry.size());
                if !self.policy.holds_all() {
                    self.older.remove(&(self.draw(txid), *txid));
                }
            }
            (false, _) => {}
        }
        self.by_age.remove(&entry.age_key());
        Some(entry)
    }

    /// After the chain's last block changed: drops transactions whose
    /// inputs are no longer unspent or whose name operations the chain has
    /// settled otherwise, shelving them, and brings back shelved ones that
    /// became valid again. `moved` holds, after a reorganization, the
    /// positions the new branch's blocks gave their outputs, by
    /// commitment: a shelved transaction whose input is no longer at its
    /// position is moved to where the same output is now (positions are
    /// not signed, so the signatures stand) and comes back too. `created`
    /// holds the time, by its block, each new output was made at: a
    /// transaction whose outputs are all there has confirmed. Returns how
    /// many left and how many returned.
    pub fn revalidate(
        &mut self,
        ledger: &impl Ledger,
        height: u32,
        moved: &HashMap<Commitment, Vec<u64>>,
        created: &HashMap<Commitment, u64>,
        now: u64,
    ) -> Result<(usize, usize), Error> {
        let _in = crate::heap::enter(crate::heap::Part::Pool);
        let mut gone = Vec::new();
        for e in self.txs.values() {
            // One only known of: gone when what it spends is no longer
            // unspent, which is all that can be told of it. (In a
            // block, or spent by another that is.)
            let Some(tx) = e.tx() else {
                for p in e.spent() {
                    if !ledger.output(*p)?.is_some_and(|(_, _, unspent)| unspent) {
                        gone.push(e.txid);
                        break;
                    }
                }
                continue;
            };
            let mut out = false;
            for (c, p) in tx.spent_commitments().zip(tx.spent_positions()) {
                if !holds(ledger, p, &c)? {
                    out = true;
                    break;
                }
            }
            // (And one whose policy's conditions the chain no longer
            // meets, as it is now: a block could not hold it, and the
            // choosing of every block would find that out anew.)
            let unmet =
                || tx.counts().policy_inputs > 0 && tx.check_policy_inputs(height, |p| made_at(ledger, p)).is_err();
            if out || (tx.counts().ops > 0 && check_ops(&tx, ledger, height).is_err()) || unmet() {
                gone.push(e.txid);
            }
        }
        for id in &gone {
            if let Some(e) = self.remove(id) {
                // (One only known of is let go, and no more: what it
                // made is not known, nor could it be pooled again.)
                let Some(tx) = e.tx() else { continue };
                // Its outputs made by the new blocks: it confirmed, and its
                // wait, to its block's timestamp (blocks replayed after a
                // restart are not timed by the clock), goes to the
                // estimates; never later than now.
                let mut at = None;
                let mut all = true;
                for o in tx.outputs().iter() {
                    match created.get(&o.commitment) {
                        Some(t) => at = Some(at.map_or(*t, |a: u64| a.min(*t))),
                        None => all = false,
                    }
                }
                if let Some(at) = at.filter(|_| all) {
                    let at = at.min(now);
                    self.remember_confirmed(per_unit(e.rate()), at.saturating_sub(e.arrived), at);
                }
                self.shelf.push(e);
            }
        }
        if self.shelf.len() > SHELF {
            let excess = self.shelf.len() - SHELF;
            self.shelf.drain(..excess);
        }
        // (And no more of them, by their size, than a part of what the
        // pool may hold: they are held beside it, and gone through at
        // every block.)
        let most = self.capacity.min(self.policy.whole_recent.saturating_add(self.policy.whole_older)) / SHELF_PART;
        let mut held: usize = self.shelf.iter().map(Entry::size).sum();
        let mut first = 0;
        while held > most && first < self.shelf.len() {
            held -= self.shelf[first].size();
            first += 1;
        }
        self.shelf.drain(..first);
        let mut back = 0;
        let mut keep = Vec::with_capacity(self.shelf.len());
        for e in std::mem::take(&mut self.shelf) {
            // (Only what is whole is shelved.)
            let Some(tx) = e.tx() else { continue };
            let mut ok = !self.txs.contains_key(&e.txid);
            let positions: Vec<u64> = tx.spent_positions().collect();
            let commitments: Vec<Commitment> = tx.spent_commitments().collect();
            // (An output made again elsewhere is another output to what
            // was signed, which is of where it lay: the transaction
            // comes back only if its outputs are where they were.)
            let _ = moved;
            // (A state that cannot be read holds nothing: the entry stays
            // on the shelf.)
            let there = |p: u64, c: &Commitment| holds(ledger, p, c).unwrap_or(false);
            for (i, c) in commitments.iter().enumerate() {
                if !ok {
                    break;
                }
                let p = positions[i];
                ok = there(p, c) && !self.spends.contains_key(&p);
            }
            // A policy input's timelocks count from its output's
            // creation, which may be another on the branch it is on
            // now.
            if ok && tx.counts().policy_inputs > 0 {
                ok = tx.check_policy_inputs(height, |p| made_at(ledger, p)).is_ok();
            }
            if ok && tx.counts().ops > 0 {
                ok = check_ops(&tx, ledger, height).is_ok() && e.claims.iter().all(|c| !self.claims.contains_key(c));
            }
            if ok && self.make_room(e.size(), e.rate(), now).is_ok() {
                self.returned.push(e.txid);
                self.add(e);
                back += 1;
            } else {
                keep.push(e);
            }
        }
        // Shelved entries that are spent for good age out with the shelf.
        self.shelf = keep;
        Ok((gone.len(), back))
    }

    /// The transactions that have come back from the shelf since this
    /// was last asked, and are still pooled: each one's id and size. A
    /// transaction that comes back is one its block was undone under:
    /// peers that did not have that block have never heard of it, and
    /// whoever keeps the pool tells them.
    pub fn take_returned(&mut self) -> Vec<(Digest, usize)> {
        let ids = std::mem::take(&mut self.returned);
        ids.into_iter().filter_map(|id| Some((id, self.txs.get(&id)?.size()))).collect()
    }

    /// Transactions for a block at `height` while `fits` accepts the
    /// running selection (it is called with the candidate list including
    /// the next transaction): first the aged reserve, the longest-waiting
    /// transactions, oldest first, while their bytes together fit
    /// `reserve_bytes` (stopping at the first that does not, so the wait
    /// is by age alone; one larger than the whole reserve is passed over
    /// there, and goes by its fee);
    /// then the rest by fee rate, highest first. Transactions whose name
    /// operations would exceed the block's caps, or whose reveals are not
    /// yet in their window (a commit waits `min_reveal` blocks), are
    /// passed over.
    pub fn select<'a>(
        &'a self,
        ledger: &impl Ledger,
        height: u32,
        min_reveal: u32,
        reserve_bytes: usize,
        mut fits: impl FnMut(&[TransactionRef<'a>]) -> bool,
    ) -> Vec<TransactionRef<'a>> {
        let mut chosen: Vec<TransactionRef<'a>> = Vec::new();
        let mut taken: std::collections::HashSet<Digest> = std::collections::HashSet::new();
        let mut counts = [0usize; 4];
        // Whether `tx` may join, its name operations counted if so.
        let admit = |tx: &TransactionRef<'a>, counts: &mut [usize; 4]| {
            if tx.counts().ops == 0 {
                return true;
            }
            let mut with = *counts;
            for op in tx.ops() {
                with[op.kind() as usize] += 1;
            }
            let over = [OpKind::Commit, OpKind::Reveal, OpKind::Update].iter().any(|k| with[*k as usize] > k.cap());
            if over || !reveals_open(tx, ledger, height, min_reveal) {
                return false;
            }
            *counts = with;
            true
        };
        let mut reserved = 0;
        let mut misfits = 0;
        for e in self.by_age.values().map(|id| &self.txs[id]) {
            // One too large for the reserve at all waits on its fee, and
            // does not hold the others back.
            if e.size() > reserve_bytes {
                continue;
            }
            if reserved + e.size() > reserve_bytes {
                break;
            }
            let before = counts;
            // (A block is made of what is held whole.)
            let Some(tx) = e.tx() else { continue };
            if !admit(&tx, &mut counts) {
                continue;
            }
            chosen.push(tx);
            if !fits(&chosen) {
                // (It, and not the others: one that no block holds, or
                // that this block has no room left for, does not keep
                // out those after it. Until so many in a row have not
                // fitted that the block is taken to be full.)
                chosen.pop();
                counts = before;
                misfits += 1;
                if misfits > MISFITS {
                    break;
                }
                continue;
            }
            misfits = 0;
            reserved += e.size();
            taken.insert(e.txid);
        }
        let mut entries: Vec<&Entry> = self.txs.values().filter(|e| !taken.contains(&e.txid)).collect();
        entries.sort_by(|a, b| b.rate().cmp(&a.rate()).then(a.age_key().cmp(&b.age_key())));
        misfits = 0;
        for e in entries {
            let before = counts;
            let Some(tx) = e.tx() else { continue };
            if !admit(&tx, &mut counts) {
                continue;
            }
            chosen.push(tx);
            if !fits(&chosen) {
                chosen.pop();
                counts = before;
                misfits += 1;
                if misfits > MISFITS {
                    break;
                }
                continue;
            }
            misfits = 0;
        }
        chosen
    }

    /// The expired commits a block at `height` may sweep, by position, at
    /// most the cap.
    pub fn sweeps(ledger: &impl Ledger, height: u32) -> Vec<u64> {
        let Some(last) = height.checked_sub(MAX_REVEAL + 1) else {
            return vec![];
        };
        match ledger.commits_up_to(last) {
            Ok(mut commits) => {
                commits.truncate(MAX_SWEEPS);
                commits
            }
            Err(_) => vec![],
        }
    }

    /// Ids of pooled transactions, in no particular order.
    pub fn ids(&self) -> Vec<Digest> {
        self.txs.keys().copied().collect()
    }
}

#[cfg(test)]
#[path = "tests/mempool.rs"]
mod tests;
