//! A block's proof, made: the proofs of [`crate::block_proof`] and the
//! chain's step ([`crate::chain_proof`]) put together for a block of
//! the chain ([`crate::chain`]), and the verifier a node checks the
//! result with.
//!
//! # What a block carries
//!
//! A block's proof is the chain's: one proof that the chain's proof
//! before it verifies and that this block's proofs do, hiding both. It
//! states what [`crate::chain::Chain::statement`] computes from the
//! block and the state, whose digest the block's header names. In a
//! body it is the argument's proof alone: its program and its
//! statement are the verifier's to say.
//!
//! # What is fixed
//!
//! A chain's step takes a block whose proofs are of one of the shapes
//! its plan lists, and names its own program; both are the same for
//! every node of a network. They follow from the circuits and from the
//! sizes of the proofs, so a [`Setup`] finds them by making a block of
//! each shape once: the sizes its proofs come to are the sizes every
//! block's proofs of that shape are made at.
//!
//! # Shapes
//!
//! - **A reward's block**: one run of [`REWARD_ROWS`] rows (the reward,
//!   and sweeps), no signatures, and the work of the header before.
//! - **A block of transactions**: one run of one of the level's sizes,
//!   or two, four and so on of the largest, joined two and two; and the
//!   signatures in a tree of one, two, four and so on proofs of a fixed
//!   number of signatures each (a proof not full is filled by saying a
//!   signature again: its entry is in the set once more, to no harm).
//!   On the main network: up to 32 runs of 2^16 rows, and up to 512
//!   proofs of 64 signatures, more than those runs have room to use.

use std::collections::HashMap;
use std::time::Duration;

use crate::block_proof::{Beside, PROGRAMS, Runs, Tables, Worked, beside_into, root_into, root_with};
use crate::chain_proof::{Plan, Shape, Stated, Statement, genesis_into, step_into};
use crate::field::F;
use crate::hash::{Digest, EMPTY};
use crate::ledger::{Emission, OUTPUTS_HEIGHT, Record};
use crate::name::{Key, NameOp};
use crate::ntt::Domain;
use crate::output::Output;
use crate::pcs::Params;
use crate::pow::{ItemSource, Nonce};
use crate::proof::{Kind, Proved, program_of, prove_at, prove_hidden, prove_with};
use crate::reading::Deferred;
use crate::segment::{self, Run, closed};
use crate::signature::{Signed, entry, node_into, segment_into};
use crate::signed;
use crate::store::partial::Partial;
use crate::sym::Shared;
use crate::transaction::Transaction;
use crate::verify::{BlockStatement, ProofVerifier};
use crate::xmss::{PublicKey, Signature};

/// Rows of the run of a block that spends nothing by a key: its reward,
/// and the commitments it sweeps.
pub const REWARD_ROWS: usize = 1 << 11;
/// Rows the walks that bring a run's outputs into the root take, at the
/// most: what a run is left room for.
const SETTLE_ROWS: usize = 3 + 2 * 3 * OUTPUTS_HEIGHT;

/// A signature with its key and what it signs.
pub type Signing = (PublicKey, Digest, Signature);

/// The parameters proofs are made under, and the shapes of the blocks
/// of transactions a chain takes.
#[derive(Clone, Copy)]
pub struct Level {
    /// Of the proofs within a block's.
    pub inner: fn(usize) -> Params,
    /// Of the chain's proof, which is the one published.
    pub published: fn(usize) -> Params,
    /// The sizes a run of transactions may have, as logs of its rows,
    /// ascending.
    pub runs: &'static [usize],
    /// Signatures in one proof of them.
    pub per_proof: usize,
    /// The most proofs of signatures a block's tree is over, as a log.
    pub trees: usize,
    /// The most runs of the largest size a block's proof joins, as a
    /// log: a block of more transactions than one run holds is of two
    /// runs, or four, and so on.
    pub joins: usize,
}

/// How long each part of proving took, since this was last asked:
/// the parts of a block's proof, in the order they were made. For
/// whoever says how long a block took, to say where the time went.
static PARTS: std::sync::Mutex<Vec<Timed>> = std::sync::Mutex::new(Vec::new());

/// How many blocks are being proven now: more than one where a block
/// given up has not yet let go beside the one begun after it.
static PROVING: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);

/// The most memory proving has held in any part of it ([`most_held`]).
static MOST_HELD: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);

/// The most memory proving has held, in bytes, in any part of it that
/// has ended, since the program began.
pub fn most_held() -> usize {
    MOST_HELD.load(std::sync::atomic::Ordering::Relaxed)
}

/// A part of proving, as it went.
#[derive(Clone, Copy, Debug)]
pub struct Timed {
    pub name: &'static str,
    /// How long it took (of a part done more than once, together).
    pub took: Duration,
    /// The most memory proving held while it was made, in bytes
    /// ([`crate::heap::Part::Proving`]): this part's, with what the
    /// parts before it left to be held.
    pub most: usize,
    /// Whether another block was being proven beside it, whose memory
    /// is then counted in `most` too.
    pub beside: bool,
}

/// Proving, on this thread, until it is dropped: what is allocated is
/// counted as proving's, and the block as one being proven.
struct Proving(#[allow(dead_code)] crate::heap::Entered);

impl Proving {
    fn begin() -> Proving {
        PROVING.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        Proving(crate::heap::enter(crate::heap::Part::Proving))
    }
}

impl Drop for Proving {
    fn drop(&mut self) {
        PROVING.fetch_sub(1, std::sync::atomic::Ordering::Relaxed);
    }
}

/// What `part` gives, the time it took added to [`PARTS`] under `name`
/// (to what is there under that name already, of a part done more
/// than once), with the most memory proving held meanwhile.
fn timed<T>(name: &'static str, part: impl FnOnce() -> T) -> T {
    use crate::heap::{Part, most, reset_most};
    let alone = || PROVING.load(std::sync::atomic::Ordering::Relaxed) <= 1;
    let began = std::time::Instant::now();
    let mut beside = !alone();
    reset_most(Part::Proving);
    let out = part();
    let held = most(Part::Proving);
    MOST_HELD.fetch_max(held, std::sync::atomic::Ordering::Relaxed);
    beside |= !alone();
    let mut parts = PARTS.lock().unwrap_or_else(|e| e.into_inner());
    match parts.iter_mut().find(|p| p.name == name) {
        Some(p) => {
            p.took += began.elapsed();
            p.most = p.most.max(held);
            p.beside |= beside;
        }
        None => parts.push(Timed { name, took: began.elapsed(), most: held, beside }),
    }
    out
}

/// The parts of proving timed since this was last asked, and how each
/// went.
pub fn parts_timed() -> Vec<Timed> {
    std::mem::take(&mut *PARTS.lock().unwrap_or_else(|e| e.into_inner()))
}

impl Level {
    /// The main network's: 124 bits proven, the published proof ground
    /// more for fewer queries.
    pub const MAINNET: Level = Level {
        inner: |m| Params::proven(m, 2, crate::pcs::SECURITY),
        published: |m| Params::proven_ground(m, 2, crate::pcs::SECURITY, 24),
        runs: &[15, 16],
        per_proof: 64,
        trees: 9,
        joins: 5,
    };

    /// For tests and the dev networks: proofs of the kinds of shape the
    /// main network's have, fewer of them, sound to a few bits and made
    /// sooner.
    pub const SMALL: Level = Level {
        inner: |m| Params::plain(m, 1, 4, 4),
        published: |m| Params::plain(m, 1, 4, 4),
        runs: &[12],
        per_proof: 2,
        trees: 1,
        joins: 1,
    };

    /// The most signatures a block's proof rests on.
    pub fn signatures(&self) -> usize {
        self.per_proof << self.trees
    }
}

/// A digest of two elements of a statement.
fn digest(x: &[F]) -> Digest {
    [x[0].0.to_le_bytes(), x[1].0.to_le_bytes()].concat().try_into().expect("two elements")
}

/// Rows of a proof's hash table and of its machine.
fn rows_of(proof: &Proved) -> [usize; 2] {
    [proof.rows(Kind::Hashes)[0], proof.rows(Kind::Machine)[0]]
}

/// The sizes the proofs of signatures are made at: a proof of
/// signatures, and the node over two of each level.
#[derive(Clone, Debug, Default)]
struct SignedSizes {
    segment: Option<[usize; 2]>,
    nodes: Vec<[usize; 2]>,
}

/// The sizes a block's last proofs are made at, of one shape, and the
/// program its root then has.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Sized {
    beside: [usize; 2],
    root: [usize; 2],
    program: Digest,
}

/// A block's signatures, proven: one proof over a tree of the proofs of
/// [`Level::per_proof`] signatures each, and where each signature's
/// entry is in the tree.
pub struct SignedProof {
    top: Proved,
    /// What the top states, if it is a node; nothing if it is the one
    /// proof of signatures.
    stated: Vec<F>,
    /// The root of the entries' tree, and the proofs it is over, as a
    /// log.
    root: Digest,
    tree: usize,
    entries: signed::Tree,
    places: HashMap<Digest, usize>,
}

impl SignedProof {
    fn as_signed(&self) -> Signed<'_> {
        match self.stated.is_empty() {
            true => Signed::Segment(&self.top, self.root),
            false => Signed::Node(&self.top, &self.stated),
        }
    }

    /// The level of the entries' tree.
    fn level(&self) -> usize {
        signed::LOG_SLOTS + self.tree
    }

    /// The signed set's root.
    pub fn set(&self) -> Digest {
        signed::lift(&self.root, self.level(), signed::DEPTH)
    }

    /// Where the entry of `key`'s signature of `message` with `leaf` is
    /// in the set, and its path. `None` if it is not there.
    fn place(&self, key: &PublicKey, message: &Digest, leaf: u64) -> Option<segment::Signed> {
        let place = *self.places.get(&entry(key, message, leaf))?;
        let mut siblings = self.entries.path(place).siblings;
        siblings.extend_from_slice(&signed::empty_roots()[self.level()..signed::DEPTH]);
        Some((place as u64, siblings))
    }
}

/// The paths of some names, changed in memory: [`Partial`], of the
/// names' tree.
#[derive(Clone, Default)]
pub struct NamesPart {
    nodes: HashMap<(u8, u128), Digest>,
}

impl NamesPart {
    fn index(key: Key, level: usize) -> u128 {
        key.checked_shr(level as u32).unwrap_or(0)
    }

    /// Takes in the leaf at `key` and its path, as the tree has them
    /// before any change.
    pub fn load(&mut self, key: Key, leaf: &Digest, siblings: &[Digest]) {
        let mut node = *leaf;
        for (level, sibling) in siblings.iter().enumerate() {
            let index = Self::index(key, level);
            self.nodes.entry((level as u8, index)).or_insert(node);
            self.nodes.entry((level as u8, index ^ 1)).or_insert(*sibling);
            node = if index & 1 == 1 {
                crate::registry::node(sibling, &node)
            } else {
                crate::registry::node(&node, sibling)
            };
        }
    }

    /// The path of the leaf at `key`, which must be one loaded.
    pub fn path(&self, key: Key) -> Vec<Digest> {
        (0..crate::registry::HEIGHT).map(|level| self.nodes[&(level as u8, Self::index(key, level) ^ 1)]).collect()
    }

    /// Makes the leaf at `key`, which must be one loaded, `leaf`.
    pub fn set(&mut self, key: Key, leaf: &Digest) {
        let mut node = *leaf;
        for level in 0..crate::registry::HEIGHT {
            let index = Self::index(key, level);
            self.nodes.insert((level as u8, index), node);
            let sibling = self.nodes[&(level as u8, index ^ 1)];
            node = if index & 1 == 1 {
                crate::registry::node(&sibling, &node)
            } else {
                crate::registry::node(&node, &sibling)
            };
        }
    }
}

/// What proving a block takes from the state, as it is before the
/// block: the paths of every output the block spends and of the next
/// position, each output spent, the paths of every name it touches, and
/// the records it replaces.
///
/// It is whoever holds the state that fills one in: the node, from its
/// store.
#[derive(Clone, Default)]
pub struct Witness {
    pub outputs: Partial<OUTPUTS_HEIGHT>,
    pub spent: HashMap<u64, crate::output::Record>,
    pub names: NamesPart,
    pub records: HashMap<Key, crate::name::Record>,
}

/// What a network's proofs are made with: the circuits, the plan of
/// the blocks a chain takes, the step's own program, and the proof of
/// where a chain begins.
pub struct Setup {
    pub level: Level,
    tables: Tables,
    pub plan: Plan,
    /// The program of the chain's step: every block's statement names
    /// it ([`crate::chain::params::ChainParams::program`]).
    pub own: Digest,
    /// Rows the chain's proof's hash table and machine are filled to, at
    /// the least.
    pub rows: [usize; 2],
    genesis: Proved,
    began: Vec<F>,
    /// The work's proof's sizes; a reward's block's; those of the
    /// proofs of signatures; and those of a block of transactions, by
    /// its run's size and its tree of signatures.
    work: [usize; 2],
    reward: Sized,
    signed: SignedSizes,
    blocks: Vec<Sized>,
    /// The sizes of the proofs that join runs, a level after another.
    joins: Vec<[usize; 2]>,
}

/// What a setup comes to, less its circuits and its proofs: the numbers
/// that are the same for every node of a network, found once
/// ([`Setup::new`], which takes minutes) and kept, in a file or in the
/// program itself. A node that only checks blocks needs no more of a
/// setup than these ([`ChainVerifier::of`]); one that makes them has
/// the rest back in the time one small proof takes
/// ([`Setup::from_parts`]).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Parts {
    /// The shapes of block a chain takes, the program of the proof of
    /// where a chain begins, and the step's own.
    pub shapes: Vec<Shape>,
    pub genesis: Digest,
    pub own: Digest,
    /// Rows the chain's proof's tables are filled to at the least, the
    /// rows they then have, and the variables of the proof's polynomial.
    pub rows: [usize; 2],
    pub tables: [usize; 2],
    pub m: usize,
    /// The sizes of every other proof: the work's; the proofs of
    /// signatures' and their nodes'; each shape's, the reward's first;
    /// and the joins of runs'.
    work: [usize; 2],
    segment: [usize; 2],
    nodes: Vec<[usize; 2]>,
    blocks: Vec<Sized>,
    joins: Vec<[usize; 2]>,
}

/// What a file of [`Parts`] begins with: other circuits, or another
/// way of writing them down, is another number.
const PARTS_VERSION: u32 = 1;

/// The main network's setup's numbers, as the test that makes that
/// setup writes them (`write_the_main_network_s_setup`).
const MAINNET_PARTS: &[u8] = include_bytes!("../../resources/setup-mainnet.bin");

/// The program of the main network's chain's proof's step, which every
/// block's statement names: the one that setup says, read from where it
/// is written ([`Parts::to_bytes`]: after the shapes and the program of
/// where a chain begins).
pub const MAINNET_PROGRAM: Digest = {
    let b = MAINNET_PARTS;
    let shapes = u32::from_le_bytes([b[4], b[5], b[6], b[7]]) as usize;
    let at = 8 + shapes * 32 * (1 + PROGRAMS) + 32;
    let mut own = [0u8; 32];
    let mut i = 0;
    while i < 32 {
        own[i] = b[at + i];
        i += 1;
    }
    own
};

/// The dev networks' (`--network dev`, `dev-recursive`: those of the
/// dev table), as the test that makes that setup writes them
/// (`write_the_dev_networks_setup`).
#[cfg(feature = "dev")]
const DEV_PARTS: &[u8] = include_bytes!("../../resources/setup-dev.bin");

impl Parts {
    /// The main network's: a node of it makes no setup.
    pub fn mainnet() -> Parts {
        Parts::from_bytes(MAINNET_PARTS).expect("the setup built in is whole")
    }

    /// The dev networks': at [`Level::SMALL`].
    #[cfg(feature = "dev")]
    pub fn dev() -> Parts {
        Parts::from_bytes(DEV_PARTS).expect("the setup built in is whole")
    }

    pub fn to_bytes(&self) -> Vec<u8> {
        let mut w = crate::codec::Writer::default();
        let pair = |w: &mut crate::codec::Writer, rows: &[usize; 2]| rows.iter().for_each(|r| w.u64(*r as u64));
        w.u32(PARTS_VERSION);
        w.u32(self.shapes.len() as u32);
        for shape in &self.shapes {
            w.digest(&shape.root);
            shape.rested.iter().for_each(|d| w.digest(d));
        }
        w.digest(&self.genesis);
        w.digest(&self.own);
        for rows in [&self.rows, &self.tables, &self.work, &self.segment] {
            pair(&mut w, rows);
        }
        w.u64(self.m as u64);
        for list in [&self.nodes, &self.joins] {
            w.u32(list.len() as u32);
            list.iter().for_each(|rows| pair(&mut w, rows));
        }
        w.u32(self.blocks.len() as u32);
        for sized in &self.blocks {
            pair(&mut w, &sized.beside);
            pair(&mut w, &sized.root);
            w.digest(&sized.program);
        }
        w.finish()
    }

    pub fn from_bytes(bytes: &[u8]) -> Option<Parts> {
        let mut r = crate::codec::Reader(bytes);
        let pair = |r: &mut crate::codec::Reader<'_>| -> Option<[usize; 2]> {
            let rows = [r.u64()?, r.u64()?];
            // (None, or what a table can be: a power of two, of the
            // rows of a group of hashes at the least.)
            let sized = |n: &u64| *n == 0 || (n.is_power_of_two() && (128..=1 << 30).contains(n));
            rows.iter().all(sized).then(|| rows.map(|n| n as usize))
        };
        let count = |r: &mut crate::codec::Reader<'_>| r.u32().filter(|n| *n <= 1 << 12).map(|n| n as usize);
        if r.u32()? != PARTS_VERSION {
            return None;
        }
        let mut shapes = Vec::new();
        for _ in 0..count(&mut r)? {
            let root = r.digest()?;
            let mut rested = [EMPTY; PROGRAMS];
            for d in rested.iter_mut() {
                *d = r.digest()?;
            }
            shapes.push(Shape { root, rested });
        }
        let (genesis, own) = (r.digest()?, r.digest()?);
        let (rows, tables, work, segment) = (pair(&mut r)?, pair(&mut r)?, pair(&mut r)?, pair(&mut r)?);
        let m = r.u64().filter(|m| *m <= 40)? as usize;
        let mut lists = [Vec::new(), Vec::new()];
        for list in lists.iter_mut() {
            for _ in 0..count(&mut r)? {
                list.push(pair(&mut r)?);
            }
        }
        let [nodes, joins] = lists;
        let mut blocks = Vec::new();
        for _ in 0..count(&mut r)? {
            blocks.push(Sized { beside: pair(&mut r)?, root: pair(&mut r)?, program: r.digest()? });
        }
        (r.end() && !shapes.is_empty() && shapes.len() == blocks.len()).then_some(Parts {
            shapes,
            genesis,
            own,
            rows,
            tables,
            m,
            work,
            segment,
            nodes,
            blocks,
            joins,
        })
    }
}

/// A chain's proof and what it states: the proof of where a chain
/// begins, or the one a block carried.
pub struct Before {
    proof: Proved,
    stated: Vec<F>,
    first: bool,
}

/// A block to prove: its transactions in order, the commitments it
/// sweeps, and the output that pays its maker (the subsidy and the
/// fees), which is the block's first.
pub struct Contents<'a> {
    pub txs: &'a [Transaction],
    pub sweeps: &'a [u64],
    pub reward: &'a Output,
}

/// A thing a run does, of a block's transactions: the reward's
/// transaction; a transaction's beginning; and its inputs, policy
/// inputs, outputs and the operations on names it carries, each by the
/// transaction's place and its own.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Item {
    Reward,
    Head(usize),
    Input(usize, usize),
    Policy(usize, usize),
    Output(usize, usize),
    Carried(usize, usize),
}

/// What goes in which run of `cap` rows at the most: by the rows each
/// thing takes, which follow from what it is and, for an output, from
/// the position it gets, the first of them `first` (the reward's). A
/// transaction may lie across runs, cut between its inputs and its
/// outputs. The operations on names and the sweeps are the last run's.
/// `None` if one input, or those, are more than a run holds.
fn grouped(
    first: u64,
    rules: &[crate::ledger::Transaction],
    ops: usize,
    sweeps: usize,
    cap: usize,
) -> Option<Vec<Vec<Item>>> {
    let made = |position: u64| 6 + 2 * position.trailing_ones() as usize;
    let input = segment::INPUT_ROWS;
    let mut groups: Vec<Vec<Item>> = vec![vec![Item::Reward]];
    let (mut rows, mut position) = (2 + made(first), first + 1);
    // The run in hand takes `items`, of `takes` rows, or the next does.
    let put = |groups: &mut Vec<Vec<Item>>, rows: &mut usize, items: &[Item], takes: usize| {
        if *rows + takes + SETTLE_ROWS > cap {
            groups.push(Vec::new());
            *rows = 1;
        }
        groups.last_mut().expect("a run").extend_from_slice(items);
        *rows += takes;
        *rows + SETTLE_ROWS <= cap
    };
    for (i, rule) in rules.iter().enumerate() {
        let inputs = (0..rule.inputs.len()).map(|k| Item::Input(i, k));
        let policy = (0..rule.policy.len()).map(|k| Item::Policy(i, k));
        let outputs: Vec<(Item, usize)> = (0..rule.outputs.len())
            .map(|k| (Item::Output(i, k), made(position + k as u64) + (k < rule.covered as usize) as usize))
            .collect();
        let carried = (0..rule.ops.len()).map(|k| Item::Carried(i, k));
        position += rule.outputs.len() as u64;
        let each = std::iter::once((Item::Head(i), 1))
            .chain(inputs.map(|item| (item, input)))
            .chain(policy.zip(&rule.policy).map(|(item, spent)| (item, segment::policy_rows(spent))))
            .chain(outputs)
            .chain(carried.map(|item| (item, 2)));
        for (item, takes) in each {
            if !put(&mut groups, &mut rows, &[item], takes) {
                return None;
            }
        }
    }
    let tail = ops * (14 + signed::DEPTH + 2 * OUTPUTS_HEIGHT + 2 * crate::registry::HEIGHT)
        + sweeps * (2 + 2 * OUTPUTS_HEIGHT);
    put(&mut groups, &mut rows, &[], tail).then_some(groups)
}

/// The proofs of signatures joined into one over `2^tree` of them:
/// `signings` filled to that many proofs' worth with its first. `sizes`
/// are the sizes to make them at; those not yet known are found.
fn sign(
    level: &Level,
    tables: &Tables,
    sizes: &mut SignedSizes,
    signings: &[Signing],
    tree: usize,
) -> Option<SignedProof> {
    let per = level.per_proof;
    assert!(!signings.is_empty() && signings.len() <= per << tree && per <= signed::SLOTS);
    let mut all = signings.to_vec();
    all.resize(per << tree, signings[0].clone());
    // Each proof's entries are its slots, one proof after another.
    let mut slots = vec![EMPTY; signed::SLOTS << tree];
    let mut places = HashMap::new();
    for (i, (key, message, signature)) in all.iter().enumerate() {
        let place = i / per * signed::SLOTS + i % per;
        slots[place] = entry(key, message, signature.index);
        places.entry(slots[place]).or_insert(place);
    }
    let mut proofs: Vec<(Proved, Vec<F>, Digest)> = Vec::new();
    for some in all.chunks(per) {
        let cx = Shared::new();
        let mut chains = Vec::new();
        let root = segment_into(&cx, &mut chains, some, per)?;
        let proof = prove_at(cx, chains, level.inner, sizes.segment.unwrap_or([128, 128]));
        if !proof.holds {
            return None;
        }
        sizes.segment.get_or_insert(rows_of(&proof));
        proofs.push((proof, Vec::new(), root));
    }
    for depth in 0..tree {
        let mut above = Vec::new();
        for pair in proofs.chunks(2) {
            let (a, b) = (as_signed(&pair[0]), as_signed(&pair[1]));
            let cx = Shared::new();
            let mut reader = Deferred::new(&cx);
            let stated = node_into(&cx, &tables.compiled, &mut reader, [&a, &b])?;
            reader.settle(&tables.all());
            let proof = prove_at(cx, vec![], level.inner, sizes.nodes.get(depth).copied().unwrap_or([128, 128]));
            if !proof.holds {
                return None;
            }
            if sizes.nodes.len() == depth {
                sizes.nodes.push(rows_of(&proof));
            }
            let root = Signed::Node(&proof, &stated).root().0;
            above.push((proof, stated, root));
        }
        proofs = above;
    }
    let (top, stated, root) = proofs.pop()?;
    let entries = signed::Tree::new(&slots);
    (entries.root() == root).then_some(SignedProof { top, stated, root, tree, entries, places })
}

fn as_signed(p: &(Proved, Vec<F>, Digest)) -> Signed<'_> {
    match p.1.is_empty() {
        true => Signed::Segment(&p.0, p.2),
        false => Signed::Node(&p.0, &p.1),
    }
}

impl Setup {
    /// The setup of a network that pays by `emission`, with proofs made
    /// at `level`. `source` is any table of the network's work: the
    /// shapes are found by proving a block of each, whose header's
    /// work is part of it.
    pub fn new(level: Level, emission: Emission, source: &impl ItemSource) -> Setup {
        Setup::new_said(level, emission, source, &|_| {})
    }

    /// [`Setup::new`], saying how far it has come to `said` as it goes:
    /// it is minutes of proving, or hours.
    pub fn new_said(level: Level, emission: Emission, source: &impl ItemSource, said: &dyn Fn(&str)) -> Setup {
        let began_at = std::time::Instant::now();
        let say = |what: std::fmt::Arguments<'_>| said(&format!("{:>6.0}s {what}", began_at.elapsed().as_secs_f64()));
        let tables = Tables::new();
        let rested = |stated: &[F]| -> [Digest; PROGRAMS] { std::array::from_fn(|i| digest(&stated[2 * i..])) };
        let work = {
            let cx = Shared::new();
            let (work, stated) = crate::work::work_into(&cx, source, &[1; 32], &[0; 32]);
            (prove_with(cx, vec![], Some(work), level.inner, [128, 128]), stated)
        };
        let shown = Worked { proof: &work.0, stated: &work.1 };
        say(format_args!("the work is proven"));
        let (record, pay) = (Record::block(&crate::ledger::Outputs::default(), 1, 1), Output::to_key_hash(&[7; 32], 1));
        let sample = |set: &Digest, rows: usize| {
            let contents = Contents { txs: &[], sweeps: &[], reward: &pay };
            let runs = Self::runs_of(&record, set, &mut Witness::default(), &contents, None, None);
            segment::prove(runs.expect("a run").remove(0), rows, level.inner)
        };

        // A block of each shape, of some header's work: a reward's, and
        // those with signatures, a tree of each size under a run of each
        // size. For the sizes of their proofs and the programs of their
        // roots.
        let mut key = crate::xmss::SecretKey::generate_with_height(&[0x5a; 32], 1);
        let signing: Signing = (key.public_key(), [0; 32], key.sign(&[0; 32]).expect("a first signature"));
        let mut sizes = SignedSizes::default();
        type Joined = (Proved, Vec<F>);
        // A sample's runs: one's proof, or the proof that joins two.
        enum Kept {
            One(segment::Proved),
            Joined(Proved, Vec<F>),
        }
        fn runs(kept: &Kept) -> Runs<'_> {
            match kept {
                Kept::One(run) => Runs::One(run),
                Kept::Joined(proof, stated) => Runs::Joined(proof, stated),
            }
        }
        use std::rc::Rc;
        let mut samples: Vec<(Rc<Kept>, Option<Rc<Joined>>)> = Vec::new();
        samples.push((Rc::new(Kept::One(sample(&signed::empty_roots()[signed::DEPTH], REWARD_ROWS))), None));
        let mut join_sizes: Vec<[usize; 2]> = Vec::new();
        let largest = 1usize << level.runs[level.runs.len() - 1];
        // The trees of signatures: a proof of them joined with itself is
        // the tree over two of it, and so on up, a proof a level.
        let mut top: Option<(Proved, Vec<F>, Digest)> = None;
        for tree in 0..=level.trees {
            top = Some(match top.take() {
                None => {
                    let one = sign(&level, &tables, &mut sizes, std::slice::from_ref(&signing), 0).expect("signatures");
                    (one.top, one.stated, one.root)
                }
                Some(under) => {
                    let (a, b) = (as_signed(&under), as_signed(&under));
                    let cx = Shared::new();
                    let mut reader = Deferred::new(&cx);
                    let stated = node_into(&cx, &tables.compiled, &mut reader, [&a, &b]).expect("a node");
                    reader.settle(&tables.all());
                    let proof =
                        prove_at(cx, vec![], level.inner, sizes.nodes.get(tree - 1).copied().unwrap_or([128, 128]));
                    assert!(proof.holds, "the sample signatures join");
                    if sizes.nodes.len() == tree - 1 {
                        sizes.nodes.push(rows_of(&proof));
                    }
                    let root = Signed::Node(&proof, &stated).root().0;
                    (proof, stated, root)
                }
            });
            let over = top.as_ref().expect("made above");
            let set = signed::lift(&over.2, signed::LOG_SLOTS + tree, signed::DEPTH);
            let cx = Shared::new();
            let mut reader = Deferred::new(&cx);
            let both = beside_into(&cx, &tables, &mut reader, &as_signed(over), &shown).expect("a join");
            reader.settle(&tables.all());
            let beside = Rc::new((prove_at(cx, vec![], level.inner, [128, 128]), both));
            assert!(beside.0.holds, "the sample signatures and work hold");
            say(format_args!("signatures in a tree of {} proofs", 1usize << tree));
            for log in level.runs {
                samples.push((Rc::new(Kept::One(sample(&set, 1 << log))), Some(beside.clone())));
            }
            say(format_args!("  runs under it"));
            // Runs joined: a run of nothing ends where it began, so it
            // follows itself, and so does what joins two of them.
            let nothing = Record::block(&crate::ledger::Outputs::default(), 1, 0);
            let idle = segment::prove(Run::new(&nothing, closed(), &set), largest, level.inner);
            let mut under = Rc::new(Kept::One(idle));
            for depth in 0..level.joins {
                let cx = Shared::new();
                let mut reader = Deferred::new(&cx);
                let both = [&runs(&under), &runs(&under)];
                let stated = crate::block_proof::join_into(&cx, &tables, &mut reader, both).expect("a join");
                reader.settle(&tables.all());
                let proof = prove_at(cx, vec![], level.inner, join_sizes.get(depth).copied().unwrap_or([128, 128]));
                assert!(proof.holds, "the sample runs join");
                if join_sizes.len() == depth {
                    join_sizes.push(rows_of(&proof));
                }
                under = Rc::new(Kept::Joined(proof, stated));
                samples.push((under.clone(), Some(beside.clone())));
                say(format_args!("  {} runs joined under it", 2usize << depth));
            }
        }
        // The roots, all of one size, so that a chain's step verifies a
        // block's root the same way whatever its shape: the largest any
        // of them comes to.
        let root_of = |(kept, beside): &(Rc<Kept>, Option<Rc<Joined>>), rows: [usize; 2]| {
            let cx = Shared::new();
            let mut reader = Deferred::new(&cx);
            let stated = match beside {
                None => root_into(&cx, &tables, &mut reader, &runs(kept), None, Some(&shown), 1),
                Some(b) => root_with(&cx, &tables, &mut reader, &runs(kept), &Beside::Joined(&b.0, &b.1), 1),
            };
            reader.settle(&tables.all());
            let root = prove_at(cx, vec![], level.inner, rows);
            assert!(root.holds, "the sample block's root holds");
            (root, stated.expect("a root"))
        };
        let mut roots: Vec<(Proved, Vec<F>)> = Vec::new();
        for (i, s) in samples.iter().enumerate() {
            roots.push(root_of(s, [128, 128]));
            say(format_args!("root {} of {}: {:?} rows", i + 1, samples.len(), rows_of(&roots[i].0)));
        }
        let most = roots.iter().map(|r| rows_of(&r.0)).fold([0; 2], |a, b| [a[0].max(b[0]), a[1].max(b[1])]);
        for (i, (root, sample)) in roots.iter_mut().zip(&samples).enumerate() {
            if rows_of(&root.0) != most {
                *root = root_of(sample, most);
                assert_eq!(rows_of(&root.0), most);
                say(format_args!("root {} again, at {most:?} rows", i + 1));
            }
        }
        let shapes: Vec<Shape> =
            roots.iter().map(|(root, stated)| Shape { root: root.program, rested: rested(stated) }).collect();
        let sized: Vec<Sized> = (roots.iter().zip(&samples))
            .map(|((root, _), (_, beside))| Sized {
                beside: beside.as_ref().map_or([0; 2], |b| rows_of(&b.0)),
                root: most,
                program: root.program,
            })
            .collect();
        let (reward, blocks) = (sized[0], sized[1..].to_vec());
        let (first, first_stated) = roots.swap_remove(0);

        // The shape of a chain's proof: rows enough for a step, found by
        // trying, and for the pads of a proof that hides what it is of.
        // The proof of where a chain begins is made to it.
        // (A proof that hides is of a hash table of a group of 128 rows
        // for every query, and more: the leaves the queries open are
        // hidden by a group each ([`crate::hidden::Places::good`]), and
        // with fewer no nonce's queries would do.)
        let hiding = ((level.published)(20).queries + 2) << 7;
        let mut rows = [hiding.next_power_of_two().max(1 << 9), 1 << 15];
        loop {
            let cx = Shared::new();
            let began = genesis_into(&cx);
            let genesis = prove_hidden(cx, level.published, rows, seed());
            assert!(genesis.holds);
            let plan = Plan::new(shapes.clone(), genesis.program, emission, *source.params());
            let cx = Shared::new();
            let mut reader = Deferred::new(&cx);
            let (block, before) =
                (Stated { proof: &first, stated: &first_stated }, Stated { proof: &genesis, stated: &began });
            step_into(&cx, &tables, &mut reader, &plan, 0, &block, &before, true, &[0; 32], &[0; 32]).expect("a step");
            reader.settle(&tables.all());
            // (The machine's rows are its operations, the values they
            // name, and a hiding proof's pads: an eighth more and 2^14
            // is room for those.)
            let (hash, machine) = cx.with(|c| {
                let ops = c.asm.finish_len();
                (c.trace.rows.len(), ops + ops / 8 + (1 << 14))
            });
            say(format_args!("the chain's step at {rows:?} rows takes {:?}", [hash, machine]));
            if hash <= rows[0] && machine <= rows[1] {
                let own = program_of(cx, level.published, rows);
                let work = rows_of(&work.0);
                let (blocks, joins) = (blocks.clone(), join_sizes.clone());
                return Setup {
                    level,
                    tables,
                    plan,
                    own,
                    rows,
                    genesis,
                    began,
                    work,
                    reward,
                    signed: sizes,
                    blocks,
                    joins,
                };
            }
            rows = [rows[0].max(hash.next_power_of_two()), rows[1].max(machine.next_power_of_two())];
        }
    }

    /// What the setup comes to, to keep ([`Parts`]).
    pub fn parts(&self) -> Parts {
        Parts {
            shapes: self.plan.shapes().to_vec(),
            genesis: self.genesis.program,
            own: self.own,
            rows: self.rows,
            tables: rows_of(&self.genesis),
            m: self.genesis.params.m,
            work: self.work,
            segment: self.signed.segment.unwrap_or([128, 128]),
            nodes: self.signed.nodes.clone(),
            blocks: std::iter::once(self.reward).chain(self.blocks.iter().copied()).collect(),
            joins: self.joins.clone(),
        }
    }

    /// The setup `parts` are of, at `level`, of a network that pays by
    /// `emission`: its circuits made, and the proof of where a chain
    /// begins made again. `None` if the parts are not this build's: that
    /// proof is of another program, or of other sizes, than they say.
    pub fn from_parts(level: Level, emission: Emission, pow: crate::pow::PowParams, parts: &Parts) -> Option<Setup> {
        let _in = crate::heap::enter(crate::heap::Part::Setup);
        let shapes = 1 + (level.trees + 1) * (level.runs.len() + level.joins);
        if parts.shapes.len() != shapes || parts.nodes.len() < level.trees || parts.joins.len() < level.joins {
            return None;
        }
        let cx = Shared::new();
        let began = genesis_into(&cx);
        let genesis = prove_hidden(cx, level.published, parts.rows, seed());
        let same = genesis.holds
            && genesis.program == parts.genesis
            && genesis.params.m == parts.m
            && rows_of(&genesis) == parts.tables;
        same.then(|| Setup {
            level,
            tables: Tables::new(),
            plan: Plan::new(parts.shapes.clone(), parts.genesis, emission, pow),
            own: parts.own,
            rows: parts.rows,
            genesis,
            began,
            work: parts.work,
            reward: parts.blocks[0],
            signed: SignedSizes { segment: Some(parts.segment), nodes: parts.nodes.clone() },
            blocks: parts.blocks[1..].to_vec(),
            joins: parts.joins.clone(),
        })
    }

    /// The proofs of `signings` (as many as [`Level::signatures`] at the
    /// most, one at the least), joined: what a block of the
    /// transactions they are of is proven with. They say nothing of any
    /// block, and are made as the transactions come.
    pub fn sign(&self, signings: &[Signing]) -> Option<SignedProof> {
        let proofs = signings.len().div_ceil(self.level.per_proof).next_power_of_two();
        let tree = proofs.trailing_zeros() as usize;
        if signings.is_empty() || tree > self.level.trees {
            return None;
        }
        let _proving = Proving::begin();
        timed("the signatures", || sign(&self.level, &self.tables, &mut self.signed.clone(), signings, tree))
    }

    /// The runs of a block of `contents`, from the state `start` is of,
    /// with the signed set of root `set`: the reward's transaction, the
    /// others, the operations on names they carry, and the sweeps. One
    /// run, if `cap` is none; else as many as it takes for none to have
    /// more than `cap` rows ([`grouped`]), and as many again of nothing
    /// as make their number a power of two. `None` if a signature is
    /// not in the set, the witness lacks a path, or what must be in one
    /// run is more than a run holds.
    fn runs_of(
        start: &Record,
        set: &Digest,
        witness: &mut Witness,
        contents: &Contents<'_>,
        proven: Option<&SignedProof>,
        cap: Option<usize>,
    ) -> Option<Vec<Run>> {
        let (first, height) = (start.next[0], start.height);
        let place = |key: &PublicKey, message: &Digest, leaf: u64| proven?.place(key, message, leaf);
        let of = |position: u64| witness.spent.get(&position).map_or(([0; 20], 0), |r| (r.memo, r.height));
        let rules: Vec<crate::ledger::Transaction> = contents.txs.iter().map(|tx| tx.rule(of)).collect();
        let ops: Vec<&NameOp> = contents.txs.iter().flat_map(|tx| &tx.ops).collect();

        let groups = grouped(first, &rules, ops.len(), contents.sweeps.len(), cap.unwrap_or(usize::MAX / 2))?;

        let reveals = ops.iter().filter_map(|op| match op {
            NameOp::Reveal { commit, .. } => Some(*commit),
            _ => None,
        });
        let last: Vec<u64> = reveals.chain(contents.sweeps.iter().copied()).collect();
        let mut runs: Vec<Run> = Vec::new();
        let mut run = Run::new(start, closed(), set);
        // The next position, and the leaves the run in hand has made,
        // which are in the tree once the run ends.
        let (mut next, mut leaves): (u64, Vec<Digest>) = (first, Vec::new());
        for (g, group) in groups.iter().enumerate() {
            if g > 0 {
                run.settle();
                for leaf in leaves.drain(..) {
                    witness.outputs.append(next, &leaf, crate::ledger::empty_roots());
                    next += 1;
                }
                let after = Run::after(&run);
                runs.push(std::mem::replace(&mut run, after));
            }
            // The nodes to the left of the next position's path, once
            // everything the run spends is gone.
            if next != 0 {
                let mut after = witness.outputs.clone();
                let own = group.iter().filter_map(|item| match item {
                    Item::Input(i, k) => Some(contents.txs[*i].inputs[*k].position),
                    Item::Policy(i, k) => Some(contents.txs[*i].policy_inputs[*k].position),
                    _ => None,
                });
                let tail = last.iter().copied().filter(|_| g + 1 == groups.len());
                own.chain(tail).for_each(|p| after.set(p, &EMPTY));
                run.frontier(&after.frontier(next));
            }
            for item in group {
                match *item {
                    // The reward's transaction: no input, one output.
                    Item::Reward => {
                        let pay = crate::ledger::Transaction {
                            outputs: vec![contents.reward.listed()],
                            ..Default::default()
                        };
                        run.head(&pay);
                        run.output(&pay.outputs[0], &contents.reward.key_hash);
                        leaves.push(pay.outputs[0].leaf(height));
                    }
                    Item::Head(i) => run.head(&rules[i]),
                    Item::Input(i, k) => {
                        let (input, spent) = (&contents.txs[i].inputs[k], &rules[i].inputs[k]);
                        let at = place(&input.pubkey, &rules[i].id(), input.signature.index)?;
                        run.input(spent, &witness.outputs.path(input.position), input.signature.index, &at);
                        witness.outputs.set(input.position, &EMPTY);
                    }
                    Item::Policy(i, k) => {
                        use crate::conditions::{Cond, Shown, rebind_message};
                        let (rule, spent) = (&rules[i], &rules[i].policy[k]);
                        let mut places = Vec::new();
                        for (cond, shown) in spent.conds.iter().zip(&spent.shown) {
                            let Shown::Signers(signers) = shown else { continue };
                            let message = match cond {
                                Cond::Rebind { channel, .. } => rebind_message(channel, &rule.cover()?.1, spent.state),
                                _ => rule.id(),
                            };
                            for (key, leaf) in signers.iter().flatten() {
                                places.push(place(key, &message, *leaf)?);
                            }
                        }
                        run.policy_input(spent, &witness.outputs.path(spent.position), &places);
                        witness.outputs.set(spent.position, &EMPTY);
                    }
                    Item::Output(i, k) => {
                        run.output(&rules[i].outputs[k], &contents.txs[i].outputs[k].key_hash);
                        leaves.push(rules[i].outputs[k].leaf(height));
                    }
                    Item::Carried(i, k) => run.carried(&contents.txs[i].ops[k].digest()),
                }
            }
        }
        // The operations, done after the transactions; then the sweeps.
        for op in ops {
            match op {
                NameOp::Commit { commit, memo } => {
                    run.commit(commit, memo);
                    leaves.push(crate::registry::commit_output(commit, *memo).leaf(height));
                }
                NameOp::Reveal { record, salt, commit } => {
                    let spent = witness.spent.get(commit)?;
                    let key = record.key();
                    let (outputs, names) = (witness.outputs.path(*commit), witness.names.path(key));
                    run.reveal(&record.rule(), salt, &spent.memo, spent.height, *commit, &outputs, &names);
                    witness.outputs.set(*commit, &EMPTY);
                    witness.names.set(key, &crate::name::leaf_of(record));
                    witness.records.insert(key, *record);
                }
                NameOp::Update { record, pubkey, signature } => {
                    let key = record.key();
                    let old = *witness.records.get(&key)?;
                    let at = place(pubkey, &crate::name::update_message(record), signature.index)?;
                    run.update(&record.rule(), &old.rule(), pubkey, signature.index, &at, &witness.names.path(key));
                    witness.names.set(key, &crate::name::leaf_of(record));
                    witness.records.insert(key, *record);
                }
            }
        }
        for position in contents.sweeps {
            let spent = witness.spent.get(position)?;
            run.sweep(&spent.commitment, &spent.memo, spent.height, *position, &witness.outputs.path(*position));
            witness.outputs.set(*position, &EMPTY);
        }
        // Runs of nothing, to a power of two of them.
        runs.push(run);
        while cap.is_some() && !runs.len().is_power_of_two() {
            let last = runs.last_mut().expect("a run");
            last.settle();
            let after = Run::after(last);
            runs.push(after);
        }
        Some(runs)
    }

    /// Whether a block of `txs`, with its reward and `sweeps` sweeps, on
    /// a state whose next position is `next`, is one a chain takes by
    /// this setup's proofs: its rows are a run's, or a few runs' joined,
    /// and its signatures no more than a block's proofs hold. For
    /// whoever chooses a block's transactions.
    pub fn fits(&self, next: u64, txs: &[Transaction], sweeps: usize) -> bool {
        let rules: Vec<crate::ledger::Transaction> = txs.iter().map(|tx| tx.rule(|_| ([0; 20], 0))).collect();
        let ops = txs.iter().map(|tx| tx.ops.len()).sum();
        let cap = match txs.is_empty() {
            true => REWARD_ROWS,
            false => 1 << self.level.runs[self.level.runs.len() - 1],
        };
        let runs = grouped(next, &rules, ops, sweeps, cap).map_or(usize::MAX, |groups| groups.len());
        let most = if txs.is_empty() { 1 } else { 1 << self.level.joins };
        runs <= most && txs.iter().map(|tx| tx.signings().len()).sum::<usize>() <= self.level.signatures()
    }

    /// The proof of where a chain begins, as the chain's proof before
    /// its first block.
    pub fn beginning(&self) -> Before {
        let proof = Proved { program: self.genesis.program, ..self.shell() };
        Before { proof, stated: self.began.clone(), first: true }
    }

    /// The chain's proof a block carried, which states `statement`
    /// ([`crate::chain::Chain::statement`]), as the proof before the
    /// next block's. `None` if the bytes are no proof.
    pub fn carried(&self, proof: &[u8], statement: &Statement) -> Option<Before> {
        let proof = Proved {
            proof: crate::argument::Proof::from_bytes(proof)?,
            public: crate::blake3::words::<8>(&statement.digest()).to_vec(),
            program: self.own,
            ..self.shell()
        };
        Some(Before { proof, stated: statement.elements(), first: false })
    }

    /// A chain's proof without its argument: the parameters and the
    /// tables every one of them has.
    fn shell(&self) -> Proved {
        Proved {
            params: self.genesis.params,
            program: self.own,
            proof: self.genesis.proof.clone(),
            tables: self.genesis.tables.clone(),
            public: self.genesis.public.clone(),
            holds: true,
            used: 0,
            proving: Duration::ZERO,
        }
    }

    /// The proof of the work of a header: `work_hash` its work's hash
    /// ([`crate::block::Header::pow_hash`]), `nonce` its nonce, `source`
    /// the table of its height.
    fn work(&self, source: &impl ItemSource, work_hash: &Digest, nonce: &Nonce) -> (Proved, Vec<F>) {
        let cx = Shared::new();
        let (work, stated) = crate::work::work_into(&cx, source, work_hash, nonce);
        (prove_with(cx, vec![], Some(work), self.level.inner, self.work), stated)
    }

    /// The proof a block of `contents` carries: a block at
    /// `start.height` on the state `start` is of ([`Record::block`]: its
    /// subsidy counted in) and `witness` was taken from. `parent` is the
    /// header before the block's, `source` the table of that header's
    /// height, `before` the chain's proof that header's block carried,
    /// and `proven` the proofs of every signature the transactions rest
    /// on ([`Setup::sign`]; none for a block that has none). `None` if
    /// the block is not one a chain takes: its rows are more than a run
    /// holds, a signature is not among those proven, or what it does
    /// does not hold.
    #[allow(clippy::too_many_arguments)]
    pub fn block(
        &self,
        source: &impl ItemSource,
        parent: &crate::block::Header,
        before: &Before,
        start: &Record,
        mut witness: Witness,
        contents: &Contents<'_>,
        proven: Option<&SignedProof>,
    ) -> Option<Vec<u8>> {
        let _proving = Proving::begin();
        let set = proven.map_or(signed::empty_roots()[signed::DEPTH], SignedProof::set);
        let kept = witness.clone();
        let run = Self::runs_of(start, &set, &mut witness, contents, proven, None)?.remove(0);
        let rows = run.len() + SETTLE_ROWS;
        let per_tree = self.level.runs.len() + self.level.joins;
        let largest = 1usize << self.level.runs[self.level.runs.len() - 1];
        let work = timed("the work", || self.work(source, &parent.pow_hash(), &parent.nonce));
        let shown = Worked { proof: &work.0, stated: &work.1 };
        let cx = Shared::new();
        let mut reader = Deferred::new(&cx);
        let (shape, sized, stated) = match proven {
            None => {
                if rows > REWARD_ROWS {
                    return None;
                }
                let run = timed("the run", || segment::prove(run, REWARD_ROWS, self.level.inner));
                let stated =
                    root_into(&cx, &self.tables, &mut reader, &Runs::One(&run), None, Some(&shown), start.height)?;
                (0, self.reward, stated)
            }
            Some(proven) => {
                // One run, of the smallest size that holds it; or runs of
                // the largest, joined two and two.
                let size = self.level.runs.iter().position(|log| rows <= 1 << log);
                let joined: Option<(Proved, Vec<F>)>;
                let (shape, run) = match size {
                    Some(size) => {
                        joined = None;
                        (
                            proven.tree * per_tree + size,
                            Some(timed("the run", || {
                                segment::prove(run, 1 << self.level.runs[size], self.level.inner)
                            })),
                        )
                    }
                    None => {
                        let mut witness = kept;
                        let runs = Self::runs_of(start, &set, &mut witness, contents, Some(proven), Some(largest))?;
                        let depth = runs.len().trailing_zeros() as usize;
                        if depth == 0 || depth > self.level.joins {
                            return None;
                        }
                        let proved: Vec<segment::Proved> = timed("the runs", || {
                            runs.into_iter().map(|run| segment::prove(run, largest, self.level.inner)).collect()
                        });
                        let mut level: Vec<(Proved, Vec<F>)> = Vec::new();
                        for at in 0..depth {
                            let mut above = Vec::new();
                            for pair in 0..(proved.len() >> (at + 1)) {
                                let children = match at {
                                    0 => [Runs::One(&proved[2 * pair]), Runs::One(&proved[2 * pair + 1])],
                                    _ => [
                                        Runs::Joined(&level[2 * pair].0, &level[2 * pair].1),
                                        Runs::Joined(&level[2 * pair + 1].0, &level[2 * pair + 1].1),
                                    ],
                                };
                                let cx = Shared::new();
                                let mut reader = Deferred::new(&cx);
                                let stated = crate::block_proof::join_into(
                                    &cx,
                                    &self.tables,
                                    &mut reader,
                                    [&children[0], &children[1]],
                                )?;
                                reader.settle(&self.tables.all());
                                let proof =
                                    timed("the runs joined", || prove_at(cx, vec![], self.level.inner, self.joins[at]));
                                if !proof.holds {
                                    return None;
                                }
                                above.push((proof, stated));
                            }
                            level = above;
                        }
                        joined = level.pop();
                        (proven.tree * per_tree + self.level.runs.len() + depth - 1, None)
                    }
                };
                let sized = self.blocks[shape];
                let runs = match (&run, &joined) {
                    (Some(run), _) => Runs::One(run),
                    (None, Some(top)) => Runs::Joined(&top.0, &top.1),
                    (None, None) => return None,
                };
                let beside = {
                    let cx = Shared::new();
                    let mut reader = Deferred::new(&cx);
                    let both = beside_into(&cx, &self.tables, &mut reader, &proven.as_signed(), &shown)?;
                    reader.settle(&self.tables.all());
                    (
                        timed("signatures and work together", || prove_at(cx, vec![], self.level.inner, sized.beside)),
                        both,
                    )
                };
                if !beside.0.holds {
                    return None;
                }
                let with = Beside::Joined(&beside.0, &beside.1);
                let stated = root_with(&cx, &self.tables, &mut reader, &runs, &with, start.height)?;
                (1 + shape, sized, stated)
            }
        };
        reader.settle(&self.tables.all());
        let root = timed("the block's root", || prove_at(cx, vec![], self.level.inner, sized.root));
        if !root.holds || root.program != sized.program {
            return None;
        }
        timed("the chain's step", || self.step(shape, &root, &stated, before, &parent.rest()))
    }

    /// The chain's step over a block's root, of the plan's shape
    /// `shape`: the proof a block carries.
    fn step(&self, shape: usize, root: &Proved, stated: &[F], before: &Before, rest: &Digest) -> Option<Vec<u8>> {
        let cx = Shared::new();
        let mut reader = Deferred::new(&cx);
        let (block, chain) = (Stated { proof: root, stated }, Stated { proof: &before.proof, stated: &before.stated });
        step_into(&cx, &self.tables, &mut reader, &self.plan, shape, &block, &chain, before.first, &self.own, rest)?;
        reader.settle(&self.tables.all());
        let step = prove_hidden(cx, self.level.published, self.rows, seed());
        (step.holds && step.program == self.own).then(|| step.proof.to_bytes())
    }

    /// The verifier of the chain's proofs this setup makes.
    pub fn verifier(&self) -> ChainVerifier {
        ChainVerifier::new(self.genesis.params, self.own, rows_of(&self.genesis))
    }
}

/// What a proof that hides is made random by: the system's randomness.
fn seed() -> [u8; 32] {
    let mut seed = [0u8; 32];
    crate::random::fill(&mut seed).expect("the system's randomness");
    seed
}

/// The verifier of a block's proof: the chain's proof, of the step's
/// program, stating what the chain computes of the block.
pub struct ChainVerifier {
    params: Params,
    program: Digest,
    rows: [usize; 2],
    hashes: crate::circuit::Circuit,
    machine: crate::circuit::Circuit,
    domain: Domain,
    /// Debugging only: every proof is taken.
    unchecked: bool,
}

impl ChainVerifier {
    /// The verifier of chain proofs made under `params`, of the step
    /// of program `program`, with `rows` in the hash table and the
    /// machine (as the proofs have them, which may be more than they
    /// were asked to be filled to).
    pub fn new(params: Params, program: Digest, rows: [usize; 2]) -> ChainVerifier {
        let (hashes, machine) = (crate::recursion::circuit(), crate::machine::circuit());
        ChainVerifier {
            params,
            program,
            rows,
            hashes,
            machine,
            domain: Domain::new(params.k(), false),
            unchecked: false,
        }
    }
}

impl ChainVerifier {
    /// The verifier of the chain's proofs of the setup `parts` are of,
    /// made at `level`: with no proof made, in the time it takes to
    /// make two circuits.
    pub fn of(level: &Level, parts: &Parts) -> ChainVerifier {
        ChainVerifier::new((level.published)(parts.m).hiding(), parts.own, parts.tables)
    }

    /// Debugging only: the same verifier, taking every proof unread.
    pub fn unchecked(self) -> ChainVerifier {
        ChainVerifier { unchecked: true, ..self }
    }
}

impl ProofVerifier for ChainVerifier {
    fn is_unchecked(&self) -> bool {
        self.unchecked
    }

    fn verify(&self, statement: &BlockStatement<'_>, proof: &[u8]) -> bool {
        if self.unchecked {
            return true;
        }
        if statement.chain.program != self.program || statement.digest == EMPTY {
            return false;
        }
        let Some(proof) = crate::argument::Proof::from_bytes(proof) else { return false };
        let public = crate::blake3::words::<8>(&statement.digest);
        let tables = [
            crate::argument::Table { circuit: &self.hashes, rows: self.rows[0], public: &[] },
            crate::argument::Table { circuit: &self.machine, rows: self.rows[1], public: &public },
        ];
        crate::argument::verify_tables(&self.params, &self.domain, &tables, Some(&self.program), &proof).is_some()
    }

    /// The chain's proof shows each header's mix to be its work's.
    fn attests_work(&self) -> bool {
        true
    }
}
