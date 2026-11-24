//! The unspent outputs: the trie of [`super::trie`] over positions, which
//! is their Merkle tree.
//!
//! Every output ever made has a position, the next of a counter, and its
//! leaf in a binary Merkle tree of height [`HEIGHT`] over all positions
//! ([`crate::output::leaf`]); a spent output's leaf is empty again, and
//! an empty subtree of each height has one hash, known beforehand.
//!
//! # A spend does not touch the output's page
//!
//! Spending an output clears its bit in the node above it and changes
//! the hashes above: the nodes on the way are written anew, as they must
//! be, and the page of records is left as it is. So a block writes about
//! a kilobyte for an output it spends, not the four of the page, and the
//! record of a spent output is still there to be had: undoing the block
//! sets the bit again.
//!
//! An output's page is written when outputs are added to it (only ever
//! at the end of the positions, where new outputs go) and when its dead
//! records are dropped.
//!
//! # The sweep
//!
//! Dead records are dropped by a sweep ([`Outputs::sweep`]) that goes
//! round the trie a little with every block: a leaf in which everything
//! dead was spent before the window in which blocks may still be undone
//! is written anew without it, if that is a quarter of it or more (so a
//! record is written at most a few times in its life), or dropped if
//! nothing in it is unspent; and a node whose outputs have thinned until
//! they fit one page becomes a leaf.

use std::io;

use super::backend::Backend;
use super::pagefile::{PageFile, ReadPages, Txn};
use super::sparse::{EMPTY, empty, level_up, root, root_with_path};
#[cfg(test)]
use super::trie::Slot;
use super::trie::{self, CHILD_BYTES, Child, Edits, Fault, LEAF_RECORDS, Part, Step, Tree};
use crate::error::Error;
use crate::hash::Digest;
use crate::hash::{digest_from_bytes, digest_to_bytes};
pub use crate::output::Record;
use crate::output::{MEMO_BYTES, memo_from_bytes, memo_to_bytes};

/// Height of the outputs' tree: positions are below `2^HEIGHT`.
pub const HEIGHT: u32 = 41;
/// The level of the subtrees the outputs are handed to another node in,
/// when it takes the state from this one: parts of 8,192 positions.
///
/// A part is fetched whole and checked whole, against its root: a node
/// that serves a wrong one costs the whole of it. With every position
/// unspent and every output a commit, a part is 8,192 times the 72
/// bytes of an output and the 40 of a commit, under a megabyte: less
/// than a block. (At level 17 it was over nine.) The price is more
/// roots to hand over first: one for each 8,192 positions in which
/// anything is unspent.
///
/// A part is a subtree the trie keeps a hash for, and those are every
/// fourth level down from the top: 17, 13, 9. Level 13 is the largest
/// whose parts are no bigger than a block.
pub const PART_LEVEL: u32 = 13;
const _: () = assert!((1usize << PART_LEVEL) * (8 + RECORD_BYTES + 8 + 32) <= 1 << 20);
const _: () = assert!((HEIGHT - PART_LEVEL).is_multiple_of(4));
/// Serialized size of a [`Record`].
pub const RECORD_BYTES: usize = 32 + MEMO_BYTES + 8 + 4;

fn corrupt(what: &'static str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, what)
}

/// The root of a subtree as it was before a block: where the subtree
/// is, and its root, or nothing where there was nothing.
pub type Before = (u64, Option<Digest>);

/// The outputs' tree: positions for keys, a fixed height, and the hash
/// of an empty subtree for whatever is not there.
pub struct OutputTree;

impl Tree for OutputTree {
    const HEIGHT: u32 = HEIGHT;
    type Key = u64;
    type Record = Record;

    fn record_len(_: &Record) -> usize {
        RECORD_BYTES
    }

    fn write_record(r: &Record, out: &mut Vec<u8>) {
        out.extend_from_slice(&digest_to_bytes(&r.commitment));
        out.extend_from_slice(&memo_to_bytes(&r.memo));
        out.extend_from_slice(&r.amount.to_le_bytes());
        out.extend_from_slice(&r.height.to_le_bytes());
    }

    fn read_record(b: &[u8]) -> io::Result<(Record, &[u8])> {
        let bad = || corrupt("an output's record is not one");
        let (b, rest) = b.split_at_checked(RECORD_BYTES).ok_or_else(bad)?;
        let record = Record {
            commitment: digest_from_bytes(&b[..32]).ok_or_else(bad)?,
            memo: memo_from_bytes(&b[32..32 + MEMO_BYTES]).map_err(|_| bad())?,
            amount: u64::from_le_bytes(b[32 + MEMO_BYTES..40 + MEMO_BYTES].try_into().unwrap()),
            height: u32::from_le_bytes(b[40 + MEMO_BYTES..].try_into().unwrap()),
        };
        Ok((record, rest))
    }

    fn leaf(_: u128, r: &Record) -> Digest {
        r.leaf()
    }

    /// An output weighs its amount: a pass that spends adds them up.
    fn weight(r: &Record) -> u64 {
        r.amount
    }

    /// The sparse tree's step: a part with no sibling is paired with the
    /// empty subtree's hash ([`super::sparse::level_up`]).
    fn lift(level: u32, parts: &mut [(u128, Part)]) -> usize {
        let mut nodes = [(0u64, EMPTY); LEAF_RECORDS];
        for (node, part) in nodes.iter_mut().zip(parts.iter()) {
            *node = (part.0 as u64, part.1.hash);
        }
        let n = level_up(level as usize, &mut nodes[..parts.len()]);
        for (part, node) in parts.iter_mut().zip(&nodes[..n]) {
            *part = (node.0 as u128, Part { hash: node.1, single: false });
        }
        n
    }

    /// Every level at once, with the parts turned to the sparse tree's
    /// nodes and back once and not at each level.
    fn combine(level: u32, top: u32, parts: &mut [(u128, Part)]) -> Option<Part> {
        if parts.is_empty() {
            return None;
        }
        let mut nodes = [(0u64, EMPTY); LEAF_RECORDS];
        for (node, part) in nodes.iter_mut().zip(parts.iter()) {
            *node = (part.0 as u64, part.1.hash);
        }
        Some(Part { hash: root(level as usize, top as usize, &mut nodes[..parts.len()]), single: false })
    }

    fn refuse(key: u128, fault: Fault) -> Error {
        match fault {
            // A spend of what is not there to spend is the block's fault;
            // anything else is ours.
            Fault::NotLive => Error::NoSuchOutput(key as u64),
            _ => corrupt("a change to the outputs cannot be made").into(),
        }
    }
}

/// The root of the outputs' tree whose nonempty subtrees at `level` have
/// the roots `parts` (ascending by index): what a node that is given a
/// state's parts checks against the state's root.
pub fn parts_root(level: u32, parts: &[(u64, Digest)]) -> Digest {
    root(level as usize, HEIGHT as usize, &mut parts.to_vec())
}

/// The root of the subtree at `level` whose unspent outputs are
/// `outputs` (ascending by position): what a part received is checked
/// against, among the roots of the parts.
pub fn part_root(level: u32, outputs: &[(u64, Record)]) -> Digest {
    let mut leaves: Vec<(u64, Digest)> = outputs.iter().map(|(p, r)| (*p, r.leaf())).collect();
    root(0, level as usize, &mut leaves)
}

/// The hash of a subtree of `height` levels with this part.
fn hash_of(part: Option<Part>, height: u32) -> Digest {
    part.map_or(*empty(height as usize), |p| p.hash)
}

/// The set of unspent outputs, as a root record holds it: the root of
/// the trie, the next position, and how many outputs are unspent.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Outputs {
    pub root: Child,
    /// The position the next new output takes.
    pub next: u64,
    /// Unspent outputs.
    pub count: u64,
}

impl Outputs {
    /// No output yet.
    pub const EMPTY: Outputs = Outputs { root: Child::Empty, next: 0, count: 0 };
    /// Serialized size.
    pub const BYTES: usize = CHILD_BYTES + 16;

    /// The root of the outputs' tree.
    pub fn hash(&self) -> Digest {
        hash_of(self.root.part(), HEIGHT)
    }

    pub fn to_bytes(&self) -> [u8; Self::BYTES] {
        let mut v = Vec::with_capacity(Self::BYTES);
        self.root.write(&mut v);
        v.resize(CHILD_BYTES, 0);
        v.extend_from_slice(&self.next.to_le_bytes());
        v.extend_from_slice(&self.count.to_le_bytes());
        v.try_into().unwrap()
    }

    pub fn from_bytes(b: &[u8]) -> io::Result<Outputs> {
        let bad = || corrupt("the outputs' root is not one");
        if b.len() != Self::BYTES {
            return Err(bad());
        }
        let (root, rest) = Child::read(&b[..CHILD_BYTES])?;
        if rest.iter().any(|x| *x != 0) {
            return Err(bad());
        }
        let next = u64::from_le_bytes(b[CHILD_BYTES..CHILD_BYTES + 8].try_into().unwrap());
        let count = u64::from_le_bytes(b[CHILD_BYTES + 8..].try_into().unwrap());
        if next > 1 << HEIGHT || count > next {
            return Err(bad());
        }
        Ok(Outputs { root, next, count })
    }

    fn pass<B: Backend>(
        &self,
        txn: &mut Txn<'_, B>,
        height: u32,
        edits: Edits<'_, OutputTree>,
        next: u64,
    ) -> Result<Outputs, Error> {
        debug_assert!(edits.flips.windows(2).all(|w| w[0] <= w[1]), "positions ascend");
        let (root, change) = trie::update(txn, self.root, height, edits)?;
        let count = self.count.checked_add_signed(change).ok_or_else(|| corrupt("the count of outputs is wrong"))?;
        Ok(Outputs { root, next, count })
    }

    /// The set after a block at `height` that spends the outputs at
    /// `spends` (ascending) and makes `outputs`, which take the next
    /// positions in order. [`Error::NoSuchOutput`] if a spent position
    /// holds no unspent output (or is spent twice); the transaction is
    /// then to be dropped.
    pub fn apply<B: Backend>(
        &self,
        txn: &mut Txn<'_, B>,
        height: u32,
        spends: &[u64],
        outputs: &[Record],
    ) -> Result<Outputs, Error> {
        let next = self.next + outputs.len() as u64;
        assert!(next <= 1 << HEIGHT, "more outputs than the tree has positions");
        if let Some(p) = spends.iter().find(|p| **p >= self.next) {
            return Err(Error::NoSuchOutput(*p));
        }
        let edits = Edits { flips: spends, run: outputs, run_from: self.next as u128, ..Edits::none() };
        self.pass(txn, height, edits, next)
    }

    /// [`Outputs::apply`], which also returns the root of every subtree
    /// at `level` the block changes, as it was before the block (`None`
    /// where there was nothing): what takes the roots of the set's parts
    /// back to the block before. And the amounts of the outputs spent,
    /// added up.
    pub fn apply_keeping<B: Backend>(
        &self,
        txn: &mut Txn<'_, B>,
        height: u32,
        spends: &[u64],
        outputs: &[Record],
        level: u32,
    ) -> Result<(Outputs, Vec<Before>, u128), Error> {
        let next = self.next + outputs.len() as u64;
        assert!(next <= 1 << HEIGHT, "more outputs than the tree has positions");
        if let Some(p) = spends.iter().find(|p| **p >= self.next) {
            return Err(Error::NoSuchOutput(*p));
        }
        let edits: Edits<'_, OutputTree> =
            Edits { flips: spends, run: outputs, run_from: self.next as u128, ..Edits::none() };
        let (root, change, before, spent) = trie::update_keeping(txn, self.root, height, edits, level)?;
        let count = self.count.checked_add_signed(change).ok_or_else(|| corrupt("the count of outputs is wrong"))?;
        let before = before.into_iter().map(|(i, part)| (i as u64, part.map(|p| p.hash))).collect();
        Ok((Outputs { root, next, count }, before, spent))
    }

    /// The root of every nonempty subtree at `level`, ascending by index:
    /// the set's parts. They hash to the set's root ([`parts_root`]).
    pub fn parts(&self, pages: &impl ReadPages, level: u32) -> io::Result<Vec<(u64, Digest)>> {
        let mut out = Vec::new();
        trie::parts_at::<OutputTree>(pages, self.root, level, &mut |index, part| out.push((index as u64, part.hash)))?;
        Ok(out)
    }

    /// Every output kept in the subtree of index `index` at `level`, in
    /// position order, and whether it is unspent.
    pub fn part(&self, pages: &impl ReadPages, level: u32, index: u64) -> io::Result<Vec<(u64, Record, bool)>> {
        let mut out = Vec::new();
        trie::for_each_in::<OutputTree>(pages, self.root, level, index as u128, &mut |key, record, live| {
            out.push((key as u64, *record, live))
        })?;
        Ok(out)
    }

    /// The set with `outputs` put in, each at its position (ascending,
    /// none of them taken), and `next` the next position after: how a
    /// state received from elsewhere is installed, a part at a time.
    pub fn install<B: Backend>(
        &self,
        txn: &mut Txn<'_, B>,
        outputs: &[(u64, Record, bool)],
        next: u64,
    ) -> Result<Outputs, Error> {
        debug_assert!(outputs.windows(2).all(|w| w[0].0 < w[1].0) && outputs.iter().all(|o| !o.2 && o.0 < next));
        self.pass(txn, 0, Edits { puts: outputs, ..Edits::none() }, next.max(self.next))
    }

    /// The set with the outputs at `removes` taken out and `puts` put
    /// in (both ascending, each put where no output is left), and `next`
    /// the next position: how a part of a state being received is put
    /// in place of an older one.
    pub fn exchange<B: Backend>(
        &self,
        txn: &mut Txn<'_, B>,
        removes: &[u64],
        puts: &[(u64, Record, bool)],
        next: u64,
    ) -> Result<Outputs, Error> {
        debug_assert!(puts.windows(2).all(|w| w[0].0 < w[1].0) && puts.iter().all(|o| !o.2 && o.0 < next));
        self.pass(txn, 0, Edits { removes, puts, ..Edits::none() }, next)
    }

    /// Frees every page of the set.
    pub fn free<B: Backend>(&self, txn: &Txn<'_, B>) -> io::Result<()> {
        trie::free::<OutputTree, B>(txn, self.root)
    }

    /// The set before a block that spent `spends` (ascending) and made
    /// the outputs from position `next` on: those are removed, and the
    /// spent ones are unspent again. `height` is the block's less one.
    pub fn undo<B: Backend>(
        &self,
        txn: &mut Txn<'_, B>,
        height: u32,
        spends: &[u64],
        next: u64,
    ) -> Result<Outputs, Error> {
        assert!(next <= self.next);
        let edits = Edits { flips: spends, revive: true, truncate: next as u128, ..Edits::none() };
        self.pass(txn, height, edits, next)
    }

    /// Sweeps part of the trie: from position `from`, looks at leaves
    /// holding up to `budget` records and drops what is dead in them and spent before
    /// `horizon` (the height of the oldest block that may still be
    /// undone). Returns the set, whose tree and counts are as they were,
    /// and the position to sweep from next: 0 once the end is reached.
    pub fn sweep<B: Backend>(
        &self,
        txn: &mut Txn<'_, B>,
        from: u64,
        budget: usize,
        horizon: u32,
    ) -> Result<(Outputs, u64), Error> {
        let (root, reached) = trie::sweep::<OutputTree, B>(txn, self.root, from as u128, budget, horizon)?;
        let next = if reached >= self.next as u128 { 0 } else { reached as u64 };
        Ok((Outputs { root, ..*self }, next))
    }

    /// The output at `position` and whether it is unspent; `None` if no
    /// record of one is kept (there never was one, or it was spent and
    /// its record has since been dropped).
    pub fn get(&self, pages: &impl ReadPages, position: u64) -> io::Result<Option<(Record, bool)>> {
        trie::get::<OutputTree>(pages, self.root, position as u128)
    }

    /// The path of `position` in the outputs' tree: its leaf (empty if no
    /// unspent output is there) and the sibling at each level up to the
    /// root, which [`super::sparse::root_of_path`] recomputes from them.
    pub fn prove(&self, pages: &impl ReadPages, position: u64) -> io::Result<(Digest, [Digest; HEIGHT as usize])> {
        let mut path = [EMPTY; HEIGHT as usize];
        let mut leaf = EMPTY;
        trie::walk_to::<OutputTree>(pages, self.root, position as u128, &mut |step| match step {
            // Nothing below: the siblings are those of an empty tree.
            Step::Empty { height, .. } => {
                for (l, s) in path[..height as usize].iter_mut().enumerate() {
                    *s = *empty(l);
                }
            }
            // The siblings from the level of the child the position is
            // under up to the node's own: below that they are the child's.
            Step::Node { height, base, children } => {
                let low = trie::below(height);
                let levels = trie::levels::<OutputTree>(children, height, base);
                let (_, span) = trie::group_of(children, height, ((position as u128 - base) >> low) as usize);
                for up in span..height - low {
                    let level = low + up;
                    let sibling = (position as u128 >> level) ^ 1;
                    path[level as usize] = levels.find(up, sibling).map_or(*empty(level as usize), |p| p.hash);
                }
            }
            Step::Leaf { height, slots, .. } => {
                let mut nodes = [(0u64, EMPTY); LEAF_RECORDS];
                let mut n = 0;
                for s in slots.iter().filter(|s| s.live) {
                    nodes[n] = (s.key as u64, s.record.leaf());
                    if s.key == position as u128 {
                        leaf = nodes[n].1;
                    }
                    n += 1;
                }
                root_with_path(0, height as usize, &mut nodes[..n], Some((position, &mut path[..height as usize])));
            }
        })?;
        Ok((leaf, path))
    }

    /// Marks every page of the set in `file`'s map of free space, as must
    /// be done when the file is opened. Reads the nodes, not the leaves.
    pub fn mark<B: Backend>(&self, file: &PageFile<B>) -> io::Result<()> {
        trie::mark::<OutputTree, B>(file, self.root)
    }

    /// Calls `f` with every output kept, in position order: its position,
    /// its record and whether it is unspent.
    pub fn for_each(&self, pages: &impl ReadPages, f: &mut dyn FnMut(u64, &Record, bool)) -> io::Result<()> {
        trie::for_each::<OutputTree>(pages, self.root, &mut |key, record, live| f(key as u64, record, live))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::store::sparse::root_of_path;
    use crate::store::testing::{Lost, MemBackend};
    use crate::store::trie::{BITS, read_leaf, read_node, span_of, write_leaf, write_node};
    use crate::test_util::Rng;
    use std::collections::BTreeMap;

    fn record(rng: &mut Rng, height: u32) -> Record {
        Record {
            commitment: rng.digest(),
            memo: rng.digest()[..20].try_into().unwrap(),
            amount: rng.next_u64(),
            height,
        }
    }

    /// The set as a map, and the tree's root by the definition.
    #[derive(Clone, Default, PartialEq, Debug)]
    struct Model {
        outputs: BTreeMap<u64, (Record, bool)>,
        next: u64,
    }

    impl Model {
        fn hash(&self) -> Digest {
            let mut nodes: Vec<(u64, Digest)> =
                self.outputs.iter().filter(|(_, v)| v.1).map(|(p, v)| (*p, v.0.leaf())).collect();
            root(0, HEIGHT as usize, &mut nodes)
        }

        fn live(&self) -> Vec<u64> {
            self.outputs.iter().filter(|(_, v)| v.1).map(|(p, _)| *p).collect()
        }
    }

    struct World {
        file: PageFile<MemBackend>,
        set: Outputs,
        model: Model,
        tip: u32,
        /// For each block: the set and the model before it, and what it spent.
        history: Vec<(Outputs, Model, Vec<u64>)>,
    }

    impl World {
        fn new() -> World {
            let file = PageFile::create(MemBackend::new()).unwrap();
            World { file, set: Outputs::EMPTY, model: Model::default(), tip: 0, history: Vec::new() }
        }

        /// A block that spends `spends` of the unspent outputs, picked by
        /// `rng`, and makes `adds`. Returns the bytes of pages it wrote.
        fn block(&mut self, rng: &mut Rng, spends: usize, adds: usize) -> Result<u64, Error> {
            let mut live = self.model.live();
            let mut picked = Vec::new();
            for _ in 0..spends.min(live.len()) {
                picked.push(live.swap_remove(rng.next_u64() as usize % live.len()));
            }
            picked.sort_unstable();
            let height = self.tip + 1;
            let records: Vec<Record> = (0..adds).map(|_| record(rng, height)).collect();
            self.apply(&picked, &records)
        }

        fn apply(&mut self, spends: &[u64], records: &[Record]) -> Result<u64, Error> {
            let height = self.tip + 1;
            let mut txn = self.file.begin()?;
            let set = self.set.apply(&mut txn, height, spends, records)?;
            let written = txn.written();
            txn.commit(&set.to_bytes())?;
            self.history.push((self.set, self.model.clone(), spends.to_vec()));
            for p in spends {
                self.model.outputs.get_mut(p).unwrap().1 = false;
            }
            for r in records {
                self.model.outputs.insert(self.model.next, (*r, true));
                self.model.next += 1;
            }
            (self.set, self.tip) = (set, height);
            Ok(written)
        }

        /// Undoes the last block.
        fn undo(&mut self) {
            let (before, model, spends) = self.history.pop().unwrap();
            let mut txn = self.file.begin().unwrap();
            let set = self.set.undo(&mut txn, self.tip - 1, &spends, before.next).unwrap();
            txn.commit(&set.to_bytes()).unwrap();
            (self.set, self.model, self.tip) = (set, model, self.tip - 1);
            assert_eq!(set.hash(), before.hash());
            assert_eq!((set.next, set.count), (before.next, before.count));
        }

        /// The set is the model: root, counts, every record and whether it
        /// is spent, and paths that lead to the root.
        fn check(&self, rng: &mut Rng) {
            let hash = self.model.hash();
            assert_eq!(self.set.hash(), hash);
            assert_eq!(self.set.next, self.model.next);
            assert_eq!(self.set.count as usize, self.model.live().len());
            let mut seen = Vec::new();
            self.set.for_each(&self.file, &mut |p, r, live| seen.push((p, (*r, live)))).unwrap();
            assert!(
                seen.iter().copied().eq(self.model.outputs.iter().map(|(p, v)| (*p, *v))),
                "every record, in order"
            );
            let mut probes: Vec<u64> = (0..12).map(|_| rng.next_u64() % (self.model.next + 3)).collect();
            probes.extend([0, self.model.next.saturating_sub(1), self.model.next, (1 << HEIGHT) - 1]);
            for p in probes {
                let want = self.model.outputs.get(&p).copied();
                assert_eq!(self.set.get(&self.file, p).unwrap(), want, "position {p}");
                let (leaf, path) = self.set.prove(&self.file, p).unwrap();
                let want_leaf = want.filter(|v| v.1).map_or(EMPTY, |v| v.0.leaf());
                assert_eq!(leaf, want_leaf, "position {p}");
                assert_eq!(root_of_path(p, &leaf, &path), hash, "the path of {p}");
            }
        }

        /// Opened again from what is on disk: the same set, and every unit
        /// in use is one the set reaches (nothing is leaked).
        fn reopen(&mut self) {
            let file = PageFile::open(MemBackend::from_image(self.file.backend().image(Lost::All))).unwrap();
            let set = Outputs::from_bytes(file.root().payload()).unwrap();
            assert_eq!(set, self.set);
            set.mark(&file).unwrap();
            file.seal();
            assert_eq!(file.space().0, self.file.space().0, "units reached, and units in use");
            self.file = file;
        }
    }

    #[test]
    fn the_empty_set_and_one_output() {
        let mut w = World::new();
        let mut rng = Rng::new(1);
        assert_eq!(w.set.hash(), *empty(HEIGHT as usize));
        w.check(&mut rng);
        assert_eq!(Outputs::from_bytes(&Outputs::EMPTY.to_bytes()).unwrap(), Outputs::EMPTY);
        // One output: the root is a leaf, a page of one record.
        w.block(&mut rng, 0, 1).unwrap();
        assert!(matches!(w.set.root, Child::Leaf { records: 1, live: 1, last_spend: 0, .. }));
        w.check(&mut rng);
        // Spent: the tree is empty again, and the record is still kept.
        w.block(&mut rng, 1, 0).unwrap();
        assert!(matches!(w.set.root, Child::Leaf { records: 1, live: 0, last_spend: 2, .. }));
        assert_eq!((w.set.hash(), w.set.count, w.set.next), (*empty(HEIGHT as usize), 0, 1));
        w.check(&mut rng);
        w.reopen();
        w.undo();
        w.check(&mut rng);
        assert!(matches!(w.set.root, Child::Leaf { records: 1, live: 1, .. }));
        w.undo();
        assert_eq!(w.set, Outputs::EMPTY);
        w.reopen();
        assert_eq!(w.file.space().0, crate::store::pagefile::HEADER_UNITS);
    }

    /// Blocks of every size against the model: after each the set is the
    /// model, and after some it is opened again from disk.
    #[test]
    fn blocks_against_a_model() {
        let mut w = World::new();
        let mut rng = Rng::new(0x0575);
        let sizes =
            [(0, 5), (2, 60), (10, 3), (30, 300), (0, 0), (200, 40), (50, 1500), (700, 0), (300, 900), (900, 2)];
        for round in 0..3 {
            let sizes = if cfg!(debug_assertions) { &sizes[2 * round..2 * round + 6] } else { &sizes[..] };
            for (i, (spends, adds)) in sizes.iter().enumerate() {
                w.block(&mut rng, *spends, *adds).unwrap();
                w.check(&mut rng);
                if i % 4 == round {
                    w.reopen();
                }
            }
        }
        assert!(w.set.count > 1000 && w.model.next > 4000, "{} of {}", w.set.count, w.model.next);
        assert!(matches!(w.set.root, Child::Node { .. }));
        // Then every block undone, newest first, back to nothing.
        while !w.history.is_empty() {
            w.undo();
            if w.history.len().is_multiple_of(7) {
                w.check(&mut rng);
                w.reopen();
            }
        }
        assert_eq!(w.set, Outputs::EMPTY);
        assert_eq!(w.file.space().0, crate::store::pagefile::HEADER_UNITS);
    }

    /// A spend writes the nodes above its output and nothing else: not
    /// the page the output is in.
    #[test]
    fn a_spend_leaves_the_outputs_page_alone() {
        let mut w = World::new();
        let mut rng = Rng::new(0x1eaf);
        w.block(&mut rng, 0, 5000).unwrap();
        // Nine nodes lie between the root and a lowest leaf.
        let levels = ((HEIGHT - 5) / BITS) as u64;
        assert_eq!(levels, 9);
        let one = w.block(&mut rng, 1, 0).unwrap();
        assert!(one <= levels * 1024, "{one} bytes for one spend");
        // A hundred spread over the set share the nodes near the root.
        let hundred = w.block(&mut rng, 100, 0).unwrap();
        assert!(hundred < 100 * 2 * 1024, "{hundred} bytes for a hundred spends");
        // Adding goes to the end: a page a few dozen outputs, and the
        // nodes above the end once.
        let added = w.block(&mut rng, 0, 320).unwrap();
        assert!(added < 320 * 80 + 12 * 1024, "{added} bytes for 320 outputs");
        w.check(&mut rng);
        // The file is about its outputs' size: what was replaced is reused.
        let (used, end) = w.file.space();
        assert!(used * 512 < 5420 * 120, "{used} units for 5,420 records");
        assert!(end < used + used / 4, "{used} of {end} units in use");
    }

    /// What a block may not spend, and that refusing leaves the set as
    /// it was.
    #[test]
    fn spends_of_nothing_are_refused() {
        let mut w = World::new();
        let mut rng = Rng::new(0xbad);
        w.block(&mut rng, 0, 300).unwrap();
        w.block(&mut rng, 40, 10).unwrap();
        let spent = *w.history[1].2.first().unwrap();
        let live = w.model.live();
        let used = w.file.space().0;
        for (spends, at) in [
            (vec![spent], spent),
            (vec![live[3], live[3]], live[3]),
            (vec![live[0], w.set.next], w.set.next),
            (vec![(1 << HEIGHT) - 1], (1 << HEIGHT) - 1),
            (vec![live[1], spent, live[200]], spent),
        ] {
            let mut sorted = spends.clone();
            sorted.sort_unstable();
            assert_eq!(w.apply(&sorted, &[record(&mut rng, 3)]).err(), Some(Error::NoSuchOutput(at)), "{spends:?}");
            // The transaction was dropped: nothing is taken, nothing changed.
            assert_eq!(w.file.space().0, used);
            w.check(&mut rng);
        }
        w.block(&mut rng, 5, 5).unwrap();
        w.check(&mut rng);
    }

    /// Outputs far apart: positions near both ends of the tree, by a
    /// counter set far ahead.
    #[test]
    fn positions_across_the_whole_tree() {
        let mut w = World::new();
        let mut rng = Rng::new(0xfa4);
        w.block(&mut rng, 0, 70).unwrap();
        for jump in [1u64 << 12, 1 << 20, 1 << 33, (1 << 40) + 12345, (1 << 41) - 200] {
            // As if every position between had been used and its record
            // dropped: the counter moves on.
            w.set.next = jump;
            w.model.next = jump;
            w.block(&mut rng, 20, 90).unwrap();
            w.check(&mut rng);
        }
        w.reopen();
        assert_eq!(w.set.next, (1 << 41) - 110);
        for _ in 0..4 {
            w.block(&mut rng, 100, 0).unwrap();
            w.check(&mut rng);
        }
    }

    /// Power lost at every write and sync of a run of blocks: what is
    /// opened afterwards is the set after one of them, whole.
    #[test]
    fn a_crash_leaves_the_set_of_a_block() {
        let run = |crash_at: Option<u64>| -> (World, Vec<Model>, u64) {
            let mut w = World::new();
            if let Some(n) = crash_at {
                w.file.backend().crash_at(n);
            }
            let mut rng = Rng::new(0xc4a5);
            let mut states = vec![w.model.clone()];
            for (spends, adds) in [(0, 100), (20, 40), (60, 0), (10, 150), (70, 70)] {
                if w.block(&mut rng, spends, adds).is_err() {
                    break;
                }
                states.push(w.model.clone());
            }
            let ops = w.file.backend().ops();
            (w, states, ops)
        };
        let (_, states, ops) = run(None);
        assert!(ops > 12, "{ops}");
        for crash_at in 1..=ops {
            let (w, done, _) = run(Some(crash_at));
            for lost in [Lost::All, Lost::None, Lost::Some(crash_at)] {
                let file = PageFile::open(MemBackend::from_image(w.file.backend().image(lost))).unwrap();
                let seq = file.root().seq as usize;
                assert!(seq + 1 == done.len() || seq == done.len(), "crash at {crash_at}: {seq} of {}", done.len());
                let set = if seq == 0 { Outputs::EMPTY } else { Outputs::from_bytes(file.root().payload()).unwrap() };
                set.mark(&file).unwrap();
                file.seal();
                let mut after = World { file, set, model: states[seq].clone(), tip: seq as u32, history: Vec::new() };
                let mut rng = Rng::new(crash_at);
                after.check(&mut rng);
                after.block(&mut rng, 25, 25).unwrap();
                after.check(&mut rng);
                after.reopen();
            }
        }
    }

    /// The decoders of pages and roots take any bytes without panicking,
    /// and what they accept they write back the same.
    #[test]
    fn decoders_refuse_what_is_not_theirs() {
        let mut rng = Rng::new(0xdec);
        let mut w = World::new();
        w.block(&mut rng, 0, 400).unwrap();
        w.block(&mut rng, 90, 30).unwrap();
        let Child::Node { page, .. } = w.set.root else { panic!("a node") };
        let mut buf = [0u8; 4096];
        let node = w.file.read(page, &mut buf).unwrap().to_vec();
        let children = read_node(&node, HEIGHT).unwrap();
        assert!(read_node(&node, HEIGHT - BITS).is_err(), "a node of another height");
        // A leaf's page and its entry, found on the way down.
        let (mut child, mut height) = (w.set.root, HEIGHT);
        let mut base = 0u128;
        while let Child::Node { page, .. } = child {
            let kids = read_node(w.file.read(page, &mut buf).unwrap(), height).unwrap();
            let low = height - BITS;
            let k = kids.iter().position(|c| *c != Child::Empty).unwrap();
            (child, base, height) = (kids[k], base + ((k as u128) << low), low + span_of(kids[k]));
        }
        let Child::Leaf { page, records, live, .. } = child else { panic!("a leaf") };
        let leaf = w.file.read(page, &mut buf).unwrap().to_vec();
        let mut slots = Vec::new();
        read_leaf::<OutputTree>(&leaf, base, height, records, live, &mut slots).unwrap();
        assert!(read_leaf::<OutputTree>(&leaf, base, height, records - 1, live, &mut Vec::new()).is_err());
        assert!(read_leaf::<OutputTree>(&leaf, base + (1 << height), height, records, live, &mut Vec::new()).is_ok());
        assert!(
            read_leaf::<OutputTree>(&leaf, base, 1, records, live, &mut Vec::new()).is_err(),
            "positions past the leaf"
        );
        let mut again = Vec::new();
        write_leaf::<OutputTree>(&slots, base, &mut again);
        assert_eq!(again, leaf);
        write_node(&children, HEIGHT, &mut again);
        assert_eq!(again, node);

        let root = w.set.to_bytes();
        for bytes in [&node[..], &leaf[..], &root[..]] {
            for _ in 0..crate::test_util::fuzz_params(3000, 0).0 {
                let mut b = bytes.to_vec();
                match rng.next_u64() % 4 {
                    0 => b.truncate(rng.next_u64() as usize % (b.len() + 1)),
                    1 => b.push(rng.next_u64() as u8),
                    _ => {
                        let at = rng.next_u64() as usize % b.len();
                        b[at] = rng.next_u64() as u8;
                    }
                }
                if let Ok(kids) = read_node(&b, HEIGHT) {
                    write_node(&kids, HEIGHT, &mut again);
                    assert_eq!(again, b);
                }
                let mut s = Vec::new();
                if read_leaf::<OutputTree>(&b, base, height, records, live, &mut s).is_ok() {
                    write_leaf::<OutputTree>(&s, base, &mut again);
                    assert_eq!(again, b);
                }
                if let Ok(set) = Outputs::from_bytes(&b) {
                    assert_eq!(set.to_bytes()[..], b[..]);
                }
            }
        }
    }

    impl World {
        /// Sweeps the whole trie once, in steps of `budget` leaves, with
        /// `horizon`; returns how many steps it took.
        fn sweep_round(&mut self, budget: usize, horizon: u32) -> usize {
            let (mut from, mut steps) = (0, 0);
            loop {
                let mut txn = self.file.begin().unwrap();
                let (set, next) = self.set.sweep(&mut txn, from, budget, horizon).unwrap();
                txn.commit(&set.to_bytes()).unwrap();
                assert_eq!((set.hash(), set.count, set.next), (self.set.hash(), self.set.count, self.set.next));
                self.set = set;
                steps += 1;
                if next == 0 {
                    return steps;
                }
                assert!(next > from, "a sweep moves on");
                from = next;
            }
        }

        /// The records kept: every unspent one, and of the spent ones
        /// only such as the model has; returns how many spent are kept.
        fn check_swept(&self, spent_since: u32) -> usize {
            let mut kept = BTreeMap::new();
            self.set.for_each(&self.file, &mut |p, r, live| assert!(kept.insert(p, (*r, live)).is_none())).unwrap();
            let mut dead = 0;
            for (p, v) in &self.model.outputs {
                match kept.get(p) {
                    Some(k) => assert_eq!(k, v, "position {p}"),
                    None => assert!(!v.1, "an unspent output at {p} was dropped"),
                }
                dead += (!v.1 && kept.contains_key(p)) as usize;
            }
            assert!(kept.keys().all(|p| self.model.outputs.contains_key(p)));
            // Nothing spent at `spent_since` or later is dropped.
            for (_, _, spends) in self.history.iter().skip(spent_since.saturating_sub(1) as usize) {
                assert!(spends.iter().all(|p| kept.contains_key(p)), "a record a block may want back was dropped");
            }
            dead
        }
    }

    /// The sweep drops what is dead and old, keeps what a block still to
    /// be undone may want back, changes no hash, and gives the space back;
    /// outputs thinned out end up a few pages.
    #[test]
    fn the_sweep_drops_what_is_dead_and_old() {
        let mut w = World::new();
        let mut rng = Rng::new(0x5ee9);
        w.block(&mut rng, 0, 4000).unwrap();
        // Blocks 2 to 4 spend in the first half of the positions, blocks
        // 5 to 7 in the second: 550 each.
        for k in 0..6u64 {
            let half: Vec<u64> = w.model.live().into_iter().filter(|p| (*p >= 2000) == (k >= 3)).collect();
            let mut picked: Vec<u64> = half.iter().copied().filter(|p| (p * 7 + k) % 3 != 0).take(550).collect();
            picked.sort_unstable();
            assert_eq!(picked.len(), 550);
            w.apply(&picked, &[]).unwrap();
        }
        let before = w.file.space().0;
        assert_eq!(w.check_swept(0), 3300);

        // With the horizon at block 5, what blocks 5 to 7 spent stays.
        let steps = w.sweep_round(40, 5);
        assert!(steps > 2, "{steps} steps");
        let kept = w.check_swept(5);
        assert!((1650..2000).contains(&kept), "{kept} spent records kept");
        assert_eq!(w.set.hash(), w.model.hash());
        // Those three blocks can still be undone, and done again.
        let redo: Vec<Vec<u64>> = w.history[4..].iter().map(|h| h.2.clone()).collect();
        for _ in 0..3 {
            w.undo();
        }
        for spends in &redo {
            w.apply(spends, &[]).unwrap();
        }

        // With the horizon past every block, a leaf keeps its dead only
        // while they are under a quarter of it.
        w.sweep_round(1000, w.tip + 1);
        let kept = w.check_swept(u32::MAX);
        assert!(kept < 700 / 3, "{kept} spent records kept of 3,300");
        let after = w.file.space().0;
        assert!(after * 3 < before, "{before} units before the sweep, {after} after");
        w.reopen();

        // Spent down to a handful, the set is a handful of pages: nodes
        // whose outputs fit one page have become that page.
        while w.set.count > 30 {
            w.block(&mut rng, 200, 0).unwrap();
        }
        w.sweep_round(64, w.tip + 1);
        w.sweep_round(64, w.tip + 1);
        w.check_swept(u32::MAX);
        let (used, _) = w.file.space();
        assert!(used < crate::store::pagefile::HEADER_UNITS + 40, "{used} units for {} outputs", w.set.count);
        w.reopen();
        // And it goes on taking blocks.
        w.block(&mut rng, 10, 500).unwrap();
        w.block(&mut rng, 100, 0).unwrap();
        w.check_swept(u32::MAX);
        assert_eq!(w.set.hash(), w.model.hash());
        // Everything spent and swept: nothing is left in the file.
        while w.set.count > 0 {
            w.block(&mut rng, 300, 0).unwrap();
        }
        w.sweep_round(64, w.tip + 1);
        assert_eq!(w.set.root, Child::Empty);
        assert_eq!(w.file.space().0, crate::store::pagefile::HEADER_UNITS);
    }

    /// A pass split among threads gives what one thread gives: the same
    /// root and count, and for a block that spends what is not there,
    /// the same fault, the first in position order.
    #[test]
    fn a_pass_on_many_threads_is_the_same() {
        let mut w = World::new();
        let mut rng = Rng::new(0x7417);
        w.block(&mut rng, 0, 6000).unwrap();
        w.block(&mut rng, 1500, 0).unwrap();
        let live = w.model.live();
        let spends: Vec<u64> = live.iter().copied().step_by(2).collect();
        let records: Vec<Record> = (0..700).map(|_| record(&mut rng, 3)).collect();
        assert!(spends.len() > 2000);
        let run = |spends: &[u64], threads: usize| {
            let txn = w.file.begin().unwrap();
            let edits = Edits { flips: spends, run: &records, run_from: w.set.next as u128, ..Edits::none() };
            let done = trie::update_on::<OutputTree, _>(&txn, w.set.root, 3, edits, threads);
            done.map(|(root, count)| (root.part(), count))
        };
        let one = run(&spends, 1).unwrap();
        for threads in [2, 3, 8, 64] {
            assert_eq!(run(&spends, threads).unwrap(), one, "{threads} threads");
        }
        assert_eq!(one.1, 700 - spends.len() as i64);
        // Two spends of nothing, far apart: the earlier is the fault.
        let dead: Vec<u64> = w.history[1].2.clone();
        let mut bad = spends.clone();
        bad.extend([dead[3], dead[dead.len() - 2]]);
        bad.sort_unstable();
        for threads in [1, 2, 8, 64] {
            assert_eq!(run(&bad, threads).err(), Some(Error::NoSuchOutput(dead[3])), "{threads} threads");
        }
        // Nothing was committed, and nothing is held.
        assert_eq!(w.file.space().0, {
            w.reopen();
            w.file.space().0
        });
    }

    /// Hashed eight at a time or one by one, a record's leaf is the same.
    #[test]
    fn leaves_hashed_together_are_the_same() {
        let mut rng = Rng::new(0xba7c);
        for n in [0usize, 1, 7, 8, 9, 16, 31, 64] {
            let slots: Vec<Slot<Record>> = (0..n)
                .map(|i| Slot { key: 3 * i as u128, record: record(&mut rng, i as u32), live: i % 5 != 2 })
                .collect();
            let mut out = [(0u128, Part { hash: EMPTY, single: false }); LEAF_RECORDS];
            let got = OutputTree::leaves(&slots, &mut out);
            let want: Vec<(u128, Part)> = slots
                .iter()
                .filter(|s| s.live)
                .map(|s| (s.key, Part { hash: s.record.leaf(), single: true }))
                .collect();
            assert_eq!(&out[..got], &want[..], "{n} records");
        }
    }

    /// What a worst-case block costs on a real file: 25,000 outputs
    /// spent, picked evenly among those unspent, and 25,000 made, in a
    /// set built by blocks like it.
    /// `cargo test --release --lib store::outputs::tests::cost -- --ignored --nocapture`
    /// (`TABMINER_STORE_OUTPUTS` sets the outputs made in all, 4,000,000
    /// unless given.)
    #[test]
    #[ignore = "slow: builds a set of millions of outputs on disk"]
    fn cost() {
        use std::sync::atomic::Ordering::Relaxed;
        let total: u64 = std::env::var("TABMINER_STORE_OUTPUTS").ok().and_then(|s| s.parse().ok()).unwrap_or(4_000_000);
        let dir = crate::store::testing::temp_dir("outputs-cost");
        let backend = crate::store::testing::Counting::open(&dir.join("state"));
        let file = PageFile::create(backend).unwrap();
        let mut rng = Rng::new(0xc057);
        let mut set = Outputs::EMPTY;
        // The unspent positions, to pick spends from evenly.
        let mut live: Vec<u64> = Vec::new();
        const BLOCK: usize = 25_000;
        let mut height = 0u32;
        let mut block = |set: &mut Outputs, live: &mut Vec<u64>, spends: usize, rng: &mut Rng| {
            height += 1;
            let mut picked: Vec<u64> = (0..spends.min(live.len()))
                .map(|_| {
                    let i = rng.next_u64() as usize % live.len();
                    live.swap_remove(i)
                })
                .collect();
            picked.sort_unstable();
            let records: Vec<Record> = (0..BLOCK).map(|_| record(rng, height)).collect();
            let before = (
                file.backend().reads.load(Relaxed),
                file.backend().written.load(Relaxed),
                file.backend().read_bytes.load(Relaxed),
                file.backend().writes.load(Relaxed),
            );
            let t = std::time::Instant::now();
            let mut txn = file.begin().unwrap();
            let next = set.apply(&mut txn, height, &picked, &records).unwrap();
            let applied = t.elapsed();
            txn.commit(&next.to_bytes()).unwrap();
            let committed = t.elapsed();
            live.extend(set.next..next.next);
            *set = next;
            let b = file.backend();
            (
                picked.len(),
                applied,
                committed,
                b.reads.load(Relaxed) - before.0,
                b.read_bytes.load(Relaxed) - before.2,
                b.writes.load(Relaxed) - before.3,
                b.written.load(Relaxed) - before.1,
            )
        };
        // Built with seven of every eight outputs spent on the way, so
        // that the set is spread thin over its positions.
        let t = std::time::Instant::now();
        while set.next < total {
            block(&mut set, &mut live, BLOCK * 7 / 8, &mut rng);
        }
        let (used, end) = file.space();
        println!(
            "built in {:.1?}: {} unspent of {} positions; file {} MB, {} MB in use ({} bytes an unspent output)",
            t.elapsed(),
            set.count,
            set.next,
            (end * 512) >> 20,
            (used * 512) >> 20,
            used * 512 / set.count
        );
        for (name, spends) in
            [("25,000 spends and 25,000 new", BLOCK), ("the same again", BLOCK), ("25,000 new only", 0)]
        {
            let (n, applied, committed, reads, read_bytes, writes, written) =
                block(&mut set, &mut live, spends, &mut rng);
            println!(
                "{name}: {n} spent | applied in {applied:.1?}, durable in {committed:.1?} | read {reads} pages, {} MB | wrote {} MB in {writes} writes",
                read_bytes >> 20,
                written >> 20
            );
        }
        // Opening: every node read to mark what is in use.
        let path = dir.join("state");
        let seq = file.root().seq;
        drop(file);
        let t = std::time::Instant::now();
        let file = PageFile::open(crate::store::backend::FileBackend::open(&path).unwrap()).unwrap();
        assert_eq!(file.root().seq, seq);
        let again = Outputs::from_bytes(file.root().payload()).unwrap();
        again.mark(&file).unwrap();
        file.seal();
        println!("opened and marked in {:.1?}; map of free space {} KB", t.elapsed(), file.space().1 / 8 / 1024);
        assert_eq!(again, set);
        std::fs::remove_dir_all(dir).unwrap();
    }
}
