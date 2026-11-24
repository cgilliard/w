//! The names: the trie of [`super::trie`] over the keys of names, which
//! is their Merkle tree.
//!
//! A name's key is the first 128 bits of its hash
//! ([`crate::name::key_of`]), and its record holds the name, its owner
//! and what the owner keeps under it. The names' tree is the registry's
//! ([`crate::registry`]): a binary tree of 128 levels, a name's leaf
//! (the hash of its name's hash and its record's) at its key, nothing
//! elsewhere, every node the hash of its two children. An empty subtree
//! of each height has one hash, so the root follows from the leaves
//! there are, and a key's path is the same 128 siblings whether a name
//! is there or not.
//!
//! Names are never spent: a record is registered, and then replaced as
//! its owner updates it. Undoing a block puts back the records it
//! replaced and removes those it registered.

use std::io;

use super::backend::Backend;
use super::pagefile::{PageFile, ReadPages, Txn};
use super::trie::{self, CHILD_BYTES, Child, Edits, Fault, LEAF_RECORDS, Part, Step, Tree};
use crate::error::Error;
use crate::hash::{Digest, EMPTY};
use crate::name::{KEY_BITS, Key, Record};
pub use crate::name::{empty_root, leaf_hash, leaf_of};
use crate::registry;

/// The level of the subtrees the names are handed to another node in,
/// when it takes the state from this one: by the first bits of a key.
pub const PART_LEVEL: u32 = KEY_BITS as u32 - 12;

fn corrupt(what: &'static str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, what)
}

/// The hash of an empty subtree of `height` levels.
fn empty(height: u32) -> &'static Digest {
    &registry::empty_roots()[height as usize]
}

/// The hash of a subtree of the names' tree, of `level` levels, with
/// no names.
pub fn empty_at(level: u32) -> Digest {
    *empty(level)
}

/// One level up: the nonempty parts of `level` (ascending) are
/// replaced, in place, by their parents at the level above, a part with
/// no sibling paired with the empty subtree's hash. Returns how many
/// parents there are.
fn level_up(level: u32, parts: &mut [(u128, Part)]) -> usize {
    let (mut r, mut w) = (0, 0);
    while r < parts.len() {
        let (i, part) = parts[r];
        let (left, right) = if i & 1 == 1 {
            (*empty(level), part.hash)
        } else if parts.get(r + 1).is_some_and(|next| next.0 == i + 1) {
            r += 1;
            (part.hash, parts[r].1.hash)
        } else {
            (part.hash, *empty(level))
        };
        r += 1;
        parts[w] = (i >> 1, Part { hash: registry::node(&left, &right), single: false });
        w += 1;
    }
    w
}

/// The root of the subtree at `top` from its nonempty parts at `level`
/// (ascending, all under it); with `path`, also the sibling at each
/// level from `level` to `top - 1` of the part of that index at
/// `level`, which need not be there. The slice is scratch.
fn root_with_path(level: u32, top: u32, parts: &mut [(u128, Part)], mut path: Option<(u128, &mut [Digest])>) -> Digest {
    let mut n = parts.len();
    for l in level..top {
        if let Some((index, siblings)) = &mut path {
            let want = *index ^ 1;
            siblings[(l - level) as usize] = match parts[..n].binary_search_by_key(&want, |x| x.0) {
                Ok(i) => parts[i].1.hash,
                Err(_) => *empty(l),
            };
            *index >>= 1;
        }
        n = level_up(l, &mut parts[..n]);
    }
    if n == 0 { *empty(top) } else { parts[0].1.hash }
}

/// The part of the node at level `top` from its nonempty parts at
/// `level`; `None` if there are none.
fn part_at(level: u32, top: u32, parts: &[(u128, Part)]) -> Option<Part> {
    let mut scratch = parts.to_vec();
    (!parts.is_empty()).then(|| Part { hash: root_with_path(level, top, &mut scratch, None), single: false })
}

/// The names' tree.
pub struct NameTree;

impl Tree for NameTree {
    const HEIGHT: u32 = KEY_BITS as u32;
    type Key = Key;
    type Record = Record;

    fn record_len(r: &Record) -> usize {
        r.size()
    }

    fn write_record(r: &Record, out: &mut Vec<u8>) {
        let at = out.len();
        out.resize(at + r.size(), 0);
        r.write_bytes(&mut out[at..]);
    }

    fn read_record(b: &[u8]) -> io::Result<(Record, &[u8])> {
        Record::read(b).ok_or_else(|| corrupt("a name's record is not one"))
    }

    fn leaf(_: u128, r: &Record) -> Digest {
        leaf_of(r)
    }

    /// The registry's step: a part with no sibling is paired with the
    /// empty subtree's hash.
    fn lift(level: u32, parts: &mut [(u128, Part)]) -> usize {
        level_up(level, parts)
    }

    fn refuse(_: u128, fault: Fault) -> Error {
        match fault {
            Fault::Present => Error::NameTaken,
            Fault::Absent => Error::NoSuchName,
            _ => corrupt("a change to the names cannot be made").into(),
        }
    }
}

/// The root of the names' tree whose nonempty subtrees at `level` have
/// the parts `parts` (ascending by index): what a node that is given the
/// names in parts checks against the names' root.
pub fn parts_root(level: u32, parts: &[(u32, Part)]) -> Digest {
    let parts: Vec<(u128, Part)> = parts.iter().map(|(i, p)| (*i as u128, *p)).collect();
    part_at(level, NameTree::HEIGHT, &parts).map_or_else(empty_root, |p| p.hash)
}

/// The part of the subtree at `level` whose names are `records`
/// (ascending by key): what a part received is checked against. `None`
/// if there are none.
pub fn part_of(level: u32, records: &[Record]) -> Option<Part> {
    let leaves: Vec<(u128, Part)> =
        records.iter().map(|r| (r.key(), Part { hash: leaf_of(r), single: true })).collect();
    part_at(0, level, &leaves)
}

/// A key's path: the leaf at the key (empty if no name is registered
/// there) and the sibling at each level, the lowest first: what
/// [`crate::registry::path_root`] takes, and a proof's rows.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NameProof {
    pub leaf: Digest,
    pub siblings: Vec<Digest>,
}

impl NameProof {
    /// The root the proof implies for `key`'s path.
    pub fn root(&self, key: Key) -> Digest {
        registry::path_root(&self.leaf, key, &self.siblings)
    }

    /// Whether the proof shows the leaf `leaf` ([`leaf_of`]) at `key`
    /// under `root`.
    pub fn verify_member(&self, root: &Digest, key: Key, leaf: &Digest) -> bool {
        self.leaf == *leaf && *leaf != EMPTY && self.siblings.len() == KEY_BITS && self.root(key) == *root
    }

    /// Whether the proof shows `key` not registered under `root`.
    pub fn verify_absent(&self, root: &Digest, key: Key) -> bool {
        self.leaf == EMPTY && self.siblings.len() == KEY_BITS && self.root(key) == *root
    }
}

/// The names, as a root record holds them: the root of the trie and how
/// many there are.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Names {
    pub root: Child,
    pub count: u64,
}

impl Names {
    /// No name yet.
    pub const EMPTY: Names = Names { root: Child::Empty, count: 0 };
    /// Serialized size.
    pub const BYTES: usize = CHILD_BYTES + 8;

    /// The root of the names' tree.
    pub fn hash(&self) -> Digest {
        self.root.part().map_or_else(empty_root, |p| p.hash)
    }

    pub fn to_bytes(&self) -> [u8; Self::BYTES] {
        let mut v = Vec::with_capacity(Self::BYTES);
        self.root.write(&mut v);
        v.resize(CHILD_BYTES, 0);
        v.extend_from_slice(&self.count.to_le_bytes());
        v.try_into().unwrap()
    }

    pub fn from_bytes(b: &[u8]) -> io::Result<Names> {
        let bad = || corrupt("the names' root is not one");
        if b.len() != Self::BYTES {
            return Err(bad());
        }
        let (root, rest) = Child::read(&b[..CHILD_BYTES])?;
        if rest.iter().any(|x| *x != 0) {
            return Err(bad());
        }
        Ok(Names { root, count: u64::from_le_bytes(b[CHILD_BYTES..].try_into().unwrap()) })
    }

    fn pass<B: Backend>(&self, txn: &mut Txn<'_, B>, edits: Edits<'_, NameTree>) -> Result<Names, Error> {
        let (root, change) = trie::update(txn, self.root, 0, edits)?;
        let count = self.count.checked_add_signed(change).ok_or_else(|| corrupt("the count of names is wrong"))?;
        Ok(Names { root, count })
    }

    /// The names after `puts`, ascending by key: each a record put at its
    /// key, with `true` in place of the one registered there
    /// ([`Error::NoSuchName`] if there is none), with `false` as a new
    /// registration ([`Error::NameTaken`] if the key is taken).
    pub fn apply<B: Backend>(&self, txn: &mut Txn<'_, B>, puts: &[(Key, Record, bool)]) -> Result<Names, Error> {
        debug_assert!(puts.windows(2).all(|w| w[0].0 < w[1].0), "keys ascend");
        debug_assert!(puts.iter().all(|p| p.0 == p.1.key()), "a record is put at its name's key");
        self.pass(txn, Edits { puts, ..Edits::none() })
    }

    /// [`Names::apply`], which also returns the part of every subtree at
    /// `level` the puts change, as it was before them (`None` where there
    /// was no name).
    #[allow(clippy::type_complexity)]
    pub fn apply_keeping<B: Backend>(
        &self,
        txn: &mut Txn<'_, B>,
        puts: &[(Key, Record, bool)],
        level: u32,
    ) -> Result<(Names, Vec<(u32, Option<Part>)>), Error> {
        debug_assert!(puts.windows(2).all(|w| w[0].0 < w[1].0), "keys ascend");
        let edits: Edits<'_, NameTree> = Edits { puts, ..Edits::none() };
        let (root, change, before, _) = trie::update_keeping(txn, self.root, 0, edits, level)?;
        let count = self.count.checked_add_signed(change).ok_or_else(|| corrupt("the count of names is wrong"))?;
        Ok((Names { root, count }, before.into_iter().map(|(i, part)| (i as u32, part)).collect()))
    }

    /// The part of every nonempty subtree at `level`, ascending by index.
    pub fn parts(&self, pages: &impl ReadPages, level: u32) -> io::Result<Vec<(u32, Part)>> {
        let mut out = Vec::new();
        trie::parts_at::<NameTree>(pages, self.root, level, &mut |index, part| out.push((index as u32, part)))?;
        Ok(out)
    }

    /// Every name's record in the subtree of index `index` at `level`,
    /// in key order.
    pub fn part(&self, pages: &impl ReadPages, level: u32, index: u32) -> io::Result<Vec<Record>> {
        let mut out = Vec::new();
        trie::for_each_in::<NameTree>(pages, self.root, level, index as u128, &mut |_, record, _| out.push(*record))?;
        Ok(out)
    }

    /// The names before a block: the records it replaced are put back
    /// (`restore`, ascending) and those it registered are removed
    /// (`remove`, ascending).
    pub fn undo<B: Backend>(
        &self,
        txn: &mut Txn<'_, B>,
        restore: &[(Key, Record, bool)],
        remove: &[Key],
    ) -> Result<Names, Error> {
        debug_assert!(restore.iter().all(|p| p.2), "what is put back replaces");
        self.pass(txn, Edits { puts: restore, removes: remove, ..Edits::none() })
    }

    /// The names with those at `removes` taken out and `puts` put in
    /// (both ascending, each put where no name is left): how a part of
    /// a state being received is put in place of an older one.
    pub fn exchange<B: Backend>(
        &self,
        txn: &mut Txn<'_, B>,
        removes: &[Key],
        puts: &[(Key, Record, bool)],
    ) -> Result<Names, Error> {
        debug_assert!(puts.windows(2).all(|w| w[0].0 < w[1].0) && puts.iter().all(|p| !p.2 && p.0 == p.1.key()));
        self.pass(txn, Edits { removes, puts, ..Edits::none() })
    }

    /// Frees every page of the names.
    pub fn free<B: Backend>(&self, txn: &Txn<'_, B>) -> io::Result<()> {
        trie::free::<NameTree, B>(txn, self.root)
    }

    /// The record registered at `key`, if any.
    pub fn get(&self, pages: &impl ReadPages, key: Key) -> io::Result<Option<Record>> {
        Ok(trie::get::<NameTree>(pages, self.root, key)?.map(|(record, _)| record))
    }

    /// The path of `key`: its leaf (empty if no name is registered
    /// there) and the sibling at each level up to the root.
    pub fn prove(&self, pages: &impl ReadPages, key: Key) -> io::Result<NameProof> {
        let mut path = vec![EMPTY; KEY_BITS];
        let mut leaf = EMPTY;
        trie::walk_to::<NameTree>(pages, self.root, key, &mut |step| match step {
            // Nothing below: the siblings are those of an empty tree.
            Step::Empty { height, .. } => {
                for (l, s) in path[..height as usize].iter_mut().enumerate() {
                    *s = *empty(l as u32);
                }
            }
            // The siblings from the level of the child the key is under
            // up to the node's own: below that they are the child's.
            Step::Node { height, base, children } => {
                let low = trie::below(height);
                let levels = trie::levels::<NameTree>(children, height, base);
                let (_, span) = trie::group_of(children, height, ((key - base) >> low) as usize);
                for up in span..height - low {
                    let level = low + up;
                    let sibling = (key >> level) ^ 1;
                    path[level as usize] = levels.find(up, sibling).map_or(*empty(level), |p| p.hash);
                }
            }
            Step::Leaf { height, slots, .. } => {
                let none = (0u128, Part { hash: EMPTY, single: true });
                let mut parts = [none; LEAF_RECORDS];
                let mut n = 0;
                for s in slots.iter().filter(|s| s.live) {
                    parts[n] = (s.key, Part { hash: leaf_of(&s.record), single: true });
                    if s.key == key {
                        leaf = parts[n].1.hash;
                    }
                    n += 1;
                }
                root_with_path(0, height, &mut parts[..n], Some((key, &mut path[..height as usize])));
            }
        })?;
        Ok(NameProof { leaf, siblings: path })
    }

    /// Marks every page of the names in `file`'s map of free space.
    pub fn mark<B: Backend>(&self, file: &PageFile<B>) -> io::Result<()> {
        trie::mark::<NameTree, B>(file, self.root)
    }

    /// Calls `f` with every name's key and record, in key order.
    pub fn for_each(&self, pages: &impl ReadPages, f: &mut dyn FnMut(Key, &Record)) -> io::Result<()> {
        trie::for_each::<NameTree>(pages, self.root, &mut |key, record, _| f(key, record))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::store::testing::{Lost, MemBackend};
    use crate::test_util::Rng;
    use std::collections::BTreeMap;

    fn record(rng: &mut Rng) -> Record {
        // (Long enough that no two are the same name.)
        let len = 12 + rng.next_u64() as usize % (crate::name::NAME_MAX - 11);
        let name: Vec<u8> = (0..len).map(|_| crate::name::CHARSET[rng.next_u64() as usize % 37]).collect();
        let d = |rng: &mut Rng| -> Digest { rng.digest() };
        Record::new(&name, d(rng), d(rng), d(rng)).unwrap()
    }

    /// The root by the definition: the subtree of `height` levels over
    /// `leaves` is nothing's root if there are none, the leaf at the
    /// bottom, and the node over its two halves above.
    fn define(leaves: &[(Key, Digest)], height: u32) -> Digest {
        match leaves {
            [] => *empty(height),
            [(_, leaf)] if height == 0 => *leaf,
            _ => {
                let mid = leaves.partition_point(|(k, _)| k >> (height - 1) & 1 == 0);
                registry::node(&define(&leaves[..mid], height - 1), &define(&leaves[mid..], height - 1))
            }
        }
    }

    struct World {
        file: PageFile<MemBackend>,
        names: Names,
        /// Keys are whatever a test puts records under: not always their
        /// names' own, so that keys can be made to share prefixes.
        model: BTreeMap<Key, Record>,
    }

    impl World {
        fn new() -> World {
            World { file: PageFile::create(MemBackend::new()).unwrap(), names: Names::EMPTY, model: BTreeMap::new() }
        }

        fn root(&self) -> Digest {
            if self.model.is_empty() {
                return empty_root();
            }
            let leaves: Vec<(Key, Digest)> = self.model.iter().map(|(k, r)| (*k, leaf_of(r))).collect();
            define(&leaves, KEY_BITS as u32)
        }

        /// Puts `puts` (sorted here) in one transaction.
        fn put(&mut self, mut puts: Vec<(Key, Record, bool)>) -> Result<(), Error> {
            puts.sort_by_key(|p| p.0);
            let mut txn = self.file.begin()?;
            let names = self.names.pass(&mut txn, Edits { puts: &puts, ..Edits::none() })?;
            txn.commit(&names.to_bytes())?;
            self.names = names;
            self.model.extend(puts.iter().map(|p| (p.0, p.1)));
            Ok(())
        }

        fn check(&self, rng: &mut Rng) {
            let root = self.root();
            assert_eq!(self.names.hash(), root);
            assert_eq!(self.names.count as usize, self.model.len());
            let mut seen = Vec::new();
            self.names.for_each(&self.file, &mut |k, r| seen.push((k, *r))).unwrap();
            assert!(seen.iter().copied().eq(self.model.iter().map(|(k, r)| (*k, *r))));
            // Every name's path leads to the root, and shows it there.
            for (k, r) in self.model.iter().step_by(1 + self.model.len() / 40) {
                assert_eq!(self.names.get(&self.file, *k).unwrap(), Some(*r));
                let proof = self.names.prove(&self.file, *k).unwrap();
                assert!(proof.verify_member(&root, *k, &leaf_of(r)), "key {k:032x}");
                assert!(!proof.verify_absent(&root, *k));
                let mut other = leaf_of(r);
                other[0] ^= 1;
                assert!(!proof.verify_member(&root, *k, &other));
            }
            // Keys not registered: any, and neighbours of registered ones.
            let near: Vec<Key> = self.model.keys().take(8).flat_map(|k| [k ^ 1, k ^ 1 << 60, k ^ 1 << 127]).collect();
            for k in (0..20).map(|_| (rng.next_u64() as u128) << 64 | rng.next_u64() as u128).chain(near) {
                if self.model.contains_key(&k) {
                    continue;
                }
                assert_eq!(self.names.get(&self.file, k).unwrap(), None);
                let proof = self.names.prove(&self.file, k).unwrap();
                assert!(proof.verify_absent(&root, k), "key {k:032x}: {proof:?}");
            }
        }

        fn reopen(&mut self) {
            let file = PageFile::open(MemBackend::from_image(self.file.backend().image(Lost::All))).unwrap();
            let names =
                if file.root().seq == 0 { Names::EMPTY } else { Names::from_bytes(file.root().payload()).unwrap() };
            assert_eq!(names, self.names);
            names.mark(&file).unwrap();
            file.seal();
            assert_eq!(file.space().0, self.file.space().0);
            self.file = file;
        }
    }

    #[test]
    fn no_name_one_name_two_names() {
        let mut w = World::new();
        let mut rng = Rng::new(0x4a3e);
        assert_eq!(w.names.hash(), empty_root());
        w.check(&mut rng);
        assert_eq!(Names::from_bytes(&Names::EMPTY.to_bytes()).unwrap(), Names::EMPTY);
        // One name: the root is its leaf's path through nothing, which is
        // the registry's of the same record.
        let a = record(&mut rng);
        w.put(vec![(a.key(), a, false)]).unwrap();
        let siblings = registry::empty_roots()[..KEY_BITS].to_vec();
        assert_eq!(w.names.hash(), registry::path_root(&leaf_of(&a), a.key(), &siblings));
        assert_eq!(w.names.prove(&w.file, a.key()).unwrap().siblings, siblings);
        let mut model = registry::Names::default();
        model.set(a.rule());
        assert_eq!((w.names.hash(), leaf_of(&a)), (model.root(), a.rule().leaf()));
        w.check(&mut rng);
        // Two: the registry's root, and its paths.
        let b = record(&mut rng);
        w.put(vec![(b.key(), b, false)]).unwrap();
        model.set(b.rule());
        assert_eq!(w.names.hash(), model.root());
        assert_eq!(w.names.prove(&w.file, a.key()).unwrap().siblings, model.path(a.key()));
        w.check(&mut rng);
        w.reopen();
    }

    /// Names by the hundred, registered a few at a time and updated: the
    /// root is the definition's throughout, and every path leads to it.
    #[test]
    fn names_against_the_definition() {
        let mut w = World::new();
        let mut rng = Rng::new(0x4a3e5);
        for round in 0..12 {
            let mut puts = Vec::new();
            for _ in 0..[1, 3, 70, 200][round % 4] {
                let r = record(&mut rng);
                if !w.model.contains_key(&r.key()) && !puts.iter().any(|p: &(Key, Record, bool)| p.0 == r.key()) {
                    puts.push((r.key(), r, false));
                }
            }
            // Some of the names there are given new records.
            for k in w.model.keys().step_by(7).copied().collect::<Vec<_>>() {
                let r = Record { name: w.model[&k].name, ..record(&mut rng) };
                puts.push((k, r, true));
            }
            w.put(puts).unwrap();
            w.check(&mut rng);
            if round % 3 == 2 {
                w.reopen();
            }
        }
        assert!(w.model.len() > 700);
    }

    /// Keys that share long prefixes, down to all but the last bit: the
    /// tree goes as deep as they part, with empty halves on the way.
    #[test]
    fn keys_that_share_prefixes() {
        let mut w = World::new();
        let mut rng = Rng::new(0x9ef1);
        let top: Key = 0x5a5a5a << 96;
        let mut puts = Vec::new();
        // Pairs that part at bit 119, 118, 100, 64, 37 and 1 from the
        // top, a run of neighbours, and both ends of the key space.
        for (i, low) in [1u128, 2, 3, 1 << 19, 1 << 55, 1 << 82, 1 << 118].into_iter().enumerate() {
            puts.push((top + ((i as u128) << 90) + low, record(&mut rng), false));
            puts.push((top + ((i as u128) << 90), record(&mut rng), false));
        }
        puts.extend((0..90u128).map(|i| (7 << 100 | i, record(&mut rng), false)));
        puts.push((0, record(&mut rng), false));
        puts.push((Key::MAX, record(&mut rng), false));
        puts.sort_by_key(|p| p.0);
        puts.dedup_by_key(|p| p.0);
        // Registered in three goes, so that leaves split where keys are dense.
        for part in puts.chunks(40) {
            w.put(part.to_vec()).unwrap();
            w.check(&mut rng);
        }
        w.reopen();
        // Two keys that differ in the last bit only: each the other's
        // first sibling.
        let (a, b) = (top, top + 1);
        assert_eq!(w.names.prove(&w.file, a).unwrap().siblings[0], leaf_of(&w.model[&b]));
        assert_eq!(w.names.prove(&w.file, b).unwrap().siblings[0], leaf_of(&w.model[&a]));
    }

    /// A key taken cannot be registered, a key not registered cannot be
    /// updated, and a refused transaction leaves the names as they were;
    /// undoing a block puts back what it replaced and removes what it
    /// registered.
    #[test]
    fn refusals_and_undo() {
        let mut w = World::new();
        let mut rng = Rng::new(0x0d0);
        let first: Vec<(Key, Record, bool)> = (0..150).map(|_| record(&mut rng)).map(|r| (r.key(), r, false)).collect();
        w.put(first.clone()).unwrap();
        let (root, used) = (w.names.hash(), w.file.space().0);
        let taken = first[20];
        let fresh = record(&mut rng);
        let refused = |puts: Vec<(Key, Record, bool)>, want: Error| {
            let mut sorted = puts;
            sorted.sort_by_key(|p| p.0);
            let mut txn = w.file.begin().unwrap();
            assert_eq!(w.names.pass(&mut txn, Edits { puts: &sorted, ..Edits::none() }).err(), Some(want));
            drop(txn);
            assert_eq!((w.names.hash(), w.file.space().0), (root, used));
        };
        refused(vec![(taken.0, record(&mut rng), false)], Error::NameTaken);
        refused(vec![(fresh.key(), fresh, true)], Error::NoSuchName);
        refused(vec![(fresh.key(), fresh, false), (taken.0, taken.1, false)], Error::NameTaken);

        // A block that registers 30 and replaces 30, then undone.
        let before = w.model.clone();
        let registered: Vec<(Key, Record, bool)> =
            (0..30).map(|_| record(&mut rng)).map(|r| (r.key(), r, false)).collect();
        let replaced: Vec<(Key, Record, bool)> = first.iter().step_by(5).map(|p| (p.0, p.1, true)).collect();
        let mut block = registered.clone();
        block.extend(replaced.iter().map(|p| (p.0, Record { name: p.1.name, ..record(&mut rng) }, true)));
        w.put(block).unwrap();
        w.check(&mut rng);
        assert_ne!(w.names.hash(), root);
        let mut restore = replaced.clone();
        restore.sort_by_key(|p| p.0);
        let mut remove: Vec<Key> = registered.iter().map(|p| p.0).collect();
        remove.sort_unstable();
        let mut txn = w.file.begin().unwrap();
        w.names = w.names.undo(&mut txn, &restore, &remove).unwrap();
        txn.commit(&w.names.to_bytes()).unwrap();
        w.model = before;
        assert_eq!((w.names.hash(), w.names.count), (root, 150));
        w.check(&mut rng);
        w.reopen();
        // Everything removed: no page is left.
        let all: Vec<Key> = w.model.keys().copied().collect();
        let mut txn = w.file.begin().unwrap();
        w.names = w.names.undo(&mut txn, &[], &all).unwrap();
        txn.commit(&w.names.to_bytes()).unwrap();
        assert_eq!(w.names, Names::EMPTY);
        assert_eq!(w.file.space().0, crate::store::pagefile::HEADER_UNITS);
    }
}
