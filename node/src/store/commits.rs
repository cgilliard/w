//! The commits waiting to be revealed: which outputs they are.
//!
//! A name is registered in two steps. A commit, the hash of the name
//! with a salt and its owner, goes into a block and is an output like
//! any other: it takes the next position, and its leaf, as any
//! output's, is of the height of its block. Blocks
//! later a reveal spends it and registers the name, or, if none came in
//! time, a sweep spends it and registers nothing.
//!
//! The output's record does not say that it is a commit: its
//! commitment is the commit's hash, and its amount nothing. This is the
//! table that
//! does: by position, the commit's hash and height; by the hash, the
//! position. A wallet finds its commit by it, and a miner the commits
//! that are past their time, to sweep.
//!
//! # Not the state
//!
//! No root commits to this table, and no rule of the chain needs it: a
//! block's proof shows that what its reveals and sweeps spend are
//! commits, of the right age. So the table is an index, kept with the
//! state and changed with it in one step, and a node whose table lacks
//! a commit (one that took its state from a node that withheld it) still
//! follows the chain: a block that spends a commit the table has not is
//! applied all the same. What an entry says is checked where it comes
//! from another node: the leaf of its hash and the output's height is
//! the output's commitment, or it is not that output's commit.

use std::io;

use super::backend::Backend;
use super::blocks::lift_flat;
use super::pagefile::{PageFile, ReadPages, Txn};
use super::sparse::EMPTY;
use super::trie::{self, Child, Edits, FLAT_BYTES, Fault, Part, Tree};
use crate::error::Error;
use crate::hash::Digest;
use crate::hash::{digest_from_bytes, digest_to_bytes};
use crate::name::key_of;

fn corrupt(what: &'static str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, what)
}

/// A commit: its hash and the height of the block that made it.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Commit {
    pub hash: Digest,
    pub height: u32,
}

impl Commit {
    /// Serialized size.
    pub const BYTES: usize = 36;

    pub fn put(&self, out: &mut Vec<u8>) {
        out.extend_from_slice(&digest_to_bytes(&self.hash));
        out.extend_from_slice(&self.height.to_le_bytes());
    }

    pub fn get(b: &[u8]) -> Option<Commit> {
        let b: &[u8; Self::BYTES] = b.try_into().ok()?;
        Some(Commit { hash: digest_from_bytes(&b[..32])?, height: u32::from_le_bytes(b[32..].try_into().unwrap()) })
    }
}

struct ByPosition;

impl Tree for ByPosition {
    const HEIGHT: u32 = super::outputs::HEIGHT;
    type Key = u64;
    type Record = Commit;

    fn record_len(_: &Commit) -> usize {
        Commit::BYTES
    }

    fn write_record(r: &Commit, out: &mut Vec<u8>) {
        r.put(out)
    }

    fn read_record(b: &[u8]) -> io::Result<(Commit, &[u8])> {
        let bad = || corrupt("a commit is not one");
        let (r, rest) = b.split_at_checked(Commit::BYTES).ok_or_else(bad)?;
        Ok((Commit::get(r).ok_or_else(bad)?, rest))
    }

    fn leaf(_: u128, _: &Commit) -> Digest {
        EMPTY
    }

    fn lift(_: u32, parts: &mut [(u128, Part)]) -> usize {
        lift_flat(parts)
    }

    fn refuse(_: u128, _: Fault) -> Error {
        corrupt("a change to the commits cannot be made").into()
    }
}

/// By the first bits of a commit's hash and then its position: the
/// hash, to tell it from another with the same bits, and the position.
/// A commit made more than once is as many entries, one after another,
/// and each is put and taken out by itself.
struct ByHash;

/// Bits of a position: no output is at one so high
/// ([`crate::output::OUTPUT_CAPACITY`]).
const POSITION_BITS: u32 = 41;
const _: () = assert!(crate::output::OUTPUT_CAPACITY <= 1 << POSITION_BITS);

/// Where the commit of `hash` at `position` is by its hash.
fn place(hash: &Digest, position: u64) -> u128 {
    key_of(hash) >> POSITION_BITS << POSITION_BITS | position as u128
}

impl Tree for ByHash {
    const HEIGHT: u32 = 128;
    type Key = u128;
    type Record = (Digest, u64);

    fn record_len(_: &(Digest, u64)) -> usize {
        40
    }

    fn write_record(r: &(Digest, u64), out: &mut Vec<u8>) {
        out.extend_from_slice(&digest_to_bytes(&r.0));
        out.extend_from_slice(&r.1.to_le_bytes());
    }

    fn read_record(b: &[u8]) -> io::Result<((Digest, u64), &[u8])> {
        let bad = || corrupt("a commit's place is not one");
        let (r, rest) = b.split_at_checked(40).ok_or_else(bad)?;
        Ok(((digest_from_bytes(&r[..32]).ok_or_else(bad)?, u64::from_le_bytes(r[32..].try_into().unwrap())), rest))
    }

    fn leaf(_: u128, _: &(Digest, u64)) -> Digest {
        EMPTY
    }

    fn lift(_: u32, parts: &mut [(u128, Part)]) -> usize {
        lift_flat(parts)
    }

    fn refuse(_: u128, _: Fault) -> Error {
        corrupt("a change to the commits cannot be made").into()
    }
}

/// The commits, as a root record holds them.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Commits {
    by_position: Child,
    by_hash: Child,
    /// How many there are.
    pub count: u64,
}

impl Commits {
    /// No commit.
    pub const EMPTY: Commits = Commits { by_position: Child::Empty, by_hash: Child::Empty, count: 0 };
    /// Serialized size.
    pub const BYTES: usize = 2 * FLAT_BYTES + 8;

    pub fn to_bytes(&self) -> [u8; Self::BYTES] {
        let mut out = Vec::with_capacity(Self::BYTES);
        trie::write_flat(&self.by_position, &mut out);
        trie::write_flat(&self.by_hash, &mut out);
        out.extend_from_slice(&self.count.to_le_bytes());
        out.try_into().unwrap()
    }

    pub fn from_bytes(b: &[u8]) -> io::Result<Commits> {
        if b.len() != Self::BYTES {
            return Err(corrupt("the commits' roots are not that"));
        }
        Ok(Commits {
            by_position: trie::read_flat(&b[..FLAT_BYTES])?,
            by_hash: trie::read_flat(&b[FLAT_BYTES..2 * FLAT_BYTES])?,
            count: u64::from_le_bytes(b[2 * FLAT_BYTES..].try_into().unwrap()),
        })
    }

    /// Marks every page of the table in `file`'s map of free space.
    pub fn mark<B: Backend>(&self, file: &PageFile<B>) -> io::Result<()> {
        trie::mark::<ByPosition, B>(file, self.by_position)?;
        trie::mark::<ByHash, B>(file, self.by_hash)
    }

    /// Frees every page of the table.
    pub fn free<B: Backend>(&self, txn: &Txn<'_, B>) -> io::Result<()> {
        trie::free::<ByPosition, B>(txn, self.by_position)?;
        trie::free::<ByHash, B>(txn, self.by_hash)
    }

    /// The commit the output at `position` is, if the table has it.
    pub fn at(&self, pages: &impl ReadPages, position: u64) -> io::Result<Option<Commit>> {
        Ok(trie::get::<ByPosition>(pages, self.by_position, position as u128)?.map(|c| c.0))
    }

    /// The position of the commit of hash `hash`: the lowest, of one
    /// made more than once.
    pub fn position_of(&self, pages: &impl ReadPages, hash: &Digest) -> io::Result<Option<u64>> {
        let mut at = place(hash, 0);
        // (Past those of other hashes with the same first bits, which
        // nobody finds two of without the work of a chain.)
        while let Some(key) = trie::next_key::<ByHash>(pages, self.by_hash, at)?
            && key >> POSITION_BITS == at >> POSITION_BITS
        {
            match trie::get::<ByHash>(pages, self.by_hash, key)? {
                Some((found, _)) if found.0 == *hash => return Ok(Some(found.1)),
                _ => at = key + 1,
            }
        }
        Ok(None)
    }

    /// The commits at the positions `from..to`, ascending: found one
    /// after another, so the cost is of those there are.
    pub fn between(&self, pages: &impl ReadPages, from: u64, to: u64) -> io::Result<Vec<(u64, Commit)>> {
        let (mut out, mut at) = (Vec::new(), from as u128);
        while let Some(key) = trie::next_key::<ByPosition>(pages, self.by_position, at)?.filter(|k| *k < to as u128) {
            let commit = self.at(pages, key as u64)?.ok_or_else(|| corrupt("a commit found is not there"))?;
            out.push((key as u64, commit));
            at = key + 1;
        }
        Ok(out)
    }

    /// The commits made at `height` or before, ascending by position:
    /// those past their time once `height` is the last they could be
    /// revealed at. Positions grow with height, so the walk stops at the
    /// first made later.
    pub fn up_to(&self, pages: &impl ReadPages, height: u32) -> io::Result<Vec<(u64, Commit)>> {
        let (mut out, mut at) = (Vec::new(), 0u128);
        while let Some(key) = trie::next_key::<ByPosition>(pages, self.by_position, at)? {
            let commit = self.at(pages, key as u64)?.ok_or_else(|| corrupt("a commit found is not there"))?;
            if commit.height > height {
                break;
            }
            out.push((key as u64, commit));
            at = key + 1;
        }
        Ok(out)
    }

    /// Notes that the output at `position` is `commit`. A commit there
    /// already is a fault of the caller's (`AlreadyExists`). The same
    /// commit made twice is two outputs, and nothing forbids it: both
    /// are found by position, the lower by its hash.
    pub fn add<B: Backend>(&mut self, txn: &Txn<'_, B>, position: u64, commit: Commit) -> Result<(), Error> {
        if self.at(txn, position)?.is_some() {
            return Err(io::Error::new(io::ErrorKind::AlreadyExists, "a commit is at the position").into());
        }
        let edits: Edits<'_, ByPosition> = Edits { puts: &[(position, commit, false)], ..Edits::none() };
        self.by_position = trie::update_on(txn, self.by_position, 0, edits, 1)?.0;
        let edits: Edits<'_, ByHash> =
            Edits { puts: &[(place(&commit.hash, position), (commit.hash, position), false)], ..Edits::none() };
        self.by_hash = trie::update_on(txn, self.by_hash, 0, edits, 1)?.0;
        self.count += 1;
        Ok(())
    }

    /// Forgets the commit at `position` (revealed, swept or undone), and
    /// returns what it was: `None` if the table had none there.
    pub fn remove<B: Backend>(&mut self, txn: &Txn<'_, B>, position: u64) -> Result<Option<Commit>, Error> {
        let Some(commit) = self.at(txn, position)? else { return Ok(None) };
        let edits: Edits<'_, ByPosition> = Edits { removes: &[position], ..Edits::none() };
        self.by_position = trie::update_on(txn, self.by_position, 0, edits, 1)?.0;
        let edits: Edits<'_, ByHash> = Edits { removes: &[place(&commit.hash, position)], ..Edits::none() };
        self.by_hash = trie::update_on(txn, self.by_hash, 0, edits, 1)?.0;
        self.count -= 1;
        Ok(Some(commit))
    }

    /// Forgets the commits at the positions `from..to`.
    pub fn remove_between<B: Backend>(&mut self, txn: &Txn<'_, B>, from: u64, to: u64) -> Result<(), Error> {
        for (position, _) in self.between(txn, from, to)? {
            self.remove(txn, position)?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::store::testing::{Lost, MemBackend};
    use crate::test_util::Rng;

    /// Commits are found by position and by hash, in order, by age; and
    /// forgotten, they leave nothing.
    #[test]
    fn commits_by_position_and_by_hash() {
        let file = PageFile::create(MemBackend::new()).unwrap();
        let empty = file.space().0;
        let (mut commits, mut rng) = (Commits::EMPTY, Rng::new(0xc0a1));
        assert_eq!(Commits::from_bytes(&commits.to_bytes()).unwrap(), commits);
        // One a block, far apart, as outputs come between them.
        let all: Vec<(u64, Commit)> = (1..=400u32)
            .map(|h| (h as u64 * 50_000 + rng.next_u64() % 1000, Commit { hash: rng.digest(), height: h }))
            .collect();
        for part in all.chunks(40) {
            let txn = file.begin().unwrap();
            part.iter().for_each(|(p, c)| commits.add(&txn, *p, *c).unwrap());
            txn.commit(&commits.to_bytes()).unwrap();
        }
        assert_eq!(commits.count, 400);
        for (p, c) in all.iter().step_by(7) {
            assert_eq!(commits.at(&file, *p).unwrap(), Some(*c));
            assert_eq!(commits.position_of(&file, &c.hash).unwrap(), Some(*p));
            assert_eq!(commits.at(&file, *p + 1).unwrap(), None);
        }
        // A hash with another's first bits is not that commit.
        let mut twin = all[3].1.hash;
        twin[31] ^= 1;
        assert_eq!(commits.position_of(&file, &twin).unwrap(), None);
        assert_eq!(commits.up_to(&file, 0).unwrap(), vec![]);
        assert_eq!(commits.up_to(&file, 25).unwrap(), all[..25]);
        assert_eq!(commits.up_to(&file, 1000).unwrap(), all);
        assert_eq!(commits.between(&file, all[10].0, all[20].0).unwrap(), all[10..20]);
        assert_eq!(commits.between(&file, 0, 1).unwrap(), vec![]);
        // A position is one commit's. A commit made twice is at both
        // positions, and its hash leads to the lower while that stands.
        let txn = file.begin().unwrap();
        let taken = Err(Error::Io(io::ErrorKind::AlreadyExists));
        assert_eq!(commits.add(&txn, all[5].0, Commit { hash: twin, height: 9 }), taken);
        let mut twice = commits;
        let (first, hash) = (all[5].0, all[5].1.hash);
        let (lower, higher) = (first.min(7), first.max(7));
        twice.add(&txn, 7, all[5].1).unwrap();
        assert_eq!((twice.at(&txn, 7).unwrap(), twice.count), (Some(all[5].1), 401));
        assert_eq!(twice.position_of(&txn, &hash).unwrap(), Some(lower));
        assert_eq!(twice.remove(&txn, 7).unwrap(), Some(all[5].1));
        assert_eq!(twice.position_of(&txn, &hash).unwrap(), Some(first));
        twice.add(&txn, 7, all[5].1).unwrap();
        // And to the other when that one is gone, whichever was made
        // first, and when it is back; to none when both are gone.
        let gone = twice.remove(&txn, lower).unwrap().unwrap();
        assert_eq!(twice.position_of(&txn, &hash).unwrap(), Some(higher));
        twice.add(&txn, lower, gone).unwrap();
        assert_eq!(twice.position_of(&txn, &hash).unwrap(), Some(lower));
        twice.remove(&txn, first).unwrap();
        assert_eq!(twice.position_of(&txn, &hash).unwrap(), Some(7));
        assert_eq!(twice.at(&txn, 7).unwrap(), Some(all[5].1));
        twice.remove(&txn, 7).unwrap();
        assert_eq!(twice.position_of(&txn, &hash).unwrap(), None);
        // (Many of one hash, taken out in their order: each by itself,
        // with no looking among the rest.)
        for position in 1000..1040 {
            twice.add(&txn, position << 20, all[5].1).unwrap();
        }
        for position in 1000..1040 {
            assert_eq!(twice.position_of(&txn, &hash).unwrap(), Some(position << 20));
            twice.remove(&txn, position << 20).unwrap();
        }
        assert_eq!((twice.position_of(&txn, &hash).unwrap(), twice.count), (None, 399));
        twice.add(&txn, first, all[5].1).unwrap();
        twice.add(&txn, 7, all[5].1).unwrap();
        drop(txn);

        // Opened again, the table is the same and its pages are found.
        let again = PageFile::open(MemBackend::from_image(file.backend().image(Lost::All))).unwrap();
        let read = Commits::from_bytes(again.root().payload()).unwrap();
        read.mark(&again).unwrap();
        again.seal();
        assert_eq!((read, again.space().0), (commits, file.space().0));
        assert_eq!(read.up_to(&again, 400).unwrap(), all);

        // Revealed and swept in any order; the last made, undone.
        let txn = file.begin().unwrap();
        for (p, c) in all.iter().step_by(3) {
            assert_eq!(commits.remove(&txn, *p).unwrap(), Some(*c));
            assert_eq!(commits.remove(&txn, *p).unwrap(), None);
        }
        commits.remove_between(&txn, all[390].0, u64::MAX).unwrap();
        txn.commit(&commits.to_bytes()).unwrap();
        let left: Vec<(u64, Commit)> =
            all[..390].iter().enumerate().filter(|(i, _)| i % 3 != 0).map(|(_, c)| *c).collect();
        assert_eq!(commits.up_to(&file, 400).unwrap(), left);
        assert_eq!(commits.count as usize, left.len());
        assert_eq!(commits.position_of(&file, &all[0].1.hash).unwrap(), None);
        let txn = file.begin().unwrap();
        commits.remove_between(&txn, 0, u64::MAX).unwrap();
        txn.commit(&commits.to_bytes()).unwrap();
        assert_eq!((commits, file.space().0), (Commits::EMPTY, empty));
        // Or all at once.
        let txn = file.begin().unwrap();
        all.iter().for_each(|(p, c)| commits.add(&txn, *p, *c).unwrap());
        txn.commit(&commits.to_bytes()).unwrap();
        let txn = file.begin().unwrap();
        commits.free(&txn).unwrap();
        txn.commit(&[]).unwrap();
        assert_eq!(file.space().0, empty);
    }
}
