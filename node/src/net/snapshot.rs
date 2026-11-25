//! The state as it crosses the wire: what a joining node is handed, in
//! what order, and what each piece is checked against.
//!
//! A node that joins does not apply every block there has been. It
//! takes the state as of one block from the nodes there are, and goes
//! on from that block ([`crate::store::receive`]). All it trusts
//! beforehand is that block's header, whose state root every piece is
//! checked against, directly or by way of a piece checked before it:
//!
//! ```text
//! the header's state root
//!   └ Manifest: the roots of the ranges of the outputs, the names' root
//!     │         and the roots of the parts of the names
//!     ├ Roots, one for each range: the roots of the range's parts
//!     │   └ Part, one for each of those: the unspent outputs
//!     └ Names, one for each part of the names: the records
//! ```
//!
//! A *part* of the outputs is the subtree of
//! [`PART_LEVEL`](crate::store::outputs::PART_LEVEL) (8,192 positions);
//! a *range* is the subtree of [`RANGE_LEVEL`] over it (4,096 parts, 33
//! million positions). Two levels, so that nothing fetched grows with
//! the chain: the manifest gains thirty-six bytes for each range that
//! comes into use, and a `Roots` object is at most 4,096 roots. Every
//! piece is small enough that a node which serves a wrong one costs
//! little, and each can come from another peer, in any order, once the
//! piece above it is in.
//!
//! This module is the bytes of those four objects and the checks that
//! need nothing but the bytes. That a part is the part of its root is
//! checked where it is kept ([`crate::store::receive::Receiving::put`]).

use crate::error::Error;
use crate::hash::Digest;
use crate::hash::{digest_from_bytes, digest_to_bytes};
use crate::name::Record as NameRecord;
use crate::output::{MEMO_BYTES, memo_from_bytes, memo_to_bytes};
use crate::registry::state_root as compress;
use crate::store::backend::Backend;
use crate::store::names::{self, PART_LEVEL as NAME_PART_LEVEL};
use crate::store::outputs::{HEIGHT, PART_LEVEL, RECORD_BYTES, Record};
use crate::store::sparse;
use crate::store::state::Past;
use crate::store::trie::Part;

/// The level of the ranges of the outputs: each is 4,096 parts.
pub const RANGE_LEVEL: u32 = PART_LEVEL + 12;
/// Parts in a range.
pub const RANGE_PARTS: u64 = 1 << (RANGE_LEVEL - PART_LEVEL);
/// The most ranges there can be, and the most parts of the names.
pub const MAX_RANGES: usize = 1 << (HEIGHT - RANGE_LEVEL);
pub const MAX_NAME_PARTS: usize = 1 << (crate::name::KEY_BITS as u32 - NAME_PART_LEVEL);
const _: () = assert!(RANGE_LEVEL < HEIGHT && MAX_NAME_PARTS == 4096);

/// The longest a manifest, a `Roots`, a `Part` and a `Names` can be: so
/// that a fetch of one is of no more.
pub const MAX_MANIFEST: usize = 8 + 4 + MAX_RANGES * 36 + 32 + 2 + MAX_NAME_PARTS * 35;
pub const MAX_ROOTS: usize = 2 + RANGE_PARTS as usize * 34;
pub const MAX_PART: usize = 4 + (1 << PART_LEVEL) * (8 + RECORD_BYTES) + 4 + (1 << PART_LEVEL) * 40;
/// (A part of the names has no most: as many names as share twelve
/// bits of their hash. A megabyte is thousands of times what chance
/// gives one.)
pub const MAX_NAMES: usize = 1 << 20;

const BAD: Error = Error::Malformed("a piece of the state");

/// The top of a state in parts: what is fetched first, and checked
/// against the header.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Manifest {
    /// The position the next output after the block takes.
    pub next: u64,
    /// The root of each range of the outputs that holds anything,
    /// ascending by index.
    pub ranges: Vec<(u32, Digest)>,
    /// The root of the names.
    pub names_root: Digest,
    /// Each part of the names that holds anything, ascending by index.
    pub name_parts: Vec<(u32, Part)>,
}

/// The roots of the ranges that the parts `parts` (ascending) lie in.
fn ranges_of(parts: &[(u64, Digest)]) -> Vec<(u32, Digest)> {
    parts
        .chunk_by(|a, b| a.0 / RANGE_PARTS == b.0 / RANGE_PARTS)
        .map(|range| {
            (
                (range[0].0 / RANGE_PARTS) as u32,
                sparse::root(PART_LEVEL as usize, RANGE_LEVEL as usize, &mut range.to_vec()),
            )
        })
        .collect()
}

impl Manifest {
    /// The manifest of a state as of an earlier block.
    pub fn of<B: Backend + 'static>(past: &Past<'_, B>) -> Manifest {
        Manifest {
            next: past.next(),
            ranges: ranges_of(past.parts()),
            names_root: past.names_root(),
            name_parts: past.name_parts().to_vec(),
        }
    }

    /// The outputs' root and the names' of the state it is the top of:
    /// what the block's proof states, with the position after its last
    /// output ([`crate::chain::Chain::check_state_block`]).
    pub fn roots(&self) -> (Digest, Digest) {
        let mut ranges: Vec<(u64, Digest)> = self.ranges.iter().map(|(i, d)| (*i as u64, *d)).collect();
        (sparse::root(RANGE_LEVEL as usize, HEIGHT as usize, &mut ranges), self.names_root)
    }

    /// The root of the state it is the top of.
    pub fn state_root(&self) -> Digest {
        let (outputs, names) = self.roots();
        compress(&outputs, &names)
    }

    /// Whether it is the top of the state of root `state_root`: its
    /// ranges and its names' root hash to that, and the parts of the
    /// names to the names' root.
    pub fn check(&self, state_root: &Digest) -> bool {
        self.state_root() == *state_root && names::parts_root(NAME_PART_LEVEL, &self.name_parts) == self.names_root
    }

    pub fn encode(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(46 + 36 * self.ranges.len() + 35 * self.name_parts.len());
        out.extend_from_slice(&self.next.to_le_bytes());
        out.extend_from_slice(&(self.ranges.len() as u32).to_le_bytes());
        for (index, root) in &self.ranges {
            out.extend_from_slice(&index.to_le_bytes());
            out.extend_from_slice(&digest_to_bytes(root));
        }
        out.extend_from_slice(&digest_to_bytes(&self.names_root));
        out.extend_from_slice(&(self.name_parts.len() as u16).to_le_bytes());
        for (index, part) in &self.name_parts {
            out.extend_from_slice(&(*index as u16).to_le_bytes());
            out.extend_from_slice(&digest_to_bytes(&part.hash));
            out.push(part.single as u8);
        }
        out
    }

    /// A manifest that is the whole of `bytes`: its indexes within what
    /// there can be, ascending and distinct.
    pub fn decode(bytes: &[u8]) -> Result<Manifest, Error> {
        let mut r = In(bytes);
        let next = u64::from_le_bytes(r.array()?);
        let n = u32::from_le_bytes(r.array()?) as usize;
        if n > MAX_RANGES {
            return Err(BAD);
        }
        let mut ranges: Vec<(u32, Digest)> = Vec::with_capacity(n);
        for _ in 0..n {
            let index = u32::from_le_bytes(r.array()?);
            if index as usize >= MAX_RANGES || ranges.last().is_some_and(|l| l.0 >= index) {
                return Err(BAD);
            }
            ranges.push((index, r.digest()?));
        }
        let names_root = r.digest()?;
        let n = u16::from_le_bytes(r.array()?) as usize;
        if n > MAX_NAME_PARTS {
            return Err(BAD);
        }
        let mut name_parts: Vec<(u32, Part)> = Vec::with_capacity(n);
        for _ in 0..n {
            let index = u16::from_le_bytes(r.array()?) as u32;
            if index as usize >= MAX_NAME_PARTS || name_parts.last().is_some_and(|l| l.0 >= index) {
                return Err(BAD);
            }
            let hash = r.digest()?;
            let [single] = r.array()?;
            if single > 1 {
                return Err(BAD);
            }
            name_parts.push((index, Part { hash, single: single == 1 }));
        }
        r.end()?;
        Ok(Manifest { next, ranges, names_root, name_parts })
    }
}

/// The roots of the parts of the outputs in the range `range`, as a
/// `Roots` object: none if the range holds nothing.
pub fn encode_roots<B: Backend + 'static>(past: &Past<'_, B>, range: u32) -> Option<Vec<u8>> {
    let parts = past.parts();
    let from = parts.partition_point(|p| p.0 / RANGE_PARTS < range as u64);
    let to = parts.partition_point(|p| p.0 / RANGE_PARTS <= range as u64);
    if from == to {
        return None;
    }
    let mut out = Vec::with_capacity(2 + 34 * (to - from));
    // (One less than how many, since there may be 4,096 and are never none.)
    out.extend_from_slice(&((to - from - 1) as u16).to_le_bytes());
    for (index, root) in &parts[from..to] {
        out.extend_from_slice(&((index % RANGE_PARTS) as u16).to_le_bytes());
        out.extend_from_slice(&digest_to_bytes(root));
    }
    Some(out)
}

/// The roots of the parts of the range `range` from a `Roots` object,
/// each with its part's index among all: checked to be those of the
/// range whose root is `want`.
pub fn decode_roots(bytes: &[u8], range: u32, want: &Digest) -> Result<Vec<(u64, Digest)>, Error> {
    let mut r = In(bytes);
    let n = u16::from_le_bytes(r.array()?) as usize + 1;
    if n > RANGE_PARTS as usize {
        return Err(BAD);
    }
    let mut parts: Vec<(u64, Digest)> = Vec::with_capacity(n);
    for _ in 0..n {
        let index = range as u64 * RANGE_PARTS + u16::from_le_bytes(r.array()?) as u64;
        if index >= (range as u64 + 1) * RANGE_PARTS || parts.last().is_some_and(|l| l.0 >= index) {
            return Err(BAD);
        }
        parts.push((index, r.digest()?));
    }
    r.end()?;
    if sparse::root(PART_LEVEL as usize, RANGE_LEVEL as usize, &mut parts.clone()) != *want {
        return Err(Error::PartRoot);
    }
    Ok(parts)
}

/// A part of the outputs as a `Part` object: its unspent outputs, and
/// which of them are commits of names, both ascending by position.
pub fn encode_part(outputs: &[(u64, Record)], commits: &[(u64, Digest)]) -> Vec<u8> {
    let mut out = Vec::with_capacity(8 + outputs.len() * (8 + RECORD_BYTES) + commits.len() * 40);
    out.extend_from_slice(&(outputs.len() as u32).to_le_bytes());
    for (position, record) in outputs {
        out.extend_from_slice(&position.to_le_bytes());
        out.extend_from_slice(&digest_to_bytes(&record.commitment));
        out.extend_from_slice(&memo_to_bytes(&record.memo));
        out.extend_from_slice(&record.amount.to_le_bytes());
        out.extend_from_slice(&record.height.to_le_bytes());
    }
    out.extend_from_slice(&(commits.len() as u32).to_le_bytes());
    for (position, hash) in commits {
        out.extend_from_slice(&position.to_le_bytes());
        out.extend_from_slice(&digest_to_bytes(hash));
    }
    out
}

/// What a part holds: its outputs, and its commits.
pub type PartContent = (Vec<(u64, Record)>, Vec<(u64, Digest)>);

/// The outputs and commits of the part `index` from a `Part` object:
/// positions within the part, ascending and distinct. That they are the
/// part of its root is for whoever keeps them to check.
pub fn decode_part(bytes: &[u8], index: u64) -> Result<PartContent, Error> {
    let within = |p: u64| p >> PART_LEVEL == index;
    let mut r = In(bytes);
    let n = u32::from_le_bytes(r.array()?) as usize;
    if n > 1 << PART_LEVEL {
        return Err(BAD);
    }
    let mut outputs: Vec<(u64, Record)> = Vec::with_capacity(n);
    for _ in 0..n {
        let position = u64::from_le_bytes(r.array()?);
        if !within(position) || outputs.last().is_some_and(|l| l.0 >= position) {
            return Err(BAD);
        }
        let record = Record {
            commitment: r.digest()?,
            memo: memo_from_bytes(r.take(MEMO_BYTES)?).map_err(|_| BAD)?,
            amount: u64::from_le_bytes(r.array()?),
            height: u32::from_le_bytes(r.array()?),
        };
        outputs.push((position, record));
    }
    let n = u32::from_le_bytes(r.array()?) as usize;
    if n > outputs.len() {
        return Err(BAD);
    }
    let mut commits: Vec<(u64, Digest)> = Vec::with_capacity(n);
    for _ in 0..n {
        let position = u64::from_le_bytes(r.array()?);
        if !within(position) || commits.last().is_some_and(|l| l.0 >= position) {
            return Err(BAD);
        }
        commits.push((position, r.digest()?));
    }
    r.end()?;
    Ok((outputs, commits))
}

/// A part of the names as a `Names` object: its records, ascending by
/// key.
pub fn encode_names(records: &[NameRecord]) -> Vec<u8> {
    let mut out = (records.len() as u32).to_le_bytes().to_vec();
    for record in records {
        out.extend_from_slice(&record.to_bytes());
    }
    out
}

/// The records of a `Names` object. That they are the part of its root
/// is for whoever keeps them to check.
pub fn decode_names(bytes: &[u8]) -> Result<Vec<NameRecord>, Error> {
    let mut r = In(bytes);
    let n = u32::from_le_bytes(r.array()?) as usize;
    // (No more than there are bytes for: a count is not believed.)
    let mut records = Vec::with_capacity(n.min(bytes.len() / 97));
    for _ in 0..n {
        let (record, rest) = NameRecord::read(r.0).ok_or(BAD)?;
        r.0 = rest;
        records.push(record);
    }
    r.end()?;
    Ok(records)
}

struct In<'a>(&'a [u8]);

impl<'a> In<'a> {
    fn take(&mut self, n: usize) -> Result<&'a [u8], Error> {
        let (head, rest) = self.0.split_at_checked(n).ok_or(BAD)?;
        self.0 = rest;
        Ok(head)
    }

    fn array<const N: usize>(&mut self) -> Result<[u8; N], Error> {
        self.take(N).map(|b| b.try_into().unwrap())
    }

    fn digest(&mut self) -> Result<Digest, Error> {
        digest_from_bytes(self.take(32)?).ok_or(BAD)
    }

    fn end(&self) -> Result<(), Error> {
        if self.0.is_empty() { Ok(()) } else { Err(BAD) }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_util::Rng;

    fn digest(rng: &mut Rng) -> Digest {
        rng.digest()
    }

    /// Parts scattered over several ranges: every range's roots check
    /// against the manifest's, and the manifest against the root the
    /// parts themselves hash to.
    #[test]
    fn roots_check_against_the_manifest_and_it_against_the_state() {
        let mut rng = Rng::new(1);
        let mut parts: Vec<(u64, Digest)> = Vec::new();
        for range in [0u64, 1, 5, 4095, 65535] {
            let mut at = range * RANGE_PARTS;
            for _ in 0..1 + rng.next_u64() % 40 {
                at += 1 + rng.next_u64() % 90;
                parts.push((at.min((range + 1) * RANGE_PARTS - 1), digest(&mut rng)));
            }
            parts.dedup_by_key(|p| p.0);
        }
        // A range full to its last part.
        let full = 9 * RANGE_PARTS;
        parts.extend((0..RANGE_PARTS).map(|k| (full + k, digest(&mut rng))));
        parts.sort_by_key(|p| p.0);
        let names_root = names::parts_root(NAME_PART_LEVEL, &[]);
        let m = Manifest { next: 77, ranges: ranges_of(&parts), names_root, name_parts: vec![] };
        assert_eq!(m.ranges.len(), 6);
        let state_root = compress(&crate::store::outputs::parts_root(PART_LEVEL, &parts), &names_root);
        assert!(m.check(&state_root));
        assert_eq!(Manifest::decode(&m.encode()), Ok(m.clone()));
        // Each range's roots, as they would be served and taken.
        let mut taken = Vec::new();
        for (range, want) in &m.ranges {
            let own: Vec<_> = parts.iter().filter(|p| p.0 / RANGE_PARTS == *range as u64).copied().collect();
            let mut bytes = ((own.len() - 1) as u16).to_le_bytes().to_vec();
            for (index, root) in &own {
                bytes.extend_from_slice(&((index % RANGE_PARTS) as u16).to_le_bytes());
                bytes.extend_from_slice(&digest_to_bytes(root));
            }
            assert!(bytes.len() <= MAX_ROOTS);
            assert_eq!(decode_roots(&bytes, *range, want), Ok(own.clone()));
            taken.extend(own.iter().copied());
            // Another range's root, a root changed, a part left out:
            // not the range's.
            assert_eq!(decode_roots(&bytes, *range, &digest(&mut rng)), Err(Error::PartRoot));
            let mut wrong = bytes.clone();
            wrong[10] ^= 1;
            assert!(decode_roots(&wrong, *range, want).is_err());
            if own.len() > 1 {
                let mut short = ((own.len() - 2) as u16).to_le_bytes().to_vec();
                short.extend_from_slice(&bytes[2..bytes.len() - 34]);
                assert_eq!(decode_roots(&short, *range, want), Err(Error::PartRoot));
            }
            // A byte more or less.
            assert!(decode_roots(&bytes[..bytes.len() - 1], *range, want).is_err());
            let mut long = bytes.clone();
            long.push(0);
            assert!(decode_roots(&long, *range, want).is_err());
        }
        assert_eq!(taken, parts);
        // The manifest with a range's root changed, or one left out, or
        // another names' root, is not the state's.
        let mut wrong = m.clone();
        wrong.ranges[2].1[0] ^= 1;
        assert!(!wrong.check(&state_root));
        let mut wrong = m.clone();
        wrong.ranges.remove(1);
        assert!(!wrong.check(&state_root));
        let mut wrong = m.clone();
        wrong.names_root[0] ^= 1;
        assert!(!wrong.check(&state_root));
        // The largest there can be is what a fetch of one allows for.
        let most = Manifest {
            next: 0,
            ranges: (0..MAX_RANGES as u32).map(|i| (i, names_root)).collect(),
            names_root,
            name_parts: (0..MAX_NAME_PARTS as u32).map(|i| (i, Part { hash: names_root, single: false })).collect(),
        };
        assert_eq!(most.encode().len(), MAX_MANIFEST);
        assert_eq!(Manifest::decode(&most.encode()), Ok(most));
    }

    #[test]
    fn a_manifest_that_could_not_have_been_made_is_refused() {
        let d = [3u8; 32];
        let good = Manifest {
            next: 5,
            ranges: vec![(1, d), (4, d)],
            names_root: d,
            name_parts: vec![(7, Part { hash: d, single: true })],
        };
        let bytes = good.encode();
        assert_eq!(Manifest::decode(&bytes), Ok(good));
        let with = |at: usize, v: &[u8]| {
            let mut b = bytes.clone();
            b[at..at + v.len()].copy_from_slice(v);
            Manifest::decode(&b).is_err()
        };
        // Ranges out of order, or the same twice; one past the last
        // there can be; more than there can be.
        assert!(with(12, &4u32.to_le_bytes()));
        assert!(with(48, &1u32.to_le_bytes()));
        assert!(with(48, &(MAX_RANGES as u32).to_le_bytes()));
        assert!(with(8, &(MAX_RANGES as u32 + 1).to_le_bytes()));
        // A part of the names past the last; "single" neither yes nor
        // no.
        assert!(with(118, &4096u16.to_le_bytes()));
        assert!(with(152, &[2]));
        // A byte more, a byte less, and anything at all.
        assert!(Manifest::decode(&bytes[..bytes.len() - 1]).is_err());
        assert!(Manifest::decode(&[bytes.clone(), vec![0]].concat()).is_err());
        let mut rng = Rng::new(4);
        for _ in 0..3000 {
            let b: Vec<u8> = (0..rng.next_u64() % 200).map(|_| rng.next_u64() as u8).collect();
            let _ = Manifest::decode(&b);
            let _ = decode_roots(&b, 0, &d);
            let _ = decode_part(&b, 0);
            let _ = decode_names(&b);
        }
    }

    #[test]
    fn a_part_roundtrips_and_holds_only_its_own_positions() {
        let mut rng = Rng::new(2);
        let index = 12345u64;
        let record = |rng: &mut Rng| Record {
            commitment: digest(rng),
            memo: rng.digest()[..20].try_into().unwrap(),
            amount: rng.next_u64(),
            height: rng.next_u64() as u32,
        };
        let outputs: Vec<(u64, Record)> =
            (0..200u64).map(|k| ((index << PART_LEVEL) + 3 * k, record(&mut rng))).collect();
        let commits: Vec<(u64, Digest)> = outputs.iter().step_by(7).map(|o| (o.0, digest(&mut rng))).collect();
        let bytes = encode_part(&outputs, &commits);
        assert_eq!(decode_part(&bytes, index), Ok((outputs.clone(), commits.clone())));
        // Of another part; a byte short or long.
        assert!(decode_part(&bytes, index + 1).is_err());
        assert!(decode_part(&bytes[..bytes.len() - 1], index).is_err());
        assert!(decode_part(&[bytes.clone(), vec![0]].concat(), index).is_err());
        // Out of order; more commits than outputs.
        let mut swapped = outputs.clone();
        swapped.swap(3, 4);
        assert!(decode_part(&encode_part(&swapped, &commits), index).is_err());
        let many: Vec<(u64, Digest)> = (0..201u64).map(|k| ((index << PART_LEVEL) + k, digest(&mut rng))).collect();
        assert!(decode_part(&encode_part(&outputs, &many), index).is_err());
        // Nothing in it is still a part's bytes; the fullest is what a
        // fetch allows for.
        assert_eq!(decode_part(&encode_part(&[], &[]), index), Ok((vec![], vec![])));
        let full: Vec<(u64, Record)> =
            (0..1u64 << PART_LEVEL).map(|k| ((index << PART_LEVEL) + k, outputs[0].1)).collect();
        let all: Vec<(u64, Digest)> = full.iter().map(|o| (o.0, o.1.commitment)).collect();
        assert_eq!(encode_part(&full, &all).len(), MAX_PART);
        const { assert!(MAX_PART <= 1 << 20) };
    }

    #[test]
    fn names_roundtrip() {
        let mut rng = Rng::new(3);
        let records: Vec<NameRecord> = ["alice", "bob", "carol"]
            .iter()
            .map(|n| NameRecord::new(n.as_bytes(), digest(&mut rng), digest(&mut rng), digest(&mut rng)).unwrap())
            .collect();
        let bytes = encode_names(&records);
        assert_eq!(decode_names(&bytes), Ok(records));
        assert!(decode_names(&bytes[..bytes.len() - 1]).is_err());
        assert!(decode_names(&[bytes.clone(), vec![0]].concat()).is_err());
        assert_eq!(decode_names(&encode_names(&[])), Ok(vec![]));
        // A count that is not believed.
        assert!(decode_names(&u32::MAX.to_le_bytes()).is_err());
    }
}
