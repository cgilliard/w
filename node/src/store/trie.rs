//! A trie over keys that is also a Merkle tree of what it holds: the
//! shape the state's two halves share.
//!
//! The outputs and the names are different trees. Their keys are of
//! different lengths, their records of different sizes, and their hashes
//! follow different rules; a new output always takes the next key, a new
//! name falls anywhere. What they share is here, written once over a
//! description of the tree ([`Tree`]): how the records lie in pages, how
//! a block's changes are made in one pass, and how the hashes follow.
//!
//! # Shape
//!
//! A node covers the keys with one prefix and has [`FANOUT`] slots, each
//! covering those with [`BITS`] more bits fixed. A slot is empty, holds
//! another node, or is under a leaf: a page of records. A leaf covers
//! one slot or a run of two, four or eight of them that is one subtree
//! of the tree (its `span`), whichever holds as many records as fit a
//! page: so pages are mostly more than half full however thinly or
//! thickly the keys lie. Beside each child the node keeps the child's
//! part in the Merkle tree, so a node's own part follows from its page
//! alone, and a key's path from the pages on the way down to it.
//!
//! ```text
//! node page := height (1) | children (1) | child ...
//! child     := slot (1) | kind and span (1) | hash (32) | page (6) | leaf's
//! leaf's    := records (1) | live (8) | last spend (4)
//! leaf page := records (1) | record ...
//! record    := distance from the key before (varint) | the tree's record
//! ```
//!
//! # A record can be dead
//!
//! Which records of a leaf count in the tree is a bit each in the node
//! above (`live`). A tree that spends its records (the outputs) clears
//! the bit and changes the hashes above: the nodes on the way are written
//! anew, as they must be, and the page of records is left as it is. A
//! dead record is still there to be had, and comes back with its bit.
//! Beside a leaf the node keeps `last spend`, the height of the latest
//! bit cleared in it, so that a sweep ([`sweep`]) can tell without
//! reading the page when everything dead in it is old enough to drop.
//!
//! # Changes
//!
//! Changes are made in one pass in key order ([`update`]): each page on
//! the way is read once, and written once when the pass leaves it.
//! Nothing is changed in place; the pages replaced are named to the
//! transaction, and the new root is returned to be committed with it.
//!
//! A pass that changes much is split among threads where the trie
//! branches: the subtrees under a node share nothing, so each is a pass
//! of its own, and what a block costs is mostly their hashing.

use std::io;

use super::backend::Backend;
use super::pagefile::{Extent, PageFile, ReadPages, Txn};
use crate::error::Error;
use crate::hash::{Digest, EMPTY, digest_from_bytes, digest_to_bytes};

/// Bits of a key a node fixes.
pub const BITS: u32 = 4;
/// Children of a node.
pub const FANOUT: usize = 1 << BITS;
/// The most records a leaf holds: a bit each in its `live`.
pub const LEAF_RECORDS: usize = 64;
/// The most bytes of a leaf page's payload: eight units.
const LEAF_BYTES: usize = Extent::capacity(8);
const PAGE: usize = 4096;
/// A pass with fewer keys to change than this stays on one thread.
const SPLIT: usize = 512;

fn corrupt(what: &'static str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, what)
}

/// The last key of the subtree of `height` levels from `base`. (Not the
/// key after it: a tree of 128 levels has none.)
fn last_key(base: u128, height: u32) -> u128 {
    base | u128::MAX.checked_shr(128 - height).unwrap_or(0)
}

/// A subtree's place in the Merkle tree: its hash, and whether it holds
/// exactly one record (which some trees hash differently).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Part {
    pub hash: Digest,
    pub single: bool,
}

/// Why a change cannot be made.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Fault {
    /// The record to mark dead is not there, or is dead already.
    NotLive,
    /// The record to bring back is not there, or is not dead.
    NotDead,
    /// A record to insert has a key already taken.
    Present,
    /// A record to replace or remove is not there.
    Absent,
    /// A record of a run does not come after every record before it.
    Order,
}

/// A tree the trie can hold: its keys, its records, and how it hashes.
pub trait Tree {
    /// Bits of a key: the height of the tree.
    const HEIGHT: u32;
    /// A key as the tree's users give it.
    type Key: Copy + Into<u128> + Send + Sync;
    type Record: Copy + PartialEq + core::fmt::Debug + Send + Sync;

    /// Bytes [`Tree::write_record`] appends for `r`.
    fn record_len(r: &Self::Record) -> usize;
    fn write_record(r: &Self::Record, out: &mut Vec<u8>);
    /// Reads a record from the front of `b`, and returns the rest.
    fn read_record(b: &[u8]) -> io::Result<(Self::Record, &[u8])>;

    /// The hash of a live record at the bottom of the tree.
    fn leaf(key: u128, r: &Self::Record) -> Digest;
    /// The hashes of the live records of `slots`, in order, into `out`;
    /// returns how many. A tree that can hash several at once does.
    fn leaves(slots: &[Slot<Self::Record>], out: &mut [(u128, Part); LEAF_RECORDS]) -> usize {
        let mut n = 0;
        for s in slots.iter().filter(|s| s.live) {
            out[n] = (s.key, Part { hash: Self::leaf(s.key, &s.record), single: true });
            n += 1;
        }
        n
    }
    /// One level up: the nonempty parts at `level` (a record is level
    /// 0; the part of index `i` covers the keys from `i << level`),
    /// ascending, are replaced in place by those of their parents at the
    /// level above. Returns how many parents there are.
    fn lift(level: u32, parts: &mut [(u128, Part)]) -> usize;
    /// The part of the node at level `top`, from its nonempty parts at
    /// `level`; `None` if there are none. The slice is scratch.
    fn combine(level: u32, top: u32, parts: &mut [(u128, Part)]) -> Option<Part> {
        let mut n = parts.len();
        for l in level..top {
            n = Self::lift(l, &mut parts[..n]);
        }
        (n > 0).then(|| parts[0].1)
    }
    /// What a record weighs: a pass adds up the weights of the records
    /// it marks dead. A tree with nothing to add up weighs nothing.
    fn weight(_: &Self::Record) -> u64 {
        0
    }
    /// What a change that cannot be made is refused with.
    fn refuse(key: u128, fault: Fault) -> Error;
}

/// A child of a node, or the root: a subtree.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Child {
    /// No record under it, live or dead.
    Empty,
    /// A node's page. `part` is `None` if nothing under it is live.
    Node { page: Extent, part: Option<Part> },
    /// A page of records.
    Leaf {
        page: Extent,
        part: Option<Part>,
        /// Records in the page.
        records: u8,
        /// Which of them are live, the first the lowest bit.
        live: u64,
        /// The height of the latest of them to die, 0 if none.
        last_spend: u32,
        /// It covers `2^span` of its node's slots, from its own.
        span: u8,
    },
}

/// Bytes of a child's encoding, less its slot: the longest, a leaf's.
pub const CHILD_BYTES: usize = 1 + 32 + 6 + 13;
const KIND: u8 = 0x0f;
const SINGLE: u8 = 0x80;
const VOID: u8 = 0x40;
const SPAN: u8 = 0x30;

fn put_extent(out: &mut Vec<u8>, e: Extent) {
    // (Five bytes of where and one of how long: a file of 2^40 units,
    // which no disk holds. Past that, what was written would be read
    // from somewhere else.)
    assert!(e.start < 1 << 40 && e.units < 256, "a page past what a child says of one");
    out.extend_from_slice(&e.start.to_le_bytes()[..5]);
    out.push(e.units as u8);
}

fn get_extent(b: &[u8]) -> Extent {
    let mut start = [0u8; 8];
    start[..5].copy_from_slice(&b[..5]);
    Extent { start: u64::from_le_bytes(start), units: b[5] as u32 }
}

impl Child {
    /// The subtree's part in the tree: `None` if nothing in it is live.
    pub fn part(&self) -> Option<Part> {
        match self {
            Child::Empty => None,
            Child::Node { part, .. } | Child::Leaf { part, .. } => *part,
        }
    }

    pub fn write(&self, out: &mut Vec<u8>) {
        let (kind, page, part) = match self {
            Child::Empty => return out.push(0),
            Child::Node { page, part } => (1, page, part),
            Child::Leaf { page, part, span, .. } => (2 | span << 4, page, part),
        };
        let flags = match part {
            None => VOID,
            Some(p) if p.single => SINGLE,
            Some(_) => 0,
        };
        out.push(kind | flags);
        out.extend_from_slice(&digest_to_bytes(&part.map_or(EMPTY, |p| p.hash)));
        put_extent(out, *page);
        if let Child::Leaf { records, live, last_spend, .. } = self {
            out.push(*records);
            out.extend_from_slice(&live.to_le_bytes());
            out.extend_from_slice(&last_spend.to_le_bytes());
        }
    }

    /// Reads a child from the front of `b`, and returns the rest.
    pub fn read(b: &[u8]) -> io::Result<(Child, &[u8])> {
        let bad = || corrupt("a node's child is not one");
        let (&tag, b) = b.split_first().ok_or_else(bad)?;
        if tag == 0 {
            return Ok((Child::Empty, b));
        }
        let (kind, span, flags) = (tag & KIND, (tag & SPAN) >> 4, tag & !(KIND | SPAN));
        let (head, b) = b.split_at_checked(38).ok_or_else(bad)?;
        let hash = digest_from_bytes(&head[..32]).ok_or_else(bad)?;
        let part = match flags {
            VOID if hash == EMPTY => None,
            SINGLE => Some(Part { hash, single: true }),
            0 => Some(Part { hash, single: false }),
            _ => return Err(bad()),
        };
        let page = get_extent(&head[32..]);
        if page.units == 0 {
            return Err(bad());
        }
        match kind {
            1 if span == 0 => Ok((Child::Node { page, part }, b)),
            2 => {
                let (tail, b) = b.split_at_checked(13).ok_or_else(bad)?;
                let records = tail[0];
                let live = u64::from_le_bytes(tail[1..9].try_into().unwrap());
                if records == 0 || records as usize > LEAF_RECORDS || (records < 64 && live >> records != 0) {
                    return Err(bad());
                }
                // A leaf with nothing live has no part, and one with has.
                if (live == 0) != part.is_none() {
                    return Err(bad());
                }
                let last_spend = u32::from_le_bytes(tail[9..].try_into().unwrap());
                Ok((Child::Leaf { page, part, records, live, last_spend, span }, b))
            }
            _ => Err(bad()),
        }
    }
}

/// Bytes of the root of a tree that hashes nothing, in a root record.
pub const FLAT_BYTES: usize = CHILD_BYTES - 32;

/// Writes the root of a tree that hashes nothing: a child less its hash,
/// which is zero, in [`FLAT_BYTES`].
pub fn write_flat(root: &Child, out: &mut Vec<u8>) {
    let mut full = Vec::with_capacity(CHILD_BYTES);
    root.write(&mut full);
    let end = out.len() + FLAT_BYTES;
    out.push(full[0]);
    if full.len() > 1 {
        debug_assert!(full[1..33].iter().all(|b| *b == 0), "the tree hashes nothing");
        out.extend_from_slice(&full[33..]);
    }
    out.resize(end, 0);
}

/// Reads what [`write_flat`] wrote.
pub fn read_flat(b: &[u8]) -> io::Result<Child> {
    let bad = || corrupt("a tree's root is not one");
    if b.len() != FLAT_BYTES {
        return Err(bad());
    }
    let mut full = vec![b[0]];
    if b[0] != 0 {
        full.extend_from_slice(&[0; 32]);
    }
    full.extend_from_slice(&b[1..]);
    let (root, rest) = Child::read(&full)?;
    match rest.iter().all(|x| *x == 0) {
        true => Ok(root),
        false => Err(bad()),
    }
}

/// A node's children, read from its page.
pub fn read_node(payload: &[u8], height: u32) -> io::Result<[Child; FANOUT]> {
    let bad = || corrupt("a node's page is not one");
    let (head, mut b) = payload.split_at_checked(2).ok_or_else(bad)?;
    if head[0] as u32 != height {
        return Err(bad());
    }
    let mut children = [Child::Empty; FANOUT];
    let slots = 1usize << (height - below(height));
    // The first slot no child given so far covers.
    let mut free = 0;
    for _ in 0..head[1] {
        let (&slot, rest) = b.split_first().ok_or_else(bad)?;
        let (child, rest) = Child::read(rest)?;
        let span = span_of(child);
        // Slots ascend past what is covered, none is given as empty, and
        // a leaf's run of slots is one subtree, short of the whole node.
        if (slot as usize) < free
            || child == Child::Empty
            || (span > 0 && (1usize << span >= slots || !(slot as usize).is_multiple_of(1 << span)))
            || slot as usize + (1 << span) > slots
        {
            return Err(bad());
        }
        children[slot as usize] = child;
        (free, b) = (slot as usize + (1 << span), rest);
    }
    if !b.is_empty() || free == 0 {
        return Err(bad());
    }
    Ok(children)
}

pub fn write_node(children: &[Child; FANOUT], height: u32, out: &mut Vec<u8>) {
    out.clear();
    out.push(height as u8);
    out.push(children.iter().filter(|c| **c != Child::Empty).count() as u8);
    for (slot, c) in children.iter().enumerate() {
        if *c != Child::Empty {
            out.push(slot as u8);
            c.write(out);
        }
    }
}

/// The height of a node's slots: [`BITS`] below it, or what is left of
/// the key.
pub const fn below(height: u32) -> u32 {
    height.saturating_sub(BITS)
}

/// How many of its node's slots a child covers, as a power of two.
pub fn span_of(child: Child) -> u32 {
    match child {
        Child::Leaf { span, .. } => span as u32,
        _ => 0,
    }
}

/// The child that covers `slot` of a node of `height` levels: where it
/// starts and its span. (An empty slot is its own, of span 0.)
pub fn group_of(children: &[Child; FANOUT], height: u32, slot: usize) -> (usize, u32) {
    for span in (1..height - below(height)).rev() {
        let start = slot & !((1 << span) - 1);
        if span_of(children[start]) == span {
            return (start, span);
        }
    }
    (slot, 0)
}

/// The nonempty parts under a node at each level from its slots' up to
/// its own: `at(0)` those at the slots' level, `at(1)` the level above,
/// to the node's one part (or none) at `at(height - below)`.
pub struct Levels {
    parts: [[(u128, Part); FANOUT]; BITS as usize + 1],
    len: [usize; BITS as usize + 1],
}

impl Levels {
    /// The parts at `up` levels above the slots', ascending by index.
    pub fn at(&self, up: u32) -> &[(u128, Part)] {
        &self.parts[up as usize][..self.len[up as usize]]
    }

    /// The part of index `index` at `up` levels above the slots', if any.
    pub fn find(&self, up: u32, index: u128) -> Option<Part> {
        self.at(up).iter().find(|p| p.0 == index).map(|p| p.1)
    }
}

/// The parts under the node of `children`, of `height` levels from
/// `base`, level by level: each child's part enters at the level of the
/// subtree it covers, and each level is lifted to the next.
pub fn levels<T: Tree>(children: &[Child; FANOUT], height: u32, base: u128) -> Levels {
    let low = below(height);
    let top = height - low;
    let none = (0u128, Part { hash: EMPTY, single: false });
    let mut out = Levels { parts: [[none; FANOUT]; BITS as usize + 1], len: [0; BITS as usize + 1] };
    let mut cur = [none; FANOUT];
    let mut n = 0;
    for up in 0..=top {
        for (k, c) in children.iter().enumerate().take(1 << top) {
            if let Some(part) = c.part().filter(|_| span_of(*c) == up) {
                cur[n] = ((base >> (low + up)) + (k as u128 >> up), part);
                n += 1;
            }
        }
        cur[..n].sort_unstable_by_key(|p| p.0);
        out.parts[up as usize][..n].copy_from_slice(&cur[..n]);
        out.len[up as usize] = n;
        if up < top {
            n = T::lift(low + up, &mut cur[..n]);
        }
    }
    out
}

fn node_part<T: Tree>(children: &[Child; FANOUT], height: u32, base: u128) -> Option<Part> {
    levels::<T>(children, height, base).at(height - below(height)).first().map(|p| p.1)
}

/// A record of a leaf, with its key and whether it is live.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Slot<R> {
    pub key: u128,
    pub record: R,
    pub live: bool,
}

fn put_varint(out: &mut Vec<u8>, mut x: u128) {
    while x >= 0x80 {
        out.push(x as u8 | 0x80);
        x >>= 7;
    }
    out.push(x as u8);
}

fn varint_len(x: u128) -> usize {
    ((128 - x.leading_zeros()).div_ceil(7).max(1)) as usize
}

fn get_varint(b: &[u8]) -> Option<(u128, &[u8])> {
    let (mut x, mut shift) = (0u128, 0);
    for (i, &byte) in b.iter().enumerate().take(19) {
        // The nineteenth byte holds the last two bits of 128.
        if shift == 126 && byte > 3 {
            return None;
        }
        x |= u128::from(byte & 0x7f) << shift;
        shift += 7;
        if byte < 0x80 {
            return Some((x, &b[i + 1..]));
        }
    }
    None
}

/// A leaf page's records, appended to `out`: those of the leaf whose
/// subtree of `height` levels starts at `base`.
pub fn read_leaf<T: Tree>(
    payload: &[u8],
    base: u128,
    height: u32,
    records: u8,
    live: u64,
    out: &mut Vec<Slot<T::Record>>,
) -> io::Result<()> {
    let bad = || corrupt("a leaf's page is not one");
    let (&count, mut b) = payload.split_first().ok_or_else(bad)?;
    if count != records {
        return Err(bad());
    }
    let last = last_key(base, height);
    let mut key = base;
    for i in 0..count as usize {
        let (delta, rest) = get_varint(b).ok_or_else(bad)?;
        // Keys ascend, and stay under the leaf.
        if i > 0 && delta == 0 {
            return Err(bad());
        }
        key = key.checked_add(delta).filter(|k| *k <= last).ok_or_else(bad)?;
        let (record, rest) = T::read_record(rest)?;
        out.push(Slot { key, record, live: live >> i & 1 == 1 });
        b = rest;
    }
    if !b.is_empty() {
        return Err(bad());
    }
    Ok(())
}

pub fn write_leaf<T: Tree>(slots: &[Slot<T::Record>], base: u128, out: &mut Vec<u8>) {
    out.clear();
    out.push(slots.len() as u8);
    let mut prev = base;
    for s in slots {
        put_varint(out, s.key - prev);
        T::write_record(&s.record, out);
        prev = s.key;
    }
}

/// Whether `slots`, under one subtree starting at `base`, fit a leaf.
fn fits<T: Tree>(slots: &[Slot<T::Record>], base: u128) -> bool {
    if slots.len() > LEAF_RECORDS {
        return false;
    }
    let mut bytes = 1;
    let mut prev = base;
    for s in slots {
        bytes += varint_len(s.key - prev) + T::record_len(&s.record);
        prev = s.key;
    }
    bytes <= LEAF_BYTES
}

/// The part of a subtree of `height` levels, from its live records.
pub fn leaf_part<T: Tree>(slots: &[Slot<T::Record>], height: u32) -> Option<Part> {
    let mut parts = [(0u128, Part { hash: EMPTY, single: true }); LEAF_RECORDS];
    let n = T::leaves(slots, &mut parts);
    T::combine(0, height, &mut parts[..n])
}

fn live_bits<R>(slots: &[Slot<R>]) -> u64 {
    slots.iter().enumerate().fold(0, |bits, (i, s)| bits | (s.live as u64) << i)
}

/// What one pass changes. Every part of it is in key order, and is cut
/// down to a subtree's keys as the pass descends, at no cost.
pub struct Edits<'a, T: Tree> {
    /// Keys whose records die, or (`revive`) come back.
    pub flips: &'a [T::Key],
    pub revive: bool,
    /// New records at the keys from `run_from` on, one after another:
    /// they come after every record there is.
    pub run: &'a [T::Record],
    pub run_from: u128,
    /// Records put at their keys: with `true` in place of the record
    /// there, which there must be; with `false` where there must be none.
    pub puts: &'a [(T::Key, T::Record, bool)],
    /// Keys whose records are removed.
    pub removes: &'a [T::Key],
    /// Every record at this key or after is removed.
    pub truncate: u128,
}

impl<T: Tree> Clone for Edits<'_, T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<T: Tree> Copy for Edits<'_, T> {}

impl<'a, T: Tree> Edits<'a, T> {
    /// No change.
    pub fn none() -> Edits<'a, T> {
        Edits { flips: &[], revive: false, run: &[], run_from: 0, puts: &[], removes: &[], truncate: u128::MAX }
    }

    /// The part that falls in `base..base + 2^height`.
    fn within(&self, base: u128, height: u32) -> Edits<'a, T> {
        let last = last_key(base, height);
        let cut = |keys: &'a [T::Key]| -> &'a [T::Key] {
            let from = keys.partition_point(|k| (*k).into() < base);
            let to = keys.partition_point(|k| (*k).into() <= last);
            &keys[from..to]
        };
        let run_end = self.run_from + self.run.len() as u128;
        let lo = self.run_from.max(base).min(run_end);
        let hi = run_end.min(last.saturating_add(1)).max(lo);
        let from = self.puts.partition_point(|p| p.0.into() < base);
        let to = self.puts.partition_point(|p| p.0.into() <= last);
        Edits {
            flips: cut(self.flips),
            revive: self.revive,
            run: &self.run[(lo - self.run_from) as usize..(hi - self.run_from) as usize],
            run_from: lo,
            puts: &self.puts[from..to],
            removes: cut(self.removes),
            truncate: self.truncate,
        }
    }

    /// How much there is to do: the keys it names.
    fn weight(&self) -> usize {
        self.flips.len() + self.run.len() + self.puts.len() + self.removes.len()
    }

    /// Whether there is nothing to do under `child`, of `height` levels
    /// from `base`: nothing of it falls there, or all that does is the
    /// removal of what an empty subtree does not have.
    fn idle(&self, child: Child, base: u128, height: u32) -> bool {
        self.is_empty(base, height) || (child == Child::Empty && self.weight() == 0)
    }

    /// Whether nothing of it falls in `base..base + 2^height`: `self` is
    /// already cut down to that.
    fn is_empty(&self, base: u128, height: u32) -> bool {
        self.flips.is_empty()
            && self.run.is_empty()
            && self.puts.is_empty()
            && self.removes.is_empty()
            && (self.truncate == u128::MAX || self.truncate > last_key(base, height))
    }
}

/// A sweep under way.
struct Sweep {
    /// The key it has reached.
    from: u128,
    /// Records it may still look at.
    budget: usize,
    /// A leaf whose last spend is below this height has nothing dead
    /// that could still be wanted back.
    horizon: u32,
}

/// Leaves whose records together number no more than this are made one
/// when a pass is by: well under a full page, so that the one leaf does
/// not at once become several again.
const MERGE: usize = LEAF_RECORDS * 3 / 4;

/// What becomes of a run of a node's slots when records are placed in
/// it: a leaf over the whole run, or (of a single slot) a node below.
struct Placed {
    slot: usize,
    span: u32,
    /// The records, as a range of those placed.
    from: usize,
    to: usize,
}

/// One pass over the trie, inside a transaction.
struct Pass<'t, 'f, T: Tree, B: Backend> {
    txn: &'t Txn<'f, B>,
    /// The height of the block the pass applies, or of the tip a pass
    /// that undoes one leaves.
    height: u32,
    /// The change in the number of live records.
    count: i64,
    /// The weights of the records marked dead.
    weight: u128,
    slots: Vec<Slot<T::Record>>,
    out: Vec<u8>,
    /// The level whose subtrees' parts are kept as they were before the
    /// pass changed them, if any is.
    capture: Option<u32>,
    /// Those parts, by index at that level: `None` where there was
    /// nothing.
    before: Vec<(u128, Option<Part>)>,
}

impl<'t, 'f, T: Tree, B: Backend> Pass<'t, 'f, T, B> {
    fn new(txn: &'t Txn<'f, B>, height: u32, capture: Option<u32>) -> Self {
        Pass { txn, height, count: 0, weight: 0, slots: Vec::new(), out: Vec::new(), capture, before: Vec::new() }
    }

    /// Keeps the parts at the captured level that `edits` reach in a
    /// leaf (or an empty subtree) of `covers` levels from `at`, whose
    /// records are `slots`, as they are before the edits. `whole` is the
    /// leaf's own part, which is the answer when it is one such subtree.
    fn keep_before(&mut self, slots: &[Slot<T::Record>], covers: u32, whole: Option<Part>, edits: Edits<'_, T>) {
        let Some(level) = self.capture.filter(|l| covers >= *l) else { return };
        // The subtrees the edits fall in, ascending.
        let mut touched: Vec<u128> = edits.flips.iter().chain(edits.removes).map(|k| (*k).into() >> level).collect();
        touched.extend(edits.puts.iter().map(|p| p.0.into() >> level));
        if !edits.run.is_empty() {
            touched.extend(edits.run_from >> level..=(edits.run_from + edits.run.len() as u128 - 1) >> level);
        }
        touched.sort_unstable();
        touched.dedup();
        for index in touched {
            let part = if covers == level {
                whole
            } else {
                let from = slots.partition_point(|s| s.key >> level < index);
                let to = slots.partition_point(|s| s.key >> level <= index);
                leaf_part::<T>(&slots[from..to], level)
            };
            self.before.push((index, part));
        }
    }

    /// The subtree `child` (of `height` levels from `base`) after `edits`,
    /// on up to `threads` threads.
    fn update(
        &mut self,
        child: Child,
        height: u32,
        base: u128,
        edits: Edits<'_, T>,
        threads: usize,
    ) -> Result<Child, Error> {
        if edits.idle(child, base, height) {
            return Ok(child);
        }
        let Child::Node { page, .. } = child else { return self.update_leaf(child, height, base, edits, threads) };
        let mut children = load_node(self.txn, page, height)?;
        let touched = self.update_children(&mut children, height, base, edits, threads)?;
        self.txn.free(page);
        // Where pages were written, leaves that have become few are made one.
        if let Some(leaf) = self.compact(&mut children, 0, height - below(height), touched, height, base)? {
            return Ok(leaf);
        }
        if children.iter().all(|c| *c == Child::Empty) {
            return Ok(Child::Empty);
        }
        self.write_node(&children, height, base)
    }

    /// Updates each child of a node that `edits` reaches. Returns which
    /// slots had pages written (a bit each).
    fn update_children(
        &mut self,
        children: &mut [Child; FANOUT],
        height: u32,
        base: u128,
        edits: Edits<'_, T>,
        threads: usize,
    ) -> Result<u32, Error> {
        let low = below(height);
        let slots = 1usize << (height - low);
        // The children there are, each with what of the edits is its.
        let mut groups: [(usize, u32); FANOUT] = [(0, 0); FANOUT];
        let mut n = 0;
        let mut k = 0;
        while k < slots {
            let span = span_of(children[k]);
            let at = base + ((k as u128) << low);
            if !edits.within(at, low + span).idle(children[k], at, low + span) {
                groups[n] = (k, span);
                n += 1;
            }
            k += 1 << span;
        }
        let groups = &groups[..n];
        let mut touched = 0u32;
        // Split where the node branches widely, so that every thread has
        // a child to itself: where it does not, the children are taken
        // in turn and the split is left to the nodes below.
        if threads >= 2 && n >= threads.min(FANOUT / 2) && edits.weight() >= SPLIT {
            // Each worker takes the next child not yet taken, and is a
            // pass of its own; the threads are shared out below it.
            let workers = threads.min(n);
            let next = std::sync::atomic::AtomicUsize::new(0);
            let (txn, height_now, kids) = (self.txn, self.height, &*children);
            type Done = Vec<(usize, u32, Result<([Child; FANOUT], bool), Error>)>;
            type Before = Vec<(u128, Option<Part>)>;
            let capture = self.capture;
            let done: Vec<((i64, u128), Before, Done)> = std::thread::scope(|scope| {
                let handles: Vec<_> = (0..workers)
                    .map(|_| {
                        scope.spawn(|| {
                            let mut pass = Pass::<T, B>::new(txn, height_now, capture);
                            let mut made: Done = Vec::new();
                            loop {
                                let i = next.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                                let Some(&(k, span)) = groups.get(i) else {
                                    return ((pass.count, pass.weight), pass.before, made);
                                };
                                let mut mine = *kids;
                                let did = pass.update_group(&mut mine, k, span, height, base, edits, threads / workers);
                                made.push((k, span, did.map(|t| (mine, t))));
                            }
                        })
                    })
                    .collect();
                handles.into_iter().map(|h| h.join().expect("a pass does not panic")).collect()
            });
            // The first fault in key order is the one reported, as when
            // one thread does it all.
            let mut made: Done = Vec::with_capacity(n);
            for ((count, weight), before, part) in done {
                self.count += count;
                self.weight += weight;
                self.before.extend(before);
                made.extend(part);
            }
            made.sort_by_key(|m| m.0);
            for (k, span, did) in made {
                let (mine, wrote) = did?;
                children[k..k + (1 << span)].copy_from_slice(&mine[k..k + (1 << span)]);
                touched |= (wrote as u32) << k;
            }
        } else {
            for &(k, span) in groups {
                touched |= (self.update_group(children, k, span, height, base, edits, threads)? as u32) << k;
            }
        }
        Ok(touched)
    }

    /// Updates the child at slot `k` of a node (of `height` levels from
    /// `base`), which covers `2^span` slots: only those slots of
    /// `children` are changed. Returns whether a page was written there.
    #[allow(clippy::too_many_arguments)]
    fn update_group(
        &mut self,
        children: &mut [Child; FANOUT],
        k: usize,
        span: u32,
        height: u32,
        base: u128,
        edits: Edits<'_, T>,
        threads: usize,
    ) -> Result<bool, Error> {
        let low = below(height);
        let (at, covers) = (base + ((k as u128) << low), low + span);
        let edits = edits.within(at, covers);
        if let Child::Node { .. } = children[k] {
            if self.capture == Some(low) {
                self.before.push((at >> low, children[k].part()));
            }
            children[k] = self.update(children[k], low, at, edits, threads)?;
            return Ok(true);
        }
        let mut slots = std::mem::take(&mut self.slots);
        let done = (|| {
            let old = self.gather(children[k], covers, at, &mut slots)?;
            self.keep_before(&slots, covers, children[k].part(), edits);
            let (rewrite, last_spend) = self.edit(&mut slots, old.map_or(0, |o| o.1), edits)?;
            if let (Some((page, _)), false) = (old, rewrite) {
                // Only the bits changed: the page stands.
                children[k] = Child::Leaf {
                    page,
                    part: leaf_part::<T>(&slots, covers),
                    records: slots.len() as u8,
                    live: live_bits(&slots),
                    last_spend,
                    span: span as u8,
                };
                return Ok(false);
            }
            if let Some((page, _)) = old {
                self.txn.free(page);
            }
            children[k] = Child::Empty;
            self.place(children, k, span, &slots, height, base, last_spend, threads)?;
            Ok(true)
        })();
        self.slots = slots;
        done
    }

    /// The records of the leaf `child` (of `height` levels from `base`)
    /// into `slots`, which is emptied first; its page and last spend, if
    /// it is a leaf.
    fn gather(
        &mut self,
        child: Child,
        height: u32,
        base: u128,
        slots: &mut Vec<Slot<T::Record>>,
    ) -> Result<Option<(Extent, u32)>, Error> {
        slots.clear();
        let Child::Leaf { page, records, live, last_spend, .. } = child else { return Ok(None) };
        let mut buf = [0u8; PAGE];
        read_leaf::<T>(self.txn.read(page, &mut buf)?, base, height, records, live, slots)?;
        Ok(Some((page, last_spend)))
    }

    fn write_node(&mut self, children: &[Child; FANOUT], height: u32, base: u128) -> Result<Child, Error> {
        write_node(children, height, &mut self.out);
        let page = self.txn.write(&self.out)?;
        Ok(Child::Node { page, part: node_part::<T>(children, height, base) })
    }

    /// A leaf that is the whole of its subtree (the root's, or one a
    /// pass reaches with no node above), or an empty subtree, after
    /// `edits`.
    fn update_leaf(
        &mut self,
        child: Child,
        height: u32,
        base: u128,
        edits: Edits<'_, T>,
        threads: usize,
    ) -> Result<Child, Error> {
        let mut slots = std::mem::take(&mut self.slots);
        let done = (|| {
            let old = self.gather(child, height, base, &mut slots)?;
            self.keep_before(&slots, height, child.part(), edits);
            let (rewrite, last_spend) = self.edit(&mut slots, old.map_or(0, |o| o.1), edits)?;
            if let (Some((page, _)), false) = (old, rewrite) {
                return Ok(Child::Leaf {
                    page,
                    part: leaf_part::<T>(&slots, height),
                    records: slots.len() as u8,
                    live: live_bits(&slots),
                    last_spend,
                    span: 0,
                });
            }
            if let Some((page, _)) = old {
                self.txn.free(page);
            }
            self.build(&slots, height, base, last_spend, threads)
        })();
        self.slots = slots;
        done
    }

    /// Makes `edits` to the records of one leaf. Returns whether its page
    /// must be written anew (anything but bits changed), and its last
    /// spend after them.
    fn edit(
        &mut self,
        slots: &mut Vec<Slot<T::Record>>,
        mut last_spend: u32,
        edits: Edits<'_, T>,
    ) -> Result<(bool, u32), Error> {
        for k in edits.flips {
            let key: u128 = (*k).into();
            match slots.binary_search_by_key(&key, |s| s.key).ok().map(|i| &mut slots[i]) {
                Some(s) if s.live != edits.revive => {
                    s.live = edits.revive;
                    self.count += if edits.revive { 1 } else { -1 };
                    if !edits.revive {
                        self.weight += T::weight(&s.record) as u128;
                    }
                }
                _ => return Err(T::refuse(key, if edits.revive { Fault::NotDead } else { Fault::NotLive })),
            }
        }
        if !edits.flips.is_empty() {
            last_spend = if edits.revive { last_spend.min(self.height) } else { self.height };
        }
        let mut rewrite = false;
        let keep = slots.partition_point(|s| s.key < edits.truncate || edits.truncate == u128::MAX);
        if keep < slots.len() {
            self.count -= slots[keep..].iter().filter(|s| s.live).count() as i64;
            slots.truncate(keep);
            rewrite = true;
        }
        for k in edits.removes {
            let key: u128 = (*k).into();
            let i = slots.binary_search_by_key(&key, |s| s.key).map_err(|_| T::refuse(key, Fault::Absent))?;
            self.count -= slots.remove(i).live as i64;
            rewrite = true;
        }
        for (k, record, replace) in edits.puts {
            let key: u128 = (*k).into();
            match (slots.binary_search_by_key(&key, |s| s.key), replace) {
                (Ok(i), true) => slots[i].record = *record,
                (Err(i), false) => {
                    slots.insert(i, Slot { key, record: *record, live: true });
                    self.count += 1;
                }
                (Ok(_), false) => return Err(T::refuse(key, Fault::Present)),
                (Err(_), true) => return Err(T::refuse(key, Fault::Absent)),
            }
            rewrite = true;
        }
        if !edits.run.is_empty() {
            if slots.last().is_some_and(|s| s.key >= edits.run_from) {
                return Err(T::refuse(edits.run_from, Fault::Order));
            }
            slots.extend(edits.run.iter().enumerate().map(|(i, r)| Slot {
                key: edits.run_from + i as u128,
                record: *r,
                live: true,
            }));
            self.count += edits.run.len() as i64;
            rewrite = true;
        }
        Ok((rewrite, last_spend))
    }

    /// Writes a leaf of `slots`, which fit one, covering `2^span` slots.
    fn write_leaf(
        &mut self,
        slots: &[Slot<T::Record>],
        height: u32,
        base: u128,
        last_spend: u32,
        span: u32,
    ) -> Result<Child, Error> {
        write_leaf::<T>(slots, base, &mut self.out);
        let page = self.txn.write(&self.out)?;
        // Only a leaf with something dead has a last spend.
        let last_spend = if slots.iter().all(|s| s.live) { 0 } else { last_spend };
        Ok(Child::Leaf {
            page,
            part: leaf_part::<T>(slots, height),
            records: slots.len() as u8,
            live: live_bits(slots),
            last_spend,
            span: span as u8,
        })
    }

    /// How `slots` (all under the `2^span` slots from `slot` of a node
    /// of `height` levels from `base`) are to lie there: as one leaf over
    /// the run if they fit, else halved and halved again, down to a node
    /// below a single slot. `offset` is where `slots` begin among the
    /// records being placed.
    #[allow(clippy::too_many_arguments)]
    fn plan(
        slots: &[Slot<T::Record>],
        offset: usize,
        slot: usize,
        span: u32,
        height: u32,
        base: u128,
        out: &mut Vec<Placed>,
    ) {
        if slots.is_empty() {
            return;
        }
        let low = below(height);
        let at = base + ((slot as u128) << low);
        if span == 0 || fits::<T>(slots, at) {
            return out.push(Placed { slot, span, from: offset, to: offset + slots.len() });
        }
        let half = slot + (1 << (span - 1));
        let mid = slots.partition_point(|s| s.key < base + ((half as u128) << low));
        Self::plan(&slots[..mid], offset, slot, span - 1, height, base, out);
        Self::plan(&slots[mid..], offset + mid, half, span - 1, height, base, out);
    }

    /// Places `slots` in the `2^span` slots from `slot` of a node, which
    /// are empty: as few leaves as hold them, and nodes below where one
    /// slot's records are more than a leaf's. Many records (a state being
    /// installed) are placed on up to `threads` threads.
    #[allow(clippy::too_many_arguments)]
    fn place(
        &mut self,
        children: &mut [Child; FANOUT],
        slot: usize,
        span: u32,
        slots: &[Slot<T::Record>],
        height: u32,
        base: u128,
        last_spend: u32,
        threads: usize,
    ) -> Result<(), Error> {
        let mut plan = Vec::new();
        Self::plan(slots, 0, slot, span, height, base, &mut plan);
        let low = below(height);
        let make = |pass: &mut Self, p: &Placed, threads: usize| -> Result<Child, Error> {
            let (part, at) = (&slots[p.from..p.to], base + ((p.slot as u128) << low));
            if fits::<T>(part, at) {
                pass.write_leaf(part, low + p.span, at, last_spend, p.span)
            } else {
                pass.build(part, low, at, last_spend, threads)
            }
        };
        if threads >= 2 && plan.len() >= 2 && slots.len() >= 8 * SPLIT {
            let workers = threads.min(plan.len());
            let next = std::sync::atomic::AtomicUsize::new(0);
            let (txn, height_now, plan) = (self.txn, self.height, &plan);
            let made: Vec<Vec<(usize, Result<Child, Error>)>> = std::thread::scope(|scope| {
                let handles: Vec<_> = (0..workers)
                    .map(|_| {
                        scope.spawn(|| {
                            let mut pass = Pass::<T, B>::new(txn, height_now, None);
                            let mut made = Vec::new();
                            loop {
                                let i = next.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                                let Some(p) = plan.get(i) else { return made };
                                made.push((p.slot, make(&mut pass, p, threads / workers)));
                            }
                        })
                    })
                    .collect();
                handles.into_iter().map(|h| h.join().expect("a pass does not panic")).collect()
            });
            for (k, child) in made.into_iter().flatten() {
                children[k] = child?;
            }
        } else {
            for p in &plan {
                children[p.slot] = make(self, p, threads)?;
            }
        }
        Ok(())
    }

    /// The subtree of `height` levels from `base` holding `slots`, all
    /// of it written anew: a leaf if they fit one, else a node.
    fn build(
        &mut self,
        slots: &[Slot<T::Record>],
        height: u32,
        base: u128,
        last_spend: u32,
        threads: usize,
    ) -> Result<Child, Error> {
        if slots.is_empty() {
            return Ok(Child::Empty);
        }
        if fits::<T>(slots, base) {
            return self.write_leaf(slots, height, base, last_spend, 0);
        }
        // Keys differ, so a subtree of one key always fits.
        assert!(height > 0, "records of one key do not fit a page");
        let low = below(height);
        let top = height - low;
        let mut children = [Child::Empty; FANOUT];
        // The two halves of the node, each placed as it fits.
        let half = 1usize << (top - 1);
        let mid = slots.partition_point(|s| s.key < base + ((half as u128) << low));
        if top == 1 {
            // A node of two slots: each is a node or a leaf of its own.
            children[0] = self.build(&slots[..mid], low, base, last_spend, threads)?;
            children[1] = self.build(&slots[mid..], low, base + (1u128 << low), last_spend, threads)?;
        } else {
            self.place(&mut children, 0, top - 1, &slots[..mid], height, base, last_spend, threads)?;
            self.place(&mut children, half, top - 1, &slots[mid..], height, base, last_spend, threads)?;
        }
        self.write_node(&children, height, base)
    }

    /// Makes one leaf of the leaves in the `2^span` slots from `slot`,
    /// where a slot in `touched` is among them and their records are few
    /// enough; else looks at each half. If the whole node (`span` its
    /// every slot) becomes one leaf, that leaf is returned, to stand in
    /// the node's place; else the slots are changed.
    fn compact(
        &mut self,
        children: &mut [Child; FANOUT],
        slot: usize,
        span: u32,
        touched: u32,
        height: u32,
        base: u128,
    ) -> Result<Option<Child>, Error> {
        let run = slot..slot + (1 << span);
        if touched >> slot & ((1u32 << (1 << span)) - 1) == 0 {
            return Ok(None);
        }
        let (mut leaves, mut records, mut blocked) = (0, 0usize, false);
        for c in &children[run.clone()] {
            match c {
                Child::Empty => {}
                Child::Leaf { records: n, .. } => {
                    leaves += 1;
                    records += *n as usize;
                }
                Child::Node { .. } => blocked = true,
            }
        }
        let low = below(height);
        let top = height - low;
        let at = base + ((slot as u128) << low);
        if !blocked && records <= MERGE && (leaves >= 2 || (leaves == 1 && span == top)) {
            // Their records, in key order.
            let mut all: Vec<Slot<T::Record>> = Vec::with_capacity(records);
            let mut last_spend = 0;
            let mut buf = [0u8; PAGE];
            let mut k = slot;
            while k < run.end {
                let child = children[k];
                if let Child::Leaf { page, records, live, last_spend: spent, span: s, .. } = child {
                    let leaf_at = base + ((k as u128) << low);
                    read_leaf::<T>(self.txn.read(page, &mut buf)?, leaf_at, low + s as u32, records, live, &mut all)?;
                    last_spend = last_spend.max(spent);
                }
                k += 1 << span_of(child);
            }
            if fits::<T>(&all, at) {
                for c in &mut children[run] {
                    if let Child::Leaf { page, .. } = *c {
                        self.txn.free(page);
                    }
                    *c = Child::Empty;
                }
                if span == top {
                    return self.write_leaf(&all, height, base, last_spend, 0).map(Some);
                }
                children[slot] = self.write_leaf(&all, low + span, at, last_spend, span)?;
                return Ok(None);
            }
        }
        if span > 0 {
            self.compact(children, slot, span - 1, touched, height, base)?;
            self.compact(children, slot + (1 << (span - 1)), span - 1, touched, height, base)?;
        }
        Ok(None)
    }

    /// Sweeps the subtree `child` from key `sweep.from` on, while the
    /// budget lasts. Returns the subtree after it.
    fn sweep(&mut self, child: Child, height: u32, base: u128, sweep: &mut Sweep) -> Result<Child, Error> {
        let end = base + (1u128 << height);
        if end <= sweep.from || sweep.budget == 0 {
            return Ok(child);
        }
        match child {
            Child::Empty => {
                sweep.from = end;
                Ok(child)
            }
            // A leaf with no node above it.
            Child::Leaf { .. } => match self.sweep_leaf(child, height, base, sweep)? {
                Some(slots) => {
                    let built = self.build(&slots, height, base, 0, 1);
                    self.slots = slots;
                    built
                }
                None => Ok(child),
            },
            Child::Node { page, .. } => {
                let mut children = load_node(self.txn, page, height)?;
                let low = below(height);
                let top = height - low;
                let mut touched = 0u32;
                let mut k = 0;
                while k < 1 << top {
                    let (c, span) = (children[k], span_of(children[k]));
                    let at = base + ((k as u128) << low);
                    match c {
                        Child::Leaf { .. } => {
                            if let Some(slots) = self.sweep_leaf(c, low + span, at, sweep)? {
                                children[k] = Child::Empty;
                                let placed = self.place(&mut children, k, span, &slots, height, base, 0, 1);
                                self.slots = slots;
                                placed?;
                                touched |= 1 << k;
                            }
                        }
                        _ => {
                            let swept = self.sweep(c, low, at, sweep)?;
                            touched |= ((swept != c) as u32) << k;
                            children[k] = swept;
                        }
                    }
                    k += 1 << span;
                }
                // Swept to its end, a node's leaves that have thinned are
                // made fewer, and a node thinned to one page becomes it.
                if sweep.from >= end {
                    let before = children;
                    if let Some(leaf) = self.compact(&mut children, 0, top, u32::MAX, height, base)? {
                        self.txn.free(page);
                        return Ok(leaf);
                    }
                    touched |= (before != children) as u32;
                }
                if touched == 0 {
                    return Ok(child);
                }
                self.txn.free(page);
                if children.iter().all(|c| *c == Child::Empty) {
                    return Ok(Child::Empty);
                }
                self.write_node(&children, height, base)
            }
        }
    }

    /// Looks at one leaf (of `height` levels from `base`) for the sweep.
    /// If what is dead in it is to be dropped, its page is freed and its
    /// live records are returned (none, if nothing in it is live), to be
    /// written anew by the caller; else `None`, and the leaf stands.
    fn sweep_leaf(
        &mut self,
        child: Child,
        height: u32,
        base: u128,
        sweep: &mut Sweep,
    ) -> Result<Option<Vec<Slot<T::Record>>>, Error> {
        let Child::Leaf { page, records, live, last_spend, .. } = child else { return Ok(None) };
        let end = base + (1u128 << height);
        if end <= sweep.from || sweep.budget == 0 {
            return Ok(None);
        }
        sweep.budget = sweep.budget.saturating_sub(records as usize);
        sweep.from = end;
        let dead = records as u32 - live.count_ones();
        // Everything dead here died before the horizon, and there is
        // enough of it to be worth a page.
        if dead == 0 || last_spend >= sweep.horizon || (live != 0 && dead * 4 < records as u32) {
            return Ok(None);
        }
        let mut slots = std::mem::take(&mut self.slots);
        slots.clear();
        if live != 0 {
            let mut buf = [0u8; PAGE];
            read_leaf::<T>(self.txn.read(page, &mut buf)?, base, height, records, live, &mut slots)?;
            slots.retain(|s| s.live);
        }
        self.txn.free(page);
        Ok(Some(slots))
    }
}

/// The trie of root `root` after `edits`, made at block `height`, and
/// the change in the number of its live records.
pub fn update<T: Tree, B: Backend>(
    txn: &Txn<'_, B>,
    root: Child,
    height: u32,
    edits: Edits<'_, T>,
) -> Result<(Child, i64), Error> {
    update_on(txn, root, height, edits, crate::parallel::threads())
}

/// [`update`] on up to `threads` threads: the result is the same on any
/// number.
pub fn update_on<T: Tree, B: Backend>(
    txn: &Txn<'_, B>,
    root: Child,
    height: u32,
    edits: Edits<'_, T>,
    threads: usize,
) -> Result<(Child, i64), Error> {
    let mut pass = Pass::<T, B>::new(txn, height, None);
    let root = pass.update(root, T::HEIGHT, 0, edits.within(0, T::HEIGHT), threads)?;
    Ok((root, pass.count))
}

/// The parts of the subtrees at one level that a pass changed, as they
/// were before it: `(index, part)`, ascending, `None` where nothing was.
pub type Before = Vec<(u128, Option<Part>)>;

/// [`update`], which also returns the weights of the records marked
/// dead, added up, and the part of every subtree at `level`
/// the edits reach, as it was before them: what takes a tree's parts
/// back to an earlier state. `level` is one at which nodes' slots lie.
pub fn update_keeping<T: Tree, B: Backend>(
    txn: &Txn<'_, B>,
    root: Child,
    height: u32,
    edits: Edits<'_, T>,
    level: u32,
) -> Result<(Child, i64, Before, u128), Error> {
    debug_assert!(level <= T::HEIGHT && (T::HEIGHT - level).is_multiple_of(BITS));
    debug_assert!(edits.truncate == u128::MAX, "a pass that removes a tail keeps nothing");
    let mut pass = Pass::<T, B>::new(txn, height, Some(level));
    let root = pass.update(root, T::HEIGHT, 0, edits.within(0, T::HEIGHT), crate::parallel::threads())?;
    let mut before = pass.before;
    before.sort_unstable_by_key(|b| b.0);
    Ok((root, pass.count, before, pass.weight))
}

/// Sweeps part of the trie: from key `from`, looks at leaves holding up
/// to `budget` records and drops what is dead in them if all of it died before
/// `horizon` and it is a quarter of the leaf or more; and where leaves
/// have thinned, makes fewer of them. Returns the root, whose part is as
/// it was, and the key the sweep reached.
pub fn sweep<T: Tree, B: Backend>(
    txn: &Txn<'_, B>,
    root: Child,
    from: u128,
    budget: usize,
    horizon: u32,
) -> Result<(Child, u128), Error> {
    let mut pass = Pass::<T, B>::new(txn, 0, None);
    let mut state = Sweep { from, budget, horizon };
    let swept = pass.sweep(root, T::HEIGHT, 0, &mut state)?;
    debug_assert_eq!(swept.part(), root.part(), "a sweep changes no hash");
    Ok((swept, state.from))
}

/// The children of the node in `page`, of `height` levels.
pub fn load_node(pages: &impl ReadPages, page: Extent, height: u32) -> io::Result<[Child; FANOUT]> {
    let mut buf = [0u8; PAGE];
    read_node(pages.read_page(page, &mut buf)?, height)
}

/// The records of the leaf `child`, of `height` levels from `base`; none
/// if it is not a leaf.
pub fn load_leaf<T: Tree>(
    pages: &impl ReadPages,
    child: Child,
    height: u32,
    base: u128,
) -> io::Result<Vec<Slot<T::Record>>> {
    let Child::Leaf { page, records, live, .. } = child else { return Ok(Vec::new()) };
    let mut slots = Vec::with_capacity(records as usize);
    let mut buf = [0u8; PAGE];
    read_leaf::<T>(pages.read_page(page, &mut buf)?, base, height, records, live, &mut slots)?;
    Ok(slots)
}

/// A step of the way down to a key.
pub enum Step<'a, T: Tree> {
    /// A node of `height` levels from `base`, and its children.
    Node { height: u32, base: u128, children: &'a [Child; FANOUT] },
    /// The leaf the way ends in, of `height` levels from `base`, and its
    /// records.
    Leaf { height: u32, base: u128, slots: &'a [Slot<T::Record>] },
    /// The empty subtree the way ends in.
    Empty { height: u32, base: u128 },
}

/// Goes down from `root` to `key`, calling `f` with each step.
pub fn walk_to<T: Tree>(
    pages: &impl ReadPages,
    root: Child,
    key: u128,
    f: &mut dyn FnMut(Step<'_, T>),
) -> io::Result<()> {
    let (mut child, mut height, mut base) = (root, T::HEIGHT, 0u128);
    loop {
        match child {
            Child::Empty => {
                f(Step::Empty { height, base });
                return Ok(());
            }
            Child::Node { page, .. } => {
                let children = load_node(pages, page, height)?;
                f(Step::Node { height, base, children: &children });
                let low = below(height);
                let (k, span) = group_of(&children, height, ((key - base) >> low) as usize);
                child = children[k];
                base += (k as u128) << low;
                height = low + span;
            }
            Child::Leaf { .. } => {
                let slots = load_leaf::<T>(pages, child, height, base)?;
                f(Step::Leaf { height, base, slots: &slots });
                return Ok(());
            }
        }
    }
}

/// The record at `key` and whether it is live; `None` if none is kept.
pub fn get<T: Tree>(pages: &impl ReadPages, root: Child, key: u128) -> io::Result<Option<(T::Record, bool)>> {
    let mut found = None;
    walk_to::<T>(pages, root, key, &mut |step| {
        if let Step::Leaf { slots, .. } = step {
            found = slots.iter().find(|s| s.key == key).map(|s| (s.record, s.live));
        }
    })?;
    Ok(found)
}

/// Marks every page of the trie in `file`'s map of free space, as must
/// be done when the file is opened. Reads the nodes, not the leaves, and
/// reads them many at a time: a large trie has millions.
pub fn mark<T: Tree, B: Backend>(file: &PageFile<B>, root: Child) -> io::Result<()> {
    /// Nodes read together.
    const BATCH: usize = 2048;
    // Nodes still to read, the deepest last: taken from the end, so that
    // the list stays short however many nodes there are.
    let mut todo: Vec<(Extent, u32)> = Vec::new();
    let see = |child: Child, height: u32, todo: &mut Vec<(Extent, u32)>| -> io::Result<()> {
        match child {
            Child::Empty => Ok(()),
            Child::Leaf { page, .. } => file.mark(page),
            Child::Node { page, .. } => {
                todo.push((page, height));
                file.mark(page)
            }
        }
    };
    see(root, T::HEIGHT, &mut todo)?;
    let mut bufs = vec![0u8; BATCH * PAGE];
    while !todo.is_empty() {
        let batch: Vec<(Extent, u32)> = todo.split_off(todo.len().saturating_sub(BATCH));
        let mut pages: Vec<(Extent, &mut [u8])> =
            batch.iter().zip(bufs.chunks_mut(PAGE)).map(|((e, _), buf)| (*e, buf)).collect();
        file.read_many(&mut pages)?;
        for ((e, height), buf) in batch.iter().zip(bufs.chunks(PAGE)) {
            let children = read_node(e.payload(buf)?, *height)?;
            for c in children {
                see(c, below(*height), &mut todo)?;
            }
        }
    }
    Ok(())
}

/// Calls `f` with every record kept, in key order: its key, the record
/// and whether it is live.
pub fn for_each<T: Tree>(
    pages: &impl ReadPages,
    root: Child,
    f: &mut dyn FnMut(u128, &T::Record, bool),
) -> io::Result<()> {
    for_each_under::<T>(pages, root, T::HEIGHT, 0, f)
}

/// [`for_each`] of the subtree `child`, of `height` levels from `base`.
fn for_each_under<T: Tree>(
    pages: &impl ReadPages,
    child: Child,
    height: u32,
    base: u128,
    f: &mut dyn FnMut(u128, &T::Record, bool),
) -> io::Result<()> {
    match child {
        Child::Empty => Ok(()),
        Child::Leaf { .. } => {
            load_leaf::<T>(pages, child, height, base)?.iter().for_each(|s| f(s.key, &s.record, s.live));
            Ok(())
        }
        Child::Node { page, .. } => {
            let children = load_node(pages, page, height)?;
            let low = below(height);
            for (k, c) in children.iter().enumerate() {
                for_each_under::<T>(pages, *c, low + span_of(*c), base + ((k as u128) << low), f)?;
            }
            Ok(())
        }
    }
}

/// Frees every page of the trie under `root`: the tree is no more. The
/// nodes are read, the leaves are not.
pub fn free<T: Tree, B: Backend>(txn: &Txn<'_, B>, root: Child) -> io::Result<()> {
    fn under<B: Backend>(txn: &Txn<'_, B>, child: Child, height: u32) -> io::Result<()> {
        match child {
            Child::Empty => Ok(()),
            Child::Leaf { page, .. } => {
                txn.free(page);
                Ok(())
            }
            Child::Node { page, .. } => {
                for c in load_node(txn, page, height)? {
                    under(txn, c, below(height))?;
                }
                txn.free(page);
                Ok(())
            }
        }
    }
    under(txn, root, T::HEIGHT)
}

/// The least key kept that is `from` or more.
pub fn next_key<T: Tree>(pages: &impl ReadPages, root: Child, from: u128) -> io::Result<Option<u128>> {
    fn under<T: Tree>(
        pages: &impl ReadPages,
        child: Child,
        height: u32,
        base: u128,
        from: u128,
    ) -> io::Result<Option<u128>> {
        match child {
            Child::Empty => Ok(None),
            Child::Leaf { .. } => {
                Ok(load_leaf::<T>(pages, child, height, base)?.iter().map(|s| s.key).find(|k| *k >= from))
            }
            Child::Node { page, .. } => {
                let children = load_node(pages, page, height)?;
                let low = below(height);
                for (k, c) in children.iter().enumerate() {
                    let (at, covers) = (base + ((k as u128) << low), low + span_of(*c));
                    // All of it before `from`: not read.
                    if at + ((1u128 << covers) - 1) < from {
                        continue;
                    }
                    if let Some(key) = under::<T>(pages, *c, covers, at, from)? {
                        return Ok(Some(key));
                    }
                }
                Ok(None)
            }
        }
    }
    under::<T>(pages, root, T::HEIGHT, 0, from)
}

/// Calls `f` with the part of every nonempty subtree at `level`, in key
/// order: its index there and its part. Reads the nodes above the level,
/// and the leaves that cover more than one such subtree.
pub fn parts_at<T: Tree>(
    pages: &impl ReadPages,
    root: Child,
    level: u32,
    f: &mut dyn FnMut(u128, Part),
) -> io::Result<()> {
    fn walk<T: Tree>(
        pages: &impl ReadPages,
        child: Child,
        height: u32,
        base: u128,
        level: u32,
        f: &mut dyn FnMut(u128, Part),
    ) -> io::Result<()> {
        match child {
            Child::Empty => Ok(()),
            _ if height == level => {
                if let Some(part) = child.part() {
                    f(base >> level, part);
                }
                Ok(())
            }
            // A leaf over several of them: each from its own records.
            Child::Leaf { .. } => {
                let slots = load_leaf::<T>(pages, child, height, base)?;
                for group in slots.chunk_by(|a, b| a.key >> level == b.key >> level) {
                    if let Some(part) = leaf_part::<T>(group, level) {
                        f(group[0].key >> level, part);
                    }
                }
                Ok(())
            }
            Child::Node { page, .. } => {
                let children = load_node(pages, page, height)?;
                let low = below(height);
                for (k, c) in children.iter().enumerate() {
                    walk::<T>(pages, *c, low + span_of(*c), base + ((k as u128) << low), level, f)?;
                }
                Ok(())
            }
        }
    }
    debug_assert!(level <= T::HEIGHT && (T::HEIGHT - level).is_multiple_of(BITS));
    walk::<T>(pages, root, T::HEIGHT, 0, level, f)
}

/// Calls `f` with every record kept in the subtree of index `index` at
/// `level`, in key order: its key, the record and whether it is live.
pub fn for_each_in<T: Tree>(
    pages: &impl ReadPages,
    root: Child,
    level: u32,
    index: u128,
    f: &mut dyn FnMut(u128, &T::Record, bool),
) -> io::Result<()> {
    let (from, to) = (index << level, last_key(index << level, level));
    let (mut child, mut height, mut base) = (root, T::HEIGHT, 0u128);
    // Down to the child that holds the subtree, or is it.
    while height > level {
        let Child::Node { page, .. } = child else { break };
        let children = load_node(pages, page, height)?;
        let low = below(height);
        let (k, span) = group_of(&children, height, ((from - base) >> low) as usize);
        (child, height, base) = (children[k], low + span, base + ((k as u128) << low));
    }
    for_each_under::<T>(pages, child, height, base, &mut |key, record, live| {
        if (from..=to).contains(&key) {
            f(key, record, live);
        }
    })
}
