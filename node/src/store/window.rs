//! The window: for each of the last blocks, what is needed to undo it.
//!
//! A block spends outputs and makes outputs. Undoing it unspends the
//! first and removes the second, and the set of outputs keeps a spent
//! output's record ([`super::outputs`]), so all that must be kept of a
//! block is which positions it spent and where its own outputs began:
//! a few bytes a spend. Names are not spent but replaced, so for those a
//! block's record holds the records it replaced, and the keys of the
//! names it registered.
//!
//! A record also keeps what takes the state's parts back to the block
//! before: the root of every part of the outputs the block changed, as it
//! was, and the names' root as it was. With those and the spent
//! positions, the state as of any block of the window can be handed to
//! another node part by part ([`super::state`]). That is a block's record here, kept for the
//! window's length of blocks and then dropped.
//!
//! The records are pages of the state's file like any others, written in
//! the block's transaction and reached from the root record through one
//! page that lists them. Only that list is held in memory (sixteen bytes
//! a block); a record is read when its block is undone. A record too
//! long for one page is cut into pages, and its first page lists them:
//! a file opened finds a record's pages by one page read, and reads
//! none of what is long.
//!
//! ```text
//! first page  := 0 | record, if it fits; else 1 | page (6) ...
//! record      := height (4) | block (32) | block before (32)
//!                | first new position (8) | spends (4) | distance (varint) ...
//!                | names registered (2) | key (16) ...
//!                | names replaced (2) | the record replaced ...
//!                | names' root before (32)
//!                | names' parts changed (2) | (index (4) | kind (1) | hash before (32)) ...
//!                | parts changed (4) | (index (4) | was there (1) | root before (32)) ...
//!                | commits spent (2) | (position (8) | hash (32) | height (4)) ...
//! list page   := blocks (2) | (height (4) | first page (6)) ...
//! ```

use std::collections::VecDeque;
use std::io;

use super::backend::Backend;
use super::commits::Commit;
use super::pagefile::{Extent, MAX_UNITS, PageFile, ReadPages, Txn, UNIT};
use super::trie::Part;
use crate::hash::Digest;
use crate::hash::{digest_from_bytes, digest_to_bytes};
use crate::name::{KEY_BITS, Key, Record as NameRecord};

/// Bytes of a name's key.
const KEY_BYTES: usize = KEY_BITS / 8;

/// The most blocks a window holds: what one page lists.
pub const MAX_BLOCKS: usize = (Extent::capacity(MAX_UNITS) - 2) / 10;
/// Bytes of a record a page holds.
const CHUNK: usize = Extent::capacity(MAX_UNITS);
const NONE: Extent = Extent { start: 0, units: 0 };
/// What a record's first page begins with: the record follows, whole.
const WHOLE: u8 = 0;
/// The same: the places of its pages follow.
const LISTED: u8 = 1;

fn corrupt(what: &'static str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, what)
}

fn put_extent(out: &mut Vec<u8>, e: Extent) {
    out.extend_from_slice(&e.start.to_le_bytes()[..5]);
    out.push(e.units as u8);
}

fn get_extent(b: &[u8]) -> Extent {
    let mut start = [0u8; 8];
    start[..5].copy_from_slice(&b[..5]);
    Extent { start: u64::from_le_bytes(start), units: b[5] as u32 }
}

/// What undoing a block needs.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct BlockRecord {
    pub height: u32,
    /// The block's id.
    pub block: Digest,
    /// The id of the block before it: the tip once this one is undone.
    pub before: Digest,
    /// The position its first new output took: the next position before
    /// it.
    pub first_new: u64,
    /// The positions it spent, ascending.
    pub spends: Vec<u64>,
    /// The keys of the names it registered, ascending.
    pub registered: Vec<Key>,
    /// The records it replaced, as they were, ascending by key.
    pub replaced: Vec<NameRecord>,
    /// The root of the names' tree before it.
    pub names_before: Digest,
    /// The part of each part of the names it changed, as it was before
    /// (`None` if the part had no name), ascending by index.
    pub names_parts_before: Vec<(u32, Option<Part>)>,
    /// The root of each part of the outputs it changed, as it was before
    /// (`None` if the part was empty), ascending by index.
    pub parts_before: Vec<(u64, Option<Digest>)>,
    /// The commits its reveals and sweeps spent, that the table of
    /// commits had: their positions and what they were.
    pub commits_spent: Vec<(u64, Commit)>,
}

impl BlockRecord {
    fn to_bytes(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(80 + 3 * self.spends.len());
        out.extend_from_slice(&self.height.to_le_bytes());
        out.extend_from_slice(&digest_to_bytes(&self.block));
        out.extend_from_slice(&digest_to_bytes(&self.before));
        out.extend_from_slice(&self.first_new.to_le_bytes());
        out.extend_from_slice(&(self.spends.len() as u32).to_le_bytes());
        let mut prev = 0;
        for p in &self.spends {
            let mut x = p - prev;
            while x >= 0x80 {
                out.push(x as u8 | 0x80);
                x >>= 7;
            }
            out.push(x as u8);
            prev = *p;
        }
        out.extend_from_slice(&(self.registered.len() as u16).to_le_bytes());
        for key in &self.registered {
            out.extend_from_slice(&key.to_le_bytes()[..KEY_BYTES]);
        }
        out.extend_from_slice(&(self.replaced.len() as u16).to_le_bytes());
        for r in &self.replaced {
            let at = out.len();
            out.resize(at + r.size(), 0);
            r.write_bytes(&mut out[at..]);
        }
        out.extend_from_slice(&digest_to_bytes(&self.names_before));
        out.extend_from_slice(&(self.names_parts_before.len() as u16).to_le_bytes());
        for (index, before) in &self.names_parts_before {
            out.extend_from_slice(&index.to_le_bytes());
            // Nothing, more names than one, or one.
            out.push(before.map_or(0, |p| 1 + p.single as u8));
            out.extend_from_slice(&digest_to_bytes(&before.map_or(crate::hash::EMPTY, |p| p.hash)));
        }
        out.extend_from_slice(&(self.parts_before.len() as u32).to_le_bytes());
        for (index, before) in &self.parts_before {
            out.extend_from_slice(&(*index as u32).to_le_bytes());
            out.push(before.is_some() as u8);
            out.extend_from_slice(&digest_to_bytes(&before.unwrap_or(crate::hash::EMPTY)));
        }
        out.extend_from_slice(&(self.commits_spent.len() as u16).to_le_bytes());
        for (position, commit) in &self.commits_spent {
            out.extend_from_slice(&position.to_le_bytes());
            commit.put(&mut out);
        }
        out
    }

    fn from_bytes(b: &[u8]) -> io::Result<BlockRecord> {
        let bad = || corrupt("a block's record is not one");
        let (head, mut b) = b.split_at_checked(80).ok_or_else(bad)?;
        let count = u32::from_le_bytes(head[76..80].try_into().unwrap()) as usize;
        if count > b.len() {
            return Err(bad());
        }
        let mut spends = Vec::with_capacity(count);
        let mut prev = 0u64;
        for i in 0..count {
            let (mut x, mut shift) = (0u64, 0);
            loop {
                let (&byte, rest) = b.split_first().ok_or_else(bad)?;
                b = rest;
                if shift > 56 {
                    return Err(bad());
                }
                x |= u64::from(byte & 0x7f) << shift;
                shift += 7;
                if byte < 0x80 {
                    break;
                }
            }
            // Positions ascend: no distance but the first is zero.
            if i > 0 && x == 0 {
                return Err(bad());
            }
            prev = prev.checked_add(x).ok_or_else(bad)?;
            spends.push(prev);
        }
        let count = |b: &mut &[u8]| -> io::Result<usize> {
            let (n, rest) = b.split_at_checked(2).ok_or_else(bad)?;
            *b = rest;
            Ok(u16::from_le_bytes([n[0], n[1]]) as usize)
        };
        let mut registered = Vec::new();
        for _ in 0..count(&mut b)? {
            let (k, rest) = b.split_at_checked(KEY_BYTES).ok_or_else(bad)?;
            let mut key = [0u8; 16];
            key[..KEY_BYTES].copy_from_slice(k);
            registered.push(Key::from_le_bytes(key));
            b = rest;
        }
        let mut replaced = Vec::new();
        for _ in 0..count(&mut b)? {
            let (r, rest) = NameRecord::read(b).ok_or_else(bad)?;
            replaced.push(r);
            b = rest;
        }
        let (names_before, mut b) = b.split_at_checked(32).ok_or_else(bad)?;
        let names_before = digest_from_bytes(names_before).ok_or_else(bad)?;
        let mut names_parts_before = Vec::new();
        for _ in 0..count(&mut b)? {
            let (entry, rest) = b.split_at_checked(37).ok_or_else(bad)?;
            let index = u32::from_le_bytes(entry[..4].try_into().unwrap());
            let hash = digest_from_bytes(&entry[5..]).ok_or_else(bad)?;
            if entry[4] > 2
                || names_parts_before.last().is_some_and(|p: &(u32, Option<Part>)| p.0 >= index)
                || (entry[4] == 0 && hash != crate::hash::EMPTY)
            {
                return Err(bad());
            }
            names_parts_before.push((index, (entry[4] > 0).then_some(Part { hash, single: entry[4] == 2 })));
            b = rest;
        }
        let (parts, mut b) = b.split_at_checked(4).ok_or_else(bad)?;
        let parts = u32::from_le_bytes(parts.try_into().unwrap()) as usize;
        if b.len() < parts * 37 {
            return Err(bad());
        }
        let mut parts_before = Vec::with_capacity(parts);
        for _ in 0..parts {
            let (entry, rest) = b.split_at(37);
            let index = u32::from_le_bytes(entry[..4].try_into().unwrap()) as u64;
            let hash = digest_from_bytes(&entry[5..]).ok_or_else(bad)?;
            // Parts ascend, and one that was not there has no root.
            if entry[4] > 1
                || parts_before.last().is_some_and(|p: &(u64, Option<Digest>)| p.0 >= index)
                || (entry[4] == 0 && hash != crate::hash::EMPTY)
            {
                return Err(bad());
            }
            parts_before.push((index, (entry[4] == 1).then_some(hash)));
            b = rest;
        }
        let spent = count(&mut b)?;
        if b.len() != spent * 44 {
            return Err(bad());
        }
        let commits_spent = b
            .chunks_exact(44)
            .map(|e| Some((u64::from_le_bytes(e[..8].try_into().unwrap()), Commit::get(&e[8..])?)))
            .collect::<Option<Vec<_>>>()
            .ok_or_else(bad)?;
        Ok(BlockRecord {
            commits_spent,
            names_before,
            names_parts_before,
            parts_before,
            registered,
            replaced,
            height: u32::from_le_bytes(head[..4].try_into().unwrap()),
            block: digest_from_bytes(&head[4..36]).ok_or_else(bad)?,
            before: digest_from_bytes(&head[36..68]).ok_or_else(bad)?,
            first_new: u64::from_le_bytes(head[68..76].try_into().unwrap()),
            spends,
        })
    }

    /// Writes the record as pages and returns the first.
    fn write<B: Backend>(&self, txn: &mut Txn<'_, B>) -> io::Result<Extent> {
        let bytes = self.to_bytes();
        let mut first = Vec::with_capacity(1 + bytes.len().min(CHUNK));
        if bytes.len() < CHUNK {
            first.push(WHOLE);
            first.extend_from_slice(&bytes);
        } else {
            first.push(LISTED);
            assert!(bytes.len().div_ceil(CHUNK) <= (CHUNK - 1) / 6, "a block's record is not hundreds of megabytes");
            for chunk in bytes.chunks(CHUNK) {
                put_extent(&mut first, txn.write(chunk)?);
            }
        }
        txn.write(&first)
    }

    /// Reads the record whose first page is `first`, and its pages.
    fn read(pages: &impl ReadPages, first: Extent) -> io::Result<(BlockRecord, Vec<Extent>)> {
        let mut bytes = Vec::new();
        let places = places(pages, first, Some(&mut bytes))?;
        Ok((BlockRecord::from_bytes(&bytes)?, places))
    }
}

/// The pages of the record whose first page is `first`, that one
/// among them; and the record's bytes, if `bytes` is given. With none,
/// only the first page is read.
fn places(pages: &impl ReadPages, first: Extent, bytes: Option<&mut Vec<u8>>) -> io::Result<Vec<Extent>> {
    let mut buf = vec![0u8; MAX_UNITS as usize * UNIT];
    let payload = pages.read_page(first, &mut buf)?;
    match payload.split_first() {
        Some((&WHOLE, record)) => {
            if let Some(bytes) = bytes {
                bytes.extend_from_slice(record);
            }
            Ok(vec![first])
        }
        Some((&LISTED, list)) if !list.is_empty() && list.len() % 6 == 0 => {
            let mut places = vec![first];
            places.extend(list.chunks_exact(6).map(get_extent));
            if places.iter().any(|e| e.units == 0 || e.units > MAX_UNITS) {
                return Err(corrupt("a record's page is not one"));
            }
            if let Some(bytes) = bytes {
                for place in &places[1..] {
                    bytes.extend_from_slice(pages.read_page(*place, &mut buf)?);
                }
            }
            Ok(places)
        }
        _ => Err(corrupt("a record's first page is not one")),
    }
}

/// The records of the last blocks, oldest first: the list in memory, the
/// records in the file.
#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct Window {
    blocks: VecDeque<(u32, Extent)>,
    /// The page the list is written in, if it is not empty.
    list: Option<Extent>,
}

impl Window {
    /// Bytes of a window's place in the root record: its list's page.
    pub const BYTES: usize = 6;

    pub fn len(&self) -> usize {
        self.blocks.len()
    }

    pub fn is_empty(&self) -> bool {
        self.blocks.is_empty()
    }

    /// The height of the oldest block that can be undone.
    pub fn oldest(&self) -> Option<u32> {
        self.blocks.front().map(|b| b.0)
    }

    pub fn to_bytes(&self) -> [u8; Self::BYTES] {
        let mut out = Vec::with_capacity(6);
        put_extent(&mut out, self.list.unwrap_or(NONE));
        out.try_into().unwrap()
    }

    /// Reads the window whose list's page the root record gives.
    pub fn read(pages: &impl ReadPages, b: &[u8]) -> io::Result<Window> {
        let bad = || corrupt("the window's list is not one");
        let list = get_extent(b.get(..6).ok_or_else(bad)?);
        if list.units == 0 {
            return Ok(Window::default());
        }
        let mut buf = vec![0u8; MAX_UNITS as usize * UNIT];
        let payload = pages.read_page(list, &mut buf)?;
        let (count, body) = payload.split_at_checked(2).ok_or_else(bad)?;
        let count = u16::from_le_bytes([count[0], count[1]]) as usize;
        if count == 0 || body.len() != 10 * count {
            return Err(bad());
        }
        let mut blocks = VecDeque::with_capacity(count);
        for e in body.chunks_exact(10) {
            let (height, page) = (u32::from_le_bytes(e[..4].try_into().unwrap()), get_extent(&e[4..]));
            // Heights follow one another.
            if page.units == 0 || blocks.back().is_some_and(|b: &(u32, Extent)| b.0 + 1 != height) {
                return Err(bad());
            }
            blocks.push_back((height, page));
        }
        Ok(Window { blocks, list: Some(list) })
    }

    /// Marks every page of the window in `file`'s map of free space.
    pub fn mark<B: Backend>(&self, file: &PageFile<B>) -> io::Result<()> {
        if let Some(list) = self.list {
            file.mark(list)?;
        }
        for (_, first) in &self.blocks {
            places(file, *first, None)?.into_iter().try_for_each(|e| file.mark(e))?;
        }
        Ok(())
    }

    /// Frees a record's pages.
    fn drop_record<B: Backend>(txn: &mut Txn<'_, B>, first: Extent) -> io::Result<()> {
        places(txn, first, None)?.into_iter().for_each(|e| txn.free(e));
        Ok(())
    }

    /// Drops every record: no block can be undone.
    pub fn clear<B: Backend>(&mut self, txn: &mut Txn<'_, B>) -> io::Result<()> {
        while let Some((_, first)) = self.blocks.pop_front() {
            Window::drop_record(txn, first)?;
        }
        self.write_list(txn)
    }

    /// Writes the list anew.
    fn write_list<B: Backend>(&mut self, txn: &mut Txn<'_, B>) -> io::Result<()> {
        if let Some(old) = self.list.take() {
            txn.free(old);
        }
        if self.blocks.is_empty() {
            return Ok(());
        }
        let mut page = Vec::with_capacity(2 + 10 * self.blocks.len());
        page.extend_from_slice(&(self.blocks.len() as u16).to_le_bytes());
        for (height, first) in &self.blocks {
            page.extend_from_slice(&height.to_le_bytes());
            put_extent(&mut page, *first);
        }
        self.list = Some(txn.write(&page)?);
        Ok(())
    }

    /// Adds the newest block's record, and drops those of blocks more
    /// than `keep` back.
    pub fn push<B: Backend>(&mut self, txn: &mut Txn<'_, B>, record: &BlockRecord, keep: usize) -> io::Result<()> {
        assert!(keep <= MAX_BLOCKS, "a window holds at most {MAX_BLOCKS} blocks");
        debug_assert!(self.blocks.back().is_none_or(|b| b.0 + 1 == record.height));
        if keep > 0 {
            let first = record.write(txn)?;
            self.blocks.push_back((record.height, first));
        }
        while self.blocks.len() > keep {
            let (_, first) = self.blocks.pop_front().unwrap();
            Window::drop_record(txn, first)?;
        }
        self.write_list(txn)
    }

    /// Takes the newest block's record out, to undo the block with:
    /// `None` if the window is empty.
    pub fn pop<B: Backend>(&mut self, txn: &mut Txn<'_, B>) -> io::Result<Option<BlockRecord>> {
        let Some((_, first)) = self.blocks.pop_back() else { return Ok(None) };
        let (record, chain) = BlockRecord::read(txn, first)?;
        chain.into_iter().for_each(|e| txn.free(e));
        self.write_list(txn)?;
        Ok(Some(record))
    }

    /// The record of the block at `height`, if the window has it.
    pub fn get(&self, pages: &impl ReadPages, height: u32) -> io::Result<Option<BlockRecord>> {
        let Some(oldest) = self.oldest() else { return Ok(None) };
        let Some((_, first)) = height.checked_sub(oldest).and_then(|i| self.blocks.get(i as usize)) else {
            return Ok(None);
        };
        Ok(Some(BlockRecord::read(pages, *first)?.0))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::store::testing::{Lost, MemBackend};
    use crate::test_util::Rng;

    fn record(rng: &mut Rng, height: u32, spends: usize) -> BlockRecord {
        let mut at = 0u64;
        let spends = (0..spends)
            .map(|i| {
                at += if i == 0 { rng.next_u64() % 3 } else { 1 + rng.next_u64() % 100_000 };
                at
            })
            .collect();
        BlockRecord {
            height,
            block: [(height) as u8; 32],
            before: [(height - 1) as u8; 32],
            first_new: rng.next_u64() >> 24,
            spends,
            registered: (0..height as u128 % 3).map(|i| (i + 1) << 100 | height as u128).collect(),
            replaced: (0..height % 4)
                .map(|i| {
                    let d = |x: u32| -> Digest { [(x + i) as u8; 32] };
                    NameRecord::new(&b"abcdefghij"[..1 + i as usize], d(height), d(7), d(9)).unwrap()
                })
                .collect(),
            commits_spent: (0..height as u64 % 4)
                .map(|i| (i * 1000 + 3, Commit { hash: [(i as u32 + 9) as u8; 32], height: height - 1 }))
                .collect(),
            names_before: [(height + 5) as u8; 32],
            names_parts_before: (0..height % 3)
                .map(|i| (i * 7, (i != 1).then_some(Part { hash: [(i + 40) as u8; 32], single: i == 2 })))
                .collect(),
            parts_before: (0..height as u64 % 5)
                .map(|i| (i * 3, (i % 2 == 0).then_some([(i as u32 + 1) as u8; 32])))
                .collect(),
        }
    }

    #[test]
    fn records_are_read_as_written() {
        let mut rng = Rng::new(0x41d0);
        for spends in [0usize, 1, 2, 300, 25_000, 60_000] {
            let r = record(&mut rng, 7, spends);
            let bytes = r.to_bytes();
            assert_eq!(BlockRecord::from_bytes(&bytes).unwrap(), r);
            // About three bytes a spend.
            assert!(bytes.len() <= 80 + 3 * spends + 700, "{} bytes for {spends} spends", bytes.len());
            for cut in [0, 79, bytes.len().saturating_sub(1)] {
                assert!(BlockRecord::from_bytes(&bytes[..cut]).is_err());
            }
            let mut longer = bytes.clone();
            longer.push(1);
            assert!(BlockRecord::from_bytes(&longer).is_err());
        }
        // Positions at both ends of what a position can be.
        let wide = BlockRecord { spends: vec![0, 1, (1 << 41) - 1], ..record(&mut rng, 3, 0) };
        assert_eq!(BlockRecord::from_bytes(&wide.to_bytes()).unwrap(), wide);
        // Any byte changed: refused, or another record, never a panic.
        let bytes = record(&mut rng, 5, 40).to_bytes();
        for _ in 0..2000 {
            let mut b = bytes.clone();
            let at = rng.next_u64() as usize % b.len();
            b[at] = rng.next_u64() as u8;
            let _ = BlockRecord::from_bytes(&b);
        }
    }

    /// A window of five blocks through thirty: the newest five are had,
    /// popped newest first, and nothing older; what is dropped is freed.
    #[test]
    fn a_window_keeps_the_last_blocks() {
        let file = PageFile::create(MemBackend::new()).unwrap();
        let mut rng = Rng::new(0x51de);
        let mut window = Window::default();
        let mut records = Vec::new();
        let keep = 5;
        for height in 1..=30u32 {
            // Some records of several pages.
            let r = record(&mut rng, height, if height % 7 == 0 { 70_000 } else { 50 * height as usize });
            let mut txn = file.begin().unwrap();
            window.push(&mut txn, &r, keep).unwrap();
            txn.commit(&window.to_bytes()).unwrap();
            records.push(r);
            assert_eq!(window.len(), (height as usize).min(keep));
            assert_eq!(window.oldest(), Some(height.saturating_sub(keep as u32 - 1).max(1)));
            // Read from the file alone, it is the same window.
            let read = Window::read(&file, file.root().payload()).unwrap();
            assert_eq!(read, window);
            for h in 0..=height + 1 {
                let want = (h + keep as u32 > height && h >= 1 && h <= height).then(|| records[h as usize - 1].clone());
                assert_eq!(window.get(&file, h).unwrap(), want, "block {h} at {height}");
            }
        }
        // Opened again: every unit in use is one the window reaches.
        let again = PageFile::open(MemBackend::from_image(file.backend().image(Lost::All))).unwrap();
        let read = Window::read(&again, again.root().payload()).unwrap();
        read.mark(&again).unwrap();
        again.seal();
        assert_eq!(again.space().0, file.space().0);
        // Popped newest first, then there is none.
        for height in (26..=30u32).rev() {
            let mut txn = file.begin().unwrap();
            assert_eq!(window.pop(&mut txn).unwrap().as_ref(), Some(&records[height as usize - 1]));
            txn.commit(&window.to_bytes()).unwrap();
        }
        let mut txn = file.begin().unwrap();
        assert_eq!(window.pop(&mut txn).unwrap(), None);
        txn.commit(&window.to_bytes()).unwrap();
        assert!(window.is_empty());
        assert_eq!(file.space().0, crate::store::pagefile::HEADER_UNITS);
        assert_eq!(Window::read(&file, file.root().payload()).unwrap(), Window::default());
        // A window of no blocks keeps nothing.
        let mut txn = file.begin().unwrap();
        window.push(&mut txn, &records[0], 0).unwrap();
        assert!(window.is_empty() && txn.written() == 0);
    }

    #[test]
    fn the_most_blocks_fit_one_list() {
        assert_eq!(MAX_BLOCKS, 6552);
        const { assert!(MAX_BLOCKS >= 7 * 144) };
    }
}
