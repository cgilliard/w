//! The blocks a node knows of: their headers, what it has of their
//! bodies, and which of them make the chain.
//!
//! The state is what the blocks add up to; this is the blocks. They are
//! kept in the state's file, in tries of their own beside the outputs'
//! and the names', so a block's header, its body, its place in the chain
//! and its change to the state are in place together or not at all: one
//! root record says all of it.
//!
//! - The **index**: by block id, the header, the work of the chain up
//!   to it and a status the chain gives it. Every header a node keeps,
//!   on the chain or beside it.
//! - The **heights**: by height, the id of the chain's block there.
//! - The **planned**: by height, the ids of a branch the chain means to
//!   take, whose bodies are still to come.
//! - The **bodies**: by height and id, a block's body and the leaves
//!   its header's auxiliary bytes commit to. They are megabytes, kept as
//!   pages and a list of them ([`super::blob`]), and dropped when the block is
//!   older than any reorganisation reaches: freed space, used again.
//! - The **files**: by SHA-256, the consensus files held.
//! - A few bytes of the chain's own ([`CHAIN_BYTES`]), which the store
//!   keeps and does not read.
//!
//! The tries are the state's trie ([`super::trie`]) with other keys and
//! records, and nothing hashed: no root commits to what a node happens
//! to have. What the store holds here it holds as bytes; what a header
//! or a status means is the chain's to say.

use std::io;

use super::backend::Backend;
use super::blob::Blob;
use super::pagefile::{PageFile, ReadPages, Txn};
use super::sparse::EMPTY;
use super::trie::{self, Child, Edits, FLAT_BYTES, Fault, Part, Tree};
use crate::block::HEADER_SIZE;
use crate::error::Error;
use crate::hash::Digest;
use crate::hash::{digest_from_bytes, digest_to_bytes};
use crate::name::key_of;
use crate::u256::U256;

/// Bytes of the chain's own in the root record.
pub const CHAIN_BYTES: usize = 64;
/// Bytes of a hash that names a file.
pub const FILE_HASH: usize = 32;

fn corrupt(what: &'static str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, what)
}

/// A step up a tree that hashes nothing: the parents of the parts.
pub(super) fn lift_flat(parts: &mut [(u128, Part)]) -> usize {
    let mut w = 0;
    for r in 0..parts.len() {
        let up = parts[r].0 >> 1;
        if w == 0 || parts[w - 1].0 != up {
            parts[w] = (up, Part { hash: EMPTY, single: false });
            w += 1;
        }
    }
    w
}

fn refuse(_: u128, _: Fault) -> Error {
    corrupt("a change to the blocks cannot be made").into()
}

/// A block as the index holds it.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Entry {
    /// The block's id: its header's hash.
    pub id: Digest,
    pub header: [u8; HEADER_SIZE],
    /// The work of the chain up to it.
    pub work: U256,
    /// What the chain knows of it: the chain's to say.
    pub status: u8,
}

const ENTRY_BYTES: usize = 32 + HEADER_SIZE + 32 + 1;

struct IndexTree;

impl Tree for IndexTree {
    const HEIGHT: u32 = 128;
    type Key = u128;
    type Record = Entry;

    fn record_len(_: &Entry) -> usize {
        ENTRY_BYTES
    }

    fn write_record(r: &Entry, out: &mut Vec<u8>) {
        out.extend_from_slice(&digest_to_bytes(&r.id));
        out.extend_from_slice(&r.header);
        out.extend_from_slice(&r.work.to_le_bytes());
        out.push(r.status);
    }

    fn read_record(b: &[u8]) -> io::Result<(Entry, &[u8])> {
        let bad = || corrupt("a block's entry is not one");
        let (r, rest) = b.split_at_checked(ENTRY_BYTES).ok_or_else(bad)?;
        let entry = Entry {
            id: digest_from_bytes(&r[..32]).ok_or_else(bad)?,
            header: r[32..32 + HEADER_SIZE].try_into().unwrap(),
            work: U256::from_le_bytes(r[32 + HEADER_SIZE..ENTRY_BYTES - 1].try_into().unwrap()),
            status: r[ENTRY_BYTES - 1],
        };
        Ok((entry, rest))
    }

    fn leaf(_: u128, _: &Entry) -> Digest {
        EMPTY
    }

    fn lift(_: u32, parts: &mut [(u128, Part)]) -> usize {
        lift_flat(parts)
    }

    fn refuse(key: u128, fault: Fault) -> Error {
        refuse(key, fault)
    }
}

struct HeightTree;

impl Tree for HeightTree {
    const HEIGHT: u32 = 32;
    type Key = u32;
    type Record = Digest;

    fn record_len(_: &Digest) -> usize {
        32
    }

    fn write_record(r: &Digest, out: &mut Vec<u8>) {
        out.extend_from_slice(&digest_to_bytes(r));
    }

    fn read_record(b: &[u8]) -> io::Result<(Digest, &[u8])> {
        let bad = || corrupt("a height's block is not an id");
        let (r, rest) = b.split_at_checked(32).ok_or_else(bad)?;
        Ok((digest_from_bytes(r).ok_or_else(bad)?, rest))
    }

    fn leaf(_: u128, _: &Digest) -> Digest {
        EMPTY
    }

    fn lift(_: u32, parts: &mut [(u128, Part)]) -> usize {
        lift_flat(parts)
    }

    fn refuse(key: u128, fault: Fault) -> Error {
        refuse(key, fault)
    }
}

/// What is kept of a block beside its header.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
struct Kept {
    id: Digest,
    body: Option<Blob>,
    aux: Option<Blob>,
}

const KEPT_BYTES: usize = 32 + 2 * Blob::BYTES;

/// By height, then id: what is old is what comes first.
struct BodyTree;

fn body_key(height: u32, id: &Digest) -> u128 {
    (height as u128) << 88 | key_of(id) >> 40
}

impl Tree for BodyTree {
    const HEIGHT: u32 = 120;
    type Key = u128;
    type Record = Kept;

    fn record_len(_: &Kept) -> usize {
        KEPT_BYTES
    }

    fn write_record(r: &Kept, out: &mut Vec<u8>) {
        out.extend_from_slice(&digest_to_bytes(&r.id));
        Blob::put_option(&r.body, out);
        Blob::put_option(&r.aux, out);
    }

    fn read_record(b: &[u8]) -> io::Result<(Kept, &[u8])> {
        let bad = || corrupt("what is kept of a block is not that");
        let (r, rest) = b.split_at_checked(KEPT_BYTES).ok_or_else(bad)?;
        let kept = Kept {
            id: digest_from_bytes(&r[..32]).ok_or_else(bad)?,
            body: Blob::get_option(&r[32..42])?,
            aux: Blob::get_option(&r[42..52])?,
        };
        Ok((kept, rest))
    }

    fn leaf(_: u128, _: &Kept) -> Digest {
        EMPTY
    }

    fn lift(_: u32, parts: &mut [(u128, Part)]) -> usize {
        lift_flat(parts)
    }

    fn refuse(key: u128, fault: Fault) -> Error {
        refuse(key, fault)
    }
}

/// A file held: its hash and where its bytes are.
type Held = ([u8; FILE_HASH], Blob);

struct FileTree;

fn file_key(hash: &[u8; FILE_HASH]) -> u128 {
    u128::from_be_bytes(hash[..16].try_into().unwrap()) >> 8
}

impl Tree for FileTree {
    const HEIGHT: u32 = 120;
    type Key = u128;
    type Record = Held;

    fn record_len(_: &Held) -> usize {
        FILE_HASH + Blob::BYTES
    }

    fn write_record(r: &Held, out: &mut Vec<u8>) {
        out.extend_from_slice(&r.0);
        r.1.put(out);
    }

    fn read_record(b: &[u8]) -> io::Result<(Held, &[u8])> {
        let bad = || corrupt("a file held is not one");
        let (r, rest) = b.split_at_checked(FILE_HASH + Blob::BYTES).ok_or_else(bad)?;
        let blob = Blob::get_option(&r[FILE_HASH..])?.ok_or_else(bad)?;
        Ok(((r[..FILE_HASH].try_into().unwrap(), blob), rest))
    }

    fn leaf(_: u128, _: &Held) -> Digest {
        EMPTY
    }

    fn lift(_: u32, parts: &mut [(u128, Part)]) -> usize {
        lift_flat(parts)
    }

    fn refuse(key: u128, fault: Fault) -> Error {
        refuse(key, fault)
    }
}

/// The blocks, as a root record holds them: the roots of the five tries
/// and the chain's bytes.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Blocks {
    index: Child,
    heights: Child,
    planned: Child,
    bodies: Child,
    files: Child,
    /// The chain's own: kept, not read.
    pub chain: [u8; CHAIN_BYTES],
    /// A note of the node's own, longer than those bytes: kept, not read.
    note: Option<Blob>,
}

/// One record put where `key` is, in place of the one there if `replace`.
fn put<T: Tree<Key = u128>, B: Backend>(
    txn: &Txn<'_, B>,
    root: &mut Child,
    key: u128,
    record: T::Record,
    replace: bool,
) -> Result<(), Error> {
    let edits: Edits<'_, T> = Edits { puts: &[(key, record, replace)], ..Edits::none() };
    *root = trie::update_on(txn, *root, 0, edits, 1)?.0;
    Ok(())
}

fn remove<T: Tree, B: Backend>(txn: &Txn<'_, B>, root: &mut Child, keys: &[T::Key]) -> Result<(), Error> {
    let edits: Edits<'_, T> = Edits { removes: keys, ..Edits::none() };
    *root = trie::update_on(txn, *root, 0, edits, 1)?.0;
    Ok(())
}

impl Blocks {
    /// No block yet.
    pub const EMPTY: Blocks = Blocks {
        index: Child::Empty,
        heights: Child::Empty,
        planned: Child::Empty,
        bodies: Child::Empty,
        files: Child::Empty,
        chain: [0; CHAIN_BYTES],
        note: None,
    };
    /// Serialized size.
    pub const BYTES: usize = 5 * FLAT_BYTES + CHAIN_BYTES + Blob::BYTES;

    pub fn to_bytes(&self) -> [u8; Self::BYTES] {
        let mut out = Vec::with_capacity(Self::BYTES);
        for root in [self.index, self.heights, self.bodies, self.files, self.planned] {
            trie::write_flat(&root, &mut out);
        }
        out.extend_from_slice(&self.chain);
        Blob::put_option(&self.note, &mut out);
        out.try_into().unwrap()
    }

    pub fn from_bytes(b: &[u8]) -> io::Result<Blocks> {
        let bad = || corrupt("the blocks' roots are not that");
        if b.len() != Self::BYTES {
            return Err(bad());
        }
        let root = |i: usize| trie::read_flat(&b[i * FLAT_BYTES..(i + 1) * FLAT_BYTES]);
        Ok(Blocks {
            index: root(0)?,
            heights: root(1)?,
            bodies: root(2)?,
            files: root(3)?,
            planned: root(4)?,
            chain: b[5 * FLAT_BYTES..5 * FLAT_BYTES + CHAIN_BYTES].try_into().unwrap(),
            note: Blob::get_option(&b[5 * FLAT_BYTES + CHAIN_BYTES..])?,
        })
    }

    /// Marks every page the blocks reach in `file`'s map of free space.
    pub fn mark<B: Backend>(&self, file: &PageFile<B>) -> io::Result<()> {
        trie::mark::<IndexTree, B>(file, self.index)?;
        trie::mark::<HeightTree, B>(file, self.heights)?;
        trie::mark::<HeightTree, B>(file, self.planned)?;
        trie::mark::<BodyTree, B>(file, self.bodies)?;
        trie::mark::<FileTree, B>(file, self.files)?;
        let mut blobs: Vec<Blob> = self.note.into_iter().collect();
        trie::for_each::<BodyTree>(file, self.bodies, &mut |_, kept, _| {
            blobs.extend(kept.body.iter().chain(&kept.aux).copied())
        })?;
        trie::for_each::<FileTree>(file, self.files, &mut |_, held, _| blobs.push(held.1))?;
        blobs.into_iter().try_for_each(|blob| blob.mark(file))
    }

    /// The block of id `id`, if the index has it.
    pub fn entry(&self, pages: &impl ReadPages, id: &Digest) -> io::Result<Option<Entry>> {
        Ok(trie::get::<IndexTree>(pages, self.index, key_of(id))?.map(|e| e.0).filter(|e| e.id == *id))
    }

    /// Puts a block in the index, in place of what the index had of it.
    /// Two ids are told apart by their first 128 bits; a second with the
    /// same is refused (`AlreadyExists`), which takes as much work to
    /// bring about as a chain of its own.
    pub fn put_entry<B: Backend>(&mut self, txn: &Txn<'_, B>, entry: &Entry) -> Result<(), Error> {
        let key = key_of(&entry.id);
        let there = trie::get::<IndexTree>(txn, self.index, key)?;
        if there.is_some_and(|(e, _)| e.id != entry.id) {
            return Err(io::Error::new(io::ErrorKind::AlreadyExists, "another block has the id's first bits").into());
        }
        put::<IndexTree, B>(txn, &mut self.index, key, *entry, there.is_some())
    }

    /// Takes a block out of the index, and what is kept of it with it.
    /// Whether it was there.
    pub fn remove_entry<B: Backend>(&mut self, txn: &Txn<'_, B>, id: &Digest) -> Result<bool, Error> {
        let Some(entry) = self.entry(txn, id)? else { return Ok(false) };
        self.drop_kept(txn, height_of(&entry), id)?;
        remove::<IndexTree, B>(txn, &mut self.index, &[key_of(id)])?;
        Ok(true)
    }

    /// The id of the chain's block at `height`.
    pub fn at(&self, pages: &impl ReadPages, height: u32) -> io::Result<Option<Digest>> {
        Ok(trie::get::<HeightTree>(pages, self.heights, height as u128)?.map(|r| r.0))
    }

    /// Says which block is the chain's at `height`: `None` for none.
    pub fn set_at<B: Backend>(&mut self, txn: &Txn<'_, B>, height: u32, id: Option<Digest>) -> Result<(), Error> {
        let there = trie::get::<HeightTree>(txn, self.heights, height as u128)?.is_some();
        match id {
            Some(id) => {
                let edits: Edits<'_, HeightTree> = Edits { puts: &[(height, id, there)], ..Edits::none() };
                self.heights = trie::update_on(txn, self.heights, 0, edits, 1)?.0;
                Ok(())
            }
            None if there => remove::<HeightTree, B>(txn, &mut self.heights, &[height]),
            None => Ok(()),
        }
    }

    /// Says which block is the chain's at each of `heights`, which
    /// ascend: [`Blocks::set_at`] of each, in one pass over the table.
    /// Said one at a time in one transaction, each writes anew the
    /// pages the one before wrote, and a chain of a year's blocks
    /// leaves ten times its size of pages behind it in the file.
    pub fn set_many<B: Backend>(&mut self, txn: &Txn<'_, B>, heights: &[(u32, Digest)]) -> Result<(), Error> {
        debug_assert!(heights.windows(2).all(|w| w[0].0 < w[1].0), "heights ascend");
        let mut puts = Vec::with_capacity(heights.len());
        for (height, id) in heights {
            let there = trie::get::<HeightTree>(txn, self.heights, *height as u128)?.is_some();
            puts.push((*height, *id, there));
        }
        let edits: Edits<'_, HeightTree> = Edits { puts: &puts, ..Edits::none() };
        self.heights = trie::update_on(txn, self.heights, 0, edits, 1)?.0;
        Ok(())
    }

    /// Says that no block is the chain's at any of the heights
    /// `from..to`: in one pass over the table, as [`Blocks::set_many`].
    pub fn clear_heights<B: Backend>(&mut self, txn: &Txn<'_, B>, from: u32, to: u32) -> Result<(), Error> {
        let mut there = Vec::new();
        let mut at = from;
        while let Some(h) = trie::next_key::<HeightTree>(txn, self.heights, at as u128)?.filter(|h| *h < to as u128) {
            there.push(h as u32);
            at = h as u32 + 1;
        }
        match there.is_empty() {
            true => Ok(()),
            false => remove::<HeightTree, B>(txn, &mut self.heights, &there),
        }
    }

    /// The id of the planned branch's block at `height`.
    pub fn planned_at(&self, pages: &impl ReadPages, height: u32) -> io::Result<Option<Digest>> {
        Ok(trie::get::<HeightTree>(pages, self.planned, height as u128)?.map(|r| r.0))
    }

    /// The lowest height at or above `from` the planned branch has a
    /// block at.
    pub fn next_planned(&self, pages: &impl ReadPages, from: u32) -> io::Result<Option<u32>> {
        Ok(trie::next_key::<HeightTree>(pages, self.planned, from as u128)?.map(|h| h as u32))
    }

    /// Says which block is the planned branch's at `height`.
    pub fn set_planned<B: Backend>(&mut self, txn: &Txn<'_, B>, height: u32, id: Digest) -> Result<(), Error> {
        let there = trie::get::<HeightTree>(txn, self.planned, height as u128)?.is_some();
        let edits: Edits<'_, HeightTree> = Edits { puts: &[(height, id, there)], ..Edits::none() };
        self.planned = trie::update_on(txn, self.planned, 0, edits, 1)?.0;
        Ok(())
    }

    /// Takes the heights `from..to` out of the planned branch: found one
    /// after another, so the cost is of those there are.
    pub fn drop_planned<B: Backend>(&mut self, txn: &Txn<'_, B>, from: u32, to: u32) -> Result<(), Error> {
        let (mut heights, mut at) = (Vec::new(), from);
        while let Some(h) = self.next_planned(txn, at)?.filter(|h| *h < to) {
            heights.push(h);
            let Some(next) = h.checked_add(1) else { break };
            at = next;
        }
        match heights.is_empty() {
            true => Ok(()),
            false => remove::<HeightTree, B>(txn, &mut self.planned, &heights),
        }
    }

    fn kept(&self, pages: &impl ReadPages, height: u32, id: &Digest) -> io::Result<Option<Kept>> {
        Ok(trie::get::<BodyTree>(pages, self.bodies, body_key(height, id))?.map(|k| k.0).filter(|k| k.id == *id))
    }

    /// The body of the block of id `id` at `height`, if it is kept.
    pub fn body(&self, pages: &impl ReadPages, height: u32, id: &Digest) -> io::Result<Option<Vec<u8>>> {
        self.kept(pages, height, id)?.and_then(|k| k.body).map(|b| b.read(pages)).transpose()
    }

    /// Whether the block's body is kept: nothing of it is read.
    pub fn has_body(&self, pages: &impl ReadPages, height: u32, id: &Digest) -> io::Result<bool> {
        Ok(self.kept(pages, height, id)?.is_some_and(|k| k.body.is_some()))
    }

    /// The leaves the block's auxiliary bytes commit to, if kept.
    pub fn aux(&self, pages: &impl ReadPages, height: u32, id: &Digest) -> io::Result<Option<Vec<u8>>> {
        self.kept(pages, height, id)?.and_then(|k| k.aux).map(|b| b.read(pages)).transpose()
    }

    /// Keeps a block's body (`aux` false) or its auxiliary leaves, in
    /// place of those kept before.
    fn keep<B: Backend>(
        &mut self,
        txn: &Txn<'_, B>,
        height: u32,
        id: &Digest,
        aux: bool,
        bytes: &[u8],
    ) -> Result<(), Error> {
        let key = body_key(height, id);
        let there = trie::get::<BodyTree>(txn, self.bodies, key)?.map(|k| k.0);
        if there.is_some_and(|k| k.id != *id) {
            return Err(io::Error::new(io::ErrorKind::AlreadyExists, "another block has the id's first bits").into());
        }
        let mut kept = there.unwrap_or(Kept { id: *id, body: None, aux: None });
        let slot = if aux { &mut kept.aux } else { &mut kept.body };
        if let Some(old) = slot.replace(Blob::write(txn, bytes)?) {
            old.free(txn)?;
        }
        put::<BodyTree, B>(txn, &mut self.bodies, key, kept, there.is_some())
    }

    /// Keeps the body of the block of id `id` at `height`.
    pub fn put_body<B: Backend>(
        &mut self,
        txn: &Txn<'_, B>,
        height: u32,
        id: &Digest,
        body: &[u8],
    ) -> Result<(), Error> {
        self.keep(txn, height, id, false, body)
    }

    /// Keeps the block's auxiliary leaves.
    pub fn put_aux<B: Backend>(
        &mut self,
        txn: &Txn<'_, B>,
        height: u32,
        id: &Digest,
        leaves: &[u8],
    ) -> Result<(), Error> {
        self.keep(txn, height, id, true, leaves)
    }

    /// Drops what is kept of one block beside its header. Whether there
    /// was anything.
    pub fn drop_kept<B: Backend>(&mut self, txn: &Txn<'_, B>, height: u32, id: &Digest) -> Result<bool, Error> {
        let Some(kept) = self.kept(txn, height, id)? else { return Ok(false) };
        for blob in kept.body.iter().chain(&kept.aux) {
            blob.free(txn)?;
        }
        remove::<BodyTree, B>(txn, &mut self.bodies, &[body_key(height, id)])?;
        Ok(true)
    }

    /// Drops what is kept of every block at the heights `from..to`, on
    /// the chain or not: their space is free. Returns how many blocks.
    pub fn drop_kept_between<B: Backend>(&mut self, txn: &Txn<'_, B>, from: u32, to: u32) -> Result<usize, Error> {
        // From one height that has something kept to the next: the
        // heights between cost nothing.
        let mut old: Vec<(u128, Kept)> = Vec::new();
        let mut at = from;
        while at < to {
            let Some(key) = trie::next_key::<BodyTree>(txn, self.bodies, (at as u128) << 88)? else { break };
            let height = (key >> 88) as u32;
            if height >= to {
                break;
            }
            trie::for_each_in::<BodyTree>(txn, self.bodies, 88, height as u128, &mut |key, kept, _| {
                old.push((key, *kept))
            })?;
            let Some(next) = height.checked_add(1) else { break };
            at = next;
        }
        for (_, kept) in &old {
            for blob in kept.body.iter().chain(&kept.aux) {
                blob.free(txn)?;
            }
        }
        let keys: Vec<u128> = old.iter().map(|o| o.0).collect();
        if !keys.is_empty() {
            remove::<BodyTree, B>(txn, &mut self.bodies, &keys)?;
        }
        Ok(keys.len())
    }

    /// The lowest height anything is kept of a block at.
    pub fn oldest_kept(&self, pages: &impl ReadPages) -> io::Result<Option<u32>> {
        Ok(trie::next_key::<BodyTree>(pages, self.bodies, 0)?.map(|key| (key >> 88) as u32))
    }

    /// A consensus file held, by its SHA-256.
    pub fn file(&self, pages: &impl ReadPages, hash: &[u8; FILE_HASH]) -> io::Result<Option<Vec<u8>>> {
        let held = trie::get::<FileTree>(pages, self.files, file_key(hash))?.map(|h| h.0).filter(|h| h.0 == *hash);
        held.map(|h| h.1.read(pages)).transpose()
    }

    /// Holds a file under `hash`, which the caller computed of it.
    /// Nothing changes if it is held.
    pub fn put_file<B: Backend>(
        &mut self,
        txn: &Txn<'_, B>,
        hash: &[u8; FILE_HASH],
        bytes: &[u8],
    ) -> Result<(), Error> {
        match trie::get::<FileTree>(txn, self.files, file_key(hash))? {
            Some((held, _)) if held.0 == *hash => Ok(()),
            Some(_) => {
                Err(io::Error::new(io::ErrorKind::AlreadyExists, "another file has the hash's first bits").into())
            }
            None => {
                let held = (*hash, Blob::write(txn, bytes)?);
                put::<FileTree, B>(txn, &mut self.files, file_key(hash), held, false)
            }
        }
    }

    /// Lets a file go. Whether it was held.
    pub fn drop_file<B: Backend>(&mut self, txn: &Txn<'_, B>, hash: &[u8; FILE_HASH]) -> Result<bool, Error> {
        match trie::get::<FileTree>(txn, self.files, file_key(hash))? {
            Some((held, _)) if held.0 == *hash => {
                held.1.free(txn)?;
                remove::<FileTree, B>(txn, &mut self.files, &[file_key(hash)])?;
                Ok(true)
            }
            _ => Ok(false),
        }
    }

    /// The node's own note, if it has written one.
    pub fn note(&self, pages: &impl ReadPages) -> io::Result<Option<Vec<u8>>> {
        self.note.map(|blob| blob.read(pages)).transpose()
    }

    /// Writes the node's own note in place of the one before: `None`,
    /// or nothing, for none.
    pub fn set_note<B: Backend>(&mut self, txn: &Txn<'_, B>, bytes: Option<&[u8]>) -> Result<(), Error> {
        if let Some(old) = self.note.take() {
            old.free(txn)?;
        }
        self.note = bytes.filter(|b| !b.is_empty()).map(|b| Blob::write(txn, b)).transpose()?;
        Ok(())
    }

    /// The hashes of the files held.
    pub fn files(&self, pages: &impl ReadPages) -> io::Result<Vec<[u8; FILE_HASH]>> {
        let mut out = Vec::new();
        trie::for_each::<FileTree>(pages, self.files, &mut |_, held, _| out.push(held.0))?;
        Ok(out)
    }
}

/// The height a header says: its bytes after the previous block's id.
fn height_of(entry: &Entry) -> u32 {
    u32::from_le_bytes(entry.header[32..36].try_into().unwrap())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::store::testing::{Lost, MemBackend};
    use crate::test_util::Rng;

    fn id(rng: &mut Rng) -> Digest {
        rng.digest()
    }

    fn entry(rng: &mut Rng, height: u32) -> Entry {
        let mut header = [0u8; HEADER_SIZE];
        header.iter_mut().for_each(|b| *b = rng.next_u64() as u8);
        header[32..36].copy_from_slice(&height.to_le_bytes());
        Entry { id: id(rng), header, work: U256([rng.next_u64(), height as u64, 0, 0]), status: (height % 5) as u8 }
    }

    fn bytes(rng: &mut Rng, len: usize) -> Vec<u8> {
        (0..len).map(|_| rng.next_u64() as u8).collect()
    }

    /// One change, committed.
    fn with(file: &PageFile<MemBackend>, blocks: &mut Blocks, f: impl FnOnce(&Txn<'_, MemBackend>, &mut Blocks)) {
        let txn = file.begin().unwrap();
        f(&txn, blocks);
        txn.commit(&blocks.to_bytes()).unwrap();
    }

    /// The file opened afresh: the blocks its root record holds, their
    /// pages marked.
    fn reopened(file: &PageFile<MemBackend>) -> (PageFile<MemBackend>, Blocks) {
        let again = PageFile::open(MemBackend::from_image(file.backend().image(Lost::All))).unwrap();
        let blocks = Blocks::from_bytes(again.root().payload()).unwrap();
        blocks.mark(&again).unwrap();
        again.seal();
        (again, blocks)
    }

    /// Headers by id, on the chain and beside it; the chain by height;
    /// all of it there when the file is opened again.
    #[test]
    fn headers_and_the_chain() {
        let file = PageFile::create(MemBackend::new()).unwrap();
        let (mut blocks, mut rng) = (Blocks::EMPTY, Rng::new(0xb10c));
        assert_eq!(Blocks::from_bytes(&blocks.to_bytes()).unwrap(), blocks);
        // Three thousand blocks, and a branch of a hundred beside the end.
        let chain: Vec<Entry> = (0..3000).map(|h| entry(&mut rng, h)).collect();
        let branch: Vec<Entry> = (2900..3000).map(|h| entry(&mut rng, h)).collect();
        for part in chain.chunks(500) {
            with(&file, &mut blocks, |txn, blocks| {
                for e in part {
                    blocks.put_entry(txn, e).unwrap();
                    blocks.set_at(txn, height_of(e), Some(e.id)).unwrap();
                }
            });
        }
        with(&file, &mut blocks, |txn, blocks| branch.iter().for_each(|e| blocks.put_entry(txn, e).unwrap()));
        let check = |file: &PageFile<MemBackend>, blocks: &Blocks, chain: &[Entry], branch: &[Entry]| {
            for e in chain.iter().step_by(7).chain(branch) {
                assert_eq!(blocks.entry(file, &e.id).unwrap(), Some(*e));
            }
            for e in chain.iter().step_by(11) {
                assert_eq!(blocks.at(file, height_of(e)).unwrap(), Some(e.id));
            }
            assert_eq!(blocks.at(file, 3000).unwrap(), None);
            assert_eq!(blocks.at(file, chain.len() as u32).unwrap(), None);
            assert_eq!(blocks.entry(file, &[5_u8; 32]).unwrap(), None);
        };
        check(&file, &blocks, &chain, &branch);

        // A block's entry changes: its status, as the chain learns of it.
        let learned = Entry { status: 9, ..chain[77] };
        with(&file, &mut blocks, |txn, blocks| blocks.put_entry(txn, &learned).unwrap());
        assert_eq!(blocks.entry(&file, &learned.id).unwrap(), Some(learned));
        with(&file, &mut blocks, |txn, blocks| blocks.put_entry(txn, &chain[77]).unwrap());

        // The branch becomes the chain: the heights say so in one step.
        with(&file, &mut blocks, |txn, blocks| {
            branch.iter().for_each(|e| blocks.set_at(txn, height_of(e), Some(e.id)).unwrap());
        });
        let mut other = chain[..2900].to_vec();
        other.extend(&branch);
        check(&file, &blocks, &other, &branch);
        // And is cut back: heights with no block, and a block forgotten.
        with(&file, &mut blocks, |txn, blocks| {
            for h in 2950..3000 {
                blocks.set_at(txn, h, None).unwrap();
            }
            blocks.set_at(txn, 5000, None).unwrap();
            assert!(blocks.remove_entry(txn, &branch[99].id).unwrap());
            assert!(!blocks.remove_entry(txn, &branch[99].id).unwrap());
        });
        assert_eq!(blocks.at(&file, 2949).unwrap(), Some(branch[49].id));
        assert_eq!(blocks.at(&file, 2950).unwrap(), None);
        assert_eq!(blocks.entry(&file, &branch[99].id).unwrap(), None);

        // A branch planned, beside the chain: its own heights, taken
        // out from either end.
        with(&file, &mut blocks, |txn, blocks| {
            for e in &branch[10..60] {
                blocks.set_planned(txn, height_of(e), e.id).unwrap();
            }
            blocks.set_planned(txn, 2915, chain[2915].id).unwrap();
        });
        assert_eq!(blocks.planned_at(&file, 2915).unwrap(), Some(chain[2915].id));
        assert_eq!(blocks.planned_at(&file, 2930).unwrap(), Some(branch[30].id));
        assert_eq!((blocks.planned_at(&file, 2909).unwrap(), blocks.planned_at(&file, 2960).unwrap()), (None, None));
        assert_eq!(blocks.next_planned(&file, 0).unwrap(), Some(2910));
        assert_eq!(blocks.next_planned(&file, 2960).unwrap(), None);
        with(&file, &mut blocks, |txn, blocks| {
            blocks.drop_planned(txn, 0, 2920).unwrap();
            blocks.drop_planned(txn, 2950, u32::MAX).unwrap();
            blocks.drop_planned(txn, 5000, 6000).unwrap();
        });
        assert_eq!(
            (blocks.next_planned(&file, 0).unwrap(), blocks.next_planned(&file, 2950).unwrap()),
            (Some(2920), None)
        );
        assert_eq!(blocks.at(&file, 2930).unwrap(), Some(branch[30].id), "the chain's heights are its own");

        // An id with another's first bits is not taken for it.
        let mut twin = chain[5];
        twin.id[31] ^= 1;
        assert_eq!(blocks.entry(&file, &twin.id).unwrap(), None);
        let txn = file.begin().unwrap();
        let refused = blocks.put_entry(&txn, &twin);
        assert_eq!(refused, Err(Error::Io(io::ErrorKind::AlreadyExists)));
        drop(txn);

        let (again, read) = reopened(&file);
        assert_eq!(read, blocks);
        assert_eq!(again.space().0, file.space().0);
        check(&again, &read, &other[..2950], &branch[..99]);
    }

    /// Bodies and auxiliary leaves are kept by block, read back whole,
    /// and dropped by height: their space is the file's again.
    #[test]
    fn bodies_are_kept_and_dropped() {
        let file = PageFile::create(MemBackend::new()).unwrap();
        let (mut blocks, mut rng) = (Blocks::EMPTY, Rng::new(0xb0d1));
        // Forty heights, one or two blocks at each, bodies from a few
        // bytes to megabytes, some with leaves, some with leaves alone.
        // (A height, an id, a body and leaves.)
        type Kept = (u32, Digest, Option<Vec<u8>>, Option<Vec<u8>>);
        let mut all: Vec<Kept> = Vec::new();
        for height in 10..50u32 {
            for fork in 0..1 + height % 2 {
                let len = [40, 3_000, 70_000, 2_000_000][(height as usize + fork as usize) % 4];
                let body = (height % 7 != 0).then(|| bytes(&mut rng, len));
                let aux = (height % 3 == 0 || body.is_none()).then(|| bytes(&mut rng, 512));
                all.push((height, id(&mut rng), body, aux));
            }
        }
        let empty = file.space().0;
        for part in all.chunks(8) {
            with(&file, &mut blocks, |txn, blocks| {
                for (height, id, body, aux) in part {
                    if let Some(aux) = aux {
                        blocks.put_aux(txn, *height, id, aux).unwrap();
                    }
                    if let Some(body) = body {
                        blocks.put_body(txn, *height, id, body).unwrap();
                    }
                }
            });
        }
        let check = |file: &PageFile<MemBackend>, blocks: &Blocks, from: u32| {
            for (height, id, body, aux) in &all {
                let (body, aux) = if *height >= from { (body.clone(), aux.clone()) } else { (None, None) };
                assert_eq!(blocks.has_body(file, *height, id).unwrap(), body.is_some());
                assert_eq!(blocks.body(file, *height, id).unwrap(), body, "the body at {height}");
                assert_eq!(blocks.aux(file, *height, id).unwrap(), aux, "the leaves at {height}");
                // Not at another height, nor of another block there.
                assert_eq!(blocks.body(file, *height + 1000, id).unwrap(), None);
            }
            assert_eq!(blocks.oldest_kept(file).unwrap(), all.iter().map(|a| a.0).find(|h| *h >= from));
        };
        check(&file, &blocks, 0);
        let (again, read) = reopened(&file);
        assert_eq!(again.space().0, file.space().0);
        check(&again, &read, 0);

        // A body put again takes the place of the first; its pages go.
        let used = file.space().0;
        let (height, id, body, _) =
            all.iter().find(|a| a.2.as_ref().is_some_and(|b| b.len() == 70_000)).unwrap().clone();
        with(&file, &mut blocks, |txn, blocks| blocks.put_body(txn, height, &id, &[7; 100]).unwrap());
        assert_eq!(blocks.body(&file, height, &id).unwrap(), Some(vec![7; 100]));
        assert!(file.space().0 < used);
        with(&file, &mut blocks, |txn, blocks| blocks.put_body(txn, height, &id, &body.unwrap()).unwrap());
        assert_eq!(file.space().0, used);

        // Dropped below a height, a few heights at a time as blocks come.
        let mut dropped = 0;
        for upto in [5, 12, 13, 30, 30, 44] {
            with(&file, &mut blocks, |txn, blocks| dropped += blocks.drop_kept_between(txn, 0, upto).unwrap());
            check(&file, &blocks, upto);
            assert_eq!(dropped, all.iter().filter(|a| a.0 < upto).count());
        }
        let (again, read) = reopened(&file);
        assert_eq!(again.space().0, file.space().0);
        check(&again, &read, 44);
        // One block's alone, then the rest: nothing is left of them.
        let last = all.last().unwrap().clone();
        with(&file, &mut blocks, |txn, blocks| {
            assert!(blocks.drop_kept(txn, last.0, &last.1).unwrap());
            assert!(!blocks.drop_kept(txn, last.0, &last.1).unwrap());
            blocks.drop_kept_between(txn, 44, u32::MAX).unwrap();
        });
        assert_eq!(blocks.oldest_kept(&file).unwrap(), None);
        assert_eq!(file.space().0, empty);
    }

    /// Consensus files are held by hash and let go.
    #[test]
    fn files_are_held_and_let_go() {
        let file = PageFile::create(MemBackend::new()).unwrap();
        let (mut blocks, mut rng) = (Blocks::EMPTY, Rng::new(0xf11e));
        let empty = file.space().0;
        let held: Vec<([u8; 32], Vec<u8>)> = [10usize, 5_000, 1 << 20, 300]
            .into_iter()
            .map(|len| (bytes(&mut rng, 32).try_into().unwrap(), bytes(&mut rng, len)))
            .collect();
        with(&file, &mut blocks, |txn, blocks| {
            for (hash, bytes) in &held {
                blocks.put_file(txn, hash, bytes).unwrap();
            }
            // Held already: nothing more is written.
            let written = txn.written();
            blocks.put_file(txn, &held[2].0, &held[2].1).unwrap();
            assert_eq!(txn.written(), written);
        });
        blocks.chain = [3; CHAIN_BYTES];
        with(&file, &mut blocks, |txn, blocks| {
            blocks.set_note(txn, Some(&[5; 512])).unwrap();
            blocks.set_note(txn, Some(&[6; 700])).unwrap();
        });
        assert_eq!(blocks.note(&file).unwrap(), Some(vec![6; 700]));
        let (again, read) = reopened(&file);
        assert_eq!((read, again.space().0), (blocks, file.space().0));
        for (hash, bytes) in &held {
            assert_eq!(read.file(&again, hash).unwrap().as_ref(), Some(bytes));
        }
        let mut hashes: Vec<[u8; 32]> = held.iter().map(|h| h.0).collect();
        hashes.sort_unstable();
        let mut listed = read.files(&again).unwrap();
        listed.sort_unstable();
        assert_eq!(listed, hashes);
        assert_eq!(blocks.file(&file, &[1; 32]).unwrap(), None);

        with(&file, &mut blocks, |txn, blocks| {
            assert!(blocks.drop_file(txn, &held[2].0).unwrap());
            assert!(!blocks.drop_file(txn, &held[2].0).unwrap());
        });
        assert_eq!(blocks.file(&file, &held[2].0).unwrap(), None);
        assert_eq!(blocks.files(&file).unwrap().len(), 3);
        with(&file, &mut blocks, |txn, blocks| {
            for (hash, _) in &held {
                blocks.drop_file(txn, hash).unwrap();
            }
            blocks.set_note(txn, None).unwrap();
        });
        assert_eq!(file.space().0, empty);
    }
}
