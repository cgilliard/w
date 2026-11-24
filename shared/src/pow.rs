//! Memory-hard proof of work in the style of Ethash, seeded by a text
//! that the chain exists to preserve.
//!
//! The seed is the American King James Bible as the gzip file
//! `resources/akjv.txt.gz` ([`SEED_TEXT_LEN`] bytes), in the binary and
//! used as it is: nothing is decompressed. Its bytes are read in
//! **windows** of 64 bytes, a Blake3 block: [`WINDOWS`] of them, a power
//! of two, spread evenly from the file's first byte to its last, so that
//! each overlaps the next and every byte is in one or two. A window is
//! picked by the low bits of a word, every one as likely as another.
//!
//! Every dataset item is made from the windows: from a key that is the
//! item's index, each of [`PowParams::parents`] steps picks a window by
//! the key and hashes it under the key, which gives the next. Miners keep the items
//! in a table of 64-byte items. The work of a header ([`hashimoto`])
//! seeds a mix of 32 words from the header's hash and a nonce and makes
//! [`PowParams::accesses`] reads, each folding in two adjacent items and
//! one window of the file itself; it then hashes the mix, and that with
//! the seed.
//!
//! # Validating a block requires the seed file, all of it
//!
//! Checking a header's work without the table computes the 128 items it
//! reads from the file: `128 * parents` windows, and 64 more read
//! directly, each picked by a hash, which nobody can foretell or steer.
//! At the parameters here one header's work reads most of the file, and
//! a few headers' all of it ([`tests`] measure both). So neither the
//! table nor any hash of the file stands in for it, no part of it can be
//! left out, and a node missing any window soon meets a block it cannot
//! validate. Every validating node keeps the file.
//!
//! # Verifiers and miners
//!
//! A verifier computes only the items a header's work touches, from the
//! file ([`SeedText::table`]): 128 of them, each the same work whatever
//! the table's size, since an item is made from its index and the text
//! and from no other item. A hash costs three compressions with the
//! table and about `2 * accesses * parents` without it, so a miner keeps
//! the table.
//!
//! # The table grows
//!
//! The chain is divided into epochs of [`PowParams::epoch_blocks`]
//! blocks. The table has `2^log_dataset_items` items in the first and
//! twice as many in each one after, until it has
//! `2^max_log_dataset_items`: on mainnet 1 GB, doubling each year to
//! 32 GB. An item is the same in every epoch, so a table that grows
//! keeps the items it has, and which table a block's work is of depends
//! on its height alone.
//!
//! # The arithmetic
//!
//! Words of 32 bits. The mixing step is Ethash's FNV,
//! `(a * 0x01000193) ^ b`, cheap enough that a hash's cost is its reads
//! of the table; the hashes are Blake3, each a call any Blake3 library
//! makes.

use std::io::{Read as _, Write as _};
use std::sync::atomic::{AtomicU32, AtomicU64, AtomicUsize, Ordering};

use crate::blake3;
use crate::difficulty::Target;
use crate::hash::{DOM_POW_ITEM, DOM_POW_MIX, DOM_POW_RESULT, DOM_POW_SEED, Digest, hash_domain};

/// One dataset item: 16 words, 64 bytes.
pub type Item = [u32; 16];
/// A nonce: 32 bytes, any.
pub type Nonce = [u8; 32];

/// The seed file: the text gzipped, in the binary and used as it is.
pub const SEED_TEXT_GZ: &[u8] = include_bytes!("../../resources/akjv.txt.gz");
/// Its size, checked when it is first used.
pub const SEED_TEXT_LEN: usize = 1_291_059;
/// Bytes of a window: a Blake3 block.
pub const WINDOW: usize = 64;
/// Windows, as a power of two.
pub const LOG_WINDOWS: u32 = 15;
pub const WINDOWS: usize = 1 << LOG_WINDOWS;
// Each window overlaps the next: every byte is in one.
const _: () = assert!((SEED_TEXT_LEN - WINDOW) / (WINDOWS - 1) < WINDOW);

const FNV_PRIME: u32 = 0x0100_0193;
/// Words of the mix: two items.
const MIX_WORDS: usize = 32;

/// `(a * FNV_PRIME) ^ b`.
#[inline(always)]
fn fnv(a: u32, b: u32) -> u32 {
    a.wrapping_mul(FNV_PRIME) ^ b
}

/// The proof of work's parameters: how large the table is in each
/// epoch, and how much work an item and a hash are.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PowParams {
    /// The table has `2^log_dataset_items` items in the first epoch.
    pub log_dataset_items: u32,
    /// It doubles each epoch until it has `2^max_log_dataset_items`.
    pub max_log_dataset_items: u32,
    /// Blocks in an epoch.
    pub epoch_blocks: u32,
    /// Steps of an item, each hashing one window of the text.
    pub parents: usize,
    /// Reads of the table (of two adjacent items each) a hash makes.
    pub accesses: usize,
}

impl PowParams {
    /// A table of 1 GB that doubles each year (52,560 blocks of ten
    /// minutes) to 32 GB.
    pub const MAINNET: PowParams = PowParams {
        log_dataset_items: 24,
        max_log_dataset_items: 29,
        epoch_blocks: 144 * 365,
        parents: 254,
        accesses: 64,
    };

    /// The dev networks': a 64 KB table that does not grow.
    pub const DEV: PowParams = PowParams { log_dataset_items: 10, max_log_dataset_items: 10, ..Self::MAINNET };

    /// The epoch of the block at `height`.
    pub const fn epoch_of(&self, height: u64) -> u32 {
        let e = height / self.epoch_blocks as u64;
        if e > u32::MAX as u64 { u32::MAX } else { e as u32 }
    }

    /// `log2` of the table's items in epoch `epoch`.
    pub const fn log_items(&self, epoch: u32) -> u32 {
        let room = self.max_log_dataset_items - self.log_dataset_items;
        self.log_dataset_items + if epoch < room { epoch } else { room }
    }

    /// `log2` of the items of the table the work of the block at
    /// `height` is of.
    pub const fn log_items_at(&self, height: u64) -> u32 {
        self.log_items(self.epoch_of(height))
    }

    const fn check(&self) {
        assert!(self.log_dataset_items >= 7 && self.log_dataset_items <= self.max_log_dataset_items);
        assert!(self.max_log_dataset_items <= 32, "an item's index is picked by one word");
        assert!(self.epoch_blocks > 0);
    }

    /// Whether a table of `2^log_items` items is one of the schedule's.
    const fn has_table(&self, log_items: u32) -> bool {
        log_items >= self.log_dataset_items && log_items <= self.max_log_dataset_items
    }
}

const _: () = PowParams::MAINNET.check();
const _: () = PowParams::DEV.check();

/// Bytes of a table of `2^log_items` items.
pub const fn table_bytes(log_items: u32) -> u64 {
    64u64 << log_items
}

/// Where window `w` begins: the windows are spread evenly, the first at
/// the text's first byte and the last ending at its last.
pub const fn window_offset(w: usize, len: usize) -> usize {
    ((w as u64 * (len - WINDOW) as u64) / (WINDOWS as u64 - 1)) as usize
}

/// A nonce with the number in its first eight bytes, for a search in
/// order.
pub fn nonce_from_u64(n: u64) -> Nonce {
    let mut out = [0u8; 32];
    out[..8].copy_from_slice(&n.to_le_bytes());
    out
}

/// The key an item's steps begin from: its index, under a mark.
pub fn first_key(index: usize) -> [u32; 8] {
    [index as u32, (index as u64 >> 32) as u32, DOM_POW_ITEM, 0, 0, 0, 0, 0]
}

/// Where a table's items come from: a table, or the text.
pub trait ItemSource {
    fn params(&self) -> &PowParams;
    /// `log2` of the table's items.
    fn log_items(&self) -> u32;
    fn item(&self, index: usize) -> Item;
    fn seed(&self) -> &SeedText<'_>;
}

/// The seed text, with the parameters items are made by.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct SeedText<'a> {
    params: PowParams,
    text: &'a [u8],
}

impl SeedText<'static> {
    /// The file in the binary.
    pub fn new(params: PowParams) -> SeedText<'static> {
        assert_eq!(SEED_TEXT_GZ.len(), SEED_TEXT_LEN, "the seed file is not the one expected");
        SeedText { params, text: SEED_TEXT_GZ }
    }
}

impl<'a> SeedText<'a> {
    /// Another text of the seed file's length: for tests.
    pub fn from_bytes(params: PowParams, text: &'a [u8]) -> SeedText<'a> {
        assert_eq!(text.len(), SEED_TEXT_LEN);
        SeedText { params, text }
    }

    pub fn params(&self) -> &PowParams {
        &self.params
    }

    /// Window `w`'s bytes.
    pub fn window(&self, w: usize) -> &'a [u8] {
        let at = window_offset(w, self.text.len());
        &self.text[at..at + WINDOW]
    }

    /// The windows an item is made of, in order, and the item. Its
    /// first key is its index under a mark; each of `parents` steps picks
    /// a window by the key's first word and hashes it under the key,
    /// which gives the next key. The item is the last key and the one
    /// before it. No other item enters, nor the table's size.
    fn item_and_windows(&self, index: usize, mut read: impl FnMut(usize)) -> Item {
        assert!(index as u64 >> self.params.max_log_dataset_items == 0, "no table has such an item");
        let mut state = first_key(index);
        let mut before = state;
        for _ in 0..self.params.parents {
            let w = state[0] as usize & (WINDOWS - 1);
            read(w);
            before = state;
            state = blake3::words(&blake3::keyed_hash(&blake3::bytes(&state), self.window(w)));
        }
        std::array::from_fn(|i| if i < 8 { state[i] } else { before[i - 8] })
    }

    /// Dataset item `index`.
    pub fn calc_dataset_item(&self, index: usize) -> Item {
        self.item_and_windows(index, |_| {})
    }

    /// The items of the table the block at `height` is mined with, each
    /// made from the file when asked for: what a verifier checks a
    /// header's work with.
    pub fn at(&self, height: u64) -> SeedItems<'a> {
        self.table(self.params.log_items_at(height))
    }

    /// The items of the table of `2^log_items` items, made when asked
    /// for.
    pub fn table(&self, log_items: u32) -> SeedItems<'a> {
        assert!(self.params.has_table(log_items), "no epoch has a table of 2^{log_items} items");
        SeedItems { seed: *self, log_items }
    }
}

/// A table's items made from the seed file as they are asked for: a
/// verifier's source. It holds no item.
#[derive(Clone, Copy)]
pub struct SeedItems<'a> {
    seed: SeedText<'a>,
    log_items: u32,
}

impl ItemSource for SeedItems<'_> {
    fn params(&self) -> &PowParams {
        &self.seed.params
    }

    fn log_items(&self) -> u32 {
        self.log_items
    }

    fn item(&self, index: usize) -> Item {
        self.seed.calc_dataset_item(index)
    }

    fn seed(&self) -> &SeedText<'_> {
        &self.seed
    }
}

/// A table made whole, in memory: for the small ones of tests and the
/// dev networks. A miner's is a [`LazyDataset`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Dataset<'a> {
    seed: SeedText<'a>,
    log_items: u32,
    items: Vec<Item>,
}

impl<'a> Dataset<'a> {
    pub fn generate(seed: &SeedText<'a>, log_items: u32) -> Dataset<'a> {
        assert!(seed.params.has_table(log_items));
        let mut items = vec![[0u32; 16]; 1 << log_items];
        crate::parallel::par_fill_min(&mut items, 16, |i| seed.calc_dataset_item(i));
        Dataset { seed: *seed, log_items, items }
    }
}

impl ItemSource for Dataset<'_> {
    fn params(&self) -> &PowParams {
        &self.seed.params
    }

    fn log_items(&self) -> u32 {
        self.log_items
    }

    fn item(&self, index: usize) -> Item {
        self.items[index]
    }

    fn seed(&self) -> &SeedText<'_> {
        &self.seed
    }
}

// ---------------------------------------------------------------------------
// A miner's table, filled as it is read
// ---------------------------------------------------------------------------

/// What begins a table's file.
const FILE_MAGIC: &[u8; 8] = b"tabtable";
/// Bytes of a table file before its bitmap: the magic, `log2` of its
/// items, and the parents of an item.
const FILE_HEADER: usize = 8 + 4 + 4;
/// Bytes of the checksum that ends a table's file.
const CHECKSUM_BYTES: usize = 8;

/// A checksum of a table's file against corruption (not forgery: the
/// sampled items guard the contents, the chain's blocks the rest): 64-bit
/// FNV-1a, taken a part of the file at a time, the same whatever compiler
/// built the node.
struct Checksum(u64);

impl Checksum {
    fn new() -> Checksum {
        Checksum(0xcbf2_9ce4_8422_2325)
    }

    fn update(&mut self, bytes: &[u8]) {
        for b in bytes {
            self.0 = (self.0 ^ *b as u64).wrapping_mul(0x0100_0000_01b3);
        }
    }

    fn finish(&self) -> [u8; CHECKSUM_BYTES] {
        self.0.to_le_bytes()
    }
}

/// A table as a miner holds it: all of its memory taken when it is made,
/// and its items computed from the seed file as they are first read, a
/// pair at a time, and kept. Threads share one by reference: reading and
/// filling need no lock, and two threads that fill the same pair write
/// the same values.
pub struct LazyDataset<'a> {
    seed: SeedText<'a>,
    log_items: u32,
    /// The items' words, 16 an item.
    words: Vec<AtomicU32>,
    /// A bit for each pair of items that is there: set after its elements
    /// are written.
    present: Vec<AtomicU64>,
    /// How many pairs are there.
    filled: AtomicUsize,
}

impl<'a> LazyDataset<'a> {
    /// Pairs of adjacent items in the table: what a hash reads.
    pub fn pairs(&self) -> usize {
        1 << (self.log_items - 1)
    }

    /// An empty table of `2^log_items` items: its whole memory
    /// ([`table_bytes`]) is allocated and written to now, so that a machine
    /// without room for it fails here and not while mining.
    pub fn new(seed: &SeedText<'a>, log_items: u32) -> std::io::Result<LazyDataset<'a>> {
        assert!(seed.params.has_table(log_items), "no epoch has a table of 2^{log_items} items");
        let _in = crate::heap::enter(crate::heap::Part::Table);
        let no_room = |_| std::io::Error::new(std::io::ErrorKind::OutOfMemory, "no memory for the dataset");
        let (n, pairs) = (16usize << log_items, 1usize << (log_items - 1));
        let mut words = Vec::new();
        words.try_reserve_exact(n).map_err(no_room)?;
        // Every word is written: the memory is the process's from here on,
        // not a promise of it. (The value is hidden from the compiler, or a
        // zero written to zeroed memory could be left out.)
        words.extend((0..n).map(|_| AtomicU32::new(std::hint::black_box(0))));
        let mut present = Vec::new();
        present.try_reserve_exact(pairs / 64).map_err(no_room)?;
        present.extend((0..pairs / 64).map(|_| AtomicU64::new(0)));
        Ok(LazyDataset { seed: *seed, log_items, words, present, filled: AtomicUsize::new(0) })
    }

    /// A table of `2^log_items` items with what the file at `path` holds
    /// of it ([`LazyDataset::save`]): a file of a smaller table, of an
    /// earlier epoch, holds its first items. Empty if there is no file.
    pub fn open(seed: &SeedText<'a>, log_items: u32, path: &std::path::Path) -> std::io::Result<LazyDataset<'a>> {
        let table = Self::new(seed, log_items)?;
        // A file that is not a table's leaves it empty: no pair is
        // marked as there until the whole file is known to be good.
        table.load(path);
        Ok(table)
    }

    /// Makes the table one of `2^log_items` items, for a later epoch: the
    /// items it has stay where they are, and room for the rest is taken
    /// and written to now, to be filled as it is read.
    pub fn grow(&mut self, log_items: u32) -> std::io::Result<()> {
        assert!(self.seed.params.has_table(log_items), "no epoch has a table of 2^{log_items} items");
        assert!(log_items >= self.log_items, "a table does not shrink");
        let no_room = |_| std::io::Error::new(std::io::ErrorKind::OutOfMemory, "no memory for the dataset");
        let (n, pairs) = (16usize << log_items, 1usize << (log_items - 1));
        self.words.try_reserve_exact(n - self.words.len()).map_err(no_room)?;
        self.present.try_reserve_exact(pairs / 64 - self.present.len()).map_err(no_room)?;
        let have = self.words.len();
        self.words.extend((have..n).map(|_| AtomicU32::new(std::hint::black_box(0))));
        let have = self.present.len();
        self.present.extend((have..pairs / 64).map(|_| AtomicU64::new(0)));
        self.log_items = log_items;
        Ok(())
    }

    /// Pairs of items that are there.
    pub fn filled(&self) -> usize {
        self.filled.load(Ordering::Acquire)
    }

    /// Whether every item is there: the table is as fast as it gets.
    pub fn is_complete(&self) -> bool {
        self.filled() == self.pairs()
    }

    fn has(&self, pair: usize) -> bool {
        self.present[pair / 64].load(Ordering::Acquire) >> (pair % 64) & 1 == 1
    }

    /// Records that `pair`'s elements are written.
    fn mark(&self, pair: usize) {
        let bit = 1u64 << (pair % 64);
        if self.present[pair / 64].fetch_or(bit, Ordering::AcqRel) & bit == 0 {
            self.filled.fetch_add(1, Ordering::AcqRel);
        }
    }

    fn write(&self, index: usize, item: &Item) {
        for (w, x) in self.words[index * 16..(index + 1) * 16].iter().zip(item) {
            w.store(*x, Ordering::Relaxed);
        }
    }

    fn read(&self, index: usize) -> Item {
        let words = &self.words[index * 16..(index + 1) * 16];
        core::array::from_fn(|k| words[k].load(Ordering::Relaxed))
    }

    /// Computes `pair`'s two items from the file and keeps them, if they
    /// are not there.
    fn ensure(&self, pair: usize) {
        if !self.has(pair) {
            for index in [2 * pair, 2 * pair + 1] {
                self.write(index, &self.seed.calc_dataset_item(index));
            }
            self.mark(pair);
        }
    }

    /// Computes every item not yet there, using all available threads.
    pub fn fill(&self) {
        crate::parallel::par_map_min(self.pairs(), 1, |pair| self.ensure(pair));
    }

    /// Writes the table to `path`, by way of a file beside it: its size,
    /// which pairs are there, every item, and a checksum. A table can be
    /// saved while it is mined with; pairs filled meanwhile may be left
    /// for next time.
    pub fn save(&self, path: &std::path::Path) -> std::io::Result<()> {
        let tmp = path.with_extension("tmp");
        let mut file = std::io::BufWriter::with_capacity(1 << 16, std::fs::File::create(&tmp)?);
        let mut sum = Checksum::new();
        let mut put = |file: &mut std::io::BufWriter<std::fs::File>, bytes: &[u8]| {
            sum.update(bytes);
            file.write_all(bytes)
        };
        put(&mut file, &file_header(self.log_items, self.seed.params.parents))?;
        // The bitmap first: a pair it says is there was whole before it was
        // read, and stays whole.
        for w in &self.present {
            put(&mut file, &w.load(Ordering::Acquire).to_le_bytes())?;
        }
        for index in 0..1usize << self.log_items {
            put(&mut file, &item_to_bytes(&self.read(index)))?;
        }
        file.write_all(&sum.finish())?;
        file.flush()?;
        drop(file);
        std::fs::rename(&tmp, path)
    }

    /// Takes in the pairs the file at `path` holds, if it is a table's of
    /// this size or a smaller one of the schedule's: with a table's
    /// header, of the size that says, the checksum
    /// right, and a few of its pairs as the seed file makes them. Returns
    /// whether it was. Pairs are marked as there only at the end, so a
    /// file refused part way leaves the table as it was.
    fn load(&self, path: &std::path::Path) -> bool {
        let params = &self.seed.params;
        let read = || -> Option<()> {
            let file = std::fs::File::open(path).ok()?;
            let size = file.metadata().ok()?.len();
            let mut file = std::io::BufReader::with_capacity(1 << 16, file);
            let mut sum = Checksum::new();
            let mut header = [0u8; FILE_HEADER];
            file.read_exact(&mut header).ok()?;
            sum.update(&header);
            // The file's table: one of the schedule's, no larger than this.
            let log_items = u32::from_le_bytes(header[8..12].try_into().unwrap());
            if !params.has_table(log_items) || log_items > self.log_items {
                return None;
            }
            let pairs = 1usize << (log_items - 1);
            if header != file_header(log_items, params.parents)
                || size != (FILE_HEADER + pairs / 8 + CHECKSUM_BYTES) as u64 + table_bytes(log_items)
            {
                return None;
            }
            // Which pairs the file has: marked here only once the whole
            // file is known to be good.
            let mut there = vec![0u64; pairs / 64];
            for w in there.iter_mut() {
                let mut b = [0u8; 8];
                file.read_exact(&mut b).ok()?;
                sum.update(&b);
                *w = u64::from_le_bytes(b);
            }
            let mut buf = [0u8; ITEM_BYTES];
            for index in 0..2 * pairs {
                file.read_exact(&mut buf).ok()?;
                sum.update(&buf);
                self.write(index, &item_from_bytes(&buf));
            }
            let mut stored = [0u8; CHECKSUM_BYTES];
            file.read_exact(&mut stored).ok()?;
            if stored != sum.finish() {
                return None;
            }
            // Up to eight of the pairs it has, spread through them.
            let has = |pair: usize| there[pair / 64] >> (pair % 64) & 1 == 1;
            let held = (0..pairs).filter(|p| has(*p)).count();
            for (seen, pair) in (0..pairs).filter(|p| has(*p)).enumerate() {
                if held <= 8 || seen % (held / 8) == 0 || seen == held - 1 {
                    for index in [2 * pair, 2 * pair + 1] {
                        if self.read(index) != self.seed.calc_dataset_item(index) {
                            return None;
                        }
                    }
                }
            }
            for pair in (0..pairs).filter(|p| has(*p)) {
                self.mark(pair);
            }
            Some(())
        };
        read().is_some()
    }
}

/// What begins the file of a table of `2^log_items` items of `parents`
/// steps each.
fn file_header(log_items: u32, parents: usize) -> [u8; FILE_HEADER] {
    let mut h = [0u8; FILE_HEADER];
    h[..8].copy_from_slice(FILE_MAGIC);
    h[8..12].copy_from_slice(&log_items.to_le_bytes());
    h[12..].copy_from_slice(&(parents as u32).to_le_bytes());
    h
}

impl core::fmt::Debug for LazyDataset<'_> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("LazyDataset")
            .field("log_items", &self.log_items)
            .field("filled", &self.filled())
            .field("pairs", &self.pairs())
            .finish_non_exhaustive()
    }
}

impl ItemSource for LazyDataset<'_> {
    fn params(&self) -> &PowParams {
        &self.seed.params
    }

    fn log_items(&self) -> u32 {
        self.log_items
    }

    /// Item `index`: read if its pair is there, computed with its pair and
    /// kept if not.
    #[inline]
    fn item(&self, index: usize) -> Item {
        self.ensure(index / 2);
        self.read(index)
    }

    fn seed(&self) -> &SeedText<'_> {
        &self.seed
    }
}

/// Bytes of one item in a file.
const ITEM_BYTES: usize = 64;

fn item_from_bytes(bytes: &[u8; ITEM_BYTES]) -> Item {
    core::array::from_fn(|k| u32::from_le_bytes(bytes[4 * k..4 * k + 4].try_into().unwrap()))
}

fn item_to_bytes(item: &Item) -> [u8; ITEM_BYTES] {
    let mut out = [0u8; ITEM_BYTES];
    for (b, x) in out.chunks_exact_mut(4).zip(item) {
        b.copy_from_slice(&x.to_le_bytes());
    }
    out
}

/// The seed of a header's work: a hash of the header's hash and the
/// nonce.
fn seed(header_hash: &Digest, nonce: &Nonce) -> [u32; 8] {
    blake3::words(&hash_domain(DOM_POW_SEED, &[&header_hash[..], nonce].concat()))
}

fn result(mix: &Digest, seed: &[u32; 8]) -> Digest {
    hash_domain(DOM_POW_RESULT, &[&mix[..], &blake3::bytes(seed)].concat())
}

/// The result for a mix a header claims: two compressions and no table.
/// A cheap check before the work is done again.
pub fn result_from_mix(header_hash: &Digest, nonce: &Nonce, mix: &Digest) -> Digest {
    result(mix, &seed(header_hash, nonce))
}

/// What one evaluation of the work gives.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PowOutput {
    /// The mix, folded: kept in the header, for verifiers to check.
    pub mix: Digest,
    /// The hash that is held against the target.
    pub result: Digest,
}

/// What a hash reads, for whoever wants to know: an item's index, or a
/// window read directly.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Read {
    Item(usize),
    Window(usize),
}

fn hashimoto_reading<S: ItemSource>(
    source: &S,
    header_hash: &Digest,
    nonce: &Nonce,
    mut read: impl FnMut(Read),
) -> PowOutput {
    let params = source.params();
    let text = source.seed();
    let seed = seed(header_hash, nonce);
    let mut mix: [u32; MIX_WORDS] = std::array::from_fn(|k| seed[k % 8]);
    let pairs = 1usize << (source.log_items() - 1);
    for i in 0..params.accesses {
        let sel = fnv(i as u32 ^ seed[0], mix[0]);
        let sel2 = fnv(i as u32 ^ seed[1], mix[16]);
        let idx = (sel as usize & (pairs - 1)) * 2;
        let window = sel2 as usize & (WINDOWS - 1);
        read(Read::Item(idx));
        read(Read::Item(idx + 1));
        read(Read::Window(window));
        let x: [u32; 16] = blake3::words(text.window(window));
        let (a, b) = (source.item(idx), source.item(idx + 1));
        for (k, (m, d)) in mix.iter_mut().zip(a.iter().chain(&b)).enumerate() {
            *m = fnv(*m, *d) ^ x[k % 16];
        }
    }
    let mix = hash_domain(DOM_POW_MIX, &mix.iter().flat_map(|w| w.to_le_bytes()).collect::<Vec<u8>>());
    PowOutput { mix, result: result(&mix, &seed) }
}

/// The memory-hard hash of a header's hash and a nonce, with `source`
/// for the table's items and the seed file. Each access folds in two
/// adjacent items, picked by `fnv(i ^ seed[0], mix[0])` among the
/// table's pairs, and one window of the file, picked by
/// `fnv(i ^ seed[1], mix[16])`: the window's word `k % 16` is folded
/// into the mix's word `k` after its item's. The mix is then hashed.
pub fn hashimoto<S: ItemSource>(source: &S, header_hash: &Digest, nonce: &Nonce) -> PowOutput {
    hashimoto_reading(source, header_hash, nonce, |_| {})
}

/// Whether `mix` is the true mix of the header's work and its result
/// meets `target`: by a table with the seed file, or by the file alone.
pub fn verify<S: ItemSource>(source: &S, header_hash: &Digest, nonce: &Nonce, mix: &Digest, target: &Target) -> bool {
    let out = hashimoto(source, header_hash, nonce);
    out.mix == *mix && target.is_met_by(&out.result)
}

/// Tries nonces in `nonces` until one meets `target`.
pub fn mine<S: ItemSource>(
    source: &S,
    header_hash: &Digest,
    target: &Target,
    nonces: impl IntoIterator<Item = Nonce>,
) -> Option<(Nonce, PowOutput)> {
    nonces.into_iter().map(|n| (n, hashimoto(source, header_hash, &n))).find(|(_, o)| target.is_met_by(&o.result))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn text() -> SeedText<'static> {
        SeedText::new(PowParams::DEV)
    }

    #[test]
    fn the_windows_cover_the_file() {
        let mut covered = vec![0u8; SEED_TEXT_LEN];
        for w in 0..WINDOWS {
            let at = window_offset(w, SEED_TEXT_LEN);
            assert!(at + WINDOW <= SEED_TEXT_LEN);
            covered[at..at + WINDOW].iter_mut().for_each(|c| *c += 1);
        }
        assert_eq!(
            (window_offset(0, SEED_TEXT_LEN), window_offset(WINDOWS - 1, SEED_TEXT_LEN)),
            (0, SEED_TEXT_LEN - WINDOW)
        );
        assert!(covered.iter().all(|c| (1..=2).contains(c)));
        // The file is the one the chain is to keep: a gzip file.
        assert_eq!(SEED_TEXT_GZ[..2], [0x1F, 0x8B]);
    }

    #[test]
    fn a_table_s_items_are_the_text_s() {
        let seed = text();
        let table = Dataset::generate(&seed, 10);
        for i in [0, 1, 513, 1023] {
            assert_eq!(table.item(i), seed.calc_dataset_item(i));
        }
        assert_ne!(table.item(0), table.item(1));
        // And every hash made of them is the same either way.
        let (hash, nonce) = ([7u8; 32], nonce_from_u64(3));
        let out = hashimoto(&table, &hash, &nonce);
        assert_eq!(out, hashimoto(&seed.table(10), &hash, &nonce));
        assert_eq!(out.result, result_from_mix(&hash, &nonce, &out.mix));
        assert!(verify(&seed.table(10), &hash, &nonce, &out.mix, &Target::MAX));
        assert!(!verify(&seed.table(10), &hash, &nonce, &[0; 32], &Target::MAX));
        assert!(!verify(&seed.table(10), &hash, &nonce, &out.mix, &Target::from_leading_zero_bits(248)));
        assert_ne!(out, hashimoto(&table, &hash, &nonce_from_u64(4)));
        assert_ne!(out, hashimoto(&table, &[8u8; 32], &nonce));
    }

    #[test]
    fn another_text_is_other_work() {
        // A byte of the file changed, in a window an item reads: that
        // item is another, and an item that reads no window with the
        // byte is as it was.
        let seed = text();
        let windows = |i: usize| {
            let mut read = Vec::new();
            seed.item_and_windows(i, |w| read.push(w));
            read
        };
        let byte = window_offset(windows(0)[100], SEED_TEXT_LEN) + 20;
        let mut other = SEED_TEXT_GZ.to_vec();
        other[byte] ^= 1;
        let changed = SeedText::from_bytes(PowParams::DEV, &other);
        assert_ne!(seed.calc_dataset_item(0), changed.calc_dataset_item(0));
        let reads_it =
            |i: usize| windows(i).iter().any(|w| (window_offset(*w, SEED_TEXT_LEN)..).take(WINDOW).any(|b| b == byte));
        let clear = (1..64).find(|i| !reads_it(*i)).unwrap();
        assert_eq!(seed.calc_dataset_item(clear), changed.calc_dataset_item(clear));
    }

    /// The bytes of the file one header's work reads when it is checked
    /// from the file, marked in `seen`.
    fn reads(seed: &SeedText, header: u64, seen: &mut [bool]) {
        let hash = hash_domain(DOM_POW_SEED, &header.to_le_bytes());
        let mut mark = |w: usize| {
            let at = window_offset(w, SEED_TEXT_LEN);
            seen[at..at + WINDOW].iter_mut().for_each(|s| *s = true);
        };
        let mut items = Vec::new();
        hashimoto_reading(&seed.table(seed.params.log_dataset_items), &hash, &nonce_from_u64(header), |r| match r {
            Read::Item(i) => items.push(i),
            Read::Window(w) => mark(w),
        });
        for i in items {
            seed.item_and_windows(i, &mut mark);
        }
    }

    #[test]
    fn checking_work_needs_the_file() {
        // One header's work, checked from the file, reads most of it, at
        // places its hash picks; a few headers' read all of it.
        let seed = SeedText::new(PowParams::MAINNET);
        let mut all = vec![false; SEED_TEXT_LEN];
        let mut blocks_to_all = 0;
        let mut least = 1.0f64;
        for header in 0..40 {
            let mut one = vec![false; SEED_TEXT_LEN];
            reads(&seed, header, &mut one);
            let part = one.iter().filter(|s| **s).count() as f64 / SEED_TEXT_LEN as f64;
            least = least.min(part);
            all.iter_mut().zip(&one).for_each(|(a, o)| *a |= *o);
            if blocks_to_all == 0 && all.iter().all(|s| *s) {
                blocks_to_all = header + 1;
            }
        }
        println!(
            "a header's work reads at least {:.1}% of the file; {blocks_to_all} headers read all of it",
            100.0 * least
        );
        assert!(least > 0.7, "{least}");
        assert!((1..=30).contains(&blocks_to_all), "{blocks_to_all}");
    }

    /// A table that does not grow, as small as the dev networks'.
    const SMALL: PowParams = PowParams::DEV;
    /// One that grows: 16 KB doubling to 64 KB, in epochs of 100 blocks.
    const GROWING: PowParams =
        PowParams { log_dataset_items: 8, max_log_dataset_items: 10, epoch_blocks: 100, ..SMALL };

    fn small_seed() -> &'static SeedText<'static> {
        static SEED: std::sync::OnceLock<SeedText<'static>> = std::sync::OnceLock::new();
        SEED.get_or_init(|| SeedText::new(SMALL))
    }

    /// The table's items from the file alone: a verifier's source.
    fn small_items() -> SeedItems<'static> {
        small_seed().at(0)
    }

    fn small_dataset() -> &'static Dataset<'static> {
        static DATASET: std::sync::OnceLock<Dataset<'static>> = std::sync::OnceLock::new();
        DATASET.get_or_init(|| Dataset::generate(small_seed(), 10))
    }

    fn d(n: u32) -> Digest {
        core::array::from_fn(|i| (n as u8).wrapping_add(i as u8) ^ (n >> 8) as u8)
    }

    /// 64-bit FNV-1a, as a table's file is summed.
    fn fnv1a64(bytes: &[u8]) -> u64 {
        bytes.iter().fold(0xcbf2_9ce4_8422_2325, |h, b| (h ^ *b as u64).wrapping_mul(0x0100_0000_01b3))
    }

    fn temp_dir(name: &str) -> std::path::PathBuf {
        let dir = std::env::temp_dir().join(format!("tabminer-pow-{name}-{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        dir
    }

    /// A miner's table starts empty and fills as it is read: every hash is
    /// the one a whole table gives, the pairs a hash read are there after
    /// it, and several threads mining with one table fill it between them.
    #[test]
    fn a_lazy_table_fills_as_it_is_read() {
        let seed = small_seed();
        let whole = small_dataset();
        let table = LazyDataset::new(seed, 10).unwrap();
        assert_eq!((table.pairs(), table.filled(), table.is_complete()), (512, 0, false));
        assert_eq!((table.log_items(), table.params(), table.seed()), (10, &SMALL, seed));
        assert!(format!("{table:?}").contains("filled: 0"));
        // One item asked for brings its pair.
        assert_eq!(table.item(77), whole.item(77));
        assert_eq!(table.filled(), 1);
        assert!(table.has(38) && !table.has(39));
        assert_eq!((table.item(76), table.filled()), (whole.item(76), 1));
        // A hash reads at most 64 pairs, and gives what the whole table gives.
        let h = d(700);
        let out = hashimoto(&table, &h, &nonce_from_u64(5));
        assert_eq!(out, hashimoto(whole, &h, &nonce_from_u64(5)));
        let after_one = table.filled();
        assert!((2..=65).contains(&after_one), "{after_one} pairs after one hash");
        // The same hash again reads only what is there.
        assert_eq!(hashimoto(&table, &h, &nonce_from_u64(5)), out);
        assert_eq!(table.filled(), after_one);
        // Threads mining together: each hash right, the table filling.
        std::thread::scope(|s| {
            for t in 0..4u64 {
                let table = &table;
                s.spawn(move || {
                    for n in 0..60 {
                        let nonce = nonce_from_u64(t << 32 | n);
                        assert_eq!(hashimoto(table, &h, &nonce), hashimoto(whole, &h, &nonce));
                    }
                });
            }
        });
        assert!(table.filled() > 500, "{} of 512 pairs after 240 hashes", table.filled());
        // What is left is computed outright, and nothing is counted twice.
        table.fill();
        assert!(table.is_complete());
        assert_eq!(table.filled(), 512);
        for i in 0..1024 {
            assert_eq!(table.item(i), whole.item(i), "item {i}");
        }
        table.fill();
        assert_eq!(table.filled(), 512);
        // Mining with it finds what mining with a whole table finds.
        let target = Target::from_leading_zero_bits(6);
        assert_eq!(
            mine(&table, &h, &target, (0..10_000).map(nonce_from_u64)),
            mine(whole, &h, &target, (0..10_000).map(nonce_from_u64))
        );
    }

    /// At the next epoch a table is grown where it is: the items it had
    /// are still there, the new half is empty and fills as it is read, and
    /// a hash is the larger table's.
    #[test]
    fn a_table_grows_where_it_is() {
        let seed = SeedText::new(GROWING);
        let whole = Dataset::generate(&seed, 10);
        let h = d(55);
        let mut table = LazyDataset::new(&seed, 8).unwrap();
        table.fill();
        assert_eq!((table.pairs(), table.filled()), (128, 128));
        let nonce = nonce_from_u64(3);
        let small = hashimoto(&table, &h, &nonce);
        assert_eq!(small, hashimoto(&seed.table(8), &h, &nonce));
        // Grown for the next epoch: the first half as it was, the second to come.
        table.grow(9).unwrap();
        assert_eq!((table.log_items(), table.pairs(), table.filled(), table.is_complete()), (9, 256, 128, false));
        assert!((0..128).all(|p| table.has(p)) && (128..256).all(|p| !table.has(p)));
        for i in 0..256 {
            assert_eq!(table.read(i), whole.item(i), "item {i}");
        }
        // Mined with: the new epoch's hashes, the new half filling.
        let large = hashimoto(&table, &h, &nonce);
        assert_eq!(large, hashimoto(&seed.table(9), &h, &nonce));
        assert_ne!(large, small);
        assert!(table.filled() > 128 && table.filled() < 256, "{} pairs", table.filled());
        for n in 0..20 {
            let nonce = nonce_from_u64(n);
            assert_eq!(hashimoto(&table, &h, &nonce), hashimoto(&seed.table(9), &h, &nonce));
        }
        // And again from a table part filled; growing to the size it is changes nothing.
        let part = table.filled();
        table.grow(10).unwrap();
        table.grow(10).unwrap();
        assert_eq!((table.pairs(), table.filled()), (512, part));
        assert_eq!(hashimoto(&table, &h, &nonce), hashimoto(&seed.table(10), &h, &nonce));
        table.fill();
        assert!(table.is_complete());
        for i in 0..1024 {
            assert_eq!(table.item(i), whole.item(i), "item {i}");
        }
        // A table does not shrink, nor grow past the last epoch's.
        let quiet = crate::test_util::Quiet::new();
        assert!(
            std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| LazyDataset::new(&seed, 9).unwrap().grow(8)))
                .is_err()
        );
        assert!(
            std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| LazyDataset::new(&seed, 9).unwrap().grow(11)))
                .is_err()
        );
        drop(quiet);
    }

    /// A table is saved as far as it is filled and taken up again from its
    /// file, by a table of its size or by the larger one of a later epoch;
    /// a file of a larger table, of other work, with a byte changed or
    /// with an item that is not the text's is not taken, and the table
    /// starts empty.
    #[test]
    fn lazy_tables_are_saved_and_loaded() {
        // Sizes no build has built in: 32 KB growing to 128 KB.
        const SAVED: PowParams = PowParams { log_dataset_items: 9, max_log_dataset_items: 11, parents: 16, ..SMALL };
        let seed = SeedText::new(SAVED);
        let whole = Dataset::generate(&seed, 11);
        let dir = temp_dir("tables");
        let path = dir.join("table.bin");
        // No file: an empty table.
        let table = LazyDataset::open(&seed, 9, &path).unwrap();
        assert_eq!(table.filled(), 0);
        // Part filled, saved, and taken up again.
        let h = d(1);
        for n in 0..3 {
            hashimoto(&table, &h, &nonce_from_u64(n));
        }
        let part = table.filled();
        assert!(part > 60 && part < 256, "{part} pairs");
        table.save(&path).unwrap();
        assert!(!dir.join("table.tmp").exists());
        let size = FILE_HEADER + 256 / 8 + 512 * ITEM_BYTES + CHECKSUM_BYTES;
        assert_eq!(std::fs::metadata(&path).unwrap().len(), size as u64);
        let again = LazyDataset::open(&seed, 9, &path).unwrap();
        assert_eq!(again.filled(), part);
        for pair in 0..256 {
            assert_eq!(again.has(pair), table.has(pair), "pair {pair}");
        }
        for i in 0..512 {
            assert_eq!(again.item(i), whole.item(i), "item {i}");
        }
        assert!(again.is_complete());
        // Whole, saved, and loaded whole.
        again.save(&path).unwrap();
        let good = std::fs::read(&path).unwrap();
        assert_eq!(good.len(), size);
        assert_eq!(&good[..8], FILE_MAGIC);
        assert_eq!(
            good[FILE_HEADER + 32..size - CHECKSUM_BYTES],
            whole.items[..512].iter().flat_map(item_to_bytes).collect::<Vec<u8>>()
        );
        assert_eq!(good[size - CHECKSUM_BYTES..], fnv1a64(&good[..size - CHECKSUM_BYTES]).to_le_bytes());
        let loaded = LazyDataset::open(&seed, 9, &path).unwrap();
        assert!(loaded.is_complete());
        assert_eq!(hashimoto(&loaded, &h, &nonce_from_u64(9)), hashimoto(&seed.table(9), &h, &nonce_from_u64(9)));
        // The next epoch's table, twice the size, starts from that file:
        // the items it had are there and the new half is to come.
        let grown = LazyDataset::open(&seed, 10, &path).unwrap();
        assert_eq!((grown.pairs(), grown.filled()), (512, 256));
        assert!(grown.has(0) && grown.has(255) && !grown.has(256));
        assert_eq!(hashimoto(&grown, &h, &nonce_from_u64(9)), hashimoto(&seed.table(10), &h, &nonce_from_u64(9)));
        grown.fill();
        for i in 0..1024 {
            assert_eq!(grown.item(i), whole.item(i), "item {i}");
        }
        // And the one after that, from the first epoch's file or the second's.
        assert_eq!(LazyDataset::open(&seed, 11, &path).unwrap().filled(), 256);
        let second = dir.join("second.bin");
        grown.save(&second).unwrap();
        assert_eq!(LazyDataset::open(&seed, 11, &second).unwrap().filled(), 512);
        // A larger table's file is of no use to a smaller table.
        assert_eq!(LazyDataset::open(&seed, 9, &second).unwrap().filled(), 0);
        // A file that is not this table's: nothing is taken from it.
        let refused = |change: &dyn Fn(&mut Vec<u8>)| {
            let mut bytes = good.clone();
            change(&mut bytes);
            std::fs::write(&path, &bytes).unwrap();
            let t = LazyDataset::open(&seed, 9, &path).unwrap();
            let empty = t.filled() == 0;
            // It works all the same, from the seed file.
            assert_eq!(t.item(3), whole.item(3));
            empty
        };
        // With the checksum made to fit, so that it is what was changed that is refused.
        let refit = |b: &mut Vec<u8>| {
            let n = b.len() - CHECKSUM_BYTES;
            let sum = fnv1a64(&b[..n]).to_le_bytes();
            b[n..].copy_from_slice(&sum);
        };
        assert!(refused(&|b| b.truncate(b.len() - 1)), "a byte short");
        assert!(refused(&|b| b.push(0)), "a byte long");
        assert!(refused(&|b| b[FILE_HEADER + 32 + 1000] ^= 1), "an item changed");
        assert!(refused(&|b| *b.last_mut().unwrap() ^= 1), "the checksum changed");
        assert!(
            refused(&|b| {
                b[0] ^= 1;
                refit(b)
            }),
            "not a table's file"
        );
        assert!(
            refused(&|b| {
                b[8] = 8;
                refit(b)
            }),
            "a size no epoch has"
        );
        assert!(
            refused(&|b| {
                b[8] = 10;
                refit(b)
            }),
            "a size the file is not"
        );
        assert!(
            refused(&|b| {
                b[12] ^= 1;
                refit(b)
            }),
            "other parents"
        );
        assert!(
            refused(&|b| {
                b[FILE_HEADER + 32] ^= 1;
                refit(b)
            }),
            "the first item is not the text's"
        );
        assert!(
            refused(&|b| {
                let at = b.len() - CHECKSUM_BYTES - 4;
                b[at] ^= 1;
                refit(b)
            }),
            "the last item is not the text's"
        );
        // Another network's table of that size is of other work.
        std::fs::write(&path, &good).unwrap();
        let other = SeedText::new(PowParams { log_dataset_items: 9, ..SMALL });
        assert_eq!(LazyDataset::open(&other, 9, &path).unwrap().filled(), 0);
        assert_eq!(LazyDataset::open(&seed, 9, &path).unwrap().filled(), 256);
        // A pair the bitmap does not have is not taken, whatever its bytes.
        let mut holed = good.clone();
        holed[FILE_HEADER] &= !1;
        refit(&mut holed);
        std::fs::write(&path, &holed).unwrap();
        let t = LazyDataset::open(&seed, 9, &path).unwrap();
        assert_eq!((t.filled(), t.has(0), t.has(1)), (255, false, true));
        std::fs::remove_dir_all(&dir).unwrap();
    }

    #[test]
    fn mine_and_verify() {
        let seed = small_items();
        let dataset = small_dataset();
        let h: Digest = core::array::from_fn(|i| 7 * i as u8 + 1);
        let target = Target::from_leading_zero_bits(6);
        let (nonce, out) = mine(dataset, &h, &target, (0..10_000).map(nonce_from_u64)).expect("a nonce within range");
        assert!(target.is_met_by(&out.result));
        assert!(verify(&seed, &h, &nonce, &out.mix, &target));
        let mut other = nonce;
        other[9] ^= 1;
        assert!(!verify(&seed, &h, &other, &out.mix, &target));
        let mut bad_mix = out.mix;
        bad_mix[0] ^= 1;
        assert!(!verify(&seed, &h, &nonce, &bad_mix, &target));
        assert!(!verify(&seed, &h, &nonce, &out.mix, &Target::from_leading_zero_bits(200)));
    }

    /// The table doubles each epoch, a year of blocks, up to its
    /// ceiling: by epoch, and by the height of the block whose work it
    /// is of. What a block is mined with and checked against follows.
    #[test]
    fn the_table_doubles_each_epoch_to_its_ceiling() {
        let m = PowParams::MAINNET;
        let year = 52_560u64;
        assert_eq!(m.epoch_blocks as u64, year);
        for (height, epoch) in
            [(0, 0), (1, 0), (year - 1, 0), (year, 1), (2 * year - 1, 1), (5 * year, 5), (1007 * year, 1007)]
        {
            assert_eq!(m.epoch_of(height), epoch, "height {height}");
        }
        assert_eq!(m.epoch_of(u64::MAX), u32::MAX);
        let gb = 1u64 << 30;
        for (epoch, size) in [
            (0, gb),
            (1, 2 * gb),
            (2, 4 * gb),
            (3, 8 * gb),
            (4, 16 * gb),
            (5, 32 * gb),
            (6, 32 * gb),
            (1000, 32 * gb),
            (u32::MAX, 32 * gb),
        ] {
            assert_eq!(table_bytes(m.log_items(epoch)), size, "epoch {epoch}");
        }
        for (height, size) in
            [(0, gb), (year - 1, gb), (year, 2 * gb), (5 * year - 1, 16 * gb), (5 * year, 32 * gb), (u64::MAX, 32 * gb)]
        {
            assert_eq!(table_bytes(m.log_items_at(height)), size, "height {height}");
            assert_eq!(table_bytes(SeedText::new(m).at(height).log_items()), size, "height {height}");
        }
        // The dev networks' table stays as it is.
        assert_eq!(table_bytes(PowParams::DEV.log_items_at(u64::MAX)), 64 << 10);
        // A table that grows: the work of a block is of the table of
        // its height, and is no work against the one of the year
        // before.
        let growing = SeedText::new(GROWING);
        let (first, later) = (0u64, GROWING.epoch_blocks as u64);
        assert_eq!(GROWING.log_items_at(later), GROWING.log_items_at(first) + 1);
        let (header, nonce) = ([3u8; 32], nonce_from_u64(5));
        let (was, is) =
            (hashimoto(&growing.at(first), &header, &nonce), hashimoto(&growing.at(later), &header, &nonce));
        assert_ne!((was.mix, was.result), (is.mix, is.result));
        // A table no epoch has is asked for by nobody.
        for log_items in [GROWING.log_dataset_items - 1, GROWING.max_log_dataset_items + 1] {
            assert!(std::panic::catch_unwind(|| growing.table(log_items)).is_err());
        }
    }

    /// The items depend on every part of the text: a byte changed
    /// anywhere, the first and the last included, changes items.
    #[test]
    fn items_depend_on_every_part_of_the_text() {
        let base = SEED_TEXT_GZ.to_vec();
        let a = SeedText::from_bytes(SMALL, &base);
        let items: Vec<Item> = (0..64).map(|i| a.calc_dataset_item(i)).collect();
        for at in [0usize, 30, SEED_TEXT_LEN / 2, SEED_TEXT_LEN - 30, SEED_TEXT_LEN - 1] {
            let mut text = base.clone();
            text[at] ^= 1;
            let b = SeedText::from_bytes(SMALL, &text);
            let changed = (0..64).filter(|&i| b.calc_dataset_item(i) != items[i]).count();
            assert!(changed >= 1, "byte {at}: no item of 64 changed");
        }
    }
}
