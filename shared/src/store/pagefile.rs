//! A file of pages that are written once and never changed, under a root
//! record that says which of them are the state.
//!
//! # Layout
//!
//! The file is counted in units of [`UNIT`] bytes. The first
//! [`HEADER_UNITS`] hold two slots for the root record; the rest is
//! pages, each an [`Extent`] of whole units:
//!
//! ```text
//! page := checksum (4) | length (4) | payload | zeros to the unit
//! root := magic (8) | sequence (8) | length (4) | payload | checksum (4)
//! ```
//!
//! A page's checksum covers where it lies as well as what it holds, so a
//! page read from the wrong place is refused like a damaged one. A root
//! record is one unit: the device writes it whole or not at all.
//!
//! # A transaction
//!
//! One at a time ([`PageFile::begin`]). It writes new pages into free
//! space and names the pages it replaces ([`Txn::free`]), which stay as
//! they are. To commit, the pages are made durable, then the root record
//! with the next sequence number is written to the slot the last one is
//! not in, and that is made durable. The record is the commit: before it
//! the file holds the old state and some unreferenced pages, after it the
//! new.
//!
//! Dropped without committing, a transaction gives back what it took and
//! the file is as it was.
//!
//! # Opening
//!
//! The root record is the valid one with the higher sequence number. The
//! map of free space is not stored: whoever knows what the pages mean
//! walks them from the root as it was at opening, marks each
//! ([`PageFile::mark`]) and then seals the map ([`PageFile::seal`]).
//! Pages written by a transaction that never committed are reached by
//! nothing, so they are free.
//!
//! A large file has millions of pages to walk, and transactions do not
//! wait for it. Until the map is sealed a new page goes past the end of
//! the file, where nothing can be, and no page is given back: what
//! transactions free meanwhile waits, and is given back at the sealing,
//! when every page of the root at opening has been marked and the map
//! is whole.
//!
//! # Readers
//!
//! A [`Pin`] is a root record held: the pages it reaches are not reused
//! while it is held, however many transactions commit meanwhile. A page a
//! transaction frees goes back to the map when the commit is durable and
//! no pin is older than it.

use std::collections::{BTreeMap, HashMap, VecDeque};
use std::io;
use std::sync::{Mutex, MutexGuard};

use super::backend::{Backend, ReadReq, WriteReq};
use super::crc32c::crc32c;
use super::freemap::FreeMap;

/// Bytes in a unit of the file: what a device writes whole.
pub const UNIT: usize = 512;
/// Units at the start of the file kept for the root record's two slots.
pub const HEADER_UNITS: u64 = 16;
/// Where the two slots lie: in different 4 KB blocks of the device.
const SLOTS: [u64; 2] = [0, 4096];
const MAGIC: [u8; 8] = *b"tabstate";
/// Bytes before a root record's payload, and after it.
const ROOT_HEAD: usize = 20;
const ROOT_TAIL: usize = 4;
/// The most a root record's payload can be.
pub const ROOT_MAX: usize = UNIT - ROOT_HEAD - ROOT_TAIL;
/// Bytes of a page before its payload.
const PAGE_HEAD: usize = 8;
/// The longest page, in units: 64 KB.
pub const MAX_UNITS: u32 = 128;
/// A transaction's pages are written out whenever this many bytes wait.
const WRITE_BUFFER: usize = 1 << 20;

fn corrupt(what: &'static str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, what)
}

/// A page's place: `units` units from unit `start`.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct Extent {
    pub start: u64,
    pub units: u32,
}

impl Extent {
    /// Units a page of `payload` bytes takes.
    pub const fn units_for(payload: usize) -> u32 {
        (payload + PAGE_HEAD).div_ceil(UNIT) as u32
    }

    /// The most payload a page of `units` units holds.
    pub const fn capacity(units: u32) -> usize {
        units as usize * UNIT - PAGE_HEAD
    }

    /// Bytes of the file this page takes: what a buffer to read it into
    /// must hold.
    pub const fn bytes(&self) -> usize {
        self.units as usize * UNIT
    }

    const fn offset(&self) -> u64 {
        self.start * UNIT as u64
    }

    fn checksum(&self, payload: &[u8]) -> u32 {
        crc32c(&[&self.start.to_le_bytes(), &(payload.len() as u32).to_le_bytes(), payload])
    }

    /// Writes the page of `payload` into `out`, which is this extent's
    /// bytes.
    fn encode(&self, payload: &[u8], out: &mut [u8]) {
        debug_assert!(out.len() == self.bytes() && payload.len() <= Extent::capacity(self.units));
        out[..4].copy_from_slice(&self.checksum(payload).to_le_bytes());
        out[4..8].copy_from_slice(&(payload.len() as u32).to_le_bytes());
        out[PAGE_HEAD..PAGE_HEAD + payload.len()].copy_from_slice(payload);
        out[PAGE_HEAD + payload.len()..].fill(0);
    }

    /// The payload of the page read into `raw` from this extent, if it is
    /// the page that was written here.
    pub fn payload<'a>(&self, raw: &'a [u8]) -> io::Result<&'a [u8]> {
        if raw.len() < self.bytes() || self.units == 0 {
            return Err(corrupt("a page's buffer is shorter than the page"));
        }
        let sum = u32::from_le_bytes(raw[..4].try_into().unwrap());
        let len = u32::from_le_bytes(raw[4..8].try_into().unwrap()) as usize;
        if len > Extent::capacity(self.units) {
            return Err(corrupt("a page's length is more than the page"));
        }
        let payload = &raw[PAGE_HEAD..PAGE_HEAD + len];
        if self.checksum(payload) != sum {
            return Err(corrupt("a page's checksum does not match"));
        }
        Ok(payload)
    }
}

/// A root record: the sequence number of the commit that wrote it, and
/// what that commit said the state is.
#[derive(Clone, Copy)]
pub struct Root {
    pub seq: u64,
    len: u16,
    bytes: [u8; ROOT_MAX],
}

impl Root {
    fn new(seq: u64, payload: &[u8]) -> Root {
        assert!(payload.len() <= ROOT_MAX, "a root record's payload is at most {ROOT_MAX} bytes");
        let mut bytes = [0u8; ROOT_MAX];
        bytes[..payload.len()].copy_from_slice(payload);
        Root { seq, len: payload.len() as u16, bytes }
    }

    pub fn payload(&self) -> &[u8] {
        &self.bytes[..self.len as usize]
    }

    fn encode(&self) -> [u8; UNIT] {
        let mut out = [0u8; UNIT];
        let len = self.len as usize;
        out[..8].copy_from_slice(&MAGIC);
        out[8..16].copy_from_slice(&self.seq.to_le_bytes());
        out[16..20].copy_from_slice(&(len as u32).to_le_bytes());
        out[ROOT_HEAD..ROOT_HEAD + len].copy_from_slice(self.payload());
        let sum = crc32c(&[&out[..ROOT_HEAD + len]]);
        out[UNIT - ROOT_TAIL..].copy_from_slice(&sum.to_le_bytes());
        out
    }

    fn decode(raw: &[u8; UNIT]) -> Option<Root> {
        if raw[..8] != MAGIC {
            return None;
        }
        let seq = u64::from_le_bytes(raw[8..16].try_into().unwrap());
        let len = u32::from_le_bytes(raw[16..20].try_into().unwrap()) as usize;
        if len > ROOT_MAX || raw[ROOT_HEAD + len..UNIT - ROOT_TAIL].iter().any(|b| *b != 0) {
            return None;
        }
        let sum = u32::from_le_bytes(raw[UNIT - ROOT_TAIL..].try_into().unwrap());
        (crc32c(&[&raw[..ROOT_HEAD + len]]) == sum).then(|| Root::new(seq, &raw[ROOT_HEAD..ROOT_HEAD + len]))
    }

    /// The slot a record of sequence number `seq` is written to.
    const fn slot(seq: u64) -> u64 {
        SLOTS[(seq % 2) as usize]
    }
}

impl core::fmt::Debug for Root {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "Root {{ seq: {}, {} bytes }}", self.seq, self.len)
    }
}

/// Anything pages are read through: the file, a pin, a transaction.
pub trait ReadPages {
    /// Reads the page at `e` into `buf` (at least [`Extent::bytes`]
    /// long) and returns its payload.
    fn read_page<'b>(&self, e: Extent, buf: &'b mut [u8]) -> io::Result<&'b [u8]>;
}

impl<B: Backend> ReadPages for PageFile<B> {
    fn read_page<'b>(&self, e: Extent, buf: &'b mut [u8]) -> io::Result<&'b [u8]> {
        self.read(e, buf)
    }
}

impl<B: Backend> ReadPages for Pin<'_, B> {
    fn read_page<'b>(&self, e: Extent, buf: &'b mut [u8]) -> io::Result<&'b [u8]> {
        self.read(e, buf)
    }
}

impl<B: Backend> ReadPages for Txn<'_, B> {
    fn read_page<'b>(&self, e: Extent, buf: &'b mut [u8]) -> io::Result<&'b [u8]> {
        self.read(e, buf)
    }
}

struct State {
    root: Root,
    map: FreeMap,
    /// Whether the map is whole: every reachable page marked.
    sealed: bool,
    /// Until it is, the unit the next new page takes: past the end of
    /// the file as it was opened.
    append: u64,
    /// Pages freed by the commit of each sequence number, oldest first,
    /// that a pin may still reach.
    pending: VecDeque<(u64, Vec<Extent>)>,
    /// How many pins hold each sequence number.
    pins: BTreeMap<u64, usize>,
    /// A commit failed where the file's state can no longer be known.
    poisoned: bool,
}

impl State {
    /// Gives back the pages no pin can reach any more: those freed by a
    /// commit no later than the oldest pin's root.
    fn release(&mut self) {
        // Not before the map is whole: a page freed may not be marked
        // yet, and would be marked after.
        if !self.sealed {
            return;
        }
        let oldest = self.pins.keys().next().copied().unwrap_or(u64::MAX);
        while self.pending.front().is_some_and(|(seq, _)| *seq <= oldest) {
            let (_, freed) = self.pending.pop_front().unwrap();
            for e in freed {
                self.map.release(e.start, e.units as u64);
            }
        }
    }
}

/// A file of pages under a root record.
pub struct PageFile<B: Backend> {
    backend: B,
    state: Mutex<State>,
    writer: Mutex<()>,
    /// Set to stop a rebuilding of the map.
    stop: std::sync::atomic::AtomicBool,
}

impl<B: Backend> PageFile<B> {
    /// Makes an empty file of `backend`, which must hold nothing: a root
    /// record of sequence number 0 with no payload, made durable.
    pub fn create(backend: B) -> io::Result<PageFile<B>> {
        if !backend.is_empty()? {
            return Err(io::Error::new(io::ErrorKind::AlreadyExists, "the file is not empty"));
        }
        let root = Root::new(0, &[]);
        // Both slots' blocks exist from the start, so that reading the
        // other slot is never a read past the end.
        backend.write_at(0, &vec![0u8; HEADER_UNITS as usize * UNIT])?;
        backend.write_at(Root::slot(0), &root.encode())?;
        backend.sync()?;
        Ok(PageFile::with(backend, root, true, HEADER_UNITS))
    }

    /// Opens the file of `backend` at its last committed root. Its map of
    /// free space is empty: every page the root reaches must be marked
    /// ([`PageFile::mark`]) and the map sealed ([`PageFile::seal`])
    /// before a transaction can begin.
    pub fn open(backend: B) -> io::Result<PageFile<B>> {
        let mut best: Option<Root> = None;
        for at in SLOTS {
            let mut raw = [0u8; UNIT];
            // (A slot that cannot be read is not a slot with nothing in
            // it: it may hold the last root, and the one before it is
            // of pages written over since. Only a file that ends
            // before the slot has none there.)
            match backend.read_at(at, &mut raw) {
                Ok(()) => {}
                Err(e) if e.kind() == io::ErrorKind::UnexpectedEof => continue,
                Err(e) => return Err(e),
            }
            if let Some(root) = Root::decode(&raw)
                && Root::slot(root.seq) == at
                && best.is_none_or(|b| root.seq > b.seq)
            {
                best = Some(root);
            }
        }
        let root = best.ok_or_else(|| corrupt("no root record is valid"))?;
        let end = backend.len()?.div_ceil(UNIT as u64);
        Ok(PageFile::with(backend, root, false, end))
    }

    /// Opens the file of `backend`, or makes it if there is none: nothing
    /// at all, or only the start of one whose making was cut short before
    /// its first root record was durable (no page can have been written).
    pub fn open_or_create(backend: B) -> io::Result<PageFile<B>> {
        let len = backend.len()?;
        if len == 0 {
            return PageFile::create(backend);
        }
        // Checked before `open` takes the backend: a file with pages and
        // no valid root record is damage, not a beginning.
        let mut valid = false;
        for at in SLOTS {
            let mut raw = [0u8; UNIT];
            valid |=
                backend.read_at(at, &mut raw).is_ok() && Root::decode(&raw).is_some_and(|r| Root::slot(r.seq) == at);
        }
        if valid || len > HEADER_UNITS * UNIT as u64 {
            return PageFile::open(backend);
        }
        let root = Root::new(0, &[]);
        backend.write_at(0, &vec![0u8; HEADER_UNITS as usize * UNIT])?;
        backend.write_at(Root::slot(0), &root.encode())?;
        backend.sync()?;
        Ok(PageFile::with(backend, root, true, HEADER_UNITS))
    }

    fn with(backend: B, root: Root, sealed: bool, end: u64) -> PageFile<B> {
        let state = State {
            root,
            map: FreeMap::new(HEADER_UNITS),
            sealed,
            append: end.max(HEADER_UNITS),
            pending: VecDeque::new(),
            pins: BTreeMap::new(),
            poisoned: false,
        };
        PageFile {
            backend,
            state: Mutex::new(state),
            writer: Mutex::new(()),
            stop: std::sync::atomic::AtomicBool::new(false),
        }
    }

    fn state(&self) -> MutexGuard<'_, State> {
        self.state.lock().unwrap_or_else(|e| e.into_inner())
    }

    pub fn backend(&self) -> &B {
        &self.backend
    }

    /// The last committed root record.
    pub fn root(&self) -> Root {
        self.state().root
    }

    /// Units of the file in use, and one past the last of them.
    pub fn space(&self) -> (u64, u64) {
        let s = self.state();
        (s.map.used(), s.map.end())
    }

    /// Marks a page the root reaches, while the map is being rebuilt. An
    /// error if it runs into the header or a page already marked: the
    /// file's pages contradict each other.
    pub fn mark(&self, e: Extent) -> io::Result<()> {
        if self.stop.load(std::sync::atomic::Ordering::Relaxed) {
            return Err(io::ErrorKind::Interrupted.into());
        }
        let mut s = self.state();
        assert!(!s.sealed, "the map is sealed");
        if e.units == 0 || e.units > MAX_UNITS || !s.map.mark(e.start, e.units as u64) {
            return Err(corrupt("two pages claim the same space"));
        }
        Ok(())
    }

    /// Declares every page the root at opening reaches marked: the rest
    /// of the file is free, and what transactions have freed since is
    /// given back. (A file just made is sealed already.)
    pub fn seal(&self) {
        let mut s = self.state();
        s.sealed = true;
        s.release();
    }

    /// Whether the map of free space is whole.
    pub fn is_sealed(&self) -> bool {
        self.state().sealed
    }

    /// Makes any marking under way fail, with
    /// [`io::ErrorKind::Interrupted`]: for closing a file whose map is
    /// still being rebuilt.
    pub fn stop_marking(&self) {
        self.stop.store(true, std::sync::atomic::Ordering::Relaxed);
    }

    /// Refuses further transactions: what marks the pages found the file
    /// damaged.
    pub fn poison(&self) {
        self.state().poisoned = true;
    }

    /// Takes `units` units for a new page: from the map once it is
    /// whole, and until then past the end.
    fn alloc(&self, units: u32) -> u64 {
        let mut s = self.state();
        if s.sealed {
            return s.map.alloc(units);
        }
        let start = s.append;
        s.append += units as u64;
        let fresh = s.map.mark(start, units as u64);
        debug_assert!(fresh, "nothing is past the end");
        start
    }

    /// Reads the page at `e` into `buf` (at least [`Extent::bytes`] long)
    /// and returns its payload, or an error if what is there is not the
    /// page that was written.
    pub fn read<'a>(&self, e: Extent, buf: &'a mut [u8]) -> io::Result<&'a [u8]> {
        let buf = buf.get_mut(..e.bytes()).ok_or_else(|| corrupt("a page's buffer is shorter than the page"))?;
        self.backend.read_at(e.offset(), buf)?;
        e.payload(buf)
    }

    /// Reads many pages at once, each into its buffer (at least
    /// [`Extent::bytes`] long). Each is then checked and opened with
    /// [`Extent::payload`].
    pub fn read_many(&self, pages: &mut [(Extent, &mut [u8])]) -> io::Result<()> {
        let mut reads = Vec::with_capacity(pages.len());
        for (e, buf) in pages.iter_mut() {
            let bytes = e.bytes();
            let buf = buf.get_mut(..bytes).ok_or_else(|| corrupt("a page's buffer is shorter than the page"))?;
            reads.push(ReadReq { offset: e.offset(), buf });
        }
        self.backend.read_many(&mut reads)
    }

    /// Holds the present root: its pages stay readable until the pin is
    /// dropped.
    pub fn pin(&self) -> Pin<'_, B> {
        let mut s = self.state();
        let root = s.root;
        *s.pins.entry(root.seq).or_insert(0) += 1;
        Pin { file: self, root }
    }

    /// Begins a transaction, waiting for the one before it to end. It
    /// need not wait for the map of free space. An error if a commit has
    /// failed, or the file was found damaged, and it must be reopened.
    pub fn begin(&self) -> io::Result<Txn<'_, B>> {
        let guard = self.writer.lock().unwrap_or_else(|e| e.into_inner());
        let s = self.state();
        if s.poisoned {
            return Err(io::Error::other("the file must be reopened"));
        }
        drop(s);
        Ok(Txn { file: self, _guard: guard, inner: Mutex::new(Pending::default()), committed: false })
    }
}

/// A root record held, and with it every page it reaches.
pub struct Pin<'a, B: Backend> {
    file: &'a PageFile<B>,
    root: Root,
}

impl<B: Backend> Pin<'_, B> {
    pub fn root(&self) -> &Root {
        &self.root
    }

    /// As [`PageFile::read`], of a page this pin's root reaches.
    pub fn read<'b>(&self, e: Extent, buf: &'b mut [u8]) -> io::Result<&'b [u8]> {
        self.file.read(e, buf)
    }
}

impl<B: Backend> Drop for Pin<'_, B> {
    fn drop(&mut self) {
        let mut s = self.file.state();
        let count = s.pins.get_mut(&self.root.seq).expect("a pin is counted");
        *count -= 1;
        if *count == 0 {
            s.pins.remove(&self.root.seq);
            s.release();
        }
    }
}

/// A transaction: the one writer, until it commits or is dropped.
///
/// Its pages may be written from several threads at once (a pass over
/// the state splits among them): what it holds is behind a lock, taken
/// for the moment it takes to place a page.
pub struct Txn<'a, B: Backend> {
    file: &'a PageFile<B>,
    _guard: MutexGuard<'a, ()>,
    inner: Mutex<Pending>,
    committed: bool,
}

/// Pages encoded and not yet in the file, with where each lies.
#[derive(Default)]
struct Batch {
    /// The pages, end to end.
    buffer: Vec<u8>,
    /// Where each of them goes, in the order they lie in the buffer.
    queued: Vec<Extent>,
    /// Their place in the buffer, by first unit.
    index: HashMap<u64, usize>,
}

impl Batch {
    fn page(&self, e: Extent) -> Option<&[u8]> {
        self.index.get(&e.start).map(|at| &self.buffer[*at..*at + e.bytes()])
    }
}

/// What a transaction holds until it commits.
#[derive(Default)]
struct Pending {
    /// The pages being gathered.
    open: Batch,
    /// Batches on their way to the file, each written by the thread that
    /// filled it, with the lock let go: their pages are still read here
    /// until they are there.
    leaving: Vec<std::sync::Arc<Batch>>,
    /// Every page this transaction has taken.
    allocated: Vec<Extent>,
    /// Every page it replaces.
    freed: Vec<Extent>,
    written: u64,
}

impl<B: Backend> Txn<'_, B> {
    fn inner(&self) -> MutexGuard<'_, Pending> {
        self.inner.lock().unwrap_or_else(|e| e.into_inner())
    }

    /// Writes a new page of `payload` and returns where it is.
    pub fn write(&self, payload: &[u8]) -> io::Result<Extent> {
        let units = Extent::units_for(payload.len());
        assert!(units <= MAX_UNITS, "a page of {} bytes is too long", payload.len());
        let e = Extent { start: self.file.alloc(units), units };
        // Encoded with no lock held: the lock is for placing it.
        let mut page = [0u8; 4096];
        let mut long = Vec::new();
        let bytes: &mut [u8] = if e.bytes() <= page.len() {
            &mut page[..e.bytes()]
        } else {
            long.resize(e.bytes(), 0);
            &mut long
        };
        e.encode(payload, bytes);
        let full = {
            let mut p = self.inner();
            p.allocated.push(e);
            let at = p.open.buffer.len();
            p.open.buffer.extend_from_slice(bytes);
            p.open.index.insert(e.start, at);
            p.open.queued.push(e);
            if p.open.buffer.len() >= WRITE_BUFFER {
                let batch = std::sync::Arc::new(std::mem::take(&mut p.open));
                p.leaving.push(batch.clone());
                Some(batch)
            } else {
                None
            }
        };
        match full {
            Some(batch) => self.flush(&batch),
            None => Ok(()),
        }?;
        Ok(e)
    }

    /// Names a page of the state before this transaction that the state
    /// after it does not reach. It is not touched, and not reused until
    /// the commit is durable and no pin reaches it.
    pub fn free(&self, e: Extent) {
        debug_assert!(
            {
                let s = self.file.state();
                !s.sealed || s.map.is_used(e.start, e.units as u64)
            },
            "freed a page that is not in use"
        );
        self.inner().freed.push(e);
    }

    /// As [`PageFile::read`]; a page this transaction wrote is read back
    /// as written, whether or not it has reached the file.
    pub fn read<'b>(&self, e: Extent, buf: &'b mut [u8]) -> io::Result<&'b [u8]> {
        {
            let p = self.inner();
            let waiting = p.open.page(e).or_else(|| p.leaving.iter().find_map(|b| b.page(e)));
            if let Some(page) = waiting {
                let buf =
                    buf.get_mut(..e.bytes()).ok_or_else(|| corrupt("a page's buffer is shorter than the page"))?;
                buf.copy_from_slice(page);
                return e.payload(buf);
            }
        }
        self.file.read(e, buf)
    }

    /// Bytes of pages written so far, those still waiting among them.
    pub fn written(&self) -> u64 {
        let p = self.inner();
        p.written + (p.open.buffer.len() + p.leaving.iter().map(|b| b.buffer.len()).sum::<usize>()) as u64
    }

    /// Hands a batch's pages to the backend, with no lock held: pages
    /// that lie one after another in the file go as one write.
    fn flush(&self, batch: &std::sync::Arc<Batch>) -> io::Result<()> {
        // In the file's order, whatever order the threads took them in.
        let mut at = 0;
        let mut pages: Vec<(Extent, usize)> = batch
            .queued
            .iter()
            .map(|e| {
                at += e.bytes();
                (*e, at - e.bytes())
            })
            .collect();
        pages.sort_unstable_by_key(|p| p.0.start);
        let mut runs: Vec<Vec<u8>> = Vec::new();
        let mut writes: Vec<(u64, usize)> = Vec::new();
        let mut direct: Vec<WriteReq<'_>> = Vec::new();
        let mut i = 0;
        while i < pages.len() {
            // A run of pages one after another in the file.
            let mut j = i + 1;
            while j < pages.len() && pages[j].0.offset() == pages[j - 1].0.offset() + pages[j - 1].0.bytes() as u64 {
                j += 1;
            }
            let in_buffer = (i + 1..j).all(|k| pages[k].1 == pages[k - 1].1 + pages[k - 1].0.bytes());
            if in_buffer {
                let end = pages[j - 1].1 + pages[j - 1].0.bytes();
                direct.push(WriteReq { offset: pages[i].0.offset(), data: &batch.buffer[pages[i].1..end] });
            } else {
                // Neighbours in the file that are not neighbours in the
                // buffer are brought together.
                let mut run = Vec::new();
                for (e, at) in &pages[i..j] {
                    run.extend_from_slice(&batch.buffer[*at..*at + e.bytes()]);
                }
                writes.push((pages[i].0.offset(), runs.len()));
                runs.push(run);
            }
            i = j;
        }
        direct.extend(writes.iter().map(|(offset, k)| WriteReq { offset: *offset, data: &runs[*k] }));
        self.file.backend.write_many(&direct)?;
        let mut p = self.inner();
        p.written += batch.buffer.len() as u64;
        p.leaving.retain(|b| !std::sync::Arc::ptr_eq(b, batch));
        Ok(())
    }

    /// Commits: the pages are made durable, then the root record of
    /// `payload` is. Returns the record's sequence number.
    ///
    /// On an error before the record is written the transaction is
    /// dropped and the file is as it was. On an error while the record is
    /// written or made durable, whether it took is not known: the file
    /// refuses further transactions until it is reopened.
    pub fn commit(mut self, payload: &[u8]) -> io::Result<u64> {
        let last = {
            let mut p = self.inner();
            // (A batch that was not written, its error passed over by
            // whoever made it: what is committed would reach pages that
            // are not in the file.)
            if !p.leaving.is_empty() {
                return Err(io::Error::other("a batch of the transaction's pages was not written"));
            }
            let batch = std::sync::Arc::new(std::mem::take(&mut p.open));
            p.leaving.push(batch.clone());
            batch
        };
        self.flush(&last)?;
        self.file.backend.sync()?;
        let root = Root::new(self.file.root().seq + 1, payload);
        let recorded =
            self.file.backend.write_at(Root::slot(root.seq), &root.encode()).and_then(|()| self.file.backend.sync());
        let freed = std::mem::take(&mut self.inner().freed);
        let mut s = self.file.state();
        self.committed = true;
        if let Err(e) = recorded {
            s.poisoned = true;
            return Err(e);
        }
        s.root = root;
        s.pending.push_back((root.seq, freed));
        s.release();
        Ok(root.seq)
    }
}

impl<B: Backend> Drop for Txn<'_, B> {
    /// Without a commit, what was taken is given back: nothing reaches it.
    fn drop(&mut self) {
        if !self.committed {
            let allocated = std::mem::take(&mut self.inner().allocated);
            let mut s = self.file.state();
            for e in allocated {
                s.map.release(e.start, e.units as u64);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::store::backend::FileBackend;
    use crate::store::testing::{Lost, MemBackend, temp_dir};
    use crate::test_util::Rng;

    fn page_of(file: &PageFile<MemBackend>, e: Extent) -> io::Result<Vec<u8>> {
        let mut buf = vec![0u8; e.bytes()];
        file.read(e, &mut buf).map(|p| p.to_vec())
    }

    #[test]
    fn sizes() {
        assert_eq!(ROOT_MAX, 488);
        assert_eq!((Extent::units_for(0), Extent::units_for(504), Extent::units_for(505)), (1, 1, 2));
        assert_eq!((Extent::capacity(1), Extent::capacity(8)), (504, 4088));
        assert_eq!(Extent::units_for(Extent::capacity(MAX_UNITS)), MAX_UNITS);
    }

    #[test]
    fn a_new_file_is_empty_and_commits_are_read_back() {
        let file = PageFile::create(MemBackend::new()).unwrap();
        assert_eq!((file.root().seq, file.root().payload().len()), (0, 0));
        assert_eq!(file.space(), (HEADER_UNITS, HEADER_UNITS));
        // Only an empty backend can be made a file of.
        assert_eq!(
            PageFile::create(MemBackend::from_image(vec![0; 9])).err().map(|e| e.kind()),
            Some(io::ErrorKind::AlreadyExists)
        );

        let txn = file.begin().unwrap();
        let a = txn.write(b"alpha").unwrap();
        let b = txn.write(&[7u8; 3000]).unwrap();
        let empty = txn.write(&[]).unwrap();
        assert_eq!((a.units, b.units, empty.units), (1, 6, 1));
        // Its own pages are read back before they reach the file.
        let mut buf = [0u8; 4096];
        assert_eq!(txn.read(a, &mut buf).unwrap(), b"alpha");
        assert_eq!(txn.read(b, &mut buf).unwrap(), &[7u8; 3000][..]);
        assert_eq!(txn.commit(b"root one").unwrap(), 1);
        assert_eq!(file.root().payload(), b"root one");
        assert_eq!(page_of(&file, a).unwrap(), b"alpha");
        assert_eq!(page_of(&file, empty).unwrap(), b"");
        assert_eq!(file.space(), (HEADER_UNITS + 8, HEADER_UNITS + 8));

        // Opened again: the same root, and the pages once marked.
        let again = PageFile::open(MemBackend::from_image(file.backend().image(Lost::All))).unwrap();
        assert_eq!((again.root().seq, again.root().payload()), (1, &b"root one"[..]));
        for e in [a, b, empty] {
            again.mark(e).unwrap();
        }
        assert!(again.mark(Extent { start: b.start + 5, units: 2 }).is_err(), "overlaps a page");
        assert!(again.mark(Extent { start: 3, units: 1 }).is_err(), "in the header");
        again.seal();
        assert_eq!(page_of(&again, b).unwrap(), vec![7u8; 3000]);
        let txn = again.begin().unwrap();
        assert_eq!(txn.write(b"next").unwrap().start, HEADER_UNITS + 8);
        assert_eq!(txn.commit(b"").unwrap(), 2);
    }

    /// A page is refused if it is not what was written at that place.
    #[test]
    fn damaged_and_misplaced_pages_are_refused() {
        let file = PageFile::create(MemBackend::new()).unwrap();
        let txn = file.begin().unwrap();
        let a = txn.write(&[1u8; 600]).unwrap();
        let b = txn.write(&[1u8; 600]).unwrap();
        txn.commit(b"").unwrap();
        let image = file.backend().image(Lost::None);
        let bad = |e: Extent, change: &dyn Fn(&mut Vec<u8>)| {
            let mut img = image.clone();
            change(&mut img);
            let f = PageFile::open(MemBackend::from_image(img)).unwrap();
            page_of(&f, e).err().map(|e| e.kind())
        };
        let at = a.start as usize * UNIT;
        assert_eq!(bad(a, &|_| {}), None);
        // Any bit of the page's bytes: checksum, length or payload.
        for bit in [0usize, 31, 32, 63, 64, 8 * 300 + 3, 8 * 607 + 7] {
            assert_eq!(
                bad(a, &|img| img[at + bit / 8] ^= 1 << (bit % 8)),
                Some(io::ErrorKind::InvalidData),
                "bit {bit}"
            );
        }
        // The padding after the payload is no part of the page.
        assert_eq!(bad(a, &|img| img[at + 700] ^= 1), None);
        // The same bytes at another place: b's page copied over a's.
        let (from, to) = (b.start as usize * UNIT, a.start as usize * UNIT);
        assert_eq!(bad(a, &|img| img.copy_within(from..from + a.bytes(), to)), Some(io::ErrorKind::InvalidData));
        // Read as longer or shorter than it is, or into too short a buffer.
        let f = PageFile::open(MemBackend::from_image(image.clone())).unwrap();
        assert!(page_of(&f, Extent { start: a.start, units: 1 }).is_err());
        assert!(f.read(a, &mut [0u8; 600]).is_err());
        assert!(page_of(&f, Extent { start: a.start + 1, units: 1 }).is_err());
        assert_eq!(page_of(&f, Extent { start: 1 << 40, units: 1 }).unwrap_err().kind(), io::ErrorKind::UnexpectedEof);
    }

    /// The root is the valid record with the higher sequence number: a
    /// torn or damaged newer one falls back to the one before.
    #[test]
    fn the_root_is_the_last_good_record() {
        let file = PageFile::create(MemBackend::new()).unwrap();
        for k in 1..=3u8 {
            assert_eq!(file.begin().unwrap().commit(&[k; 5]).unwrap(), k as u64);
        }
        let image = file.backend().image(Lost::None);
        let root_of = |img: Vec<u8>| {
            PageFile::open(MemBackend::from_image(img)).map(|f| (f.root().seq, f.root().payload().to_vec()))
        };
        assert_eq!(root_of(image.clone()).unwrap(), (3, vec![3; 5]));
        // Records 3 and 2 are in slots 1 and 0. Any byte of the newer
        // changed: the older is the root.
        for at in [0usize, 7, 8, 16, 20, 24, 300, 508, 511] {
            let mut img = image.clone();
            img[SLOTS[1] as usize + at] ^= 0x40;
            assert_eq!(root_of(img).unwrap(), (2, vec![2; 5]), "byte {at}");
        }
        // Both damaged: there is no state to open, and none is made in
        // its place while the file is long enough to have held pages.
        let mut img = image.clone();
        img[SLOTS[0] as usize + 9] ^= 1;
        img[SLOTS[1] as usize + 9] ^= 1;
        assert_eq!(root_of(img.clone()).unwrap_err().kind(), io::ErrorKind::InvalidData);
        img.resize(HEADER_UNITS as usize * UNIT + 1, 0);
        assert!(PageFile::open_or_create(MemBackend::from_image(img)).is_err());
        // An existing file is opened, not made again.
        let opened = PageFile::open_or_create(MemBackend::from_image(image.clone())).unwrap();
        assert_eq!(opened.root().seq, 3);
        // A record copied into the other slot is not that slot's.
        let mut img = image.clone();
        img.copy_within(SLOTS[1] as usize..SLOTS[1] as usize + UNIT, 0);
        assert_eq!(root_of(img).unwrap(), (3, vec![3; 5]));
        let mut img = image.clone();
        img.copy_within(0..UNIT, SLOTS[1] as usize);
        assert_eq!(root_of(img).unwrap(), (2, vec![2; 5]));
        // A payload as long as a record holds, and no longer.
        assert!(file.begin().unwrap().commit(&[9; ROOT_MAX]).is_ok());
        assert_eq!(root_of(file.backend().image(Lost::None)).unwrap(), (4, vec![9; ROOT_MAX]));
    }

    #[test]
    #[should_panic(expected = "at most 488 bytes")]
    fn a_root_payload_too_long_is_a_bug() {
        let file = PageFile::create(MemBackend::new()).unwrap();
        let _ = file.begin().unwrap().commit(&[0; ROOT_MAX + 1]);
    }

    /// A transaction dropped gives back what it took; one that commits
    /// keeps the pages it replaced until the commit, then gives them back.
    #[test]
    fn space_comes_back() {
        let file = PageFile::create(MemBackend::new()).unwrap();
        let txn = file.begin().unwrap();
        let old: Vec<Extent> = (0..10).map(|i| txn.write(&[i; 1000]).unwrap()).collect();
        txn.commit(b"one").unwrap();
        let used = file.space().0;
        assert_eq!(used, HEADER_UNITS + 20);

        // Dropped: as if it had not been.
        let txn = file.begin().unwrap();
        for i in 0..50 {
            txn.write(&[i; 2000]).unwrap();
        }
        txn.free(old[3]);
        assert!(file.space().0 > used);
        drop(txn);
        assert_eq!(file.space(), (used, used));
        assert_eq!(page_of(&file, old[3]).unwrap(), vec![3; 1000]);

        // Committed: the replaced pages are not written over before the
        // commit (the new ones lie elsewhere), and are free after it.
        let txn = file.begin().unwrap();
        for e in &old[..5] {
            txn.free(*e);
        }
        let new: Vec<Extent> = (0..5).map(|i| txn.write(&[100 + i; 1000]).unwrap()).collect();
        assert!(new.iter().all(|n| old.iter().all(|o| n.start >= o.start + 2 || o.start >= n.start + 2)));
        txn.commit(b"two").unwrap();
        assert_eq!(file.space().0, used);
        // The next transaction writes where they were.
        let txn = file.begin().unwrap();
        let reused = txn.write(&[0; 4000]).unwrap();
        assert_eq!(reused.start, old[0].start);
        txn.commit(b"three").unwrap();
    }

    /// A pin keeps reading the state it began with while transactions
    /// replace it; its pages are reused only once it is dropped.
    #[test]
    fn a_pin_keeps_its_pages() {
        let file = PageFile::create(MemBackend::new()).unwrap();
        let txn = file.begin().unwrap();
        let first: Vec<Extent> = (0..8).map(|i| txn.write(&[i; 900]).unwrap()).collect();
        txn.commit(b"first").unwrap();
        let pin = file.pin();
        let early = file.pin();
        assert_eq!(pin.root().payload(), b"first");
        // Ten transactions each replace everything.
        let mut live = first.clone();
        for round in 1..=10u8 {
            let txn = file.begin().unwrap();
            for e in live.drain(..) {
                txn.free(e);
            }
            live = (0..8).map(|i| txn.write(&[round * 10 + i; 900]).unwrap()).collect();
            txn.commit(&[round]).unwrap();
            if round == 4 {
                drop(file.pin());
            }
        }
        let mut buf = [0u8; 1024];
        for (i, e) in first.iter().enumerate() {
            assert_eq!(pin.read(*e, &mut buf).unwrap(), &[i as u8; 900][..], "the pinned state is whole");
        }
        // Everything since the pin is still held: eleven states' pages.
        assert_eq!(file.space().0, HEADER_UNITS + 11 * 16);
        drop(pin);
        assert_eq!(file.space().0, HEADER_UNITS + 11 * 16, "another pin of the same root holds them");
        drop(early);
        assert_eq!(file.space().0, HEADER_UNITS + 16);
        // A pin of the present state holds nothing back.
        let now = file.pin();
        let txn = file.begin().unwrap();
        txn.write(b"x").unwrap();
        txn.commit(b"").unwrap();
        assert_eq!(now.root().payload(), &[10u8][..]);
    }

    /// More pages than the write buffer holds: early ones are read back
    /// from the file, late ones from the buffer, all of them after.
    #[test]
    fn a_large_transaction_is_written_as_it_goes() {
        let file = PageFile::create(MemBackend::new()).unwrap();
        let mut rng = Rng::new(0xb16);
        let txn = file.begin().unwrap();
        let mut pages = Vec::new();
        for i in 0..1500u32 {
            let len = rng.next_u64() as usize % 4000;
            let data: Vec<u8> = (0..len).map(|k| (i as usize * 31 + k) as u8).collect();
            pages.push((txn.write(&data).unwrap(), data));
        }
        assert!(txn.written() > 2 << 20);
        // Pages taken one after another are written as one: the file's
        // making took two writes and a sync, and these a write a buffer.
        assert!(file.backend().ops() <= 3 + 4, "{} writes and syncs", file.backend().ops());
        let mut buf = [0u8; 4096];
        for (e, data) in &pages {
            assert_eq!(txn.read(*e, &mut buf).unwrap(), &data[..]);
        }
        txn.commit(b"big").unwrap();
        let mut reads: Vec<(Extent, Vec<u8>)> = pages.iter().map(|(e, _)| (*e, vec![0u8; e.bytes()])).collect();
        let mut batch: Vec<(Extent, &mut [u8])> = reads.iter_mut().map(|(e, b)| (*e, &mut b[..])).collect();
        file.read_many(&mut batch).unwrap();
        for ((e, raw), (_, data)) in reads.iter().zip(&pages) {
            assert_eq!(e.payload(raw).unwrap(), &data[..]);
        }
    }

    /// A commit whose root record could not be made durable leaves the
    /// file refusing transactions: what it holds is no longer known here.
    #[test]
    fn a_failed_commit_ends_the_files_use() {
        let file = PageFile::create(MemBackend::new()).unwrap();
        // The transaction's page, the sync of the pages, the root record.
        file.backend().crash_at(3);
        let txn = file.begin().unwrap();
        txn.write(b"page").unwrap();
        assert!(txn.commit(b"lost").is_err());
        assert!(file.begin().is_err());
        assert_eq!(file.root().seq, 0);
        // Failing before the root record is only a transaction dropped.
        let file = PageFile::create(MemBackend::new()).unwrap();
        file.backend().crash_at(2);
        let txn = file.begin().unwrap();
        txn.write(b"page").unwrap();
        assert!(txn.commit(b"lost").is_err());
        assert_eq!(file.space().0, HEADER_UNITS);
    }

    // -- A small state on the pages, to lose power under.

    /// The state: keys with versions, each key's value a page, and a page
    /// listing them; the root record says where the list is.
    #[derive(Clone, Debug, PartialEq, Eq, Default)]
    struct Toy {
        /// Key, version and the value's page, ascending by key.
        entries: Vec<(u32, u64, Extent)>,
        list: Option<Extent>,
    }

    /// A key's value at a version: its length and bytes follow from both.
    fn value(key: u32, version: u64) -> Vec<u8> {
        let mut rng = Rng::new(((key as u64) << 32 | version) ^ 0x7a1e);
        let len = rng.next_u64() as usize % 3000;
        let mut out = Vec::with_capacity(len + 8);
        while out.len() < len {
            out.extend_from_slice(&rng.next_u64().to_le_bytes());
        }
        out.truncate(len);
        out
    }

    fn extent_bytes(e: Extent) -> [u8; 12] {
        let mut out = [0u8; 12];
        out[..8].copy_from_slice(&e.start.to_le_bytes());
        out[8..].copy_from_slice(&e.units.to_le_bytes());
        out
    }

    fn extent_from(b: &[u8]) -> Extent {
        Extent {
            start: u64::from_le_bytes(b[..8].try_into().unwrap()),
            units: u32::from_le_bytes(b[8..12].try_into().unwrap()),
        }
    }

    impl Toy {
        /// What the keys and versions are: the state, less where it lies.
        fn contents(&self) -> Vec<(u32, u64)> {
            self.entries.iter().map(|(k, v, _)| (*k, *v)).collect()
        }

        /// Reads the state the root reaches, checking every value, and
        /// marking every page if `mark`.
        fn load<B: Backend>(file: &PageFile<B>, mark: bool) -> io::Result<Toy> {
            let root = file.root();
            if root.payload().is_empty() {
                return Ok(Toy::default());
            }
            let list = extent_from(root.payload());
            let mut buf = vec![0u8; MAX_UNITS as usize * UNIT];
            let mut toy = Toy { entries: Vec::new(), list: Some(list) };
            for rec in file.read(list, &mut buf)?.chunks_exact(24) {
                let key = u32::from_le_bytes(rec[..4].try_into().unwrap());
                let version = u64::from_le_bytes(rec[4..12].try_into().unwrap());
                toy.entries.push((key, version, extent_from(&rec[12..])));
            }
            if mark {
                file.mark(list)?;
            }
            for (key, version, e) in &toy.entries {
                if mark {
                    file.mark(*e)?;
                }
                if file.read(*e, &mut buf)? != &value(*key, *version)[..] {
                    return Err(corrupt("a value is not its key's"));
                }
            }
            Ok(toy)
        }

        /// One transaction: some keys set to `version`, perhaps one
        /// removed, the list written anew.
        fn step<B: Backend>(&mut self, file: &PageFile<B>, rng: &mut Rng, version: u64) -> io::Result<u64> {
            let mut next = self.clone();
            let txn = file.begin()?;
            for _ in 0..1 + rng.next_u64() % 6 {
                let key = (rng.next_u64() % 40) as u32;
                let e = txn.write(&value(key, version))?;
                match next.entries.binary_search_by_key(&key, |(k, _, _)| *k) {
                    Ok(i) => {
                        txn.free(next.entries[i].2);
                        next.entries[i] = (key, version, e);
                    }
                    Err(i) => next.entries.insert(i, (key, version, e)),
                }
            }
            if rng.next_u64().is_multiple_of(4) && !next.entries.is_empty() {
                let (_, _, e) = next.entries.remove(rng.next_u64() as usize % next.entries.len());
                txn.free(e);
            }
            let mut list = Vec::new();
            for (key, version, e) in &next.entries {
                list.extend_from_slice(&key.to_le_bytes());
                list.extend_from_slice(&version.to_le_bytes());
                list.extend_from_slice(&extent_bytes(*e));
            }
            if let Some(old) = next.list {
                txn.free(old);
            }
            let at = txn.write(&list)?;
            next.list = Some(at);
            let seq = txn.commit(&extent_bytes(at))?;
            *self = next;
            Ok(seq)
        }
    }

    /// Transactions of the workload: fewer in a debug build, where the
    /// test would otherwise take most of a minute.
    const STEPS: u64 = if cfg!(debug_assertions) { 10 } else { 60 };

    /// The states after each of the workload's commits, and how many
    /// writes and syncs the whole of it makes.
    fn workload() -> (Vec<Vec<(u32, u64)>>, u64) {
        let file = PageFile::create(MemBackend::new()).unwrap();
        let (mut toy, mut rng) = (Toy::default(), Rng::new(0xc7a5));
        let mut states = vec![toy.contents()];
        for v in 1..=STEPS {
            assert_eq!(toy.step(&file, &mut rng, v).unwrap(), v);
            states.push(toy.contents());
            assert_eq!(Toy::load(&file, false).unwrap(), toy);
        }
        // Space is reused: the file is not the sum of all that was written.
        let (used, end) = file.space();
        assert!(end < 2 * used, "{used} of {end} units in use");
        (states, file.backend().ops())
    }

    /// Power is lost at every write and every sync of the workload,
    /// and for each, the unsynced writes are lost, kept, or lost and kept
    /// sector by sector. What is opened afterwards is always the state of
    /// a commit, whole: the last one that returned, or the one that was
    /// being made durable. And it can be gone on with.
    #[test]
    fn a_crash_anywhere_leaves_a_committed_state() {
        let (states, ops) = workload();
        assert!(ops > 4 * STEPS, "{ops}");
        let mut outcomes = [0u32; 2];
        for crash_at in 1..=ops {
            let backend = MemBackend::new();
            backend.crash_at(crash_at);
            let mut committed = 0;
            let created = PageFile::create(backend);
            let file = match created {
                Ok(file) => {
                    let (mut toy, mut rng) = (Toy::default(), Rng::new(0xc7a5));
                    for v in 1..=STEPS {
                        match toy.step(&file, &mut rng, v) {
                            Ok(seq) => committed = seq,
                            Err(_) => break,
                        }
                    }
                    assert!(file.backend().crashed(), "crash {crash_at} of {ops}");
                    Some(file)
                }
                Err(_) => None,
            };
            // Power lost while the file was being made: whatever is left
            // is made into an empty file, never taken for a damaged one.
            let Some(file) = file else {
                assert!(crash_at <= 3);
                let backend = MemBackend::new();
                backend.crash_at(crash_at);
                assert!(PageFile::open_or_create(backend).is_err());
                for lost in [Lost::All, Lost::None, Lost::Some(crash_at)] {
                    let backend = MemBackend::new();
                    backend.crash_at(crash_at);
                    let _ = backend.write_at(0, &vec![0u8; HEADER_UNITS as usize * UNIT]);
                    let _ = backend.write_at(Root::slot(0), &Root::new(0, &[]).encode());
                    let _ = backend.sync();
                    let made = PageFile::open_or_create(MemBackend::from_image(backend.image(lost))).unwrap();
                    assert_eq!((made.root().seq, made.space().0), (0, HEADER_UNITS));
                    // Nothing to mark: no page is reached.
                    made.seal();
                    made.begin().unwrap().commit(b"begun").unwrap();
                }
                continue;
            };
            for lost in
                [Lost::All, Lost::None, Lost::Some(crash_at), Lost::Some(crash_at + 1000), Lost::Some(!crash_at)]
            {
                let what = format!("crash at {crash_at} of {ops}, {lost:?}");
                let reopened = PageFile::open(MemBackend::from_image(file.backend().image(lost))).expect(&what);
                let seq = reopened.root().seq;
                assert!(seq == committed || seq == committed + 1, "{what}: at {seq} after {committed} commits");
                outcomes[(seq - committed) as usize] += 1;
                let mut toy = Toy::load(&reopened, true).expect(&what);
                assert_eq!(toy.contents(), states[seq as usize], "{what}");
                reopened.seal();
                // Going on from there: three more transactions, the state
                // read back whole after each, and after another opening.
                let mut rng = Rng::new(crash_at);
                for v in 0..3 {
                    toy.step(&reopened, &mut rng, 1000 + v).expect(&what);
                    assert_eq!(Toy::load(&reopened, false).expect(&what), toy, "{what}");
                }
                let third = PageFile::open(MemBackend::from_image(reopened.backend().image(Lost::All))).unwrap();
                assert_eq!(Toy::load(&third, true).expect(&what), toy, "{what}");
            }
        }
        // Both happen: a commit under way is sometimes lost, sometimes kept.
        assert!(outcomes[0] > 50 && outcomes[1] > 10, "{outcomes:?}");
        assert_eq!(states.len() as u64, STEPS + 1);
    }

    /// Transactions before the map is sealed: their pages lie past the
    /// end of the file as it was opened, one dropped gives its pages
    /// back, and once the pages of the root at opening are marked and
    /// the map sealed, it is the map a fresh opening builds.
    #[test]
    fn transactions_do_not_wait_for_the_map() {
        let first = PageFile::create(MemBackend::new()).unwrap();
        let (mut toy, mut rng) = (Toy::default(), Rng::new(0xea71));
        for v in 1..=12 {
            toy.step(&first, &mut rng, v).unwrap();
        }
        let image = first.backend().image(Lost::All);
        let end = image.len() as u64 / UNIT as u64;

        let file = PageFile::open(MemBackend::from_image(image)).unwrap();
        let opened = Toy::load(&file, false).unwrap();
        assert!(!file.is_sealed());
        for v in 13..=20 {
            toy.step(&file, &mut rng, v).unwrap();
            assert!(toy.list.unwrap().start >= end, "a new page past the end");
            assert!(toy.entries.iter().all(|e| e.1 < 13 || e.2.start >= end));
        }
        // One dropped: nothing of it stays.
        let used = file.space().0;
        let txn = file.begin().unwrap();
        txn.write(&[1; 3000]).unwrap();
        drop(txn);
        assert_eq!(file.space().0, used);
        assert_eq!(Toy::load(&file, false).unwrap(), toy);

        // The pages of the state as it was opened, marked; then sealed.
        file.mark(opened.list.unwrap()).unwrap();
        opened.entries.iter().for_each(|e| file.mark(e.2).unwrap());
        file.seal();
        let fresh = PageFile::open(MemBackend::from_image(file.backend().image(Lost::All))).unwrap();
        assert_eq!(Toy::load(&fresh, true).unwrap(), toy);
        fresh.seal();
        assert_eq!(file.space().0, fresh.space().0);
        // Sealed, the space freed meanwhile is used: the file's end stays.
        let end = file.space().1;
        for v in 21..=40 {
            toy.step(&file, &mut rng, v).unwrap();
        }
        assert!(file.space().1 <= end + 16, "{end} units at the sealing, {} after", file.space().1);
        assert_eq!(Toy::load(&file, false).unwrap(), toy);
    }

    /// The same on a real file: transactions, a second opening refused
    /// while the first holds the directory, and the state there again
    /// after closing.
    #[test]
    fn on_a_real_file() {
        use crate::store::backend::DirLock;
        let dir = temp_dir("pagefile");
        let lock = DirLock::acquire(&dir).unwrap();
        let path = dir.join("state");
        let file = PageFile::create(FileBackend::open(&path).unwrap()).unwrap();
        let (mut toy, mut rng) = (Toy::default(), Rng::new(0xf11e));
        for v in 1..=25 {
            toy.step(&file, &mut rng, v).unwrap();
        }
        assert!(DirLock::acquire(&dir).is_err());
        drop(file);
        let file = PageFile::open(FileBackend::open(&path).unwrap()).unwrap();
        assert_eq!(file.root().seq, 25);
        assert_eq!(Toy::load(&file, true).unwrap(), toy);
        file.seal();
        toy.step(&file, &mut rng, 26).unwrap();
        assert_eq!(Toy::load(&file, false).unwrap(), toy);
        assert_eq!(std::fs::metadata(&path).unwrap().len(), file.space().1 * UNIT as u64);
        drop((file, lock));
        std::fs::remove_dir_all(dir).unwrap();
    }
}
