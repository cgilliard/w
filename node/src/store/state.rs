//! The state: the unspent outputs, the names, the window of blocks that
//! can be undone, and the block they are the state after, under one root
//! record.
//!
//! A block is applied in one transaction: its spends and its outputs go
//! into the set, its names into theirs, its record into the window, and the root record that
//! commits both names the block as the tip. Either all of it is on disk
//! or none is. Undoing the tip is the same in reverse.
//!
//! The state's root is the hash the block's header commits to: the
//! outputs' tree and the names' tree under one node.
//!
//! ```text
//! root record := version (1) | height (4) | tip (32) | outputs (68) | names (60)
//!                | window (6) | sweep (8)
//! ```
//!
//! With every block the sweep of the outputs goes a little further round
//! ([`super::outputs`]): past sixteen records for each output the block
//! spent, so that records of spent outputs are dropped faster than they
//! are made, once the blocks that spent them have left the window.
//!
//! A [`Snapshot`] is the state after some block, held while later blocks
//! are applied: whoever reads through it sees that state, whole.
//!
//! # The state as of an earlier block
//!
//! A node that joins takes the state from the nodes there are, and takes
//! long enough that the chain moves on meanwhile: so what it asks for is
//! the state as of one block, and any block of the window will do
//! ([`State::past`]). No block is marked for it beforehand and nothing
//! is stored for it but what the window keeps to undo blocks with:
//!
//! - An output made after that block has a position past the block's
//!   last, so the outputs unspent as of the block are those unspent now
//!   below that position, and those spent since, whose records the set
//!   still holds.
//! - The outputs are handed over in parts, the subtrees of
//!   [`PART_LEVEL`]. The roots of the parts as of the block are their
//!   roots now, with those any block since changed put back as its
//!   record has them. They hash to the outputs' root as of the block, so
//!   each part that arrives is checked alone, against its root.
//! - The names go the same way, in parts by the first bits of their
//!   keys: the names of a part as of the block are those it has now,
//!   less those registered since, with the records replaced since as
//!   they were.

use std::collections::VecDeque;
use std::io;
use std::sync::{Arc, Mutex};
use std::thread::JoinHandle;

use super::backend::Backend;
use super::blocks::Blocks;
use super::commits::{Commit, Commits};
use super::names::{NameProof, Names, PART_LEVEL as NAME_PART_LEVEL};
use super::outputs::{Outputs, PART_LEVEL, Record};
use super::pagefile::{PageFile, Pin, Root, Txn};
pub use super::sparse::{STATE_HEIGHT, empty_state, root_of_state_path};
use super::trie::Part;
use super::window::{BlockRecord, Window};
use crate::error::Error;
use crate::hash::Digest;
use crate::hash::{digest_from_bytes, digest_to_bytes};
use crate::name::{Key, Record as NameRecord};
use crate::registry::state_root as compress;

/// How many states as of earlier blocks are kept made ([`State::past`]).
pub const PASTS_KEPT: usize = 4;

/// How a root record of this making begins. (1 was of blocks and
/// their records kept as chains of pages, each naming the next
/// ([`super::blob`]); 2 of a state being received, with blocks kept
/// so; 3 of blocks kept as they are and their records as chains.)
const VERSION: u8 = 4;
/// What records of makings before this one began with.
const OLDER: [u8; 3] = [1, 2, 3];
/// What a root record begins with while its state is still being
/// received from other nodes ([`super::receive`]): not a state to open.
pub(super) const RECEIVING: u8 = 5;
const RECORD: usize = COMMITS_AT + Commits::BYTES;
const COMMITS_AT: usize = BLOCKS_AT + Blocks::BYTES;
const NAMES_AT: usize = 37 + Outputs::BYTES;
const WINDOW_AT: usize = NAMES_AT + Names::BYTES;
const BLOCKS_AT: usize = WINDOW_AT + Window::BYTES + 8;
const _: () = assert!(RECORD <= super::pagefile::ROOT_MAX);
/// Records the sweep goes past with a block, at least.
const SWEEP_MIN: usize = 2048;
/// And for each output the block spends.
const SWEEP_RATE: usize = 16;
/// The window's length unless another is asked for: a week of blocks.
pub const DEFAULT_WINDOW: usize = 7 * 144;

fn corrupt(what: &'static str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, what)
}

/// Marks every page the state reaches as it was opened, and seals the
/// map. If the pages contradict each other the file takes no more
/// transactions.
fn mark_all<B: Backend>(file: &PageFile<B>, opened: &Meta) -> Result<(), io::ErrorKind> {
    let marked = opened
        .outputs
        .mark(file)
        .and_then(|()| opened.names.mark(file))
        .and_then(|()| opened.window.mark(file))
        .and_then(|()| opened.blocks.mark(file))
        .and_then(|()| opened.commits.mark(file));
    match marked {
        Ok(()) => {
            file.seal();
            Ok(())
        }
        Err(e) => {
            // Stopped because the state is being closed is not damage.
            if e.kind() != io::ErrorKind::Interrupted {
                file.poison();
            }
            Err(e.kind())
        }
    }
}

/// Closing a state stops the rebuilding of its map, and waits for the
/// thread to be gone: nothing touches the file after.
impl<B: Backend + 'static> Drop for State<B> {
    fn drop(&mut self) {
        self.file.stop_marking();
        let _ = self.wait_ready();
    }
}

/// What a root record says the state is.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct Meta {
    /// The height of the block the state is the state after; 0 with
    /// `tip` zero before any block.
    pub(super) height: u32,
    pub(super) tip: Digest,
    pub(super) outputs: Outputs,
    pub(super) names: Names,
    pub(super) window: Window,
    /// The position the sweep of the outputs has reached.
    pub(super) sweep: u64,
    /// The blocks known of.
    pub(super) blocks: Blocks,
    /// Which outputs are commits of names.
    pub(super) commits: Commits,
}

impl Meta {
    fn empty() -> Meta {
        Meta {
            height: 0,
            tip: crate::hash::EMPTY,
            outputs: Outputs::EMPTY,
            names: Names::EMPTY,
            window: Window::default(),
            sweep: 0,
            blocks: Blocks::EMPTY,
            commits: Commits::EMPTY,
        }
    }

    pub(super) fn to_bytes(&self) -> [u8; RECORD] {
        let mut out = Vec::with_capacity(RECORD);
        out.push(VERSION);
        out.extend_from_slice(&self.height.to_le_bytes());
        out.extend_from_slice(&digest_to_bytes(&self.tip));
        out.extend_from_slice(&self.outputs.to_bytes());
        out.extend_from_slice(&self.names.to_bytes());
        out.extend_from_slice(&self.window.to_bytes());
        out.extend_from_slice(&self.sweep.to_le_bytes());
        out.extend_from_slice(&self.blocks.to_bytes());
        out.extend_from_slice(&self.commits.to_bytes());
        out.try_into().unwrap()
    }

    /// Everything a root record says, the window's list read from its
    /// page.
    fn read(pages: &impl super::pagefile::ReadPages, root: &Root) -> io::Result<Meta> {
        if root.payload().is_empty() && root.seq == 0 {
            return Ok(Meta::empty());
        }
        let (height, tip, outputs, names) = Meta::head(root)?;
        let rest = &root.payload()[WINDOW_AT..];
        let window = Window::read(pages, &rest[..Window::BYTES])?;
        let sweep = u64::from_le_bytes(rest[Window::BYTES..Window::BYTES + 8].try_into().unwrap());
        let (blocks, commits) = Meta::blocks(root)?;
        Ok(Meta { height, tip, outputs, names, window, sweep, blocks, commits })
    }

    /// The blocks and the commits of a root record.
    fn blocks(root: &Root) -> io::Result<(Blocks, Commits)> {
        match root.payload() {
            b if b.len() == RECORD => {
                Ok((Blocks::from_bytes(&b[BLOCKS_AT..COMMITS_AT])?, Commits::from_bytes(&b[COMMITS_AT..])?))
            }
            _ => Ok((Blocks::EMPTY, Commits::EMPTY)),
        }
    }

    /// The tip, the outputs and the names of a root record: what a
    /// reader needs.
    fn head(root: &Root) -> io::Result<(u32, Digest, Outputs, Names)> {
        let b = root.payload();
        if b.is_empty() && root.seq == 0 {
            return Ok((0, crate::hash::EMPTY, Outputs::EMPTY, Names::EMPTY));
        }
        if b.first() == Some(&RECEIVING) {
            return Err(corrupt("the state is still being received"));
        }
        if b.first().is_some_and(|v| OLDER.contains(v)) {
            return Err(corrupt(
                "the state was kept by an earlier version, and is not read by this one: with its directory gone, it is taken again",
            ));
        }
        if b.len() != RECORD || b[0] != VERSION {
            return Err(corrupt("the state's root record is not one"));
        }
        let height = u32::from_le_bytes(b[1..5].try_into().unwrap());
        let tip = digest_from_bytes(&b[5..37]).ok_or_else(|| corrupt("the state's tip is not a digest"))?;
        let names = Names::from_bytes(&b[NAMES_AT..NAMES_AT + Names::BYTES])?;
        Ok((height, tip, Outputs::from_bytes(&b[37..NAMES_AT])?, names))
    }
}

/// The state's root: the outputs' tree and the names' under one node.
fn state_root(outputs: &Outputs, names: &Names) -> Digest {
    compress(&outputs.hash(), &names.hash())
}

/// A block, as the state takes it.
pub struct BlockEdit<'a> {
    pub height: u32,
    /// The block's id.
    pub block: Digest,
    /// The positions of the outputs it spends, ascending.
    pub spends: &'a [u64],
    /// The outputs it makes, in order.
    pub outputs: &'a [Record],
    /// The names it registers (`false`) and the records it puts in place
    /// of those registered (`true`), ascending by key.
    pub names: &'a [(Key, NameRecord, bool)],
    /// The hashes of the commits of names it makes: they are the last
    /// of `outputs`, in this order, each an output of no amount whose
    /// commitment is the commit's hash, made at this height.
    pub commits: &'a [Digest],
    /// Those of `spends` that its reveals and sweeps spend: commits.
    pub commits_spent: &'a [u64],
    /// The state root its header commits to. If given and the state after
    /// the block is another, the block is refused.
    pub state_root: Option<Digest>,
}

/// The state, in a file of pages.
pub struct State<B: Backend + 'static> {
    file: Arc<PageFile<B>>,
    meta: Mutex<Meta>,
    /// Held by whoever changes the state or the blocks, from before
    /// what it starts from is read until what it made is what the next
    /// starts from: the file orders those who write it only until one
    /// is durable, and another that began then from what was there
    /// before would undo it.
    writing: Mutex<()>,
    /// Blocks whose records the window keeps.
    keep: usize,
    /// The level of the outputs' parts.
    part_level: u32,
    /// The level of the names' parts.
    name_level: u32,
    /// The thread that rebuilds the file's map of free space, until it
    /// has been waited for.
    marking: Mutex<Option<JoinHandle<Result<(), io::ErrorKind>>>>,
    /// The states as of earlier blocks that were last asked for
    /// ([`State::past`]), [`PASTS_KEPT`] of them, and the block the
    /// state was at when each was made: each is the same for as long as
    /// the state is, and making one reads the root of every part there
    /// is. (More than one: two nodes that take the state as of two
    /// blocks ask for their parts turn about.)
    past: Mutex<VecDeque<(Digest, Arc<PastThen>)>>,
    /// Tests: how long each step of the last block applied took (the
    /// outputs, the names and the window, the sweep, the commit).
    #[cfg(test)]
    times: Mutex<[std::time::Duration; 4]>,
}

impl<B: Backend + 'static> State<B> {
    /// Opens the state in `backend`, making an empty one if there is
    /// none, with a window of `keep` blocks.
    ///
    /// It is ready at once: blocks can be applied and the state read. To
    /// know what of the file is free every node of the tries and every
    /// page of the window is read, which for a large state takes
    /// seconds, and that is done on a thread of its own; until it is
    /// done, new pages go at the end of the file
    /// ([`super::pagefile`]). [`State::wait_ready`] waits for it.
    pub fn open(backend: B, keep: usize) -> io::Result<State<B>> {
        let state = State::open_idle(backend, keep)?;
        state.start()?;
        Ok(state)
    }

    /// [`State::open`], of a file opened already and found to hold a
    /// state ([`super::receive::open`]).
    pub(super) fn open_file(file: PageFile<B>, keep: usize) -> io::Result<State<B>> {
        let meta = Meta::read(&file, &file.root())?;
        let state = State::with(Arc::new(file), meta, keep);
        state.start()?;
        Ok(state)
    }

    /// Starts the thread that rebuilds the map, if it is not whole.
    fn start(&self) -> io::Result<()> {
        if !self.file.is_sealed() {
            let (file, meta) = (self.file.clone(), self.meta().clone());
            let thread = std::thread::Builder::new().name("state-map".into());
            *self.marking.lock().unwrap() = Some(thread.spawn(move || mark_all(&file, &meta))?);
        }
        Ok(())
    }

    /// The state of a file whose root record is `meta`'s: one just
    /// received whole.
    pub(super) fn of(file: Arc<PageFile<B>>, meta: Meta, keep: usize) -> io::Result<State<B>> {
        let state = State::with(file, meta, keep);
        state.start()?;
        Ok(state)
    }

    /// Tests: parts at other levels, so that small states have many.
    #[cfg(test)]
    pub(super) fn set_levels(&mut self, outputs: u32, names: u32) {
        (self.part_level, self.name_level) = (outputs, names);
    }

    fn with(file: Arc<PageFile<B>>, meta: Meta, keep: usize) -> State<B> {
        State {
            file,
            meta: Mutex::new(meta),
            writing: Mutex::new(()),
            keep,
            part_level: PART_LEVEL,
            name_level: NAME_PART_LEVEL,
            marking: Mutex::new(None),
            past: Mutex::new(VecDeque::new()),
            #[cfg(test)]
            times: Mutex::new([std::time::Duration::ZERO; 4]),
        }
    }

    /// As [`State::open`], with no thread started: the map is rebuilt
    /// when [`State::mark_now`] is called.
    fn open_idle(backend: B, keep: usize) -> io::Result<State<B>> {
        let file = PageFile::open_or_create(backend)?;
        let meta = Meta::read(&file, &file.root())?;
        Ok(State::with(Arc::new(file), meta, keep))
    }

    /// Rebuilds the map on the calling thread, from the state as it is:
    /// for a state opened idle that nothing has been applied to.
    #[cfg(test)]
    fn mark_now(&self, opened: &Meta) -> io::Result<()> {
        mark_all(&self.file, opened).map_err(io::Error::from)
    }

    /// Waits until the map of free space is whole. An error if the file
    /// was found damaged on the way: it then takes no more blocks.
    pub fn wait_ready(&self) -> io::Result<()> {
        let thread = self.marking.lock().unwrap_or_else(|e| e.into_inner()).take();
        match thread.map(|t| t.join()) {
            None | Some(Ok(Ok(()))) => Ok(()),
            Some(Ok(Err(kind))) => Err(kind.into()),
            Some(Err(_)) => Err(io::Error::other("the thread rebuilding the map panicked")),
        }
    }

    fn meta(&self) -> std::sync::MutexGuard<'_, Meta> {
        self.meta.lock().unwrap_or_else(|e| e.into_inner())
    }

    pub fn file(&self) -> &PageFile<B> {
        &self.file
    }

    /// The height and id of the block the state is the state after.
    pub fn tip(&self) -> (u32, Digest) {
        let m = self.meta();
        (m.height, m.tip)
    }

    /// The state's root.
    pub fn root(&self) -> Digest {
        let m = self.meta();
        state_root(&m.outputs, &m.names)
    }

    /// The height of the oldest block that can be undone, if any can.
    pub fn oldest_undo(&self) -> Option<u32> {
        self.meta().window.oldest()
    }

    /// The state as it is now, held: see [`Snapshot`].
    pub fn snapshot(&self) -> io::Result<Snapshot<'_, B>> {
        let pin = self.file.pin();
        let (height, tip, outputs, names) = Meta::head(pin.root())?;
        let (blocks, commits) = Meta::blocks(pin.root())?;
        Ok(Snapshot { pin, height, tip, outputs, names, blocks, commits })
    }

    /// The state as of the block at `height`, to hand to another node:
    /// any block from the one before the oldest that can be undone to
    /// the tip. [`Error::NoUndoRecord`] for one older.
    ///
    /// Making it reads the record of every block since, so it is to be
    /// made once and asked for many parts.
    pub fn past(&self, height: u32) -> Result<Past<'_, B>, Error> {
        // The state now, and everything read from the root record that
        // is held: a block applied meanwhile changes neither.
        let pin = self.file.pin();
        let meta = Meta::read(&pin, pin.root())?;
        // The one made last, if it is of this block and the state is
        // what it was made of: a node that hands a state over is asked
        // for the same one thousands of times. (The state, not the
        // file: headers go on arriving, each a root of the file's, and
        // none of them changes what a block's state was.)
        let mut kept = self.past.lock().unwrap_or_else(|e| e.into_inner());
        // (Those made of a state that is no more are of no use again.)
        kept.retain(|(tip, then)| {
            *tip == meta.tip
                && then.outputs.to_bytes() == meta.outputs.to_bytes()
                && then.names.to_bytes() == meta.names.to_bytes()
                && then.commits.to_bytes() == meta.commits.to_bytes()
        });
        if let Some(at) = kept.iter().position(|(_, then)| then.height == height) {
            kept.swap(0, at);
            return Ok(Past { pin, then: Arc::clone(&kept[0].1) });
        }
        drop(kept);
        let oldest = meta.window.oldest().unwrap_or(meta.height + 1);
        if height > meta.height || height + 1 < oldest {
            return Err(Error::NoUndoRecord);
        }
        let level = self.part_level;
        let mut parts: std::collections::BTreeMap<u64, Digest> = meta.outputs.parts(&pin, level)?.into_iter().collect();
        let (mut block, mut next, mut names_root) = (meta.tip, meta.outputs.next, meta.names.hash());
        let name_level = self.name_level;
        let mut name_parts: std::collections::BTreeMap<u32, Part> =
            meta.names.parts(&pin, name_level)?.into_iter().collect();
        // The names changed since: each as it was, or that it was not.
        let mut names_then: std::collections::BTreeMap<Key, Option<NameRecord>> = std::collections::BTreeMap::new();
        // The commits spent since: commits then.
        let mut commits_then: std::collections::BTreeMap<u64, Commit> = std::collections::BTreeMap::new();
        // How many outputs each part has had spent since, then which.
        let mut spent: std::collections::BTreeMap<u64, Vec<u32>> = std::collections::BTreeMap::new();
        for h in (height + 1..=meta.height).rev() {
            let record = meta.window.get(&pin, h)?.ok_or_else(|| corrupt("a block of the window has no record"))?;
            for (index, before) in &record.parts_before {
                match before {
                    Some(root) => parts.insert(*index, *root),
                    None => parts.remove(index),
                };
            }
            for (index, before) in &record.names_parts_before {
                match before {
                    Some(part) => name_parts.insert(*index, *part),
                    None => name_parts.remove(index),
                };
            }
            // Blocks are met newest first, so the oldest has the last word.
            for key in &record.registered {
                names_then.insert(*key, None);
            }
            for old in &record.replaced {
                names_then.insert(old.key(), Some(*old));
            }
            commits_then.extend(record.commits_spent.iter().copied());
            for p in &record.spends {
                spent.entry(p >> level).or_default().push((p & ((1 << level) - 1)) as u32);
            }
            (block, next, names_root) = (record.before, record.first_new, record.names_before);
        }
        // What was spent since but made since too was never in that state.
        for (index, offsets) in &mut spent {
            offsets.retain(|o| (index << level | *o as u64) < next);
            offsets.sort_unstable();
        }
        let then = Arc::new(PastThen {
            outputs: meta.outputs,
            level,
            height,
            block,
            next,
            names_root,
            parts: parts.into_iter().collect(),
            spent,
            names: meta.names,
            name_level,
            name_parts: name_parts.into_iter().collect(),
            names_then,
            commits: meta.commits,
            commits_then,
        });
        let mut kept = self.past.lock().unwrap_or_else(|e| e.into_inner());
        kept.push_front((meta.tip, Arc::clone(&then)));
        kept.truncate(PASTS_KEPT);
        drop(kept);
        Ok(Past { pin, then })
    }

    /// Changes the blocks known of ([`Blocks`]) and nothing of the
    /// state: a header that arrived, a body, a file. Durable when this
    /// returns; if `change` fails nothing is changed.
    pub fn write_blocks<T>(
        &self,
        change: impl FnOnce(&Txn<'_, B>, &mut Blocks) -> Result<T, Error>,
    ) -> Result<T, Error> {
        let _writing = self.writing.lock().unwrap_or_else(|e| e.into_inner());
        let txn = self.file.begin()?;
        let mut meta = self.meta().clone();
        let done = change(&txn, &mut meta.blocks)?;
        txn.commit(&meta.to_bytes())?;
        *self.meta() = meta;
        Ok(done)
    }

    /// The state taken apart, to receive another in its file: the file
    /// and what its root record says, the map of free space whole.
    pub(super) fn dissolve(self) -> io::Result<(Arc<PageFile<B>>, Meta)> {
        self.wait_ready()?;
        let parts = (self.file.clone(), self.meta().clone());
        drop(self);
        Ok(parts)
    }

    /// Applies the next block, and returns the state's root after it.
    /// Refused, with the state as it was: a block that spends what is not
    /// there ([`Error::NoSuchOutput`]), registers a name that is taken
    /// ([`Error::NameTaken`]), replaces the record of one that is not
    /// registered ([`Error::NoSuchName`]), or whose header commits to
    /// another state ([`Error::StateRoot`]).
    pub fn apply(&self, block: &BlockEdit<'_>) -> Result<Digest, Error> {
        self.apply_with(block, |_, _| Ok(()))
    }

    /// [`State::apply`], and in the same step whatever `also` does to
    /// the blocks known of ([`Blocks`]): the block's body kept, its
    /// place in the chain. If `also` fails the block is not applied.
    pub fn apply_with(
        &self,
        block: &BlockEdit<'_>,
        also: impl FnOnce(&Txn<'_, B>, &mut Blocks) -> Result<(), Error>,
    ) -> Result<Digest, Error> {
        self.session(|session| {
            let (root, _) = session.apply(block)?;
            let (txn, blocks) = session.blocks();
            also(txn, blocks)?;
            Ok(root)
        })
    }

    /// Undoes the tip: the state is again the one after the block before
    /// it, whose height and id are returned. [`Error::NoUndoRecord`] if
    /// the tip's record is no longer kept.
    pub fn undo(&self) -> Result<(u32, Digest), Error> {
        self.undo_with(|_, _| Ok(()))
    }

    /// [`State::undo`], and in the same step whatever `also` does to
    /// the blocks known of.
    pub fn undo_with(
        &self,
        also: impl FnOnce(&Txn<'_, B>, &mut Blocks) -> Result<(), Error>,
    ) -> Result<(u32, Digest), Error> {
        self.session(|session| {
            let tip = session.undo()?;
            let (txn, blocks) = session.blocks();
            also(txn, blocks)?;
            Ok(tip)
        })
    }

    /// Work on the state that is then given up: `work` is handed a
    /// transaction with the outputs, the names and the commits as they
    /// are, changes them as it will and reads back what it changed, and
    /// none of it is kept. It is how the changes of a block are seen
    /// one at a time by whoever proves it. No block is applied while it
    /// runs.
    pub fn scratch<T>(
        &self,
        work: impl FnOnce(&mut Txn<'_, B>, Outputs, Names, &Commits) -> Result<T, Error>,
    ) -> Result<T, Error> {
        let _writing = self.writing.lock().unwrap_or_else(|e| e.into_inner());
        let mut txn = self.file.begin()?;
        let meta = self.meta().clone();
        work(&mut txn, meta.outputs, meta.names, &meta.commits)
    }

    /// Several changes as one step: blocks undone and blocks applied,
    /// and what goes with them, all in place when `change` returns well
    /// and this does, or none of it. It is how a chain goes over to
    /// another branch: a branch that turns out to have a block that is
    /// not valid leaves the state where it was.
    ///
    /// What the session has done is read back through it; nothing else
    /// sees any of it until it is all done.
    pub fn session<T>(&self, change: impl FnOnce(&mut Session<'_, B>) -> Result<T, Error>) -> Result<T, Error> {
        let _writing = self.writing.lock().unwrap_or_else(|e| e.into_inner());
        let txn = self.file.begin()?;
        let meta = self.meta().clone();
        let mut session = Session {
            state: self,
            txn,
            meta,
            #[cfg(test)]
            clock: std::time::Instant::now(),
            #[cfg(test)]
            times: [std::time::Duration::ZERO; 4],
        };
        let done = change(&mut session)?;
        #[cfg(test)]
        let (clock, mut times) = (session.clock, session.times);
        let Session { txn, meta, .. } = session;
        txn.commit(&meta.to_bytes())?;
        #[cfg(test)]
        {
            times[3] = clock.elapsed();
            *self.times.lock().unwrap() = times;
        }
        *self.meta() = meta;
        Ok(done)
    }
}

/// Changes to the state being made as one step ([`State::session`]).
pub struct Session<'a, B: Backend + 'static> {
    state: &'a State<B>,
    txn: Txn<'a, B>,
    meta: Meta,
    /// Tests: when the last block's application began, and how long its
    /// steps took.
    #[cfg(test)]
    clock: std::time::Instant,
    #[cfg(test)]
    times: [std::time::Duration; 4],
}

impl<'a, B: Backend + 'static> Session<'a, B> {
    /// The block the state is the state after, as the session has it.
    pub fn tip(&self) -> (u32, Digest) {
        (self.meta.height, self.meta.tip)
    }

    /// The state's root, as the session has it.
    pub fn root(&self) -> Digest {
        state_root(&self.meta.outputs, &self.meta.names)
    }

    /// The position the next output takes.
    pub fn next(&self) -> u64 {
        self.meta.outputs.next
    }

    /// The outputs' root and the names', as the session has them: the
    /// two the state's root is over.
    pub fn roots(&self) -> (Digest, Digest) {
        (self.meta.outputs.hash(), self.meta.names.hash())
    }

    /// The output at `position` and whether it is unspent.
    pub fn output(&self, position: u64) -> io::Result<Option<(Record, bool)>> {
        self.meta.outputs.get(&self.txn, position)
    }

    /// The record registered at `key`, if any.
    pub fn name(&self, key: Key) -> io::Result<Option<NameRecord>> {
        self.meta.names.get(&self.txn, key)
    }

    /// The blocks known of, to read through the transaction and to
    /// change with it.
    pub fn blocks(&mut self) -> (&Txn<'a, B>, &mut Blocks) {
        (&self.txn, &mut self.meta.blocks)
    }

    /// Applies the next block: returns the state's root after it, and
    /// the amounts of the outputs it spent, added up. As
    /// [`State::apply`]; after an error the session is to be given up.
    pub fn apply(&mut self, block: &BlockEdit<'_>) -> Result<(Digest, u128), Error> {
        let (state, txn, meta) = (self.state, &mut self.txn, &mut self.meta);
        assert_eq!(block.height, meta.height + 1, "blocks are applied in order");
        let first_new = meta.outputs.next;
        #[cfg(test)]
        {
            self.clock = std::time::Instant::now();
        }
        let names_before = meta.names.hash();
        let (outputs, parts_before, spent) =
            meta.outputs.apply_keeping(txn, block.height, block.spends, block.outputs, state.part_level)?;
        meta.outputs = outputs;
        #[cfg(test)]
        {
            self.times[0] = self.clock.elapsed();
        }
        // The records the block replaces, as they are, to undo it with.
        let mut replaced = Vec::new();
        for (key, _, _) in block.names.iter().filter(|n| n.2) {
            replaced.push(meta.names.get(&*txn, *key)?.ok_or(Error::NoSuchName)?);
        }
        let (names, names_parts_before) = meta.names.apply_keeping(txn, block.names, state.name_level)?;
        meta.names = names;
        let root = state_root(&meta.outputs, &meta.names);
        if block.state_root.is_some_and(|want| want != root) {
            return Err(Error::StateRoot);
        }
        // The table of commits: those spent leave it, those made enter.
        // One spent that it has not is no fault: the table is an index.
        let mut commits_spent = Vec::new();
        for position in block.commits_spent {
            debug_assert!(block.spends.binary_search(position).is_ok(), "a commit spent is among the spends");
            if let Some(commit) = meta.commits.remove(&*txn, *position)? {
                commits_spent.push((*position, commit));
            }
        }
        let made = block.outputs.len().checked_sub(block.commits.len()).expect("the commits are among the outputs");
        for (i, hash) in block.commits.iter().enumerate() {
            let output = &block.outputs[made + i];
            assert!(output.commitment == *hash && output.height == block.height, "a commit's output is its leaf");
            meta.commits.add(&*txn, first_new + (made + i) as u64, Commit { hash: *hash, height: block.height })?;
        }
        let record = BlockRecord {
            height: block.height,
            block: block.block,
            before: meta.tip,
            first_new,
            spends: block.spends.to_vec(),
            registered: block.names.iter().filter(|n| !n.2).map(|n| n.0).collect(),
            replaced,
            names_before,
            names_parts_before,
            parts_before,
            commits_spent,
        };
        meta.window.push(txn, &record, state.keep)?;
        // What was spent before the oldest block of the window is dead
        // for good.
        let horizon = (block.height + 1).saturating_sub(state.keep as u32);
        let budget = SWEEP_MIN.max(SWEEP_RATE * block.spends.len());
        #[cfg(test)]
        {
            self.times[1] = self.clock.elapsed();
        }
        (meta.outputs, meta.sweep) = meta.outputs.sweep(txn, meta.sweep, budget, horizon)?;
        (meta.height, meta.tip) = (block.height, block.block);
        #[cfg(test)]
        {
            self.times[2] = self.clock.elapsed();
        }
        Ok((root, spent))
    }

    /// Undoes the tip, as [`State::undo`].
    pub fn undo(&mut self) -> Result<(u32, Digest), Error> {
        let (txn, meta) = (&mut self.txn, &mut self.meta);
        let record = meta.window.pop(txn)?.ok_or(Error::NoUndoRecord)?;
        if record.height != meta.height || record.block != meta.tip {
            return Err(corrupt("the newest record is not the tip's").into());
        }
        meta.outputs = meta.outputs.undo(txn, record.height - 1, &record.spends, record.first_new)?;
        let restore: Vec<(Key, NameRecord, bool)> = record.replaced.iter().map(|r| (r.key(), *r, true)).collect();
        meta.names = meta.names.undo(txn, &restore, &record.registered)?;
        meta.commits.remove_between(&*txn, record.first_new, u64::MAX)?;
        for (position, commit) in &record.commits_spent {
            meta.commits.add(&*txn, *position, *commit)?;
        }
        (meta.height, meta.tip) = (record.height - 1, record.before);
        Ok((meta.height, meta.tip))
    }
}

/// The state as of an earlier block ([`State::past`]), to be handed to
/// another node in parts. While it is held the pages it reads are not
/// reused.
pub struct Past<'a, B: Backend + 'static> {
    pin: Pin<'a, B>,
    then: Arc<PastThen>,
}

impl<B: Backend + 'static> std::ops::Deref for Past<'_, B> {
    type Target = PastThen;

    fn deref(&self) -> &PastThen {
        &self.then
    }
}

/// What a [`Past`] is made of besides the pages it reads: how the state
/// then differs from the state now. Kept from one asking to the next
/// ([`State::past`]).
pub struct PastThen {
    /// The outputs as they are now.
    outputs: Outputs,
    level: u32,
    height: u32,
    block: Digest,
    next: u64,
    names_root: Digest,
    parts: Vec<(u64, Digest)>,
    /// The outputs spent since, by part: each its place within the part.
    spent: std::collections::BTreeMap<u64, Vec<u32>>,
    /// The names as they are now.
    names: Names,
    name_level: u32,
    name_parts: Vec<(u32, Part)>,
    /// The names changed since: each as it was, or that it was not.
    names_then: std::collections::BTreeMap<Key, Option<NameRecord>>,
    /// The table of commits as it is now, and those spent since.
    commits: Commits,
    commits_then: std::collections::BTreeMap<u64, Commit>,
}

impl<B: Backend + 'static> Past<'_, B> {
    /// The block it is the state after: its height and id.
    pub fn tip(&self) -> (u32, Digest) {
        (self.height, self.block)
    }

    /// The position the next output would have taken.
    pub fn next(&self) -> u64 {
        self.next
    }

    /// The level of the outputs' parts.
    pub fn level(&self) -> u32 {
        self.level
    }

    /// The root of each part of the outputs, ascending by index.
    pub fn parts(&self) -> &[(u64, Digest)] {
        &self.parts
    }

    /// Which of the outputs of the part of index `index` are commits of
    /// names, as this node's table has them: position and hash,
    /// ascending. They go with the part, and are checked against its
    /// outputs by whoever takes them ([`super::receive`]).
    pub fn commits(&self, index: u64) -> io::Result<Vec<(u64, Digest)>> {
        let (from, to) = (index << self.level, ((index + 1) << self.level).min(self.next));
        let mut all: std::collections::BTreeMap<u64, Digest> =
            self.commits.between(&self.pin, from, to)?.into_iter().map(|(p, c)| (p, c.hash)).collect();
        all.extend(self.commits_then.range(from..to.max(from)).map(|(p, c)| (*p, c.hash)));
        Ok(all.into_iter().collect())
    }

    /// The root of the names' tree.
    pub fn names_root(&self) -> Digest {
        self.names_root
    }

    /// The level of the names' parts.
    pub fn name_level(&self) -> u32 {
        self.name_level
    }

    /// Each part of the names, ascending by index. They hash to the
    /// names' root ([`super::names::parts_root`]).
    pub fn name_parts(&self) -> &[(u32, Part)] {
        &self.name_parts
    }

    /// The names of the part of index `index`, ascending by key: those
    /// it has now, less those registered since, the records replaced
    /// since as they were.
    pub fn names_part(&self, index: u32) -> io::Result<Vec<NameRecord>> {
        // (An index is whatever a peer asks for: one past the last part
        // there can be is of no names. And the last part's keys end
        // where keys do, which is not a key to say "below" of.)
        if (index as Key) >> (Key::BITS - self.name_level) != 0 {
            return Ok(Vec::new());
        }
        let from = (index as Key) << self.name_level;
        let to = from | (((1 as Key) << self.name_level) - 1);
        let mut then = self.names_then.range(from..=to).peekable();
        let mut out = Vec::new();
        for now in self.names.part(&self.pin, self.name_level, index)? {
            match then.next_if(|t| *t.0 == now.key()) {
                Some((_, was)) => out.extend(*was),
                None => out.push(now),
            }
        }
        // Every name changed since is one there is now: none is removed.
        match then.next() {
            None => Ok(out),
            Some(_) => Err(corrupt("a name the window changed is not in the names")),
        }
    }

    /// The state's root: the one the block's header commits to.
    pub fn root(&self) -> Digest {
        compress(&super::outputs::parts_root(self.level, &self.parts), &self.names_root)
    }

    /// The unspent outputs of the part of index `index`, ascending by
    /// position: those unspent now, and those spent since, less those
    /// made since.
    pub fn part(&self, index: u64) -> io::Result<Vec<(u64, Record)>> {
        // (An index is whatever a peer asks for: no output is in a part
        // past where the outputs ended.)
        if index >= self.next.div_ceil(1 << self.level) {
            return Ok(Vec::new());
        }
        let since = self.spent.get(&index).map_or(&[][..], |s| &s[..]);
        let offset = |p: u64| (p & ((1 << self.level) - 1)) as u32;
        Ok(self
            .outputs
            .part(&self.pin, self.level, index)?
            .into_iter()
            .filter(|(p, _, live)| *p < self.next && (*live || since.binary_search(&offset(*p)).is_ok()))
            .map(|(p, record, _)| (p, record))
            .collect())
    }

    /// The output that was unspent at `position` as of this block, and
    /// its path up to the state's root then: the sibling at each of
    /// the [`STATE_HEIGHT`] levels. None if no output was unspent
    /// there. (The outputs of its part as they were, which give its
    /// path within the part; then the roots of the parts as they
    /// were; then the names' root.)
    pub fn prove(&self, position: u64) -> io::Result<Option<(Record, [Digest; STATE_HEIGHT])>> {
        use super::sparse::{EMPTY, root_with_path};
        let (level, index) = (self.level as usize, position >> self.level);
        let part = self.part(index)?;
        let Some(record) = part.iter().find(|(p, _)| *p == position).map(|(_, record)| *record) else {
            return Ok(None);
        };
        let mut path = [EMPTY; STATE_HEIGHT];
        let mut leaves: Vec<(u64, Digest)> = part.iter().map(|(p, record)| (*p, record.leaf())).collect();
        let (within, above) = path.split_at_mut(level);
        root_with_path(0, level, &mut leaves, Some((position, within)));
        let top = super::outputs::HEIGHT as usize;
        root_with_path(level, top, &mut self.parts.clone(), Some((index, &mut above[..top - level])));
        path[STATE_HEIGHT - 1] = self.names_root;
        Ok(Some((record, path)))
    }
}

/// The state after one block, held: reads through it see that state
/// however many blocks are applied or undone meanwhile. While it is held
/// the pages of that state are not reused, so it should not be held long.
pub struct Snapshot<'a, B: Backend + 'static> {
    pin: Pin<'a, B>,
    height: u32,
    tip: Digest,
    outputs: Outputs,
    names: Names,
    blocks: Blocks,
    commits: Commits,
}

impl<'a, B: Backend + 'static> Snapshot<'a, B> {
    /// The blocks known of when the snapshot was taken, and what reads
    /// them: `snapshot.blocks().entry(snapshot.pages(), &id)`.
    pub fn blocks(&self) -> &Blocks {
        &self.blocks
    }

    /// Which outputs are commits of names: read as the blocks are.
    pub fn commits(&self) -> &Commits {
        &self.commits
    }

    /// The pages of the snapshot's state.
    pub fn pages(&self) -> &Pin<'a, B> {
        &self.pin
    }
}

impl<B: Backend + 'static> Snapshot<'_, B> {
    pub fn tip(&self) -> (u32, Digest) {
        (self.height, self.tip)
    }

    pub fn root(&self) -> Digest {
        state_root(&self.outputs, &self.names)
    }

    /// The names: their count, and their tree's root.
    pub fn names(&self) -> &Names {
        &self.names
    }

    /// The record registered at `key`, if any.
    pub fn name(&self, key: Key) -> io::Result<Option<NameRecord>> {
        self.names.get(&self.pin, key)
    }

    /// The path of the name of `key` in the names' tree, whose root is
    /// the right half of the state's: the outputs' root is its sibling.
    pub fn prove_name(&self, key: Key) -> io::Result<(NameProof, Digest)> {
        Ok((self.names.prove(&self.pin, key)?, self.outputs.hash()))
    }

    /// The outputs: their count, the next position, and their tree's root.
    pub fn outputs(&self) -> &Outputs {
        &self.outputs
    }

    /// The output at `position` and whether it is unspent.
    pub fn output(&self, position: u64) -> io::Result<Option<(Record, bool)>> {
        self.outputs.get(&self.pin, position)
    }

    /// Whether `position` holds an unspent output.
    pub fn is_unspent(&self, position: u64) -> io::Result<bool> {
        Ok(self.output(position)?.is_some_and(|(_, live)| live))
    }

    /// The path of `position` up to the state's root: its leaf, and the
    /// sibling at each of the [`STATE_HEIGHT`] levels.
    pub fn prove(&self, position: u64) -> io::Result<(Digest, [Digest; STATE_HEIGHT])> {
        let (leaf, below) = self.outputs.prove(&self.pin, position)?;
        let mut path = [self.names.hash(); STATE_HEIGHT];
        path[..STATE_HEIGHT - 1].copy_from_slice(&below);
        Ok((leaf, path))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::store::sparse::EMPTY;
    use crate::store::testing::{Lost, MemBackend, temp_dir};
    use crate::test_util::Rng;

    fn record(rng: &mut Rng, height: u32) -> Record {
        Record {
            commitment: rng.digest(),
            memo: rng.digest()[..20].try_into().unwrap(),
            amount: rng.next_u64(),
            height,
        }
    }

    fn id(height: u32, fork: u32) -> Digest {
        core::array::from_fn(|i| (height * 1000 + fork * 10 + i as u32) as u8 ^ (height >> 4) as u8)
    }

    /// A chain of blocks made as they are applied: what each spent and
    /// made, and the root after it.
    struct Chain {
        rng: Rng,
        /// Unspent positions.
        live: Vec<u64>,
        next: u64,
        /// Per block: its id, spends, outputs, and the root after it.
        blocks: Vec<(Digest, Vec<u64>, Vec<Record>, Digest)>,
    }

    impl Chain {
        fn new(seed: u64) -> Chain {
            Chain { rng: Rng::new(seed), live: Vec::new(), next: 0, blocks: Vec::new() }
        }

        /// Makes the next block and applies it to `state`.
        fn extend<B: Backend + 'static>(
            &mut self,
            state: &State<B>,
            spends: usize,
            adds: usize,
            fork: u32,
        ) -> Result<Digest, Error> {
            let height = self.blocks.len() as u32 + 1;
            let mut picked: Vec<u64> = (0..spends.min(self.live.len()))
                .map(|_| {
                    let i = self.rng.next_u64() as usize % self.live.len();
                    self.live.swap_remove(i)
                })
                .collect();
            picked.sort_unstable();
            let outputs: Vec<Record> = (0..adds).map(|_| record(&mut self.rng, height)).collect();
            let block = BlockEdit {
                height,
                block: id(height, fork),
                spends: &picked,
                outputs: &outputs,
                names: &[],
                commits: &[],
                commits_spent: &[],
                state_root: None,
            };
            let root = state.apply(&block)?;
            self.live.extend(self.next..self.next + adds as u64);
            self.next += adds as u64;
            self.blocks.push((id(height, fork), picked, outputs, root));
            Ok(root)
        }

        /// Forgets the last block, as the state does when it undoes it.
        fn forget(&mut self) {
            let (_, spends, outputs, _) = self.blocks.pop().unwrap();
            self.next -= outputs.len() as u64;
            self.live.retain(|p| *p < self.next);
            self.live.extend(spends);
        }

        fn tip(&self) -> (u32, Digest) {
            (self.blocks.len() as u32, self.blocks.last().map_or(crate::hash::EMPTY, |b| b.0))
        }
    }

    #[test]
    fn an_empty_state() {
        let state = State::open(MemBackend::new(), 10).unwrap();
        assert_eq!(state.tip(), (0, crate::hash::EMPTY));
        assert_eq!(state.root(), empty_state());
        assert_eq!(state.oldest_undo(), None);
        assert_eq!(state.undo().err(), Some(Error::NoUndoRecord));
        let snap = state.snapshot().unwrap();
        assert_eq!((snap.tip().0, snap.root()), (0, empty_state()));
        assert_eq!(snap.output(0).unwrap(), None);
        let (leaf, path) = snap.prove(5).unwrap();
        assert_eq!(root_of_state_path(5, &leaf, &path), empty_state());
        // Opened again before any block, it is still empty.
        let again = State::open(MemBackend::from_image(state.file().backend().image(Lost::All)), 10).unwrap();
        assert_eq!(again.root(), empty_state());
    }

    /// Blocks applied, the tip undone and another chain taken from there,
    /// the state opened again between: tips, roots and paths all agree
    /// with the chain, and undoing returns to the root there was.
    #[test]
    fn blocks_are_applied_and_undone() {
        let mut chain = Chain::new(0x57a7e);
        let mut state = State::open(MemBackend::new(), 8).unwrap();
        for (spends, adds) in [(0, 300), (40, 100), (100, 20), (0, 0), (150, 500), (300, 300), (20, 0)] {
            let root = chain.extend(&state, spends, adds, 0).unwrap();
            assert_eq!((state.root(), state.tip()), (root, chain.tip()));
        }
        assert_eq!(state.oldest_undo(), Some(1));
        // A path of an unspent output, of a spent one, and of none.
        let snap = state.snapshot().unwrap();
        let spent = chain.blocks[1].1[0];
        for (position, unspent) in [(chain.live[0], true), (spent, false), (chain.next, false)] {
            let (leaf, path) = snap.prove(position).unwrap();
            assert_eq!(root_of_state_path(position, &leaf, &path), state.root(), "position {position}");
            assert_eq!(leaf != EMPTY, unspent);
            assert_eq!(snap.is_unspent(position).unwrap(), unspent);
        }
        drop(snap);

        // A reorganisation three blocks deep.
        let roots: Vec<Digest> = chain.blocks.iter().map(|b| b.3).collect();
        for back in 1..=3 {
            let tip = state.undo().unwrap();
            chain.forget();
            assert_eq!(tip, chain.tip());
            assert_eq!(state.root(), roots[roots.len() - 1 - back]);
        }
        // Opened again in the middle of it.
        state = State::open(MemBackend::from_image(state.file().backend().image(Lost::All)), 8).unwrap();
        assert_eq!((state.tip(), state.root()), (chain.tip(), roots[3]));
        for (spends, adds) in [(10, 10), (200, 50), (0, 400), (90, 90)] {
            let root = chain.extend(&state, spends, adds, 1).unwrap();
            assert_eq!(state.root(), root);
        }
        assert_eq!(state.tip(), (8, id(8, 1)));
        // The other chain's blocks at those heights gave other roots.
        assert_ne!(chain.blocks[4].3, roots[4]);

        // Everything undone, back to nothing: all eight are in the window.
        while state.tip().0 > 0 {
            state.undo().unwrap();
            chain.forget();
            assert_eq!(state.tip(), chain.tip());
        }
        assert_eq!(state.root(), empty_state());
        state.wait_ready().unwrap();
        assert_eq!(state.file().space().0, crate::store::pagefile::HEADER_UNITS);
    }

    /// A block is refused whole: one that spends what is not there, and
    /// one whose header commits to another state.
    #[test]
    fn a_refused_block_changes_nothing() {
        let mut chain = Chain::new(0xbad5);
        let state = State::open(MemBackend::new(), 4).unwrap();
        chain.extend(&state, 0, 200, 0).unwrap();
        chain.extend(&state, 50, 50, 0).unwrap();
        let (root, tip, used) = (state.root(), state.tip(), state.file().space().0);
        let spent = chain.blocks[1].1[3];
        let outputs = [record(&mut chain.rng, 3)];
        let block = |spends: &'static [u64], state_root| BlockEdit {
            height: 3,
            block: id(3, 0),
            spends,
            outputs: &outputs,
            names: &[],
            commits: &[],
            commits_spent: &[],
            state_root,
        };
        let gone: &'static [u64] = Box::leak(vec![spent].into_boxed_slice());
        assert_eq!(state.apply(&block(gone, None)).err(), Some(Error::NoSuchOutput(spent)));
        assert_eq!(state.apply(&block(&[], Some(root))).err(), Some(Error::StateRoot));
        assert_eq!((state.root(), state.tip(), state.file().space().0), (root, tip, used));
        // With the root the block really leaves, it is taken.
        let after = state.apply(&block(&[], None)).unwrap();
        state.undo().unwrap();
        assert_eq!(state.apply(&block(&[], Some(after))).unwrap(), after);
    }

    /// Only the window's blocks can be undone, and the records of older
    /// ones are gone from the file.
    #[test]
    fn the_window_bounds_what_can_be_undone() {
        let mut chain = Chain::new(0x1d0);
        let state = State::open(MemBackend::new(), 3).unwrap();
        for _ in 0..10 {
            chain.extend(&state, 30, 60, 0).unwrap();
        }
        assert_eq!(state.oldest_undo(), Some(8));
        for height in (7..10).rev() {
            assert_eq!(state.undo().unwrap().0, height);
        }
        assert_eq!(state.undo().err(), Some(Error::NoUndoRecord));
        assert_eq!(state.tip().0, 7);
        // A window of no blocks: nothing can be undone.
        let none = State::open(MemBackend::new(), 0).unwrap();
        let mut chain = Chain::new(1);
        chain.extend(&none, 0, 5, 0).unwrap();
        assert_eq!(none.undo().err(), Some(Error::NoUndoRecord));
    }

    /// A snapshot goes on reading the state it was taken of.
    #[test]
    fn a_snapshot_is_the_state_it_was_taken_of() {
        let mut chain = Chain::new(0x54a9);
        let state = State::open(MemBackend::new(), 4).unwrap();
        chain.extend(&state, 0, 400, 0).unwrap();
        chain.extend(&state, 100, 100, 0).unwrap();
        let snap = state.snapshot().unwrap();
        let (root, live) = (state.root(), chain.live.clone());
        for _ in 0..6 {
            chain.extend(&state, 80, 120, 0).unwrap();
        }
        state.undo().unwrap();
        assert_ne!(state.root(), root);
        assert_eq!((snap.root(), snap.tip()), (root, (2, id(2, 0))));
        assert_eq!(snap.outputs().count as usize, live.len());
        for p in live.iter().step_by(7) {
            assert!(snap.is_unspent(*p).unwrap(), "position {p}");
            let (leaf, path) = snap.prove(*p).unwrap();
            assert_eq!(root_of_state_path(*p, &leaf, &path), root);
        }
    }

    /// Power lost at every write and sync of a chain with a
    /// reorganisation in it: what is opened afterwards is the state after
    /// one of its steps, and goes on from there.
    #[test]
    fn a_crash_leaves_the_state_after_a_block() {
        // Each step applies a block or undoes the tip.
        let steps: &[Option<(usize, usize)>] = &[
            Some((0, 120)),
            Some((30, 40)),
            Some((50, 0)),
            None,
            None,
            Some((20, 60)),
            Some((40, 40)),
            None,
            Some((5, 90)),
        ];
        let run = |crash_at: Option<u64>| {
            let backend = MemBackend::new();
            if let Some(n) = crash_at {
                backend.crash_at(n);
            }
            let mut chain = Chain::new(0xc4a5);
            // The tip and root after each step that completed.
            let mut done = Vec::new();
            let state = match State::open(backend, 4) {
                Ok(state) => state,
                Err(_) => return (None, done),
            };
            done.push((state.tip(), state.root()));
            for (fork, step) in steps.iter().enumerate() {
                let ok = match step {
                    Some((spends, adds)) => chain.extend(&state, *spends, *adds, fork as u32).is_ok(),
                    None => {
                        let undone = state.undo().is_ok();
                        if undone {
                            chain.forget();
                        }
                        undone
                    }
                };
                if !ok {
                    break;
                }
                done.push((state.tip(), state.root()));
            }
            (Some(state), done)
        };
        let (whole, all) = run(None);
        let ops = whole.unwrap().file().backend().ops();
        assert_eq!(all.len(), steps.len() + 1);
        for crash_at in 1..=ops {
            let (state, done) = run(Some(crash_at));
            let Some(state) = state else { continue };
            for lost in [Lost::All, Lost::None, Lost::Some(crash_at)] {
                let again = State::open(MemBackend::from_image(state.file().backend().image(lost)), 4).unwrap();
                let at = (again.tip(), again.root());
                // The last step that returned, or the one under way.
                assert!(
                    at == all[done.len() - 1] || all.get(done.len()) == Some(&at),
                    "crash at {crash_at} of {ops}, {lost:?}: {:?} after {} steps",
                    at.0,
                    done.len() - 1
                );
                // It goes on: a block, and that block undone.
                let height = again.tip().0 + 1;
                let outputs = [record(&mut Rng::new(crash_at), height)];
                let block = BlockEdit {
                    height,
                    block: id(height, 99),
                    spends: &[],
                    outputs: &outputs,
                    names: &[],
                    commits: &[],
                    commits_spent: &[],
                    state_root: None,
                };
                again.apply(&block).unwrap();
                assert_eq!(again.undo().unwrap(), at.0);
                assert_eq!(again.root(), at.1);
            }
        }
    }

    /// Over a long chain whose blocks spend as much as they make, the
    /// file stays the size of what is unspent and what the window keeps:
    /// the sweep drops the rest as it goes. And at any point the whole
    /// window can still be undone.
    #[test]
    fn the_file_does_not_grow_with_the_chain() {
        let mut chain = Chain::new(0x9a0);
        let keep = 5;
        let state = State::open(MemBackend::new(), keep).unwrap();
        chain.extend(&state, 0, 3000, 0).unwrap();
        let mut sizes = Vec::new();
        for round in 0..60 {
            chain.extend(&state, 300, 300, 0).unwrap();
            sizes.push(state.file().space().0);
            if round % 20 == 19 {
                // The whole window undone and made again: the records the
                // sweep dropped were none of those blocks'.
                let roots: Vec<Digest> = chain.blocks.iter().map(|b| b.3).collect();
                for back in 1..=keep {
                    state.undo().unwrap();
                    chain.forget();
                    assert_eq!(state.root(), roots[roots.len() - 1 - back]);
                }
                assert_eq!(state.undo().err(), Some(Error::NoUndoRecord));
                for _ in 0..keep {
                    chain.extend(&state, 300, 300, 1).unwrap();
                }
            }
        }
        // 18,000 outputs were spent on the way; 3,000 are unspent.
        assert_eq!(state.snapshot().unwrap().outputs().count, 3000);
        let (early, late) = (sizes[15], *sizes.last().unwrap());
        assert!(late < early + early / 3, "{early} units after 16 blocks, {late} after 60");
        assert!(late * 512 < 3000 * 66 * 5, "{late} units for 3,000 unspent outputs and a window of five blocks");
        // Opened again, every unit in use is reached.
        let again = State::open(MemBackend::from_image(state.file().backend().image(Lost::All)), keep).unwrap();
        again.wait_ready().unwrap();
        assert_eq!(again.file().space().0, state.file().space().0);
        assert_eq!(again.root(), state.root());
    }

    /// Names in blocks: registered and replaced with the outputs, in the
    /// state's root, undone with the block, and proven to the root.
    #[test]
    fn names_change_with_the_blocks() {
        use crate::store::names::{empty_root, leaf_of};
        let mut rng = Rng::new(0x4a3e);
        let name = |rng: &mut Rng, text: &str| {
            let d = |rng: &mut Rng| -> Digest { rng.digest() };
            NameRecord::new(text.as_bytes(), d(rng), d(rng), d(rng)).unwrap()
        };
        let sorted = |mut puts: Vec<(Key, NameRecord, bool)>| {
            puts.sort_by_key(|p| p.0);
            puts
        };
        let state = State::open(MemBackend::new(), 6).unwrap();
        let outputs = [record(&mut rng, 1)];
        let block = |height: u32, names: &[(Key, NameRecord, bool)]| {
            state.apply(&BlockEdit {
                height,
                block: id(height, 0),
                spends: &[],
                outputs: &outputs,
                names,
                commits: &[],
                commits_spent: &[],
                state_root: None,
            })
        };
        // Block 1 registers three names.
        let (alice, bob, carol) = (name(&mut rng, "alice"), name(&mut rng, "bob"), name(&mut rng, "carol_1"));
        let root1 =
            block(1, &sorted(vec![(alice.key(), alice, false), (bob.key(), bob, false), (carol.key(), carol, false)]))
                .unwrap();
        let snap1 = state.snapshot().unwrap();
        assert_eq!(snap1.names().count, 3);
        assert_eq!(snap1.name(bob.key()).unwrap(), Some(bob));
        assert_eq!(root1, compress(&snap1.outputs().hash(), &snap1.names().hash()));
        assert_ne!(snap1.names().hash(), empty_root());
        // A name's path leads to the names' root, and that with the
        // outputs' root to the state's.
        let (proof, outputs_root) = snap1.prove_name(alice.key()).unwrap();
        assert!(proof.verify_member(&snap1.names().hash(), alice.key(), &leaf_of(&alice)));
        assert_eq!(compress(&outputs_root, &proof.root(alice.key())), root1);
        // An output's path passes the names' root on its way up.
        let (leaf, path) = snap1.prove(0).unwrap();
        assert_eq!(root_of_state_path(0, &leaf, &path), root1);
        assert_eq!(path[STATE_HEIGHT - 1], snap1.names().hash());

        // Block 2 replaces bob's record and registers dave.
        let (bob2, dave) = (NameRecord { name: bob.name, ..name(&mut rng, "x") }, name(&mut rng, "dave"));
        let root2 = block(2, &sorted(vec![(bob.key(), bob2, true), (dave.key(), dave, false)])).unwrap();
        assert_ne!(root2, root1);
        let used = state.file().space().0;
        // Refused whole: a name taken, and a name not there.
        assert_eq!(block(3, &[(alice.key(), alice, false)]).err(), Some(Error::NameTaken));
        let erin = name(&mut rng, "erin");
        assert_eq!(block(3, &[(erin.key(), erin, true)]).err(), Some(Error::NoSuchName));
        assert_eq!((state.root(), state.tip().0), (root2, 2));
        drop(snap1);
        assert!(state.file().space().0 <= used);

        // Opened again, then block 2 undone: bob's old record is back and
        // dave is gone.
        let state = State::open(MemBackend::from_image(state.file().backend().image(Lost::All)), 6).unwrap();
        assert_eq!(state.root(), root2);
        assert_eq!(state.snapshot().unwrap().name(bob.key()).unwrap(), Some(bob2));
        assert_eq!(state.undo().unwrap().0, 1);
        assert_eq!(state.root(), root1);
        let snap = state.snapshot().unwrap();
        assert_eq!(snap.name(bob.key()).unwrap(), Some(bob));
        assert_eq!(snap.name(dave.key()).unwrap(), None);
        let (proof, _) = snap.prove_name(dave.key()).unwrap();
        assert!(proof.verify_absent(&snap.names().hash(), dave.key()));
        assert_eq!(proof.leaf, crate::hash::EMPTY);
        drop(snap);
        // And block 1: no name, no output, no page.
        state.undo().unwrap();
        assert_eq!(state.root(), empty_state());
        state.wait_ready().unwrap();
        assert_eq!(state.file().space().0, crate::store::pagefile::HEADER_UNITS);
    }

    /// Blocks are applied, and undone, before the map of free space is
    /// rebuilt: their pages go past the end of the file, and nothing
    /// they free is given back. When the map is then rebuilt from the
    /// state as it was opened, it is the map of the state as it is: the
    /// same units in use as a fresh opening finds, and the space the
    /// blocks freed is there to be used.
    #[test]
    fn blocks_are_applied_before_the_map_is_rebuilt() {
        let mut chain = Chain::new(0xea51);
        let first = State::open(MemBackend::new(), 6).unwrap();
        for _ in 0..5 {
            chain.extend(&first, 100, 400, 0).unwrap();
        }
        let image = first.file().backend().image(Lost::All);
        let end = first.file().space().1;

        // Opened with no thread rebuilding the map.
        let state = State::open_idle(MemBackend::from_image(image), 6).unwrap();
        let opened = state.meta().clone();
        assert!(!state.file().is_sealed());
        let snap = state.snapshot().unwrap();
        for _ in 0..4 {
            chain.extend(&state, 200, 150, 0).unwrap();
        }
        state.undo().unwrap();
        chain.forget();
        chain.extend(&state, 50, 50, 1).unwrap();
        // The state at opening is still read whole: none of its pages
        // was written over.
        assert_eq!(snap.tip().0, 5);
        for p in chain.blocks[4].2.iter().enumerate().map(|(i, _)| opened.outputs.next - 1 - i as u64).take(50) {
            assert!(snap.output(p).unwrap().is_some());
        }
        drop(snap);
        // Everything written since lies past where the file ended.
        let grown = state.file().backend().image(Lost::All).len() as u64 / 512;
        assert!(grown > end);

        // The map rebuilt, from the state as it was opened.
        state.mark_now(&opened).unwrap();
        assert!(state.file().is_sealed());
        let fresh = State::open(MemBackend::from_image(state.file().backend().image(Lost::All)), 6).unwrap();
        fresh.wait_ready().unwrap();
        assert_eq!(state.file().space().0, fresh.file().space().0, "units in use, and units a fresh opening reaches");
        assert_eq!((state.root(), state.tip()), (fresh.root(), fresh.tip()));
        // What was freed meanwhile is used again: the file stops growing.
        let before = state.file().space().1;
        for _ in 0..6 {
            chain.extend(&state, 150, 150, 1).unwrap();
        }
        let after = state.file().space().1;
        assert!(after < before + before / 5, "{before} units at the sealing, {after} six blocks on");
        // And every block in the window can still be undone.
        while state.oldest_undo().is_some() {
            state.undo().unwrap();
        }
    }

    /// A file whose pages are damaged is found out by the rebuilding:
    /// waiting for it says so, and the state takes no more blocks.
    #[test]
    fn a_damaged_file_takes_no_blocks() {
        use crate::store::trie::Child;
        let mut chain = Chain::new(0xda3a);
        let state = State::open(MemBackend::new(), 4).unwrap();
        chain.extend(&state, 0, 2000, 0).unwrap();
        let Child::Node { page, .. } = state.meta().outputs.root else { panic!("a node") };
        let mut image = state.file().backend().image(Lost::All);
        image[page.start as usize * 512 + 40] ^= 1;
        let damaged = State::open(MemBackend::from_image(image), 4).unwrap();
        assert_eq!(damaged.wait_ready().unwrap_err().kind(), io::ErrorKind::InvalidData);
        assert!(matches!(chain.extend(&damaged, 0, 1, 0), Err(Error::Io(_))));
        // Waiting again is not an error of its own.
        assert!(damaged.wait_ready().is_ok());
    }

    /// The outputs unspent after the first `blocks` blocks of a chain,
    /// by doing what they say.
    fn replay(chain: &Chain, blocks: usize) -> std::collections::BTreeMap<u64, Record> {
        let mut unspent = std::collections::BTreeMap::new();
        let mut next = 0u64;
        for (_, spends, outputs, _) in &chain.blocks[..blocks] {
            for p in spends {
                unspent.remove(p).expect("a block spends what is unspent");
            }
            for r in outputs {
                unspent.insert(next, *r);
                next += 1;
            }
        }
        unspent
    }

    /// What another node does with a state it is handed: every part
    /// checked against its root, the parts' roots against the state's,
    /// and the outputs gathered.
    fn receive(past: &Past<'_, MemBackend>) -> std::collections::BTreeMap<u64, Record> {
        use crate::store::outputs::{part_root, parts_root};
        let level = past.level();
        assert_eq!(compress(&parts_root(level, past.parts()), &past.names_root()), past.root());
        let mut all = std::collections::BTreeMap::new();
        for (index, root) in past.parts() {
            let part = past.part(*index).unwrap();
            assert!(!part.is_empty() && part.iter().all(|(p, _)| p >> level == *index && *p < past.next()));
            assert_eq!(part_root(level, &part), *root, "part {index}");
            // One output left out, or one changed: not that part.
            assert_ne!(part_root(level, &part[1..]), *root);
            all.extend(part);
        }
        // A part with no root holds nothing.
        let absent = past.parts().last().map_or(0, |p| p.0 + 1);
        assert!(past.part(absent).unwrap().is_empty());
        // Nor does one that no state could have, which a peer may ask for.
        for index in [1 << 28, (1 << 28) + 1, 1 << 40, u64::MAX] {
            assert!(past.part(index).unwrap().is_empty());
        }
        all
    }

    /// The state as of any block of the window is handed over whole and
    /// checked: after blocks, after a reorganisation, after the file is
    /// opened again, and while later blocks are applied.
    #[test]
    fn the_state_as_of_any_block_of_the_window() {
        let keep = 6usize;
        let mut chain = Chain::new(0x9a57);
        let mut state = State::open(MemBackend::new(), keep).unwrap();
        // Parts of 512 positions, so that a few thousand outputs are many.
        state.part_level = 9;
        let check = |state: &State<MemBackend>, chain: &Chain| {
            let tip = chain.blocks.len();
            for height in tip.saturating_sub(keep)..=tip {
                let past = state.past(height as u32).unwrap();
                let (id, root) = match height {
                    0 => (crate::hash::EMPTY, empty_state()),
                    h => (chain.blocks[h - 1].0, chain.blocks[h - 1].3),
                };
                assert_eq!((past.tip(), past.root()), ((height as u32, id), root), "as of block {height} at {tip}");
                let want = replay(chain, height);
                assert_eq!(past.next(), chain.blocks[..height].iter().map(|b| b.2.len() as u64).sum::<u64>());
                assert_eq!(receive(&past), want, "as of block {height} at {tip}");
                // Each output unspent then has a path to the root then:
                // of some of them, and of a position nothing was at.
                for (index, _) in past.parts().iter().step_by(3) {
                    for (position, record) in past.part(*index).unwrap().into_iter().step_by(37) {
                        let (shown, path) = past.prove(position).unwrap().expect("it was unspent then");
                        assert_eq!(shown, record);
                        assert_eq!(
                            root_of_state_path(position, &record.leaf(), &path),
                            root,
                            "{position} as of {height}"
                        );
                    }
                }
                assert_eq!(past.prove(past.next()).unwrap(), None);
            }
            if tip > keep {
                assert_eq!(state.past((tip - keep - 1) as u32).err(), Some(Error::NoUndoRecord));
            }
            assert_eq!(state.past(tip as u32 + 1).err(), Some(Error::NoUndoRecord));
        };
        check(&state, &chain);
        for (spends, adds) in
            [(0, 700), (100, 300), (300, 20), (0, 0), (250, 900), (400, 100), (50, 0), (300, 600), (200, 200)]
        {
            chain.extend(&state, spends, adds, 0).unwrap();
            check(&state, &chain);
        }
        assert!(state.past(9).unwrap().parts().len() >= 4, "several parts");

        // A state held while the chain goes on, and back: it is still
        // the state it was made of.
        let held = state.past(6).unwrap();
        let (root, outputs) = (held.root(), receive(&held));
        state.undo().unwrap();
        state.undo().unwrap();
        chain.forget();
        chain.forget();
        for _ in 0..3 {
            chain.extend(&state, 150, 250, 1).unwrap();
        }
        assert_eq!((held.root(), receive(&held)), (root, outputs));
        drop(held);
        check(&state, &chain);

        // Opened again: the records are the file's.
        let mut again = State::open(MemBackend::from_image(state.file().backend().image(Lost::All)), keep).unwrap();
        again.part_level = 9;
        check(&again, &chain);
        chain.extend(&again, 100, 100, 1).unwrap();
        check(&again, &chain);
    }

    /// The names' root as of an earlier block goes with its state.
    #[test]
    fn the_names_root_goes_back_with_the_state() {
        let mut rng = Rng::new(0x4a57);
        let state = State::open(MemBackend::new(), 4).unwrap();
        let d = |rng: &mut Rng| -> Digest { rng.digest() };
        let mut roots = vec![state.root()];
        for (height, name) in [(1u32, "alice"), (2, "bob"), (3, "carol")] {
            let named = NameRecord::new(name.as_bytes(), d(&mut rng), d(&mut rng), d(&mut rng)).unwrap();
            let outputs = [record(&mut rng, height)];
            let names = [(named.key(), named, false)];
            let block = BlockEdit {
                height,
                block: id(height, 0),
                spends: &[],
                outputs: &outputs,
                names: &names,
                commits: &[],
                commits_spent: &[],
                state_root: None,
            };
            roots.push(state.apply(&block).unwrap());
        }
        for height in 0..=3u32 {
            let past = state.past(height).unwrap();
            assert_eq!(past.root(), roots[height as usize], "as of block {height}");
            assert_eq!(past.next(), height as u64);
        }
        assert_ne!(state.past(1).unwrap().names_root(), state.past(2).unwrap().names_root());
    }

    /// The names as of any block of the window are handed over in parts
    /// and checked: each part against its own, the parts against the
    /// names' root, and that with the outputs' against the state's.
    #[test]
    fn the_names_as_of_any_block_of_the_window() {
        use crate::store::names::{part_of, parts_root};
        use std::collections::BTreeMap;
        // Parts of a sixteenth of the keys, with many names each, and
        // the parts as they are, with few.
        for level in [116, NAME_PART_LEVEL] {
            let mut rng = Rng::new(0x4a57 + level as u64);
            let d = |rng: &mut Rng| -> Digest { rng.digest() };
            let mut state = State::open(MemBackend::new(), 5).unwrap();
            state.name_level = level;
            // The names after each block, and the root.
            let mut then: Vec<(BTreeMap<Key, NameRecord>, Digest)> = vec![(BTreeMap::new(), state.root())];
            let check = |state: &State<MemBackend>, then: &[(BTreeMap<Key, NameRecord>, Digest)]| {
                let tip = then.len() - 1;
                // After a block is undone the window reaches one less far.
                #[allow(clippy::needless_range_loop)]
                for height in state.oldest_undo().map_or(tip, |o| o as usize - 1)..=tip {
                    let past = state.past(height as u32).unwrap();
                    assert_eq!(past.root(), then[height].1, "as of block {height} at {tip}");
                    assert_eq!(parts_root(level, past.name_parts()), past.names_root());
                    let mut all = BTreeMap::new();
                    for (index, part) in past.name_parts() {
                        let names = past.names_part(*index).unwrap();
                        assert!(names.iter().all(|r| (r.key() >> level) as u32 == *index));
                        assert_eq!(part_of(level, &names), Some(*part), "part {index} as of block {height}");
                        assert_ne!(part_of(level, &names[1..]), Some(*part));
                        all.extend(names.into_iter().map(|r| (r.key(), r)));
                    }
                    assert_eq!(all, then[height].0, "as of block {height} at {tip}");
                    let absent = (0..1u32 << (120 - level)).find(|i| past.name_parts().iter().all(|p| p.0 != *i));
                    if let Some(index) = absent {
                        assert!(past.names_part(index).unwrap().is_empty());
                    }
                    // The last part there can be, and those past it,
                    // which a peer may ask for.
                    let last = ((1u64 << (Key::BITS - level)) - 1) as u32;
                    past.names_part(last).unwrap();
                    for index in [last.saturating_add(1), u32::MAX] {
                        assert!(index == last || past.names_part(index).unwrap().is_empty());
                    }
                }
            };
            let mut serial = 0u32;
            for (height, (adds, changes)) in
                [(1, 0), (40, 0), (0, 0), (60, 10), (3, 30), (0, 1), (200, 50), (10, 10)].into_iter().enumerate()
            {
                let height = height as u32 + 1;
                let mut names = then.last().unwrap().0.clone();
                let mut puts: BTreeMap<Key, (NameRecord, bool)> = BTreeMap::new();
                let known: Vec<NameRecord> = names.values().copied().collect();
                for _ in 0..changes.min(known.len()) {
                    let old = known[rng.next_u64() as usize % known.len()];
                    puts.insert(
                        old.key(),
                        (
                            NameRecord {
                                name: old.name,
                                ..NameRecord::new(b"x", d(&mut rng), d(&mut rng), d(&mut rng)).unwrap()
                            },
                            true,
                        ),
                    );
                }
                for _ in 0..adds {
                    serial += 1;
                    let new = NameRecord::new(format!("n{serial}").as_bytes(), d(&mut rng), d(&mut rng), d(&mut rng))
                        .unwrap();
                    puts.insert(new.key(), (new, false));
                }
                let puts: Vec<(Key, NameRecord, bool)> =
                    puts.into_iter().map(|(k, (r, replaces))| (k, r, replaces)).collect();
                names.extend(puts.iter().map(|p| (p.0, p.1)));
                let outputs = [record(&mut rng, height)];
                let block = BlockEdit {
                    height,
                    block: id(height, 0),
                    spends: &[],
                    outputs: &outputs,
                    names: &puts,
                    commits: &[],
                    commits_spent: &[],
                    state_root: None,
                };
                let root = state.apply(&block).unwrap();
                then.push((names, root));
                check(&state, &then);
            }
            // A block undone, and the file opened again.
            state.undo().unwrap();
            then.pop();
            check(&state, &then);
            let mut again = State::open(MemBackend::from_image(state.file().backend().image(Lost::All)), 5).unwrap();
            again.name_level = level;
            check(&again, &then);
        }
    }

    /// A header, its work and status, as the index holds them.
    fn entry(rng: &mut Rng, height: u32, block: Digest) -> crate::store::blocks::Entry {
        let mut header = [0u8; crate::block::HEADER_SIZE];
        header.iter_mut().for_each(|b| *b = rng.next_u64() as u8);
        header[32..36].copy_from_slice(&height.to_le_bytes());
        crate::store::blocks::Entry { id: block, header, work: crate::u256::U256([height as u64, 0, 0, 0]), status: 1 }
    }

    /// A block's change to the state, its header, its body and its
    /// place in the chain are one step: wherever the power is lost,
    /// all of them are there or none is.
    #[test]
    fn a_block_and_what_is_kept_of_it_are_one_step() {
        let mut rng = Rng::new(0xb0d7);
        let body: Vec<u8> = (0..200_000).map(|_| rng.next_u64() as u8).collect();
        let outputs: Vec<Record> = (0..300).map(|_| record(&mut rng, 3)).collect();
        let header = entry(&mut rng, 3, id(3, 0));
        let mut whole = 0;
        for crash in 1.. {
            let mut chain = Chain::new(0x57e9);
            let state = State::open(MemBackend::new(), 4).unwrap();
            chain.extend(&state, 0, 500, 0).unwrap();
            chain.extend(&state, 100, 100, 0).unwrap();
            let before = (state.tip(), state.root());
            // Outputs of the second block: none of them spent.
            let spends: Vec<u64> = (0..50).map(|i| 500 + i * 2).collect();
            let block = BlockEdit {
                height: 3,
                block: id(3, 0),
                spends: &spends,
                outputs: &outputs,
                names: &[],
                commits: &[],
                commits_spent: &[],
                state_root: None,
            };
            state.file().backend().crash_at(crash);
            let applied = state.apply_with(&block, |txn, blocks| {
                blocks.put_entry(txn, &header)?;
                blocks.put_body(txn, 3, &header.id, &body)?;
                blocks.set_at(txn, 3, Some(header.id))
            });
            assert!(matches!(applied, Ok(_) | Err(Error::Io(_))), "{applied:?}");
            let lost = if crash % 2 == 0 { Lost::Some(crash) } else { Lost::All };
            let again = State::open(MemBackend::from_image(state.file().backend().image(lost)), 4).unwrap();
            let snap = again.snapshot().unwrap();
            let (blocks, pages) = (snap.blocks(), snap.pages());
            if again.tip().0 == 3 {
                assert_eq!(blocks.entry(pages, &header.id).unwrap(), Some(header));
                assert_eq!(blocks.body(pages, 3, &header.id).unwrap().as_ref(), Some(&body));
                assert_eq!(blocks.at(pages, 3).unwrap(), Some(header.id));
                whole += 1;
            } else {
                assert_eq!((again.tip(), again.root()), before, "the power lost at write {crash}");
                assert_eq!(blocks.entry(pages, &header.id).unwrap(), None);
                assert!(!blocks.has_body(pages, 3, &header.id).unwrap());
                assert_eq!(blocks.at(pages, 3).unwrap(), None);
            }
            drop(snap);
            if applied.is_ok() {
                assert_eq!(again.tip().0, 3);
                // Undone, with its place in the chain: the body stays
                // until it is dropped, and then nothing of the block is
                // left in the file.
                again.wait_ready().unwrap();
                again.undo_with(|txn, blocks| blocks.set_at(txn, 3, None)).unwrap();
                let snap = again.snapshot().unwrap();
                assert_eq!(snap.blocks().at(snap.pages(), 3).unwrap(), None);
                assert!(snap.blocks().has_body(snap.pages(), 3, &header.id).unwrap());
                drop(snap);
                assert!(again.write_blocks(|txn, blocks| blocks.remove_entry(txn, &header.id)).unwrap());
                let old = State::open(MemBackend::from_image(state.file().backend().image(Lost::All)), 4).unwrap();
                old.wait_ready().unwrap();
                old.undo_with(|txn, blocks| blocks.set_at(txn, 3, None)).unwrap();
                old.write_blocks(|txn, blocks| blocks.remove_entry(txn, &header.id)).unwrap();
                assert_eq!(again.file().space().0, old.file().space().0);
                break;
            }
        }
        assert!(whole >= 1);
    }

    /// The blocks known of change without the state, a change that
    /// fails changes nothing, and a snapshot goes on reading the blocks
    /// as they were.
    #[test]
    fn blocks_change_without_the_state() {
        let mut rng = Rng::new(0xb10c);
        let mut chain = Chain::new(0xb10d);
        let state = State::open(MemBackend::new(), 4).unwrap();
        chain.extend(&state, 0, 200, 0).unwrap();
        let root = state.root();
        let headers: Vec<_> = (5..25).map(|h| entry(&mut rng, h, id(h, 3))).collect();
        state.write_blocks(|txn, blocks| headers[..10].iter().try_for_each(|e| blocks.put_entry(txn, e))).unwrap();
        let snap = state.snapshot().unwrap();
        let used = state.file().space().0;
        // Refused half way: none of it is kept.
        let failed: Result<(), Error> = state.write_blocks(|txn, blocks| {
            headers[10..].iter().try_for_each(|e| blocks.put_entry(txn, e))?;
            blocks.put_file(txn, &[9; 32], &[1; 70_000])?;
            Err(Error::NoSuchName)
        });
        assert_eq!(failed, Err(Error::NoSuchName));
        assert_eq!(state.file().space().0, used);
        assert_eq!(state.snapshot().unwrap().blocks(), snap.blocks());
        // And then kept.
        state
            .write_blocks(|txn, blocks| {
                blocks.chain[0] = 7;
                blocks.put_file(txn, &[9; 32], &[1; 70_000])?;
                headers[10..].iter().try_for_each(|e| blocks.put_entry(txn, e))
            })
            .unwrap();
        chain.extend(&state, 20, 20, 0).unwrap();
        let now = state.snapshot().unwrap();
        for (i, e) in headers.iter().enumerate() {
            assert_eq!(now.blocks().entry(now.pages(), &e.id).unwrap(), Some(*e));
            assert_eq!(snap.blocks().entry(snap.pages(), &e.id).unwrap(), (i < 10).then_some(*e));
        }
        assert_eq!(snap.blocks().file(snap.pages(), &[9; 32]).unwrap(), None);
        assert_eq!((snap.root(), snap.blocks().chain[0]), (root, 0));
        drop((snap, now));
        // Opened again: the same blocks, and no space lost to them.
        let again = State::open(MemBackend::from_image(state.file().backend().image(Lost::All)), 4).unwrap();
        again.wait_ready().unwrap();
        assert_eq!(again.file().space().0, state.file().space().0);
        let now = again.snapshot().unwrap();
        assert_eq!(now.blocks().file(now.pages(), &[9; 32]).unwrap(), Some(vec![1; 70_000]));
        assert_eq!(now.blocks().chain[0], 7);
        assert_eq!(now.blocks().entry(now.pages(), &headers[19].id).unwrap(), Some(headers[19]));
    }

    /// The table of commits follows the blocks: a commit enters with
    /// the block that makes it and leaves with the one that reveals or
    /// sweeps it, a block undone puts back what it took and takes out
    /// what it put, and a block that spends a commit the table has not
    /// is applied all the same.
    #[test]
    fn commits_follow_the_blocks() {
        let mut rng = Rng::new(0xc0a7);
        let state = State::open(MemBackend::new(), 4).unwrap();
        let d = |rng: &mut Rng| -> Digest { rng.digest() };
        let hashes: Vec<Digest> = (0..8).map(|_| d(&mut rng)).collect();
        // Block h: nine outputs and then the commit `hashes[h]`, at
        // position 10 h - 1; and whatever it spends.
        let apply = |state: &State<MemBackend>, height: u32, spent: &[u64], commits: bool| {
            let mut outputs: Vec<Record> = (0..9).map(|_| record(&mut Rng::new(height as u64), height)).collect();
            let commit = hashes[height as usize];
            outputs.push(Record { commitment: commit, amount: 0, ..outputs[0] });
            state.apply(&BlockEdit {
                height,
                block: id(height, 0),
                spends: spent,
                outputs: &outputs,
                names: &[],
                commits: &[commit],
                commits_spent: if commits { spent } else { &[] },
                state_root: None,
            })
        };
        let table = |state: &State<MemBackend>| {
            let snap = state.snapshot().unwrap();
            let all = snap.commits().up_to(snap.pages(), u32::MAX).unwrap();
            assert_eq!(all.len() as u64, snap.commits().count);
            for (position, commit) in &all {
                assert_eq!(snap.commits().position_of(snap.pages(), &commit.hash).unwrap(), Some(*position));
                assert_eq!(snap.output(*position).unwrap().unwrap().0.commitment, commit.hash);
            }
            all.into_iter().map(|(p, c)| (p, c.height)).collect::<Vec<_>>()
        };
        apply(&state, 1, &[], true).unwrap();
        apply(&state, 2, &[], true).unwrap();
        assert_eq!(table(&state), vec![(9, 1), (19, 2)]);
        // The first is revealed, and an output that is no commit spent.
        apply(&state, 3, &[3, 9], true).unwrap();
        assert_eq!(table(&state), vec![(9, 1), (19, 2), (29, 3)][1..]);
        // Undone: the commit is back, the one the block made is gone.
        state.undo().unwrap();
        assert_eq!(table(&state), vec![(9, 1), (19, 2)]);
        apply(&state, 3, &[9], true).unwrap();
        // The state as of each block has the commits of then.
        for (height, want) in [(1u32, vec![9u64]), (2, vec![9, 19]), (3, vec![19, 29])] {
            let past = state.past(height).unwrap();
            let got: Vec<u64> = past.commits(0).unwrap().into_iter().map(|c| c.0).collect();
            assert_eq!(got, want, "as of block {height}");
        }
        // Opened again, the table is the file's.
        let again = State::open(MemBackend::from_image(state.file().backend().image(Lost::All)), 4).unwrap();
        again.wait_ready().unwrap();
        assert_eq!(again.file().space().0, state.file().space().0);
        assert_eq!(table(&again), vec![(19, 2), (29, 3)]);

        // A table that lacks a commit: the block that spends it is
        // applied, and undone, as by a node that has it.
        let lacking = State::open(MemBackend::new(), 4).unwrap();
        let whole = State::open(MemBackend::new(), 4).unwrap();
        for height in 1..=2 {
            let mut outputs: Vec<Record> = (0..9).map(|_| record(&mut Rng::new(height as u64), height)).collect();
            outputs.push(Record { commitment: hashes[height as usize], amount: 0, ..outputs[0] });
            let block = BlockEdit {
                height,
                block: id(height, 0),
                spends: &[],
                outputs: &outputs,
                names: &[],
                commits: &[],
                commits_spent: &[],
                state_root: None,
            };
            lacking.apply(&block).unwrap();
            apply(&whole, height, &[], true).unwrap();
        }
        assert_eq!((table(&lacking), lacking.root()), (vec![], whole.root()));
        assert_eq!(apply(&lacking, 3, &[9], true).unwrap(), apply(&whole, 3, &[9], true).unwrap());
        assert_eq!(table(&lacking), vec![(29, 3)]);
        assert_eq!(lacking.undo().unwrap(), whole.undo().unwrap());
        assert_eq!((table(&lacking), lacking.root()), (vec![], whole.root()));
        assert_eq!(table(&whole), vec![(9, 1), (19, 2)]);
    }

    /// Blocks undone and blocks applied as one step: a branch left for
    /// another is all in place or not at all, and what the session has
    /// done so far it reads back.
    #[test]
    fn several_blocks_are_one_step() {
        let mut chain = Chain::new(0x5e55);
        let state = State::open(MemBackend::new(), 6).unwrap();
        for _ in 0..4 {
            chain.extend(&state, 40, 120, 0).unwrap();
        }
        let before = (state.tip(), state.root(), state.file().space().0);
        // Another branch from block 2: three blocks, made on a copy.
        let other = State::open(MemBackend::from_image(state.file().backend().image(Lost::All)), 6).unwrap();
        let mut fork = Chain::new(0x5e55);
        fork.blocks = chain.blocks[..2].to_vec();
        fork.next = fork.blocks.iter().map(|b| b.2.len() as u64).sum();
        other.undo().unwrap();
        other.undo().unwrap();
        fork.live = (0..fork.next).filter(|p| other.snapshot().unwrap().is_unspent(*p).unwrap()).collect();
        for _ in 0..3 {
            fork.extend(&other, 30, 90, 1).unwrap();
        }
        let edit = |b: &(Digest, Vec<u64>, Vec<Record>, Digest), height: u32, root: Option<Digest>| {
            (
                BlockEdit {
                    height,
                    block: b.0,
                    spends: &[],
                    outputs: &[],
                    names: &[],
                    commits: &[],
                    commits_spent: &[],
                    state_root: root,
                },
                b.1.clone(),
                b.2.clone(),
            )
        };
        let go_over = |wrong: bool| {
            state.session(|s| {
                assert_eq!(s.undo()?, (3, chain.blocks[2].0));
                assert_eq!(s.undo()?, (2, chain.blocks[1].0));
                assert_eq!((s.tip().0, s.root()), (2, chain.blocks[1].3));
                let mut spent = Vec::new();
                for (i, b) in fork.blocks[2..].iter().enumerate() {
                    let height = 3 + i as u32;
                    // The last block's header commits to another state.
                    let root = if wrong && i == 2 { Some(chain.blocks[0].3) } else { Some(b.3) };
                    let (e, spends, outputs) = edit(b, height, root);
                    // What it spends is there to read, as the session has it.
                    let amounts: u128 = spends
                        .iter()
                        .map(|p| s.output(*p).unwrap().unwrap())
                        .map(|(r, live)| (live as u128) * r.amount as u128)
                        .sum();
                    let (root, sum) = s.apply(&BlockEdit { spends: &spends, outputs: &outputs, ..e })?;
                    assert_eq!((root, sum), (b.3, amounts));
                    spent.push(sum);
                }
                assert_eq!(s.tip(), (5, fork.blocks[4].0));
                Ok(spent)
            })
        };
        // The branch refused at its last block: nothing has changed.
        assert_eq!(go_over(true).err(), Some(Error::StateRoot));
        assert_eq!((state.tip(), state.root(), state.file().space().0), before);
        let again = State::open(MemBackend::from_image(state.file().backend().image(Lost::All)), 6).unwrap();
        assert_eq!((again.tip(), again.root()), (before.0, before.1));
        // Taken: the state is the other branch's, and goes back down it.
        let spent = go_over(false).unwrap();
        assert!(spent.iter().all(|s| *s > 0));
        assert_eq!((state.tip(), state.root()), (other.tip(), other.root()));
        state.wait_ready().unwrap();
        other.wait_ready().unwrap();
        assert_eq!(state.file().space().0, other.file().space().0);
        for _ in 0..3 {
            assert_eq!(state.undo().unwrap(), other.undo().unwrap());
        }
        assert_eq!(state.root(), chain.blocks[1].3);
    }

    /// On a real file, closed and opened.
    #[test]
    fn on_a_real_file() {
        use crate::store::backend::{DirLock, FileBackend};
        let dir = temp_dir("state");
        let _lock = DirLock::acquire(&dir).unwrap();
        let path = dir.join("state");
        let mut chain = Chain::new(0xf11e);
        let state = State::open(FileBackend::open(&path).unwrap(), DEFAULT_WINDOW).unwrap();
        for _ in 0..12 {
            chain.extend(&state, 60, 200, 0).unwrap();
        }
        let (tip, root) = (state.tip(), state.root());
        drop(state);
        let state = State::open(FileBackend::open(&path).unwrap(), DEFAULT_WINDOW).unwrap();
        assert_eq!((state.tip(), state.root()), (tip, root));
        assert_eq!(state.oldest_undo(), Some(1));
        state.undo().unwrap();
        chain.forget();
        chain.extend(&state, 10, 10, 1).unwrap();
        assert_eq!(state.tip(), (12, id(12, 1)));
        drop(state);
        std::fs::remove_dir_all(dir).unwrap();
    }

    /// The memory the process holds now, in megabytes (Linux).
    fn peak_memory() -> u64 {
        std::fs::read_to_string("/proc/self/status")
            .ok()
            .and_then(|s| {
                s.lines()
                    .find(|l| l.starts_with("VmHWM:"))
                    .and_then(|l| l.split_whitespace().nth(1)?.parse::<u64>().ok())
            })
            .map_or(0, |kb| kb / 1024)
    }

    /// A full block applied to a large set on a real disk: 25,000 outputs
    /// spent, picked evenly among those unspent, and 25,000 made, in a
    /// set of unspent outputs spread one in eight over its positions.
    ///
    /// `TABMINER_STORE_UNSPENT` sets the unspent outputs (2,000,000
    /// unless given; 170,000,000 is the scale of Bitcoin's set), and
    /// `TABMINER_STORE_DIR` where the file goes (a disk, not memory).
    /// `cargo test --release --lib store::state::tests::cost_at_scale -- --ignored --nocapture`
    #[test]
    #[ignore = "slow: builds a state of millions of outputs on disk"]
    fn cost_at_scale() {
        use crate::store::testing::Counting;
        let unspent: u64 =
            std::env::var("TABMINER_STORE_UNSPENT").ok().and_then(|s| s.parse().ok()).unwrap_or(2_000_000);
        let dir =
            std::env::var("TABMINER_STORE_DIR").map(std::path::PathBuf::from).unwrap_or_else(|_| temp_dir("scale"));
        std::fs::create_dir_all(&dir).unwrap();
        let path = dir.join("state");
        const BLOCK: usize = 25_000;
        const BLOCKS: usize = 4;
        let mut rng = Rng::new(0x5ca1e);

        // The positions, from a generator of their own, so that a file
        // kept from an earlier run (`TABMINER_STORE_KEEP`) is known
        // without being read: of them, a sample is kept to spend from.
        let keep = std::env::var("TABMINER_STORE_KEEP").is_ok();
        let mut sample: Vec<u64> = Vec::with_capacity(BLOCKS * BLOCK);
        let mut walk = Rng::new(0x9051);
        let (mut position, mut made) = (0u64, 0u64);
        let mut step = |rng: &mut Rng, sample: &mut Vec<u64>| {
            position += 1 + walk.next_u64() % 15;
            made += 1;
            if sample.len() < BLOCKS * BLOCK {
                sample.push(position);
            } else if rng.next_u64() % made < (BLOCKS * BLOCK) as u64 {
                let at = rng.next_u64() as usize % sample.len();
                sample[at] = position;
            }
            position
        };
        if keep && path.exists() {
            let mut pick = Rng::new(0x51c);
            for _ in 0..unspent {
                step(&mut pick, &mut sample);
            }
            println!("kept the file of an earlier run");
        } else {
            let _ = std::fs::remove_file(&path);
            // Installed a part at a time, as a state received from
            // elsewhere would be.
            let t = std::time::Instant::now();
            let file = PageFile::create(Counting::open(&path)).unwrap();
            let mut outputs = Outputs::EMPTY;
            let mut pick = Rng::new(0x51c);
            let mut done = 0;
            while done < unspent {
                let part: Vec<(u64, Record, bool)> = (0..(unspent - done).min(1_000_000))
                    .map(|_| (step(&mut pick, &mut sample), record(&mut rng, 1), false))
                    .collect();
                done += part.len() as u64;
                let last = part.last().unwrap().0;
                let mut txn = file.begin().unwrap();
                outputs = outputs.install(&mut txn, &part, last + 1).unwrap();
                let meta = Meta { height: 1, tip: id(1, 0), outputs, ..Meta::empty() };
                txn.commit(&meta.to_bytes()).unwrap();
            }
            let (used, end) = file.space();
            println!(
                "installed {} outputs among {} positions in {:.1?}: file {:.1} GB, {} bytes an output; memory held {} MB",
                outputs.count,
                outputs.next,
                t.elapsed(),
                end as f64 * 512.0 / 1e9,
                used * 512 / outputs.count,
                peak_memory()
            );
        }

        // Opened, and at once ready: the map of free space is rebuilt
        // behind the blocks, unless `TABMINER_STORE_WAIT` says to wait.
        let opening = std::time::Instant::now();
        let state = State::open(Counting::open(&path), DEFAULT_WINDOW).unwrap();
        println!("opened in {:.1?}; memory held {} MB", opening.elapsed(), peak_memory());
        if std::env::var("TABMINER_STORE_WAIT").is_ok() {
            state.wait_ready().unwrap();
            let [reads, read_bytes, ..] = state.file().backend().take();
            println!(
                "the map of free space rebuilt {:.1?} after opening: {reads} pages read ({} MB)",
                opening.elapsed(),
                read_bytes >> 20
            );
        }
        let start = state.tip().0;
        let unspent_end = state.snapshot().unwrap().outputs().next;

        // The sample may hold a position twice over: each is spent once.
        sample.sort_unstable();
        sample.dedup();
        let mut order: Vec<usize> = (0..sample.len()).collect();
        for i in (1..order.len()).rev() {
            order.swap(i, rng.next_u64() as usize % (i + 1));
        }
        for (b, picked) in order.chunks(BLOCK).take(BLOCKS).enumerate() {
            let height = start + 1 + b as u32;
            let mut spends: Vec<u64> = picked.iter().map(|i| sample[*i]).collect();
            spends.sort_unstable();
            let new: Vec<Record> = (0..BLOCK).map(|_| record(&mut rng, height)).collect();
            let block = BlockEdit {
                height,
                block: id(height, 0),
                spends: &spends,
                outputs: &new,
                names: &[],
                commits: &[],
                commits_spent: &[],
                state_root: None,
            };
            let t = std::time::Instant::now();
            state.apply(&block).unwrap();
            let times = *state.times.lock().unwrap();
            let [reads, read_bytes, writes, written] = state.file().backend().take();
            println!(
                "block {height}: {} spent, {BLOCK} made | applied and durable in {:.2?} (outputs {:.2?}, names and window {:.2?}, sweep {:.2?}, commit {:.2?}) | read {reads} pages ({} MB) | wrote {} MB in {writes} writes | memory held {} MB",
                spends.len(),
                t.elapsed(),
                times[0],
                times[1] - times[0],
                times[2] - times[1],
                times[3] - times[2],
                read_bytes >> 20,
                written >> 20,
                peak_memory()
            );
        }
        // The last block undone.
        let t = std::time::Instant::now();
        state.undo().unwrap();
        println!("the last block undone in {:.2?}", t.elapsed());
        state.wait_ready().unwrap();
        println!("the map of free space whole {:.1?} after opening", opening.elapsed());

        // The state as of the block the run began at, for another node:
        // made, then some of its parts taken and checked.
        let t = std::time::Instant::now();
        let past = state.past(start).unwrap();
        let made = t.elapsed();
        let t = std::time::Instant::now();
        let (mut outputs, mut bytes) = (0usize, 0usize);
        let step = (past.parts().len() / 64).max(1);
        let taken: Vec<&(u64, Digest)> = past.parts().iter().step_by(step).collect();
        for (index, root) in &taken {
            let part = past.part(*index).unwrap();
            assert_eq!(crate::store::outputs::part_root(past.level(), &part), *root);
            outputs += part.len();
            bytes += part.len() * (8 + crate::store::outputs::RECORD_BYTES);
        }
        println!(
            "the state as of block {start}, {} blocks back: made in {made:.2?} ({} parts); {} parts of it read and checked in {:.2?}, {} outputs and {} KB a part; memory held {} MB",
            state.tip().0 - start,
            past.parts().len(),
            taken.len(),
            t.elapsed(),
            outputs / taken.len().max(1),
            bytes / taken.len().max(1) / 1024,
            peak_memory()
        );
        assert_eq!(past.next(), unspent_end);

        // The same parts put by a node that receives: each checked
        // against its root, put in its trie and made durable.
        {
            use crate::store::receive::{Receiving, Target};
            let into = dir.join("received");
            let _ = std::fs::remove_file(&into);
            let target = Target { height: start, block: past.tip().1, state_root: past.root(), next: past.next() };
            let parts: Vec<(u64, Vec<(u64, Record)>)> =
                taken.iter().map(|(index, _)| (*index, past.part(*index).unwrap())).collect();
            let mut receiving =
                Receiving::open(Counting::open(&into), target, past.parts(), past.name_parts()).unwrap();
            let t = std::time::Instant::now();
            for (index, part) in &parts {
                receiving.put(*index, part).unwrap();
            }
            let took = t.elapsed();
            let left = receiving.missing().len();
            println!(
                "received: {} parts put in {took:.2?}, {:.1?} a part; {left} still to come, about {:.0}s at that rate; file {} KB a part",
                parts.len(),
                took / parts.len() as u32,
                took.as_secs_f64() / parts.len() as f64 * left as f64,
                std::fs::metadata(&into).unwrap().len() / parts.len() as u64 / 1024,
            );
            drop(receiving);
            std::fs::remove_file(&into).unwrap();
        }
        drop(past);
        // Undone to where it began, so that a kept file is as it was.
        while state.tip().0 > start {
            state.undo().unwrap();
        }
        drop(state);
        if !keep {
            std::fs::remove_file(&path).unwrap();
        }
    }
}
