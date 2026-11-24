//! A state taken from other nodes, part by part.
//!
//! A node that joins does not apply every block there has been: it takes
//! the state as of one block from the nodes there are
//! ([`super::state::Past`]) and goes on from that block. What it knows
//! beforehand is the block and the state root its header commits to
//! ([`Target`]); everything else it is handed is checked against that
//! root before it is kept:
//!
//! - the roots of the parts of the outputs and of the names, which must
//!   hash to the state's root;
//! - each part, which must hash to its root among those.
//!
//! So the parts can come from any nodes, in any order, and a node that
//! hands over something else is found out by that one part.
//!
//! # Stopped and gone on with
//!
//! Each part is durable when it is put: the file's root record says the
//! state is being received and for which block, and holds the tries as
//! far as they have got. Opened again, with the parts' roots asked for
//! again, what is wanted is what the tries do not hold yet. Nothing more
//! is stored to know it.
//!
//! # Another block
//!
//! If the taking outlasts the window of the nodes that serve it, it is
//! gone on with for a later block: opened with that block's roots, the
//! parts whose roots are the same are kept, and only those that changed
//! are asked for again, each put in place of what there was.
//!
//! The blocks a node knows of ([`super::blocks`]) are in the same file
//! and are not the state: they are kept through all of it, and written
//! to while the state is received.
//!
//! Until the state is whole the file cannot be opened as a state
//! ([`super::state::State::open`] refuses it); [`Receiving::finish`]
//! makes it one, with no block to undo.

use std::collections::BTreeMap;
use std::io;

use std::sync::Arc;

use super::backend::Backend;
use super::blocks::Blocks;
use super::commits::{Commit, Commits};
use super::names::{self, Names, PART_LEVEL as NAME_PART_LEVEL};
use super::outputs::{self, HEIGHT, Outputs, PART_LEVEL, Record};
use super::pagefile::{PageFile, Txn};
use super::state::{Meta, RECEIVING, State};
use super::trie::Part;
use super::window::Window;
use crate::error::Error;
use crate::hash::Digest;
use crate::hash::{digest_from_bytes, digest_to_bytes};
use crate::name::{KEY_BITS, Key, Record as NameRecord};
use crate::registry::state_root as compress;

/// The root record while receiving: what it begins with, the block's
/// height and id, the tries so far, the blocks known of, the state root
/// wanted and the position after the last output.
const RECORD: usize = COMMITS_AT + Commits::BYTES + 32 + 8;
const COMMITS_AT: usize = BLOCKS_AT + Blocks::BYTES;
const BLOCKS_AT: usize = 37 + Outputs::BYTES + Names::BYTES;
const _: () = assert!(RECORD <= super::pagefile::ROOT_MAX);

fn corrupt(what: &'static str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, what)
}

/// The block a state is received as of, and what is known of its state
/// beforehand.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Target {
    pub height: u32,
    /// The block's id.
    pub block: Digest,
    /// The state root its header commits to.
    pub state_root: Digest,
    /// The position the next output after it takes.
    pub next: u64,
}

/// A state being received: see the module.
pub struct Receiving<B: Backend + 'static> {
    file: Arc<PageFile<B>>,
    target: Target,
    outputs: Outputs,
    names: Names,
    blocks: Blocks,
    commits: Commits,
    level: u32,
    name_level: u32,
    /// The root of each part of the outputs as of the block, and of each
    /// part held now.
    want: BTreeMap<u64, Digest>,
    have: BTreeMap<u64, Digest>,
    /// The parts of the outputs still to be put, once asked for and
    /// kept up from then on: a state has a hundred thousand parts, and
    /// which are missing is asked at every one that arrives.
    lacking: std::sync::Mutex<Option<std::collections::BTreeSet<u64>>>,
    /// The same of the names.
    want_names: BTreeMap<u32, Part>,
    have_names: BTreeMap<u32, Part>,
    /// Whether the roots wanted are known. They are not kept in the
    /// file: a state whose receiving was cut short is opened without
    /// them ([`open`]), and they are to be asked for again.
    known: bool,
}

impl<B: Backend + 'static> Receiving<B> {
    /// Begins to receive the state as of `target` into the file of
    /// `backend`, or goes on: the file holds nothing, or a state being
    /// received, for this block or another.
    ///
    /// `parts` and `name_parts` are the roots of the state's parts as
    /// another node gave them ([`super::state::Past::parts`],
    /// [`super::state::Past::name_parts`]): [`Error::PartRoot`] if they
    /// do not hash to the target's state root. A file that holds a whole
    /// state is refused (`AlreadyExists`).
    pub fn open(
        backend: B,
        target: Target,
        parts: &[(u64, Digest)],
        name_parts: &[(u32, Part)],
    ) -> Result<Receiving<B>, Error> {
        Receiving::open_at(backend, target, parts, name_parts, PART_LEVEL, NAME_PART_LEVEL)
    }

    fn open_at(
        backend: B,
        target: Target,
        parts: &[(u64, Digest)],
        name_parts: &[(u32, Part)],
        level: u32,
        name_level: u32,
    ) -> Result<Receiving<B>, Error> {
        Self::check(&target, parts, name_parts, level, name_level)?;
        let file = PageFile::open_or_create(backend)?;
        let (outputs, names, blocks, commits) = {
            let root = file.root();
            let b = root.payload();
            if b.is_empty() && root.seq == 0 {
                (Outputs::EMPTY, Names::EMPTY, Blocks::EMPTY, Commits::EMPTY)
            } else if b.len() == RECORD && b[0] == RECEIVING {
                let names_at = 37 + Outputs::BYTES;
                (
                    Outputs::from_bytes(&b[37..names_at])?,
                    Names::from_bytes(&b[names_at..BLOCKS_AT])?,
                    Blocks::from_bytes(&b[BLOCKS_AT..COMMITS_AT])?,
                    Commits::from_bytes(&b[COMMITS_AT..COMMITS_AT + Commits::BYTES])?,
                )
            } else {
                return Err(io::Error::new(io::ErrorKind::AlreadyExists, "the file holds a state").into());
            }
        };
        // A file gone on with: what of it is in use is all the tries
        // reach, known before anything is put in place of anything.
        if !file.is_sealed() {
            outputs.mark(&file)?;
            names.mark(&file)?;
            blocks.mark(&file)?;
            commits.mark(&file)?;
            file.seal();
        }
        Receiving::begin(Arc::new(file), target, parts, name_parts, level, name_level, outputs, names, blocks, commits)
    }

    /// Receives the state as of `target` in place of the state `state`
    /// holds, which is given up: for a node that has the headers and
    /// little else, and takes the state rather than every block. The
    /// blocks it knows of are kept ([`Receiving::write_blocks`]); its
    /// outputs, its names and what undoes its blocks are freed, which
    /// reads every node of their tries.
    pub fn replace(
        state: State<B>,
        target: Target,
        parts: &[(u64, Digest)],
        name_parts: &[(u32, Part)],
    ) -> Result<Receiving<B>, Error> {
        Receiving::replace_with(state, target, parts, name_parts, |_, _| Ok(()))
    }

    /// The same, and `change` made to the blocks known of in the same
    /// step: what is said of the chain's blocks goes with the state
    /// they were the blocks of, or neither does.
    pub fn replace_with(
        state: State<B>,
        target: Target,
        parts: &[(u64, Digest)],
        name_parts: &[(u32, Part)],
        change: impl FnOnce(&Txn<'_, B>, &mut Blocks) -> Result<(), Error>,
    ) -> Result<Receiving<B>, Error> {
        Receiving::replace_at(state, target, parts, name_parts, PART_LEVEL, NAME_PART_LEVEL, change)
    }

    fn replace_at(
        state: State<B>,
        target: Target,
        parts: &[(u64, Digest)],
        name_parts: &[(u32, Part)],
        level: u32,
        name_level: u32,
        change: impl FnOnce(&Txn<'_, B>, &mut Blocks) -> Result<(), Error>,
    ) -> Result<Receiving<B>, Error> {
        Self::check(&target, parts, name_parts, level, name_level)?;
        let (file, mut meta) = state.dissolve()?;
        // One step: the state is gone and one is being received.
        let mut txn = file.begin()?;
        meta.outputs.free(&txn)?;
        meta.names.free(&txn)?;
        meta.commits.free(&txn)?;
        meta.window.clear(&mut txn)?;
        change(&txn, &mut meta.blocks)?;
        let mut this = Receiving {
            file: file.clone(),
            target,
            outputs: Outputs::EMPTY,
            names: Names::EMPTY,
            blocks: meta.blocks,
            commits: Commits::EMPTY,
            level,
            name_level,
            lacking: Default::default(),
            want: BTreeMap::new(),
            have: BTreeMap::new(),
            want_names: BTreeMap::new(),
            have_names: BTreeMap::new(),
            known: true,
        };
        txn.commit(&this.record())?;
        this.want = parts.iter().copied().collect();
        this.lacking = Default::default();
        this.want_names = name_parts.iter().copied().collect();
        Ok(this)
    }

    /// Whether `parts` and `name_parts` are the roots of the parts of
    /// the state `target` names: what [`Receiving::open`] and
    /// [`Receiving::replace`] check first.
    pub fn check_roots(target: &Target, parts: &[(u64, Digest)], name_parts: &[(u32, Part)]) -> Result<(), Error> {
        Self::check(target, parts, name_parts, PART_LEVEL, NAME_PART_LEVEL)
    }

    /// Goes on for another block: the state as of `target`, whose parts'
    /// roots are these, in place of the one being received. The parts
    /// whose roots are the same are kept, and only those that changed
    /// are wanted again ([`Receiving::missing`]). [`Error::PartRoot`],
    /// with nothing changed, if the roots are not the target's.
    ///
    /// (What is refused comes back with why, whole and by value: it is
    /// what the caller goes on with, and is not put behind a pointer to
    /// be handed back.)
    #[allow(clippy::result_large_err)]
    pub fn retarget(
        self,
        target: Target,
        parts: &[(u64, Digest)],
        name_parts: &[(u32, Part)],
    ) -> Result<Receiving<B>, (Receiving<B>, Error)> {
        if let Err(e) = Self::check(&target, parts, name_parts, self.level, self.name_level) {
            return Err((self, e));
        }
        let (level, name_level) = (self.level, self.name_level);
        let Receiving { file, outputs, names, blocks, commits, .. } = self;
        // (Past the check, a failure is the file's, and there is no
        // going back to what was.)
        Receiving::begin(file.clone(), target, parts, name_parts, level, name_level, outputs, names, blocks, commits)
            .map_err(|e| {
                let lost = Receiving {
                    file,
                    target,
                    outputs,
                    names,
                    blocks,
                    commits,
                    level,
                    name_level,
                    lacking: Default::default(),
                    want: BTreeMap::new(),
                    have: BTreeMap::new(),
                    want_names: BTreeMap::new(),
                    have_names: BTreeMap::new(),
                    known: false,
                };
                (lost, e)
            })
    }

    /// What was handed over, against the root: first that it is a list
    /// of parts at all, since the hashing takes that for granted.
    fn check(
        target: &Target,
        parts: &[(u64, Digest)],
        name_parts: &[(u32, Part)],
        level: u32,
        name_level: u32,
    ) -> Result<(), Error> {
        let ordered = parts.windows(2).all(|w| w[0].0 < w[1].0) && name_parts.windows(2).all(|w| w[0].0 < w[1].0);
        let in_range = target.next <= 1 << HEIGHT
            && parts.last().is_none_or(|p| p.0 < target.next.div_ceil(1 << level))
            && name_parts.last().is_none_or(|p| (p.0 as u64) < 1 << (KEY_BITS as u32 - name_level))
            // (A part of the names' tree is never one name's leaf alone.)
            && name_parts.iter().all(|p| !p.1.single)
            // (Nor is a part listed that holds nothing: its root is what
            // the tree has where there is no part, so the roots would
            // hash to the state's all the same, and no outputs or
            // names anyone sent would ever be it.)
            && parts.iter().all(|p| p.1 != outputs::part_root(level, &[]))
            && name_parts.iter().all(|p| p.1.hash != names::empty_at(name_level));
        if !ordered || !in_range {
            return Err(Error::PartRoot);
        }
        let root = compress(&outputs::parts_root(level, parts), &names::parts_root(name_level, name_parts));
        match root == target.state_root {
            true => Ok(()),
            false => Err(Error::PartRoot),
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn begin(
        file: Arc<PageFile<B>>,
        target: Target,
        parts: &[(u64, Digest)],
        name_parts: &[(u32, Part)],
        level: u32,
        name_level: u32,
        outputs: Outputs,
        names: Names,
        blocks: Blocks,
        commits: Commits,
    ) -> Result<Receiving<B>, Error> {
        let mut this = Receiving {
            lacking: Default::default(),
            have: outputs.parts(&*file, level)?.into_iter().collect(),
            have_names: names.parts(&*file, name_level)?.into_iter().collect(),
            want: parts.iter().copied().collect(),
            want_names: name_parts.iter().copied().collect(),
            known: true,
            file,
            target,
            outputs,
            names,
            blocks,
            commits,
            level,
            name_level,
        };
        // Parts held for another block that this one's state has not.
        let gone: Vec<u64> = this.have.keys().filter(|i| !this.want.contains_key(i)).copied().collect();
        for index in gone {
            this.exchange(index, &[], &[])?;
        }
        let gone: Vec<u32> = this.have_names.keys().filter(|i| !this.want_names.contains_key(i)).copied().collect();
        for index in gone {
            this.exchange_names(index, &[])?;
        }
        // The block is the file's from here on, before any part of it.
        let txn = this.file.begin()?;
        txn.commit(&this.record())?;
        Ok(this)
    }

    /// The blocks known of, and the file that reads them.
    pub fn blocks(&self) -> (&Blocks, &PageFile<B>) {
        (&self.blocks, &self.file)
    }

    /// Changes the blocks known of while the state is received: headers
    /// and bodies go on arriving. As [`State::write_blocks`].
    pub fn write_blocks<T>(
        &mut self,
        change: impl FnOnce(&Txn<'_, B>, &mut Blocks) -> Result<T, Error>,
    ) -> Result<T, Error> {
        let txn = self.file.begin()?;
        let before = self.blocks;
        let done = change(&txn, &mut self.blocks).inspect_err(|_| self.blocks = before);
        let done = done?;
        // (What did not become the file's is not what the next change
        // starts from: its pages are free again.)
        txn.commit(&self.record()).inspect_err(|_| self.blocks = before)?;
        Ok(done)
    }

    /// The block the state is received as of.
    pub fn target(&self) -> &Target {
        &self.target
    }

    /// Whether the roots of the state's parts are known: not, in a
    /// state opened again after its receiving was cut short, until it
    /// is gone on with ([`Receiving::retarget`]). Until then nothing
    /// can be put, and it cannot be finished.
    pub fn roots_known(&self) -> bool {
        self.known
    }

    /// The parts of the outputs still to be put, ascending.
    pub fn missing(&self) -> Vec<u64> {
        self.want.iter().filter(|(i, root)| self.have.get(i) != Some(root)).map(|(i, _)| *i).collect()
    }

    /// The first `most` of the parts of the outputs still to be put,
    /// ascending, and how many there are in all: what
    /// [`Receiving::missing`] says, without going through every part
    /// each time it is asked.
    pub fn missing_first(&self, most: usize) -> (Vec<u64>, usize) {
        let mut lacking = self.lacking.lock().unwrap_or_else(|e| e.into_inner());
        let set = lacking.get_or_insert_with(|| self.missing().into_iter().collect());
        (set.iter().take(most).copied().collect(), set.len())
    }

    /// The part of index `index` is kept, as it is wanted.
    fn put_done(&self, index: u64) {
        if let Some(set) = &mut *self.lacking.lock().unwrap_or_else(|e| e.into_inner()) {
            set.remove(&index);
        }
    }

    /// The parts of the names still to be put, ascending.
    pub fn missing_names(&self) -> Vec<u32> {
        self.want_names.iter().filter(|(i, part)| self.have_names.get(i) != Some(part)).map(|(i, _)| *i).collect()
    }

    /// Puts the part of the outputs of index `index`: its unspent
    /// outputs as of the block, ascending by position
    /// ([`super::state::Past::part`]). Durable when this returns.
    /// [`Error::PartRoot`], with nothing changed, if they are not that
    /// part.
    pub fn put(&mut self, index: u64, outputs: &[(u64, Record)]) -> Result<(), Error> {
        self.put_with(index, outputs, &[])
    }

    /// [`Receiving::put`], with which of the outputs are commits of
    /// names, as the other node has them
    /// ([`super::state::Past::commits`]): position and hash, ascending.
    /// Each must be the commit of its output, or the part is refused;
    /// that none is left out cannot be known, and need not be
    /// ([`super::commits`]).
    pub fn put_with(&mut self, index: u64, outputs: &[(u64, Record)], commits: &[(u64, Digest)]) -> Result<(), Error> {
        self.checked(index, outputs, commits)?;
        if self.have.get(&index) == self.want.get(&index) {
            return Ok(());
        }
        self.exchange(index, outputs, commits)
    }

    /// Several parts put at once ([`Receiving::put_with`] of each, in
    /// one step): all of them durable when this returns, or, if any is
    /// not its part, none ([`Error::PartRoot`]). They are checked, and
    /// put, on as many threads as there are: many parts so take little
    /// longer than one. `parts` ascend by index.
    #[allow(clippy::type_complexity)]
    pub fn put_many(&mut self, parts: &[(u64, &[(u64, Record)], &[(u64, Digest)])]) -> Result<(), Error> {
        if !parts.windows(2).all(|w| w[0].0 < w[1].0) {
            return Err(Error::PartRoot);
        }
        let checks = crate::parallel::par_map_min(parts.len(), 1, |i| self.checked(parts[i].0, parts[i].1, parts[i].2));
        checks.into_iter().collect::<Result<(), Error>>()?;
        // One that is held already, as another, is put by itself: what
        // it held is to be taken out.
        if parts.iter().any(|p| self.have.contains_key(&p.0)) {
            for (index, outputs, commits) in parts {
                if self.have.get(index) != self.want.get(index) {
                    self.exchange(*index, outputs, commits)?;
                }
            }
            return Ok(());
        }
        let puts: Vec<(u64, Record, bool)> = parts.iter().flat_map(|p| p.1.iter().map(|o| (o.0, o.1, false))).collect();
        let mut txn = self.file.begin()?;
        let (outputs_before, commits_before) = (self.outputs, self.commits);
        let done = (|| {
            self.outputs = self.outputs.exchange(&mut txn, &[], &puts, self.target.next)?;
            for (_, outputs, commits) in parts {
                for (position, hash) in *commits {
                    let height = outputs[outputs.binary_search_by_key(position, |o| o.0).unwrap()].1.height;
                    self.commits.add(&txn, *position, Commit { hash: *hash, height })?;
                }
            }
            Ok::<(), Error>(())
        })();
        if let Err(e) = done {
            (self.outputs, self.commits) = (outputs_before, commits_before);
            return Err(e);
        }
        if let Err(e) = txn.commit(&self.record()) {
            (self.outputs, self.commits) = (outputs_before, commits_before);
            return Err(e.into());
        }
        for (index, outputs, _) in parts {
            if let Some(root) = self.want.get(index).filter(|_| !outputs.is_empty()) {
                self.have.insert(*index, *root);
                self.put_done(*index);
            }
        }
        Ok(())
    }

    /// Whether `outputs`, with `commits`, are the part of index `index`
    /// that is wanted: [`Error::PartRoot`] if not.
    fn checked(&self, index: u64, outputs: &[(u64, Record)], commits: &[(u64, Digest)]) -> Result<(), Error> {
        if !self.known {
            return Err(Error::PartsMissing);
        }
        let is_commit = |(position, hash): &(u64, Digest)| {
            outputs.binary_search_by_key(position, |o| o.0).is_ok_and(|i| {
                let record = &outputs[i].1;
                record.amount == 0 && record.commitment == *hash
            })
        };
        if !commits.windows(2).all(|w| w[0].0 < w[1].0) || !outputs.windows(2).all(|w| w[0].0 < w[1].0) {
            return Err(Error::PartRoot);
        }
        if !commits.iter().all(is_commit) {
            return Err(Error::PartRoot);
        }
        let Some(want) = self.want.get(&index) else { return Err(Error::PartRoot) };
        let sound = outputs.windows(2).all(|w| w[0].0 < w[1].0)
            && outputs.iter().all(|o| o.0 >> self.level == index && o.0 < self.target.next);
        if !sound || outputs::part_root(self.level, outputs) != *want {
            return Err(Error::PartRoot);
        }
        Ok(())
    }

    /// Puts the part of the names of index `index`: its names' records
    /// as of the block, ascending by key
    /// ([`super::state::Past::names_part`]). As [`Receiving::put`].
    pub fn put_names(&mut self, index: u32, records: &[NameRecord]) -> Result<(), Error> {
        if !self.known {
            return Err(Error::PartsMissing);
        }
        let Some(want) = self.want_names.get(&index) else { return Err(Error::PartRoot) };
        let sound = records.windows(2).all(|w| w[0].key() < w[1].key())
            && records.iter().all(|r| r.key() >> self.name_level == index as Key);
        if !sound || names::part_of(self.name_level, records) != Some(*want) {
            return Err(Error::PartRoot);
        }
        if self.have_names.get(&index) == Some(want) {
            return Ok(());
        }
        self.exchange_names(index, records)
    }

    /// The state, whole: the file is one a state is opened of from here
    /// on, at the block, with no block to undo. `keep` is the length of
    /// its window. [`Error::PartsMissing`] if parts are still to be put.
    pub fn finish(self, keep: usize) -> Result<State<B>, Error> {
        self.finish_with(keep, |_, _| Ok(())).map_err(|(_, e)| e)
    }

    /// The same, and `change` made to the blocks known of in the same
    /// step: the chain's blocks are said to be the state's block's
    /// branch as the state becomes whole, or neither happens. Refused
    /// before that step is the file's, what was being received is
    /// handed back as it was, to go on with.
    #[allow(clippy::type_complexity, clippy::result_large_err)]
    pub fn finish_with(
        self,
        keep: usize,
        change: impl FnOnce(&Txn<'_, B>, &mut Blocks) -> Result<(), Error>,
    ) -> Result<State<B>, (Option<Box<Receiving<B>>>, Error)> {
        if !self.known || self.have != self.want || self.have_names != self.want_names {
            return Err((Some(Box::new(self)), Error::PartsMissing));
        }
        // Every part was checked, so this is the root unless the file
        // lost something since.
        if compress(&self.outputs.hash(), &self.names.hash()) != self.target.state_root {
            return Err((Some(Box::new(self)), corrupt("the state received is not the block's").into()));
        }
        let file = self.file.clone();
        let made = (|| {
            let mut blocks = self.blocks;
            let txn = file.begin()?;
            change(&txn, &mut blocks)?;
            let meta = Meta {
                height: self.target.height,
                tip: self.target.block,
                outputs: Outputs { next: self.target.next, ..self.outputs },
                names: self.names,
                window: Window::default(),
                sweep: 0,
                blocks,
                commits: self.commits,
            };
            txn.commit(&meta.to_bytes())?;
            Ok::<_, Error>(meta)
        })();
        match made {
            Ok(meta) => State::of(file, meta, keep).map_err(|e| (None, e.into())),
            Err(e) => Err((Some(Box::new(self)), e)),
        }
    }

    fn record(&self) -> [u8; RECORD] {
        let mut out = Vec::with_capacity(RECORD);
        out.push(RECEIVING);
        out.extend_from_slice(&self.target.height.to_le_bytes());
        out.extend_from_slice(&digest_to_bytes(&self.target.block));
        out.extend_from_slice(&self.outputs.to_bytes());
        out.extend_from_slice(&self.names.to_bytes());
        out.extend_from_slice(&self.blocks.to_bytes());
        out.extend_from_slice(&self.commits.to_bytes());
        out.extend_from_slice(&digest_to_bytes(&self.target.state_root));
        out.extend_from_slice(&self.target.next.to_le_bytes());
        out.try_into().unwrap()
    }

    /// Puts `outputs` in place of what the part of index `index` holds:
    /// what is in both stays, since a position's output never changes.
    fn exchange(&mut self, index: u64, outputs: &[(u64, Record)], commits: &[(u64, Digest)]) -> Result<(), Error> {
        let held = match self.have.contains_key(&index) {
            true => self.outputs.part(&*self.file, self.level, index)?,
            false => Vec::new(),
        };
        // (The same output, not only the same place: held for a block of
        // another branch, a place past where the two part has another
        // output on each, and the one held would else stay for good.)
        let same =
            |a: &[(u64, Record)], p: u64, r: &Record| a.binary_search_by_key(&p, |x| x.0).is_ok_and(|i| a[i].1 == *r);
        let held: Vec<(u64, Record)> = held.into_iter().map(|h| (h.0, h.1)).collect();
        let removes: Vec<u64> = held.iter().filter(|h| !same(outputs, h.0, &h.1)).map(|h| h.0).collect();
        let puts: Vec<(u64, Record, bool)> =
            outputs.iter().filter(|o| !same(&held, o.0, &o.1)).map(|o| (o.0, o.1, false)).collect();
        // (What does not become the file's is not what the next change
        // starts from: its pages are free again.)
        let before = (self.outputs, self.commits);
        let mut txn = self.file.begin()?;
        let done = (|| {
            self.outputs = self.outputs.exchange(&mut txn, &removes, &puts, self.target.next)?;
            // The part's commits with it: those of what it held go.
            self.commits.remove_between(&txn, index << self.level, (index + 1) << self.level)?;
            for (position, hash) in commits {
                let height = outputs[outputs.binary_search_by_key(position, |o| o.0).unwrap()].1.height;
                self.commits.add(&txn, *position, Commit { hash: *hash, height })?;
            }
            Ok::<(), Error>(())
        })();
        let done = done.and_then(|()| Ok(txn.commit(&self.record())?));
        if let Err(e) = done {
            (self.outputs, self.commits) = before;
            return Err(e);
        }
        match self.want.get(&index).filter(|_| !outputs.is_empty()) {
            Some(root) => self.have.insert(index, *root),
            None => self.have.remove(&index),
        };
        // (Whatever it was: which are missing is reckoned anew.)
        match self.have.get(&index) == self.want.get(&index) {
            true => self.put_done(index),
            false => *self.lacking.lock().unwrap_or_else(|e| e.into_inner()) = None,
        }
        Ok(())
    }

    /// The same of the names, whose records do change: one held with
    /// another record is taken out and put again.
    fn exchange_names(&mut self, index: u32, records: &[NameRecord]) -> Result<(), Error> {
        let held = match self.have_names.contains_key(&index) {
            true => self.names.part(&*self.file, self.name_level, index)?,
            false => Vec::new(),
        };
        let same =
            |a: &[NameRecord], r: &NameRecord| a.binary_search_by_key(&r.key(), |x| x.key()).is_ok_and(|i| a[i] == *r);
        let removes: Vec<Key> = held.iter().filter(|h| !same(records, h)).map(|h| h.key()).collect();
        let puts: Vec<(Key, NameRecord, bool)> =
            records.iter().filter(|r| !same(&held, r)).map(|r| (r.key(), *r, false)).collect();
        let before = self.names;
        let mut txn = self.file.begin()?;
        self.names = self.names.exchange(&mut txn, &removes, &puts)?;
        txn.commit(&self.record()).inspect_err(|_| self.names = before)?;
        match self.want_names.get(&index).filter(|_| !records.is_empty()) {
            Some(part) => self.have_names.insert(index, *part),
            None => self.have_names.remove(&index),
        };
        Ok(())
    }
}

/// What a file was found to hold.
pub enum Opened<B: Backend + 'static> {
    /// A state.
    Whole(State<B>),
    /// A state whose receiving was cut short: what was received is
    /// kept, and the blocks known of. The roots of its parts are to be
    /// asked for again ([`Receiving::roots_known`]).
    Receiving(Receiving<B>),
}

/// Opens the file of `backend`, whichever it holds: a state (or
/// nothing, which is the state before any block), or one that was
/// being received when the node stopped. `keep` is the length of a
/// state's window.
pub fn open<B: Backend + 'static>(backend: B, keep: usize) -> Result<Opened<B>, Error> {
    let file = PageFile::open_or_create(backend)?;
    let Some(target) = pending(&file)? else {
        return Ok(Opened::Whole(State::open_file(file, keep)?));
    };
    let (outputs, names, blocks, commits) = {
        let root = file.root();
        let b = root.payload();
        let names_at = 37 + Outputs::BYTES;
        (
            Outputs::from_bytes(&b[37..names_at])?,
            Names::from_bytes(&b[names_at..BLOCKS_AT])?,
            Blocks::from_bytes(&b[BLOCKS_AT..COMMITS_AT])?,
            Commits::from_bytes(&b[COMMITS_AT..COMMITS_AT + Commits::BYTES])?,
        )
    };
    // What of the file is in use is all the tries reach.
    if !file.is_sealed() {
        outputs.mark(&file)?;
        names.mark(&file)?;
        blocks.mark(&file)?;
        commits.mark(&file)?;
        file.seal();
    }
    Ok(Opened::Receiving(Receiving {
        have: outputs.parts(&file, PART_LEVEL)?.into_iter().collect(),
        have_names: names.parts(&file, NAME_PART_LEVEL)?.into_iter().collect(),
        lacking: Default::default(),
        want: BTreeMap::new(),
        want_names: BTreeMap::new(),
        known: false,
        file: Arc::new(file),
        target,
        outputs,
        names,
        blocks,
        commits,
        level: PART_LEVEL,
        name_level: NAME_PART_LEVEL,
    }))
}

/// The block a file's state is being received as of, if it is: what a
/// node reads when it starts, to know whether to go on receiving.
pub fn pending<B: Backend>(file: &PageFile<B>) -> io::Result<Option<Target>> {
    let root = file.root();
    let b = root.payload();
    if b.len() != RECORD || b[0] != RECEIVING {
        return Ok(None);
    }
    let digest = |b: &[u8]| digest_from_bytes(b).ok_or_else(|| corrupt("the block received for is not a digest"));
    Ok(Some(Target {
        height: u32::from_le_bytes(b[1..5].try_into().unwrap()),
        block: digest(&b[5..37])?,
        state_root: digest(&b[RECORD - 40..RECORD - 8])?,
        next: u64::from_le_bytes(b[RECORD - 8..].try_into().unwrap()),
    }))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::store::state::{BlockEdit, Past};
    use crate::store::testing::{Lost, MemBackend};
    use crate::test_util::Rng;

    /// Parts small enough that a few thousand outputs and a few hundred
    /// names are many of them, and blocks that leave some as they were.
    const LEVEL: u32 = 5;
    const NAME_LEVEL: u32 = 112;
    const KEEP: usize = 6;

    /// A block as it was applied to the node that serves.
    struct Block {
        id: Digest,
        spends: Vec<u64>,
        outputs: Vec<Record>,
        names: Vec<(Key, NameRecord, bool)>,
        commits: Vec<Digest>,
        commits_spent: Vec<u64>,
        root: Digest,
        next: u64,
    }

    impl Block {
        fn edit(&self, height: u32) -> BlockEdit<'_> {
            BlockEdit {
                height,
                block: self.id,
                spends: &self.spends,
                outputs: &self.outputs,
                names: &self.names,
                commits: &self.commits,
                commits_spent: &self.commits_spent,
                state_root: Some(self.root),
            }
        }
    }

    /// A node with `blocks` blocks applied, each spending, making
    /// outputs, registering names and replacing some.
    fn serving(seed: u64, blocks: u32) -> (State<MemBackend>, Vec<Block>) {
        let mut rng = Rng::new(seed);
        let d = |rng: &mut Rng| -> Digest { rng.digest() };
        let mut state = State::open(MemBackend::new(), KEEP).unwrap();
        state.set_levels(LEVEL, NAME_LEVEL);
        let (mut live, mut next, mut known): (Vec<u64>, u64, Vec<NameRecord>) = (Vec::new(), 0, Vec::new());
        // The commits made: the height and the position of each.
        let mut made: Vec<(u32, u64)> = Vec::new();
        let mut chain = Vec::new();
        for height in 1..=blocks {
            let mut spends: Vec<u64> = (0..(live.len() / 3).min(15))
                .map(|_| {
                    let i = rng.next_u64() as usize % live.len();
                    live.swap_remove(i)
                })
                .collect();
            // The commit of two blocks back is spent, by every other block.
            let commits_spent: Vec<u64> =
                made.iter().filter(|m| m.0 + 2 == height && height % 2 == 1).map(|m| m.1).collect();
            spends.extend(&commits_spent);
            spends.sort_unstable();
            let mut outputs: Vec<Record> = (0..300 + rng.next_u64() % 400)
                .map(|_| Record {
                    commitment: d(&mut rng),
                    memo: rng.digest()[..20].try_into().unwrap(),
                    amount: rng.next_u64(),
                    height,
                })
                .collect();
            let mut puts: BTreeMap<Key, (NameRecord, bool)> = BTreeMap::new();
            for _ in 0..known.len().min(8) {
                let old = known[rng.next_u64() as usize % known.len()];
                let other = NameRecord::new(b"x", d(&mut rng), d(&mut rng), d(&mut rng)).unwrap();
                puts.insert(old.key(), (NameRecord { name: old.name, ..other }, true));
            }
            for i in 0..30 {
                let name = format!("name{height}x{i}");
                let new = NameRecord::new(name.as_bytes(), d(&mut rng), d(&mut rng), d(&mut rng)).unwrap();
                puts.insert(new.key(), (new, false));
                known.push(new);
            }
            let names: Vec<(Key, NameRecord, bool)> =
                puts.into_iter().map(|(k, (r, replaces))| (k, r, replaces)).collect();
            let id: Digest = core::array::from_fn(|i| (height * 100 + i as u32) as u8 ^ (height >> 2) as u8);
            // One commit a block, the last of its outputs.
            let commit = d(&mut rng);
            outputs.push(Record {
                commitment: commit,
                memo: rng.digest()[..20].try_into().unwrap(),
                amount: 0,
                height,
            });
            made.push((height, next + outputs.len() as u64 - 1));
            let commits = vec![commit];
            let mut block =
                Block { id, spends, outputs, names, commits, commits_spent, root: crate::hash::EMPTY, next: 0 };
            block.root = state.apply(&BlockEdit { state_root: None, ..block.edit(height) }).unwrap();
            live.extend(next..next + block.outputs.len() as u64 - 1);
            next += block.outputs.len() as u64;
            block.next = next;
            chain.push(block);
        }
        (state, chain)
    }

    fn target(chain: &[Block], height: u32) -> Target {
        let b = &chain[height as usize - 1];
        Target { height, block: b.id, state_root: b.root, next: b.next }
    }

    fn open(backend: MemBackend, target: Target, past: &Past<'_, MemBackend>) -> Result<Receiving<MemBackend>, Error> {
        Receiving::open_at(backend, target, past.parts(), past.name_parts(), LEVEL, NAME_LEVEL)
    }

    /// Puts every part still missing, in an order of the seed's.
    fn fill(receiving: &mut Receiving<MemBackend>, past: &Past<'_, MemBackend>, seed: u64) {
        let mut rng = Rng::new(seed);
        let (mut parts, mut names) = (receiving.missing(), receiving.missing_names());
        while !parts.is_empty() || !names.is_empty() {
            if !parts.is_empty() && (names.is_empty() || !rng.next_u64().is_multiple_of(4)) {
                let index = parts.swap_remove(rng.next_u64() as usize % parts.len());
                receiving.put_with(index, &past.part(index).unwrap(), &past.commits(index).unwrap()).unwrap();
            } else {
                let index = names.swap_remove(rng.next_u64() as usize % names.len());
                receiving.put_names(index, &past.names_part(index).unwrap()).unwrap();
            }
        }
    }

    /// The node that received goes on as the one that served did: the
    /// same blocks give the same roots, and the outputs and names it
    /// holds are the same.
    fn goes_on(mut state: State<MemBackend>, source: &State<MemBackend>, chain: &[Block], from: u32) {
        state.set_levels(LEVEL, NAME_LEVEL);
        assert_eq!(state.tip(), (from, chain[from as usize - 1].id));
        assert_eq!(state.root(), chain[from as usize - 1].root);
        assert_eq!(state.oldest_undo(), None, "no block to undo");
        for height in from + 1..=chain.len() as u32 {
            assert_eq!(state.apply(&chain[height as usize - 1].edit(height)).unwrap(), chain[height as usize - 1].root);
        }
        let (ours, theirs) = (state.past(chain.len() as u32).unwrap(), source.past(chain.len() as u32).unwrap());
        assert_eq!((ours.parts(), ours.name_parts()), (theirs.parts(), theirs.name_parts()));
        for (index, _) in theirs.parts() {
            assert_eq!(ours.part(*index).unwrap(), theirs.part(*index).unwrap());
        }
        for (index, _) in theirs.name_parts() {
            assert_eq!(ours.names_part(*index).unwrap(), theirs.names_part(*index).unwrap());
        }
        drop((ours, theirs));
        // And has the same commits waiting.
        let (ours, theirs) = (state.snapshot().unwrap(), source.snapshot().unwrap());
        let waiting = theirs.commits().up_to(theirs.pages(), u32::MAX).unwrap();
        assert!(waiting.len() >= 2 && (waiting.len() as u64) == theirs.commits().count);
        assert_eq!(ours.commits().up_to(ours.pages(), u32::MAX).unwrap(), waiting);
        for (position, commit) in &waiting {
            assert_eq!(ours.commits().position_of(ours.pages(), &commit.hash).unwrap(), Some(*position));
        }
        drop((ours, theirs));
        // It serves in its turn, as of the blocks it applied itself.
        assert!(state.past(from).is_ok());
        // Back to the block it was received as of, and no further.
        while state.oldest_undo().is_some() {
            state.undo().unwrap();
        }
        assert_eq!((state.tip().0, state.root()), (from, chain[from as usize - 1].root));
        assert_eq!(state.undo().err(), Some(Error::NoUndoRecord));
        // Nothing of the receiving is left in the file but the state.
        state.wait_ready().unwrap();
        let fresh = State::open(MemBackend::from_image(state.file().backend().image(Lost::All)), KEEP).unwrap();
        fresh.wait_ready().unwrap();
        assert_eq!(state.file().space().0, fresh.file().space().0);
    }

    /// A state as of a block some way back is received whole, the parts
    /// in any order, and the node goes on from that block.
    #[test]
    fn a_state_is_received_and_gone_on_from() {
        let (source, chain) = serving(0x5e4d, 9);
        for height in [9, 6, 3] {
            let past = source.past(height).unwrap();
            assert!(past.parts().len() >= 4 && past.name_parts().len() >= 4, "several parts of each");
            let mut receiving = open(MemBackend::new(), target(&chain, height), &past).unwrap();
            assert_eq!(receiving.missing().len(), past.parts().len());
            assert_eq!(receiving.missing_names().len(), past.name_parts().len());
            assert_eq!(pending(&receiving.file).unwrap(), Some(target(&chain, height)));
            fill(&mut receiving, &past, height as u64);
            assert!(receiving.missing().is_empty() && receiving.missing_names().is_empty());
            // A part put twice changes nothing.
            let first = past.parts()[0].0;
            let used = receiving.file.space().0;
            receiving.put_with(first, &past.part(first).unwrap(), &past.commits(first).unwrap()).unwrap();
            assert_eq!(receiving.file.space().0, used);
            let state = receiving.finish(KEEP).unwrap();
            assert_eq!(pending(state.file()).unwrap(), None);
            goes_on(state, &source, &chain, height);
        }
    }

    /// What is not the state is refused, and changes nothing.
    #[test]
    fn what_is_not_the_state_is_refused() {
        let (source, chain) = serving(0x0bad, 7);
        let past = source.past(5).unwrap();
        let t = target(&chain, 5);
        let open_with = |t: Target, parts: &[(u64, Digest)], names: &[(u32, Part)]| {
            Receiving::open_at(MemBackend::new(), t, parts, names, LEVEL, NAME_LEVEL).err()
        };
        // The parts' roots: one left out, one changed, two out of order,
        // one past the last position, the names' of another kind, the
        // roots of another block.
        let (parts, names) = (past.parts().to_vec(), past.name_parts().to_vec());
        assert_eq!(open_with(t, &parts[1..], &names), Some(Error::PartRoot));
        let mut changed = parts.clone();
        changed[2].1[0] ^= 1;
        assert_eq!(open_with(t, &changed, &names), Some(Error::PartRoot));
        let mut swapped = parts.clone();
        swapped.swap(0, 1);
        assert_eq!(open_with(t, &swapped, &names), Some(Error::PartRoot));
        let mut beyond = parts.clone();
        beyond.push((t.next.div_ceil(1 << LEVEL), parts[0].1));
        assert_eq!(open_with(t, &beyond, &names), Some(Error::PartRoot));
        let mut flagged = names.clone();
        flagged[0].1.single ^= true;
        assert_eq!(open_with(t, &parts, &flagged), Some(Error::PartRoot));
        let mut far = names.clone();
        far.push((1 << (KEY_BITS as u32 - NAME_LEVEL), names[0].1));
        assert_eq!(open_with(t, &parts, &far), Some(Error::PartRoot));
        let other = source.past(6).unwrap();
        assert_eq!(open_with(t, other.parts(), other.name_parts()), Some(Error::PartRoot));
        assert_eq!(open_with(Target { next: (1 << HEIGHT) + 1, ..t }, &parts, &names), Some(Error::PartRoot));

        let mut receiving = open(MemBackend::new(), t, &past).unwrap();
        let used = receiving.file.space().0;
        // A part: one output left out, one changed, one more, out of
        // order, under another index, at an index with no part.
        let index = parts[1].0;
        let part = past.part(index).unwrap();
        assert_eq!(receiving.put(index, &part[1..]), Err(Error::PartRoot));
        let mut changed = part.clone();
        changed[0].1.amount ^= 1;
        assert_eq!(receiving.put(index, &changed), Err(Error::PartRoot));
        let mut more = part.clone();
        more.push((t.next, part[0].1));
        assert_eq!(receiving.put(index, &more), Err(Error::PartRoot));
        let mut swapped = part.clone();
        swapped.swap(0, 1);
        assert_eq!(receiving.put(index, &swapped), Err(Error::PartRoot));
        assert_eq!(receiving.put(parts[0].0, &part), Err(Error::PartRoot));
        assert_eq!(receiving.put(1 << 30, &part), Err(Error::PartRoot));
        assert_eq!(receiving.put(index, &[]), Err(Error::PartRoot));
        // A commit that is not its output's: another hash, an output
        // that is no commit, a position the part has not.
        let with = parts.iter().map(|p| p.0).find(|i| !past.commits(*i).unwrap().is_empty()).unwrap();
        let (part, commits) = (past.part(with).unwrap(), past.commits(with).unwrap());
        let other = [(commits[0].0, part[0].1.commitment)];
        assert_eq!(receiving.put_with(with, &part, &other), Err(Error::PartRoot));
        let plain = part.iter().find(|o| o.1.amount != 0).unwrap().0;
        assert_eq!(receiving.put_with(with, &part, &[(plain, commits[0].1)]), Err(Error::PartRoot));
        assert_eq!(receiving.put_with(with, &part, &[(1 << 40, commits[0].1)]), Err(Error::PartRoot));
        // The same of the names.
        let index = names[1].0;
        let part = past.names_part(index).unwrap();
        let mut changed = part.clone();
        changed[0].owner[0] ^= 1;
        assert_eq!(receiving.put_names(index, &changed), Err(Error::PartRoot));
        assert_eq!(receiving.put_names(index, &[]), Err(Error::PartRoot));
        assert_eq!(receiving.put_names(names[0].0, &part), Err(Error::PartRoot));
        assert_eq!(receiving.put_names(u32::MAX, &part), Err(Error::PartRoot));
        assert_eq!(receiving.file.space().0, used);
        assert_eq!(receiving.missing().len(), parts.len());

        // Not whole, it is not a state: neither finished nor opened.
        receiving.put_with(parts[0].0, &past.part(parts[0].0).unwrap(), &past.commits(parts[0].0).unwrap()).unwrap();
        let image = receiving.file.backend().image(Lost::All);
        assert_eq!(
            State::open(MemBackend::from_image(image), KEEP).err().map(|e| e.kind()),
            Some(io::ErrorKind::InvalidData)
        );
        assert_eq!(receiving.finish(KEEP).err(), Some(Error::PartsMissing));
        // And a state is not received over.
        let whole = MemBackend::from_image(source.file().backend().image(Lost::All));
        assert_eq!(open(whole, t, &past).err(), Some(Error::Io(io::ErrorKind::AlreadyExists)));
    }

    /// Stopped at any point, with or without the power lost, the
    /// receiving goes on from the parts that were put.
    #[test]
    fn a_receiving_stopped_goes_on() {
        let (source, chain) = serving(0x570b, 8);
        let past = source.past(6).unwrap();
        let t = target(&chain, 6);
        let all = past.parts().len() + past.name_parts().len();
        for (round, lost) in [Lost::All, Lost::None, Lost::Some(7), Lost::Some(8)].into_iter().enumerate() {
            let mut receiving = open(MemBackend::new(), t, &past).unwrap();
            // Some parts put, then the power lost in the middle of one more.
            let (parts, names) = (receiving.missing(), receiving.missing_names());
            for index in parts.iter().step_by(2) {
                receiving.put_with(*index, &past.part(*index).unwrap(), &past.commits(*index).unwrap()).unwrap();
            }
            for index in names.iter().skip(1).step_by(3) {
                receiving.put_names(*index, &past.names_part(*index).unwrap()).unwrap();
            }
            let put = parts.len().div_ceil(2) + (names.len() - 1).div_ceil(3);
            receiving.file.backend().crash_at(1 + round as u64);
            assert!(
                receiving.put_with(parts[1], &past.part(parts[1]).unwrap(), &past.commits(parts[1]).unwrap()).is_err()
            );
            let image = receiving.file.backend().image(lost);

            let file = PageFile::open(MemBackend::from_image(image.clone())).unwrap();
            assert_eq!(pending(&file).unwrap(), Some(t));
            let mut again = open(MemBackend::from_image(image), t, &past).unwrap();
            let left = again.missing().len() + again.missing_names().len();
            // The part the power was lost in is there or it is not.
            assert!(left == all - put || left == all - put - 1, "{left} left of {all}, {put} put");
            fill(&mut again, &past, round as u64);
            goes_on(again.finish(KEEP).unwrap(), &source, &chain, 6);
        }
    }

    /// Gone on with for another block: the parts that are the same stay,
    /// those that changed are put again, those the other block's state
    /// has not are taken out. To a later block and to an earlier one.
    #[test]
    fn a_receiving_goes_on_for_another_block() {
        let (source, chain) = serving(0x4e37, 9);
        for (first, then) in [(4, 8), (8, 4), (5, 9), (6, 6)] {
            let past = source.past(first).unwrap();
            let mut receiving = open(MemBackend::new(), target(&chain, first), &past).unwrap();
            // Most of it, not all.
            for index in receiving.missing().into_iter().skip(1) {
                receiving.put_with(index, &past.part(index).unwrap(), &past.commits(index).unwrap()).unwrap();
            }
            for index in receiving.missing_names().into_iter().skip(1) {
                receiving.put_names(index, &past.names_part(index).unwrap()).unwrap();
            }
            let image = receiving.file.backend().image(Lost::All);
            drop(receiving);

            let other = source.past(then).unwrap();
            let mut again = open(MemBackend::from_image(image), target(&chain, then), &other).unwrap();
            assert_eq!(pending(&again.file).unwrap(), Some(target(&chain, then)));
            // Asked for again: what differs between the two blocks, and
            // the one part of each left out before, no more.
            let same = other.parts().iter().filter(|p| past.parts().contains(p)).count();
            let missing = again.missing().len();
            assert!(missing >= other.parts().len() - same && missing <= other.parts().len() - same + 1);
            if first != then {
                assert!(same > 0 && same < other.parts().len(), "{same} parts the same of {}", other.parts().len());
            }
            let same = other.name_parts().iter().filter(|p| past.name_parts().contains(p)).count();
            assert!(again.missing_names().len() <= other.name_parts().len() - same + 1);
            fill(&mut again, &other, then as u64);
            goes_on(again.finish(KEEP).unwrap(), &source, &chain, then);
        }
    }

    /// A state was being received as of a block of one branch, and is
    /// gone on with as of a block of another: where the two have
    /// another output each at the same place, the one held goes. And a
    /// part listed that holds nothing is no part, though the roots hash
    /// to the state's with it or without.
    #[test]
    fn a_receiving_goes_on_for_a_block_of_another_branch() {
        let ((one, chain), (other, branch)) = (serving(0x4e37, 6), serving(0x51aa, 6));
        let past = one.past(6).unwrap();
        let mut receiving = open(MemBackend::new(), target(&chain, 6), &past).unwrap();
        fill(&mut receiving, &past, 1);
        let image = receiving.file.backend().image(Lost::All);
        drop(receiving);
        let then = other.past(6).unwrap();
        let mut again = open(MemBackend::from_image(image), target(&branch, 6), &then).unwrap();
        assert!(!again.missing().is_empty());
        fill(&mut again, &then, 2);
        goes_on(again.finish(KEEP).unwrap(), &other, &branch, 6);

        let absent = (0..).find(|i| then.parts().iter().all(|p| p.0 != *i)).unwrap();
        let mut parts = then.parts().to_vec();
        parts.push((absent, outputs::part_root(LEVEL, &[])));
        parts.sort_by_key(|p| p.0);
        if parts.last().unwrap().0 < target(&branch, 6).next.div_ceil(1 << LEVEL) {
            assert_eq!(outputs::parts_root(LEVEL, &parts), outputs::parts_root(LEVEL, then.parts()));
        }
        let refused =
            Receiving::open_at(MemBackend::new(), target(&branch, 6), &parts, then.name_parts(), LEVEL, NAME_LEVEL);
        assert_eq!(refused.err(), Some(Error::PartRoot));
    }

    /// A node that has the headers and a state of its own takes the
    /// state as of a later block in its place: the blocks it knows of
    /// are kept through it, more arrive meanwhile, and the state it had
    /// leaves nothing behind.
    #[test]
    fn a_state_is_received_in_place_of_another() {
        use crate::store::blocks::Entry;
        let (source, chain) = serving(0x4e91, 8);
        let entry = |height: u32| {
            let mut header = [height as u8; crate::block::HEADER_SIZE];
            header[32..36].copy_from_slice(&height.to_le_bytes());
            Entry {
                id: chain[height as usize - 1].id,
                header,
                work: crate::u256::U256([height as u64, 0, 0, 0]),
                status: 3,
            }
        };
        // Its own state: the first three blocks, applied, and the
        // headers of the first six.
        let mut node = State::open(MemBackend::new(), KEEP).unwrap();
        node.set_levels(LEVEL, NAME_LEVEL);
        for height in 1..=3u32 {
            node.apply_with(&chain[height as usize - 1].edit(height), |txn, blocks| {
                blocks.put_body(txn, height, &entry(height).id, &[height as u8; 90_000])?;
                blocks.set_at(txn, height, Some(entry(height).id))
            })
            .unwrap();
        }
        node.write_blocks(|txn, blocks| (1..=6).try_for_each(|h| blocks.put_entry(txn, &entry(h)))).unwrap();

        let past = source.past(6).unwrap();
        let t = target(&chain, 6);
        // Roots that are not the block's: the node's state is left.
        let wrong =
            Receiving::replace_at(node, t, &past.parts()[1..], past.name_parts(), LEVEL, NAME_LEVEL, |_, _| Ok(()));
        assert_eq!(wrong.err(), Some(Error::PartRoot));
        let mut node = State::open(MemBackend::new(), KEEP).unwrap();
        node.set_levels(LEVEL, NAME_LEVEL);
        for height in 1..=3u32 {
            node.apply_with(&chain[height as usize - 1].edit(height), |txn, blocks| {
                blocks.put_body(txn, height, &entry(height).id, &[height as u8; 90_000])?;
                blocks.set_at(txn, height, Some(entry(height).id))
            })
            .unwrap();
        }
        node.write_blocks(|txn, blocks| (1..=6).try_for_each(|h| blocks.put_entry(txn, &entry(h)))).unwrap();

        let mut receiving =
            Receiving::replace_at(node, t, past.parts(), past.name_parts(), LEVEL, NAME_LEVEL, |_, _| Ok(())).unwrap();
        assert_eq!(receiving.missing().len(), past.parts().len());
        // Some parts, a header and a body meanwhile, and a stop.
        for index in receiving.missing().into_iter().step_by(3) {
            receiving.put_with(index, &past.part(index).unwrap(), &past.commits(index).unwrap()).unwrap();
        }
        receiving
            .write_blocks(|txn, blocks| {
                blocks.put_entry(txn, &entry(7))?;
                blocks.put_body(txn, 7, &entry(7).id, &[7; 300_000])
            })
            .unwrap();
        // A change that fails leaves the blocks as they were.
        let failed: Result<(), Error> = receiving.write_blocks(|txn, blocks| {
            blocks.put_entry(txn, &entry(8))?;
            Err(Error::NoSuchName)
        });
        assert_eq!(failed, Err(Error::NoSuchName));
        let image = receiving.file.backend().image(Lost::All);
        drop(receiving);

        let mut again = open(MemBackend::from_image(image), t, &past).unwrap();
        fill(&mut again, &past, 3);
        let (blocks, file) = again.blocks();
        for height in 1..=7u32 {
            assert_eq!(blocks.entry(file, &entry(height).id).unwrap(), Some(entry(height)));
            assert_eq!(blocks.at(file, height).unwrap(), (height <= 3).then_some(entry(height).id));
        }
        assert_eq!(blocks.entry(file, &entry(8).id).unwrap(), None);
        assert_eq!(blocks.body(file, 2, &entry(2).id).unwrap(), Some(vec![2; 90_000]));
        assert_eq!(blocks.body(file, 7, &entry(7).id).unwrap(), Some(vec![7; 300_000]));
        let state = again.finish(KEEP).unwrap();
        let snap = state.snapshot().unwrap();
        assert_eq!(snap.blocks().entry(snap.pages(), &entry(7).id).unwrap(), Some(entry(7)));
        assert_eq!(snap.blocks().body(snap.pages(), 7, &entry(7).id).unwrap(), Some(vec![7; 300_000]));
        drop(snap);
        // The same as the node that served, and nothing in the file
        // that is not the state or the blocks.
        goes_on(state, &source, &chain, 6);
    }

    /// An empty state is received too: the one before any output.
    #[test]
    fn nothing_is_received() {
        let state = State::open(MemBackend::new(), KEEP).unwrap();
        let block = BlockEdit {
            height: 1,
            block: [1u8; 32],
            spends: &[],
            outputs: &[],
            names: &[],
            commits: &[],
            commits_spent: &[],
            state_root: None,
        };
        let root = state.apply(&block).unwrap();
        let past = state.past(1).unwrap();
        let t = Target { height: 1, block: [1u8; 32], state_root: root, next: 0 };
        let receiving = Receiving::open(MemBackend::new(), t, past.parts(), past.name_parts()).unwrap();
        assert!(receiving.missing().is_empty() && receiving.missing_names().is_empty());
        let received = receiving.finish(KEEP).unwrap();
        assert_eq!((received.tip(), received.root()), (state.tip(), root));
    }
}
