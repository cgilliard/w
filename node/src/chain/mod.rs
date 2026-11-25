//! The chain: which blocks are valid, and which of them make it.
//!
//! The store ([`crate::store`]) keeps the state and the blocks and knows
//! nothing of what they mean. This is what they mean: the rules a header
//! and a block are held to, the work that chooses between branches, and
//! what a block's proof is asked to show.
//!
//! - [`params`]: a network's fixed numbers, what a block pays, and
//!   genesis.
//! - [`verify`]: the statement a block's proof attests to, and who
//!   checks it.
//! - [`headers`]: the rules of a header, and the headers a node keeps
//!   ahead of the blocks it has.
//! - [`apply`]: the rules of a block, and the chain going from one
//!   branch to another.
//! - [`leaves`]: what a header's auxiliary bytes commit to, the votes
//!   they cast and the files voted for.
//!
//! A [`Chain`] is a store with a network's rules over it.

pub mod apply;
#[cfg(feature = "dev")]
pub mod debug;
pub mod headers;
pub mod leaves;
pub mod receive;

// The network's parameters, and what a proof is asked to show, are
// `tabshared`'s: the prover and the wallet go by them too.
pub use tabshared::{params, verify};

use std::sync::{Arc, Mutex, RwLock};

use crate::block::Header;
use crate::error::Error;
use crate::hash::Digest;
use crate::pow::{Dataset, SeedText};
use crate::store::backend::Backend;
use crate::store::blocks::Blocks;
use crate::store::pagefile::{Extent, PageFile, ReadPages, Txn};
use crate::store::receive::Receiving;
use crate::store::state::{Snapshot, State};
use crate::u256::U256;
use headers::{Known, Status};
use params::ChainParams;
use std::sync::{RwLockReadGuard, RwLockWriteGuard};

/// A network's chain, in a store.
pub struct Chain<B: Backend + 'static, V> {
    store: RwLock<Store<B>>,
    /// Blocks that can be undone, and whose bodies are kept.
    keep: usize,
    params: ChainParams,
    seed: SeedText<'static>,
    verifier: V,
    /// A table of the proof of work, if one is loaded: a header's work is
    /// checked against it in microseconds, where from the seed text
    /// alone it takes tens of milliseconds.
    dataset: RwLock<Option<Arc<Dataset<'static>>>>,
    /// A header and block 1 of its branch, as last found: where a
    /// schedule that starts at the first block is anchored.
    anchor: Mutex<Option<(Digest, Header)>>,
    /// Debugging only: a header's work is taken as what it claims
    /// ([`Chain::debug_trust_work`]).
    trust_work: std::sync::atomic::AtomicBool,
    /// How many times what the votes for a consensus file are counted
    /// from, other than the chain's blocks, has changed: leaves and
    /// files kept or let go, and this node's own leaves
    /// ([`Chain::votes_epoch`]).
    votes_epoch: std::sync::atomic::AtomicU64,
    /// The header of the chain's last block as last read, with its id
    /// ([`Chain::tip`]).
    tip_read: Mutex<Option<(Digest, headers::Known)>>,
    /// Heights whose full proof of work was checked, for the tests.
    #[cfg(test)]
    pub(crate) full_pow_heights: Mutex<Vec<u32>>,
}

impl<B: Backend + 'static, V> Chain<B, V> {
    /// Opens the chain kept in `backend`, or begins it: an empty store
    /// is given the network's genesis. A store whose state was being
    /// received from other nodes when it was last closed is opened as
    /// it was: with its headers, and without a state until that is
    /// gone on with ([`Chain::receiving`]). A store that holds another
    /// genesis is refused ([`Error::WrongGenesis`]). `keep` is how many
    /// blocks can be undone ([`crate::store::state`]); `seed` must be the
    /// text of `params.pow`.
    pub fn open(
        backend: B,
        keep: usize,
        params: ChainParams,
        seed: SeedText<'static>,
        verifier: V,
    ) -> Result<Self, Error> {
        assert_eq!(*seed.params(), params.pow, "the seed text is the network's");
        let genesis = params.genesis().header;
        let id = genesis.hash();
        let store = match crate::store::receive::open(backend, keep)? {
            crate::store::receive::Opened::Whole(state) => {
                let there = {
                    let snap = state.snapshot()?;
                    snap.blocks().at(snap.pages(), 0)?
                };
                match there {
                    Some(found) if found == id => {}
                    Some(_) => return Err(Error::WrongGenesis),
                    None => state.write_blocks(|txn, blocks| {
                        let known = Known { header: genesis, work: U256::ZERO, status: Status::Valid };
                        blocks.put_entry(txn, &known.entry())?;
                        blocks.set_at(txn, 0, Some(id))
                    })?,
                }
                Store::Whole(state)
            }
            // The node stopped while it was taking its state from
            // others: it has the blocks it knew of and what it had
            // received, and goes on from there.
            crate::store::receive::Opened::Receiving(receiving) => {
                let (blocks, file) = receiving.blocks();
                if blocks.at(file, 0)? != Some(id) {
                    return Err(Error::WrongGenesis);
                }
                Store::Receiving(receiving)
            }
        };
        Ok(Chain {
            store: RwLock::new(store),
            keep,
            params,
            seed,
            verifier,
            dataset: RwLock::new(None),
            anchor: Mutex::new(None),
            trust_work: std::sync::atomic::AtomicBool::new(false),
            votes_epoch: std::sync::atomic::AtomicU64::new(0),
            tip_read: Mutex::new(None),
            #[cfg(test)]
            full_pow_heights: Mutex::new(Vec::new()),
        })
    }

    pub fn params(&self) -> &ChainParams {
        &self.params
    }

    pub fn verifier(&self) -> &V {
        &self.verifier
    }

    /// How many blocks can be undone: how far back the state can be
    /// handed over as it was.
    pub fn keep(&self) -> usize {
        self.keep
    }

    /// What is held of the chain's blocks, as it is and not as it would
    /// be had the chain been here all along: the lowest height a body
    /// is kept at, and the height of the oldest block that can be
    /// undone. A node that took its state whole has neither from under
    /// the block it took it as of, however many blocks it keeps.
    pub fn held(&self) -> Result<(Option<u32>, Option<u32>), Error> {
        let state = self.whole()?;
        let undo = state.oldest_undo();
        let snap = state.snapshot()?;
        Ok((snap.blocks().oldest_kept(snap.pages())?, undo))
    }

    /// What the chain is kept in, to read.
    pub(crate) fn store(&self) -> Held<'_, B> {
        let once = Once::taking(&self.store as *const RwLock<Store<B>> as usize);
        Held { guard: self.store.read().unwrap_or_else(|e| e.into_inner()), _once: once }
    }

    /// The same, to put another in its place.
    pub(crate) fn store_mut(&self) -> RwLockWriteGuard<'_, Store<B>> {
        self.store.write().unwrap_or_else(|e| e.into_inner())
    }

    /// The state: [`Error::Receiving`] while it is being received from
    /// others, when there is none to read.
    pub fn whole(&self) -> Result<StateRef<'_, B>, Error> {
        let store = self.store();
        match &*store {
            Store::Whole(_) => Ok(StateRef(store)),
            _ => Err(Error::Receiving),
        }
    }

    /// The state, of a chain known to have one.
    ///
    /// # Panics
    ///
    /// While the state is being received from others.
    pub fn state(&self) -> StateRef<'_, B> {
        self.whole().expect("a chain with its state")
    }

    /// Whether the state is being received from others: the chain has
    /// headers, and no blocks join it, until it is whole.
    pub fn receiving(&self) -> bool {
        matches!(&*self.store(), Store::Receiving(_))
    }

    /// Tests: the store's bytes as they would be after a crash.
    #[cfg(test)]
    pub(crate) fn image(&self) -> Vec<u8>
    where
        B: crate::store::testing::Imaged,
    {
        match &*self.store() {
            Store::Whole(state) => state.file().backend().bytes(),
            Store::Receiving(receiving) => receiving.blocks().1.backend().bytes(),
            Store::Gone => panic!("no store"),
        }
    }

    /// Changes the blocks known of, whichever the store is.
    pub(crate) fn write_blocks<T>(
        &self,
        change: impl FnOnce(&Txn<'_, B>, &mut Blocks) -> Result<T, Error>,
    ) -> Result<T, Error> {
        // (A state orders its own writers: nothing is taken from those
        // who read the chain while this waits for a block being applied,
        // as it would be were the store asked for whole: whoever waits
        // to write it keeps every reader that comes after waiting too.)
        {
            let store = self.store();
            if let Store::Whole(state) = &*store {
                return state.write_blocks(change);
            }
        }
        match &mut *self.store_mut() {
            Store::Whole(state) => state.write_blocks(change),
            Store::Receiving(receiving) => receiving.write_blocks(change),
            Store::Gone => Err(Error::Receiving),
        }
    }

    /// Debugging only: from here until it is said otherwise, a header's
    /// work is taken as what the header claims of it. For a node making
    /// a long chain of its own to try others with
    /// ([`crate::miner::extend_empty`]): never for what comes from
    /// anyone else.
    #[cfg(feature = "dev")]
    pub fn debug_trust_work(&self, trust: bool) {
        self.trust_work.store(trust, std::sync::atomic::Ordering::Relaxed);
    }

    /// Gives the chain a table of the proof of work to check headers
    /// against. It is used for the heights it is the table of.
    pub fn set_dataset(&self, dataset: Arc<Dataset<'static>>) {
        *self.dataset.write().unwrap() = Some(dataset);
    }
}

/// What a chain is kept in: a state, with the blocks known of beside
/// it, or the same blocks with a state still being received from other
/// nodes ([`crate::store::receive`]).
///
/// The headers are the same business either way: which are known,
/// which has the most work, what is still to fetch. So everything of
/// the chain that is about headers reads and writes through this, and
/// goes on while a state is received; what is about the state (a block
/// joining, an output looked up) needs it whole.
pub(crate) enum Store<B: Backend + 'static> {
    Whole(State<B>),
    Receiving(Receiving<B>),
    /// Between the two, for the moment one is made of the other; and
    /// for good if that failed, when the store must be opened again.
    Gone,
}

impl<B: Backend + 'static> Store<B> {
    /// The blocks known of, to read: of one moment, whatever is written
    /// meanwhile.
    pub(crate) fn view(&self) -> Result<View<'_, B>, Error> {
        match self {
            Store::Whole(state) => Ok(View::Whole(state.snapshot()?)),
            Store::Receiving(receiving) => {
                let (blocks, file) = receiving.blocks();
                // A chain with no state has no last block but its first.
                let first = blocks.at(file, 0)?.ok_or(Error::Receiving)?;
                Ok(View::Receiving { blocks, file, first })
            }
            Store::Gone => Err(Error::Receiving),
        }
    }
}

/// The blocks known of, as they were at one moment.
///
/// (The whole state's view is some 1,250 bytes where the other is 48:
/// one is made for a call and let go with it, so it is left as it is.)
#[allow(clippy::large_enum_variant)]
pub(crate) enum View<'a, B: Backend + 'static> {
    Whole(Snapshot<'a, B>),
    Receiving { blocks: &'a Blocks, file: &'a PageFile<B>, first: Digest },
}

impl<B: Backend + 'static> View<'_, B> {
    /// What reads the pages the blocks are kept in.
    pub(crate) fn pages(&self) -> &Self {
        self
    }

    pub(crate) fn blocks(&self) -> &Blocks {
        match self {
            View::Whole(snap) => snap.blocks(),
            View::Receiving { blocks, .. } => blocks,
        }
    }

    /// The chain's last block: its height and id. While a state is
    /// received, the first block.
    pub(crate) fn tip(&self) -> (u32, Digest) {
        match self {
            View::Whole(snap) => snap.tip(),
            View::Receiving { first, .. } => (0, *first),
        }
    }
}

impl<B: Backend + 'static> ReadPages for View<'_, B> {
    fn read_page<'b>(&self, e: Extent, buf: &'b mut [u8]) -> std::io::Result<&'b [u8]> {
        match self {
            View::Whole(snap) => snap.pages().read_page(e, buf),
            View::Receiving { file, .. } => file.read_page(e, buf),
        }
    }
}

/// A chain's state, held to be read: while it is, the state is not
/// given up for another.
pub struct StateRef<'a, B: Backend + 'static>(Held<'a, B>);

/// A chain's store, held to be read.
///
/// A thread holds it once. To take it again while holding it (to ask
/// the chain for something while holding its state, say) waits for ever
/// on anyone who came to write between the two: the writer waits for
/// the first to be let go of, and the second waits behind the writer.
/// Nothing of that shows until a writer comes at that moment, so a
/// build with debug assertions refuses the second taking outright.
pub(crate) struct Held<'a, B: Backend + 'static> {
    guard: RwLockReadGuard<'a, Store<B>>,
    _once: Once,
}

impl<B: Backend + 'static> std::ops::Deref for Held<'_, B> {
    type Target = Store<B>;

    fn deref(&self) -> &Store<B> {
        &self.guard
    }
}

/// That this thread holds a store, by where the store is: for as long
/// as this lives. Nothing, without debug assertions.
struct Once(#[cfg(debug_assertions)] usize);

#[cfg(debug_assertions)]
thread_local! {
    static HELD: std::cell::RefCell<Vec<usize>> = const { std::cell::RefCell::new(Vec::new()) };
}

impl Once {
    #[cfg(debug_assertions)]
    fn taking(store: usize) -> Once {
        HELD.with(|held| {
            let mut held = held.borrow_mut();
            assert!(!held.contains(&store), "a chain's store is taken to be read by a thread that holds it already");
            held.push(store);
        });
        Once(store)
    }

    #[cfg(not(debug_assertions))]
    fn taking(_: usize) -> Once {
        Once()
    }
}

#[cfg(debug_assertions)]
impl Drop for Once {
    fn drop(&mut self) {
        HELD.with(|held| {
            let mut held = held.borrow_mut();
            if let Some(at) = held.iter().rposition(|s| *s == self.0) {
                held.swap_remove(at);
            }
        });
    }
}

impl<B: Backend + 'static> std::ops::Deref for StateRef<'_, B> {
    type Target = State<B>;

    fn deref(&self) -> &State<B> {
        match &*self.0 {
            Store::Whole(state) => state,
            _ => unreachable!("made of a whole state"),
        }
    }
}

#[cfg(test)]
impl<V> Chain<crate::store::testing::MemBackend, V> {
    /// How many times the store has been read from, for the tests.
    pub(crate) fn store_reads(&self) -> u64 {
        match &*self.store() {
            Store::Whole(state) => state.file().backend().reads(),
            _ => 0,
        }
    }
}
