//! Making blocks: the block after the chain's last is built, proven,
//! and its proof of work found.
//!
//! [`mine`] makes one block and hands it back whole; whoever runs it
//! gives the block to the node, which applies it and tells its peers.
//! Nothing here knows of the network.
//!
//! A block made here pays its reward to one key, with the fees of the
//! transactions it carries: those chosen for it from the pool
//! ([`choose`]), no more of them than the miner is to prove.
//!
//! A block's proof is the chain's ([`crate::prover`]): it builds on the
//! proof the block before carried, which is in that block's body, kept,
//! and on what that proof states, made again from that body and the
//! state.
//!
//! The steps, each given up if `cancel` says so (the chain has another
//! last block, or the node is stopping):
//!
//! 1. The reward's output, and the witnesses of it and of the
//!    transactions chosen, against the state as it is.
//! 2. The block's proof: what takes the time.
//! 3. The header, and a nonce whose hash meets the target: on every
//!    thread there is, each trying its own nonces.

use std::sync::Mutex;
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::time::{Duration, Instant};

use crate::block::{Block, Body, BodyRef, HEADER_SIZE, Header};
use crate::chain::Chain;
use crate::chain::verify::{BlockStatement, ProofVerifier};
use crate::difficulty::Target;
use crate::error::Error;
use crate::hash::{Digest, EMPTY};
use crate::ledger::Record;
use crate::mempool::{Mempool, PROOF_BYTES};
use crate::output::Output;
use crate::pow::{ItemSource, LazyDataset, Nonce, hashimoto, nonce_from_u64};
use crate::prover::{ChainVerifier, Contents, Setup, Signing};
use crate::proving::witness_of;
use crate::store::backend::Backend;
use crate::transaction::Transaction;

/// Signatures a block made here checks at the most, unless told
/// otherwise: one for each input of its transactions (a policy input
/// may be several). Some hundred transactions: what a machine with
/// nothing but its processor proves in a few times what a block of
/// nothing takes it. The block's size allows many times as many, which
/// is for those who prove on many machines.
pub const MAX_SIGNATURES: usize = 256;

/// Whether to make blocks now, or to wait for a chain ahead of ours to
/// come in ([`HoldOff::ask`]).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Now {
    /// Make blocks.
    Mine,
    /// Wait: `first` when this is the first time of asking that it is
    /// so, of this chain ahead.
    Wait { first: bool },
    /// Make blocks though a chain ahead is known of: its blocks have
    /// not come in the time allowed. `first` as above.
    MineAnyway { first: bool },
}

/// When a node that knows of a chain ahead of its own stops making
/// blocks, and for how long.
///
/// A block made on a chain about to be replaced is work thrown away,
/// so a node well behind waits. But a node that waits for ever for
/// blocks that do not come makes none: so it waits only so long for
/// the blocks of any one chain ahead (by its last header), and then
/// goes on making its own until a chain ahead with another last header
/// is known of. Waiting wrongly costs the network a miner; making
/// blocks wrongly costs the miner its own work, and no one else
/// anything.
pub struct HoldOff {
    /// How long the blocks of a chain ahead are waited for.
    limit: Duration,
    /// The chain ahead being waited for, by its last header, and since
    /// when.
    waiting: Option<(Digest, Instant)>,
    /// The chain ahead that was waited for long enough.
    given_up: Option<Digest>,
}

impl HoldOff {
    /// For a network whose blocks are `block_time` seconds apart: three
    /// blocks' time is waited, ten seconds at the least.
    pub fn new(block_time: u64) -> HoldOff {
        HoldOff { limit: Duration::from_secs((3 * block_time).max(10)), waiting: None, given_up: None }
    }

    pub fn limit(&self) -> Duration {
        self.limit
    }

    /// What to do at `now`, where the best chain known of that is two
    /// blocks or more ahead of ours ends in the header `ahead`: none,
    /// if there is none.
    pub fn ask(&mut self, ahead: Option<Digest>, now: Instant) -> Now {
        let Some(ahead) = ahead else {
            (self.waiting, self.given_up) = (None, None);
            return Now::Mine;
        };
        if self.given_up == Some(ahead) {
            return Now::MineAnyway { first: false };
        }
        match self.waiting {
            Some((chain, since)) if chain == ahead => {
                if now.duration_since(since) < self.limit {
                    return Now::Wait { first: false };
                }
                (self.waiting, self.given_up) = (None, Some(ahead));
                Now::MineAnyway { first: true }
            }
            _ => {
                self.waiting = Some((ahead, now));
                Now::Wait { first: true }
            }
        }
    }
}

/// Fills what is missing of `table`, on every thread there is, and says
/// how far it has got: `progress` is called with each twentieth of the
/// table that has come to be there (5, 10, ... 95 in a hundred), as
/// that is seen, the table being looked at every `look`. A table
/// filled faster than it is looked at passes some of them by.
pub fn fill_table(table: &LazyDataset<'_>, look: Duration, progress: &(dyn Fn(u32) + Sync)) {
    let twentieths = || (table.filled() * 20 / table.pairs()) as u32;
    let done = AtomicBool::new(false);
    std::thread::scope(|scope| {
        scope.spawn(|| {
            table.fill();
            done.store(true, Ordering::Release);
        });
        let mut said = twentieths();
        while !done.load(Ordering::Acquire) {
            std::thread::sleep(look);
            let now = twentieths();
            if now > said && now < 20 {
                said = now;
                progress(5 * now);
            }
        }
    });
}

/// What came of trying to make a block.
///
/// (A block made carries its header, and so is some 300 bytes where
/// the others are none: one is made for a try and let go with it, so
/// it is left as it is.)
#[allow(clippy::large_enum_variant)]
#[derive(Debug)]
pub enum Mined {
    /// The block, whole: with how long proving it took, and how many
    /// hashes finding its nonce took and how long.
    Block { block: Vec<u8>, header: Header, proved: Duration, hashes: u64, solved: Duration },
    /// Given up: `cancel` said so.
    Cancelled,
    /// A transaction chosen for the block no longer applies: the state
    /// has changed since it was chosen, and the pool has not yet been
    /// looked over. To be tried again, with what is chosen then.
    Stale,
    /// The chain has had its last block: there is none to make.
    Finished,
}

/// The transactions of the pool for the block after `chain`'s last,
/// and the commits of names past their time that it is to sweep.
///
/// The longest waiting first, a tenth of the block, and then the best
/// paying for their weight ([`Mempool::select`]), while the block
/// checks no more than `max_signatures` signatures (nor more than the
/// proofs of one block hold), its transactions are one run's, and it is
/// no larger than a block may be. `with_pool` gives the pool, held
/// while they are chosen: the state is taken first, as by everyone
/// that takes both.
#[allow(clippy::type_complexity)]
pub fn choose<B: Backend + 'static>(
    chain: &Chain<B, ChainVerifier>,
    setup: &Setup,
    with_pool: &dyn Fn(&mut dyn FnMut(&Mempool)),
    max_signatures: usize,
) -> Result<(Vec<Transaction>, Vec<u64>), Error> {
    let params = *chain.params();
    let state = chain.whole()?;
    let snap = state.snapshot()?;
    let height = snap.tip().0 + 1;
    let sweeps = Mempool::sweeps(&snap, height);
    let mut chosen: Vec<Transaction> = Vec::new();
    let most = max_signatures.min(setup.level.signatures());
    if most == 0 {
        return Ok((chosen, sweeps));
    }
    with_pool(&mut |pool: &Mempool| {
        // (What is chosen so far, decoded once: the choosing asks of
        // all of it each time one more is tried.)
        let mut so_far: Vec<Transaction> = Vec::new();
        let reserve = most * crate::output::INPUT_SIZE * pool.policy().reserve_percent / 100;
        let taken = pool.select(&snap, height, params.min_reveal, reserve, |trying| {
            so_far.truncate(trying.len() - 1);
            so_far.push(trying[trying.len() - 1].to_transaction());
            if so_far.iter().map(Transaction::weight).sum::<usize>() > most {
                return false;
            }
            let ops = || so_far.iter().flat_map(|tx| tx.ops.iter());
            let spends: usize = so_far.iter().map(|tx| tx.inputs.len() + tx.policy_inputs.len()).sum();
            let makes = 1 + so_far.iter().map(|tx| tx.outputs.len()).sum::<usize>();
            let names =
                ops().map(|op| op.block_op().size()).sum::<usize>() + sweeps.len() * crate::codec::POSITION_BYTES;
            if HEADER_SIZE + Body::size_of(spends, makes, names, PROOF_BYTES) > params.max_block_size {
                return false;
            }
            setup.fits(snap.outputs().next, &so_far, sweeps.len())
        });
        chosen = taken.iter().map(|tx| tx.to_transaction()).collect();
    });
    Ok((chosen, sweeps))
}

/// What the block after `chain`'s last is to pay whoever makes it, if
/// it carries the transactions `pooled`: its height, and what it may
/// make with their fees. None if the chain has had its last block.
pub fn reward_due<B: Backend + 'static, V>(
    chain: &Chain<B, V>,
    pooled: &[Transaction],
) -> Result<Option<(u32, u64)>, Error> {
    let height = chain.tip()?.height + 1;
    let subsidy = chain.params().subsidy(height);
    let fees: u64 = pooled.iter().map(|tx| tx.balance().clamp(0, u64::MAX as i128) as u64).sum();
    Ok((subsidy > 0).then_some((height, subsidy.saturating_add(fees))))
}

/// [`mine_with`], of a block that carries nothing but its reward, paid
/// to the key of hash `reward`.
#[allow(clippy::too_many_arguments)]
pub fn mine<B: Backend + 'static, S: ItemSource + Sync>(
    chain: &Chain<B, ChainVerifier>,
    setup: &Setup,
    dataset: &S,
    reward: &Digest,
    unix: u64,
    start: u64,
    proved: &dyn Fn(Duration),
    cancel: &(dyn Fn() -> bool + Sync),
) -> Result<Mined, Error> {
    let Some((_, due)) = reward_due(chain, &[])? else { return Ok(Mined::Finished) };
    mine_with(chain, setup, dataset, &Output::to_key_hash(reward, due), unix, start, &[], &[], proved, cancel)
}

/// The chain's proof the block of `tip` carried, as the proof before
/// the next block's: where a chain begins, before the first.
fn before<B: Backend + 'static>(
    chain: &Chain<B, ChainVerifier>,
    setup: &Setup,
    tip: &Header,
    roots: &(Digest, Digest),
    next: u64,
) -> Result<crate::prover::Before, Error> {
    if tip.height == 0 {
        return Ok(setup.beginning());
    }
    let bytes = chain.body(&tip.hash())?.ok_or(Error::BadProof)?;
    let body = BodyRef::from_bytes(&bytes)?;
    let stated = chain.statement(tip.height, &tip.prev_hash, &body, roots, next);
    // (A proof before that this build does not take is not built on:
    // the block's own could not be made, and is not tried.)
    if stated.digest() != tip.statement {
        return Err(Error::BadProof);
    }
    setup.carried(body.proof(), &stated).ok_or(Error::BadProof)
}

/// Whether the proof of `chain`'s last block is one this build takes:
/// true where there is none to hold (the first block, a block whose
/// body is not kept).
///
/// A block's proof builds on the proof of the block before, and says
/// so in a program that is the network's rules: its circuits, and the
/// numbers in them. A chain made by a build of other rules has proofs
/// this build's blocks cannot build on, and it would not take that
/// chain's blocks from a peer either. Such a chain is not to be gone on
/// with: whoever starts a node on one is told, before anything is made.
pub fn last_proof_holds<B: Backend + 'static>(chain: &Chain<B, ChainVerifier>) -> Result<bool, Error> {
    let tip = chain.tip()?;
    if tip.height == 0 || chain.verifier().is_unchecked() {
        return Ok(true);
    }
    let Some(bytes) = chain.body(&tip.hash())? else { return Ok(true) };
    let body = BodyRef::from_bytes(&bytes)?;
    let state = chain.whole()?;
    let snap = state.snapshot()?;
    let roots = (snap.outputs().hash(), snap.names().hash());
    let stated = chain.statement(tip.height, &tip.prev_hash, &body, &roots, snap.outputs().next);
    let statement = BlockStatement { chain: stated, digest: stated.digest(), body };
    Ok(stated.digest() == tip.statement && chain.verifier().verify(&statement, body.proof()))
}

/// Makes the block after `chain`'s last, of the transactions `pooled`
/// and sweeping the commits at `sweeps` ([`choose`]), paying its reward
/// and their fees ([`reward_due`]) by the output `paid`, which is the
/// maker's own. `unix` is the time by the calendar, in seconds,
/// and `start` where the nonces tried begin (any number: so that two
/// miners do not try the same). `proved` is called when the block's
/// proof is made, with how long that took: from then the nonce is
/// looked for. `cancel` is asked now and then whether to give up.
///
/// `dataset` is the table of the proof of work for that block's
/// height, which is the table of the header before's wherever the two
/// are of one epoch: whole, or one that fills as it is read
/// ([`crate::pow::LazyDataset`]).
#[allow(clippy::too_many_arguments)]
pub fn mine_with<B: Backend + 'static, S: ItemSource + Sync>(
    chain: &Chain<B, ChainVerifier>,
    setup: &Setup,
    dataset: &S,
    paid: &Output,
    unix: u64,
    start: u64,
    pooled: &[Transaction],
    sweeps: &[u64],
    proved: &dyn Fn(Duration),
    cancel: &(dyn Fn() -> bool + Sync),
) -> Result<Mined, Error> {
    let params = *chain.params();
    let tip = chain.tip()?;
    let height = tip.height + 1;
    let subsidy = params.subsidy(height);
    if subsidy == 0 {
        return Ok(Mined::Finished);
    }
    // The reward pays what the block may make and what its
    // transactions leave: an output made for another block's is not
    // this block's.
    let fees: u64 = pooled.iter().map(|tx| tx.balance().clamp(0, u64::MAX as i128) as u64).sum();
    if paid.amount != subsidy.saturating_add(fees) {
        return Ok(Mined::Stale);
    }
    let began = Instant::now();
    let state = chain.whole()?;
    let (witness, start_at, roots, next) = {
        let snap = state.snapshot()?;
        // (The state of the block being built on, or it has moved on.)
        // (The state before the first block is of no block.)
        let (at, id) = snap.tip();
        if at != tip.height || (at > 0 && id != tip.hash()) {
            return Ok(Mined::Cancelled);
        }
        let witness = match witness_of(&snap, pooled, sweeps) {
            Ok(witness) => witness,
            // What a transaction of the pool spends is not there.
            Err(Error::NoSuchOutput(_)) if !pooled.is_empty() || !sweeps.is_empty() => return Ok(Mined::Stale),
            Err(e) => return Err(e),
        };
        let (roots, next) = ((snap.outputs().hash(), snap.names().hash()), snap.outputs().next);
        let record = Record {
            root: [roots.0; 2],
            inputs: [EMPTY; 2],
            outputs: [EMPTY; 2],
            next: [next; 2],
            sum_in: subsidy as u128,
            sum_out: 0,
            height,
            names: [roots.1; 2],
            ops: [EMPTY; 2],
            done: [EMPTY; 2],
        };
        (witness, record, roots, next)
    };
    drop(state);
    // (Asked of the chain once its state is let go of: to ask the
    // chain while holding its state is to take what keeps it twice,
    // which waits for ever on anyone waiting to write between the
    // two.)
    let chained = before(chain, setup, &tip, &roots, next)?;
    // The body, without its proof: what the header is of, and what the
    // proof is to state.
    let mut body = Body {
        inputs: pooled.iter().flat_map(|tx| tx.spent_positions()).collect(),
        outputs: [paid].into_iter().chain(pooled.iter().flat_map(|tx| &tx.outputs)).map(Output::block_output).collect(),
        ops: pooled.iter().flat_map(|tx| &tx.ops).map(|op| op.block_op()).collect(),
        sweeps: sweeps.to_vec(),
        proof: vec![],
    };
    let unproven = body.to_bytes();
    let (state_root, stated) = match chain.header_after(&BodyRef::from_bytes(&unproven)?) {
        Ok(after) => after,
        // The chain has gone on meanwhile: what this block was made of
        // is no longer what the chain holds, and that is no fault. Nor
        // is a name taken, or a commit out of its window: the pool has
        // not yet been looked over.
        Err(Error::Io(kind)) => return Err(Error::Io(kind)),
        Err(_) => return Ok(Mined::Stale),
    };
    // The signatures, proven; and the block's proof on the proof before.
    let signings: Vec<Signing> = pooled.iter().flat_map(Transaction::signings).collect();
    let signed = match signings.is_empty() {
        true => None,
        false => match setup.sign(&signings) {
            Some(signed) => Some(signed),
            None => return Ok(Mined::Stale),
        },
    };
    if cancel() {
        return Ok(Mined::Cancelled);
    }
    let contents = Contents { txs: pooled, sweeps, reward: paid };
    let Some(proof) = setup.block(dataset, &tip, &chained, &start_at, witness, &contents, signed.as_ref()) else {
        return Ok(Mined::Stale);
    };
    // The chain may have another last block by now, heard of while the
    // proof was made: then this block is for nothing.
    if cancel() {
        return Ok(Mined::Cancelled);
    }
    body.proof = proof;
    // (What was proven is what the chain will ask of the block.)
    let whole = body.to_bytes();
    let statement = BlockStatement { chain: stated, digest: stated.digest(), body: BodyRef::from_bytes(&whole)? };
    if !chain.verifier().verify(&statement, &body.proof) {
        return Err(Error::BadProof);
    }
    let took = began.elapsed();
    // The proof is made: what is left is to find the nonce.
    proved(took);
    let header = Header {
        prev_hash: tip.hash(),
        height,
        timestamp: unix.max(chain.earliest_timestamp(&tip)?),
        body_commitment: body.commitment(),
        state_root,
        statement: stated.digest(),
        aux: chain.aux_root()?,
        mix: tip.mix,
        nonce: [0; 32],
    };
    let target = chain.expected_target(&tip)?;
    let began = Instant::now();
    let Some((nonce, mix, hashes)) = solve(dataset, &header.pow_hash(), &target, start, cancel) else {
        return Ok(Mined::Cancelled);
    };
    let header = Header { nonce, mix, ..header };
    let solved = began.elapsed();
    Ok(Mined::Block { block: Block { header, body }.to_bytes(), header, proved: took, hashes, solved })
}

/// Debugging only: how many outputs and spends of those asked for a
/// block of `max_block_size` holds, with its reward and room for a
/// proof: both less in the same measure, where they do not fit.
#[cfg(feature = "dev")]
pub fn fill_plan(max_block_size: usize, outputs: usize, spends: usize) -> (usize, usize) {
    use crate::output::BLOCK_OUTPUT_SIZE;
    let space = max_block_size.saturating_sub(HEADER_SIZE + Body::size_of(0, 1, 0, PROOF_BYTES));
    let asked = spends * crate::codec::POSITION_BYTES + outputs * BLOCK_OUTPUT_SIZE;
    match asked > space {
        true => (outputs * space / asked, spends * space / asked),
        false => (outputs, spends),
    }
}

/// Debugging only: makes the block after `chain`'s last without proving
/// it, where proofs go unchecked: of `outputs` outputs nobody is paid
/// by (each of one unit), and `spends` spends, chosen at random, of the
/// outputs the chain began with (`filled`: how many, and how far
/// apart), with a stand-in the size of a proof. `paid` is the reward:
/// what the block may make, less a unit for each of the outputs.
/// `said` is told what the block is and how long building it took.
#[cfg(feature = "dev")]
#[allow(clippy::too_many_arguments)]
pub fn mine_filled<B: Backend + 'static, S: ItemSource + Sync>(
    chain: &Chain<B, ChainVerifier>,
    dataset: &S,
    paid: &Output,
    unix: u64,
    start: u64,
    outputs: usize,
    spends: usize,
    filled: Option<(u64, u64)>,
    said: &dyn Fn(&str),
    cancel: &(dyn Fn() -> bool + Sync),
) -> Result<Mined, Error> {
    use crate::output::BlockOutput;
    let began = Instant::now();
    let params = *chain.params();
    let tip = chain.tip()?;
    let height = tip.height + 1;
    let subsidy = params.subsidy(height);
    if subsidy == 0 {
        return Ok(Mined::Finished);
    }
    if paid.amount.checked_add(outputs as u64) != Some(subsidy) {
        return Ok(Mined::Stale);
    }
    // (splitmix64, from the system's own randomness.)
    let mut seed = [0u8; 8];
    crate::random::fill(&mut seed)?;
    let mut x = u64::from_le_bytes(seed);
    let mut next = || {
        x = x.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = x;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        z ^ (z >> 31)
    };
    // What it spends: outputs the chain began with that are still
    // unspent, each once.
    let mut picked: Vec<u64> = Vec::with_capacity(spends);
    if let Some((n, spacing)) = filled.filter(|(n, _)| *n > 0) {
        let state = chain.whole()?;
        let snap = state.snapshot()?;
        let (at, id) = snap.tip();
        if at != tip.height || (at > 0 && id != tip.hash()) {
            return Ok(Mined::Cancelled);
        }
        let mut seen = std::collections::HashSet::with_capacity(spends);
        for _ in 0..4 * spends {
            if picked.len() == spends {
                break;
            }
            let position = (next() % n) * spacing;
            if seen.insert(position) && snap.is_unspent(position)? {
                picked.push(position);
            }
        }
    }
    picked.sort_unstable();
    let mut made = vec![paid.block_output()];
    made.extend((0..outputs).map(|_| BlockOutput {
        commitment: core::array::from_fn(|_| next() as u8),
        memo: core::array::from_fn(|_| next() as u8),
        amount: 1,
    }));
    let spent = picked.len();
    let body = Body { inputs: picked, outputs: made, proof: vec![0u8; PROOF_BYTES], ..Default::default() };
    let bytes = body.to_bytes();
    let (state_root, stated) = match chain.header_after(&BodyRef::from_bytes(&bytes)?) {
        Ok(after) => after,
        // The chain has gone on meanwhile, and spent what was chosen.
        Err(_) if chain.tip()?.hash() != tip.hash() => return Ok(Mined::Stale),
        Err(e) => return Err(e),
    };
    if cancel() {
        return Ok(Mined::Cancelled);
    }
    let took = began.elapsed();
    said(&format!(
        "debug fill: block {height}: {outputs} outputs, {spent} spends, {} bytes, built in {:.2}s",
        HEADER_SIZE + bytes.len(),
        took.as_secs_f64()
    ));
    let header = Header {
        prev_hash: tip.hash(),
        height,
        timestamp: unix.max(chain.earliest_timestamp(&tip)?),
        body_commitment: body.commitment(),
        state_root,
        statement: stated.digest(),
        aux: chain.aux_root()?,
        mix: tip.mix,
        nonce: [0; 32],
    };
    let target = chain.expected_target(&tip)?;
    let began = Instant::now();
    let Some((nonce, mix, hashes)) = solve(dataset, &header.pow_hash(), &target, start, cancel) else {
        return Ok(Mined::Cancelled);
    };
    let header = Header { nonce, mix, ..header };
    let solved = began.elapsed();
    Ok(Mined::Block { block: Block { header, body }.to_bytes(), header, proved: took, hashes, solved })
}

/// The last blocks of a chain made long without a table whose work is
/// done ([`extend_empty`]): more than a node joining it checks in full.
#[cfg(feature = "dev")]
pub const WORKED: u32 = 16;

/// Debugging only: makes `chain`, whose blocks' proofs go unchecked,
/// `blocks` blocks long, of blocks that are empty but for what each
/// pays (to nobody) and carry no proof: a chain as long as one that has
/// run for years, made in minutes, for trying how a node takes its
/// headers. Their times are `spacing` seconds apart from the first
/// block's, which on a dev network is far more than its blocks are
/// meant to be: so each asks for the least work there is. `unix` is
/// the time now, which no block's time may be ahead of; `progress` is
/// told, now and then, how long the chain is.
///
/// With a table (`dataset`) every block's work is done. Without one a
/// block's work is tens of milliseconds a try, from the seed's text,
/// and a year of blocks most of a day: so only the first and the last
/// [`WORKED`] have their work done, and the rest claim work they have
/// not, in a header
/// that is otherwise what it should be; the chain is told to take
/// their word while they are made ([`Chain::debug_trust_work`]). To a
/// node that takes them as headers, leaving their work to a proof, and
/// checks in full only the last few, they are what any chain's are.
#[cfg(feature = "dev")]
#[allow(clippy::too_many_arguments)]
pub fn extend_empty<B: Backend + 'static>(
    chain: &Chain<B, ChainVerifier>,
    seed: &crate::pow::SeedText<'_>,
    dataset: Option<&crate::pow::Dataset<'_>>,
    blocks: u32,
    spacing: u64,
    unix: u64,
    progress: &dyn Fn(u32),
) -> Result<(), Error> {
    use crate::output::BlockOutput;
    let params = *chain.params();
    loop {
        let tip = chain.tip()?;
        let height = tip.height + 1;
        if height > blocks || params.subsidy(height) == 0 {
            return Ok(());
        }
        // (An output like no other: its commitment is its height.)
        let mut commitment = [0x0e; 32];
        commitment[..4].copy_from_slice(&height.to_le_bytes());
        let paid = BlockOutput { commitment, memo: Default::default(), amount: params.subsidy(height) };
        let body = Body { outputs: vec![paid], ..Default::default() };
        let bytes = body.to_bytes();
        let (state_root, stated) = chain.header_after(&BodyRef::from_bytes(&bytes)?)?;
        let timestamp = (params.genesis_timestamp + height as u64 * spacing).max(chain.earliest_timestamp(&tip)?);
        let header = Header {
            prev_hash: tip.hash(),
            height,
            timestamp: timestamp.min(unix),
            body_commitment: body.commitment(),
            state_root,
            statement: stated.digest(),
            aux: chain.aux_root()?,
            mix: tip.mix,
            nonce: [0; 32],
        };
        let target = chain.expected_target(&tip)?;
        // (The first of them too: a node checks in full the work of the
        // headers nearest its own last block, which for a new node are
        // the chain's first.)
        let worked = dataset.is_some() || height <= WORKED || height + WORKED > blocks;
        chain.debug_trust_work(!worked);
        let found = match (dataset, worked) {
            (Some(table), _) => solve(table, &header.pow_hash(), &target, height as u64, &|| false),
            (None, true) => solve(&seed.at(height as u64), &header.pow_hash(), &target, height as u64, &|| false),
            // The first nonce whose claim, of a mix of nothing, meets
            // the target.
            (None, false) => {
                let mut claimed = Header { mix: EMPTY, ..header };
                let mut tried = 0u64;
                loop {
                    claimed.nonce = nonce_from_u64(tried);
                    if claimed.quick_pow_check(&target) {
                        break Some((claimed.nonce, claimed.mix, tried));
                    }
                    tried += 1;
                }
            }
        };
        let Some((nonce, mix, _)) = found else {
            chain.debug_trust_work(false);
            return Ok(());
        };
        let block = Block { header: Header { nonce, mix, ..header }, body }.to_bytes();
        let applied = chain.apply_block(&crate::block::BlockRef::from_bytes(&block)?, unix);
        chain.debug_trust_work(false);
        applied?;
        if height.is_multiple_of(5000) {
            progress(height);
        }
    }
}

/// A nonce whose hash with `header_hash` meets `target`, with the mix
/// that goes in the header beside it, and how many were tried: on
/// every thread there is, the nonces from `start` dealt out among
/// them. None if `cancel` said to give up first.
pub fn solve<S: ItemSource + Sync>(
    dataset: &S,
    header_hash: &Digest,
    target: &Target,
    start: u64,
    cancel: &(dyn Fn() -> bool + Sync),
) -> Option<(Nonce, Digest, u64)> {
    let threads = crate::parallel::threads() as u64;
    let (done, tried) = (AtomicBool::new(false), AtomicU64::new(0));
    let found = Mutex::new(None);
    std::thread::scope(|scope| {
        for t in 0..threads {
            let (done, tried, found) = (&done, &tried, &found);
            scope.spawn(move || {
                let (mut n, mut mine) = (start.wrapping_add(t), 0u64);
                while !done.load(Ordering::Relaxed) {
                    let nonce = nonce_from_u64(n);
                    let out = hashimoto(dataset, header_hash, &nonce);
                    mine += 1;
                    if target.is_met_by(&out.result) && !done.swap(true, Ordering::Relaxed) {
                        *found.lock().unwrap_or_else(|e| e.into_inner()) = Some((nonce, out.mix));
                    }
                    // (One of them asks, and not at every hash.)
                    if t == 0 && mine.is_multiple_of(64) && cancel() {
                        done.store(true, Ordering::Relaxed);
                    }
                    n = n.wrapping_add(threads);
                }
                tried.fetch_add(mine, Ordering::Relaxed);
            });
        }
    });
    let (nonce, mix) = found.into_inner().unwrap_or_else(|e| e.into_inner())?;
    Some((nonce, mix, tried.into_inner()))
}

#[cfg(test)]
mod hold_off {
    use super::*;

    /// A table is filled whole, and how far it has got is said in
    /// twentieths, each once and in order, none of them the last.
    #[test]
    fn a_table_is_filled_and_says_how_far_it_has_got() {
        let seed = crate::pow::SeedText::new(crate::pow::PowParams {
            log_dataset_items: 12,
            max_log_dataset_items: 12,
            ..crate::pow::PowParams::MAINNET
        });
        let table = LazyDataset::new(&seed, 12).unwrap();
        let said = Mutex::new(Vec::new());
        fill_table(&table, Duration::from_micros(200), &|percent| said.lock().unwrap().push(percent));
        assert!(table.is_complete());
        let said = said.into_inner().unwrap();
        assert!(said.windows(2).all(|w| w[0] < w[1]), "{said:?}");
        assert!(said.iter().all(|p| p % 5 == 0 && (5..=95).contains(p)), "{said:?}");
        // Whole already: nothing to fill, nothing to say.
        fill_table(&table, Duration::from_micros(200), &|_| panic!("nothing was to be said"));
    }

    /// A chain ahead is waited for so long, and no longer; another
    /// chain ahead is waited for afresh; and with none ahead, blocks
    /// are made.
    #[test]
    fn a_chain_ahead_is_waited_for_so_long_and_no_longer() {
        let chain = |n: u32| -> Digest { [n as u8; 32] };
        let mut hold = HoldOff::new(600);
        assert_eq!(hold.limit(), Duration::from_secs(1800));
        assert_eq!(HoldOff::new(1).limit(), Duration::from_secs(10));
        let t = Instant::now();
        let at = |seconds: u64| t + Duration::from_secs(seconds);
        assert_eq!(hold.ask(None, at(0)), Now::Mine);
        // A chain ahead: waited for, until the time allowed is up.
        assert_eq!(hold.ask(Some(chain(1)), at(10)), Now::Wait { first: true });
        assert_eq!(hold.ask(Some(chain(1)), at(1000)), Now::Wait { first: false });
        assert_eq!(hold.ask(Some(chain(1)), at(1809)), Now::Wait { first: false });
        assert_eq!(hold.ask(Some(chain(1)), at(1810)), Now::MineAnyway { first: true });
        // From then on blocks are made, however long it stays ahead.
        assert_eq!(hold.ask(Some(chain(1)), at(1811)), Now::MineAnyway { first: false });
        assert_eq!(hold.ask(Some(chain(1)), at(99_999)), Now::MineAnyway { first: false });
        // It grows (another last header): that is news, and waited for.
        assert_eq!(hold.ask(Some(chain(2)), at(100_000)), Now::Wait { first: true });
        assert_eq!(hold.ask(Some(chain(2)), at(100_500)), Now::Wait { first: false });
        // Its blocks come: nothing is ahead, and blocks are made.
        assert_eq!(hold.ask(None, at(100_600)), Now::Mine);
        // The same chain ahead again later is waited for again.
        assert_eq!(hold.ask(Some(chain(2)), at(100_700)), Now::Wait { first: true });
        // A chain ahead that keeps growing is waited for each time it
        // does, the time allowed counted from when it last did.
        assert_eq!(hold.ask(Some(chain(3)), at(102_000)), Now::Wait { first: true });
        assert_eq!(hold.ask(Some(chain(3)), at(103_700)), Now::Wait { first: false });
        assert_eq!(hold.ask(Some(chain(3)), at(103_800)), Now::MineAnyway { first: true });
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::block::BlockRef;
    use crate::chain::apply::Applied;
    use crate::chain::headers::tests::{NOW, seed, table};
    use crate::proving::tests::network;
    use crate::store::testing::MemBackend;
    use crate::transaction::UnsignedTransaction;

    /// Blocks made here join the chain: one of its reward alone, built
    /// on where a chain begins; one that carries what was chosen for it
    /// from the pool and pays its fee with the reward, built on the
    /// first's proof. And a block is given up when told, or when what
    /// it was to carry is spent.
    #[test]
    #[cfg_attr(debug_assertions, ignore = "proves blocks; run with --release")]
    fn blocks_made_here_join_the_chain() {
        let (setup, params) = network();
        let chain = Chain::open(MemBackend::new(), 8, params, seed(), setup.verifier()).unwrap();
        chain.set_dataset(table());
        let dataset = &*table();
        let mut key = crate::xmss::SecretKey::generate(&[5; 32]);
        let reward = crate::output::pubkey_hash(&key.public_key());
        // Told to give up before it begins, it does.
        assert!(matches!(mine(&chain, setup, dataset, &reward, NOW, 0, &|_| {}, &|| true).unwrap(), Mined::Cancelled));
        let said = std::sync::atomic::AtomicU64::new(0);
        let made =
            mine(&chain, setup, dataset, &reward, NOW, 3, &|_| _ = said.fetch_add(1, Ordering::Relaxed), &|| false);
        let Mined::Block { block, header, .. } = made.unwrap() else { panic!("no block") };
        assert_eq!(said.load(Ordering::Relaxed), 1);
        assert_eq!(chain.apply_block(&BlockRef::from_bytes(&block).unwrap(), NOW), Ok(Applied::Extended));
        assert_eq!((chain.tip().unwrap(), header.height), (header, 1));

        // The second carries a spend of the first's reward, all but a
        // fee, back to the key.
        let (paid, fee) = (params.subsidy(1), 1_000_000);
        let mut pool = Mempool::new(1 << 20);
        {
            let state = chain.whole().unwrap();
            let snap = state.snapshot().unwrap();
            let tx = UnsignedTransaction::new(
                vec![(key.public_key(), paid)],
                vec![Output::new(&key.public_key(), paid - fee)],
            )
            .at(&[0])
            .sign(|_, _, m| key.sign(m))
            .unwrap();
            pool.insert(&tx.to_bytes(), &snap, 2, NOW).unwrap();
        }
        // Nothing is chosen for a miner that is to prove no signatures.
        assert!(choose(&chain, setup, &|f| f(&pool), 0).unwrap().0.is_empty());
        let (pooled, sweeps) = choose(&chain, setup, &|f| f(&pool), MAX_SIGNATURES).unwrap();
        assert_eq!((pooled.len(), sweeps.len()), (1, 0));
        let due = reward_due(&chain, &pooled).unwrap().unwrap();
        assert_eq!(due, (2, params.subsidy(2) + fee));
        let pay = Output::to_key_hash(&reward, due.1);
        let made = mine_with(&chain, setup, dataset, &pay, NOW, 7, &pooled, &sweeps, &|_| {}, &|| false).unwrap();
        let Mined::Block { block, .. } = made else { panic!("{made:?}") };
        let view = BlockRef::from_bytes(&block).unwrap();
        assert_eq!(chain.apply_block(&view, NOW), Ok(Applied::Extended));
        // It spends that output, and makes two: the reward with the fee
        // first, and what the transaction paid.
        assert_eq!(view.body().inputs().collect::<Vec<u64>>(), [0]);
        let amounts: Vec<u64> = view.body().outputs().map(|o| o.amount).collect();
        assert_eq!(amounts, [params.subsidy(2) + fee, paid - fee]);
        // The same transaction again, its output spent: the block is
        // not made, and nothing is wrong.
        let pay = Output::to_key_hash(&reward, reward_due(&chain, &pooled).unwrap().unwrap().1);
        let again = mine_with(&chain, setup, dataset, &pay, NOW, 9, &pooled, &sweeps, &|_| {}, &|| false).unwrap();
        assert!(matches!(again, Mined::Stale), "{again:?}");
        // A target nothing meets: looked for until told.
        let asked = AtomicU64::new(0);
        let cancel = || asked.fetch_add(1, Ordering::Relaxed) >= 3;
        assert!(solve(dataset, &reward, &Target([0; 32]), 7, &cancel).is_none());
    }

    /// Blocks that register a name, pay a policy, spend it by its two
    /// keys and update the name, each made from the pool: the
    /// operations are done after the transactions, a commitment's
    /// output comes after the block's others, and a policy's signers
    /// and a name's owner are found in the signed set.
    #[test]
    #[cfg_attr(debug_assertions, ignore = "proves blocks; run with --release")]
    fn names_and_policies_are_mined() {
        use crate::name::{NameOp, Record, commit_hash};
        use crate::output::{Key, pubkey_hash};
        use crate::policy::{Cond, CondWitness, Leaf, Mode, Policy, Signer};
        let (setup, params) = network();
        let chain = Chain::open(MemBackend::new(), 8, params, seed(), setup.verifier()).unwrap();
        chain.set_dataset(table());
        let dataset = &*table();
        let mut key = Key::generate(&[6; 32]);
        let (pk, mine_to) = (key.public_key(), pubkey_hash(&key.public_key()));
        // The next block, of what the pool holds: what it carried.
        let next = |pool: &mut Mempool, txs: Vec<Vec<u8>>| -> Vec<u8> {
            {
                let state = chain.whole().unwrap();
                let snap = state.snapshot().unwrap();
                let height = snap.tip().0 + 1;
                for tx in &txs {
                    pool.insert(tx, &snap, height, NOW).unwrap();
                }
            }
            let (pooled, sweeps) = choose(&chain, setup, &|f| f(pool), MAX_SIGNATURES).unwrap();
            assert_eq!(pooled.len(), txs.len());
            let pay = Output::to_key_hash(&[0xEE; 32], reward_due(&chain, &pooled).unwrap().unwrap().1);
            let made = mine_with(&chain, setup, dataset, &pay, NOW, 1, &pooled, &sweeps, &|_| {}, &|| false).unwrap();
            let Mined::Block { block, .. } = made else { panic!("{made:?}") };
            assert_eq!(chain.apply_block(&BlockRef::from_bytes(&block).unwrap(), NOW), Ok(Applied::Extended));
            for tx in &pooled {
                pool.remove(&tx.txid());
            }
            block
        };
        let mut pool = Mempool::new(1 << 22);
        let made = mine(&chain, setup, dataset, &mine_to, NOW, 3, &|_| {}, &|| false).unwrap();
        let Mined::Block { block, .. } = made else { panic!("{made:?}") };
        assert_eq!(chain.apply_block(&BlockRef::from_bytes(&block).unwrap(), NOW), Ok(Applied::Extended));
        let (mut held, fee) = (params.subsidy(1), 10_000_000);

        // Block 2: a payment that commits to a name. Its outputs are at
        // 1 (the reward) and 2, its commitment's at 3.
        let mut owner = Key::generate(&[7; 32]);
        let alice = Record::new(b"alice", pubkey_hash(&owner.public_key()), [1; 32], [2; 32]).unwrap();
        let salt = [9; 32];
        let ops = vec![NameOp::Commit { commit: commit_hash(&alice.name.hash(), &salt, &alice.owner), memo: [3; 20] }];
        let tx = UnsignedTransaction::with_ops(vec![(pk, held)], vec![Output::new(&pk, held - fee)], ops)
            .at(&[0])
            .sign_with(&mut key)
            .unwrap();
        held -= fee;
        let block = next(&mut pool, vec![tx.to_bytes()]);
        let view = BlockRef::from_bytes(&block).unwrap();
        assert_eq!((view.body().outputs().len(), view.body().ops().len()), (2, 1));

        // Block 3: the name revealed, by a payment to a policy of two
        // keys. The policy's output is at 5.
        let (mut a, mut b) = (Key::generate(&[10; 32]), Key::generate(&[11; 32]));
        let keys = vec![pubkey_hash(&a.public_key()), pubkey_hash(&b.public_key())];
        let policy = Policy::new(vec![Leaf::new(vec![Cond::Thresh { mode: Mode::Body, m: 2, keys }])]);
        let ops = vec![NameOp::Reveal { record: alice, salt, commit: 3 }];
        let outputs = vec![Output::to_key_hash(&policy.root(), held - fee)];
        let tx = UnsignedTransaction::with_ops(vec![(pk, held)], outputs, ops).at(&[2]).sign_with(&mut key).unwrap();
        held -= fee;
        next(&mut pool, vec![tx.to_bytes()]);
        {
            let state = chain.whole().unwrap();
            let snap = state.snapshot().unwrap();
            assert_eq!(snap.name(alice.key()).unwrap(), Some(alice));
            assert!(!snap.is_unspent(3).unwrap() && snap.is_unspent(5).unwrap());
        }

        // Block 4: the policy's output spent by its two keys, into more
        // outputs than one run holds (the block is of two, joined, and
        // the spend lies across them), and the name given a new record
        // by its owner.
        let moved = Record { owner: pubkey_hash(&pk), value: [5; 32], ..alice };
        let ops = vec![NameOp::update(moved, &mut owner).unwrap()];
        let (count, each, fee) = (600u64, 1_000_000u64, 100_000_000u64);
        let mut outputs: Vec<Output> = (1..count).map(|i| Output::to_key_hash(&[i as u8; 32], each)).collect();
        outputs.push(Output::new(&pk, held - (count - 1) * each - fee));
        let unsigned =
            UnsignedTransaction::with_ops(vec![], outputs, ops).with_policy_inputs(vec![policy.spend(0, held, 5)]);
        let body = unsigned.body_hash();
        let mut tx = unsigned.sign(|_, _, _| Err::<crate::output::Sig, ()>(())).unwrap();
        tx.policy_inputs[0].witness[0] = CondWitness::Signatures(vec![
            Signer { key: 0, pubkey: a.public_key(), signature: a.sign(&body).unwrap() },
            Signer { key: 1, pubkey: b.public_key(), signature: b.sign(&body).unwrap() },
        ]);
        let block = next(&mut pool, vec![tx.to_bytes()]);
        let view = BlockRef::from_bytes(&block).unwrap();
        assert_eq!(view.body().inputs().collect::<Vec<u64>>(), [5]);
        assert_eq!(view.body().outputs().len(), 1 + count as usize);
        let state = chain.whole().unwrap();
        let snap = state.snapshot().unwrap();
        assert_eq!(snap.name(alice.key()).unwrap(), Some(moved));
        assert!(!snap.is_unspent(5).unwrap());
    }

    /// A block of more than one run holds is of two runs, joined: a
    /// transaction may lie across them, the second run going on from the
    /// state, the outputs and the transaction in hand the first left.
    #[test]
    #[cfg_attr(debug_assertions, ignore = "proves blocks; run with --release")]
    fn a_block_of_more_than_a_run_holds_is_joined() {
        use crate::output::{Key, pubkey_hash};
        let (setup, params) = network();
        let chain = Chain::open(MemBackend::new(), 8, params, seed(), setup.verifier()).unwrap();
        chain.set_dataset(table());
        let dataset = &*table();
        let mut key = Key::generate(&[8; 32]);
        let (pk, mine_to) = (key.public_key(), pubkey_hash(&key.public_key()));
        for _ in 0..2 {
            let made = mine(&chain, setup, dataset, &mine_to, NOW, 3, &|_| {}, &|| false).unwrap();
            let Mined::Block { block, .. } = made else { panic!("{made:?}") };
            assert_eq!(chain.apply_block(&BlockRef::from_bytes(&block).unwrap(), NOW), Ok(Applied::Extended));
        }
        // A payment of 500 outputs, more than one run holds, and one of
        // 100: the first lies across the two runs.
        let (counts, each, fee) = ([500u64, 100], 1_000_000u64, 100_000_000u64);
        let mut pool = Mempool::new(1 << 22);
        {
            let state = chain.whole().unwrap();
            let snap = state.snapshot().unwrap();
            for position in 0..2u64 {
                let held = params.subsidy(position as u32 + 1);
                let count = counts[position as usize];
                let mut outputs: Vec<Output> = (1..count).map(|i| Output::to_key_hash(&[i as u8; 32], each)).collect();
                outputs.push(Output::new(&pk, held - (count - 1) * each - fee));
                let tx =
                    UnsignedTransaction::new(vec![(pk, held)], outputs).at(&[position]).sign_with(&mut key).unwrap();
                pool.insert(&tx.to_bytes(), &snap, 3, NOW).unwrap();
            }
        }
        let (pooled, sweeps) = choose(&chain, setup, &|f| f(&pool), MAX_SIGNATURES).unwrap();
        assert_eq!((pooled.len(), sweeps.len()), (2, 0));
        let pay = Output::to_key_hash(&mine_to, reward_due(&chain, &pooled).unwrap().unwrap().1);
        let made = mine_with(&chain, setup, dataset, &pay, NOW, 1, &pooled, &sweeps, &|_| {}, &|| false).unwrap();
        let Mined::Block { block, .. } = made else { panic!("{made:?}") };
        let view = BlockRef::from_bytes(&block).unwrap();
        assert_eq!(chain.apply_block(&view, NOW), Ok(Applied::Extended));
        let count = counts[0] + counts[1];
        assert_eq!((view.body().inputs().len(), view.body().outputs().len()), (2, 1 + count as usize));
        let state = chain.whole().unwrap();
        let snap = state.snapshot().unwrap();
        assert_eq!(snap.outputs().next, 2 + 1 + count);
    }

    /// Debugging only, where proofs go unchecked: blocks filled with
    /// what nobody sent, that spend the outputs a chain began with; and
    /// a chain of empty blocks made beforehand, with a table and
    /// without one.
    #[cfg(feature = "dev")]
    #[test]
    fn blocks_are_filled_and_a_chain_is_made_beforehand() {
        use crate::chain::headers::tests::easy;
        use crate::chain::params::ChainParams;
        use crate::prover::{Level, Parts};
        let open = |params: ChainParams| {
            let verifier = ChainVerifier::of(&Level::SMALL, &Parts::dev()).unchecked();
            let chain = Chain::open(MemBackend::new(), 8, params, seed(), verifier).unwrap();
            chain.set_dataset(table());
            chain
        };
        // What a block holds of what is asked for: all of it, or both
        // less in the same measure.
        assert_eq!(fill_plan(2_000_000, 10, 20), (10, 20));
        let (outputs, spends) = fill_plan(2_000_000, 100_000, 100_000);
        assert!(outputs == spends && (20_000..100_000).contains(&outputs), "{outputs}");
        assert_eq!(fill_plan(0, 5, 5), (0, 0));

        // A chain begun with a state nobody made.
        let (n, spacing) = (400u64, 5u64);
        let (root, roots) = crate::chain::debug::root(n, spacing, &|_| {});
        let params = ChainParams { genesis_state: Some(root), ..easy() };
        let chain = open(params);
        crate::chain::debug::fill(&chain, n, spacing, &roots, &|_| {}).unwrap();
        let dataset = &*table();
        let said = Mutex::new(Vec::new());
        let say = |line: &str| said.lock().unwrap().push(line.to_string());
        let filled = Some((n, spacing));
        for height in 1..=3u32 {
            let paid = Output::to_key_hash(&[9; 32], params.subsidy(height) - 30);
            let made = mine_filled(&chain, dataset, &paid, NOW, 1, 30, 20, filled, &say, &|| false).unwrap();
            let Mined::Block { block, header, .. } = made else { panic!("{made:?}") };
            let view = BlockRef::from_bytes(&block).unwrap();
            assert_eq!((view.body().outputs().len(), view.body().inputs().len()), (31, 20));
            assert_eq!(chain.apply_block(&view, NOW), Ok(Applied::Extended));
            assert_eq!(chain.tip().unwrap(), header);
        }
        let lines = said.lock().unwrap().clone();
        assert!(lines[0].starts_with("debug fill: block 1: 30 outputs, 20 spends, "), "{lines:?}");
        assert_eq!(reward_due(&chain, &[]).unwrap(), Some((4, params.subsidy(4))));
        // A reward that is not what the block may make with its outputs
        // is another block's; and a block given up is not made.
        let paid = Output::to_key_hash(&[9; 32], params.subsidy(4));
        let made = mine_filled(&chain, dataset, &paid, NOW, 1, 30, 20, filled, &say, &|| false).unwrap();
        assert!(matches!(made, Mined::Stale), "{made:?}");
        let paid = Output::to_key_hash(&[9; 32], params.subsidy(4) - 30);
        let made = mine_filled(&chain, dataset, &paid, NOW, 1, 30, 20, filled, &say, &|| true).unwrap();
        assert!(matches!(made, Mined::Cancelled), "{made:?}");

        // A chain of empty blocks: with the table every block's work is
        // done, and a chain that is long enough already is left alone.
        let chain = open(easy());
        let told = Mutex::new(Vec::new());
        let progress = |height: u32| told.lock().unwrap().push(height);
        extend_empty(&chain, &seed(), Some(dataset), 20, 600, NOW + 1_000_000, &progress).unwrap();
        assert_eq!(chain.tip().unwrap().height, 20);
        extend_empty(&chain, &seed(), Some(dataset), 20, 600, NOW + 1_000_000, &progress).unwrap();
        assert_eq!(chain.tip().unwrap().height, 20);
        // Without one, only the first and the last of them: the rest
        // claim work nobody did, which the chain is told to take while
        // they are made, and no longer.
        let chain = open(easy());
        let blocks = 2 * WORKED + 8;
        extend_empty(&chain, &seed(), None, blocks, 600, NOW + 1_000_000, &progress).unwrap();
        assert_eq!(chain.tip().unwrap().height, blocks);
        let claimed = chain.header_at(WORKED + 4).unwrap().unwrap();
        assert_eq!(claimed.mix, EMPTY);
        assert_ne!(chain.header_at(WORKED).unwrap().unwrap().mix, EMPTY);
        assert_ne!(chain.header_at(blocks).unwrap().unwrap().mix, EMPTY);
    }
}
