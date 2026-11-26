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
//!    transactions chosen, against the state as it is ([`draft`]).
//! 2. The block's proof: what takes the time
//!    ([`crate::job::ProveJob::prove`]).
//! 3. The proof checked, and the header ([`Draft::proven`]).
//! 4. A nonce whose hash meets the target: on every thread there is,
//!    each trying its own nonces ([`crate::job::HashJob::solve`]).
//! 5. The block, whole ([`Proven::block`]).
//!
//! The first, third and fifth are the node's. The second and fourth are
//! work it gives out, as jobs ([`crate::job`]), to whoever proves and
//! whoever hashes for it: each job says all that doing it takes, and
//! what comes back is checked here as anything from outside is.
//! [`mine_with`] is the five together in one place, for the tests and
//! for the dev networks' tools: its job goes through its bytes, as one
//! sent does.

use std::time::{Duration, Instant};

use crate::block::{Block, Body, BodyRef, HEADER_SIZE, Header};
use crate::chain::Chain;
use crate::chain::verify::{BlockStatement, ProofVerifier};
use crate::chain_proof::Statement;
use crate::difficulty::Target;
use crate::error::Error;
use crate::hash::Digest;
use crate::job::{Found, HashJob, Proof, ProveJob};
pub use crate::job::{fill_table, solve};
use crate::mempool::{Mempool, PROOF_BYTES};
use crate::output::Output;
use crate::pow::ItemSource;
use crate::prover::{ChainVerifier, Level, Setup};
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
/// that takes both. `level` is the level of the network's proofs:
/// whoever chooses needs no more of a setup.
#[allow(clippy::type_complexity)]
pub fn choose<B: Backend + 'static, V>(
    chain: &Chain<B, V>,
    level: &Level,
    with_pool: &dyn Fn(&mut dyn FnMut(&Mempool)),
    max_signatures: usize,
) -> Result<(Vec<Transaction>, Vec<u64>), Error> {
    let params = *chain.params();
    let state = chain.whole()?;
    let snap = state.snapshot()?;
    let height = snap.tip().0 + 1;
    let sweeps = Mempool::sweeps(&snap, height);
    let mut chosen: Vec<Transaction> = Vec::new();
    let most = max_signatures.min(level.signatures());
    if most == 0 {
        return Ok((chosen, sweeps));
    }
    // What a block comes to with the transactions chosen so far: the
    // signatures it checks, what it spends and makes, the bytes of its
    // operations on names and its sweeps, and what it has taken of its
    // proof.
    #[derive(Clone, Copy)]
    struct Sum {
        weight: usize,
        spends: usize,
        makes: usize,
        names: usize,
        filled: crate::prover::Filled,
    }
    with_pool(&mut |pool: &Mempool| {
        // What is chosen so far, decoded once, and what it comes to
        // after each: kept as the choosing goes, so that trying one more
        // asks of that one alone. (To ask of all of them again for each
        // one tried is minutes, of a full block.)
        let mut so_far: Vec<Transaction> = Vec::new();
        let mut sums = vec![Sum {
            weight: 0,
            spends: 0,
            makes: 1,
            names: sweeps.len() * crate::codec::POSITION_BYTES,
            filled: level.filled(snap.outputs().next),
        }];
        let reserve = most * crate::output::INPUT_SIZE * pool.policy().reserve_percent / 100;
        let taken = pool.select(&snap, height, params.min_reveal, reserve, |trying| {
            // (Those before the one tried are those chosen: one that
            // did not go in was never kept.)
            let chosen = trying.len() - 1;
            so_far.truncate(chosen);
            sums.truncate(chosen + 1);
            let tx = trying[chosen].to_transaction();
            let before = sums[chosen];
            let Some(filled) = level.filled_with(&before.filled, &tx) else { return false };
            let with = Sum {
                weight: before.weight + tx.weight(),
                spends: before.spends + tx.inputs.len() + tx.policy_inputs.len(),
                makes: before.makes + tx.outputs.len(),
                names: before.names + tx.ops.iter().map(|op| op.block_op().size()).sum::<usize>(),
                filled,
            };
            let size = HEADER_SIZE + Body::size_of(with.spends, with.makes, with.names, PROOF_BYTES);
            if with.weight > most || size > params.max_block_size || !level.takes(&with.filled, sweeps.len()) {
                return false;
            }
            so_far.push(tx);
            sums.push(with);
            true
        });
        so_far.truncate(taken.len());
        chosen = std::mem::take(&mut so_far);
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

/// What the chain's proof stated with the block of `tip` in, and the
/// proof that block carried: what the next block's proof builds on.
/// None where a chain begins, before the first.
fn before<B: Backend + 'static, V: ProofVerifier + Sync>(
    chain: &Chain<B, V>,
    tip: &Header,
    roots: &(Digest, Digest),
    next: u64,
) -> Result<Option<(Statement, Vec<u8>)>, Error> {
    if tip.height == 0 {
        return Ok(None);
    }
    let bytes = chain.body(&tip.hash())?.ok_or(Error::BadProof)?;
    let body = BodyRef::from_bytes(&bytes)?;
    let stated = chain.statement(tip.height, &tip.prev_hash, &body, roots, next);
    if stated.digest() != tip.statement {
        return Err(Error::BadProof);
    }
    Ok(Some((stated, body.proof().to_vec())))
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

/// A block begun: what the node keeps of it while its proof is made.
pub struct Draft {
    /// The header it builds on.
    tip: Header,
    /// Its body, without its proof.
    body: Body,
    /// What its header is to say of the state after it, and what the
    /// chain's proof is to state with it in.
    state_root: Digest,
    stated: Statement,
}

/// What came of beginning a block ([`draft`]).
///
/// (A block begun is some 700 bytes where the others are none: one is
/// made for a block and let go with it, so it is left as it is.)
#[allow(clippy::large_enum_variant)]
pub enum Drafted {
    /// The job of proving it, and what is kept meanwhile.
    Begun(Box<ProveJob>, Draft),
    /// The chain has another last block than the state is of.
    Cancelled,
    /// As [`Mined::Stale`].
    Stale,
    /// As [`Mined::Finished`].
    Finished,
}

/// Begins the block after `chain`'s last, of the transactions `pooled`
/// and sweeping the commits at `sweeps` ([`choose`]), paying its reward
/// and their fees ([`reward_due`]) by the output `paid`, which is the
/// maker's own: the job of proving it, which says all that takes, and
/// what the node keeps until the proof comes ([`Draft::proven`]).
///
/// Nothing is proven here, and nothing of a setup is needed: a chain
/// whose proofs go unchecked begins a block as any does.
pub fn draft<B: Backend + 'static, V: ProofVerifier + Sync>(
    chain: &Chain<B, V>,
    paid: &Output,
    pooled: &[Transaction],
    sweeps: &[u64],
) -> Result<Drafted, Error> {
    let params = *chain.params();
    let tip = chain.tip()?;
    let height = tip.height + 1;
    let subsidy = params.subsidy(height);
    if subsidy == 0 {
        return Ok(Drafted::Finished);
    }
    // The reward pays what the block may make and what its
    // transactions leave: an output made for another block's is not
    // this block's.
    let fees: u64 = pooled.iter().map(|tx| tx.balance().clamp(0, u64::MAX as i128) as u64).sum();
    if paid.amount != subsidy.saturating_add(fees) {
        return Ok(Drafted::Stale);
    }
    let state = chain.whole()?;
    let (witness, roots, next) = {
        let snap = state.snapshot()?;
        // (The state of the block being built on, or it has moved on.)
        // (The state before the first block is of no block.)
        let (at, id) = snap.tip();
        if at != tip.height || (at > 0 && id != tip.hash()) {
            return Ok(Drafted::Cancelled);
        }
        let witness = match witness_of(&snap, pooled, sweeps) {
            Ok(witness) => witness,
            // What a transaction of the pool spends is not there.
            Err(Error::NoSuchOutput(_)) if !pooled.is_empty() || !sweeps.is_empty() => return Ok(Drafted::Stale),
            Err(e) => return Err(e),
        };
        (witness, (snap.outputs().hash(), snap.names().hash()), snap.outputs().next)
    };
    drop(state);
    // (Asked of the chain once its state is let go of: to ask the
    // chain while holding its state is to take what keeps it twice,
    // which waits for ever on anyone waiting to write between the
    // two.)
    let before = before(chain, &tip, &roots, next)?;
    // The body, without its proof: what the header is of, and what the
    // proof is to state.
    let body = Body {
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
        Err(_) => return Ok(Drafted::Stale),
    };
    let job = ProveJob {
        program: params.program,
        parent: tip,
        before,
        roots,
        next,
        subsidy,
        witness,
        txs: pooled.to_vec(),
        sweeps: sweeps.to_vec(),
        reward: *paid,
    };
    Ok(Drafted::Begun(Box::new(job), Draft { tip, body, state_root, stated }))
}

impl Draft {
    /// The height of the block begun, and the header it builds on.
    pub fn on(&self) -> &Header {
        &self.tip
    }

    /// The block with `proof` for its proof, which came of the job: its
    /// header, for its nonce to be found. `unix` is the time by the
    /// calendar, in seconds.
    ///
    /// The proof is whatever was handed over, and is checked as the
    /// chain will check the block's: one that is no proof of this block
    /// is refused here ([`Error::BadProof`]), as is one that makes the
    /// block larger than a block may be.
    pub fn proven<B: Backend + 'static, V: ProofVerifier + Sync>(
        self,
        chain: &Chain<B, V>,
        proof: Vec<u8>,
        unix: u64,
    ) -> Result<Proven, Error> {
        let Draft { tip, mut body, state_root, stated } = self;
        body.proof = proof;
        let size = HEADER_SIZE + body.size();
        if size > chain.params().max_block_size {
            return Err(Error::TooLarge(size));
        }
        // (What was proven is what the chain will ask of the block.)
        let whole = body.to_bytes();
        let statement = BlockStatement { chain: stated, digest: stated.digest(), body: BodyRef::from_bytes(&whole)? };
        if !chain.verifier().verify(&statement, &body.proof) {
            return Err(Error::BadProof);
        }
        let header = Header {
            prev_hash: tip.hash(),
            height: tip.height + 1,
            timestamp: unix.max(chain.earliest_timestamp(&tip)?),
            body_commitment: body.commitment(),
            state_root,
            statement: stated.digest(),
            aux: chain.aux_root()?,
            mix: tip.mix,
            nonce: [0; 32],
        };
        let target = chain.expected_target(&tip)?;
        Ok(Proven { header, body, target })
    }
}

/// A block proven: all of it but its nonce.
pub struct Proven {
    /// Its header, with no nonce yet.
    header: Header,
    body: Body,
    target: Target,
}

impl Proven {
    /// The job of finding its nonce.
    pub fn job(&self) -> HashJob {
        HashJob { height: self.header.height, hash: self.header.pow_hash(), target: self.target }
    }

    /// The block with the nonce `found`, whole, and its header. None if
    /// what was found is not this header's, or does not claim work that
    /// meets its target: whether the work is as claimed is for the chain
    /// to say when it takes the block, as of any block.
    pub fn block(&self, found: &Found) -> Option<(Vec<u8>, Header)> {
        if !found.claims(&self.job()) {
            return None;
        }
        let header = Header { nonce: found.nonce, mix: found.mix, ..self.header };
        Some((Block { header, body: self.body.clone() }.to_bytes(), header))
    }
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
///
/// All of a block's steps, in one place: the block is begun
/// ([`draft`]), its job proven as whoever is sent one proves it, from
/// its bytes, and its nonce found as whoever is sent that job finds it.
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
    let began = Instant::now();
    let (job, draft) = match draft(chain, paid, pooled, sweeps)? {
        Drafted::Begun(job, draft) => (job, draft),
        Drafted::Cancelled => return Ok(Mined::Cancelled),
        Drafted::Stale => return Ok(Mined::Stale),
        Drafted::Finished => return Ok(Mined::Finished),
    };
    // (A proof before that this build does not take is not built on:
    // the block's own could not be made, and is not tried.)
    if let Some((stated, proof)) = &job.before {
        setup.carried(proof, stated).ok_or(Error::BadProof)?;
    }
    // The signatures, proven; and the block's proof on the proof before.
    let job = ProveJob::from_bytes(&job.to_bytes())?;
    let proof = match job.prove(setup, dataset, &|| cancel()) {
        Proof::Made(proof) => proof,
        Proof::Refused => return Ok(Mined::Stale),
        Proof::GivenUp => return Ok(Mined::Cancelled),
    };
    // The chain may have another last block by now, heard of while the
    // proof was made: then this block is for nothing.
    if cancel() {
        return Ok(Mined::Cancelled);
    }
    let proven = draft.proven(chain, proof, unix)?;
    let took = began.elapsed();
    // The proof is made: what is left is to find the nonce.
    proved(took);
    let began = Instant::now();
    let Some((found, hashes)) = proven.job().solve(dataset, start, cancel) else {
        return Ok(Mined::Cancelled);
    };
    let (block, header) = proven.block(&found).ok_or(Error::BadProofOfWork)?;
    let solved = began.elapsed();
    Ok(Mined::Block { block, header, proved: took, hashes, solved })
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
    use crate::hash::EMPTY;
    use crate::output::BlockOutput;
    use crate::pow::nonce_from_u64;
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

#[cfg(test)]
mod hold_off {
    use super::*;

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
    use std::sync::atomic::{AtomicU64, Ordering};

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
        assert!(choose(&chain, &setup.level, &|f| f(&pool), 0).unwrap().0.is_empty());
        let (pooled, sweeps) = choose(&chain, &setup.level, &|f| f(&pool), MAX_SIGNATURES).unwrap();
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
            let (pooled, sweeps) = choose(&chain, &setup.level, &|f| f(pool), MAX_SIGNATURES).unwrap();
            assert_eq!(pooled.len(), txs.len());
            // (Chosen one at a time, they are what asking of them all
            // together takes; and their signatures are counted as many
            // as they are.)
            let next = chain.state().snapshot().unwrap().outputs().next;
            assert!(setup.level.fits(next, &pooled, sweeps.len()));
            assert!(pooled.iter().all(|tx| tx.signings_len() == tx.signings().len()));
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
        let (pooled, sweeps) = choose(&chain, &setup.level, &|f| f(&pool), MAX_SIGNATURES).unwrap();
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
        use crate::hash::EMPTY;
        use crate::prover::Parts;
        use std::sync::Mutex;
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

    /// What each output of [`funded`] holds, and what a payment leaves
    /// for whoever makes its block, for each output it spends.
    const HELD: u64 = 100_000_000;
    const FEE: u64 = 1_000_000;

    type Unchecked = Chain<MemBackend, crate::chain::verify::AcceptAllProofs>;

    fn key(tag: u32) -> crate::xmss::SecretKey {
        let mut seed = [0u8; 32];
        seed[..4].copy_from_slice(&tag.to_le_bytes());
        crate::xmss::SecretKey::generate(&seed)
    }

    /// A chain whose proofs go unchecked, in which each of `keys` keys
    /// (those of the tags from 1) has two outputs of [`HELD`]: the key
    /// of tag `t` the one `2 * (t - 1)` on from the position returned,
    /// and the one after it.
    fn funded(keys: u32) -> (Unchecked, u64) {
        use crate::chain::apply::tests::extend_with;
        use crate::chain::headers::tests::easy;
        let chain = Chain::open(MemBackend::new(), 8, easy(), seed(), crate::chain::verify::AcceptAllProofs).unwrap();
        chain.set_dataset(table());
        let first = chain.state().snapshot().unwrap().outputs().next;
        let outputs: Vec<crate::output::BlockOutput> = crate::parallel::par_map(keys as usize, |i| {
            Output::new(&key(i as u32 + 1).public_key(), HELD).block_output()
        });
        // (In one block, which makes what a block may and no more: the
        // rest of it is nobody's, and is the block's last output.)
        let mut made: Vec<crate::output::BlockOutput> = outputs.iter().flat_map(|o| [*o, *o]).collect();
        let rest = chain.params().subsidy(1) - HELD * made.len() as u64;
        made.push(Output::to_key_hash(&[0xee; 32], rest).block_output());
        extend_with(&chain, &made);
        (chain, first)
    }

    /// A payment by the key of tag `tag` on the chain of [`funded`],
    /// whose outputs begin at `first`: of one of its outputs or of both,
    /// half to the next key and the rest, less [`FEE`] for each, back to
    /// itself.
    fn payment(tag: u32, first: u64, both: bool) -> Transaction {
        let mut key = key(tag);
        let (own, at) = (key.public_key(), first + 2 * (tag as u64 - 1));
        let positions: Vec<u64> = (at..at + 1 + both as u64).collect();
        let held = HELD * positions.len() as u64;
        let fee = FEE * positions.len() as u64;
        let to = crate::output::pubkey_hash(&own).map(|b| b ^ 0x5a);
        UnsignedTransaction::new(
            positions.iter().map(|_| (own, HELD)).collect(),
            vec![Output::to_key_hash(&to, held / 2), Output::new(&own, held - held / 2 - fee)],
        )
        .at(&positions)
        .sign(|_, _, m| key.sign(m))
        .unwrap()
    }

    /// A block is made in steps, and whoever does one needs only what
    /// it is handed: the node begins the block and gives out the job of
    /// proving it, which is read back whole from its bytes; with a
    /// proof it gives out the job of finding the nonce; and with the
    /// nonce it has the block, which the chain takes. Nothing is proven
    /// here: the chain's proofs go unchecked.
    #[test]
    fn a_block_is_made_in_steps() {
        let (chain, first) = funded(3);
        let level = &Level::MAINNET;
        let mut pool = Mempool::with_policy(1 << 20, crate::mempool::Policy::MAINNET.holding_all());
        let txs = [payment(1, first, false), payment(2, first, true)];
        {
            let state = chain.state();
            let snap = state.snapshot().unwrap();
            txs.iter().for_each(|tx| _ = pool.insert(&tx.to_bytes(), &snap, snap.tip().0 + 1, NOW).unwrap());
        }
        let tip = chain.tip().unwrap();
        let (pooled, sweeps) = choose(&chain, level, &|f| f(&pool), MAX_SIGNATURES).unwrap();
        assert_eq!((pooled.len(), sweeps.len()), (2, 0));
        assert!(level.fits(first + 7, &pooled, 0) && pooled.iter().all(|tx| tx.signings_len() == tx.signings().len()));
        // No more of them than the signatures to be proven: the two
        // check three, and the dearer for what it checks goes first.
        let fewer = choose(&chain, level, &|f| f(&pool), 2).unwrap().0;
        assert_eq!(fewer.iter().map(Transaction::weight).collect::<Vec<usize>>(), [2]);
        assert_eq!(choose(&chain, level, &|f| f(&pool), 1).unwrap().0.len(), 1);
        let (height, due) = reward_due(&chain, &pooled).unwrap().unwrap();
        assert_eq!((height, due), (tip.height + 1, chain.params().subsidy(height) + 3 * FEE));
        let paid = Output::to_key_hash(&[9; 32], due);
        // A reward that is not what this block pays: none is begun.
        let other = Output::to_key_hash(&[9; 32], due + 1);
        assert!(matches!(draft(&chain, &other, &pooled, &sweeps).unwrap(), Drafted::Stale));

        // The job says the block, and what is before it.
        let begin = || match draft(&chain, &paid, &pooled, &sweeps).unwrap() {
            Drafted::Begun(job, draft) => (job, draft),
            _ => panic!("no block begun"),
        };
        let (job, begun) = begin();
        assert_eq!((job.height(), job.parent, begun.on()), (height, tip, &tip));
        assert_eq!((job.program, job.subsidy), (chain.params().program, chain.params().subsidy(height)));
        assert_eq!((job.txs.len(), job.reward, job.next), (2, paid, first + 7));
        let mut spent: Vec<u64> = job.witness.spent.keys().copied().collect();
        spent.sort_unstable();
        assert_eq!(spent, [first, first + 2, first + 3]);
        let (stated, proof) = job.before.clone().unwrap();
        assert_eq!(stated.digest(), tip.statement);
        assert_eq!(
            Some(proof),
            chain.body(&tip.hash()).unwrap().map(|b| BodyRef::from_bytes(&b).unwrap().proof().to_vec())
        );
        // It is its bytes: whoever proves it has no more.
        let bytes = job.to_bytes();
        let read = ProveJob::from_bytes(&bytes).unwrap();
        assert_eq!(read.to_bytes(), bytes);
        assert_eq!((read.txs.len(), read.start(), read.roots), (2, job.start(), job.roots));
        // One that has not the path of all it spends is none, nor one
        // that says of an output what the state does not.
        let mut lacking = (*job).clone();
        lacking.witness.spent.remove(&(first + 2));
        assert!(ProveJob::from_bytes(&lacking.to_bytes()).is_err());
        let mut other = (*job).clone();
        other.witness.spent.get_mut(&first).unwrap().amount += 1;
        assert!(ProveJob::from_bytes(&other.to_bytes()).is_err());

        // A proof that makes the block larger than a block may be.
        let large = begin().1.proven(&chain, vec![0; chain.params().max_block_size], NOW);
        assert!(matches!(large.err(), Some(Error::TooLarge(_))));
        // The proof handed back (any bytes, to this chain): the header,
        // and the job of finding its nonce.
        let proven = begun.proven(&chain, vec![7; 1000], NOW).unwrap();
        let hashing = proven.job();
        assert_eq!((hashing.height, hashing.target), (height, chain.expected_target(&tip).unwrap()));
        let (found, _) = hashing.solve(&*table(), 5, &|| false).unwrap();
        // What is found for another header is not this block's.
        assert!(proven.block(&Found { hash: [0; 32], ..found }).is_none());
        let (block, header) = proven.block(&found).unwrap();
        assert_eq!(header.pow_hash(), hashing.hash);
        let view = BlockRef::from_bytes(&block).unwrap();
        assert_eq!(chain.apply_block(&view, NOW), Ok(Applied::Extended));
        assert_eq!(view.body().inputs().collect::<Vec<u64>>(), [first, first + 2, first + 3]);
        assert_eq!(view.body().outputs().count(), 5);
        assert_eq!(view.body().proof(), [7; 1000]);
        // What it spent is spent: the same again is no block.
        assert!(matches!(draft(&chain, &paid, &pooled, &sweeps).unwrap(), Drafted::Stale));
    }

    /// A proof that is none is refused when it is handed back, by a
    /// chain that checks proofs: whatever the bytes are.
    #[cfg(feature = "dev")]
    #[test]
    fn a_proof_that_is_none_is_refused() {
        use crate::chain::headers::tests::easy;
        use crate::prover::Parts;
        let verifier = ChainVerifier::of(&Level::SMALL, &Parts::dev());
        let chain = Chain::open(MemBackend::new(), 8, easy(), seed(), verifier).unwrap();
        chain.set_dataset(table());
        let paid = Output::to_key_hash(&[9; 32], reward_due(&chain, &[]).unwrap().unwrap().1);
        for proof in [vec![], vec![0; 64], vec![0xff; 5000], (0..=255u8).cycle().take(450_000).collect()] {
            let Drafted::Begun(job, begun) = draft(&chain, &paid, &[], &[]).unwrap() else { panic!("no block begun") };
            // (The chain's first block: nothing is before it.)
            assert!(job.before.is_none() && job.txs.is_empty());
            assert_eq!(begun.proven(&chain, proof, NOW).err(), Some(Error::BadProof));
        }
    }

    /// The node's part of a full block: one of 2 MB, of ordinary
    /// payments of one input or two, and room for its proof. It is
    /// chosen from the pool, begun, its job written and read back, and
    /// with a stand-in for its proof and a nonce found the chain takes
    /// it. Nothing is proven: the chain's proofs go unchecked, as in the
    /// tests of size the reference has. Said with `--nocapture`: how
    /// many transactions and signatures that is, how large the job, and
    /// how long each step took.
    #[test]
    #[cfg_attr(debug_assertions, ignore = "signs thousands of transactions; run with --release")]
    fn a_full_block_is_begun_and_its_job_written() {
        let keys = 13_000u32;
        let (chain, first) = funded(keys);
        let level = &Level::MAINNET;
        let txs: Vec<Vec<u8>> =
            crate::parallel::par_map(keys as usize, |i| payment(i as u32 + 1, first, i % 2 == 1).to_bytes());
        let mut pool = Mempool::with_policy(1 << 30, crate::mempool::Policy::MAINNET.holding_all());
        {
            let state = chain.state();
            let snap = state.snapshot().unwrap();
            txs.iter().for_each(|tx| _ = pool.insert(tx, &snap, snap.tip().0 + 1, NOW).unwrap());
        }
        assert_eq!(pool.len(), keys as usize);
        let began = Instant::now();
        let (pooled, sweeps) = choose(&chain, level, &|f| f(&pool), level.signatures()).unwrap();
        let chosen = began.elapsed();
        let signatures: usize = pooled.iter().map(Transaction::weight).sum();
        let paid = Output::to_key_hash(&[9; 32], reward_due(&chain, &pooled).unwrap().unwrap().1);
        let began = Instant::now();
        let Drafted::Begun(job, begun) = draft(&chain, &paid, &pooled, &sweeps).unwrap() else {
            panic!("no block begun")
        };
        let drafted = began.elapsed();
        let began = Instant::now();
        let bytes = job.to_bytes();
        let written = began.elapsed();
        let began = Instant::now();
        let read = ProveJob::from_bytes(&bytes).unwrap();
        let read_in = began.elapsed();
        assert!(read.to_bytes() == bytes);
        let proven = begun.proven(&chain, vec![0; PROOF_BYTES], NOW).unwrap();
        let (found, _) = proven.job().solve(&*table(), 5, &|| false).unwrap();
        let (block, _) = proven.block(&found).unwrap();
        // Full: one payment more, the smallest the pool has left, does
        // not go in. What stops it is the block's size, or the rows the
        // block's proof has for it, whichever the payments reach first.
        let max = chain.params().max_block_size;
        let next = chain.state().snapshot().unwrap().outputs().next;
        let more = Transaction::from_bytes(&txs[keys as usize - 2]).unwrap();
        assert!(more.inputs.len() == 1 && pooled.iter().all(|tx| tx.txid() != more.txid()));
        let with: Vec<Transaction> = pooled.iter().cloned().chain([more]).collect();
        // (Asked of them all together, as they were not when chosen.)
        assert!(level.fits(next, &pooled, 0));
        let (by_rows, by_size) = (!level.fits(next, &with, 0), block.len() + 126 > max);
        println!(
            "a full block: {} transactions, {signatures} signatures, {} bytes (full by its proof's rows: {by_rows}; \
             by its size: {by_size}); its job {} bytes; chosen in {chosen:?}, begun in {drafted:?}, \
             written in {written:?}, read in {read_in:?}",
            pooled.len(),
            block.len(),
            bytes.len(),
        );
        assert!(block.len() <= max && (by_rows || by_size), "{}", block.len());
        assert_eq!(chain.apply_block(&BlockRef::from_bytes(&block).unwrap(), NOW), Ok(Applied::Extended));
    }
}
