//! Work a node gives out: a block to prove, and a header to find the
//! nonce of.
//!
//! A node makes a block in steps, and two of them are not its own: the
//! block's proof, and the search for a nonce. Each is given out as a
//! job, which says everything whoever does it needs, so that it needs
//! nothing of the chain; and what comes back is checked by the node as
//! it checks anything from outside.
//!
//! `docs/WORK.md` is the account of both, byte by byte: they are what
//! a prover or a miner made elsewhere speaks too.
//!
//! * A [`ProveJob`] is bytes: it carries a block's transactions and the
//!   paths in the state of all they spend, megabytes of a full block.
//! * A [`HashJob`] is JSON, and so is what answers it ([`Found`]): a
//!   hash, a target, a nonce.

use std::collections::BTreeSet;
use std::sync::Mutex;
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::time::Duration;

use crate::block::{HEADER_SIZE, Header};
use crate::chain_proof::{STATEMENT_BYTES, Statement};
use crate::codec::{Reader, Writer};
use crate::difficulty::Target;
use crate::error::Error;
use crate::hash::{Digest, EMPTY};
use crate::json::Json;
use crate::ledger::{OUTPUTS_HEIGHT, Record, state_node};
use crate::name::Key;
use crate::output::{MEMO_BYTES, OUTPUT_SIZE, Output, memo_from_bytes, memo_to_bytes};
use crate::pow::{ItemSource, LazyDataset, Nonce, hashimoto, nonce_from_u64, result_from_mix};
use crate::prover::{Contents, Setup, Signing, Witness};
use crate::transaction::Transaction;

/// The version of a [`ProveJob`]'s bytes: their first.
pub const VERSION: u8 = 1;

/// Bytes of an output spent, as a job carries it: its position, what
/// the state keeps of it, and its path.
const SPENT_BYTES: usize = 8 + 32 + MEMO_BYTES + 8 + 4 + 32 * OUTPUTS_HEIGHT;
/// Bytes of a name's path, as a job carries it, before the record that
/// may follow: its key, its leaf, and its path.
const NAMED_BYTES: usize = 16 + 32 + 32 * crate::registry::HEIGHT + 1;

/// A block to prove: what [`Setup::sign`] and [`Setup::block`] take,
/// and nothing else of the chain.
#[derive(Clone)]
pub struct ProveJob {
    /// The program of the chain's step: a prover whose setup has
    /// another is of another network, or another build, and makes no
    /// proof this chain takes.
    pub program: Digest,
    /// The header of the block before.
    pub parent: Header,
    /// What the chain's proof stated with that block in, and the proof
    /// it carried. None where a chain begins: the block is its first.
    pub before: Option<(Statement, Vec<u8>)>,
    /// The roots of the outputs and of the names, before the block.
    pub roots: (Digest, Digest),
    /// The position the block's first output takes.
    pub next: u64,
    /// What the block may make, before its transactions' fees.
    pub subsidy: u64,
    /// The paths in the state of all the block spends and touches.
    pub witness: Witness,
    /// The block's transactions, in order.
    pub txs: Vec<Transaction>,
    /// The commitments of names past their time that it sweeps.
    pub sweeps: Vec<u64>,
    /// The output that pays the block's maker: its first.
    pub reward: Output,
}

/// What came of a job to prove.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Proof {
    /// The block's proof, for its body.
    Made(Vec<u8>),
    /// There is none to make: the job is of another setup, or the block
    /// is not one a chain takes.
    Refused,
    /// Given up when told to.
    GivenUp,
}

impl ProveJob {
    /// The height of the block.
    pub fn height(&self) -> u32 {
        self.parent.height + 1
    }

    /// The record the block starts from ([`Record::block`]).
    pub fn start(&self) -> Record {
        Record {
            root: [self.roots.0; 2],
            inputs: [EMPTY; 2],
            outputs: [EMPTY; 2],
            next: [self.next; 2],
            sum_in: self.subsidy as u128,
            sum_out: 0,
            height: self.height(),
            names: [self.roots.1; 2],
            ops: [EMPTY; 2],
            done: [EMPTY; 2],
        }
    }

    /// The keys of the names the block's transactions touch, ascending,
    /// each once.
    fn named(&self) -> BTreeSet<Key> {
        self.txs.iter().flat_map(|tx| &tx.ops).filter_map(|op| op.record()).map(|record| record.key()).collect()
    }

    /// The job's proof, with `setup`: the signatures its transactions
    /// rest on, and then the block. `source` gives the items of the
    /// work of the header before, which any source does: a table, or
    /// the seed text ([`crate::pow::SeedText::at`]), from which they
    /// are made as fast as the proof needs them. `cancel` is asked,
    /// between the two, whether to give up.
    pub fn prove(&self, setup: &Setup, source: &impl ItemSource, cancel: &dyn Fn() -> bool) -> Proof {
        if self.program != setup.own {
            return Proof::Refused;
        }
        let before = match &self.before {
            None => setup.beginning(),
            Some((stated, proof)) => match setup.carried(proof, stated) {
                Some(before) => before,
                None => return Proof::Refused,
            },
        };
        let signings: Vec<Signing> = self.txs.iter().flat_map(Transaction::signings).collect();
        let signed = match signings.is_empty() {
            true => None,
            false => match setup.sign(&signings) {
                Some(signed) => Some(signed),
                None => return Proof::Refused,
            },
        };
        if cancel() {
            return Proof::GivenUp;
        }
        let contents = Contents { txs: &self.txs, sweeps: &self.sweeps, reward: &self.reward };
        let (start, witness) = (self.start(), self.witness.clone());
        match setup.block(source, &self.parent, &before, &start, witness, &contents, signed.as_ref()) {
            Some(proof) => Proof::Made(proof),
            None => Proof::Refused,
        }
    }

    /// The job as bytes (`docs/WORK.md`).
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut w = Writer::default();
        w.bytes(&[VERSION]);
        w.digest(&self.program);
        w.bytes(&self.parent.to_bytes());
        match &self.before {
            None => w.bytes(&[0]),
            Some((stated, proof)) => {
                w.bytes(&[1]);
                w.bytes(&stated.to_bytes());
                w.len(proof.len());
                w.bytes(proof);
            }
        }
        w.digest(&self.roots.0);
        w.digest(&self.roots.1);
        w.u64(self.next);
        w.u64(self.subsidy);
        // The outputs spent, ascending, and then the next position's
        // path.
        let mut spent: Vec<u64> = self.witness.spent.keys().copied().collect();
        spent.sort_unstable();
        w.len(spent.len());
        for position in spent {
            let record = &self.witness.spent[&position];
            w.u64(position);
            w.digest(&record.commitment);
            w.bytes(&memo_to_bytes(&record.memo));
            w.u64(record.amount);
            w.u32(record.height);
            self.witness.outputs.path(position).iter().for_each(|sibling| w.digest(sibling));
        }
        w.digest(&self.witness.outputs.leaf(self.next));
        self.witness.outputs.path(self.next).iter().for_each(|sibling| w.digest(sibling));
        // The names touched, ascending.
        let named = self.named();
        w.len(named.len());
        for key in named {
            w.bytes(&key.to_le_bytes());
            w.digest(&self.witness.names.leaf(key));
            self.witness.names.path(key).iter().for_each(|sibling| w.digest(sibling));
            match self.witness.records.get(&key) {
                None => w.bytes(&[0]),
                Some(record) => {
                    w.bytes(&[1]);
                    w.bytes(&record.to_bytes());
                }
            }
        }
        w.len(self.txs.len());
        for tx in &self.txs {
            let bytes = tx.to_bytes();
            w.len(bytes.len());
            w.bytes(&bytes);
        }
        w.len(self.sweeps.len());
        self.sweeps.iter().for_each(|position| w.u64(*position));
        w.bytes(&self.reward.to_bytes());
        w.finish()
    }

    /// The job `bytes` are. An error if they are not one whole: of
    /// another version, cut short, with something after, or with a path
    /// that does not lead to the root the job names. So a job read has
    /// the path of everything it says it spends, and proving it looks
    /// for none that is not there.
    pub fn from_bytes(bytes: &[u8]) -> Result<ProveJob, Error> {
        Self::decode(bytes).ok_or(Error::Malformed("job to prove"))
    }

    fn decode(bytes: &[u8]) -> Option<ProveJob> {
        let mut r = Reader(bytes);
        if r.take(1)? != [VERSION] {
            return None;
        }
        let program = r.digest()?;
        let parent = Header::from_bytes(r.take(HEADER_SIZE)?).ok()?;
        let before = match r.take(1)?[0] {
            0 => None,
            1 => {
                let stated = Statement::from_bytes(r.take(STATEMENT_BYTES)?)?;
                let len = r.len(1)?;
                Some((stated, r.take(len)?.to_vec()))
            }
            _ => return None,
        };
        let roots = (r.digest()?, r.digest()?);
        let (next, subsidy) = (r.u64()?, r.u64()?);
        let mut witness = Witness::default();
        let path = |r: &mut Reader| -> Option<[Digest; OUTPUTS_HEIGHT]> {
            let mut siblings = [EMPTY; OUTPUTS_HEIGHT];
            for sibling in &mut siblings {
                *sibling = r.digest()?;
            }
            Some(siblings)
        };
        // (A path is of the job's root, or the job is refused: the
        // paths then agree wherever they meet.)
        let leads = |position: u64, leaf: &Digest, siblings: &[Digest; OUTPUTS_HEIGHT]| {
            position >> OUTPUTS_HEIGHT == 0 && {
                let mut node = *leaf;
                for (level, sibling) in siblings.iter().enumerate() {
                    node = match position >> level & 1 {
                        1 => state_node(sibling, &node),
                        _ => state_node(&node, sibling),
                    };
                }
                node == roots.0
            }
        };
        for _ in 0..r.len(SPENT_BYTES)? {
            let position = r.u64()?;
            let record = crate::output::Record {
                commitment: r.digest()?,
                memo: memo_from_bytes(r.take(MEMO_BYTES)?).ok()?,
                amount: r.u64()?,
                height: r.u32()?,
            };
            let siblings = path(&mut r)?;
            if !leads(position, &record.leaf(), &siblings) || witness.spent.insert(position, record).is_some() {
                return None;
            }
            witness.outputs.load(position, &record.leaf(), &siblings);
        }
        let (leaf, siblings) = (r.digest()?, path(&mut r)?);
        if !leads(next, &leaf, &siblings) {
            return None;
        }
        witness.outputs.load(next, &leaf, &siblings);
        let mut named = BTreeSet::new();
        for _ in 0..r.len(NAMED_BYTES)? {
            let key = Key::from_le_bytes(r.take(16)?.try_into().ok()?);
            let leaf = r.digest()?;
            let siblings: Vec<Digest> = (0..crate::registry::HEIGHT).map(|_| r.digest()).collect::<Option<_>>()?;
            if crate::registry::path_root(&leaf, key, &siblings) != roots.1 || !named.insert(key) {
                return None;
            }
            witness.names.load(key, &leaf, &siblings);
            match r.take(1)?[0] {
                0 => {}
                1 => {
                    let (record, rest) = crate::name::Record::read(r.0)?;
                    r.0 = rest;
                    witness.records.insert(key, record);
                }
                _ => return None,
            }
        }
        let mut txs = Vec::new();
        for _ in 0..r.len(4)? {
            let len = r.len(1)?;
            txs.push(Transaction::from_bytes(r.take(len)?).ok()?);
        }
        let sweeps: Vec<u64> = (0..r.len(8)?).map(|_| r.u64()).collect::<Option<_>>()?;
        let reward = Output::from_bytes(r.take(OUTPUT_SIZE)?).ok()?;
        let job = ProveJob { program, parent, before, roots, next, subsidy, witness, txs, sweeps, reward };
        // What the transactions spend and touch is what the job has the
        // paths of, each of them.
        let spends = job.txs.iter().flat_map(|tx| {
            let reveals = tx.ops.iter().filter_map(|op| match op {
                crate::name::NameOp::Reveal { commit, .. } => Some(*commit),
                _ => None,
            });
            tx.spent_positions().into_iter().chain(reveals)
        });
        let held = spends.chain(job.sweeps.iter().copied()).all(|position| job.witness.spent.contains_key(&position));
        (r.end() && held && job.named() == named).then_some(job)
    }
}

/// A header to find the nonce of.
///
/// Its hash names it: a nonce found is found for that hash, and the
/// node knows which header of its own that is.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct HashJob {
    /// The header's height: which table its work is of
    /// ([`crate::pow::PowParams::log_items_at`]).
    pub height: u32,
    /// The hash the work is of ([`Header::pow_hash`]).
    pub hash: Digest,
    /// What the work's result is to meet.
    pub target: Target,
}

impl HashJob {
    pub fn to_json(&self) -> Json {
        Json::object([
            ("height", Json::int(self.height)),
            ("hash", Json::hex(&self.hash)),
            ("target", Json::hex(&self.target.0)),
        ])
    }

    pub fn from_json(json: &Json) -> Option<HashJob> {
        Some(HashJob {
            height: u32::try_from(json.get("height")?.as_u64()?).ok()?,
            hash: json.get("hash")?.as_hex()?,
            target: Target(json.get("target")?.as_hex()?),
        })
    }

    /// Looks for the job's nonce in `dataset`, which is the table of
    /// its height, from `start` ([`solve`]).
    pub fn solve<S: ItemSource + Sync>(
        &self,
        dataset: &S,
        start: u64,
        cancel: &(dyn Fn() -> bool + Sync),
    ) -> Option<(Found, u64)> {
        let (nonce, mix, tried) = solve(dataset, &self.hash, &self.target, start, cancel)?;
        Some((Found { hash: self.hash, nonce, mix }, tried))
    }
}

/// A nonce found, for the header of a [`HashJob`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Found {
    /// The job's hash.
    pub hash: Digest,
    pub nonce: Nonce,
    /// The mix that goes in the header beside the nonce.
    pub mix: Digest,
}

impl Found {
    pub fn to_json(&self) -> Json {
        Json::object([
            ("hash", Json::hex(&self.hash)),
            ("nonce", Json::hex(&self.nonce)),
            ("mix", Json::hex(&self.mix)),
        ])
    }

    pub fn from_json(json: &Json) -> Option<Found> {
        Some(Found {
            hash: json.get("hash")?.as_hex()?,
            nonce: json.get("nonce")?.as_hex()?,
            mix: json.get("mix")?.as_hex()?,
        })
    }

    /// Whether what was found is `job`'s, and claims work that meets
    /// its target: by the mix it says, which costs a hash to look at
    /// and is not yet shown to be the work's ([`crate::pow::verify`],
    /// which whoever takes the block does).
    pub fn claims(&self, job: &HashJob) -> bool {
        self.hash == job.hash && job.target.is_met_by(&result_from_mix(&self.hash, &self.nonce, &self.mix))
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

#[cfg(test)]
mod tests {
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

    /// The job of a chain's first block, of its reward alone: nothing
    /// spent, no name touched, and the path of the first position in a
    /// state of nothing.
    fn first_block() -> ProveJob {
        let empty = crate::ledger::empty_roots();
        let mut witness = Witness::default();
        witness.outputs.load(0, &EMPTY, empty[..OUTPUTS_HEIGHT].try_into().unwrap());
        let parent = Header {
            prev_hash: [1; 32],
            height: 0,
            timestamp: 1_700_000_000,
            body_commitment: [2; 32],
            state_root: [3; 32],
            statement: [4; 32],
            aux: [5; 32],
            mix: [6; 32],
            nonce: [7; 32],
        };
        ProveJob {
            program: [8; 32],
            parent,
            before: None,
            roots: (empty[OUTPUTS_HEIGHT], crate::registry::empty_roots()[crate::registry::HEIGHT]),
            next: 0,
            subsidy: 5_000_000_000,
            witness,
            txs: vec![],
            sweeps: vec![],
            reward: Output::to_key_hash(&[9; 32], 5_000_000_000),
        }
    }

    /// A job is its bytes, and bytes that are not a job, whole, are
    /// refused: another version, any part of one, one with something
    /// after it, and one whose path leads to another root than it
    /// names. (A job that spends is made by a node, and is read back in
    /// the node's tests.)
    #[test]
    fn a_job_to_prove_is_read_back_from_its_bytes() {
        let job = first_block();
        let bytes = job.to_bytes();
        let read = ProveJob::from_bytes(&bytes).unwrap();
        assert_eq!(read.to_bytes(), bytes);
        assert_eq!((read.program, read.parent, read.roots), (job.program, job.parent, job.roots));
        assert_eq!((read.next, read.subsidy, read.reward), (0, 5_000_000_000, job.reward));
        assert_eq!((read.height(), read.start()), (1, job.start()));
        assert_eq!(read.start().sum_in, 5_000_000_000);
        // With the proof before, and what it stated.
        let stated = Statement {
            height: 7,
            next: 9,
            sum_in: u128::MAX - 1,
            grows: u32::MAX,
            program: [8; 32],
            ..Statement::genesis()
        };
        assert_eq!(Statement::from_bytes(&stated.to_bytes()), Some(stated));
        assert_eq!(Statement::from_bytes(&stated.to_bytes()[1..]), None);
        let after = ProveJob { before: Some((stated, vec![1, 2, 3])), ..job.clone() };
        let read = ProveJob::from_bytes(&after.to_bytes()).unwrap();
        assert_eq!(read.before, Some((stated, vec![1, 2, 3])));
        assert_eq!(read.to_bytes(), after.to_bytes());

        let refused = |bytes: &[u8]| ProveJob::from_bytes(bytes).err() == Some(Error::Malformed("job to prove"));
        assert!((0..bytes.len()).all(|n| refused(&bytes[..n])));
        assert!(refused(&[&bytes[..], &[0]].concat()));
        let mut other = bytes.clone();
        other[0] = VERSION + 1;
        assert!(refused(&other));
        // The last sibling of the first position's path.
        let mut other = bytes.clone();
        let at = other.len() - OUTPUT_SIZE - 4 - 4 - 4 - 1;
        other[at] ^= 1;
        assert!(refused(&other));
        // A list said to be longer than the bytes left could hold.
        let mut other = bytes.clone();
        let at = other.len() - OUTPUT_SIZE - 4;
        other[at..at + 4].copy_from_slice(&u32::MAX.to_le_bytes());
        assert!(refused(&other));
    }

    /// A job to find a nonce is JSON, and so is what is found: a nonce
    /// found is taken as the job's if it is of its hash and claims work
    /// that meets its target.
    #[test]
    fn a_nonce_is_found_for_a_job_and_claimed() {
        let seed = crate::pow::SeedText::new(crate::pow::PowParams::DEV);
        let table = crate::pow::Dataset::generate(&seed, 10);
        // A target that one hash in sixteen or so meets.
        let mut target = Target([0xff; 32]);
        (target.0[30], target.0[31]) = (0x0f, 0);
        let job = HashJob { height: 3, hash: [5; 32], target };
        assert_eq!(HashJob::from_json(&Json::read(job.to_json().write().as_bytes()).unwrap()), Some(job));
        assert_eq!(HashJob::from_json(&Json::object([("height", Json::int(3))])), None);
        let (found, tried) = job.solve(&table, 100, &|| false).unwrap();
        assert!(tried >= 1 && found.claims(&job));
        assert!(crate::pow::verify(&table, &job.hash, &found.nonce, &found.mix, &job.target));
        assert_eq!(Found::from_json(&Json::read(found.to_json().write().as_bytes()).unwrap()), Some(found));
        // Another job's, another nonce, another mix: not this job's.
        assert!(!found.claims(&HashJob { hash: [6; 32], ..job }));
        assert!(!Found { hash: [6; 32], ..found }.claims(&job));
        // A mix that is not the work's may claim as much: a claim costs a
        // hash to look at, and the work itself is what shows it false.
        let mut false_claim = Found { mix: [0; 32], hash: found.hash, nonce: found.nonce };
        while !false_claim.claims(&job) {
            false_claim.mix[0] += 1;
        }
        assert!(!crate::pow::verify(&table, &job.hash, &false_claim.nonce, &false_claim.mix, &job.target));
        // A target nothing meets: looked for until told.
        let asked = AtomicU64::new(0);
        let cancel = || asked.fetch_add(1, Ordering::Relaxed) >= 3;
        assert!(HashJob { target: Target([0; 32]), ..job }.solve(&table, 7, &cancel).is_none());
    }
}
