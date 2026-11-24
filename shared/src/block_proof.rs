//! A block's proof: the proofs of its parts, joined into one that says
//! what the block did.
//!
//! | part | proves | by |
//! |---|---|---|
//! | runs of transactions | the state's change, given a signed set | [`crate::segment`] |
//! | signatures | the signed set | [`crate::signature`], [`crate::signed`] |
//! | joins | two runs, one after the other, are one run | [`join_into`] |
//! | nodes of signatures | two signed sets are one | [`crate::signature::node_into`] |
//! | work | the work of the header before the block's | [`crate::work`] |
//! | signatures and work | both, in one proof for the root to verify | [`beside_into`] |
//! | the root | the runs are the whole block's, of this signed set, after that work | [`root_into`] |
//!
//! Each join and the root are compiled computations
//! ([`crate::alg`]): they verify their children's proofs by rows of the
//! hash table and the machine, and state what the children were of.
//!
//! # What a block's proof is of
//!
//! [`Statement`]: the state's root before and after, the running hashes
//! of the positions spent, of the outputs made and of the operations
//! on names (which a node computes from the block's lists), the
//! positions given out, the height, and what the inputs and the outputs
//! came to. The root finds
//! the runs to begin from nothing (no transaction in hand, the running
//! hashes at their start, the sums at zero) and to end with every
//! transaction whole.
//!
//! The root also states which programs the proofs under it were of
//! ([`PROGRAMS`]), for a chain to hold against the shapes it takes
//! ([`crate::chain_proof::Plan`]), and the header whose work it was shown
//! ([`crate::header`]), for a chain's step to find to be its own.

use crate::alg::{Alg, halves};
use crate::circuit::Circuit;
use crate::field::F;
use crate::hash::{DOM_RESTED, Digest};
use crate::ledger::Record;
use crate::proof::{Circuits, Proved};
use crate::segment::{self, CHAINED, FIXED};
use crate::signature::Signed;
use crate::signed;
use crate::structure::Reader;
use crate::sym::{Shared, Sym};

/// The circuits a block's proofs are of.
pub struct Tables {
    pub compiled: Circuits,
    pub segment: Circuit,
}

impl Default for Tables {
    fn default() -> Tables {
        Tables::new()
    }
}

impl Tables {
    pub fn new() -> Tables {
        Tables { compiled: Circuits::new(), segment: segment::circuit() }
    }

    pub fn all(&self) -> Vec<&Circuit> {
        self.compiled.all().into_iter().chain([&self.segment]).collect()
    }
}

/// A proof of runs: of one run, or of two joined, with what that proof
/// states (the run table's program, what the join rested on, then the
/// record).
pub enum Runs<'a> {
    One(&'a segment::Proved),
    Joined(&'a Proved, &'a [F]),
}

/// The elements public words are.
pub fn elements(words: &[u32]) -> Vec<F> {
    words.chunks(4).map(|w| F(w.iter().rev().fold(0, |x, w| x << 32 | *w as u128))).collect()
}

/// What a proof of runs rests on, as a circuit that verified it holds
/// it: the run table's program; the proof's own program if it is a
/// join's (zeros if not); and what that join rested on in turn.
struct Rested {
    table: Vec<Sym>,
    own: Vec<Sym>,
    below: Vec<Sym>,
}

impl Runs<'_> {
    /// The proof's verification, made rows of `cx`: what it rests on,
    /// and the record.
    fn verify_into(&self, cx: &Shared, tables: &Tables, reader: &mut impl Reader<Sym>) -> Option<(Rested, Vec<Sym>)> {
        let zeros = || vec![cx.constant(F::ZERO), cx.constant(F::ZERO)];
        match self {
            Runs::One(p) => {
                let (table, record) = p.verify_into(cx, &tables.segment, reader)?;
                Some((Rested { table, own: zeros(), below: zeros() }, record))
            }
            Runs::Joined(p, stated) => {
                let of = p.verify_into(cx, &tables.compiled, reader)?;
                let mut said = cx.stated(&[of[2].clone(), of[3].clone()], stated);
                let record = said.split_off(4);
                let below = said.split_off(2);
                Some((Rested { table: said, own: of[..2].to_vec(), below }, record))
            }
        }
    }
}

/// A computation, in `cx`, that verifies two proofs of runs and states
/// them to be one run: what it states, by the field. That is the run
/// table's program, the hash of what its two children were proofs of
/// (their own programs, and what those rested on), and the record.
pub fn join_into(cx: &Shared, tables: &Tables, reader: &mut impl Reader<Sym>, children: [&Runs; 2]) -> Option<Vec<F>> {
    let (a, first) = children[0].verify_into(cx, tables, reader)?;
    let (b, second) = children[1].verify_into(cx, tables, reader)?;
    // Both rest on the one run table.
    assert!(a.table[0].is(&b.table[0]) && a.table[1].is(&b.table[1]));
    let below = cx.hashed(DOM_RESTED, &[a.own, a.below, b.own, b.below].concat());
    let stated = [a.table, below.to_vec(), segment::join(&first, &second)].concat();
    cx.state(&stated);
    Some(stated.iter().map(Sym::value).collect())
}

/// Digests of programs a block's root states before the statement.
pub const PROGRAMS: usize = 6;
/// Elements of a [`Statement`].
pub const STATEMENT: usize = 30;

/// What a block's proof is of.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Statement {
    /// The outputs' root before the block and after.
    pub root: [Digest; 2],
    /// The running hashes of the positions spent and of the outputs
    /// made, each from [`EMPTY`].
    pub inputs: Digest,
    pub outputs: Digest,
    /// The first position given out, and the one after the last.
    pub next: [u64; 2],
    pub height: u32,
    /// What the inputs and the subsidy came to, and the outputs: the
    /// same, which is the rule.
    pub sum_in: u128,
    pub sum_out: u128,
    /// What the block pays its maker.
    pub subsidy: u64,
    /// The registry's root before the block and after.
    pub names: [Digest; 2],
    /// The running hash of the operations on names, from [`EMPTY`]:
    /// those the transactions carried, which are those done.
    pub ops: Digest,
    /// The signed set the inputs' keys are found to have signed in.
    pub signed: Digest,
    /// The work shown of the header before this block's: that header's
    /// work's hash, its nonce and its mix. Zeros if none is shown.
    pub work: [Digest; 3],
    /// The size of the table that work is of, as the mask of a pair's
    /// index ([`crate::work::pairs_mask`]). Zero if none is shown.
    pub table: u32,
}

impl Statement {
    /// The statement of a block that is `record` ([`Record::block`]),
    /// from the ledger's rules, paying `subsidy`, with the signed set of
    /// root `signed`.
    pub fn of(record: &Record, subsidy: u64, signed: &Digest) -> Statement {
        Statement {
            root: record.root,
            inputs: record.inputs[1],
            outputs: record.outputs[1],
            next: record.next,
            height: record.height,
            sum_in: record.sum_in,
            sum_out: record.sum_out,
            subsidy,
            names: record.names,
            ops: record.done[1],
            signed: *signed,
            work: [[0; 32]; 3],
            table: 0,
        }
    }

    /// The statement as the elements a proof states.
    pub fn elements(&self) -> Vec<F> {
        let pairs = [&self.root[0], &self.root[1], &self.inputs, &self.outputs, &self.signed];
        let mut out: Vec<F> = pairs.into_iter().flat_map(halves).collect();
        out.extend([
            F(self.next[0] as u128),
            F(self.next[1] as u128),
            F(self.height as u128),
            F(self.sum_in),
            F(self.sum_out),
            // The height before, which a chain's step finds to be the
            // block before's.
            F(self.height.wrapping_sub(1) as u128),
            F(self.subsidy as u128),
        ]);
        out.extend(self.names.iter().flat_map(halves));
        out.extend(halves(&self.ops));
        out.extend(self.work.iter().flat_map(halves));
        out.push(F(self.table as u128));
        out
    }
}

/// A proof of a header's work ([`crate::work::work_into`]), with what it
/// states: the header's work's hash, the nonce, the mix and the result.
pub struct Worked<'a> {
    pub proof: &'a Proved,
    pub stated: &'a [F],
}

/// A computation, in `cx`, that verifies the proof of a block's runs,
/// of its signatures (none for a block that spends nothing) and of the
/// work of the header before it (none only for a block no chain takes),
/// and states what the block did: the statement, as elements, after the
/// programs the proofs were verified against: [`PROGRAMS`] digests, the
/// run table's, the join's and what it rested on (zeros if the runs are
/// one), the signatures' proof's and what that rested on (zeros if
/// there are none; the second zeros if it is of one run of signatures),
/// and the work's (zeros if none is shown).
pub fn root_into(
    cx: &Shared,
    tables: &Tables,
    reader: &mut impl Reader<Sym>,
    runs: &Runs,
    signatures: Option<&Signed>,
    work: Option<&Worked>,
    height: u32,
) -> Option<Vec<F>> {
    root_with(cx, tables, reader, runs, &Beside::Apart(signatures, work), height)
}

/// What a block's root has beside its runs: the proof of its
/// signatures and the proof of the work, each if there is one; or one
/// proof that verified both ([`beside_into`]), with what it states.
pub enum Beside<'a> {
    Apart(Option<&'a Signed<'a>>, Option<&'a Worked<'a>>),
    Joined(&'a Proved, &'a [F]),
}

/// Elements a proof of signatures and work together states: the hash of
/// what it rested on, the signatures' root and its level, and the
/// work's header's hash, nonce and mix.
pub const BESIDE: usize = 12;

/// A computation, in `cx`, that verifies a proof of signatures and a
/// proof of a header's work and states both: so that a root has one
/// proof to verify beside its runs, and not two. What it states, by
/// the field: the hash of the programs the two were of and what the
/// signatures' rested on, then what they were of.
pub fn beside_into(
    cx: &Shared,
    tables: &Tables,
    reader: &mut impl Reader<Sym>,
    signatures: &Signed,
    work: &Worked,
) -> Option<Vec<F>> {
    let v = signatures.verify_into(cx, &tables.compiled, reader)?;
    let of = work.proof.verify_into(cx, &tables.compiled, reader)?;
    let said = cx.stated(&[of[2].clone(), of[3].clone()], work.stated);
    let below = cx.hashed(DOM_RESTED, &[v.own, v.below, of[..2].to_vec()].concat());
    // (Of the work: the header's work's hash, the nonce, the mix, and
    // the table's size; not the result, which the header says.)
    let stated = [below.to_vec(), v.root.to_vec(), vec![v.level], said[..6].to_vec(), vec![said[8].clone()]].concat();
    cx.state(&stated);
    Some(stated.iter().map(Sym::value).collect())
}

/// [`root_into`], with what is beside the runs as one proof or as two.
/// Of one, the root states its program and what it rested on where it
/// states the signatures' proof's, and zeros for the work's.
pub fn root_with(
    cx: &Shared,
    tables: &Tables,
    reader: &mut impl Reader<Sym>,
    runs: &Runs,
    beside: &Beside,
    height: u32,
) -> Option<Vec<F>> {
    let (rested, r) = runs.verify_into(cx, tables, reader)?;
    let (ins, outs) = r.split_at(CHAINED + FIXED);
    let mut programs = [rested.table, rested.own, rested.below].concat();
    let zeros = |n: usize| (0..n).map(|_| cx.constant(F::ZERO));
    // The signed set, lifted from the level its root is said to be of
    // to the set's height (or the set of nothing); and the work of the
    // header before: what its proof states it is of.
    let lifted = |root: &[Sym; 2], level: &Sym, from: usize| {
        assert!(from <= signed::DEPTH && level.is(&cx.constant(crate::signature::level_element(from))));
        signed::lift_into(cx, root, from, signed::DEPTH)
    };
    let nothing = || halves(&signed::empty_roots()[signed::DEPTH]).map(|x| cx.constant(x));
    let (set, worked): ([Sym; 2], Vec<Sym>) = match beside {
        Beside::Apart(signatures, work) => {
            let set = match signatures {
                Some(s) => {
                    let v = s.verify_into(cx, &tables.compiled, reader)?;
                    programs.extend(v.own.into_iter().chain(v.below));
                    lifted(&v.root, &v.level, s.root().1)
                }
                None => {
                    programs.extend(zeros(4));
                    nothing()
                }
            };
            let worked = match work {
                Some(w) => {
                    let of = w.proof.verify_into(cx, &tables.compiled, reader)?;
                    let said = cx.stated(&[of[2].clone(), of[3].clone()], w.stated);
                    programs.extend(of[..2].iter().cloned());
                    said[..6].iter().chain(&said[8..9]).cloned().collect()
                }
                None => {
                    programs.extend(zeros(2));
                    zeros(7).collect()
                }
            };
            (set, worked)
        }
        Beside::Joined(proof, stated) => {
            if stated.len() != BESIDE {
                return None;
            }
            let of = proof.verify_into(cx, &tables.compiled, reader)?;
            let said = cx.stated(&[of[2].clone(), of[3].clone()], stated);
            programs.extend(of[..2].iter().chain(&said[..2]).cloned().chain(zeros(2)));
            let level = (0..=signed::DEPTH).find(|l| crate::signature::level_element(*l) == stated[4])?;
            (lifted(&[said[2].clone(), said[3].clone()], &said[4], level), said[5..].to_vec())
        }
    };
    assert!(ins[CHAINED].is(&set[0]) && ins[CHAINED + 1].is(&set[1]));
    // The runs begin from nothing: the running hashes at their start,
    // no transaction in hand, no outputs yet; the inputs' sum begins
    // from the subsidy, and ends as the outputs': the block's inputs
    // and what it pays come to what it makes.
    let zero = cx.constant(F::ZERO);
    // No operation on names carried or done yet, and transactions
    // still to come; at the end those done are those carried.
    for x in ins[2..10].iter().chain(&ins[13..14]).chain(&ins[17..CHAINED]) {
        assert!(x.is(&zero));
    }
    assert!(outs[12].is(&outs[13]));
    assert!(outs[17].is(&outs[19]) && outs[18].is(&outs[20]));
    // No operation on names yet: each count's bit at its start.
    assert!(ins[16].is(&cx.constant(F(1 | 1 << 32 | 1 << 64 | 1 << 96))));
    // And end with every transaction whole: its body's hash its id, and
    // nothing left. The height is the element above the two counters.
    let h = cx.input(F(height as u128));
    let counts = h.clone() * cx.constant(F(1 << 64));
    assert!(ins[10].is(&counts) && outs[10].is(&counts));
    assert!(outs[6].is(&outs[8]) && outs[7].is(&outs[9]));
    // No output conditions are on is still to come.
    assert!(outs[26].is(&zero));
    let mut stated = programs;
    stated.extend(ins[..2].iter().chain(&outs[..2]).chain(&outs[2..6]).chain(&set).cloned());
    let before = ins[CHAINED + 2].clone();
    stated.extend([ins[11].clone(), outs[11].clone(), h, outs[12].clone(), outs[13].clone(), before, ins[12].clone()]);
    stated.extend(ins[14..16].iter().chain(&outs[14..16]).chain(&outs[19..21]).cloned());
    stated.extend(worked);
    cx.state(&stated);
    Some(stated.iter().map(Sym::value).collect())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::alg::statement;
    use crate::hash::EMPTY;
    use crate::ledger::{Input, MEMO, Output, Outputs, Transaction, key_hash};
    use crate::pcs::Params;
    use crate::reading::Deferred;
    use crate::segment::{Run, closed};
    use crate::xmss::{SecretKey, Signature};

    fn params(m: usize) -> Params {
        Params::plain(m, 1, 4, 4)
    }

    /// The signed set over a signature proof's entries, the rest empty:
    /// an entry's siblings to the set's root.
    fn path(entries: &[Digest], place: usize) -> Vec<Digest> {
        let mut leaves = entries.to_vec();
        leaves.resize(signed::SLOTS, EMPTY);
        let mut siblings = signed::Tree::new(&leaves).path(place).siblings;
        siblings.extend_from_slice(&signed::empty_roots()[signed::LOG_SLOTS..signed::DEPTH]);
        siblings
    }

    /// The most memory the process has held, in megabytes; and the mark
    /// set back to what it holds now.
    fn peak() -> usize {
        let status = std::fs::read_to_string("/proc/self/status").unwrap_or_default();
        let kb =
            status.lines().find(|l| l.starts_with("VmHWM")).and_then(|l| l.split_whitespace().nth(1)?.parse().ok());
        let _ = std::fs::write("/proc/self/clear_refs", "5");
        kb.unwrap_or(0usize) / 1024
    }

    /// What a block of payments costs under its chain's step, at the
    /// chain's parameters: `TXS` payments (16 if not said) of two
    /// inputs and two outputs each, their signatures in one proof, the
    /// payments in one run, the work of a header, and the root over
    /// the three.
    #[test]
    #[ignore = "timing; run with --release --nocapture"]
    fn payments_block_timing() {
        use std::time::Instant;
        let params = |m: usize| Params::proven(m, 2, crate::pcs::SECURITY);
        let count: usize = std::env::var("TXS").ok().and_then(|n| n.parse().ok()).unwrap_or(16);
        assert!(2 * count <= signed::SLOTS, "signatures for one proof");
        let mut keys: Vec<SecretKey> = (0..2 * count)
            .map(|i| SecretKey::generate_with_height(&[i as u8, (i >> 8) as u8 + 1].repeat(16).try_into().unwrap(), 2))
            .collect();
        let mut state = Outputs::default();
        let owned: Vec<Input> = (keys.iter().enumerate())
            .map(|(i, sk)| {
                let (key, memo) = (sk.public_key(), [i as u8; MEMO]);
                let position = state.insert(&Output::to(&key_hash(&key), 100, memo), 1);
                Input { key, amount: 100, memo, created: 1, position }
            })
            .collect();
        let to = key_hash(&owned[0].key);
        let txs: Vec<Transaction> = (0..count)
            .map(|t| Transaction {
                inputs: vec![owned[2 * t].clone(), owned[2 * t + 1].clone()],
                outputs: vec![Output::to(&to, 150, [9; MEMO]), Output::to(&to, 50, [8; MEMO])],
                ops: vec![],
                policy: vec![],
                covered: 0,
            })
            .collect();
        let height = 2;
        let mut signatures: Vec<(crate::xmss::PublicKey, Digest, Signature)> = Vec::new();
        for (t, tx) in txs.iter().enumerate() {
            for k in [2 * t, 2 * t + 1] {
                let sig = keys[k].sign(&tx.id()).unwrap();
                signatures.push((keys[k].public_key(), tx.id(), sig));
            }
        }
        let entries: Vec<Digest> =
            signatures.iter().map(|(pk, msg, sig)| crate::signature::entry(pk, msg, sig.index)).collect();
        let shape = |p: &Proved| format!("2^{} elements, {:?}", p.params.m, p.tables);
        peak();
        let t = Instant::now();
        let cx = Shared::new();
        let mut chains = Vec::new();
        let entries_root = crate::signature::segment_into(&cx, &mut chains, &signatures, 64).unwrap();
        let signed_proof = crate::proof::prove(cx, chains, params);
        println!(
            "{} signatures: {:.2?}, {} MB, {} KB, {}",
            signatures.len(),
            t.elapsed(),
            peak(),
            signed_proof.size() / 1000,
            shape(&signed_proof)
        );
        let set = signed::lift(&entries_root, signed::LOG_SLOTS, signed::DEPTH);

        let t = Instant::now();
        let start = Record::block(&state, height, 0);
        let mut run = Run::new(&start, closed(), &set);
        let spent = |txs: &[Transaction]| -> Vec<u64> {
            txs.iter().flat_map(|tx| tx.inputs.iter().map(|i| i.position)).collect()
        };
        run.frontier(&state.frontier_without(spent(&txs)));
        // The tree as the run has it: without the outputs it makes.
        let mut tree = state.clone();
        let mut entry = 0;
        for tx in &txs {
            run.head(tx);
            for input in &tx.inputs {
                let at = (entry as u64, path(&entries, entry));
                run.input(input, &tree.path(input.position), signatures[entry].2.index, &at);
                tree.set(input.position, EMPTY);
                state.set(input.position, EMPTY);
                entry += 1;
            }
            for output in &tx.outputs {
                run.output(output, &to);
                state.insert(output, height);
            }
        }
        let run = segment::prove(run, 512, params);
        println!(
            "{count} payments in a run: {:.2?}, {} MB, {} KB, 2^{} elements",
            t.elapsed(),
            peak(),
            run.proof.size() / 1000,
            run.params.m
        );

        let t = Instant::now();
        let text = crate::pow::SeedText::new(crate::pow::PowParams::MAINNET);
        let source = text.table(crate::pow::PowParams::MAINNET.log_dataset_items);
        let cx = Shared::new();
        let (work, worked) = crate::work::work_into(&cx, &source, &[5; 32], &crate::pow::nonce_from_u64(1));
        let work = crate::proof::prove_with(cx, vec![], Some(work), params, [128, 128]);
        println!("work: {:.2?}, {} MB, {} KB", t.elapsed(), peak(), work.size() / 1000);

        let t = Instant::now();
        let tables = Tables::new();
        let cx = Shared::new();
        let mut reader = Deferred::new(&cx);
        let signatures = Signed::Segment(&signed_proof, entries_root);
        let shown = Worked { proof: &work, stated: &worked };
        let both = beside_into(&cx, &tables, &mut reader, &signatures, &shown).unwrap();
        reader.settle(&tables.all());
        let (hash, ops) = cx.with(|c| (c.trace.rows.len(), c.asm.finish_len()));
        let beside = crate::proof::prove(cx, vec![], params);
        assert!(beside.holds && beside.verifies());
        println!(
            "signatures and work as one: {:.2?}, {} MB, {} KB, {}; {hash} hash rows, {} machine rows used ({ops} operations)",
            t.elapsed(),
            peak(),
            beside.size() / 1000,
            shape(&beside),
            beside.used
        );

        let t = Instant::now();
        let cx = Shared::new();
        let mut reader = Deferred::new(&cx);
        root_with(&cx, &tables, &mut reader, &Runs::One(&run), &Beside::Joined(&beside, &both), height).unwrap();
        reader.settle(&tables.all());
        let (hash, ops) = cx.with(|c| (c.trace.rows.len(), c.asm.finish_len()));
        let root = crate::proof::prove(cx, vec![], params);
        assert!(root.holds && root.verifies());
        println!(
            "the root over the two: {:.2?}, {} MB, {} KB, {}; {hash} hash rows, {} machine rows used ({ops} operations)",
            t.elapsed(),
            peak(),
            root.size() / 1000,
            shape(&root),
            root.used
        );
    }

    #[test]
    #[cfg_attr(debug_assertions, ignore = "slow unoptimized")]
    fn a_block_of_payments_is_proven_from_its_signatures_up() {
        // Three keys own an output each; two payments spend them, each
        // input signed by its key over the payment's id.
        let mut keys: Vec<SecretKey> = (0..3u8).map(|i| SecretKey::generate_with_height(&[i + 1; 32], 2)).collect();
        let mut state = Outputs::default();
        let owned: Vec<Input> = (keys.iter().enumerate())
            .map(|(i, sk)| {
                let (key, memo) = (sk.public_key(), [i as u8; MEMO]);
                let position = state.insert(&Output::to(&key_hash(&key), 100, memo), 1);
                Input { key, amount: 100, memo, created: 1, position }
            })
            .collect();
        let to = key_hash(&owned[0].key);
        let pay = |inputs: &[usize], amounts: &[u64]| Transaction {
            inputs: inputs.iter().map(|i| owned[*i].clone()).collect(),
            outputs: amounts.iter().map(|a| Output::to(&to, *a, [9; MEMO])).collect(),
            ops: vec![],
            policy: vec![],
            covered: 0,
        };
        let txs = [pay(&[0, 2], &[150, 50]), pay(&[1], &[130])];
        let height = 2;

        // The signatures, and the proof of them: its entries' root.
        let mut signatures: Vec<(crate::xmss::PublicKey, Digest, Signature)> = Vec::new();
        for (tx, spends) in txs.iter().zip([vec![0usize, 2], vec![1]]) {
            for k in spends {
                let sig = keys[k].sign(&tx.id()).unwrap();
                signatures.push((keys[k].public_key(), tx.id(), sig));
            }
        }
        let entries: Vec<Digest> =
            signatures.iter().map(|(pk, msg, sig)| crate::signature::entry(pk, msg, sig.index)).collect();
        let cx = Shared::new();
        let mut chains = Vec::new();
        let entries_root = crate::signature::segment_into(&cx, &mut chains, &signatures, 4).unwrap();
        let signed_proof = crate::proof::prove(cx, chains, params);
        assert!(signed_proof.holds && signed_proof.verifies());
        let set = signed::lift(&entries_root, signed::LOG_SLOTS, signed::DEPTH);

        // The runs: the first payment, then the second, each its proof.
        // The block pays 30: its outputs come to its inputs and that.
        let start = Record::block(&state, height, 30);
        let mut record = start;
        let mut run = Run::new(&start, closed(), &set);
        let spent = |txs: &[Transaction]| -> Vec<u64> {
            txs.iter().flat_map(|tx| tx.inputs.iter().map(|i| i.position)).collect()
        };
        run.frontier(&state.frontier_without(spent(&txs[..1])));
        // The tree as a run has it: without the outputs it makes.
        let mut tree = state.clone();
        let mut runs = Vec::new();
        let mut entry = 0;
        let mut applied = state.clone();
        for (t, tx) in txs.iter().enumerate() {
            if t == 1 {
                run.settle();
                let mut next = Run::after(&run);
                next.frontier(&state.frontier_without(spent(&txs[1..])));
                runs.push(std::mem::replace(&mut run, next));
                tree = state.clone();
            }
            run.head(tx);
            for input in &tx.inputs {
                run.input(
                    input,
                    &tree.path(input.position),
                    signatures[entry].2.index,
                    &(entry as u64, path(&entries, entry)),
                );
                tree.set(input.position, EMPTY);
                state.set(input.position, EMPTY);
                entry += 1;
            }
            for output in &tx.outputs {
                run.output(output, &to);
                state.insert(output, height);
            }
            record.apply(&mut applied, tx).unwrap();
        }
        runs.push(run);
        let proved: Vec<segment::Proved> = runs.into_iter().map(|r| segment::prove(r, 512, params)).collect();
        assert!(proved.iter().all(segment::Proved::verifies));

        // The join of the two runs, and the root over it and the
        // signatures.
        let tables = Tables::new();
        let cx = Shared::new();
        let mut reader = Deferred::new(&cx);
        let joined = join_into(&cx, &tables, &mut reader, [&Runs::One(&proved[0]), &Runs::One(&proved[1])]).unwrap();
        reader.settle(&tables.all());
        let join = crate::proof::prove(cx, vec![], params);
        assert!(join.holds && join.verifies());
        assert_eq!(join.statement(), statement(&joined));

        let cx = Shared::new();
        let mut reader = Deferred::new(&cx);
        let signatures = Signed::Segment(&signed_proof, entries_root);
        let stated =
            root_into(&cx, &tables, &mut reader, &Runs::Joined(&join, &joined), Some(&signatures), None, height)
                .unwrap();
        reader.settle(&tables.all());
        let root = crate::proof::prove(cx, vec![], params);
        assert!(root.holds && root.verifies());
        assert_eq!(root.statement(), statement(&stated));
        // What the block's proof is of is what the ledger's rules make of
        // the block: after the programs, the statement.
        let expect = Statement::of(&record, 30, &set);
        assert_eq!((record.sum_in, record.sum_out), (330, 330));
        assert_eq!((stated.len(), expect.elements().len()), (2 * PROGRAMS + STATEMENT, STATEMENT));
        assert_eq!(stated[2 * PROGRAMS..], expect.elements()[..]);
        assert_eq!(stated[..2], halves(&proved[0].program));
        assert_eq!(stated[2..4], halves(&join.program));

        // The same block with its signatures and the work of a header in
        // one proof: the root states the same of the block, and the work.
        let text = crate::pow::SeedText::new(crate::pow::PowParams::DEV);
        let source = text.table(10);
        let (header, nonce) = ([4u8; 32], crate::pow::nonce_from_u64(3));
        let cx = Shared::new();
        let (work, worked) = crate::work::work_into(&cx, &source, &header, &nonce);
        let work = crate::proof::prove_with(cx, vec![], Some(work), params, [128, 128]);
        let shown = Worked { proof: &work, stated: &worked };
        let cx = Shared::new();
        let mut reader = Deferred::new(&cx);
        let both = beside_into(&cx, &tables, &mut reader, &signatures, &shown).unwrap();
        reader.settle(&tables.all());
        let beside = crate::proof::prove(cx, vec![], params);
        assert!(beside.holds && beside.verifies() && both.len() == BESIDE);
        let cx = Shared::new();
        let mut reader = Deferred::new(&cx);
        let runs = Runs::Joined(&join, &joined);
        let one = root_with(&cx, &tables, &mut reader, &runs, &Beside::Joined(&beside, &both), height).unwrap();
        reader.settle(&tables.all());
        let root = crate::proof::prove(cx, vec![], params);
        assert!(root.holds && root.verifies());
        let mix = crate::pow::hashimoto(&source, &header, &nonce).mix;
        let table = crate::work::pairs_mask(crate::pow::ItemSource::log_items(&source));
        let with_work = Statement { work: [header, nonce, mix], table, ..expect };
        assert_eq!(one[2 * PROGRAMS..], with_work.elements()[..]);
        // It states the one proof's program where the signatures' was,
        // and what that rested on.
        assert_eq!((&one[6..8], &one[8..10]), (&halves(&beside.program)[..], &both[..2]));
        assert_eq!(one[10..12], [F::ZERO; 2]);
        // Another header's work said of this proof: no root.
        let mut other = both.clone();
        other[5] += F::ONE;
        let cx = Shared::new();
        let mut reader = Deferred::new(&cx);
        root_with(&cx, &tables, &mut reader, &runs, &Beside::Joined(&beside, &other), height);
        assert!(!cx.finish().asm.finish(128).holds);

        // A root at another height, or over runs that leave a
        // transaction in hand, does not hold.
        let cx = Shared::new();
        let mut reader = Deferred::new(&cx);
        root_into(&cx, &tables, &mut reader, &Runs::Joined(&join, &joined), Some(&signatures), None, height + 1);
        assert!(!cx.finish().asm.finish(128).holds);
        let cx = Shared::new();
        let mut reader = Deferred::new(&cx);
        root_into(&cx, &tables, &mut reader, &Runs::One(&proved[1]), Some(&signatures), None, height);
        assert!(!cx.finish().asm.finish(128).holds);
    }
}
