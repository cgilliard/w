//! Proving, as far as it is the node's: what a proof takes from the
//! state, which only the node has; and the tests of proofs against a
//! chain, which only the node keeps.
//!
//! Everything else of proving is `tabshared::prover`'s.

use crate::name::NameOp;
use crate::prover::Witness;
use crate::transaction::Transaction;
use tabshared::ledger::OUTPUTS_HEIGHT;

/// The witness of a block of `txs` and `sweeps` on the state of
/// `snap`. An error if the block cannot be: it spends what is not
/// there.
pub fn witness_of<B: crate::store::Backend + 'static>(
    snap: &crate::store::state::Snapshot<'_, B>,
    txs: &[Transaction],
    sweeps: &[u64],
) -> Result<Witness, crate::error::Error> {
    let mut witness = Witness::default();
    let reveals = |tx: &Transaction| -> Vec<u64> {
        let commits = tx.ops.iter().filter_map(|op| match op {
            NameOp::Reveal { commit, .. } => Some(*commit),
            _ => None,
        });
        commits.collect()
    };
    let spent = txs.iter().flat_map(|tx| tx.spent_positions().into_iter().chain(reveals(tx)));
    for position in spent.chain(sweeps.iter().copied()) {
        let record = match snap.output(position)? {
            Some((record, true)) => record,
            _ => return Err(crate::error::Error::NoSuchOutput(position)),
        };
        let (leaf, path) = snap.prove(position)?;
        witness.outputs.load(position, &leaf, path[..OUTPUTS_HEIGHT].try_into().expect("the outputs' levels"));
        witness.spent.insert(position, record);
    }
    let next = snap.outputs().next;
    let (leaf, path) = snap.prove(next)?;
    witness.outputs.load(next, &leaf, path[..OUTPUTS_HEIGHT].try_into().expect("the outputs' levels"));
    for op in txs.iter().flat_map(|tx| &tx.ops) {
        let Some(record) = op.record() else { continue };
        let key = record.key();
        let (proof, _) = snap.prove_name(key)?;
        witness.names.load(key, &proof.leaf, &proof.siblings);
        if let Some(old) = snap.name(key)? {
            witness.records.insert(key, old);
        }
    }
    Ok(witness)
}

#[cfg(test)]
pub(crate) mod tests {
    use super::*;
    use crate::block::{Block, BlockRef, Body, BodyRef, Header};
    use crate::chain::Chain;
    use crate::chain::apply::Applied;
    use crate::chain::headers::tests::{NOW, easy, seed, table};
    use crate::chain::params::ChainParams;
    use crate::error::Error;
    use crate::field::F;
    use crate::hash::{Digest, EMPTY};
    use crate::ledger::{Emission, Record};
    use crate::pcs::Params;
    use crate::pow::ItemSource;
    use crate::pow::hashimoto;
    use crate::prover::*;
    use crate::store::testing::MemBackend;

    /// A network of small proofs, on the dev table, whose every header
    /// meets its target: its setup, made once for every test, and its
    /// parameters.
    pub(crate) fn network() -> (&'static Setup, ChainParams) {
        static SETUP: std::sync::OnceLock<Setup> = std::sync::OnceLock::new();
        let setup = SETUP.get_or_init(|| Setup::new(Level::SMALL, Emission(easy().emission), &*table()));
        let params = ChainParams { program: setup.own, ..easy() };
        (setup, ChainParams { genesis_mix: None, ..params })
    }

    /// The header of a block of `body` on the chain's last, its work
    /// found.
    fn header_for(chain: &Chain<MemBackend, ChainVerifier>, body: &Body) -> Header {
        header_from(chain, body, &*table())
    }

    /// As [`header_for`], its work of the table `source`.
    fn header_from(chain: &Chain<MemBackend, ChainVerifier>, body: &Body, source: &impl ItemSource) -> Header {
        let parent = chain.tip().unwrap();
        let bytes = body.to_bytes();
        let (state_root, stated) = chain.header_after(&BodyRef::from_bytes(&bytes).unwrap()).unwrap();
        let mut header = Header {
            prev_hash: parent.hash(),
            height: parent.height + 1,
            timestamp: parent.timestamp + 600,
            body_commitment: body.commitment(),
            state_root,
            statement: stated.digest(),
            aux: [0; 32],
            mix: EMPTY,
            nonce: [0; 32],
        };
        let target = chain.expected_target(&parent).unwrap();
        loop {
            header.mix = hashimoto(source, &header.pow_hash(), &header.nonce).mix;
            if header.quick_pow_check(&target) {
                return header;
            }
            header.nonce[0] = header.nonce[0].wrapping_add(1);
        }
    }

    /// The proof of the next block of the chain, which pays `reward` and
    /// nothing else.
    fn prove_next(setup: &Setup, chain: &Chain<MemBackend, ChainVerifier>, reward: &crate::output::Output) -> Vec<u8> {
        prove_with(setup, chain, reward, &[], None).expect("a proof")
    }

    /// The proof of the next block of the chain, of `txs` and `reward`,
    /// if there is one.
    fn prove_with(
        setup: &Setup,
        chain: &Chain<MemBackend, ChainVerifier>,
        reward: &crate::output::Output,
        txs: &[Transaction],
        proven: Option<&SignedProof>,
    ) -> Option<Vec<u8>> {
        prove_from(setup, chain, &*table(), reward, txs, proven)
    }

    /// As [`prove_with`], the work of the table `source`.
    fn prove_from(
        setup: &Setup,
        chain: &Chain<MemBackend, ChainVerifier>,
        source: &impl ItemSource,
        reward: &crate::output::Output,
        txs: &[Transaction],
        proven: Option<&SignedProof>,
    ) -> Option<Vec<u8>> {
        let parent = chain.tip().unwrap();
        let state = chain.state();
        let snap = state.snapshot().unwrap();
        let (roots, next) = ((snap.outputs().hash(), snap.names().hash()), snap.outputs().next);
        // The chain's proof before: where a chain begins, or the one the
        // last block carried, which states what the chain says of it.
        let before = match parent.height {
            0 => setup.beginning(),
            _ => {
                let bytes = chain.body(&parent.hash()).unwrap().expect("the last block's body is kept");
                let body = BodyRef::from_bytes(&bytes).unwrap();
                let stated = chain.statement(parent.height, &parent.prev_hash, &body, &roots, next);
                assert_eq!(stated.digest(), parent.statement);
                setup.carried(body.proof(), &stated).unwrap()
            }
        };
        let height = parent.height + 1;
        let start = Record {
            root: [roots.0; 2],
            inputs: [EMPTY; 2],
            outputs: [EMPTY; 2],
            next: [next; 2],
            sum_in: chain.params().subsidy(height) as u128,
            sum_out: 0,
            height,
            names: [roots.1; 2],
            ops: [EMPTY; 2],
            done: [EMPTY; 2],
        };
        let witness = witness_of(&snap, txs, &[]).unwrap();
        let contents = Contents { txs, sweeps: &[], reward };
        setup.block(source, &parent, &before, &start, witness, &contents, proven)
    }

    /// Blocks that pay their reward, each carrying the chain's proof,
    /// are taken by a chain that checks it: from the first block, whose
    /// proof rests on where a chain begins, on.
    #[test]
    #[cfg_attr(debug_assertions, ignore = "slow unoptimized")]
    fn a_chain_takes_blocks_by_their_proofs() {
        let (setup, params) = network();
        let chain = Chain::open(MemBackend::new(), 8, params, seed(), setup.verifier()).unwrap();
        chain.set_dataset(table());
        let pay = |height: u32| crate::output::Output::to_key_hash(&[height as u8; 32], params.subsidy(height));
        let mut last = Vec::new();
        for height in 1..=3 {
            let reward = pay(height);
            let proof = prove_next(setup, &chain, &reward);
            let body = Body { outputs: vec![reward.block_output()], proof, ..Body::default() };
            let block = Block { header: header_for(&chain, &body), body };
            // With another proof, or the proof of the block before, it
            // is not taken; the block is not held to that.
            let mut other = block.clone();
            let at = other.body.proof.len() / 2;
            other.body.proof[at] ^= 1;
            let view = other.to_bytes();
            assert_eq!(chain.apply_block(&BlockRef::from_bytes(&view).unwrap(), NOW), Err(Error::BadProof));
            if !last.is_empty() {
                other.body.proof = std::mem::take(&mut last);
                let view = other.to_bytes();
                assert_eq!(chain.apply_block(&BlockRef::from_bytes(&view).unwrap(), NOW), Err(Error::BadProof));
            }
            let bytes = block.to_bytes();
            assert_eq!(chain.apply_block(&BlockRef::from_bytes(&bytes).unwrap(), NOW), Ok(Applied::Extended));
            assert_eq!(chain.tip().unwrap(), block.header);
            last = block.body.proof;
        }
        // A reward that is more than the block may pay has no proof.
        let greedy = crate::output::Output::to_key_hash(&[9; 32], params.subsidy(4) + 1);
        let parent = chain.tip().unwrap();
        let state = chain.state();
        let snap = state.snapshot().unwrap();
        let (roots, next) = ((snap.outputs().hash(), snap.names().hash()), snap.outputs().next);
        let bytes = chain.body(&parent.hash()).unwrap().unwrap();
        let body = BodyRef::from_bytes(&bytes).unwrap();
        let stated = chain.statement(parent.height, &parent.prev_hash, &body, &roots, next);
        let before = setup.carried(body.proof(), &stated).unwrap();
        let start = Record {
            root: [roots.0; 2],
            inputs: [EMPTY; 2],
            outputs: [EMPTY; 2],
            next: [next; 2],
            sum_in: params.subsidy(4) as u128,
            sum_out: 0,
            height: 4,
            names: [roots.1; 2],
            ops: [EMPTY; 2],
            done: [EMPTY; 2],
        };
        let witness = witness_of(&snap, &[], &[]).unwrap();
        let contents = Contents { txs: &[], sweeps: &[], reward: &greedy };
        assert!(setup.block(&*table(), &parent, &before, &start, witness, &contents, None).is_none());
    }

    /// A block of a payment: its signature proven beforehand, its input
    /// found in the signed set, its outputs made after the reward's. The
    /// chain takes it by its proof, and takes no other body with it.
    #[test]
    #[cfg_attr(debug_assertions, ignore = "slow unoptimized")]
    fn a_chain_takes_a_block_of_payments() {
        use crate::output::{Key, Output};
        use crate::transaction::UnsignedTransaction;
        let (setup, params) = network();
        let chain = Chain::open(MemBackend::new(), 8, params, seed(), setup.verifier()).unwrap();
        chain.set_dataset(table());
        let extend = |body: Body| {
            let block = Block { header: header_for(&chain, &body), body };
            let bytes = block.to_bytes();
            chain.apply_block(&BlockRef::from_bytes(&bytes).unwrap(), NOW)
        };
        // The first block pays a key, which the second block's payment
        // spends: half to one, the rest less a fee to another.
        let mut key = Key::generate(&[3; 32]);
        let first = Output::new(&key.public_key(), params.subsidy(1));
        let proof = prove_next(setup, &chain, &first);
        assert_eq!(
            extend(Body { outputs: vec![first.block_output()], proof, ..Body::default() }),
            Ok(Applied::Extended)
        );
        let (half, fee) = (first.amount / 2, 1000);
        let outputs =
            vec![Output::to_key_hash(&[1; 32], half), Output::to_key_hash(&[2; 32], first.amount - half - fee)];
        let tx = UnsignedTransaction::new(vec![(key.public_key(), first.amount)], outputs)
            .at(&[0])
            .sign_with(&mut key)
            .unwrap();
        let txs = [tx];
        // The signature is proven with no block in mind.
        let proven = setup.sign(&txs[0].signings()).unwrap();
        let reward = Output::to_key_hash(&[4; 32], params.subsidy(2) + fee);
        // A reward of more than the subsidy and the fee has no proof;
        // nor has the payment without its signature's proof.
        let greedy = Output::to_key_hash(&[4; 32], reward.amount + 1);
        assert!(prove_with(setup, &chain, &greedy, &txs, Some(&proven)).is_none());
        let other = setup.sign(&[(key.public_key(), [9; 32], key.sign(&[9; 32]).unwrap())]).unwrap();
        assert!(prove_with(setup, &chain, &reward, &txs, Some(&other)).is_none());
        let proof = prove_with(setup, &chain, &reward, &txs, Some(&proven)).unwrap();
        let listed: Vec<_> = [&reward].into_iter().chain(&txs[0].outputs).map(Output::block_output).collect();
        let body = Body { inputs: vec![0], outputs: listed, proof, ..Body::default() };
        // The proof is of this body: with its outputs in another order
        // it is another block's.
        let mut swapped = body.clone();
        swapped.outputs.swap(1, 2);
        assert_eq!(extend(swapped), Err(Error::BadProof));
        assert_eq!(extend(body), Ok(Applied::Extended));
        let state = chain.state();
        let snap = state.snapshot().unwrap();
        assert_eq!((snap.outputs().next, snap.is_unspent(0).unwrap(), snap.is_unspent(2).unwrap()), (4, false, true));
    }

    /// A setup's numbers are kept and read back; a setup made of them
    /// again is the same setup, and the verifier made of them alone
    /// takes the blocks it makes.
    #[test]
    #[cfg_attr(debug_assertions, ignore = "slow unoptimized")]
    fn a_setup_is_kept_and_made_again() {
        let (setup, params) = network();
        let parts = setup.parts();
        assert!(Parts::from_bytes(&parts.to_bytes()).as_ref() == Some(&parts));
        let bytes = parts.to_bytes();
        assert!(Parts::from_bytes(&bytes[..bytes.len() - 1]).is_none());
        assert!(Parts::from_bytes(&[&bytes[..], &[0]].concat()).is_none());
        let again = Setup::from_parts(Level::SMALL, Emission(params.emission), params.pow, &parts).unwrap();
        assert!(again.parts() == parts && again.own == setup.own);
        // Parts of another build's circuits: the proof of where a chain
        // begins is not of the program they say.
        let mut other = parts.clone();
        other.genesis = [1; 32];
        assert!(Setup::from_parts(Level::SMALL, Emission(params.emission), params.pow, &other).is_none());
        // A block made by the setup made again is taken by a chain that
        // has the verifier of the parts alone.
        let chain =
            Chain::open(MemBackend::new(), 8, params, seed(), ChainVerifier::of(&Level::SMALL, &parts)).unwrap();
        chain.set_dataset(table());
        let reward = crate::output::Output::to_key_hash(&[1; 32], params.subsidy(1));
        let proof = prove_next(&again, &chain, &reward);
        let body = Body { outputs: vec![reward.block_output()], proof, ..Body::default() };
        let block = Block { header: header_for(&chain, &body), body }.to_bytes();
        assert_eq!(chain.apply_block(&BlockRef::from_bytes(&block).unwrap(), NOW), Ok(Applied::Extended));
    }

    /// The main network's proofs, timed: the setup read back from its
    /// file, and two blocks of a reward made and taken, on the main
    /// network's table (its items made as they are asked for) with
    /// every header meeting its target.
    #[test]
    #[ignore = "timing; run with --release --nocapture, after the main network's setup is written"]
    fn main_network_block_timing() {
        use std::time::Instant;
        let bytes = std::fs::read("../resources/setup-mainnet.bin").unwrap();
        let parts = Parts::from_bytes(&bytes).unwrap();
        let text = crate::pow::SeedText::new(crate::pow::PowParams::MAINNET);
        let params = ChainParams {
            pow: crate::pow::PowParams::MAINNET,
            emission: ChainParams::MAINNET.emission,
            program: parts.own,
            ..easy()
        };
        let params = ChainParams { genesis_mix: None, ..params };
        let began = Instant::now();
        let setup = Setup::from_parts(Level::MAINNET, Emission(params.emission), params.pow, &parts).unwrap();
        println!("the setup, from its file: {:.1?}", began.elapsed());
        let chain =
            Chain::open(MemBackend::new(), 8, params, text, ChainVerifier::of(&Level::MAINNET, &parts)).unwrap();
        let source = text.at(0);
        for height in 1..=2u32 {
            let reward = crate::output::Output::to_key_hash(&[height as u8; 32], params.subsidy(height));
            let (parent, state) = (chain.tip().unwrap(), chain.state());
            let snap = state.snapshot().unwrap();
            let (roots, next) = ((snap.outputs().hash(), snap.names().hash()), snap.outputs().next);
            let began = Instant::now();
            let before = match parent.height {
                0 => setup.beginning(),
                _ => {
                    let bytes = chain.body(&parent.hash()).unwrap().unwrap();
                    let body = BodyRef::from_bytes(&bytes).unwrap();
                    let stated = chain.statement(parent.height, &parent.prev_hash, &body, &roots, next);
                    setup.carried(body.proof(), &stated).unwrap()
                }
            };
            let start = Record {
                root: [roots.0; 2],
                inputs: [EMPTY; 2],
                outputs: [EMPTY; 2],
                next: [next; 2],
                sum_in: params.subsidy(height) as u128,
                sum_out: 0,
                height,
                names: [roots.1; 2],
                ops: [EMPTY; 2],
                done: [EMPTY; 2],
            };
            let witness = witness_of(&snap, &[], &[]).unwrap();
            let contents = Contents { txs: &[], sweeps: &[], reward: &reward };
            let proof = setup.block(&source, &parent, &before, &start, witness, &contents, None).unwrap();
            println!("block {height}: proved in {:.1?}, a proof of {} bytes", began.elapsed(), proof.len());
            let body = Body { outputs: vec![reward.block_output()], proof, ..Body::default() };
            let bytes = body.to_bytes();
            let (state_root, stated) = chain.header_after(&BodyRef::from_bytes(&bytes).unwrap()).unwrap();
            let mut header = Header {
                prev_hash: parent.hash(),
                height,
                timestamp: parent.timestamp + 600,
                body_commitment: body.commitment(),
                state_root,
                statement: stated.digest(),
                aux: [0; 32],
                mix: EMPTY,
                nonce: [0; 32],
            };
            let target = chain.expected_target(&parent).unwrap();
            loop {
                header.mix = hashimoto(&source, &header.pow_hash(), &header.nonce).mix;
                if header.quick_pow_check(&target) {
                    break;
                }
                header.nonce[0] = header.nonce[0].wrapping_add(1);
            }
            let block = Block { header, body }.to_bytes();
            let began = Instant::now();
            assert_eq!(chain.apply_block(&BlockRef::from_bytes(&block).unwrap(), NOW), Ok(Applied::Extended));
            println!("block {height}: taken in {:.1?}", began.elapsed());
        }
    }

    /// Says where the bytes of a block's proof are: what is not the
    /// opening, the opening's rounds and what it sends whole, and for
    /// each committed codeword the leaves the queries open and the
    /// hashes that show them.
    fn said_by_part(proof: &[u8], params: &Params) {
        let proof = crate::argument::Proof::from_bytes(proof).unwrap();
        let (f, digest) = (core::mem::size_of::<F>(), core::mem::size_of::<Digest>());
        let pcs = &proof.pcs;
        let opened =
            |b: &crate::pcs::Batch| b.leaves.iter().map(|l| 4 + l.len() * f).sum::<usize>() + b.siblings.len() * digest;
        let openings: usize = pcs.openings.iter().chain(&pcs.joined_openings).map(opened).sum();
        println!(
            "  the proof: {} bytes; {} queries at rate 1/{}, {} bits ground before them",
            proof.size(),
            params.queries,
            1 << params.log_inv_rate,
            params.query_grinding
        );
        println!("    all but the opening (the tables' sums): {} bytes", proof.size() - pcs.size());
        println!(
            "    the opening without its queries: {} bytes ({} rounds of the sum, {} of the folding, {} roots, {} elements sent whole)",
            pcs.size() - openings,
            pcs.sums.len(),
            pcs.rounds.len(),
            pcs.roots.len(),
            pcs.last.len()
        );
        for (name, batches) in [("codeword", &pcs.openings), ("joined codeword", &pcs.joined_openings)] {
            for (i, b) in batches.iter().enumerate() {
                let elements = b.leaves.first().map_or(0, Vec::len);
                println!(
                    "    {name} {i}: {} bytes: {} leaves of {elements} elements ({} bytes), {} hashes ({} bytes)",
                    opened(b),
                    b.leaves.len(),
                    b.leaves.len() * (4 + elements * f),
                    b.siblings.len(),
                    b.siblings.len() * digest
                );
            }
        }
    }

    /// What making a block holds, on the main network's proofs: a block
    /// of a reward alone; a block of one payment, of one signature and
    /// `INPUTS` outputs (256 unless given); and a block of one payment
    /// that spends those, of `INPUTS` signatures, the most a block made
    /// here checks, and `OUTPUTS` outputs (1 unless given). Said for
    /// each: the most memory held while each part of its proof was
    /// made, the most held at all, and what taking the block held.
    #[test]
    #[ignore = "memory; run with --release --nocapture, after the main network's setup is written"]
    fn main_network_block_memory() {
        use crate::heap::{self, Part};
        use crate::output::{Key, Output};
        use crate::transaction::UnsignedTransaction;
        use std::time::Instant;
        let number = |name: &str, or: usize| std::env::var(name).ok().and_then(|n| n.parse().ok()).unwrap_or(or);
        let (inputs, outputs) = (number("INPUTS", 256), number("OUTPUTS", 1));
        let megabytes = |bytes: usize| bytes / 1_000_000;
        let bytes = std::fs::read("../resources/setup-mainnet.bin").unwrap();
        let parts = Parts::from_bytes(&bytes).unwrap();
        let text = crate::pow::SeedText::new(crate::pow::PowParams::MAINNET);
        let params = ChainParams {
            pow: crate::pow::PowParams::MAINNET,
            emission: ChainParams::MAINNET.emission,
            program: parts.own,
            ..easy()
        };
        let params = ChainParams { genesis_mix: None, ..params };
        let setup = Setup::from_parts(Level::MAINNET, Emission(params.emission), params.pow, &parts).unwrap();
        println!("the setup holds {} MB", megabytes(heap::held(Part::Setup)));
        let chain =
            Chain::open(MemBackend::new(), 8, params, text, ChainVerifier::of(&Level::MAINNET, &parts)).unwrap();
        let source = text.at(0);
        // A block of `txs` and `reward` made, said, and taken.
        let make = |name: &str, reward: &Output, txs: &[Transaction]| {
            let _ = parts_timed();
            heap::reset_peak();
            let (began, before) = (Instant::now(), heap::now());
            let signings: Vec<Signing> = txs.iter().flat_map(Transaction::signings).collect();
            let proven = (!signings.is_empty()).then(|| setup.sign(&signings).unwrap());
            let proof = prove_from(&setup, &chain, &source, reward, txs, proven.as_ref()).unwrap();
            println!(
                "{name}: proved in {:.1?}, a proof of {} bytes; {} MB held before, {} MB at the most",
                began.elapsed(),
                proof.len(),
                megabytes(before),
                megabytes(heap::peak())
            );
            for part in parts_timed() {
                println!("  {}: {:.1?}, {} MB of proving's at the most", part.name, part.took, megabytes(part.most));
            }
            said_by_part(&proof, &(Level::MAINNET.published)(0));
            drop(proven);
            let spent: Vec<u64> = txs.iter().flat_map(|tx| tx.inputs.iter().map(|i| i.position)).collect();
            let made = [reward].into_iter().chain(txs.iter().flat_map(|tx| &tx.outputs)).map(Output::block_output);
            let body = Body { inputs: spent, outputs: made.collect(), proof, ..Body::default() };
            let block = Block { header: header_from(&chain, &body, &source), body }.to_bytes();
            heap::reset_peak();
            let (began, before) = (Instant::now(), heap::now());
            assert_eq!(chain.apply_block(&BlockRef::from_bytes(&block).unwrap(), NOW), Ok(Applied::Extended));
            println!(
                "{name}: {} bytes, taken in {:.1?} with {} MB more held at the most",
                block.len(),
                began.elapsed(),
                megabytes(heap::peak() - before)
            );
        };
        // The first block pays a key; the second spends that into an
        // output for each of `inputs` keys; the third spends them all.
        let mut first = Key::generate(&[3; 32]);
        let paid = Output::new(&first.public_key(), params.subsidy(1));
        make("a block of a reward alone", &paid, &[]);
        if number("BLOCKS", 3) < 2 {
            return;
        }
        let mut keys: Vec<Key> = (0..inputs)
            .map(|i| {
                let mut seed = [5; 32];
                seed[..8].copy_from_slice(&(i as u64).to_le_bytes());
                Key::generate(&seed)
            })
            .collect();
        let (fee, each) = (1000, (paid.amount - 1000) / inputs as u64);
        let shares: Vec<Output> = keys.iter().map(|key| Output::new(&key.public_key(), each)).collect();
        let fee_first = paid.amount - each * inputs as u64;
        let split = UnsignedTransaction::new(vec![(first.public_key(), paid.amount)], shares)
            .at(&[0])
            .sign_with(&mut first)
            .unwrap();
        let reward = Output::to_key_hash(&[4; 32], params.subsidy(2) + fee_first);
        make(&format!("a block of one signature and {inputs} outputs"), &reward, &[split]);
        // (The reward of the second block lies at 1, the shares after it.)
        let positions: Vec<u64> = (0..inputs as u64).map(|i| 2 + i).collect();
        let total = each * inputs as u64 - fee;
        let made: Vec<Output> = (0..outputs)
            .map(|o| {
                let amount = total / outputs as u64 + if o == 0 { total % outputs as u64 } else { 0 };
                Output::to_key_hash(&[6 + o as u8; 32], amount)
            })
            .collect();
        let all = UnsignedTransaction::new(keys.iter().map(|key| (key.public_key(), each)).collect(), made)
            .at(&positions)
            .sign(|i, _, msg| keys[i].sign(msg))
            .unwrap();
        let reward = Output::to_key_hash(&[7; 32], params.subsidy(3) + fee);
        make(&format!("a block of {inputs} signatures and {outputs} outputs"), &reward, &[all]);
        // (What the system says the process held at the most, all told:
        // more than was asked for, by what its allocator keeps.)
        let status = std::fs::read_to_string("/proc/self/status").unwrap_or_default();
        let resident = status.lines().find(|l| l.starts_with("VmHWM")).and_then(|l| l.split_whitespace().nth(1));
        println!("the process, by the system: {} kB at the most", resident.unwrap_or("?"));
    }
}
