//! Debugging only: a state filled at once, for trying a node at the
//! size of a chain that has run for years without running one.
//!
//! The state is of outputs nobody made: one at every `spacing`-th
//! position from the first (the positions between as if their outputs
//! had been spent long ago, as on a chain with a history), each drawn
//! from its position alone and of amount zero. So every node that is
//! told the same two numbers has the same state, and the same first
//! block: whose header says that state's root, where a chain's first
//! block says the root of nothing.
//!
//! A node may be given the state itself ([`fill`]), or only its root
//! ([`root`]): one with only the root is a new node of that chain, with
//! everything still to take from the others.
//!
//! The state is made a part at a time, and put where a state taken from
//! other nodes is put, by the same steps: so a state of any size is
//! made in the memory of one part, and filling one is itself a trial of
//! how a state is taken.
//!
//! None of it is for a network anybody uses: it is built only with the
//! `dev` feature, and a chain so begun is of blocks whose proofs nobody
//! checks.

use super::Chain;
use crate::block::Body;
use crate::error::Error;
use crate::hash::Digest;
use crate::output::Memo;
use crate::registry::state_root as compress;
use crate::store::Backend;
use crate::store::outputs::{PART_LEVEL, Record, part_root, parts_root};

/// The output at `position`: commitment and memo drawn from the
/// position (splitmix64), amount zero, of the first block.
pub fn output(position: u64) -> Record {
    let mut x = position ^ 0x5eed_f111_0000_0000;
    let mut byte = || {
        x = x.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = x;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        (z ^ (z >> 31)) as u8
    };
    let commitment: Digest = core::array::from_fn(|_| byte());
    let memo: Memo = core::array::from_fn(|_| byte());
    Record { commitment, memo, amount: 0, height: 0 }
}

/// The position the next output takes, after `n` outputs one every
/// `spacing` positions.
pub fn next(n: u64, spacing: u64) -> u64 {
    n * spacing.max(1)
}

/// The outputs of part `index` of a state of `n` outputs one every
/// `spacing` positions.
pub fn part(index: u64, n: u64, spacing: u64) -> Vec<(u64, Record)> {
    let spacing = spacing.max(1);
    let (first, end) = (index << PART_LEVEL, ((index + 1) << PART_LEVEL).min(next(n, spacing)));
    let from = first.div_ceil(spacing) * spacing;
    (from..end).step_by(spacing as usize).map(|p| (p, output(p))).collect()
}

/// The roots of the parts of a state of `n` outputs one every `spacing`
/// positions, and the state's root: nothing is kept but the roots.
/// `progress` is told, now and then, how many outputs are done.
pub fn root(n: u64, spacing: u64, progress: &(dyn Fn(u64) + Sync)) -> (Digest, Vec<(u64, Digest)>) {
    let parts = next(n, spacing).div_ceil(1 << PART_LEVEL);
    let mut roots: Vec<(u64, Digest)> = Vec::with_capacity(parts as usize);
    // (A run of parts at a time, each on a thread of its own.)
    const RUN: u64 = 1024;
    for run in (0..parts).step_by(RUN as usize) {
        let count = RUN.min(parts - run) as usize;
        let made = crate::parallel::par_map_min(count, 1, |k| {
            let outputs = part(run + k as u64, n, spacing);
            (!outputs.is_empty()).then(|| part_root(PART_LEVEL, &outputs))
        });
        roots.extend(made.into_iter().enumerate().filter_map(|(k, r)| Some((run + k as u64, r?))));
        progress(((run + RUN) << PART_LEVEL).min(next(n, spacing)).div_ceil(spacing.max(1)));
    }
    let names = crate::store::names::parts_root(crate::store::names::PART_LEVEL, &[]);
    (compress(&parts_root(PART_LEVEL, &roots), &names), roots)
}

/// Fills `chain`, which is at its first block and whose first block
/// says the state's root ([`crate::chain::params::ChainParams::genesis_state`]),
/// with the state of `n` outputs one every `spacing` positions, whose
/// parts' roots are `roots` ([`root`]). A chain that has the state
/// already, or has gone on from its first block, is left as it is.
/// `progress` is told, now and then, how many outputs are in.
pub fn fill<B: Backend + 'static, V: crate::chain::verify::ProofVerifier + Sync>(
    chain: &Chain<B, V>,
    n: u64,
    spacing: u64,
    roots: &[(u64, Digest)],
    progress: &dyn Fn(u64),
) -> Result<(), Error> {
    let genesis = chain.params().genesis().header;
    {
        let state = chain.whole()?;
        let snap = state.snapshot()?;
        if snap.tip().0 != 0 || snap.outputs().next != 0 {
            return Ok(());
        }
    }
    chain.begin_receiving(&genesis, next(n, spacing), roots, &[])?;
    // (A run of parts at a time: made, checked and put on every
    // thread there is, and durable together.)
    const RUN: usize = 64;
    for run in roots.chunks(RUN) {
        let made = crate::parallel::par_map_min(run.len(), 1, |k| part(run[k].0, n, spacing));
        // (A part: which, its outputs by position, and hashes by position.)
        type Part<'a> = (u64, &'a [(u64, Record)], &'a [(u64, Digest)]);
        let parts: Vec<Part<'_>> = run.iter().zip(&made).map(|(r, outputs)| (r.0, &outputs[..], &[][..])).collect();
        chain.put_parts(&parts)?;
        let index = run[run.len() - 1].0;
        progress((((index + 1) << PART_LEVEL).min(next(n, spacing))).div_ceil(spacing.max(1)));
    }
    chain.finish_receiving(&Body::default().to_bytes())?;
    progress(n);
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::chain::apply::tests::{extend_spending, grow};
    use crate::chain::headers::tests::{easy, seed, table};
    use crate::chain::params::ChainParams;
    use crate::chain::verify::AcceptAllProofs;
    use crate::store::testing::MemBackend;

    /// A chain is begun with a state filled at once: its first block
    /// says that state's root, the state is there, what is in it is
    /// spent like any output, and the chain goes on from it. And a node
    /// given only the root has the same first block.
    #[test]
    fn a_chain_begins_with_a_state_filled_at_once() {
        let (n, spacing) = (20_000u64, 5u64);
        let (state_root, roots) = root(n, spacing, &|_| {});
        assert_eq!(roots.len() as u64, (n * spacing).div_ceil(1 << PART_LEVEL));
        // (Another size, another spacing: another state.)
        assert_ne!(root(n + 1, spacing, &|_| {}).0, state_root);
        assert_ne!(root(n, spacing + 1, &|_| {}).0, state_root);
        let params = ChainParams { genesis_state: Some(state_root), ..easy() };
        let open = || {
            let chain = Chain::open(MemBackend::new(), 64, params, seed(), AcceptAllProofs).unwrap();
            chain.set_dataset(table());
            chain
        };
        let chain = open();
        assert_eq!(chain.tip().unwrap().state_root, state_root);
        assert_ne!(chain.tip().unwrap().hash(), easy().genesis().header.hash());
        fill(&chain, n, spacing, &roots, &|_| {}).unwrap();
        {
            let state = chain.state();
            let snap = state.snapshot().unwrap();
            assert_eq!((snap.root(), snap.tip().0, snap.outputs().next), (state_root, 0, n * spacing));
            assert_eq!(snap.output(5 * 7).unwrap(), Some((output(35), true)));
            assert_eq!(snap.output(5 * 7 + 1).unwrap(), None);
        }
        // Filled already: left as it is.
        fill(&chain, n, spacing, &roots, &|_| {}).unwrap();
        // The chain goes on: blocks that make outputs, and one that
        // spends some of what it began with.
        grow(&chain, 2, 1);
        let reward = crate::block::BlockOutput { commitment: [9; 32], memo: [0; 20], amount: easy().subsidy(3) };
        extend_spending(&chain, &[0, 5, 50_000], &[reward]);
        let state = chain.state();
        let snap = state.snapshot().unwrap();
        assert!(!snap.is_unspent(5).unwrap() && snap.is_unspent(10).unwrap() && !snap.is_unspent(50_000).unwrap());
        assert_eq!(snap.tip().0, 3);
        drop(snap);
        drop(state);
        // A node with only the root is a node of the same chain, with
        // nothing in it.
        let other = open();
        assert_eq!(other.tip().unwrap().hash(), chain.header_at(0).unwrap().unwrap().hash());
        assert_eq!(other.state().snapshot().unwrap().outputs().next, 0);
    }
}
