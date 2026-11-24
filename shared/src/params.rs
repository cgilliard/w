//! A network's parameters: what every node of it must agree on before
//! the first block.
//!
//! # What a block pays
//!
//! Coins are made by blocks and by nothing else. The schedule is a list
//! of eras, each so many blocks at so much a block, starting at block 1;
//! genesis pays nothing. When the last era ends the chain ends: a block
//! above [`ChainParams::final_height`] is not valid. Every amount is in
//! base units, [`COIN`] of them a coin.
//!
//! # Work
//!
//! Between two branches a node follows the one with the most work, a
//! block counting for the hashes its target asks on average:
//! [`block_work`].

use crate::block::{Block, Body, Header};
use crate::chain_proof::Statement;
use crate::difficulty::Schedule;
use crate::hash::{Digest, EMPTY};
use crate::pow::PowParams;
use crate::store::sparse::empty_state;
use crate::u256::U256;

/// Base units per coin: ten decimals, the most that fits. Every coin the
/// schedule makes, 735,840,000 of them, is 7.4 × 10^18 base units, which a
/// `u64` (1.8 × 10^19) holds with room for 2.5 times as many; at eleven
/// decimals it would not.
pub const COIN: u64 = crate::ledger::COIN;
/// Decimal places of [`COIN`].
pub const DECIMALS: usize = 10;
/// Blocks per year at the ten-minute target: 144 a day.
pub const BLOCKS_PER_YEAR: u32 = 144 * 365;

/// Mainnet emission: 1500 coins a block for 3.5 years, 500 for 3.5 years,
/// then 7 for 1000 years, 735,840,000 coins in all; then the chain ends.
pub const MAINNET_EMISSION: &[(u32, u64)] = crate::ledger::MAINNET_EMISSION.0;

/// The 32 bytes `hex` writes, as 64 digits: a hash as it is shown. The
/// program is not built of anything else.
const fn unhex(hex: &str) -> [u8; 32] {
    const fn digit(c: u8) -> u8 {
        match c {
            b'0'..=b'9' => c - b'0',
            b'a'..=b'f' => c - b'a' + 10,
            _ => panic!("a hash is written in the digits 0 to 9 and a to f"),
        }
    }
    let hex = hex.as_bytes();
    assert!(hex.len() == 64, "a hash is 64 digits");
    let mut out = [0u8; 32];
    let mut i = 0;
    while i < 32 {
        out[i] = digit(hex[2 * i]) << 4 | digit(hex[2 * i + 1]);
        i += 1;
    }
    out
}

/// Consensus parameters.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ChainParams {
    pub pow: PowParams,
    /// Timestamp of the genesis block, an empty block (see
    /// [`ChainParams::genesis`]).
    pub genesis_timestamp: u64,
    /// The genesis header's nonce: on mainnet, the hash of the latest
    /// Bitcoin block when genesis was made, so the chain provably did not
    /// exist before it.
    pub genesis_nonce: [u8; 32],
    /// The genesis header's mix, where it is not its work's: on every
    /// network there is it is (none is said, and the mix is worked out
    /// when the genesis is first made), as the first block's proof
    /// shows it. The work of genesis is held to no target.
    pub genesis_mix: Option<Digest>,
    /// The program of the chain's proof's step, which every block's
    /// statement names ([`crate::chain_proof::Statement`]).
    pub program: Digest,
    /// Target of the block after genesis; the ASERT anchor.
    pub genesis_target: U256,
    /// Easiest permitted target.
    pub max_target: U256,
    /// Largest serialized block, header and body (input positions,
    /// outputs and proof), in bytes. The only limit on a block's contents.
    pub max_block_size: usize,
    /// Seconds a timestamp may lead the local clock.
    pub max_future_drift: u64,
    /// Number of past blocks whose median timestamp bounds the next.
    pub median_time_window: usize,
    /// The emission schedule: consecutive eras of `(blocks, subsidy per
    /// block in base units)`, starting at height 1 (genesis pays nothing).
    /// The chain ends with the last era: a block above
    /// [`ChainParams::final_height`] is invalid.
    pub emission: &'static [(u32, u64)],
    /// Blocks a name's commit waits before its reveal
    /// ([`crate::name::MIN_REVEAL`] on mainnet).
    pub min_reveal: u32,
    /// The block time and difficulty schedule.
    pub schedule: Schedule,
    /// Debugging only (the node's `chain::debug`): the state root the
    /// first block's header has, where it is not that of nothing: a
    /// chain begun with a state filled at once, for trying a node at
    /// the size of a chain that has run for years. None on every
    /// network there is.
    pub genesis_state: Option<crate::hash::Digest>,
}

impl ChainParams {
    pub const MAINNET: ChainParams = ChainParams {
        pow: PowParams::MAINNET,
        genesis_timestamp: crate::genesis::TIMESTAMP,
        genesis_nonce: unhex(crate::genesis::BITCOIN_HASH_HEX),
        genesis_mix: None,
        program: crate::prover::MAINNET_PROGRAM,
        genesis_target: U256(crate::genesis::TARGET),
        max_target: U256([u64::MAX, u64::MAX, u64::MAX, u64::MAX >> 8]), // 2^248 - 1
        max_block_size: 2_000_000,
        max_future_drift: 2 * 3600,
        median_time_window: 11,
        emission: MAINNET_EMISSION,
        min_reveal: crate::name::MIN_REVEAL,
        schedule: Schedule::MAINNET,
        genesis_state: None,
    };

    /// The dev network (`--network dev`), for rapid testing on a machine
    /// or a few: a block a second (the schedule starting at block 1), the
    /// built-in 64 KB dataset, an easy target. Its own genesis, so its
    /// nodes never mix with mainnet's.
    pub const DEV: ChainParams = ChainParams {
        pow: PowParams::DEV,
        genesis_timestamp: 1_767_225_600, // 2026-01-01
        genesis_nonce: *b"tabminer dev network, direct....",
        genesis_mix: None,
        program: crate::prover::MAINNET_PROGRAM,
        genesis_target: U256([0, 0, 0, 1 << 36]), // 2^20 hashes, about a second on 12 cores
        max_target: ChainParams::MAINNET.max_target,
        max_block_size: 2_000_000,
        // (A sixth of the half life, where the main network's two
        // hours are a twenty-fourth of its: a block stamped as far
        // ahead as may be makes the next an eighth easier, not free.)
        max_future_drift: 10,
        median_time_window: 11,
        emission: MAINNET_EMISSION,
        min_reveal: crate::name::MIN_REVEAL,
        schedule: Schedule { block_time: 1, half_life: 60, from_first_block: true },
        genesis_state: None,
    };

    /// A dev network with the main network's work (`--network
    /// dev-main-work`): its table, its targets and its times, and the
    /// least work a block may have from the first. For trying, with the
    /// debugging options, what the main network's rules cost a node:
    /// above all the checking of headers, which a node that makes no
    /// blocks does from the seed's text. Its own genesis, well in the
    /// past: a chain years long has room before now.
    pub const DEV_MAIN_WORK: ChainParams = ChainParams {
        genesis_timestamp: 1_735_689_600, // 2025-01-01
        genesis_nonce: *b"tabminer dev network, main work.",
        genesis_target: ChainParams::MAINNET.max_target,
        ..Self::MAINNET
    };

    /// The recursive dev network (`--network dev-recursive`): as
    /// [`ChainParams::DEV`], a block every ten seconds, its blocks to
    /// carry chain proofs made the mainnet way at the smallest
    /// parameters.
    pub const DEV_RECURSIVE: ChainParams = ChainParams {
        genesis_nonce: *b"tabminer dev network, recursive.",
        schedule: Schedule { block_time: 10, half_life: 300, from_first_block: true },
        max_future_drift: 50,
        ..Self::DEV
    };

    /// Subsidy paid by the block at `height`: zero for genesis and above
    /// the final height.
    pub fn subsidy(&self, height: u32) -> u64 {
        if height == 0 {
            return 0;
        }
        let mut first = 1u64;
        for &(blocks, subsidy) in self.emission {
            if (height as u64) < first + blocks as u64 {
                return subsidy;
            }
            first += blocks as u64;
        }
        0
    }

    /// The subsidies of blocks 1 to `height`: with what genesis creates
    /// (nothing on mainnet), what the amounts of the unspent outputs
    /// after block `height` sum to exactly.
    pub fn issued(&self, height: u32) -> u128 {
        let (mut total, mut first) = (0u128, 1u64);
        for &(blocks, subsidy) in self.emission {
            if (height as u64) < first {
                break;
            }
            let n = (blocks as u64).min(height as u64 + 1 - first);
            total += n as u128 * subsidy as u128;
            first += blocks as u64;
        }
        total
    }

    /// Height of the last block the chain can have.
    pub fn final_height(&self) -> u32 {
        self.emission.iter().map(|&(blocks, _)| blocks as u64).sum::<u64>().min(u32::MAX as u64) as u32
    }

    /// Every coin the schedule creates, in base units.
    pub fn total_supply(&self) -> u128 {
        self.emission.iter().map(|&(blocks, subsidy)| blocks as u128 * subsidy as u128).sum()
    }

    /// The mix of the genesis header's work, from the seed's text.
    pub fn genesis_work(&self, seed: &crate::pow::SeedText<'_>) -> Digest {
        let header = self.unworked();
        crate::pow::hashimoto(&seed.at(0), &header.pow_hash(), &header.nonce).mix
    }

    /// The genesis header's mix: the one said, or its work's, from the
    /// seed's text in the program. That is worked out once for a genesis
    /// (some thousands of hashes) and kept.
    fn mix(&self, header: &Header) -> Digest {
        type Worked = (Digest, [u8; 32], PowParams, Digest);
        static KEPT: std::sync::Mutex<Vec<Worked>> = std::sync::Mutex::new(Vec::new());
        if let Some(mix) = self.genesis_mix {
            return mix;
        }
        let of = (header.pow_hash(), header.nonce, self.pow);
        let found = |kept: &Vec<Worked>| kept.iter().find(|k| (k.0, k.1, k.2) == of).map(|k| k.3);
        if let Some(mix) = found(&KEPT.lock().unwrap_or_else(|e| e.into_inner())) {
            return mix;
        }
        let mix = self.genesis_work(&crate::pow::SeedText::new(self.pow));
        let mut kept = KEPT.lock().unwrap_or_else(|e| e.into_inner());
        if found(&kept).is_none() {
            kept.push((of.0, of.1, of.2, mix));
        }
        mix
    }

    /// The genesis header, its mix still to be said.
    fn unworked(&self) -> Header {
        Header {
            prev_hash: EMPTY,
            height: 0,
            timestamp: self.genesis_timestamp,
            body_commitment: Body::default().commitment(),
            state_root: self.genesis_state.unwrap_or_else(empty_state),
            statement: Statement::genesis().digest(),
            aux: [0u8; 32],
            mix: EMPTY,
            nonce: self.genesis_nonce,
        }
    }

    /// The genesis block: empty, at `genesis_timestamp`, over the empty
    /// state tree, stating where a chain begins, with `genesis_nonce` as
    /// its nonce and that nonce's mix (the work is held to no target on
    /// genesis). Every node of a network must start from the
    /// same one. Nothing is allocated: an empty body holds no memory.
    pub fn genesis(&self) -> Block {
        let header = self.unworked();
        Block { header: Header { mix: self.mix(&header), ..header }, body: Body::default() }
    }
}

/// Work a block mined at `target` adds to its chain: `2^256 / (target +
/// 1)`, computed as `(!target / (target + 1)) + 1`.
pub fn block_work(target: U256) -> U256 {
    let t1 = target.saturating_add(U256::ONE);
    (!target / t1).saturating_add(U256::ONE)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hash::digest_to_bytes;

    fn small() -> ChainParams {
        ChainParams { emission: &[(10, 50), (10, 25), (5, 12)], ..ChainParams::MAINNET }
    }

    #[test]
    fn subsidy_schedule() {
        let p = small();
        assert_eq!(p.subsidy(0), 0);
        assert_eq!((p.subsidy(1), p.subsidy(10)), (50, 50));
        assert_eq!((p.subsidy(11), p.subsidy(20)), (25, 25));
        assert_eq!((p.subsidy(21), p.subsidy(25)), (12, 12));
        assert_eq!(p.subsidy(26), 0);
        assert_eq!(p.subsidy(u32::MAX), 0);
        assert_eq!(p.final_height(), 25);
        let m = ChainParams::MAINNET;
        let era = 144 * 365 * 7 / 2;
        assert_eq!(era, 183_960);
        assert_eq!(m.subsidy(0), 0);
        assert_eq!((m.subsidy(1), m.subsidy(era)), (1500 * COIN, 1500 * COIN));
        assert_eq!((m.subsidy(era + 1), m.subsidy(2 * era)), (500 * COIN, 500 * COIN));
        assert_eq!(m.subsidy(2 * era + 1), 7 * COIN);
        assert_eq!(m.final_height(), 2 * era + 144 * 365 * 1000);
        assert_eq!(m.final_height(), 52_927_920);
        assert_eq!(m.subsidy(m.final_height()), 7 * COIN);
        assert_eq!(m.subsidy(m.final_height() + 1), 0);
        assert_eq!(m.total_supply(), 735_840_000 * COIN as u128);
        // All of it fits the type an amount has, and COIN is its decimals.
        assert!(m.total_supply() < u64::MAX as u128);
        assert_eq!(COIN, 10u64.pow(DECIMALS as u32));
    }

    #[test]
    fn issued_sums_the_schedule() {
        let p = small();
        assert_eq!(p.issued(0), 0);
        assert_eq!(p.issued(1), 50);
        assert_eq!(p.issued(10), 500);
        assert_eq!(p.issued(11), 525);
        assert_eq!(p.issued(25), 500 + 250 + 60);
        assert_eq!(p.issued(1000), p.total_supply());
        for h in 0..30 {
            assert_eq!(p.issued(h), (1..=h).map(|i| p.subsidy(i) as u128).sum::<u128>());
        }
        let m = ChainParams::MAINNET;
        assert_eq!(m.issued(m.final_height()), m.total_supply());
        assert_eq!(m.issued(u32::MAX), m.total_supply());
        // An era that ends where a height can no longer count.
        let long = ChainParams { emission: &[(u32::MAX, 1), (u32::MAX, 2)], ..m };
        assert_eq!(long.final_height(), u32::MAX);
        assert_eq!(long.issued(u32::MAX), u32::MAX as u128);
        assert_eq!(long.subsidy(u32::MAX), 1);
    }

    #[test]
    fn work_of_a_block() {
        assert_eq!(block_work(U256::MAX.shift_right(8)), U256::from_u64(256));
        assert_eq!(block_work(U256::ZERO), U256::MAX);
        assert_eq!(block_work(U256::MAX), U256::ONE);
        // 2^256 / (2^232 + 1), rounded down; a harder target is more work.
        let t = U256([0, 0, 0, 1 << 40]);
        assert_eq!(block_work(t), U256::from_u64((1 << 24) - 1));
        assert!(block_work(t.shift_right(1)) > block_work(t));
    }

    /// Mainnet's genesis is of what its file says.
    #[test]
    fn mainnet_genesis_is_of_its_file() {
        let g = ChainParams::MAINNET.genesis();
        let hex = |bytes: &[u8]| bytes.iter().map(|b| format!("{b:02x}")).collect::<String>();
        println!("the main network's genesis: {}", hex(&digest_to_bytes(&g.header.hash())));
        assert_eq!(g.header.timestamp, crate::genesis::TIMESTAMP);
        assert_eq!(hex(&g.header.nonce), crate::genesis::BITCOIN_HASH_HEX);
        let digits = "00ff10abcdef0000000000000000000000000000000000000000000000000001";
        assert_eq!(hex(&unhex(digits)), digits);
        assert!(crate::genesis::BITCOIN_TIME <= g.header.timestamp, "the Bitcoin block must come first");
        assert_eq!((g.header.height, g.header.state_root), (0, empty_state()));
        assert_eq!(g.header.statement, Statement::genesis().digest());
        assert_eq!(g.header.body_commitment, g.body.commitment());
        assert_eq!(g.size(), crate::block::HEADER_SIZE + g.body.size());
    }

    /// Each network's genesis header carries the mix of its work, as
    /// the first block's proof is to show it.
    #[test]
    fn a_genesis_header_s_mix_is_its_work_s() {
        let networks = [
            ("mainnet", ChainParams::MAINNET),
            ("dev", ChainParams::DEV),
            ("dev-main-work", ChainParams::DEV_MAIN_WORK),
            ("dev-recursive", ChainParams::DEV_RECURSIVE),
        ];
        for (name, params) in networks {
            let mix = params.genesis_work(&crate::pow::SeedText::new(params.pow));
            assert_eq!(params.genesis_mix, None, "{name}");
            // Worked out, and the same when asked for again.
            assert_eq!(params.genesis().header.mix, mix, "{name}");
            assert_eq!(params.genesis().header, params.genesis().header, "{name}");
            // One that is said is the header's as it is.
            let said = ChainParams { genesis_mix: Some([7; 32]), ..params };
            assert_eq!(said.genesis().header.mix, [7; 32], "{name}");
        }
    }

    /// Each network has a genesis of its own, and is made the same way
    /// every time.
    #[test]
    fn networks_do_not_share_a_genesis() {
        let ids =
            [ChainParams::MAINNET, ChainParams::DEV, ChainParams::DEV_RECURSIVE].map(|p| p.genesis().header.hash());
        assert!(ids[0] != ids[1] && ids[1] != ids[2] && ids[0] != ids[2]);
        assert_eq!(ChainParams::DEV.genesis(), ChainParams::DEV.genesis());
        assert_eq!(ChainParams::DEV.pow, PowParams::DEV);
        assert_eq!(ChainParams::DEV.min_reveal, ChainParams::MAINNET.min_reveal);
    }
}
