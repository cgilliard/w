//! What a transaction pays, and what a node asks of one before it will
//! keep it and pass it on.
//!
//! A fee is so much a unit of weight ([`Weights`]): an output weighs
//! more than an input, every node keeping the outputs for as long as
//! they are unspent. What a node asks beyond validity is its own to
//! set ([`Policy`]): the least it takes a unit, the smallest output,
//! how long a transaction may wait.
//!
//! These are a node's pool's rules, and are here and not with the pool
//! because a wallet goes by them too: it pays what a node will take.
//! The pool itself is the node's.

use crate::name::OpKind;
use crate::transaction::TransactionRef;

/// Largest transaction accepted by default, in bytes: a bound on what
/// one message may make a node hold, not a rule of what is paid for. A
/// transaction of any size below it is pooled and relayed if it pays
/// for its weight (about 750 inputs fit). An operator may set another
/// ([`Policy::max_tx_size`]).
pub const MAX_TX_SIZE: usize = 2 << 20;

/// Of the transactions known, the most recent held whole: this many
/// bytes of them, unless said otherwise. A transaction is passed on in
/// its first moments, so this is what a node needs to pass them on.
/// With full blocks about twenty come a second, of 2.5 KB each: this
/// is five minutes of that, and half a minute of ten times that.
pub const WHOLE_RECENT: usize = 16 << 20;

/// Of the older ones, the bytes held whole, unless said otherwise: for
/// whoever makes blocks and comes late. None is needed of a node for
/// the rest to go on, and a seed holds none.
pub const WHOLE_OLDER: usize = 64 << 20;

/// Base units a unit of weight ([`Weights`]) that a transaction must pay
/// to be pooled at all, by default: so that relaying a signature, and
/// adding to the set of outputs every node keeps, costs something
/// (2.5 millionths of a coin, at ten decimals).
pub const MIN_FEE_PER_UNIT: u64 = 25_000;

/// Base units a unit of weight a replacement must add over what it
/// replaces, by default.
pub const REPLACEMENT_FEE_PER_UNIT: u64 = MIN_FEE_PER_UNIT;

/// What a transaction weighs, for its fee: a fee is so much a unit of
/// weight. An output weighs more than an input: every node keeps the
/// set of outputs for as long as they are unspent, where a signature is
/// relayed and proven once. So a transaction that leaves fewer outputs
/// than it spends is the cheap one.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Weights {
    /// An input; and each signature of an input that spends a policy's
    /// output (one at the least).
    pub input: u64,
    pub output: u64,
    /// A commitment to a name (an output), a reveal (which spends it and
    /// registers a name for good) and an update (a signature).
    pub commit: u64,
    pub reveal: u64,
    pub update: u64,
}

impl Weights {
    pub const DEFAULT: Weights = Weights { input: 1, output: 3, commit: 3, reveal: 4, update: 1 };

    /// The weight of a transaction of `inputs` and `outputs` and no name
    /// operations.
    pub const fn of(&self, inputs: usize, outputs: usize) -> u64 {
        inputs as u64 * self.input + outputs as u64 * self.output
    }

    /// The weight of a transaction as its maker has it
    /// ([`Weights::weigh`], of the same one).
    pub fn of_tx(&self, tx: &crate::transaction::Transaction) -> u64 {
        let policy: u64 = tx.policy_inputs.iter().map(|p| p.signatures().max(1) as u64).sum();
        let ops: u64 = tx.ops.iter().map(|op| self.of_op(op.kind())).sum();
        (tx.inputs.len() as u64 + policy) * self.input + tx.outputs.len() as u64 * self.output + ops
    }

    /// The weight of an operation on a name.
    pub fn of_op(&self, kind: OpKind) -> u64 {
        match kind {
            OpKind::Commit => self.commit,
            OpKind::Reveal => self.reveal,
            _ => self.update,
        }
    }

    /// The weight of `tx`.
    pub fn weigh(&self, tx: &TransactionRef<'_>) -> u64 {
        let n = tx.counts();
        let policy: u64 = tx.policy_inputs().map(|p| p.signatures().max(1) as u64).sum();
        let ops: u64 = (tx.ops())
            .map(|op| match op.kind() {
                OpKind::Commit => self.commit,
                OpKind::Reveal => self.reveal,
                _ => self.update,
            })
            .sum();
        (n.inputs as u64 + policy) * self.input + n.outputs as u64 * self.output + ops
    }
}

/// The smallest output pooled, by default: one worth the fee of spending
/// it at the floor, so that nobody fills the set with outputs no one
/// will spend.
pub const DUST: u64 = MIN_FEE_PER_UNIT * Weights::DEFAULT.input;

/// How long the rolling admission minimum takes to fall halfway back to
/// the floor, by default: as Bitcoin's.
pub const HALF_LIFE_SECS: u64 = 12 * 3600;

/// How long a transaction may wait in the pool, by default: then it is
/// dropped, and its id refused for as long again.
pub const EXPIRY_SECS: u64 = 14 * 86400;

/// About the size of a block's proof, the rest of a block being space
/// for transactions.
pub const PROOF_BYTES: usize = 450_000;

/// The share of a block's space for transactions the reference miner
/// gives to the longest-waiting ones, by default.
pub const RESERVE_PERCENT: usize = 10;

/// The main network's block time, in seconds.
pub const BLOCK_TIME: u64 = crate::difficulty::IDEAL_BLOCK_TIME as u64;

/// The main network's largest block.
pub const MAX_BLOCK_SIZE: usize = crate::params::ChainParams::MAINNET.max_block_size;

/// The aged reserve, in bytes: about 180 KB.
pub const RESERVE_BYTES: usize = reserve_bytes(MAX_BLOCK_SIZE, RESERVE_PERCENT);

/// The aged reserve of a block of `max_block_size` at `percent` of its
/// space for transactions.
pub const fn reserve_bytes(max_block_size: usize, percent: usize) -> usize {
    max_block_size.saturating_sub(PROOF_BYTES) * percent / 100
}

/// The waits fees are estimated for: about a block, an hour, a day.
pub const TARGET_BLOCK: u64 = BLOCK_TIME;

pub const TARGET_HOUR: u64 = 3600;

pub const TARGET_DAY: u64 = 86400;

/// The oldest transactions kept from eviction, by default: about a day
/// of the reserve (some 26 MB), so that in a flood they still age into it.
pub const PROTECT_BYTES: usize = RESERVE_BYTES * (86_400 / BLOCK_TIME as usize);

/// What a pool asks of a transaction beyond validity: a node's own
/// policy, set by its operator.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Policy {
    /// The relay floor: base units a unit of weight, below which a
    /// transaction is neither pooled nor relayed.
    pub min_fee_per_unit: u64,
    /// What a replacement must add over what it replaces, a unit of its
    /// weight; and what the minimum rises by over a transaction evicted.
    pub replacement_per_unit: u64,
    /// What a transaction's parts weigh.
    pub weights: Weights,
    /// The smallest output pooled: the fee of spending it at the floor.
    pub dust: u64,
    /// The rolling minimum's half-life.
    pub half_life_secs: u64,
    /// How long a transaction may wait in the pool.
    pub expiry_secs: u64,
    /// The oldest transactions' bytes kept from eviction and admitted
    /// whatever the rolling minimum; at most half the pool, so that fees
    /// always compete for the rest.
    pub protect_bytes: usize,
    /// The share of a block's space for transactions that this node,
    /// mining, gives to the longest-waiting ones, oldest first,
    /// whatever they pay: of a hundred. None of it, and a block is
    /// filled by fee alone.
    pub reserve_percent: usize,
    /// The largest transaction pooled and relayed, in bytes.
    pub max_tx_size: usize,
    /// How much of what the pool knows of it holds whole: the most
    /// recent, so many bytes of them; and of the older ones, so many
    /// bytes. Of the rest it keeps what a node that makes no blocks
    /// needs of a transaction, and not the transaction. A node that
    /// makes blocks holds all.
    pub whole_recent: usize,
    pub whole_older: usize,
}

impl Policy {
    pub const MAINNET: Policy = Policy {
        min_fee_per_unit: MIN_FEE_PER_UNIT,
        replacement_per_unit: REPLACEMENT_FEE_PER_UNIT,
        weights: Weights::DEFAULT,
        dust: DUST,
        half_life_secs: HALF_LIFE_SECS,
        expiry_secs: EXPIRY_SECS,
        protect_bytes: PROTECT_BYTES,
        reserve_percent: RESERVE_PERCENT,
        max_tx_size: MAX_TX_SIZE,
        whole_recent: WHOLE_RECENT,
        whole_older: WHOLE_OLDER,
    };
    /// Anything valid, for tests.
    pub const NONE: Policy = Policy { min_fee_per_unit: 0, dust: 0, ..Policy::MAINNET };

    /// The mainnet policy at another floor, its dust limit following.
    pub const fn with_floor(min_fee_per_unit: u64) -> Policy {
        Policy { min_fee_per_unit, dust: min_fee_per_unit * Weights::DEFAULT.input, ..Policy::MAINNET }
    }

    /// The same policy, taking transactions of up to `bytes`.
    pub const fn with_max_tx_size(self, bytes: usize) -> Policy {
        Policy { max_tx_size: bytes, ..self }
    }

    /// The same policy, holding whole so much of what the pool knows
    /// of: `recent` bytes of the most recent, and `older` bytes of the
    /// older ones.
    pub const fn holding(self, recent: usize, older: usize) -> Policy {
        Policy { whole_recent: recent, whole_older: older, ..self }
    }

    /// The same policy, holding everything whole: as a node that makes
    /// blocks does.
    pub const fn holding_all(self) -> Policy {
        self.holding(usize::MAX, usize::MAX)
    }

    /// Whether everything is held whole.
    pub const fn holds_all(&self) -> bool {
        self.whole_older == usize::MAX
    }

    /// The same policy with other weights, its dust limit following.
    pub const fn with_weights(self, weights: Weights) -> Policy {
        Policy { weights, dust: self.min_fee_per_unit * weights.input, ..self }
    }

    /// The policy an operator sets: the floor, in base units a unit of
    /// weight (the dust limit follows it); the half-life of the raised
    /// minimum, in hours; how long a transaction may wait, in days;
    /// and the reserve, of a hundred (what is kept from eviction is a
    /// day of it, as by default).
    pub const fn set(min_fee_per_unit: u64, half_life_hours: u64, expiry_days: u64, reserve_percent: usize) -> Policy {
        Policy {
            half_life_secs: half_life_hours * 3600,
            expiry_secs: expiry_days * 86400,
            protect_bytes: reserve_bytes(MAX_BLOCK_SIZE, reserve_percent) * (86_400 / BLOCK_TIME as usize),
            reserve_percent,
            ..Policy::with_floor(min_fee_per_unit)
        }
    }

    /// The smallest fee a transaction of `inputs` and `outputs` and no
    /// name operations may pay.
    pub fn min_fee(&self, inputs: usize, outputs: usize) -> u64 {
        self.min_fee_for(self.weights.of(inputs, outputs))
    }

    /// The smallest fee a transaction of `weight` may pay.
    pub fn min_fee_for(&self, weight: u64) -> u64 {
        self.min_fee_per_unit.saturating_mul(weight)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A weight is its parts': inputs, outputs, and the operations on
    /// names by their kinds.
    #[test]
    fn a_weight_is_of_its_parts() {
        let w = Weights::DEFAULT;
        assert_eq!((w.of(0, 0), w.of(2, 3), w.of(1, 0)), (0, 2 * w.input + 3 * w.output, w.input));
        assert_eq!((w.of_op(OpKind::Commit), w.of_op(OpKind::Reveal)), (w.commit, w.reveal));
        let other = Weights { input: 5, output: 7, ..w };
        assert_eq!(other.of(2, 3), 31);
    }

    /// The least a transaction pays is the floor a unit of its weight;
    /// the smallest output follows the floor, and the weights.
    #[test]
    fn the_floor_sets_the_least_fee_and_the_smallest_output() {
        let main = Policy::MAINNET;
        assert_eq!(main.min_fee(1, 2), MIN_FEE_PER_UNIT * Weights::DEFAULT.of(1, 2));
        assert_eq!(main.min_fee_for(7), 7 * MIN_FEE_PER_UNIT);
        assert_eq!((main.dust, DUST), (DUST, MIN_FEE_PER_UNIT * Weights::DEFAULT.input));
        let floor = Policy::with_floor(40);
        assert_eq!((floor.min_fee_per_unit, floor.dust, floor.min_fee(1, 1)), (40, 40, 160));
        let heavy = floor.with_weights(Weights { input: 3, ..Weights::DEFAULT });
        assert_eq!((heavy.dust, heavy.min_fee(1, 1)), (120, 40 * 6));
        // (A weight no fee can pay for is not one that wraps round.)
        assert_eq!(main.min_fee_for(u64::MAX), u64::MAX);
        assert_eq!((Policy::NONE.min_fee(9, 9), Policy::NONE.dust), (0, 0));
    }

    /// What an operator sets is in hours and days and of a hundred;
    /// what is kept is in seconds and bytes.
    #[test]
    fn what_an_operator_sets() {
        let set = Policy::set(50, 6, 3, 25);
        assert_eq!((set.min_fee_per_unit, set.dust), (50, 50));
        assert_eq!((set.half_life_secs, set.expiry_secs, set.reserve_percent), (6 * 3600, 3 * 86400, 25));
        let a_day = 86_400 / BLOCK_TIME as usize;
        assert_eq!(set.protect_bytes, reserve_bytes(MAX_BLOCK_SIZE, 25) * a_day);
        // The reserve is a share of a block's room for transactions,
        // which is the block less its proof.
        assert_eq!(reserve_bytes(PROOF_BYTES + 1000, 10), 100);
        assert_eq!(reserve_bytes(PROOF_BYTES - 1, 10), 0);
        assert_eq!(
            (RESERVE_BYTES, PROTECT_BYTES),
            (reserve_bytes(MAX_BLOCK_SIZE, RESERVE_PERCENT), RESERVE_BYTES * a_day)
        );
        // What it holds whole, and how large a transaction it takes.
        let held = Policy::MAINNET.holding(1, 3).with_max_tx_size(4);
        assert_eq!((held.whole_recent, held.whole_older, held.max_tx_size, held.holds_all()), (1, 3, 4, false));
        assert_eq!((Policy::MAINNET.whole_recent, Policy::MAINNET.whole_older), (16 << 20, 64 << 20));
        let all = Policy::MAINNET.holding_all();
        assert_eq!((all.whole_recent, all.whole_older, all.holds_all()), (usize::MAX, usize::MAX, true));
    }
}
