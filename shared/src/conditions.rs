//! Spend policies: outputs that are not one key's to spend, but
//! whoever meets a condition's.
//!
//! A policy is a tree of up to 16 **leaves**, each a list of
//! **conditions** that must all hold; a spend shows one leaf, so the
//! leaves are the ways the output may be spent and the others stay
//! unseen. The tree's root stands where a key's hash does in an
//! output's commitment ([`crate::listed::commitment`]): on the chain a
//! policy's output is like any other.
//!
//! | condition | holds when |
//! |---|---|
//! | [`Cond::Thresh`] | `m` of the listed keys signed the transaction |
//! | [`Cond::Hash`] | the spender shows what hashes to it |
//! | [`Cond::After`] | the block's height is at least this |
//! | [`Cond::Older`] | the output is at least this many blocks old |
//!
//! Multisignature outputs are a threshold; a hash lock with a time lock
//! beside it on another leaf is a payment that is claimed or taken back.
//!
//! Not here yet: conditions on a channel's state and on the
//! transaction's own outputs (the reference's eltoo and covenants).
//!
//! # Hashes
//!
//! A condition is a block: its tag, a number or two, and a digest (a
//! threshold's keys, hashed in a chain; a hash lock's hash). A leaf is
//! its conditions' hashes in a chain; the tree's nodes hash pairs. Each
//! in a domain of its own.

use crate::hash::{
    DOM_COND, DOM_COVERED, DOM_HASHLOCK, DOM_POLICY_LEAF, DOM_POLICY_NODE, DOM_REBIND, DOM_SIGNERS, Digest, EMPTY,
    hash_domain,
};
use crate::xmss::PublicKey;

/// Levels of a policy's tree.
pub const DEPTH: usize = 4;

/// A condition.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Cond {
    /// `m` of the keys of these hashes sign.
    Thresh { m: u32, keys: Vec<Digest> },
    /// A value that hashes to this is shown ([`hash_lock`]).
    Hash(Digest),
    /// The block's height is at least this.
    After(u32),
    /// The output was made at least this many blocks ago.
    Older(u32),
    /// The spend's state is above this: a channel's later state takes
    /// the place of an earlier one.
    State(u32),
    /// The transaction's first `count` outputs are these, by their hash
    /// ([`covered`]): a covenant.
    Outputs { count: u32, digest: Digest },
    /// `m` of the keys sign, not the transaction, but the channel, the
    /// spend's state and the transaction's covered outputs
    /// ([`rebind_message`]), each with the leaf of its key that the state
    /// numbers: a signature that binds to whichever output of the
    /// channel it is used on.
    Rebind { m: u32, keys: Vec<Digest>, channel: Digest },
}

fn block(tag: u32, a: u32, b: u32, digest: &Digest, last: u32) -> [u8; 64] {
    let mut out = [0u8; 64];
    out[..4].copy_from_slice(&tag.to_le_bytes());
    out[4..8].copy_from_slice(&a.to_le_bytes());
    out[8..12].copy_from_slice(&b.to_le_bytes());
    out[16..48].copy_from_slice(digest);
    out[60..].copy_from_slice(&last.to_le_bytes());
    out
}

/// What a hash lock asks to be shown the preimage of.
pub fn hash_lock(preimage: &Digest) -> Digest {
    hash_domain(DOM_HASHLOCK, &[*preimage, EMPTY].concat())
}

/// A threshold's keys, hashed one after another.
pub fn keys_digest(keys: &[Digest]) -> Digest {
    keys_from(&EMPTY, keys)
}

/// The same from `start`: a channel's keys are hashed from the channel.
fn keys_from(start: &Digest, keys: &[Digest]) -> Digest {
    keys.iter().fold(*start, |acc, key| hash_domain(DOM_SIGNERS, &[acc, *key].concat()))
}

/// The hash of outputs a condition is on: their items, one after
/// another.
pub fn covered(outputs: &[crate::listed::Output]) -> Digest {
    outputs.iter().fold(EMPTY, |acc, o| hash_domain(DOM_COVERED, &[acc, o.item()].concat()))
}

/// What a channel's keys sign: the channel, the covered outputs' hash,
/// and the state.
pub fn rebind_message(channel: &Digest, cover: &Digest, state: u32) -> Digest {
    hash_domain(DOM_REBIND, &[&channel[..], cover, &state.to_le_bytes()].concat())
}

impl Cond {
    pub fn digest(&self) -> Digest {
        let block = match self {
            Cond::Thresh { m, keys } => block(1, *m, keys.len() as u32, &keys_digest(keys), 0),
            Cond::Hash(hash) => block(2, 0, 0, hash, 0),
            Cond::After(height) => block(3, 0, 0, &EMPTY, *height),
            Cond::Older(blocks) => block(4, 0, 0, &EMPTY, *blocks),
            Cond::State(above) => block(5, 0, 0, &EMPTY, *above),
            Cond::Outputs { count, digest } => block(6, *count, 0, digest, 0),
            Cond::Rebind { m, keys, channel } => block(7, *m, keys.len() as u32, &keys_from(channel, keys), 0),
        };
        hash_domain(DOM_COND, &block)
    }
}

/// A leaf's hash: its conditions', one after another.
pub fn leaf(conds: &[Cond]) -> Digest {
    assert!(!conds.is_empty(), "a leaf has a condition");
    conds.iter().fold(EMPTY, |acc, c| hash_domain(DOM_POLICY_LEAF, &[acc, c.digest()].concat()))
}

pub fn node(left: &Digest, right: &Digest) -> Digest {
    hash_domain(DOM_POLICY_NODE, &[*left, *right].concat())
}

/// A policy: its leaves, the others empty.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Policy(pub Vec<Vec<Cond>>);

impl Policy {
    fn at(&self, level: usize, index: usize) -> Digest {
        if level == 0 {
            return self.0.get(index).map_or(EMPTY, |conds| leaf(conds));
        }
        node(&self.at(level - 1, 2 * index), &self.at(level - 1, 2 * index + 1))
    }

    /// The root: what an output's commitment is to.
    pub fn root(&self) -> Digest {
        assert!(!self.0.is_empty() && self.0.len() <= 1 << DEPTH);
        self.at(DEPTH, 0)
    }

    /// Leaf `index`'s siblings, the lowest first.
    pub fn path(&self, index: usize) -> [Digest; DEPTH] {
        std::array::from_fn(|level| self.at(level, (index >> level) ^ 1))
    }
}

/// What a spend shows for a condition.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Shown {
    /// For each key of a threshold, in order: the key and the leaf of
    /// its signature, if it signs; its hash is in the condition.
    Signers(Vec<Option<(PublicKey, u64)>>),
    /// A hash lock's preimage.
    Preimage(Digest),
    Nothing,
}

/// An input that spends a policy's output: the output (its amount, its
/// memo, the height it was made at, where it lies), the leaf shown and
/// where it is in the policy's tree, and what is shown for each of the
/// leaf's conditions.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct PolicyInput {
    pub amount: u64,
    pub memo: crate::listed::Memo,
    pub created: u32,
    pub position: u64,
    pub conds: Vec<Cond>,
    pub index: usize,
    pub siblings: [Digest; DEPTH],
    pub shown: Vec<Shown>,
    /// The channel's state this spend is of, where a condition asks.
    pub state: u32,
}

impl PolicyInput {
    /// The policy's root: the path from the leaf shown.
    pub fn root(&self) -> Digest {
        let mut hash = leaf(&self.conds);
        for (level, sibling) in self.siblings.iter().enumerate() {
            hash = if self.index >> level & 1 == 0 { node(&hash, sibling) } else { node(sibling, &hash) };
        }
        hash
    }

    /// The output it spends.
    pub fn output(&self) -> crate::listed::Output {
        crate::listed::Output::to(&self.root(), self.amount, self.memo)
    }

    /// Whether the leaf's conditions hold in a block at `height`, for a
    /// transaction of id `id` whose covered outputs are `cover` (how
    /// many, and their hash; none if it covers none). `signed` says whether a key's signature
    /// of the id, with a leaf, is in the block's signed set.
    pub fn holds(
        &self,
        height: u32,
        id: &Digest,
        cover: Option<(u32, Digest)>,
        signed: &dyn Fn(&PublicKey, &Digest, u64) -> bool,
    ) -> bool {
        if self.conds.len() != self.shown.len() || self.conds.is_empty() || self.index >> DEPTH != 0 {
            return false;
        }
        // A threshold's signers: each the key listed in its place, each
        // signature there, and as many as asked.
        let threshold =
            |m: u32, keys: &[Digest], signers: &[Option<(PublicKey, u64)>], msg: &Digest, leaf: Option<u64>| {
                let named = (keys.iter().zip(signers))
                    .all(|(hash, s)| s.is_none_or(|(key, _)| crate::listed::key_hash(&key) == *hash));
                let with = signers.iter().flatten().all(|(_, at)| leaf.is_none_or(|l| l == *at));
                let signing = signers.iter().flatten().filter(|(key, at)| signed(key, msg, *at)).count();
                signers.len() == keys.len()
                    && named
                    && with
                    && signing == signers.iter().flatten().count()
                    && signing as u32 == m
            };
        self.conds.iter().zip(&self.shown).all(|(cond, shown)| match (cond, shown) {
            (Cond::Thresh { m, keys }, Shown::Signers(signers)) => threshold(*m, keys, signers, id, None),
            (Cond::Rebind { m, keys, channel }, Shown::Signers(signers)) => cover.is_some_and(|(_, c)| {
                threshold(*m, keys, signers, &rebind_message(channel, &c, self.state), Some(self.state as u64))
            }),
            (Cond::State(above), Shown::Nothing) => self.state > *above,
            (Cond::Outputs { count, digest }, Shown::Nothing) => cover == Some((*count, *digest)),
            (Cond::Hash(hash), Shown::Preimage(preimage)) => hash_lock(preimage) == *hash,
            (Cond::After(at), Shown::Nothing) => height >= *at,
            (Cond::Older(blocks), Shown::Nothing) => height >= self.created && height - self.created >= *blocks,
            _ => false,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::listed::key_hash;
    use crate::xmss::SecretKey;

    fn key(i: u8) -> PublicKey {
        SecretKey::generate_with_height(&[i; 32], 1).public_key()
    }

    #[test]
    fn a_policy_is_its_leaves_and_a_leaf_its_conditions() {
        let keys: Vec<Digest> = (0..3).map(|i| key_hash(&key(i))).collect();
        let multi = vec![Cond::Thresh { m: 2, keys: keys.clone() }];
        let back = vec![Cond::After(500), Cond::Thresh { m: 1, keys: keys[..1].to_vec() }];
        let policy = Policy(vec![multi.clone(), back.clone()]);
        let input = |conds: &[Cond], index: usize| PolicyInput {
            amount: 1,
            memo: [0; 20],
            created: 0,
            position: 0,
            conds: conds.to_vec(),
            index,
            siblings: policy.path(index),
            shown: vec![],
            state: 0,
        };
        assert_eq!(input(&multi, 0).root(), policy.root());
        assert_eq!(input(&back, 1).root(), policy.root());
        // A leaf at another place, or other conditions, is another root.
        assert_ne!(input(&multi, 1).root(), policy.root());
        let others: [Vec<Cond>; 5] = [
            vec![Cond::Thresh { m: 1, keys: keys.clone() }],
            vec![Cond::Thresh { m: 2, keys: keys[..2].to_vec() }],
            vec![Cond::Thresh { m: 2, keys: vec![keys[1], keys[0], keys[2]] }],
            vec![Cond::After(500)],
            vec![Cond::Thresh { m: 1, keys: keys[..1].to_vec() }, Cond::After(500)],
        ];
        for other in &others {
            assert!(leaf(other) != leaf(&multi) && leaf(other) != leaf(&back));
        }
        assert_ne!(Cond::After(7).digest(), Cond::Older(7).digest());
        assert_ne!(Cond::Hash([1; 32]).digest(), Cond::Hash([2; 32]).digest());
    }

    #[test]
    fn conditions_hold_when_they_are_met() {
        let keys: Vec<PublicKey> = (0..3).map(key).collect();
        let hashes: Vec<Digest> = keys.iter().map(key_hash).collect();
        let secret = [9u8; 32];
        let conds = vec![
            Cond::Thresh { m: 2, keys: hashes.clone() },
            Cond::Hash(hash_lock(&secret)),
            Cond::After(100),
            Cond::Older(10),
        ];
        let policy = Policy(vec![conds.clone()]);
        let id = [4u8; 32];
        let spend = |signers: [bool; 3], preimage: Digest| PolicyInput {
            amount: 5,
            memo: [0; 20],
            created: 95,
            position: 0,
            conds: conds.clone(),
            index: 0,
            siblings: policy.path(0),
            shown: vec![
                Shown::Signers((0..3).map(|i| signers[i].then_some((keys[i], 1))).collect()),
                Shown::Preimage(preimage),
                Shown::Nothing,
                Shown::Nothing,
            ],
            state: 0,
        };
        let all = |_: &PublicKey, _: &Digest, _: u64| true;
        let good = spend([true, false, true], secret);
        assert!(good.holds(105, &id, None, &all));
        // Too few signers or too many; one whose signature is not there;
        // the wrong secret; too early; too young.
        assert!(!spend([true, false, false], secret).holds(105, &id, None, &all));
        assert!(!spend([true, true, true], secret).holds(105, &id, None, &all));
        assert!(!good.holds(105, &id, None, &|key, _, _| *key != keys[2]));
        assert!(!spend([true, false, true], [8; 32]).holds(105, &id, None, &all));
        assert!(!good.holds(99, &id, None, &all));
        assert!(!good.holds(104, &id, None, &all));
        // A signer who is not the key listed there.
        let mut other = good.clone();
        other.shown[0] = Shown::Signers(vec![Some((keys[1], 1)), None, Some((keys[2], 1))]);
        assert!(!other.holds(105, &id, None, &all));
    }
}
