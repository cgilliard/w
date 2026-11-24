//! Names: the rules by which a name is registered to a key and its
//! record changed, as the facts a node and a prover both compute.
//!
//! A name is taken in two steps, so that nobody who sees it being taken
//! can take it first:
//!
//! - **Commit** publishes a hash of the name, a salt and the owner. It
//!   becomes an output of no amount in the state, at the next position.
//! - **Reveal**, [`MIN_REVEAL`] to [`MAX_REVEAL`] blocks later, gives
//!   the name's record and the salt, spends the commitment's output and
//!   registers the name, if nobody has it.
//! - **Update** replaces a registered record. The owner's key signs the
//!   new record ([`update_message`]), and the new record has another
//!   owner: a key is used once.
//! - **Sweep** removes a commitment's output that was not revealed in
//!   time.
//!
//! # The registry
//!
//! A tree of [`HEIGHT`] levels, a name at the leaf its hash's first
//! bits say: empty where no name is, and where one is, the hash of the
//! name's hash and its record's. A name whose hash begins as a
//! registered one's does is not to be had. The state's root is the hash
//! of the outputs' root and the registry's ([`state_root`]).
//!
//! A block may hold [`MAX_COMMITS`] commits, [`MAX_REVEALS`] reveals,
//! [`MAX_UPDATES`] updates and [`MAX_SWEEPS`] sweeps.

use crate::hash::{
    DOM_COMMIT, DOM_NAME, DOM_NAME_LEAF, DOM_NAME_NODE, DOM_OP, DOM_RECORD, DOM_STATE, DOM_UPDATE, Digest, EMPTY,
    hash_domain,
};
use crate::listed::{Memo, Output};
use std::collections::HashMap;

/// Characters of the longest name.
pub const NAME_MAX: usize = 32;
/// Levels of the registry: a name's place is this many bits of its hash.
pub const HEIGHT: usize = 128;
/// Blocks after its commitment that a name may be revealed from, and to.
/// (These and the four after are the chain's too: [`crate::name`] and the
/// chain's parameters have them from here, and say why they are what
/// they are.)
pub const MIN_REVEAL: u32 = 1;
pub const MAX_REVEAL: u32 = 288;
/// What a block may hold of each.
pub const MAX_COMMITS: usize = 1;
pub const MAX_REVEALS: usize = 5;
pub const MAX_UPDATES: usize = 8;
pub const MAX_SWEEPS: usize = 16;

/// Whether `name` is a name: 1 to 32 of `a` to `z`, `0` to `9` and `_`.
pub fn is_name(name: &str) -> bool {
    let ok = |c: u8| c.is_ascii_lowercase() || c.is_ascii_digit() || c == b'_';
    (1..=NAME_MAX).contains(&name.len()) && name.bytes().all(ok)
}

/// A name's hash: of its characters, in a block of zeros.
pub fn name_hash(name: &str) -> Digest {
    assert!(is_name(name));
    let mut block = [0u8; 64];
    block[..name.len()].copy_from_slice(name.as_bytes());
    hash_domain(DOM_NAME, &block)
}

/// What a name is registered as: whose it is, a value and a memo.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Record {
    pub name: String,
    /// The owner's key's hash ([`crate::listed::key_hash`]).
    pub owner: Digest,
    pub value: Digest,
    pub memo: Digest,
}

impl Record {
    /// The record's hash: of the name's hash, the owner, the value and
    /// the memo.
    pub fn hash(&self) -> Digest {
        hash_domain(DOM_RECORD, &[name_hash(&self.name), self.owner, self.value, self.memo].concat())
    }

    /// The registry's leaf of the name with this record.
    pub fn leaf(&self) -> Digest {
        hash_domain(DOM_NAME_LEAF, &[name_hash(&self.name), self.hash()].concat())
    }
}

/// The commitment to registering the name of hash `name` to `owner`.
pub fn commit(name: &Digest, salt: &Digest, owner: &Digest) -> Digest {
    hash_domain(DOM_COMMIT, &[*name, *salt, *owner].concat())
}

/// The output a commitment is in the state: of no amount, and of no
/// key's (a payment's commitment is hashed in another domain).
pub fn commit_output(commit: &Digest, memo: Memo) -> Output {
    Output { commitment: *commit, memo, amount: 0 }
}

/// What the owner of a name signs to change its record to `new`.
pub fn update_message(new: &Record) -> Digest {
    hash_domain(DOM_UPDATE, &new.hash())
}

/// An operation on names, as a transaction carries it.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Op {
    Commit {
        commit: Digest,
        memo: Memo,
    },
    /// The record, the salt of its commitment, and where the
    /// commitment's output lies (which is not in the operation's hash).
    Reveal {
        record: Record,
        salt: Digest,
        position: u64,
    },
    Update {
        record: Record,
    },
}

impl Op {
    /// The operation as a transaction's id and the block's list take it:
    /// what kind it is, and the commitment with its memo, or the
    /// record.
    pub fn digest(&self) -> Digest {
        let mut block = [0u8; 64];
        match self {
            Op::Commit { commit, memo } => {
                block[0] = 1;
                block[4..36].copy_from_slice(commit);
                block[36..56].copy_from_slice(memo);
            }
            Op::Reveal { record, .. } | Op::Update { record } => {
                block[0] = if matches!(self, Op::Reveal { .. }) { 2 } else { 3 };
                block[4..36].copy_from_slice(&record.hash());
            }
        }
        hash_domain(DOM_OP, &block)
    }
}

/// A node of the registry.
pub fn node(left: &Digest, right: &Digest) -> Digest {
    hash_domain(DOM_NAME_NODE, &[*left, *right].concat())
}

/// The roots of empty registries: `[h]` of `2^h` empty leaves.
pub fn empty_roots() -> &'static [Digest; HEIGHT + 1] {
    static ROOTS: std::sync::OnceLock<[Digest; HEIGHT + 1]> = std::sync::OnceLock::new();
    ROOTS.get_or_init(|| {
        let mut roots = [EMPTY; HEIGHT + 1];
        for h in 0..HEIGHT {
            roots[h + 1] = node(&roots[h], &roots[h]);
        }
        roots
    })
}

/// A name's place in the registry: the first bits of its hash.
pub fn key(name: &Digest) -> u128 {
    u128::from_le_bytes(name[..16].try_into().unwrap())
}

/// The state's root: over the outputs' root and the registry's.
pub fn state_root(outputs: &Digest, names: &Digest) -> Digest {
    hash_domain(DOM_STATE, &[*outputs, *names].concat())
}

/// The registry, in memory, holding only what is not empty: for provers
/// and tests.
#[derive(Clone, Default)]
pub struct Names {
    nodes: HashMap<(u8, u128), Digest>,
    records: HashMap<u128, Record>,
}

impl Names {
    fn at(&self, level: usize, index: u128) -> Digest {
        self.nodes.get(&(level as u8, index)).copied().unwrap_or(empty_roots()[level])
    }

    pub fn root(&self) -> Digest {
        self.at(HEIGHT, 0)
    }

    /// The record at a name's place, if one is registered there.
    pub fn record(&self, name: &Digest) -> Option<&Record> {
        self.records.get(&key(name))
    }

    /// The siblings of a place's path, the lowest first.
    pub fn path(&self, key: u128) -> Vec<Digest> {
        (0..HEIGHT).map(|level| self.at(level, (key >> level) ^ 1)).collect()
    }

    /// Puts `record` at its name's place, whatever was there.
    pub fn set(&mut self, record: Record) {
        let key = key(&name_hash(&record.name));
        let mut hash = record.leaf();
        self.records.insert(key, record);
        for level in 0..=HEIGHT {
            let index = if level == HEIGHT { 0 } else { key >> level };
            self.nodes.insert((level as u8, index), hash);
            if level < HEIGHT {
                let sibling = self.at(level, index ^ 1);
                hash = if index & 1 == 0 { node(&hash, &sibling) } else { node(&sibling, &hash) };
            }
        }
    }
}

/// The root a path reaches from `leaf` at the place `key`.
pub fn path_root(leaf: &Digest, key: u128, siblings: &[Digest]) -> Digest {
    let mut hash = *leaf;
    for (level, sibling) in siblings.iter().enumerate() {
        hash = if key >> level & 1 == 0 { node(&hash, sibling) } else { node(sibling, &hash) };
    }
    hash
}

/// Why an operation cannot be applied.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Refused {
    /// Not a name, or a record whose name is none.
    NotAName,
    /// The commitment's output is not in the state where the reveal says,
    /// or is not of this name, salt and owner.
    NoCommitment,
    /// Revealed too soon or too late; or swept before it was too late.
    Window,
    /// The name's place is taken; or, for an update, is not this name's.
    Taken,
    NotRegistered,
    /// An update to the owner it already has.
    SameOwner,
}

/// Whether a commitment made at height `made` may be revealed at
/// `height`.
pub fn in_window(made: u32, height: u32) -> bool {
    height >= made && (MIN_REVEAL..=MAX_REVEAL).contains(&(height - made))
}

impl Names {
    /// Whether `record` may be registered by a reveal: its name a name,
    /// and nothing at its place.
    pub fn can_reveal(&self, record: &Record) -> Result<(), Refused> {
        if !is_name(&record.name) {
            return Err(Refused::NotAName);
        }
        match self.record(&name_hash(&record.name)) {
            Some(_) => Err(Refused::Taken),
            None => Ok(()),
        }
    }

    /// Whether `record` may replace what its name is registered as: the
    /// record there, which the owner's key must have signed
    /// [`update_message`] of `record` to change.
    pub fn can_update(&self, record: &Record) -> Result<&Record, Refused> {
        if !is_name(&record.name) {
            return Err(Refused::NotAName);
        }
        let old = self.record(&name_hash(&record.name)).ok_or(Refused::NotRegistered)?;
        if old.name != record.name {
            return Err(Refused::Taken);
        }
        if old.owner == record.owner {
            return Err(Refused::SameOwner);
        }
        Ok(old)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn record(name: &str, owner: u8) -> Record {
        Record { name: name.into(), owner: [owner; 32], value: [3; 32], memo: [4; 32] }
    }

    #[test]
    fn names_are_what_they_may_be() {
        for ok in ["a", "abc_123", &"z".repeat(32)] {
            assert!(is_name(ok), "{ok}");
        }
        for bad in ["", "A", "a b", "é", "a-b", &"z".repeat(33)] {
            assert!(!is_name(bad), "{bad}");
        }
        assert_ne!(name_hash("ab"), name_hash("a"));
        assert_ne!(name_hash("a"), name_hash("b"));
    }

    #[test]
    fn a_record_and_an_operation_are_all_of_what_they_say() {
        let r = record("alice", 1);
        let changes: [&dyn Fn(&mut Record); 4] =
            [&|r| r.name = "alicf".into(), &|r| r.owner[0] ^= 1, &|r| r.value[0] ^= 1, &|r| r.memo[0] ^= 1];
        for change in changes {
            let mut other = r.clone();
            change(&mut other);
            assert!(other.hash() != r.hash() && other.leaf() != r.leaf());
        }
        // A reveal and an update of one record are two operations; where
        // a reveal's commitment lies and its salt are not in its hash.
        let reveal = |salt: u8, position: u64| Op::Reveal { record: r.clone(), salt: [salt; 32], position };
        assert_eq!(reveal(1, 5).digest(), reveal(2, 9).digest());
        assert_ne!(reveal(1, 5).digest(), Op::Update { record: r.clone() }.digest());
        let c = commit(&name_hash("alice"), &[9; 32], &r.owner);
        assert_ne!(c, commit(&name_hash("alice"), &[8; 32], &r.owner));
        assert_ne!(c, commit(&name_hash("alice"), &[9; 32], &[2; 32]));
        let op = |memo: u8| Op::Commit { commit: c, memo: [memo; 20] }.digest();
        assert_ne!(op(1), op(2));
        // A commitment's output is of no amount.
        assert_eq!(commit_output(&c, [1; 20]).amount, 0);
    }

    #[test]
    fn the_registry_is_its_paths() {
        let mut names = Names::default();
        assert_eq!(names.root(), empty_roots()[HEIGHT]);
        let (a, b) = (record("alice", 1), record("bob", 2));
        let (ka, kb) = (key(&name_hash("alice")), key(&name_hash("bob")));
        // Before: nothing at alice's place; after: her leaf, by the same
        // path.
        let path = names.path(ka);
        assert_eq!(path_root(&EMPTY, ka, &path), names.root());
        names.set(a.clone());
        assert_eq!(path_root(&a.leaf(), ka, &path), names.root());
        names.set(b.clone());
        assert_eq!(path_root(&b.leaf(), kb, &names.path(kb)), names.root());
        assert_eq!(path_root(&a.leaf(), ka, &names.path(ka)), names.root());
        assert_eq!(names.record(&name_hash("bob")), Some(&b));
        assert_ne!(state_root(&[1; 32], &names.root()), state_root(&names.root(), &[1; 32]));
    }

    #[test]
    fn the_rules_of_revealing_and_updating() {
        let mut names = Names::default();
        let a = record("alice", 1);
        assert_eq!(names.can_reveal(&a), Ok(()));
        assert_eq!(names.can_update(&a), Err(Refused::NotRegistered));
        names.set(a.clone());
        assert_eq!(names.can_reveal(&a), Err(Refused::Taken));
        assert_eq!(names.can_update(&a), Err(Refused::SameOwner));
        assert_eq!(names.can_update(&record("alice", 2)), Ok(&a));
        assert_eq!(names.can_reveal(&record("Alice", 2)), Err(Refused::NotAName));
        assert!(
            !in_window(10, 10) && in_window(10, 11) && in_window(10, 298) && !in_window(10, 299) && !in_window(10, 9)
        );
    }
}
