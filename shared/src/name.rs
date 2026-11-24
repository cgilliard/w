//! Names: what a name, its record and a name operation are, and how each
//! is hashed and encoded. The registry that holds them is elsewhere; this
//! is what transactions, blocks and the registry share.
//!
//! # Model
//!
//! A name is 1 to [`NAME_MAX`] characters of [`CHARSET`]. Its [`Record`]
//! gives the hash of the key that may update it, the hash of the owner's
//! payment keys and the owner's wallet data. A name is registered in two
//! steps so that nobody watching can take it first: a *commit* publishes
//! `H(H(name), salt, owner)`, and some blocks later a *reveal* names the
//! commit and gives the record. An *update* replaces the record of a
//! registered name, signed by its current owner key, and must name
//! another owner key: every signed operation rotates the key.
//!
//! A [`NameOp`] is an operation as a transaction carries it; its
//! [`BlockNameOp`] is the public part, which a block lists. The salt of a
//! reveal and the key and signature of an update go to the block prover
//! only.
//!
//! Everything here is held in place: a name is a fixed array, so records
//! and operations own no heap memory and reading one from bytes allocates
//! nothing. A [`Name`] is well formed by construction, so a record or an
//! operation that exists has a hash.
//!
//! # Encoding
//!
//! All integers little-endian.
//!
//! ```text
//! record := u8 length | name | owner (32) | value (32) | memo (32)
//! block op := u8 1 | commit (32) | memo (20)            commit
//!           | u8 2 | record | position (6)              reveal
//!           | u8 3 | record                             update
//! op := block op, then
//!           nothing                                     commit
//!           | salt (32)                                 reveal
//!           | pubkey (49) | signature                   update
//! ```
//!
//! # Hashing
//!
//! The hashes are [`crate::registry`]'s, which is what the proofs
//! compute. An operation's digest is one block: its tag, then the commit
//! and its memo, or the record's hash. The record's hash covers the
//! name's hash, owner, value and memo. The witness (salt, key,
//! signature) and a reveal's commit position are not in the digest.

use core::fmt;
use core::ops::Deref;

use crate::codec::{DIGEST_BYTES, POSITION_BYTES, read_digest, read_position, write_position};
use crate::error::Error;
use crate::hash::{DOM_NAME_LEAF, DOM_OP, DOM_RECORD, DOM_UPDATE, Digest, digest_to_bytes, hash_domain};
use crate::output::{Key as OwnerKey, MEMO_BYTES, Memo, Sig, memo_from_bytes, memo_to_bytes, pubkey_hash};
use crate::registry;
use crate::xmss::PublicKey;

/// Longest name, in characters.
pub const NAME_MAX: usize = 32;
/// The characters a name may use.
pub const CHARSET: &[u8; 37] = b"abcdefghijklmnopqrstuvwxyz0123456789_";

/// Most reveals in a block. Every reveal needs a commit, so names come at
/// most one a block over time ([`MAX_COMMITS`]): 52,560 a year. Five let
/// reveals catch up after a burst rather than bid for one slot, so a
/// commit finds one within its window, with room to spare. Sub-names give names to as many
/// users as their owners admit, so few top-level ones are needed; a name
/// never expires, so a slow allocation keeps the namespace from being
/// taken early.
pub const MAX_REVEALS: usize = crate::registry::MAX_REVEALS;
/// Most commits in a block: one, the long-run rate of new names.
pub const MAX_COMMITS: usize = crate::registry::MAX_COMMITS;
/// Most updates in a block.
pub const MAX_UPDATES: usize = crate::registry::MAX_UPDATES;
/// Most swept commits in a block.
pub const MAX_SWEEPS: usize = crate::registry::MAX_SWEEPS;
/// A commit made in the block at height `h` can be revealed in blocks
/// `h + MIN_REVEAL` to `h + MAX_REVEAL`, and swept after that.
///
/// The least is one: a reveal is in a later block than its commit, and
/// that is all the chain asks. A commit a few blocks deep can be undone
/// by a reorganization of as many, and whoever saw the reveal could
/// then commit to the name first: how deep is deep enough is for
/// whoever registers the name to say, not the chain (the wallet waits
/// as long as it waits before it spends an output, unless told).
pub const MIN_REVEAL: u32 = crate::registry::MIN_REVEAL;
pub const MAX_REVEAL: u32 = crate::registry::MAX_REVEAL;

/// Whether a commit made at `commit_height` can be revealed at `height`,
/// where a commit waits `min_reveal` blocks ([`MIN_REVEAL`] on mainnet).
pub fn in_window(height: u32, commit_height: u32, min_reveal: u32) -> bool {
    height >= commit_height && (min_reveal..=MAX_REVEAL).contains(&(height - commit_height))
}

/// Whether a commit made at `commit_height` can be swept at `height`.
pub fn expired(height: u32, commit_height: u32) -> bool {
    height > commit_height && height - commit_height > MAX_REVEAL
}

/// Serialized size of a commit operation.
pub const COMMIT_OP_SIZE: usize = 1 + DIGEST_BYTES + MEMO_BYTES;
/// Serialized size of a record, less the name.
const RECORD_FIXED: usize = 1 + 3 * DIGEST_BYTES;
/// Serialized size of a reveal or update as a block lists it, less the name.
pub const RECORD_OP_FIXED: usize = 1 + RECORD_FIXED;
/// Serialized size of a [`Commit`].
pub const COMMIT_ENTRY: usize = DIGEST_BYTES + 4;

pub(crate) const TAG_COMMIT: u8 = 1;
pub(crate) const TAG_REVEAL: u8 = 2;
pub(crate) const TAG_UPDATE: u8 = 3;

// ---------------------------------------------------------------------------
// Names and their keys
// ---------------------------------------------------------------------------

/// Bits of a key: the first of the name's hash, which are its place in
/// the registry's tree.
pub const KEY_BITS: usize = registry::HEIGHT;

/// A name's key in the registry: [`KEY_BITS`] bits.
pub type Key = u128;

/// The key of a name's hash.
pub fn key_of(hash: &Digest) -> Key {
    registry::key(hash)
}

/// Whether `name` is well formed: 1 to [`NAME_MAX`] characters of
/// [`CHARSET`].
pub fn valid_name(name: &[u8]) -> bool {
    (1..=NAME_MAX).contains(&name.len()) && name.iter().all(|c| CHARSET.contains(c))
}

/// The hash of a well-formed name: of its characters, in a block of
/// zeros ([`crate::registry::name_hash`]).
pub fn name_hash(name: &[u8]) -> Result<Digest, Error> {
    Name::new(name).map(|n| n.hash())
}

/// The registry key of a well-formed name.
pub fn name_key(name: &[u8]) -> Result<Key, Error> {
    name_hash(name).map(|h| key_of(&h))
}

/// A well-formed name, held in place: 1 to [`NAME_MAX`] characters of
/// [`CHARSET`]. Reads as the slice of its characters.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct Name {
    len: u8,
    /// The characters, then zeros.
    chars: [u8; NAME_MAX],
}

impl Name {
    /// The name `name`; `None` unless it is well formed.
    pub fn new(name: &[u8]) -> Result<Name, Error> {
        Self::checked(name).ok_or(Error::Malformed("name"))
    }

    fn checked(name: &[u8]) -> Option<Name> {
        if !valid_name(name) {
            return None;
        }
        let mut chars = [0u8; NAME_MAX];
        chars[..name.len()].copy_from_slice(name);
        Some(Name { len: name.len() as u8, chars })
    }

    pub fn as_bytes(&self) -> &[u8] {
        &self.chars[..self.len as usize]
    }

    pub fn as_str(&self) -> &str {
        core::str::from_utf8(self.as_bytes()).expect("a name's characters are ASCII")
    }

    pub fn hash(&self) -> Digest {
        registry::name_hash(self.as_str())
    }

    /// Its key in the registry.
    pub fn key(&self) -> Key {
        key_of(&self.hash())
    }
}

impl Deref for Name {
    type Target = [u8];

    fn deref(&self) -> &[u8] {
        self.as_bytes()
    }
}

impl fmt::Display for Name {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

impl fmt::Debug for Name {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self.as_str())
    }
}

/// A commit `H(H(name), salt, owner)`: what a registrant publishes first.
pub fn commit_hash(name_hash: &Digest, salt: &Digest, owner: &Digest) -> Digest {
    registry::commit(name_hash, salt, owner)
}

// ---------------------------------------------------------------------------
// Records
// ---------------------------------------------------------------------------

/// A registered name.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Record {
    pub name: Name,
    /// Hash of the XMSS public key that may update the record.
    pub owner: Digest,
    /// The hash of the owner's payment keys.
    pub value: Digest,
    /// The owner's wallet data.
    pub memo: Digest,
}

impl Record {
    /// Serialized size of the largest record: room for any.
    pub const MAX_SIZE: usize = RECORD_FIXED + NAME_MAX;

    /// A record for `name`; `None` unless the name is well formed.
    pub fn new(name: &[u8], owner: Digest, value: Digest, memo: Digest) -> Result<Record, Error> {
        Ok(Record { name: Name::new(name)?, owner, value, memo })
    }

    pub fn key(&self) -> Key {
        self.name.key()
    }

    /// The record as the proofs' rules hold it ([`crate::registry`]).
    pub fn rule(&self) -> registry::Record {
        registry::Record { name: self.name.as_str().to_string(), owner: self.owner, value: self.value, memo: self.memo }
    }

    /// The value its registry leaf holds: the hash of the name's hash,
    /// owner, value and memo.
    pub fn leaf_value(&self) -> Digest {
        let mut input = [0u8; 4 * DIGEST_BYTES];
        input[..32].copy_from_slice(&self.name.hash());
        input[32..64].copy_from_slice(&self.owner);
        input[64..96].copy_from_slice(&self.value);
        input[96..].copy_from_slice(&self.memo);
        hash_domain(DOM_RECORD, &input)
    }

    /// Serialized size.
    pub fn size(&self) -> usize {
        RECORD_FIXED + self.name.len()
    }

    /// Writes the record to `out`, which must be [`Record::size`] long:
    /// length byte, name, owner, value, memo.
    pub fn write_bytes(&self, out: &mut [u8]) {
        assert_eq!(out.len(), self.size(), "buffer is not the record's size");
        let n = self.name.len();
        out[0] = n as u8;
        out[1..1 + n].copy_from_slice(&self.name);
        let rest = &mut out[1 + n..];
        rest[..DIGEST_BYTES].copy_from_slice(&digest_to_bytes(&self.owner));
        rest[DIGEST_BYTES..2 * DIGEST_BYTES].copy_from_slice(&digest_to_bytes(&self.value));
        rest[2 * DIGEST_BYTES..].copy_from_slice(&digest_to_bytes(&self.memo));
    }

    /// The record's bytes, in a new buffer on the heap.
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = vec![0u8; self.size()];
        self.write_bytes(&mut out);
        out
    }

    /// Reads a record from the front of `bytes`, returning the rest.
    pub fn read(bytes: &[u8]) -> Option<(Record, &[u8])> {
        let (&n, rest) = bytes.split_first()?;
        let (name, rest) = rest.split_at_checked(n as usize)?;
        let name = Name::checked(name)?;
        let (owner, rest) = read_digest(rest)?;
        let (value, rest) = read_digest(rest)?;
        let (memo, rest) = read_digest(rest)?;
        Some((Record { name, owner, value, memo }, rest))
    }

    /// A record that is the whole of `bytes`.
    pub fn from_bytes(bytes: &[u8]) -> Result<Record, Error> {
        Self::decode(bytes).ok_or(Error::Malformed("name record"))
    }

    fn decode(bytes: &[u8]) -> Option<Record> {
        match Self::read(bytes)? {
            (record, []) => Some(record),
            _ => None,
        }
    }
}

/// A commit as the registry's side table holds it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Commit {
    pub hash: Digest,
    pub height: u32,
}

impl Commit {
    pub fn to_bytes(self) -> [u8; COMMIT_ENTRY] {
        let mut out = [0u8; COMMIT_ENTRY];
        out[..DIGEST_BYTES].copy_from_slice(&digest_to_bytes(&self.hash));
        out[DIGEST_BYTES..].copy_from_slice(&self.height.to_le_bytes());
        out
    }

    pub fn from_bytes(bytes: &[u8]) -> Result<Commit, Error> {
        Self::decode(bytes).ok_or(Error::Malformed("name commit"))
    }

    fn decode(bytes: &[u8]) -> Option<Commit> {
        if bytes.len() != COMMIT_ENTRY {
            return None;
        }
        let (hash, rest) = read_digest(bytes)?;
        Some(Commit { hash, height: u32::from_le_bytes(rest.try_into().unwrap()) })
    }
}

/// The message the current owner signs to update a record to `record`:
/// the hash of its [leaf value](Record::leaf_value), which covers the
/// name, owner, value and memo.
pub fn update_message(record: &Record) -> Digest {
    hash_domain(DOM_UPDATE, &record.leaf_value())
}

// ---------------------------------------------------------------------------
// Operations
// ---------------------------------------------------------------------------

/// A name operation as a block lists it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BlockNameOp {
    /// Stores `commit` with the block height and `memo` as an output of
    /// amount zero at the next counter position.
    Commit { commit: Digest, memo: Memo },
    /// Registers the record; the commit at `commit` must be its, in the
    /// window.
    Reveal { record: Record, commit: u64 },
    /// Replaces the record of a registered name.
    Update(Record),
}

/// A name operation as a transaction carries it: the public part and
/// what the prover needs.
///
/// (An update carries a signature, and so is some 2,400 bytes where the
/// others are under 200. They are few and not kept long: it is left as
/// it is, and not put behind a pointer.)
#[allow(clippy::large_enum_variant)]
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum NameOp {
    Commit {
        commit: Digest,
        memo: Memo,
    },
    /// `commit` is the position of the commit's output, unsigned like an
    /// input's position.
    Reveal {
        record: Record,
        salt: Digest,
        commit: u64,
    },
    Update {
        record: Record,
        pubkey: PublicKey,
        signature: Sig,
    },
}

/// Which kind of operation, for counting against the caps.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum OpKind {
    Commit,
    Reveal,
    Update,
    /// Not an operation a transaction carries; counted like one.
    Sweep,
}

impl OpKind {
    /// The error of more operations of this kind than its cap.
    pub fn too_many(self) -> Error {
        Error::TooManyOps { kind: self.name(), cap: self.cap() }
    }

    pub fn cap(self) -> usize {
        match self {
            OpKind::Commit => MAX_COMMITS,
            OpKind::Reveal => MAX_REVEALS,
            OpKind::Update => MAX_UPDATES,
            OpKind::Sweep => MAX_SWEEPS,
        }
    }

    pub fn name(self) -> &'static str {
        match self {
            OpKind::Commit => "commit",
            OpKind::Reveal => "reveal",
            OpKind::Update => "update",
            OpKind::Sweep => "sweep",
        }
    }
}

/// Counts of each kind in `kinds`, indexed by `OpKind as usize`; an error
/// naming the kind if one exceeds its cap.
pub fn count_ops(kinds: impl IntoIterator<Item = OpKind>) -> Result<[usize; 4], Error> {
    let mut counts = [0usize; 4];
    for k in kinds {
        counts[k as usize] += 1;
        if counts[k as usize] > k.cap() {
            return Err(k.too_many());
        }
    }
    Ok(counts)
}

impl BlockNameOp {
    /// Serialized size of the largest: room for any.
    pub const MAX_SIZE: usize = 1 + Record::MAX_SIZE + POSITION_BYTES;

    pub fn kind(&self) -> OpKind {
        match self {
            BlockNameOp::Commit { .. } => OpKind::Commit,
            BlockNameOp::Reveal { .. } => OpKind::Reveal,
            BlockNameOp::Update(_) => OpKind::Update,
        }
    }

    fn tag(&self) -> u8 {
        match self {
            BlockNameOp::Commit { .. } => TAG_COMMIT,
            BlockNameOp::Reveal { .. } => TAG_REVEAL,
            BlockNameOp::Update(_) => TAG_UPDATE,
        }
    }

    /// The record a reveal or update writes.
    pub fn record(&self) -> Option<&Record> {
        match self {
            BlockNameOp::Commit { .. } => None,
            BlockNameOp::Reveal { record, .. } => Some(record),
            BlockNameOp::Update(r) => Some(r),
        }
    }

    /// The position a reveal spends.
    pub fn spends(&self) -> Option<u64> {
        match self {
            BlockNameOp::Reveal { commit, .. } => Some(*commit),
            _ => None,
        }
    }

    /// The operation's digest, over its tag and public fields: one block
    /// ([`crate::registry::Op::digest`]).
    pub fn digest(&self) -> Digest {
        let mut block = [0u8; 64];
        block[0] = self.tag();
        match self {
            BlockNameOp::Commit { commit, memo } => {
                block[4..36].copy_from_slice(commit);
                block[36..36 + MEMO_BYTES].copy_from_slice(memo);
            }
            BlockNameOp::Reveal { record, .. } | BlockNameOp::Update(record) => {
                block[4..36].copy_from_slice(&record.leaf_value());
            }
        }
        hash_domain(DOM_OP, &block)
    }

    /// Serialized size.
    pub fn size(&self) -> usize {
        match self {
            BlockNameOp::Commit { .. } => COMMIT_OP_SIZE,
            BlockNameOp::Reveal { record, .. } => 1 + record.size() + POSITION_BYTES,
            BlockNameOp::Update(r) => 1 + r.size(),
        }
    }

    /// Writes the operation to `out`, which must be [`BlockNameOp::size`]
    /// long. Panics for a reveal of a position that does not fit its bytes.
    pub fn write_bytes(&self, out: &mut [u8]) {
        assert_eq!(out.len(), self.size(), "buffer is not the operation's size");
        let (tag, rest) = out.split_first_mut().expect("an operation has a tag");
        *tag = self.tag();
        match self {
            BlockNameOp::Commit { commit, memo } => {
                rest[..DIGEST_BYTES].copy_from_slice(&digest_to_bytes(commit));
                rest[DIGEST_BYTES..].copy_from_slice(&memo_to_bytes(memo));
            }
            BlockNameOp::Reveal { record, commit } => {
                let (rec, position) = rest.split_at_mut(record.size());
                record.write_bytes(rec);
                write_position(position, *commit);
            }
            BlockNameOp::Update(r) => r.write_bytes(rest),
        }
    }

    /// The operation's bytes, in a new buffer on the heap.
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = vec![0u8; self.size()];
        self.write_bytes(&mut out);
        out
    }

    /// Parses one operation from the front of `bytes`; returns the rest.
    pub fn parse(bytes: &[u8]) -> Option<(BlockNameOp, &[u8])> {
        let (&tag, rest) = bytes.split_first()?;
        match tag {
            TAG_COMMIT => {
                let (commit, rest) = read_digest(rest)?;
                let (memo, rest) = rest.split_at_checked(MEMO_BYTES)?;
                let memo = memo_from_bytes(memo).ok()?;
                Some((BlockNameOp::Commit { commit, memo }, rest))
            }
            TAG_REVEAL => {
                let (record, rest) = Record::read(rest)?;
                let (commit, rest) = read_position(rest)?;
                Some((BlockNameOp::Reveal { record, commit }, rest))
            }
            TAG_UPDATE => Record::read(rest).map(|(r, rest)| (BlockNameOp::Update(r), rest)),
            _ => None,
        }
    }
}

impl NameOp {
    /// The operation as the proofs' rules hold it ([`crate::registry`]).
    pub fn rule(&self) -> registry::Op {
        match self {
            NameOp::Commit { commit, memo } => registry::Op::Commit { commit: *commit, memo: *memo },
            NameOp::Reveal { record, salt, commit } => {
                registry::Op::Reveal { record: record.rule(), salt: *salt, position: *commit }
            }
            NameOp::Update { record, .. } => registry::Op::Update { record: record.rule() },
        }
    }

    /// An update of `record`'s name to `record`, signed by `key`, the
    /// name's current owner key.
    pub fn update(record: Record, key: &mut OwnerKey) -> Result<NameOp, Error> {
        let signature = key.sign(&update_message(&record))?;
        Ok(NameOp::Update { record, pubkey: key.public_key(), signature })
    }

    pub fn kind(&self) -> OpKind {
        self.block_op().kind()
    }

    /// The part a block lists.
    pub fn block_op(&self) -> BlockNameOp {
        match self {
            NameOp::Commit { commit, memo } => BlockNameOp::Commit { commit: *commit, memo: *memo },
            NameOp::Reveal { record, commit, .. } => BlockNameOp::Reveal { record: *record, commit: *commit },
            NameOp::Update { record, .. } => BlockNameOp::Update(*record),
        }
    }

    /// The record a reveal or update writes.
    pub fn record(&self) -> Option<&Record> {
        match self {
            NameOp::Commit { .. } => None,
            NameOp::Reveal { record, .. } | NameOp::Update { record, .. } => Some(record),
        }
    }

    /// The digest of the public part: see [`BlockNameOp::digest`].
    pub fn digest(&self) -> Digest {
        self.block_op().digest()
    }

    /// For an update: whether the carried key is the one `current_owner`
    /// names, its signature covers the new record, and the record names a
    /// different owner. Other operations carry no signature and pass.
    pub fn verify_owner(&self, current_owner: &Digest) -> bool {
        match self {
            NameOp::Update { record, pubkey, signature } => {
                record.owner != *current_owner
                    && pubkey_hash(pubkey) == *current_owner
                    && pubkey.verify(&update_message(record), signature)
            }
            _ => true,
        }
    }

    /// Serialized size.
    pub fn size(&self) -> usize {
        self.block_op().size()
            + match self {
                NameOp::Commit { .. } => 0,
                NameOp::Reveal { .. } => DIGEST_BYTES,
                NameOp::Update { pubkey, .. } => PublicKey::SIZE + Sig::size(pubkey.height()),
            }
    }

    /// Writes the operation to `out`, which must be [`NameOp::size`] long.
    /// Panics for an update whose signature is not of its key's height:
    /// it has no encoding.
    pub fn write_bytes(&self, out: &mut [u8]) {
        assert_eq!(out.len(), self.size(), "buffer is not the operation's size");
        let public = self.block_op();
        let (head, rest) = out.split_at_mut(public.size());
        public.write_bytes(head);
        match self {
            NameOp::Commit { .. } => {}
            NameOp::Reveal { salt, .. } => rest.copy_from_slice(&digest_to_bytes(salt)),
            NameOp::Update { pubkey, signature, .. } => {
                let (pk, sig) = rest.split_at_mut(PublicKey::SIZE);
                pk.copy_from_slice(&pubkey.to_bytes());
                signature.write_bytes(sig);
            }
        }
    }

    /// The operation's bytes, in a new buffer on the heap.
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = vec![0u8; self.size()];
        self.write_bytes(&mut out);
        out
    }

    /// Parses one operation from the front of `bytes`; returns the rest.
    pub fn parse(bytes: &[u8]) -> Option<(NameOp, &[u8])> {
        let (op, rest) = BlockNameOp::parse(bytes)?;
        match op {
            BlockNameOp::Commit { commit, memo } => Some((NameOp::Commit { commit, memo }, rest)),
            BlockNameOp::Reveal { record, commit } => {
                let (salt, rest) = read_digest(rest)?;
                Some((NameOp::Reveal { record, salt, commit }, rest))
            }
            BlockNameOp::Update(record) => {
                let (pk, rest) = rest.split_at_checked(PublicKey::SIZE)?;
                let pubkey = PublicKey::from_bytes(pk).ok()?;
                let (sig, rest) = rest.split_at_checked(Sig::size(pubkey.height()))?;
                let signature = Sig::from_bytes(sig, pubkey.height()).ok()?;
                Some((NameOp::Update { record, pubkey, signature }, rest))
            }
        }
    }
}

/// The root of the names' tree with no names.
pub fn empty_root() -> Digest {
    registry::empty_roots()[KEY_BITS]
}

/// The leaf of the name whose hash is `name` and whose record's value
/// is `value` ([`Record::leaf_value`]).
pub fn leaf_hash(name: &Digest, value: &Digest) -> Digest {
    let mut block = [0u8; 64];
    block[..32].copy_from_slice(name);
    block[32..].copy_from_slice(value);
    hash_domain(DOM_NAME_LEAF, &block)
}

/// A record's leaf.
pub fn leaf_of(r: &Record) -> Digest {
    leaf_hash(&r.name.hash(), &r.leaf_value())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hash::EMPTY;
    use crate::output::{TREE_HEIGHT, memo5};

    fn d(n: u32) -> Digest {
        let mut x = EMPTY;
        x[..4].copy_from_slice(&n.to_le_bytes());
        x[20..24].copy_from_slice(&(n * 3).to_le_bytes());
        x
    }

    fn record(name: &str, n: u32) -> Record {
        Record::new(name.as_bytes(), d(n), d(n + 1), d(n + 2)).unwrap()
    }

    fn owner_key(tag: u8) -> OwnerKey {
        let mut seed = [0u8; 32];
        seed[0] = tag;
        seed[1] = 77;
        OwnerKey::generate(&seed)
    }

    #[test]
    fn names_are_validated_and_hashed() {
        assert!(valid_name(b"example"));
        assert!(valid_name(b"a"));
        assert!(valid_name(b"nvidia_2026"));
        assert!(valid_name(&[b'z'; NAME_MAX]));
        assert!(!valid_name(b""));
        assert!(!valid_name(&[b'z'; NAME_MAX + 1]));
        assert!(!valid_name(b"Example"));
        assert!(!valid_name(b"cool.example"));
        assert!(!valid_name(b"a-b"));
        assert!(!valid_name("é".as_bytes()));
        assert_eq!(CHARSET.len(), 37);
        assert_ne!(name_hash(b"az0_"), name_hash(b"az0"));
        assert!(name_hash(b"Az").is_err());
        assert_ne!(name_key(b"abc"), name_key(b"abd"));
        assert_eq!(name_key(b"abc"), name_key(b"abc"));
        // The commit binds every field.
        let h = name_hash(b"az0_").unwrap();
        let c = commit_hash(&h, &d(1), &d(2));
        assert_ne!(c, commit_hash(&h, &d(1), &d(3)));
        assert_ne!(c, commit_hash(&h, &d(9), &d(2)));
        assert_ne!(c, commit_hash(&name_hash(b"az0").unwrap(), &d(1), &d(2)));
    }

    /// A `Name` is a well-formed name and nothing else: it gives the hash
    /// and key the functions on bytes give, reads as its characters, and
    /// compares by them.
    #[test]
    fn a_name_is_well_formed_by_construction() {
        for bad in [&b""[..], &[b'z'; NAME_MAX + 1], b"Example", b"cool.example", b"a-b", "é".as_bytes(), b"a b"] {
            assert!(Name::new(bad).is_err());
        }
        for good in [&b"a"[..], b"example", b"nvidia_2026", &[b'z'; NAME_MAX], &[b'_'; NAME_MAX]] {
            let name = Name::new(good).unwrap();
            assert_eq!((name.as_bytes(), &name[..], name.len()), (good, good, good.len()));
            assert_eq!(name.as_str().as_bytes(), good);
            assert_eq!(Ok(name.hash()), name_hash(good));
            // It is the hash the proofs' rules give the name.
            assert_eq!(name.hash(), registry::name_hash(name.as_str()));
            assert_eq!(Ok(name.key()), name_key(good));
            assert_eq!(name.to_string().as_bytes(), good);
            assert_eq!(format!("{name:?}"), format!("{:?}", name.as_str()));
        }
        assert_eq!(Name::new(b"abc"), Name::new(b"abc"));
        assert_ne!(Name::new(b"abc"), Name::new(b"abcd"));
        assert_ne!(Name::new(b"abc"), Name::new(b"abd"));
        // A key is the hash's first bits.
        let hash: Digest = core::array::from_fn(|i| 255 - i as u8);
        assert_eq!(key_of(&hash), u128::from_le_bytes(hash[..16].try_into().unwrap()));
        assert_eq!(key_of(&EMPTY), 0);
    }

    #[test]
    fn records_round_trip() {
        let r = record("example", 4);
        assert_eq!(r.size(), 1 + 7 + 96);
        crate::test_util::fuzz_decoder("Record::from_bytes", &[r.to_bytes()], 20_000, |b| {
            Record::from_bytes(b).ok().map(|x| Some(x.to_bytes()))
        });
        let bytes = r.to_bytes();
        assert_eq!(bytes.len(), r.size());
        assert_eq!(Record::from_bytes(&bytes), Ok(r));
        assert!(Record::from_bytes(&bytes[..bytes.len() - 1]).is_err());
        assert!(Record::from_bytes(&[&bytes[..], &[0]].concat()).is_err());
        assert_eq!(Record::read(&[&bytes[..], &[9]].concat()), Some((r, &[9u8][..])));
        let mut bad = bytes.clone();
        bad[1] = b'E';
        assert!(Record::from_bytes(&bad).is_err());
        // A length of none, and one past the longest name.
        let mut bad = bytes.clone();
        bad[0] = 0;
        assert_eq!(Record::read(&bad), None);
        let long = [&[NAME_MAX as u8 + 1][..], &[b'a'; NAME_MAX + 1], &[0u8; 96]].concat();
        assert_eq!(Record::read(&long), None);
        assert_ne!(r.leaf_value(), record("example", 5).leaf_value());
        assert_ne!(r.leaf_value(), record("exampl", 4).leaf_value());
        assert!(Record::new(b"", d(1), d(2), d(3)).is_err());
        assert_eq!(r.key(), r.name.key());
        // Its hash, and what its owner signs to change it, are the rules'.
        assert_eq!(r.leaf_value(), r.rule().hash());
        assert_eq!(update_message(&r), registry::update_message(&r.rule()));
        // The longest record fills MAX_SIZE.
        let longest = record(&"z".repeat(NAME_MAX), 1);
        assert_eq!(longest.size(), Record::MAX_SIZE);
        assert_eq!(Record::from_bytes(&longest.to_bytes()), Ok(longest));
        // A commit's side-table entry.
        let c = Commit { hash: d(8), height: 77 };
        assert_eq!(Commit::from_bytes(&c.to_bytes()), Ok(c));
        assert!(Commit::from_bytes(&c.to_bytes()[1..]).is_err());
    }

    #[test]
    fn operations_encode_digest_and_count() {
        let commit = NameOp::Commit { commit: d(1), memo: memo5(d(2)) };
        let reveal = NameOp::Reveal { record: record("alice", 3), salt: d(4), commit: 77 };
        let mut k = owner_key(1);
        let update = NameOp::update(record("alice", 5), &mut k).unwrap();
        // Fuzzed: a parse consumes one operation, written back the same.
        let samples: Vec<Vec<u8>> = [&commit, &reveal, &update].iter().map(|o| o.to_bytes()).collect();
        crate::test_util::fuzz_decoder("NameOp::parse", &samples, 20_000, |b| {
            NameOp::parse(b).map(|(op, rest)| Some([op.to_bytes(), rest.to_vec()].concat()))
        });
        let public: Vec<Vec<u8>> = [&commit, &reveal, &update].iter().map(|o| o.block_op().to_bytes()).collect();
        crate::test_util::fuzz_decoder("BlockNameOp::parse", &public, 20_000, |b| {
            BlockNameOp::parse(b).map(|(op, rest)| Some([op.to_bytes(), rest.to_vec()].concat()))
        });
        for op in [&commit, &reveal, &update] {
            let bytes = op.to_bytes();
            assert_eq!(bytes.len(), op.size());
            let (back, rest) = NameOp::parse(&bytes).unwrap();
            assert_eq!((&back, rest.len()), (op, 0));
            assert!(NameOp::parse(&bytes[..bytes.len() - 1]).is_none());
            let public = op.block_op();
            let pb = public.to_bytes();
            assert_eq!(pb.len(), public.size());
            assert!(pb.len() <= BlockNameOp::MAX_SIZE);
            assert_eq!(BlockNameOp::parse(&pb).unwrap(), (public, &[][..]));
            assert!(bytes.starts_with(&pb));
            assert_eq!(public.digest(), op.digest());
            assert_eq!((public.kind(), public.record()), (op.kind(), op.record()));
        }
        assert_eq!(commit.size(), COMMIT_OP_SIZE);
        assert_eq!(reveal.block_op().size(), RECORD_OP_FIXED + 5 + POSITION_BYTES);
        assert_eq!(reveal.size(), RECORD_OP_FIXED + 5 + POSITION_BYTES + 32);
        assert_eq!(POSITION_BYTES, 6);
        assert_eq!(update.size(), RECORD_OP_FIXED + 5 + PublicKey::SIZE + Sig::size(TREE_HEIGHT));
        // An operation's digest is the one the proofs' rules give it.
        for op in [&commit, &reveal, &update] {
            assert_eq!(op.digest(), op.rule().digest());
        }
        assert_eq!((commit.block_op().spends(), reveal.block_op().spends()), (None, Some(77)));
        assert_eq!((commit.record(), reveal.record()), (None, Some(&record("alice", 3))));
        // The largest reveal a block lists fills MAX_SIZE; its position is
        // six bytes, and one that does not fit them is not written short.
        let widest = BlockNameOp::Reveal { record: record(&"z".repeat(NAME_MAX), 1), commit: (1 << 48) - 1 };
        assert_eq!(widest.size(), BlockNameOp::MAX_SIZE);
        assert_eq!(BlockNameOp::parse(&widest.to_bytes()).unwrap(), (widest, &[][..]));
        let last = BlockNameOp::Reveal { record: record("alice", 3), commit: crate::output::OUTPUT_CAPACITY - 1 };
        assert_eq!(BlockNameOp::parse(&last.to_bytes()).unwrap(), (last, &[][..]));
        let too_far = NameOp::Reveal { record: record("alice", 3), salt: d(4), commit: 1 << 48 };
        assert!(std::panic::catch_unwind(|| too_far.to_bytes()).is_err());

        // Digests separate kinds and fields; the witness and the commit
        // position are not in them.
        let other_salt = NameOp::Reveal { record: record("alice", 3), salt: d(9), commit: 78 };
        assert_eq!(other_salt.digest(), reveal.digest());
        assert_ne!(reveal.digest(), NameOp::Reveal { record: record("alicf", 3), salt: d(4), commit: 77 }.digest());
        assert_ne!(BlockNameOp::Reveal { record: record("alice", 5), commit: 0 }.digest(), update.digest());
        assert_ne!(commit.digest(), NameOp::Commit { commit: d(2), memo: memo5(d(1)) }.digest());
        let mut digests: Vec<_> = [&commit, &reveal, &update].iter().map(|op| op.digest()).collect();
        digests.dedup();
        assert_eq!(digests.len(), 3);

        // A malformed name is no record, so no operation: its bytes are refused.
        let mut bad = reveal.block_op().to_bytes();
        bad[2] = b'A';
        assert!(BlockNameOp::parse(&bad).is_none());
        assert!(BlockNameOp::parse(&[9, 0, 0]).is_none());
        assert!(Record::new(b"Alice", d(1), d(2), d(3)).is_err());
        assert_eq!(Record::new(b"alice", d(1), d(2), d(3)), Ok(record("alice", 1)));

        // Counts against the caps.
        let kinds = |n: usize, k: OpKind| std::iter::repeat_n(k, n);
        assert_eq!(
            count_ops(kinds(MAX_REVEALS, OpKind::Reveal).chain(kinds(MAX_COMMITS, OpKind::Commit))),
            Ok([MAX_COMMITS, MAX_REVEALS, 0, 0])
        );
        assert_eq!(count_ops(kinds(MAX_COMMITS + 1, OpKind::Commit)), Err(OpKind::Commit.too_many()));
        assert_eq!(count_ops(kinds(MAX_REVEALS + 1, OpKind::Reveal)), Err(OpKind::Reveal.too_many()));
        assert_eq!(count_ops(kinds(MAX_UPDATES + 1, OpKind::Update)), Err(OpKind::Update.too_many()));
        assert_eq!(count_ops(kinds(MAX_SWEEPS + 1, OpKind::Sweep)), Err(OpKind::Sweep.too_many()));
        assert_eq!(count_ops(kinds(MAX_SWEEPS, OpKind::Sweep)), Ok([0, 0, 0, 16]));
        let names: Vec<&str> =
            [OpKind::Commit, OpKind::Reveal, OpKind::Update, OpKind::Sweep].map(OpKind::name).to_vec();
        assert_eq!(names, ["commit", "reveal", "update", "sweep"]);
    }

    #[test]
    fn updates_are_signed_by_the_current_owner_and_rotate_it() {
        let mut k1 = owner_key(1);
        let owner1 = pubkey_hash(&k1.public_key());
        let new = Record::new(b"alice", d(20), d(21), d(22)).unwrap();
        let update = NameOp::update(new, &mut k1).unwrap();
        assert!(update.verify_owner(&owner1));
        // Wrong current owner, wrong key, tampered record.
        assert!(!update.verify_owner(&d(99)));
        let mut k2 = owner_key(2);
        let by_other = NameOp::update(new, &mut k2).unwrap();
        assert!(!by_other.verify_owner(&owner1));
        if let NameOp::Update { record, pubkey, signature } = update.clone() {
            let mut tampered = record;
            tampered.value = d(5);
            assert!(!NameOp::Update { record: tampered, pubkey, signature: signature.clone() }.verify_owner(&owner1));
            // Keeping the same owner is refused: every signed operation rotates the key.
            let same = Record::new(b"alice", owner1, d(21), d(22)).unwrap();
            let op = NameOp::update(same, &mut k1).unwrap();
            assert!(!op.verify_owner(&owner1));
            // The message is domain separated from the leaf value.
            assert_ne!(update_message(&record), record.leaf_value());
        } else {
            unreachable!()
        }
        // Operations without a signature pass the owner check.
        assert!(NameOp::Commit { commit: d(1), memo: memo5(d(2)) }.verify_owner(&d(3)));
        assert!(NameOp::Reveal { record: new, salt: d(1), commit: 0 }.verify_owner(&d(3)));
        // A key with no leaf left signs no update.
        let mut spent = OwnerKey::generate_with_height(&[3; 32], 1);
        spent.set_next_index(2);
        assert_eq!(NameOp::update(new, &mut spent), Err(Error::KeyExhausted));
        // An update whose signature is not of its key's height has no encoding.
        let mut short = OwnerKey::generate_with_height(&[4; 32], 2);
        let signature = short.sign(&update_message(&new)).unwrap();
        let mixed = NameOp::Update { record: new, pubkey: k1.public_key(), signature };
        assert!(std::panic::catch_unwind(|| mixed.to_bytes()).is_err());
    }
}
