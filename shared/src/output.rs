//! Outputs, what they commit to and the plain way to spend one: the
//! types and hashes shared by transactions, spend policies, blocks and
//! the state tree.
//!
//! An output pays `amount` to the key with hash `H(pubkey)`; only its
//! commitment `H(H(pubkey) || amount)` goes on chain, with its memo. Every
//! output uses a fresh key, so the key hash is a secret of the payer and
//! payee and the commitment hides the key from everyone else.
//!
//! An output's memo is twenty bytes its owner's wallet fills to find the
//! output again from its seed; consensus only carries it, bound to the
//! amount in a memo slot ([`memo_slot`]).
//!
//! The hashes are [`crate::ledger`]'s, each one block of Blake3, which
//! is what the proofs compute. Encodings are little-endian:
//!
//! ```text
//! output := key hash (32) | amount u64 (8) | memo (20)
//! input  := pubkey (49) | amount u64 (8) | position u64 (8) | signature
//! ```
//!
//! To spend an output, an [`Input`] reveals the public key and the amount
//! (from which the commitment is recomputed and the output found) and
//! carries an XMSS signature, made with that key, over the body of the
//! transaction it is part of. A signature's size grows with the key's tree
//! height: 2312 bytes at [`TREE_HEIGHT`]. Outputs under a spend policy
//! are spent otherwise ([`crate::conditions`]).
//!
//! Each input consumes one XMSS leaf of its key, so a key with tree height
//! [`TREE_HEIGHT`] can appear in at most `2^TREE_HEIGHT` inputs in total.

use crate::codec::{DIGEST_BYTES, read_digest, read_u64};
use crate::error::Error;
use crate::hash::{DOM_STATE_LEAF, Digest, digest_to_bytes, hash_domain};
use crate::xmss::{PublicKey, SecretKey, Signature};

/// Outputs the chain can ever hold: an output's position is below this.
/// Positions are given out in order and never again, and the state tree
/// has this many leaves for them. A block of 2 MB creates fewer than 30,000 outputs, so
/// the 52,927,920 blocks of the emission schedule, every one full, use
/// `2^40.53` positions.
pub const OUTPUT_CAPACITY: u64 = 1 << 41;
const _: () = assert!(OUTPUT_CAPACITY <= 1 << (8 * crate::codec::POSITION_BYTES));

/// An output commitment `H(H(pubkey) || amount)`.
pub type Commitment = Digest;
/// Bytes of an output's memo: a nonce of sixteen and a recognition tag.
pub const MEMO_LEN: usize = crate::ledger::MEMO;
/// An output's recovery memo: opaque to consensus.
pub type Memo = crate::ledger::Memo;
/// The empty memo.
pub const EMPTY_MEMO: Memo = [0; MEMO_LEN];

/// Serialized size of a memo.
pub const MEMO_BYTES: usize = MEMO_LEN;
/// Serialized size of an [`Output`].
pub const OUTPUT_SIZE: usize = DIGEST_BYTES + 8 + MEMO_BYTES;

// ---------------------------------------------------------------------------
// Hashing
// ---------------------------------------------------------------------------

/// `H(pubkey)`: the root, the public seed and the tree height.
pub fn pubkey_hash(pk: &PublicKey) -> Digest {
    crate::ledger::key_hash(pk)
}

/// `H(H(pubkey) || amount)`, the commitment stored in an output.
pub fn commitment(pk: &PublicKey, amount: u64) -> Commitment {
    key_commitment(&pubkey_hash(pk), amount)
}

/// What a leaf and a block's lists take for an output's memo: the memo's
/// twenty bytes, then the amount's eight, then four of zero, so that the
/// amount, public, is carried wherever the memo is. An output of amount
/// zero (a name commit) has the memo padded with zeros.
pub fn memo_slot(memo: &Memo, amount: u64) -> Digest {
    let mut slot = [0u8; DIGEST_BYTES];
    slot[..MEMO_LEN].copy_from_slice(memo);
    slot[MEMO_LEN..MEMO_LEN + 8].copy_from_slice(&amount.to_le_bytes());
    slot
}

/// The memo and the amount a slot holds; `None` if its last bytes are
/// not zero.
pub fn slot_parts(slot: &Digest) -> Option<(Memo, u64)> {
    let memo: Memo = slot[..MEMO_LEN].try_into().unwrap();
    let amount = u64::from_le_bytes(slot[MEMO_LEN..MEMO_LEN + 8].try_into().unwrap());
    (slot[MEMO_LEN + 8..] == [0; 4]).then_some((memo, amount))
}

/// A memo from a digest's first bytes (tests).
#[cfg(test)]
pub(crate) fn memo5(d: Digest) -> Memo {
    d[..MEMO_LEN].try_into().unwrap()
}

/// A memo's bytes.
pub fn memo_to_bytes(memo: &Memo) -> [u8; MEMO_BYTES] {
    *memo
}

/// A memo from its bytes: an error on a wrong length.
pub fn memo_from_bytes(bytes: &[u8]) -> Result<Memo, Error> {
    memo_decode(bytes).ok_or(Error::Malformed("memo"))
}

fn memo_decode(bytes: &[u8]) -> Option<Memo> {
    bytes.try_into().ok()
}

/// The state tree leaf from a commitment, a memo slot ([`memo_slot`]) and
/// a creation height: one hash of the commitment, the memo, the amount
/// and the height ([`crate::ledger::Output::leaf`]), so the state root
/// covers the memo and the amount too.
pub fn leaf(commitment: &Commitment, slot: &Digest, height: u32) -> Digest {
    let mut block = [0u8; 64];
    block[..32].copy_from_slice(commitment);
    block[32..60].copy_from_slice(&slot[..MEMO_LEN + 8]);
    block[60..].copy_from_slice(&height.to_le_bytes());
    hash_domain(DOM_STATE_LEAF, &block)
}

/// The state tree leaf of an unspent output.
pub fn output_leaf(commitment: &Commitment, memo: &Memo, amount: u64, height: u32) -> Digest {
    leaf(commitment, &memo_slot(memo, amount), height)
}

/// `H(key_hash || amount)`: [`commitment`] from the key's hash.
pub fn key_commitment(key_hash: &Digest, amount: u64) -> Commitment {
    crate::ledger::commitment(key_hash, amount)
}

// ---------------------------------------------------------------------------
// Outputs
// ---------------------------------------------------------------------------

/// A newly created output: the recipient's key hash and the amount, which
/// travel with the transaction, the commitment derived from them, and the
/// memo. The commitment and the memo are all that goes on chain.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct Output {
    pub key_hash: Digest,
    pub amount: u64,
    pub commitment: Commitment,
    pub memo: Memo,
}

impl Output {
    /// Creates an output paying `amount` to `pk`, with an empty memo.
    pub fn new(pk: &PublicKey, amount: u64) -> Output {
        Output::to_key_hash(&pubkey_hash(pk), amount)
    }

    /// Creates an output paying `amount` to the key with hash `key_hash`,
    /// with an empty memo.
    pub fn to_key_hash(key_hash: &Digest, amount: u64) -> Output {
        Output::with_memo(key_hash, amount, EMPTY_MEMO)
    }

    /// The output as the proofs' rules take it ([`crate::ledger`]).
    pub fn listed(&self) -> crate::ledger::Output {
        crate::ledger::Output { commitment: self.commitment, memo: self.memo, amount: self.amount }
    }

    /// The part a block lists: the commitment, the memo and the amount.
    pub fn block_output(&self) -> BlockOutput {
        BlockOutput { commitment: self.commitment, memo: self.memo, amount: self.amount }
    }

    /// Its memo slot ([`memo_slot`]).
    pub fn slot(&self) -> Digest {
        memo_slot(&self.memo, self.amount)
    }

    /// Creates an output with a memo.
    pub fn with_memo(key_hash: &Digest, amount: u64, memo: Memo) -> Output {
        Output { key_hash: *key_hash, amount, commitment: key_commitment(key_hash, amount), memo }
    }

    /// Key hash, amount, memo; the commitment is recomputed on decoding.
    pub fn to_bytes(&self) -> [u8; OUTPUT_SIZE] {
        let mut out = [0u8; OUTPUT_SIZE];
        out[..DIGEST_BYTES].copy_from_slice(&digest_to_bytes(&self.key_hash));
        out[DIGEST_BYTES..DIGEST_BYTES + 8].copy_from_slice(&self.amount.to_le_bytes());
        out[DIGEST_BYTES + 8..].copy_from_slice(&memo_to_bytes(&self.memo));
        out
    }

    /// Whether `bytes` are an output's encoding: [`Output::from_bytes`]
    /// would read them. Does not compute the commitment.
    pub fn is_encoding(bytes: &[u8]) -> bool {
        bytes.len() == OUTPUT_SIZE
            && read_digest(bytes).is_some()
            && memo_from_bytes(&bytes[DIGEST_BYTES + 8..]).is_ok()
    }

    pub fn from_bytes(bytes: &[u8]) -> Result<Output, Error> {
        Self::decode(bytes).ok_or(Error::Malformed("output"))
    }

    fn decode(bytes: &[u8]) -> Option<Output> {
        if bytes.len() != OUTPUT_SIZE {
            return None;
        }
        let (key_hash, rest) = read_digest(bytes)?;
        let (amount, rest) = read_u64(rest)?;
        let memo = memo_decode(rest)?;
        Some(Output::with_memo(&key_hash, amount, memo))
    }
}

/// Serialized size of a [`BlockOutput`]: commitment, memo and amount.
pub const BLOCK_OUTPUT_SIZE: usize = DIGEST_BYTES + MEMO_BYTES + 8;

/// An output as a block lists it: what of an [`Output`] goes on chain.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct BlockOutput {
    pub commitment: Commitment,
    pub memo: Memo,
    /// Public: every node sums these to check the supply, and the proof
    /// binds it to the amount the commitment hides.
    pub amount: u64,
}

impl BlockOutput {
    /// The output as the proofs' rules take it ([`crate::ledger`]).
    pub fn listed(&self) -> crate::ledger::Output {
        crate::ledger::Output { commitment: self.commitment, memo: self.memo, amount: self.amount }
    }

    /// Its memo slot: the memo and the amount, as leaves and lists take it.
    pub fn slot(&self) -> Digest {
        memo_slot(&self.memo, self.amount)
    }

    /// Commitment, memo, amount.
    pub fn to_bytes(&self) -> [u8; BLOCK_OUTPUT_SIZE] {
        let mut out = [0u8; BLOCK_OUTPUT_SIZE];
        out[..DIGEST_BYTES].copy_from_slice(&digest_to_bytes(&self.commitment));
        out[DIGEST_BYTES..DIGEST_BYTES + MEMO_BYTES].copy_from_slice(&memo_to_bytes(&self.memo));
        out[DIGEST_BYTES + MEMO_BYTES..].copy_from_slice(&self.amount.to_le_bytes());
        out
    }

    pub fn from_bytes(bytes: &[u8]) -> Result<BlockOutput, Error> {
        Self::decode(bytes).ok_or(Error::Malformed("block output"))
    }

    fn decode(bytes: &[u8]) -> Option<BlockOutput> {
        if bytes.len() != BLOCK_OUTPUT_SIZE {
            return None;
        }
        let (commitment, rest) = read_digest(bytes)?;
        let memo = memo_decode(&rest[..MEMO_BYTES])?;
        let (amount, _) = read_u64(&rest[MEMO_BYTES..])?;
        Some(BlockOutput { commitment, memo, amount })
    }
}

impl From<Commitment> for BlockOutput {
    /// An output with an empty memo and amount zero.
    fn from(commitment: Commitment) -> BlockOutput {
        BlockOutput { commitment, memo: EMPTY_MEMO, amount: 0 }
    }
}

/// A transaction's outputs as a spend's check reads them: how many there
/// are, and each one's commitment and memo slot. A slice of outputs is
/// one; so is a transaction's encoding, read where it lies.
pub trait OutputList {
    fn len(&self) -> usize;

    fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// The commitment and the memo slot of output `i`. Panics past the end.
    fn pair(&self, i: usize) -> (Commitment, Digest);
}

impl OutputList for [Output] {
    fn len(&self) -> usize {
        <[Output]>::len(self)
    }

    fn pair(&self, i: usize) -> (Commitment, Digest) {
        (self[i].commitment, self[i].slot())
    }
}

impl OutputList for Vec<Output> {
    fn len(&self) -> usize {
        Vec::len(self)
    }

    fn pair(&self, i: usize) -> (Commitment, Digest) {
        self.as_slice().pair(i)
    }
}

impl<const N: usize> OutputList for [Output; N] {
    fn len(&self) -> usize {
        N
    }

    fn pair(&self, i: usize) -> (Commitment, Digest) {
        self.as_slice().pair(i)
    }
}

// ---------------------------------------------------------------------------
// Inputs
// ---------------------------------------------------------------------------

/// XMSS tree height of payment keys (16 leaves per key).
pub const TREE_HEIGHT: usize = crate::xmss::PLAIN_HEIGHT;
/// Signature type used in inputs.
pub type Sig = Signature;
/// Secret key type matching [`Sig`].
pub type Key = SecretKey;
/// Serialized size of an [`Input`] whose key has [`TREE_HEIGHT`]; an input
/// is [`Input::size`] bytes in general.
pub const INPUT_SIZE: usize = PublicKey::SIZE + 8 + 8 + Signature::size(TREE_HEIGHT);

/// A spend of an existing output: the revealed key and amount plus a
/// signature over the transaction body, and the output's position in the
/// UTXO set. The position is not signed (nor part of the transaction id):
/// it only tells nodes where to find the output, which they check, so a
/// wallet can correct it after a reorganization moves the output.
///
/// An input holds no memory but its own: reading one from bytes allocates
/// nothing.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Input {
    pub pubkey: PublicKey,
    pub amount: u64,
    pub position: u64,
    pub signature: Sig,
}

impl Input {
    /// Offset of the position in an input's encoding: it is not signed, so
    /// it may be rewritten in place.
    pub const POSITION_AT: usize = PublicKey::SIZE + 8;

    /// The commitment of the output this input spends.
    pub fn commitment(&self) -> Commitment {
        commitment(&self.pubkey, self.amount)
    }

    /// Serialized size: the signature's grows with the key's tree height.
    pub fn size(&self) -> usize {
        PublicKey::SIZE + 8 + 8 + Signature::size(self.pubkey.height())
    }

    /// Writes the input to `out`, which must be [`Input::size`] long.
    /// Panics if the signature is not of the key's height: such an input
    /// has no encoding.
    pub fn write_bytes(&self, out: &mut [u8]) {
        assert_eq!(out.len(), self.size(), "buffer is not the input's size");
        let (pk, rest) = out.split_at_mut(PublicKey::SIZE);
        pk.copy_from_slice(&self.pubkey.to_bytes());
        rest[..8].copy_from_slice(&self.amount.to_le_bytes());
        rest[8..16].copy_from_slice(&self.position.to_le_bytes());
        self.signature.write_bytes(&mut rest[16..]);
    }

    /// The input's bytes, in a new buffer on the heap.
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = vec![0u8; self.size()];
        self.write_bytes(&mut out);
        out
    }

    /// Parses an input from the front of `bytes`, returning the rest.
    pub fn read(bytes: &[u8]) -> Option<(Input, &[u8])> {
        let (pk, rest) = bytes.split_at_checked(PublicKey::SIZE)?;
        let pubkey = PublicKey::from_bytes(pk).ok()?;
        let (amount, rest) = read_u64(rest)?;
        let (position, rest) = read_u64(rest)?;
        let (sig, rest) = rest.split_at_checked(Signature::size(pubkey.height()))?;
        let signature = Sig::from_bytes(sig, pubkey.height()).ok()?;
        Some((Input { pubkey, amount, position, signature }, rest))
    }

    pub fn from_bytes(bytes: &[u8]) -> Result<Input, Error> {
        Self::decode(bytes).ok_or(Error::Malformed("input"))
    }

    fn decode(bytes: &[u8]) -> Option<Input> {
        match Self::read(bytes)? {
            (input, []) => Some(input),
            _ => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::xmss::SecretKey;

    fn key(tag: u8) -> SecretKey {
        let mut seed = [0u8; 32];
        seed[0] = tag;
        SecretKey::generate(&seed)
    }

    fn d(x: u32) -> Digest {
        std::array::from_fn(|i| (x as usize * 7 + i) as u8)
    }

    #[test]
    fn sizes() {
        assert_eq!(OUTPUT_SIZE, 60);
        assert_eq!(MEMO_BYTES, 20);
        assert_eq!(INPUT_SIZE, 49 + 8 + 8 + 2312);
        assert_eq!(TREE_HEIGHT, 4);
        assert_eq!(Key::generate(&[7; 32]).leaves(), 16);
    }

    /// An input reads back from its bytes, of whatever height its key is;
    /// its position is where POSITION_AT says and is not part of what it
    /// spends; other lengths and a signature of another height are refused.
    #[test]
    fn input_encoding() {
        let body = d(99);
        for height in [1usize, TREE_HEIGHT, 7] {
            let mut sk = SecretKey::generate_with_height(&[height as u8; 32], height);
            let input = Input {
                pubkey: sk.public_key(),
                amount: u64::MAX - 3,
                position: 1 << 39,
                signature: sk.sign(&body).unwrap(),
            };
            assert_eq!(input.size(), PublicKey::SIZE + 16 + Signature::size(height));
            assert_eq!(input.commitment(), commitment(&sk.public_key(), u64::MAX - 3));
            let bytes = input.to_bytes();
            assert_eq!(bytes.len(), input.size());
            let mut buf = vec![0u8; input.size()];
            input.write_bytes(&mut buf);
            assert_eq!(buf, bytes);
            assert_eq!(Input::from_bytes(&bytes), Ok(input.clone()));
            assert_eq!(Input::read(&[&bytes[..], &[5, 6]].concat()), Some((input.clone(), &[5u8, 6][..])));
            assert!(Input::from_bytes(&bytes[..bytes.len() - 1]).is_err());
            assert!(Input::from_bytes(&[&bytes[..], &[0]].concat()).is_err());
            let mut moved = bytes.clone();
            moved[Input::POSITION_AT..Input::POSITION_AT + 8].copy_from_slice(&7u64.to_le_bytes());
            let moved = Input::from_bytes(&moved).unwrap();
            assert_eq!((moved.position, moved.commitment()), (7, input.commitment()));
            assert!(moved.pubkey.verify(&body, &moved.signature));
            // A key that says another height: the signature is not its length.
            let mut other = bytes.clone();
            other[PublicKey::SIZE - 1] = height as u8 + 1;
            assert!(Input::from_bytes(&other).is_err());
        }
        // An input whose signature is not of its key's height has no encoding.
        let mut a = SecretKey::generate_with_height(&[1; 32], 2);
        let b = SecretKey::generate_with_height(&[2; 32], 3);
        let mixed = Input { pubkey: b.public_key(), amount: 1, position: 0, signature: a.sign(&body).unwrap() };
        assert!(std::panic::catch_unwind(|| mixed.to_bytes()).is_err());
    }

    /// The input decoder, fuzzed: no input makes it panic, and what it
    /// decodes encodes back to the same bytes.
    #[test]
    fn fuzz_input_decoder() {
        let mut sk = key(9);
        let input = Input { pubkey: sk.public_key(), amount: 7, position: 12345, signature: sk.sign(&d(1)).unwrap() };
        crate::test_util::fuzz_decoder("Input::read", &[input.to_bytes()], 20_000, |b| {
            Input::read(b).map(|(i, rest)| Some([i.to_bytes(), rest.to_vec()].concat()))
        });
    }

    #[test]
    fn commitments() {
        let a = key(1).public_key();
        let b = key(2).public_key();
        assert_eq!(commitment(&a, 5), commitment(&a, 5));
        assert_ne!(commitment(&a, 5), commitment(&a, 6));
        assert_ne!(commitment(&a, 5), commitment(&b, 5));
        assert_ne!(commitment(&a, 5), pubkey_hash(&a));
        assert_ne!(pubkey_hash(&a), pubkey_hash(&b));
        let out = Output::new(&a, 5);
        assert_eq!(out.amount, 5);
        assert_eq!(out.commitment, commitment(&a, 5));
        assert_eq!(out.commitment, key_commitment(&pubkey_hash(&a), 5));
    }

    /// A slot gives back its memo and amount, and is not one with
    /// anything after them.
    #[test]
    fn memo_slots_hold_the_memo_and_the_amount() {
        let memo = memo5(d(40));
        for amount in [0u64, 1, 1 << 30, 1 << 60, u64::MAX] {
            let slot = memo_slot(&memo, amount);
            assert_eq!(slot_parts(&slot), Some((memo, amount)));
            assert_eq!(Output::with_memo(&d(1), amount, memo).slot(), slot);
        }
        for at in MEMO_LEN + 8..DIGEST_BYTES {
            let mut slot = memo_slot(&memo, 7);
            slot[at] = 1;
            assert_eq!(slot_parts(&slot), None, "byte {at}");
        }
        assert_eq!(memo_from_bytes(&memo_to_bytes(&memo)), Ok(memo));
        assert!(memo_from_bytes(&memo_to_bytes(&memo)[1..]).is_err());
    }

    /// A leaf depends on each of the commitment, the memo, the amount and
    /// the height.
    #[test]
    fn leaves_cover_every_part() {
        let (c, memo) = (d(1), memo5(d(2)));
        let leaf0 = output_leaf(&c, &memo, 5, 9);
        assert_eq!(leaf0, leaf(&c, &memo_slot(&memo, 5), 9));
        // And it is the leaf the proofs' rules make.
        assert_eq!(leaf0, crate::ledger::Output { commitment: c, memo, amount: 5 }.leaf(9));
        assert_ne!(leaf0, output_leaf(&d(3), &memo, 5, 9));
        assert_ne!(leaf0, output_leaf(&c, &memo5(d(4)), 5, 9));
        assert_ne!(leaf0, output_leaf(&c, &memo, 6, 9));
        assert_ne!(leaf0, output_leaf(&c, &memo, 5, 10));
    }

    /// A list of outputs gives each one's commitment and slot, whether a
    /// slice, a vector or an array; `is_encoding` says what `from_bytes` reads.
    #[test]
    fn output_lists_and_encodings() {
        let outs = [Output::with_memo(&d(1), 5, memo5(d(2))), Output::with_memo(&d(3), 6, memo5(d(4)))];
        fn check(list: &(impl OutputList + ?Sized), outs: &[Output]) {
            assert_eq!((list.len(), list.is_empty()), (outs.len(), outs.is_empty()));
            for (i, o) in outs.iter().enumerate() {
                assert_eq!(list.pair(i), (o.commitment, o.slot()));
            }
        }
        check(&outs, &outs);
        check(&outs[..], &outs);
        check(&outs.to_vec(), &outs);
        check(&outs[..0], &[]);
        let bytes = outs[0].to_bytes();
        assert!(Output::is_encoding(&bytes));
        assert!(!Output::is_encoding(&bytes[1..]) && !Output::is_encoding(&[&bytes[..], &[0]].concat()));
        assert_eq!(Output::from_bytes(&bytes[1..]), Err(Error::Malformed("output")));
    }

    /// What a block lists of an output is its commitment, memo and amount,
    /// and reads back from its 60 bytes.
    #[test]
    fn block_outputs() {
        let out = Output::with_memo(&d(7), u64::MAX - 1, memo5(d(8)));
        let listed = out.block_output();
        assert_eq!((listed.commitment, listed.memo, listed.amount), (out.commitment, out.memo, out.amount));
        assert_eq!(listed.slot(), out.slot());
        let bytes = listed.to_bytes();
        assert_eq!((bytes.len(), BLOCK_OUTPUT_SIZE), (60, 60));
        assert_eq!(BlockOutput::from_bytes(&bytes), Ok(listed));
        assert!(BlockOutput::from_bytes(&bytes[1..]).is_err());
        assert_eq!(BlockOutput::from(d(3)), BlockOutput { commitment: d(3), memo: EMPTY_MEMO, amount: 0 });
        crate::test_util::fuzz_decoder("BlockOutput::from_bytes", &[bytes.to_vec()], 20_000, |b| {
            BlockOutput::from_bytes(b).ok().map(|o| Some(o.to_bytes().to_vec()))
        });
    }

    /// The output decoder, fuzzed: no input makes it panic, and what it
    /// decodes encodes back to the same bytes.
    #[test]
    fn output_encoding() {
        let out = Output::with_memo(&d(7), u64::MAX, memo5(d(8)));
        let bytes = out.to_bytes();
        assert_eq!(Output::from_bytes(&bytes), Ok(out));
        assert!(Output::from_bytes(&bytes[1..]).is_err());
        crate::test_util::fuzz_decoder("Output::from_bytes", &[bytes.to_vec()], 20_000, |b| {
            Output::from_bytes(b).ok().map(|o| Some(o.to_bytes().to_vec()))
        });
    }
}
