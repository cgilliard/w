//! XMSS (eXtended Merkle Signature Scheme) with WOTS+ one-time
//! signatures, over Blake3.
//!
//! The Merkle tree's height is a property of each key, 1 to
//! [`MAX_HEIGHT`], part of its public key; a key pair of height `h` can
//! sign `2^h` messages. Payment keys use [`PLAIN_HEIGHT`].
//!
//! # Construction
//!
//! A WOTS chain step is Blake3's keyed hash under a key that is the
//! step's tweak ([`th`]): the public seed (16 bytes), the leaf's index,
//! the chain and the step, and a word that holds the use's tag under a
//! marker no other key of this crate has ([`crate::hash`]'s keys end in
//! a zero word). The signer's own hashes (the chains' secret starts, the
//! randomizer, the seeds) are keyed the same way.
//!
//! | keyed use | tag | index | extra |
//! |---|---|---|---|
//! | WOTS secret chain starts | `PRF` | leaf | chain |
//! | WOTS chain steps | `CHAIN` | leaf | chain, and the step above 16 bits |
//! | message randomizer | `RAND` | leaf | 0 |
//! | seed expansion | `KEYGEN` | 0 or 1 | 0 |
//!
//! Everything else a verifier hashes is a hash in a domain of
//! [`crate::hash`]:
//!
//! - **The message digest and the leaf** (the WOTS public key, a hash
//!   of the 67 chain ends) begin with a [`head`]: the public seed, the
//!   leaf's index and the tree's height. So a signature is of one leaf
//!   of one key of one height, and of no other.
//! - **The tree's nodes** are the hash of their two children and
//!   nothing else: a Merkle path. This is not XMSS as published, whose
//!   nodes are tweaked each with its place; with digests of 256 bits
//!   the many targets that leaves an attacker cost a few dozen bits of
//!   a wide margin, and the height in the leaf is what keeps half a
//!   tree from being a key of its own.
//!
//! A digest is 32 bytes. WOTS+ uses the Winternitz parameter `w = 16`: a
//! digest is 64 digits of four bits, so 64 message chains, and 3 for the
//! checksum. Chain steps have a tweak each, not a bitmask, as in
//! SPHINCS+.
//!
//! # What a circuit pays
//!
//! A chain step is one compression: the tweak is the chaining value it
//! starts from, the digest its block. A tree node is one. The leaf is
//! three hashes of a chunk or less (of the first 31 ends, of the next
//! 31, and of the last five with those two digests), and the digest of
//! a 32-byte message is two blocks. A signature of a height-4 key is
//! 1,047 compressions to verify, 1,005 of them chain steps.
//!
//! # State
//!
//! XMSS is stateful: a leaf must never be used twice.
//! [`SecretKey::sign`] advances the index before it makes a signature,
//! and [`SecretKey::to_bytes`] records it: store the key after every
//! signature and never restore an older copy.

use crate::blake3::{self, OUT_LEN};
use crate::error::Error;
use crate::hash::{DOM_XMSS_LEAF, DOM_XMSS_MSG, DOM_XMSS_TREE, Digest, hash_domain};

/// Winternitz parameter.
pub const W: usize = 16;
/// `log2(W)`: bits of the message digest a chain takes.
pub const LOG_W: usize = 4;
/// Chains for the message digest: its digits.
pub const MSG_CHAINS: usize = 8 * OUT_LEN / LOG_W;
/// Chains for the checksum.
pub const CSUM_CHAINS: usize = 3;
pub const CHAINS: usize = MSG_CHAINS + CSUM_CHAINS;
/// The largest checksum: every digit zero.
pub const MAX_CSUM: usize = MSG_CHAINS * (W - 1);
const _: () = assert!(MAX_CSUM < 1 << (CSUM_CHAINS * LOG_W));

/// Bytes of the seed a key pair is made from.
pub const SEED_SIZE: usize = 32;
/// Height of a payment key's tree.
pub const PLAIN_HEIGHT: usize = 4;
/// The tallest tree.
pub const MAX_HEIGHT: usize = 20;
/// Bytes of a public seed.
pub const PUB_SEED_LEN: usize = 16;
pub type PubSeed = [u8; PUB_SEED_LEN];
/// Bytes of a stored secret key.
pub const SECRET_KEY_SIZE: usize = SecretKey::SIZE;

/// Chain ends hashed in each of the leaf's first two parts: a chunk,
/// with the head.
pub(crate) const PK_PART: usize = blake3::CHUNK_LEN / OUT_LEN - 1;

const TAG_PRF: u32 = 1;
pub(crate) const TAG_CHAIN: u32 = 2;
const TAG_RAND: u32 = 6;
const TAG_KEYGEN: u32 = 7;
/// What a tweak's last word holds above its tag: "XMS".
pub(crate) const MARKER: u32 = 0x584D_5300;

// ---------------------------------------------------------------------------
// Tweakable hash
// ---------------------------------------------------------------------------

/// The key of a use: the eight words the hash starts from.
pub(crate) fn tweak(pub_seed: &PubSeed, tag: u32, index: u64, extra: u32) -> [u32; 8] {
    let seed: [u32; 4] = blake3::words(pub_seed);
    [seed[0], seed[1], seed[2], seed[3], index as u32, (index >> 32) as u32, extra, MARKER | tag]
}

/// The tweakable hash: Blake3's keyed hash of `msg` under the tweak.
/// Every use hashes a chunk at most.
pub(crate) fn th(pub_seed: &PubSeed, tag: u32, index: u64, extra: u32, msg: &[u8]) -> Digest {
    debug_assert!(msg.len() <= blake3::CHUNK_LEN);
    blake3::keyed_hash_words(&tweak(pub_seed, tag, index, extra), msg)
}

// ---------------------------------------------------------------------------
// WOTS+
// ---------------------------------------------------------------------------

/// The secret start of chain `chain` of the WOTS key pair at `leaf`.
fn wots_sk(pub_seed: &PubSeed, sk_seed: &Digest, leaf: u64, chain: usize) -> Digest {
    th(pub_seed, TAG_PRF, leaf, chain as u32, sk_seed)
}

/// `steps` chain steps from `x`, the first of them step `start`.
pub(crate) fn chain(pub_seed: &PubSeed, leaf: u64, chain: usize, x: &Digest, start: usize, steps: usize) -> Digest {
    debug_assert!(start + steps < W);
    let mut x = *x;
    for step in start..start + steps {
        x = th(pub_seed, TAG_CHAIN, leaf, (chain as u32) | ((step as u32) << 16), &x);
    }
    x
}

/// What the message digest and the leaf's hashes begin with: the public
/// seed, the leaf's index, the tree's height and which hash of the use
/// it is. Two field elements, to a circuit.
pub(crate) fn head(pub_seed: &PubSeed, leaf: u64, height: u8, part: u32) -> [u8; 32] {
    let mut out = [0u8; 32];
    out[..16].copy_from_slice(pub_seed);
    out[16..24].copy_from_slice(&leaf.to_le_bytes());
    out[24..28].copy_from_slice(&(height as u32).to_le_bytes());
    out[28..].copy_from_slice(&part.to_le_bytes());
    out
}

/// The chains' ends as the WOTS public key, which is the Merkle leaf:
/// the first [`PK_PART`] ends hashed, the next as many, and those two
/// digests hashed after the ends left over; each after its head.
pub(crate) fn wots_pk_from_ends(pub_seed: &PubSeed, leaf: u64, height: u8, ends: &[Digest; CHAINS]) -> Digest {
    let part = |i: usize| {
        let head = head(pub_seed, leaf, height, i as u32);
        hash_domain(DOM_XMSS_LEAF, &[&head[..], ends[i * PK_PART..(i + 1) * PK_PART].as_flattened()].concat())
    };
    let head = head(pub_seed, leaf, height, 2);
    hash_domain(DOM_XMSS_LEAF, &[&head[..], ends[2 * PK_PART..].as_flattened(), &part(0), &part(1)].concat())
}

/// The WOTS public key at `leaf`, from the secret seed.
fn wots_leaf(pub_seed: &PubSeed, sk_seed: &Digest, leaf: u64, height: u8) -> Digest {
    let mut ends = [[0u8; OUT_LEN]; CHAINS];
    for (c, end) in ends.iter_mut().enumerate() {
        *end = chain(pub_seed, leaf, c, &wots_sk(pub_seed, sk_seed, leaf, c), 0, W - 1);
    }
    wots_pk_from_ends(pub_seed, leaf, height, &ends)
}

/// A digest's digits, two a byte and the low one first, then the
/// checksum's: the base-16 digits of the sum of `15 - digit`, lowest
/// first.
pub(crate) fn digits(d: &Digest) -> [u8; CHAINS] {
    let mut out = [0u8; CHAINS];
    for (i, byte) in d.iter().enumerate() {
        (out[2 * i], out[2 * i + 1]) = (byte & 15, byte >> 4);
    }
    let csum: u32 = out[..MSG_CHAINS].iter().map(|x| (W - 1) as u32 - *x as u32).sum();
    for i in 0..CSUM_CHAINS {
        out[MSG_CHAINS + i] = ((csum >> (LOG_W * i)) & (W as u32 - 1)) as u8;
    }
    out
}

/// The digest that is signed: of the head, the randomizer and the
/// message. A message of 32 bytes, as a transaction's is, makes it two
/// blocks; a long one is hashed by itself first.
pub(crate) fn message_digest(pub_seed: &PubSeed, leaf: u64, height: u8, randomizer: &Digest, msg: &[u8]) -> Digest {
    let short = msg.len() <= blake3::CHUNK_LEN - 2 * OUT_LEN;
    let inner = if short { [0; OUT_LEN] } else { hash_domain(DOM_XMSS_MSG, msg) };
    let (head, msg) = (head(pub_seed, leaf, height, !short as u32), if short { msg } else { &inner[..] });
    hash_domain(DOM_XMSS_MSG, &[&head[..], randomizer, msg].concat())
}

// ---------------------------------------------------------------------------
// The Merkle tree
// ---------------------------------------------------------------------------

/// A node of the tree, from its two children.
pub(crate) fn tree_node(left: &Digest, right: &Digest) -> Digest {
    hash_domain(DOM_XMSS_TREE, &[&left[..], right].concat())
}

// ---------------------------------------------------------------------------
// Keys and signatures
// ---------------------------------------------------------------------------

/// A public key: the tree's root, the public seed and the tree's height.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct PublicKey {
    pub root: Digest,
    pub pub_seed: PubSeed,
    pub height: u8,
}

/// A signature: the leaf used, the randomizer of the message's digest,
/// a value of each chain, and the leaf's path to the root (as long as
/// the tree is high).
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Signature {
    pub index: u64,
    pub randomizer: Digest,
    pub wots: [Digest; CHAINS],
    pub auth_path: Vec<Digest>,
}

#[derive(Clone)]
pub struct SecretKey {
    height: u8,
    sk_seed: Digest,
    pub_seed: PubSeed,
    next_index: u64,
    /// The whole tree, the root at 1 and node `i`'s children at `2i` and
    /// `2i + 1`: signing does not make the leaves again.
    tree: Vec<Digest>,
}

impl PublicKey {
    pub const SIZE: usize = OUT_LEN + PUB_SEED_LEN + 1;

    pub fn to_bytes(&self) -> [u8; Self::SIZE] {
        let mut out = [0u8; Self::SIZE];
        out[..OUT_LEN].copy_from_slice(&self.root);
        out[OUT_LEN..Self::SIZE - 1].copy_from_slice(&self.pub_seed);
        out[Self::SIZE - 1] = self.height;
        out
    }

    /// A key of the bytes: its height must be 1 to [`MAX_HEIGHT`].
    pub fn from_bytes(bytes: &[u8]) -> Result<PublicKey, Error> {
        Self::decode(bytes).ok_or(Error::Malformed("public key"))
    }

    fn decode(bytes: &[u8]) -> Option<PublicKey> {
        let height = *bytes.last()?;
        if bytes.len() != Self::SIZE || height == 0 || height as usize > MAX_HEIGHT {
            return None;
        }
        Some(PublicKey {
            root: bytes[..OUT_LEN].try_into().unwrap(),
            pub_seed: bytes[OUT_LEN..Self::SIZE - 1].try_into().unwrap(),
            height,
        })
    }

    pub fn height(&self) -> usize {
        self.height as usize
    }

    /// Whether `sig` is this key's signature of `msg`: not for a
    /// signature of another height, a leaf the tree has not, or anything
    /// that does not hash to the root.
    pub fn verify(&self, msg: &[u8], sig: &Signature) -> bool {
        let h = self.height();
        if h == 0 || h > MAX_HEIGHT || sig.auth_path.len() != h || sig.index >= 1 << h {
            return false;
        }
        let d = digits(&message_digest(&self.pub_seed, sig.index, self.height, &sig.randomizer, msg));
        let mut ends = [[0u8; OUT_LEN]; CHAINS];
        for (c, end) in ends.iter_mut().enumerate() {
            let done = d[c] as usize;
            *end = chain(&self.pub_seed, sig.index, c, &sig.wots[c], done, W - 1 - done);
        }
        let mut node = wots_pk_from_ends(&self.pub_seed, sig.index, self.height, &ends);
        let mut index = sig.index;
        for sibling in &sig.auth_path {
            node = if index & 1 == 0 { tree_node(&node, sibling) } else { tree_node(sibling, &node) };
            index >>= 1;
        }
        node == self.root
    }
}

impl Signature {
    /// Bytes of a signature of a tree of `height`.
    pub const fn size(height: usize) -> usize {
        8 + (1 + CHAINS + height) * OUT_LEN
    }

    /// Bytes of the tallest signature: room for any.
    pub const MAX_SIZE: usize = Self::size(MAX_HEIGHT);

    /// The height of the tree it is of.
    pub fn height(&self) -> usize {
        self.auth_path.len()
    }

    /// Writes the signature to `out`, which must be [`Signature::size`]
    /// of its height long.
    pub fn write_bytes(&self, out: &mut [u8]) {
        assert_eq!(out.len(), Self::size(self.height()), "buffer is not the signature's size");
        out[..8].copy_from_slice(&self.index.to_le_bytes());
        let digests = std::iter::once(&self.randomizer).chain(&self.wots).chain(&self.auth_path);
        for (to, d) in out[8..].chunks_exact_mut(OUT_LEN).zip(digests) {
            to.copy_from_slice(d);
        }
    }

    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = vec![0u8; Self::size(self.height())];
        self.write_bytes(&mut out);
        out
    }

    /// A signature of a tree of `height`, which the signer's key says.
    pub fn from_bytes(bytes: &[u8], height: usize) -> Result<Signature, Error> {
        Self::decode(bytes, height).ok_or(Error::Malformed("signature"))
    }

    fn decode(bytes: &[u8], height: usize) -> Option<Signature> {
        if height == 0 || height > MAX_HEIGHT || bytes.len() != Self::size(height) {
            return None;
        }
        // (A leaf the tree has.)
        let index = Some(u64::from_le_bytes(bytes[..8].try_into().unwrap())).filter(|i| *i >> height == 0)?;
        let mut digests = bytes[8..].chunks_exact(OUT_LEN).map(|d| -> Digest { d.try_into().unwrap() });
        let randomizer = digests.next()?;
        let mut wots = [[0u8; OUT_LEN]; CHAINS];
        for (w, d) in wots.iter_mut().zip(&mut digests) {
            *w = d;
        }
        Some(Signature { index, randomizer, wots, auth_path: digests.collect() })
    }
}

impl SecretKey {
    /// Bytes of a stored key: the seeds, the next leaf and the height.
    /// The tree is made again when it is read.
    pub const SIZE: usize = OUT_LEN + PUB_SEED_LEN + 8 + 1;

    /// A payment key pair ([`PLAIN_HEIGHT`]) from `seed`, which must be
    /// uniformly random.
    pub fn generate(seed: &[u8; SEED_SIZE]) -> SecretKey {
        Self::generate_with_height(seed, PLAIN_HEIGHT)
    }

    /// A key pair of a tree of `height`, 1 to [`MAX_HEIGHT`], from
    /// `seed`. It makes the whole tree: the work grows as `2^height`.
    pub fn generate_with_height(seed: &[u8; SEED_SIZE], height: usize) -> SecretKey {
        assert!((1..=MAX_HEIGHT).contains(&height), "a tree's height is 1 to {MAX_HEIGHT}");
        let zero = [0u8; PUB_SEED_LEN];
        let sk_seed = th(&zero, TAG_KEYGEN, 0, 0, seed);
        let pub_seed = th(&zero, TAG_KEYGEN, 1, 0, seed)[..PUB_SEED_LEN].try_into().unwrap();
        Self::from_parts(height as u8, sk_seed, pub_seed, 0)
    }

    fn from_parts(height: u8, sk_seed: Digest, pub_seed: PubSeed, next_index: u64) -> SecretKey {
        let h = height as usize;
        let n = 1usize << h;
        let mut tree = vec![[0u8; OUT_LEN]; 2 * n];
        // The leaves, in place: at least 2^6 to a thread.
        crate::parallel::par_fill_min(&mut tree[n..], 1 << 6, |i| wots_leaf(&pub_seed, &sk_seed, i as u64, height));
        for pos in (1..n).rev() {
            tree[pos] = tree_node(&tree[2 * pos], &tree[2 * pos + 1]);
        }
        SecretKey { height, sk_seed, pub_seed, next_index, tree }
    }

    pub fn public_key(&self) -> PublicKey {
        PublicKey { root: self.tree[1], pub_seed: self.pub_seed, height: self.height }
    }

    pub fn height(&self) -> usize {
        self.height as usize
    }

    /// Signatures a key pair can make in all.
    pub fn leaves(&self) -> u64 {
        1 << self.height
    }

    /// The leaf the next signature will use.
    pub fn next_index(&self) -> u64 {
        self.next_index
    }

    /// Moves to leaf `index`, skipping those before it: for a key whose
    /// count of leaves used is kept elsewhere. Never move back.
    pub fn set_next_index(&mut self, index: u64) {
        assert!(index <= self.leaves(), "a leaf the tree has not");
        self.next_index = index;
    }

    /// Signatures left.
    pub fn remaining(&self) -> u64 {
        self.leaves() - self.next_index
    }

    /// Signs `msg` with the next unused leaf, and moves past it.
    pub fn sign(&mut self, msg: &[u8]) -> Result<Signature, Error> {
        if self.next_index >= self.leaves() {
            return Err(Error::KeyExhausted);
        }
        let index = self.next_index;
        self.next_index += 1;
        let randomizer = th(&self.pub_seed, TAG_RAND, index, 0, &self.sk_seed);
        let d = digits(&message_digest(&self.pub_seed, index, self.height, &randomizer, msg));
        let mut wots = [[0u8; OUT_LEN]; CHAINS];
        for (c, out) in wots.iter_mut().enumerate() {
            let sk = wots_sk(&self.pub_seed, &self.sk_seed, index, c);
            *out = chain(&self.pub_seed, index, c, &sk, 0, d[c] as usize);
        }
        let mut auth_path = Vec::with_capacity(self.height());
        let mut pos = (1usize << self.height()) + index as usize;
        for _ in 0..self.height() {
            auth_path.push(self.tree[pos ^ 1]);
            pos >>= 1;
        }
        Ok(Signature { index, randomizer, wots, auth_path })
    }

    /// The seeds and the next leaf. Store this after every signature: an
    /// older copy restored signs with leaves already used, and the key
    /// is then no key.
    pub fn to_bytes(&self) -> [u8; Self::SIZE] {
        let mut out = [0u8; Self::SIZE];
        out[..OUT_LEN].copy_from_slice(&self.sk_seed);
        out[OUT_LEN..OUT_LEN + PUB_SEED_LEN].copy_from_slice(&self.pub_seed);
        out[OUT_LEN + PUB_SEED_LEN..Self::SIZE - 1].copy_from_slice(&self.next_index.to_le_bytes());
        out[Self::SIZE - 1] = self.height;
        out
    }

    /// The key [`SecretKey::to_bytes`] stored, its tree made again.
    pub fn from_bytes(bytes: &[u8]) -> Result<SecretKey, Error> {
        Self::decode(bytes).ok_or(Error::Malformed("secret key"))
    }

    fn decode(bytes: &[u8]) -> Option<SecretKey> {
        if bytes.len() != Self::SIZE {
            return None;
        }
        let sk_seed = bytes[..OUT_LEN].try_into().unwrap();
        let pub_seed = bytes[OUT_LEN..OUT_LEN + PUB_SEED_LEN].try_into().unwrap();
        let next_index = u64::from_le_bytes(bytes[OUT_LEN + PUB_SEED_LEN..Self::SIZE - 1].try_into().unwrap());
        let height = bytes[Self::SIZE - 1];
        if height == 0 || height as usize > MAX_HEIGHT || next_index > 1 << height {
            return None;
        }
        Some(Self::from_parts(height, sk_seed, pub_seed, next_index))
    }
}

impl std::fmt::Debug for SecretKey {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("SecretKey")
            .field("height", &self.height)
            .field("next_index", &self.next_index)
            .field("public_key", &self.public_key())
            .finish_non_exhaustive()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn key(seed: u8, height: usize) -> SecretKey {
        SecretKey::generate_with_height(&[seed; SEED_SIZE], height)
    }

    #[test]
    fn a_tweak_is_no_domain_s_key_and_a_use_s_own() {
        let seed = [0u8; PUB_SEED_LEN];
        // The marker: a hash domain's key ends in a zero word.
        assert_ne!(tweak(&seed, TAG_PRF, 0, 0)[7], crate::hash::domain_key(TAG_PRF)[7]);
        let all = [
            tweak(&seed, TAG_CHAIN, 0, 0),
            tweak(&seed, TAG_CHAIN, 1, 0),
            tweak(&seed, TAG_CHAIN, 0, 1),
            tweak(&seed, TAG_CHAIN, 0, 1 << 16),
            tweak(&seed, TAG_PRF, 0, 0),
            tweak(&[1; PUB_SEED_LEN], TAG_CHAIN, 0, 0),
            tweak(&seed, TAG_RAND, 4 << 32, 0),
        ];
        for (i, a) in all.iter().enumerate() {
            assert!(all[i + 1..].iter().all(|b| a != b));
        }
        // And the hash is Blake3's keyed hash under the tweak's bytes.
        let key = blake3::bytes(&tweak(&[7; PUB_SEED_LEN], TAG_CHAIN, 9, 3));
        assert_eq!(th(&[7; PUB_SEED_LEN], TAG_CHAIN, 9, 3, b"abc"), blake3::keyed_hash(&key, b"abc"));
    }

    #[test]
    fn digits_are_nibbles_and_a_checksum() {
        let mut d = [0u8; OUT_LEN];
        d[0] = 0xA5;
        let digits = digits(&d);
        assert_eq!((digits[0], digits[1], digits[2]), (5, 10, 0));
        // 62 zeros, a five and a ten: 64 * 15 - 15.
        let csum = MAX_CSUM as u32 - 15;
        assert_eq!(digits[MSG_CHAINS..], [(csum & 15) as u8, (csum >> 4 & 15) as u8, (csum >> 8) as u8]);
        // A digit raised anywhere lowers the checksum: none can be
        // raised without another lowered.
        assert_eq!(super::digits(&[0xFF; OUT_LEN])[MSG_CHAINS..], [0, 0, 0]);
    }

    #[test]
    fn signatures_verify() {
        for height in [1, 2, PLAIN_HEIGHT, 6] {
            let mut sk = key(height as u8, height);
            let pk = sk.public_key();
            assert_eq!((pk.height(), sk.remaining()), (height, 1 << height));
            for i in 0..sk.leaves() {
                let msg = [i as u8; 32];
                let sig = sk.sign(&msg).unwrap();
                assert_eq!((sig.index, sig.height()), (i, height));
                assert!(pk.verify(&msg, &sig));
                assert!(!pk.verify(&[i as u8 + 1; 32], &sig));
            }
            assert_eq!(sk.sign(b"one more"), Err(Error::KeyExhausted));
        }
    }

    #[test]
    fn messages_of_any_length_are_signed() {
        let mut sk = key(9, 3);
        let pk = sk.public_key();
        for len in [0, 1, 31, 33, 960, 961, 5000] {
            let msg: Vec<u8> = (0..len).map(|i| i as u8).collect();
            let sig = sk.sign(&msg).unwrap();
            assert!(pk.verify(&msg, &sig), "{len} bytes");
            if len > 0 {
                assert!(!pk.verify(&msg[1..], &sig), "{len} bytes");
            }
        }
    }

    #[test]
    fn anything_changed_does_not_verify() {
        let mut sk = key(3, PLAIN_HEIGHT);
        let pk = sk.public_key();
        sk.set_next_index(5);
        let msg = [7u8; 32];
        let sig = sk.sign(&msg).unwrap();
        assert!(pk.verify(&msg, &sig));
        let changed = |change: &dyn Fn(&mut Signature)| {
            let mut s = sig.clone();
            change(&mut s);
            pk.verify(&msg, &s)
        };
        assert!(!changed(&|s| s.index ^= 1));
        assert!(!changed(&|s| s.index += 16));
        assert!(!changed(&|s| s.randomizer[0] ^= 1));
        for c in [0, 31, 32, 63, 64, 66] {
            assert!(!changed(&|s| s.wots[c][5] ^= 1), "chain {c}");
        }
        for level in 0..PLAIN_HEIGHT {
            assert!(!changed(&|s| s.auth_path[level][0] ^= 1), "level {level}");
        }
        assert!(!changed(&|s| _ = s.auth_path.pop()));
        assert!(!changed(&|s| s.auth_path.push([0; OUT_LEN])));
        // Another key's signature, and this one under another key.
        let mut other = key(4, PLAIN_HEIGHT);
        other.set_next_index(5);
        assert!(!pk.verify(&msg, &other.sign(&msg).unwrap()));
        assert!(!other.public_key().verify(&msg, &sig));
        for field in 0..3 {
            let mut k = pk;
            match field {
                0 => k.root[0] ^= 1,
                1 => k.pub_seed[0] ^= 1,
                _ => k.height += 1,
            }
            assert!(!k.verify(&msg, &sig));
        }
        // A chain value moved along its chain is a signature of a larger
        // digit: the checksum's chains then do not reach their ends.
        let d = digits(&message_digest(&pk.pub_seed, sig.index, pk.height, &sig.randomizer, &msg));
        let c = (0..MSG_CHAINS).find(|c| d[*c] < 15).unwrap();
        assert!(!changed(&|s| s.wots[c] = chain(&pk.pub_seed, s.index, c, &s.wots[c], d[c] as usize, 1)));
    }

    #[test]
    fn keys_and_signatures_are_stored_and_read() {
        let mut sk = key(5, 3);
        let pk = sk.public_key();
        assert_eq!(PublicKey::from_bytes(&pk.to_bytes()), Ok(pk));
        assert_eq!((PublicKey::SIZE, Signature::size(PLAIN_HEIGHT)), (49, 2312));
        let sig = sk.sign(b"first").unwrap();
        let bytes = sig.to_bytes();
        assert_eq!(bytes.len(), Signature::size(3));
        assert_eq!(Signature::from_bytes(&bytes, 3), Ok(sig));
        assert!(Signature::from_bytes(&bytes, 4).is_err());
        assert!(Signature::from_bytes(&bytes[1..], 3).is_err());
        // A stored key goes on from the leaf it was at.
        let mut again = SecretKey::from_bytes(&sk.to_bytes()).unwrap();
        assert_eq!((again.next_index(), again.public_key()), (1, pk));
        assert_eq!(again.sign(b"second"), sk.sign(b"second"));
        // Not a key: another length, no height, a leaf past the tree.
        let stored = sk.to_bytes();
        assert!(SecretKey::from_bytes(&stored[1..]).is_err());
        for (at, value) in [(SecretKey::SIZE - 1, 0), (SecretKey::SIZE - 1, 21), (OUT_LEN + PUB_SEED_LEN, 9)] {
            let mut bad = stored;
            bad[at] = value;
            assert!(SecretKey::from_bytes(&bad).is_err());
        }
        let mut bad = pk.to_bytes();
        bad[PublicKey::SIZE - 1] = 0;
        assert!(PublicKey::from_bytes(&bad).is_err());
    }

    #[test]
    fn half_a_tree_is_not_a_key() {
        // The tree's nodes are not tweaked with their place, so the root
        // of a tree's left half is the root a key of one less height
        // would have over the same leaves. The leaf's hash has the
        // height in it: no signature verifies under that root.
        let mut sk = key(6, 3);
        let pk = sk.public_key();
        let half = PublicKey { root: sk.tree[2], pub_seed: pk.pub_seed, height: 2 };
        let msg = [1u8; 32];
        let mut sig = sk.sign(&msg).unwrap();
        assert!(pk.verify(&msg, &sig));
        sig.auth_path.pop();
        assert!(!half.verify(&msg, &sig));
        // And a node is not a leaf, nor the other way: their domains.
        assert_ne!(tree_node(&[1; 32], &[2; 32]), hash_domain(DOM_XMSS_LEAF, &[[1u8; 32], [2; 32]].concat()));
    }

    #[test]
    fn a_key_is_its_seed_s() {
        let (a, b) = (key(1, 2), key(1, 2));
        assert_eq!(a.public_key(), b.public_key());
        assert_ne!(a.public_key(), key(2, 2).public_key());
        // The same seed at another height is another key, root and all.
        assert_ne!(a.public_key().root, key(1, 3).public_key().root);
    }

    /// A key whose every leaf has signed is stored and read as that:
    /// it signs nothing more. And what is printed of a key, for whoever
    /// looks into what went wrong, says nothing of its secret.
    #[test]
    fn a_key_used_up_stays_used_up_and_a_key_printed_keeps_its_secret() {
        let mut sk = key(7, 2);
        for i in 0..sk.leaves() {
            sk.sign(&[i as u8; 32]).unwrap();
        }
        assert_eq!(sk.remaining(), 0);
        let mut again = SecretKey::from_bytes(&sk.to_bytes()).unwrap();
        assert_eq!((again.remaining(), again.next_index()), (0, 4));
        assert_eq!(again.sign(b"one more"), Err(Error::KeyExhausted));
        // (A leaf past the tree's last, by one or by many, is no key's.)
        for next in [5u64, u64::MAX] {
            let mut bad = sk.to_bytes();
            bad[OUT_LEN + PUB_SEED_LEN..SecretKey::SIZE - 1].copy_from_slice(&next.to_le_bytes());
            assert!(SecretKey::from_bytes(&bad).is_err(), "next leaf {next}");
        }
        let fresh = key(7, 2);
        let text = format!("{fresh:?}");
        assert!(text.contains("height: 2") && text.contains("next_index: 0") && text.contains("public_key"), "{text}");
        assert!(!text.contains("sk_seed"), "{text}");
        // (Nor its bytes, however they would be written.)
        let secret = fresh.to_bytes()[..OUT_LEN].to_vec();
        let listed = format!("{secret:?}");
        let hex: String = secret.iter().map(|b| format!("{b:02x}")).collect();
        assert!(!text.contains(&listed[1..listed.len() - 1]) && !text.contains(&hex), "{text}");
    }
}
