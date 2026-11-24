//! Proofs that a payment was made, or coins burned: for whoever has
//! the chain's headers, and nothing else of it.
//!
//! Every output is a leaf of the state's tree, and every header says
//! the tree's root after its block. So an output with its path to the
//! root of the block that made it shows that the block made it: an
//! output of that key and amount, at that height. It does not show
//! whose the key is. An output's key is one its owner's wallet made
//! for it alone, tied on the chain to nothing; whoever saw the slate
//! knows the key and the amount, and could say it paid any address.
//! The wallet that is paid has to say so.
//!
//! It says so in a receipt ([`Receipt`]): its signature, by the key
//! its address is the hash of, over the output, the slate, what the
//! slate said (its note), and a tag of whoever pays. The tag is the
//! hash of the paying wallet's address with a secret it keeps
//! ([`sender_tag`]): the wallet that is paid cannot tell whose it is,
//! and it is fixed from then on. A proof of payment ([`Proof`]) is the
//! output, its path, the receipt, the secret, and the paying wallet's
//! own signature over the same, by the key its address is the hash
//! of: that address paid that one, so much, for what the note says,
//! in that block. The note is whatever the wallet that is paid asked
//! to be paid by: the number of an invoice, or a challenge of its.
//!
//! A burn is the payment that nobody is paid: an output to the key
//! hash that no key hashes to, so that nobody ever spends it, with a
//! memo that is the hash of what it is for ([`Burn`]): whom it is to
//! the credit of, an address or a name as it is written, what for, and
//! a number that makes it this burn and no other. The memo is in the
//! leaf, so a burn is to the credit of whom it says and nobody else's
//! to show as theirs. Its proof is the output, its path, and what the
//! memo is the hash of.
//!
//! A proof is against the header of the block that made the output and
//! no later one: it then says nothing of what became of the output,
//! which is no business of it. It is text to keep in a file or to
//! copy, as a slate is ([`Proof::to_text`]).

use crate::address::id_of;
use crate::hash::{Digest, digest_from_bytes, digest_to_bytes, hash_domain};
use crate::keccak::Sponge;
use crate::mldsa::{self, PK_LEN, SIG_LEN};
use crate::output::{
    EMPTY_MEMO, MEMO_BYTES, MEMO_LEN, Memo, Output, key_commitment, memo_from_bytes, memo_to_bytes, output_leaf,
};
use crate::store::sparse::{STATE_HEIGHT, root_of_state_path as root_of_path};

/// Domain tag of the tag of whoever pays: the hash of its secret.
pub const DOM_SENDER: u32 = 63;
/// Domain tag of a burn's memo.
pub const DOM_BURN: u32 = 64;
/// The key hash no key hashes to: what is paid to it is nobody's.
pub const BURN_KEY_HASH: Digest = [0; 32];
/// The longest a slate's note, and what a burn is for, may be.
pub const MAX_NOTE: usize = 255;
const CTX_RECEIPT: &[u8] = b"tab receipt";
const CTX_PAYER: &[u8] = b"tab payer";
const PAYMENT_MARKER: &str = "TAB PAYMENT PROOF";
const BURN_MARKER: &str = "TAB BURN PROOF";
const FORMAT_PAYMENT: u8 = 1;
const FORMAT_BURN: u8 = 2;
/// A payment made to a name: with the name, and what shows whose a
/// name under a name is.
const FORMAT_NAMED: u8 = 3;
/// What marks, in what a receipt signs, that a name follows.
const NAMED: &[u8] = b"paid as";
/// The longest a name a payment is made to is, as it is written
/// (`@name`, or `label@name`).
pub const MAX_PAID_AS: usize = 2 * crate::name::NAME_MAX + 1;

/// What a paying wallet is known by in a slate and a receipt: the hash
/// of its address and of a secret it keeps. Nobody has the address
/// from it; shown with the secret, to whomever the payment is proven
/// to, it is that address and no other.
pub fn sender_tag(address: &Digest, secret: &[u8; 32]) -> Digest {
    let both = [&digest_to_bytes(address)[..], &secret[..]].concat();
    hash_domain(DOM_SENDER, &both)
}

/// The wallet that is paid says it is: its Dilithium key, and its
/// signature over the payment.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Receipt {
    pub key: Vec<u8>,
    pub signature: Vec<u8>,
}

impl Receipt {
    pub const SIZE: usize = PK_LEN + SIG_LEN;

    /// What is signed: the output (its commitment, which is of its key
    /// and amount; the amount; its memo), the slate, the tag of whoever
    /// pays, and the slate's note; and, of a payment made to a name
    /// that the paid wallet says is its own, that name (`@name`, or
    /// `label@name`: nothing, for a payment to an address, which is
    /// then signed as it always was).
    fn message(output: &Output, slate: &[u8; 32], sender: &Digest, note: &[u8], name: &[u8]) -> [u8; 64] {
        let mut h = Sponge::shake256();
        h.absorb(&digest_to_bytes(&output.commitment)).absorb(&output.amount.to_le_bytes());
        h.absorb(&memo_to_bytes(&output.memo)).absorb(slate).absorb(&digest_to_bytes(sender));
        h.absorb(&(note.len() as u32).to_le_bytes()).absorb(note);
        if !name.is_empty() {
            h.absorb(NAMED).absorb(&(name.len() as u32).to_le_bytes()).absorb(name);
        }
        h.squeezed()
    }

    /// [`Receipt::sign`], of a payment made to `name`, which the wallet
    /// that signs says is its own.
    pub fn sign_as(
        key: &mldsa::SecretKey,
        output: &Output,
        slate: &[u8; 32],
        sender: &Digest,
        note: &[u8],
        name: &[u8],
    ) -> Receipt {
        let signature = key.sign(&Self::message(output, slate, sender, note, name), CTX_RECEIPT).to_vec();
        Receipt { key: key.public_key().to_vec(), signature }
    }

    /// [`Receipt::verify`], of a payment made to `name`.
    pub fn verify_as(&self, output: &Output, slate: &[u8; 32], sender: &Digest, note: &[u8], name: &[u8]) -> bool {
        mldsa::verify(&self.key, &Self::message(output, slate, sender, note, name), CTX_RECEIPT, &self.signature)
    }

    /// [`Receipt::sign_as_payer`], of a payment made to `name`.
    pub fn sign_as_payer_to(
        key: &mldsa::SecretKey,
        output: &Output,
        slate: &[u8; 32],
        sender: &Digest,
        note: &[u8],
        name: &[u8],
    ) -> Receipt {
        let signature = key.sign(&Self::message(output, slate, sender, note, name), CTX_PAYER).to_vec();
        Receipt { key: key.public_key().to_vec(), signature }
    }

    /// [`Receipt::verify_as_payer`], of a payment made to `name`.
    pub fn verify_as_payer_to(
        &self,
        output: &Output,
        slate: &[u8; 32],
        sender: &Digest,
        note: &[u8],
        name: &[u8],
    ) -> bool {
        mldsa::verify(&self.key, &Self::message(output, slate, sender, note, name), CTX_PAYER, &self.signature)
    }

    /// The receipt of the wallet whose key is `key`, for `output` of
    /// the slate of id `slate`.
    pub fn sign(key: &mldsa::SecretKey, output: &Output, slate: &[u8; 32], sender: &Digest, note: &[u8]) -> Receipt {
        Self::sign_as(key, output, slate, sender, note, &[])
    }

    /// Whether it is a receipt for that output of that slate, to
    /// whoever has that tag, with that note.
    pub fn verify(&self, output: &Output, slate: &[u8; 32], sender: &Digest, note: &[u8]) -> bool {
        self.verify_as(output, slate, sender, note, &[])
    }

    /// The address of the wallet that signed it.
    pub fn recipient(&self) -> Digest {
        id_of(&self.key)
    }

    /// The word of the wallet that pays, over the same: that the
    /// payment is its own. Its key and its signature, as a receipt is
    /// the paid wallet's.
    pub fn sign_as_payer(
        key: &mldsa::SecretKey,
        output: &Output,
        slate: &[u8; 32],
        sender: &Digest,
        note: &[u8],
    ) -> Receipt {
        Self::sign_as_payer_to(key, output, slate, sender, note, &[])
    }

    /// Whether it is the paying wallet's word for that payment.
    pub fn verify_as_payer(&self, output: &Output, slate: &[u8; 32], sender: &Digest, note: &[u8]) -> bool {
        self.verify_as_payer_to(output, slate, sender, note, &[])
    }

    pub fn to_bytes(&self) -> Vec<u8> {
        [&self.key[..], &self.signature[..]].concat()
    }

    pub fn from_bytes(bytes: &[u8]) -> Option<Receipt> {
        let (key, signature) = bytes.split_at_checked(PK_LEN).filter(|_| bytes.len() == Self::SIZE)?;
        Some(Receipt { key: key.to_vec(), signature: signature.to_vec() })
    }
}

/// To whose credit a burn is: a wallet, by its address; or a name, as
/// it is written (`name`, or `label@name`), whoever holds it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Beneficiary {
    Address(Digest),
    Name(String),
}

impl Beneficiary {
    /// Read as it is written: an address (`tab1…`), a name (`@name`)
    /// or a name under a name (`label@name`).
    pub fn read(text: &str) -> Option<Beneficiary> {
        if let Some(id) = crate::address::decode(text) {
            return Some(Beneficiary::Address(id));
        }
        match text.strip_prefix('@') {
            Some(name) => crate::name::valid_name(name.as_bytes()).then(|| Beneficiary::Name(name.to_string())),
            None => crate::subnames::split(text).map(|_| Beneficiary::Name(text.to_string())),
        }
    }

    /// As it is written.
    pub fn said(&self) -> String {
        match self {
            Beneficiary::Address(id) => crate::address::encode(id),
            Beneficiary::Name(name) if name.contains('@') => name.clone(),
            Beneficiary::Name(name) => format!("@{name}"),
        }
    }

    fn to_bytes(&self) -> Vec<u8> {
        match self {
            Beneficiary::Address(id) => [&[0u8][..], &digest_to_bytes(id)].concat(),
            Beneficiary::Name(name) => [&[1u8, name.len() as u8][..], name.as_bytes()].concat(),
        }
    }

    fn read_bytes(bytes: &mut &[u8]) -> Option<Beneficiary> {
        let (kind, rest) = bytes.split_first()?;
        match kind {
            0 => {
                let (id, rest) = rest.split_at_checked(32)?;
                *bytes = rest;
                Some(Beneficiary::Address(digest_from_bytes(id)?))
            }
            1 => {
                let (n, rest) = rest.split_first()?;
                let (name, rest) = rest.split_at_checked(*n as usize)?;
                *bytes = rest;
                let name = std::str::from_utf8(name).ok()?;
                let sound = crate::name::valid_name(name.as_bytes()) || crate::subnames::split(name).is_some();
                sound.then(|| Beneficiary::Name(name.to_string()))
            }
            _ => None,
        }
    }
}

/// What a burn's memo is the hash of.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Burn {
    pub beneficiary: Beneficiary,
    /// What makes it this burn: two for one beneficiary and purpose are
    /// two.
    pub nonce: [u8; 32],
    /// What it is for: up to [`MAX_NOTE`] bytes.
    pub purpose: String,
}

impl Burn {
    fn to_bytes(&self) -> Vec<u8> {
        let mut out = self.beneficiary.to_bytes();
        out.extend_from_slice(&self.nonce);
        out.push(self.purpose.len() as u8);
        out.extend_from_slice(self.purpose.as_bytes());
        out
    }

    fn read_bytes(bytes: &mut &[u8]) -> Option<Burn> {
        let beneficiary = Beneficiary::read_bytes(bytes)?;
        let (nonce, rest) = bytes.split_at_checked(32)?;
        let (n, rest) = rest.split_first()?;
        let (purpose, rest) = rest.split_at_checked(*n as usize)?;
        *bytes = rest;
        let purpose = std::str::from_utf8(purpose).ok()?.to_string();
        Some(Burn { beneficiary, nonce: nonce.try_into().ok()?, purpose })
    }

    /// The memo of the output that burns for it.
    pub fn memo(&self) -> Memo {
        let hash = hash_domain(DOM_BURN, &self.to_bytes());
        let mut memo = EMPTY_MEMO;
        memo.copy_from_slice(&hash[..MEMO_LEN]);
        memo
    }

    /// The output that burns `amount` for it: nobody's to spend.
    pub fn output(&self, amount: u64) -> Output {
        let commitment = key_commitment(&BURN_KEY_HASH, amount);
        Output { key_hash: BURN_KEY_HASH, amount, commitment, memo: self.memo() }
    }
}

/// Whose an output is, by what is shown of it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Claim {
    /// A payment: the wallet that was paid says so (`receipt`), of the
    /// slate of this id and note, to the wallet whose address with
    /// `secret` is the tag it signed; and that wallet says it is its
    /// own (`payer`, whose key its address is the hash of).
    ///
    /// `name` is the name the payment was made to, if it was made to
    /// one and the paid wallet signed that it is its own (`@name`, or
    /// `label@name`: nothing, of a payment to an address). The paid
    /// wallet's word is not the chain's: whoever reads the proof holds
    /// the name against the chain as it then is, and of a name under a
    /// name against `bundle`, its certificate, if it still holds. A
    /// name that no longer holds is no part of what the proof shows;
    /// the address is, always.
    Payment {
        secret: [u8; 32],
        slate: [u8; 32],
        note: Vec<u8>,
        name: Vec<u8>,
        bundle: Vec<u8>,
        receipt: Receipt,
        payer: Receipt,
    },
    /// A burn: what its memo is the hash of.
    Burn(Burn),
}

/// Why a proof does not hold.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ProofError {
    /// The output and its path do not lead to the root of the state
    /// after that block.
    NotInBlock,
    /// The receipt is not one for this output, slate, note and secret.
    Receipt,
    /// The output is not one nobody can spend.
    NotBurned,
    /// The output's memo is not the hash of what is said of the burn.
    Memo,
}

impl std::fmt::Display for ProofError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            ProofError::NotInBlock => "the block of that height did not make that output",
            ProofError::Receipt => "the receipt is not for that payment",
            ProofError::NotBurned => "the output is not burned: it has a key",
            ProofError::Memo => "the burn is not for what the proof says",
        })
    }
}

/// A proof that the block at `height` made an output, and whose it is.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Proof {
    /// The block that made the output.
    pub height: u32,
    /// Where the output is in the state's tree.
    pub position: u64,
    pub key_hash: Digest,
    pub amount: u64,
    pub memo: Memo,
    /// The sibling at each level from the output's leaf to the root.
    pub path: [Digest; STATE_HEIGHT],
    pub claim: Claim,
}

impl Proof {
    /// The output it is of.
    pub fn output(&self) -> Output {
        let commitment = key_commitment(&self.key_hash, self.amount);
        Output { key_hash: self.key_hash, amount: self.amount, commitment, memo: self.memo }
    }

    /// Checks it against `root`, the state root of the header at its
    /// height: that the block made the output (at that height, and no
    /// other: the leaf says when it was made), and that the output is
    /// whose the proof says.
    pub fn check(&self, root: &Digest) -> Result<(), ProofError> {
        let output = self.output();
        let leaf = output_leaf(&output.commitment, &self.memo, self.amount, self.height);
        if root_of_path(self.position, &leaf, &self.path) != *root {
            return Err(ProofError::NotInBlock);
        }
        match &self.claim {
            Claim::Payment { secret, slate, note, name, receipt, payer, .. } => {
                // (The tag the paid wallet signed is of the paying
                // wallet's address: the one whose key signs here.)
                let tag = sender_tag(&payer.recipient(), secret);
                let paid = self.key_hash != BURN_KEY_HASH && receipt.verify_as(&output, slate, &tag, note, name);
                let sound = paid && payer.verify_as_payer_to(&output, slate, &tag, note, name);
                sound.then_some(()).ok_or(ProofError::Receipt)
            }
            Claim::Burn(_) if self.key_hash != BURN_KEY_HASH => Err(ProofError::NotBurned),
            Claim::Burn(burn) => (burn.memo() == self.memo).then_some(()).ok_or(ProofError::Memo),
        }
    }

    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = vec![match &self.claim {
            Claim::Payment { name, .. } if !name.is_empty() => FORMAT_NAMED,
            Claim::Payment { .. } => FORMAT_PAYMENT,
            Claim::Burn(_) => FORMAT_BURN,
        }];
        out.extend_from_slice(&self.height.to_le_bytes());
        out.extend_from_slice(&self.position.to_le_bytes());
        out.extend_from_slice(&digest_to_bytes(&self.key_hash));
        out.extend_from_slice(&self.amount.to_le_bytes());
        out.extend_from_slice(&memo_to_bytes(&self.memo));
        self.path.iter().for_each(|sibling| out.extend_from_slice(&digest_to_bytes(sibling)));
        match &self.claim {
            Claim::Payment { secret, slate, note, name, bundle, receipt, payer } => {
                out.extend_from_slice(secret);
                out.extend_from_slice(slate);
                out.push(note.len() as u8);
                out.extend_from_slice(note);
                if !name.is_empty() {
                    out.push(name.len() as u8);
                    out.extend_from_slice(name);
                    out.extend_from_slice(&(bundle.len() as u16).to_le_bytes());
                    out.extend_from_slice(bundle);
                }
                out.extend_from_slice(&receipt.to_bytes());
                out.extend_from_slice(&payer.to_bytes());
            }
            Claim::Burn(burn) => out.extend_from_slice(&burn.to_bytes()),
        }
        out
    }

    pub fn from_bytes(bytes: &[u8]) -> Option<Proof> {
        let (format, mut r) = bytes.split_first()?;
        let mut take = |n: usize| -> Option<&[u8]> {
            let (head, rest) = r.split_at_checked(n)?;
            r = rest;
            Some(head)
        };
        let height = u32::from_le_bytes(take(4)?.try_into().ok()?);
        // (A position there is: the path reads no more of it than the
        // tree is deep, and one past that would be the same proof said
        // another way.)
        let position =
            Some(u64::from_le_bytes(take(8)?.try_into().ok()?)).filter(|p| *p < crate::output::OUTPUT_CAPACITY)?;
        let key_hash = digest_from_bytes(take(32)?)?;
        let amount = u64::from_le_bytes(take(8)?.try_into().ok()?);
        let memo = memo_from_bytes(take(MEMO_BYTES)?).ok()?;
        let mut path = [[0; 32]; STATE_HEIGHT];
        for sibling in path.iter_mut() {
            *sibling = digest_from_bytes(take(32)?)?;
        }
        let claim = match *format {
            FORMAT_PAYMENT | FORMAT_NAMED => {
                let (secret, slate) = (take(32)?.try_into().ok()?, take(32)?.try_into().ok()?);
                let n = take(1)?[0] as usize;
                let note = take(n)?.to_vec();
                let (name, bundle) = match *format {
                    FORMAT_NAMED => {
                        let n = Some(take(1)?[0] as usize).filter(|n| (1..=MAX_PAID_AS).contains(n))?;
                        let name = take(n)?.to_vec();
                        let n = u16::from_le_bytes(take(2)?.try_into().ok()?) as usize;
                        (name, take(Some(n).filter(|n| *n <= crate::subnames::MAX_BUNDLE)?)?.to_vec())
                    }
                    _ => (Vec::new(), Vec::new()),
                };
                let receipt = Receipt::from_bytes(take(Receipt::SIZE)?)?;
                let payer = Receipt::from_bytes(take(Receipt::SIZE)?)?;
                Claim::Payment { secret, slate, note, name, bundle, receipt, payer }
            }
            FORMAT_BURN => Claim::Burn(Burn::read_bytes(&mut r)?),
            _ => return None,
        };
        r.is_empty().then_some(Proof { height, position, key_hash, amount, memo, path, claim })
    }

    fn marker(&self) -> &'static str {
        match self.claim {
            Claim::Payment { .. } => PAYMENT_MARKER,
            Claim::Burn(_) => BURN_MARKER,
        }
    }

    /// The proof as text to keep in a file or to copy: base64 between
    /// markers that say what it is, 64 characters a line.
    pub fn to_text(&self) -> String {
        let b64 = crate::base64::encode(&self.to_bytes());
        let mut out = format!("-----BEGIN {}-----\n", self.marker());
        for line in b64.as_bytes().chunks(64) {
            out.push_str(core::str::from_utf8(line).expect("base64 is ASCII"));
            out.push('\n');
        }
        out.push_str(&format!("-----END {}-----\n", self.marker()));
        out
    }

    /// A proof from text holding one between its markers, whatever
    /// surrounds it.
    pub fn from_text(text: &str) -> Option<Proof> {
        [PAYMENT_MARKER, BURN_MARKER].into_iter().find_map(|marker| {
            let (begin, end) = (format!("-----BEGIN {marker}-----"), format!("-----END {marker}-----"));
            let body = &text[text.find(&begin)? + begin.len()..];
            let b64: String = body[..body.find(&end)?].chars().filter(|c| !c.is_whitespace()).collect();
            Proof::from_bytes(&crate::base64::decode(&b64)?).filter(|proof| proof.marker() == marker)
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::registry::state_root as compress;

    /// A proof of `output`, made at `height`, the only output of a
    /// state: its path is of empty subtrees, and the root what that
    /// comes to.
    fn alone(output: &Output, height: u32, position: u64, claim: Claim) -> (Proof, Digest) {
        let mut path = [[0; 32]; STATE_HEIGHT];
        for (level, sibling) in path.iter_mut().enumerate() {
            *sibling = *crate::store::sparse::empty(level);
        }
        let leaf = output_leaf(&output.commitment, &output.memo, output.amount, height);
        let root = root_of_path(position, &leaf, &path);
        let (key_hash, amount, memo) = (output.key_hash, output.amount, output.memo);
        (Proof { height, position, key_hash, amount, memo, path, claim }, root)
    }

    /// A receipt is the paid wallet's word for one payment: this
    /// output, this slate, this note, to the wallet of this tag.
    #[test]
    fn a_receipt_is_for_one_payment() {
        let (key, payer) = (mldsa::keygen(&[1; 32]), id_of(mldsa::keygen(&[2; 32]).public_key()));
        let output = Output::to_key_hash(&[9_u8; 32], 5000);
        let (secret, slate) = ([3u8; 32], [4u8; 32]);
        let tag = sender_tag(&payer, &secret);
        let receipt = Receipt::sign(&key, &output, &slate, &tag, b"invoice 4821");
        assert_eq!(receipt.recipient(), id_of(key.public_key()));
        assert!(receipt.verify(&output, &slate, &tag, b"invoice 4821"));
        assert_eq!(Receipt::from_bytes(&receipt.to_bytes()), Some(receipt.clone()));
        // Not for another output, slate, note, or paying wallet.
        assert!(!receipt.verify(&Output::to_key_hash(&[9_u8; 32], 5001), &slate, &tag, b"invoice 4821"));
        assert!(!receipt.verify(&output, &[5; 32], &tag, b"invoice 4821"));
        assert!(!receipt.verify(&output, &slate, &tag, b"invoice 4822"));
        assert!(!receipt.verify(&output, &slate, &sender_tag(&payer, &[6; 32]), b"invoice 4821"));
        assert!(!receipt.verify(&output, &slate, &sender_tag(&id_of(key.public_key()), &secret), b"invoice 4821"));
        // The tag is of the address and the secret, and says neither.
        assert_ne!(tag, payer);
        assert_ne!(tag, sender_tag(&payer, &[6; 32]));
        // The paid wallet's word is not the paying wallet's, nor that its.
        assert!(!receipt.verify_as_payer(&output, &slate, &tag, b"invoice 4821"));
        assert_eq!(Receipt::from_bytes(&receipt.to_bytes()[1..]), None);
    }

    /// A proof of payment holds against the root of the block that
    /// made the output: that address paid that one, by the word of
    /// both; and against nothing else, nor for anybody else.
    #[test]
    fn a_payment_is_proven_against_its_block() {
        let (paid_key, payer_key) = (mldsa::keygen(&[1; 32]), mldsa::keygen(&[2; 32]));
        let output = Output::to_key_hash(&[9_u8; 32], 5000);
        let (secret, slate, note) = ([3u8; 32], [4u8; 32], b"invoice 4821".to_vec());
        let tag = sender_tag(&id_of(payer_key.public_key()), &secret);
        let receipt = Receipt::sign(&paid_key, &output, &slate, &tag, &note);
        let payer = Receipt::sign_as_payer(&payer_key, &output, &slate, &tag, &note);
        let claim = Claim::Payment { secret, slate, note, name: Vec::new(), bundle: Vec::new(), receipt, payer };
        let (proof, root) = alone(&output, 77, 12_345, claim);
        assert_eq!(proof.check(&root), Ok(()));
        // As text, with whatever is around it; and as bytes.
        let text = format!("here it is:\n{}thanks", proof.to_text());
        assert!(text.contains("-----BEGIN TAB PAYMENT PROOF-----\n"));
        assert_eq!(Proof::from_text(&text), Some(proof.clone()));
        assert_eq!(Proof::from_bytes(&proof.to_bytes()), Some(proof.clone()));
        assert_eq!(Proof::from_bytes(&proof.to_bytes()[..100]), None);
        assert_eq!(Proof::from_text("no proof here"), None);
        // Another root; another height, amount, position, memo: not in
        // that block.
        assert_eq!(proof.check(&compress(&root, &root)), Err(ProofError::NotInBlock));
        for other in [
            Proof { height: 78, ..proof.clone() },
            Proof { amount: 5001, ..proof.clone() },
            Proof { position: 12_346, ..proof.clone() },
            Proof { memo: [1_u8; MEMO_LEN], ..proof.clone() },
        ] {
            assert_eq!(other.check(&root), Err(ProofError::NotInBlock));
        }
        // In the block, and not what the proof says: another secret,
        // another note, another slate.
        let Claim::Payment { secret, slate, note, receipt, payer, .. } = proof.claim.clone() else { unreachable!() };
        let with = |secret, slate, note: &[u8], payer: &Receipt| {
            let (name, bundle) = (Vec::new(), Vec::new());
            let (note, receipt, payer) = (note.to_vec(), receipt.clone(), payer.clone());
            let claim = Claim::Payment { secret, slate, note, name, bundle, receipt, payer };
            Proof { claim, ..proof.clone() }.check(&root)
        };
        assert_eq!(with(secret, slate, &note, &payer), Ok(()));
        assert_eq!(with([8; 32], slate, &note, &payer), Err(ProofError::Receipt));
        assert_eq!(with(secret, slate, b"invoice 1", &payer), Err(ProofError::Receipt));
        assert_eq!(with(secret, [8; 32], &note, &payer), Err(ProofError::Receipt));
        // Shown by another wallet as its own payment: the paid wallet's
        // receipt is not for that wallet, whatever it signs.
        let thief = mldsa::keygen(&[9; 32]);
        let stolen = Receipt::sign_as_payer(&thief, &output, &slate, &tag, &note);
        assert_eq!(with(secret, slate, &note, &stolen), Err(ProofError::Receipt));
        let own_tag = sender_tag(&id_of(thief.public_key()), &secret);
        let resigned = Receipt::sign_as_payer(&thief, &output, &slate, &own_tag, &note);
        assert_eq!(with(secret, slate, &note, &resigned), Err(ProofError::Receipt));
        // And the paying wallet's word is needed: the paid wallet's own
        // signature in its place is not it.
        assert_eq!(with(secret, slate, &note, &receipt), Err(ProofError::Receipt));
    }

    /// A burn is to the credit of whom its memo says, for what it
    /// says: an address, or a name as it is written.
    #[test]
    fn a_burn_is_for_whom_and_what_its_memo_says() {
        let id = id_of(mldsa::keygen(&[2; 32]).public_key());
        for said in [crate::address::encode(&id), "@mailhub".to_string(), "alice@mailhub".to_string()] {
            let beneficiary = Beneficiary::read(&said).unwrap();
            assert_eq!(beneficiary.said(), said);
            let burn = Burn { beneficiary, nonce: [7; 32], purpose: "a year of hosting".to_string() };
            let output = burn.output(9000);
            assert_eq!(output.key_hash, BURN_KEY_HASH);
            let (proof, root) = alone(&output, 300, 5, Claim::Burn(burn.clone()));
            assert_eq!(proof.check(&root), Ok(()));
            let text = proof.to_text();
            assert!(text.starts_with("-----BEGIN TAB BURN PROOF-----\n"));
            assert_eq!(Proof::from_text(&text), Some(proof.clone()));
            // For another purpose, another number, or another's credit.
            let others = [
                Burn { purpose: "two years".to_string(), ..burn.clone() },
                Burn { nonce: [8; 32], ..burn.clone() },
                Burn { beneficiary: Beneficiary::Name("bob@mailhub".to_string()), ..burn.clone() },
            ];
            for other in others {
                assert_ne!(other.memo(), burn.memo());
                assert_eq!(Proof { claim: Claim::Burn(other), ..proof.clone() }.check(&root), Err(ProofError::Memo));
            }
            // An output somebody can spend is no burn, whatever its memo.
            let key_hash = [3_u8; 32];
            let spendable = Output { key_hash, commitment: key_commitment(&key_hash, 9000), ..output };
            let (proof, root) = alone(&spendable, 300, 5, Claim::Burn(burn));
            assert_eq!(proof.check(&root), Err(ProofError::NotBurned));
        }
        for not in ["", "Alice@mailhub", "@", "tab1nothing", "a@b@c"] {
            assert_eq!(Beneficiary::read(not), None, "{not}");
        }
    }

    /// A payment made to a name: the paid wallet signs the name with
    /// the rest, the proof carries it, and it is as much a part of
    /// what is proven as the note. A proof of a payment to an address
    /// is, to the byte, what it was before there were names in them.
    #[test]
    fn a_payment_to_a_name_is_proven_with_the_name() {
        let (paid_key, payer_key) = (mldsa::keygen(&[1; 32]), mldsa::keygen(&[2; 32]));
        let output = Output::to_key_hash(&[9; 32], 5000);
        let (secret, slate, note) = ([3u8; 32], [4u8; 32], b"rent".to_vec());
        let tag = sender_tag(&id_of(payer_key.public_key()), &secret);
        let named = |name: &[u8], signed_as: &[u8], bundle: &[u8]| {
            let receipt = Receipt::sign_as(&paid_key, &output, &slate, &tag, &note, signed_as);
            let payer = Receipt::sign_as_payer_to(&payer_key, &output, &slate, &tag, &note, signed_as);
            let (note, name, bundle) = (note.clone(), name.to_vec(), bundle.to_vec());
            alone(&output, 77, 12_345, Claim::Payment { secret, slate, note, name, bundle, receipt, payer })
        };
        let (proof, root) = named(b"alice@hub", b"alice@hub", b"a certificate");
        assert_eq!(proof.check(&root), Ok(()));
        let again = Proof::from_text(&proof.to_text()).unwrap();
        assert_eq!((again.check(&root), &again), (Ok(()), &proof));
        // Another name than was signed for, or none: not that payment.
        assert_eq!(named(b"mallory@hub", b"alice@hub", b"").0.check(&root), Err(ProofError::Receipt));
        assert_eq!(named(b"", b"alice@hub", b"").0.check(&root), Err(ProofError::Receipt));
        assert_eq!(named(b"alice@hub", b"", b"").0.check(&root), Err(ProofError::Receipt));
        // To an address: as it always was, and a byte shorter for it.
        let (plain, root) = named(b"", b"", b"");
        assert_eq!(plain.check(&root), Ok(()));
        assert_eq!((plain.to_bytes()[0], proof.to_bytes()[0]), (FORMAT_PAYMENT, FORMAT_NAMED));
        let receipt = Receipt::sign(&paid_key, &output, &slate, &tag, &note);
        assert!(
            receipt.verify_as(&output, &slate, &tag, &note, b"")
                && !receipt.verify_as(&output, &slate, &tag, &note, b"@a")
        );
        // What is no name of a length there is, is no proof.
        let mut long = proof.to_bytes();
        let at = long.len() - 2 * Receipt::SIZE - 2 - 13 - 9 - 1;
        assert_eq!(long[at], 9);
        long[at] = 0;
        assert!(Proof::from_bytes(&long).is_none());
    }
}
