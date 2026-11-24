//! What wallets say to each other over the message layer, and how it is
//! kept from everyone between them.
//!
//! A wallet is known by its id, the hash of its Dilithium key
//! ([`crate::address`]). To be reached it says, to each node that
//! stands between it and whoever would reach it, an [`Announced`]: its
//! Dilithium key, a Kyber key made for the purpose, and its signature
//! over that key, a number that only rises, a time it holds until, and
//! a token of the node it is said to. Whoever has a wallet's id asks
//! such a node for what the wallet announced, checks the key against
//! the id and the signature against the key, and so has a key to seal
//! to that the wallet alone opens.
//!
//! What is sent is [`seal`]ed: encapsulated to that Kyber key, and
//! under the secret so agreed (ChaCha20-Poly1305) the sender's own
//! announcement, what kind of thing is said, the thing, and the
//! sender's signature over it and over whom it is to. So a node that
//! passes it on learns whom it is for and how long it is: not who sent
//! it, and nothing of what it says. The one it is for learns who sent
//! it, by a key it can check, and has a Kyber key of the sender's to
//! answer to.
//!
//! The Kyber keys are made anew often, and the old ones dropped: what
//! was sealed to one cannot be opened once it is gone, by anyone.
//!
//! This is not the form the node before this one used.

use crate::address::id_of;
use crate::chacha20poly1305 as aead;
use crate::hash::{Digest, digest_from_bytes, digest_to_bytes, hash_domain};
use crate::{mldsa, mlkem};

/// The bytes of an announcement: the Dilithium key, the Kyber key, the
/// sequence number, the expiry, the token, the signature.
pub const ANNOUNCE_LEN: usize = mldsa::PK_LEN + mlkem::EK_LEN + 24 + mldsa::SIG_LEN;
/// The most a message may say: what it carries, not what carries it.
pub const MAX_BODY: usize = 64 << 10;
/// The bytes a sealed message is longer than what it says by: one sent
/// to a wallet, which says nothing of who sends it, and its answer,
/// which is signed.
pub const OVERHEAD: usize = 1 + 32 + mlkem::CT_LEN + mlkem::EK_LEN + 1 + aead::TAG_LEN;
pub const ANSWER_OVERHEAD: usize = 1 + 32 + mlkem::CT_LEN + mldsa::PK_LEN + 1 + mldsa::SIG_LEN + aead::TAG_LEN;
/// The longest sealed message.
pub const MAX_SEALED: usize = ANSWER_OVERHEAD + MAX_BODY;
/// The first byte of a sealed message: one sent to a wallet, or the
/// answer to one.
const SENT: u8 = 0;
const ANSWER: u8 = 1;

/// What a message says: a slate, of a payment being made.
pub const KIND_SLATE: u8 = 1;
/// A certificate that the wallet it is sent to is a name under a name,
/// with what goes with it ([`crate::subnames`]).
pub const KIND_NAME: u8 = 2;

/// Domain tag of the id of a sealed message, by which it is fetched.
const DOM_SEALED: u32 = 60;
/// Domain tag of the choice of a wallet's rendezvous points.
const DOM_POINT: u32 = 61;
/// What an announcement is signed under, and a message.
const CTX_ANNOUNCE: &[u8] = b"tab announce";
const CTX_MESSAGE: &[u8] = b"tab message";

const SIGNED: std::ops::Range<usize> = mldsa::PK_LEN..mldsa::PK_LEN + mlkem::EK_LEN + 24;

/// An announcement of the wallet whose key is `identity`: that `kyber`
/// is the key to seal to it with, from now until `expires` (Unix
/// seconds), unless one of a higher `seq` is seen. `bind` is the token
/// of the node it is said to, which takes it from nobody that token
/// was not given to: so that it cannot be said again by another, from
/// elsewhere.
pub fn announce(
    identity: &mldsa::SecretKey,
    kyber: &[u8; mlkem::EK_LEN],
    seq: u64,
    expires: u64,
    bind: u64,
) -> Vec<u8> {
    let mut out = Vec::with_capacity(ANNOUNCE_LEN);
    out.extend_from_slice(identity.public_key());
    out.extend_from_slice(kyber);
    out.extend_from_slice(&seq.to_le_bytes());
    out.extend_from_slice(&expires.to_le_bytes());
    out.extend_from_slice(&bind.to_le_bytes());
    let signature = identity.sign(&out[SIGNED], CTX_ANNOUNCE);
    out.extend_from_slice(&signature);
    out
}

/// An announcement that was checked: of the right length, signed by the
/// key it carries, and not yet past its time.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Announced<'a>(&'a [u8]);

impl<'a> Announced<'a> {
    /// Reads and checks an announcement, at `now` (Unix seconds).
    pub fn read(bytes: &'a [u8], now: u64) -> Option<Announced<'a>> {
        if bytes.len() != ANNOUNCE_LEN {
            return None;
        }
        let said = Announced(bytes);
        let signature = &bytes[SIGNED.end..];
        let sound = said.expires() > now
            && mlkem::valid_public_key(said.kyber())
            && mldsa::verify(said.key(), &bytes[SIGNED], CTX_ANNOUNCE, signature);
        sound.then_some(said)
    }

    pub fn bytes(&self) -> &'a [u8] {
        self.0
    }

    /// The Dilithium key of whoever said it.
    pub fn key(&self) -> &'a [u8] {
        &self.0[..mldsa::PK_LEN]
    }

    /// Whose it is: the hash of that key.
    pub fn id(&self) -> Digest {
        id_of(self.key())
    }

    /// The Kyber key to seal to.
    pub fn kyber(&self) -> &'a [u8] {
        &self.0[mldsa::PK_LEN..mldsa::PK_LEN + mlkem::EK_LEN]
    }

    fn number(&self, at: usize) -> u64 {
        let from = mldsa::PK_LEN + mlkem::EK_LEN + 8 * at;
        u64::from_le_bytes(self.0[from..from + 8].try_into().expect("eight bytes"))
    }

    pub fn seq(&self) -> u64 {
        self.number(0)
    }

    pub fn expires(&self) -> u64 {
        self.number(1)
    }

    pub fn bind(&self) -> u64 {
        self.number(2)
    }
}

/// The id of a sealed message: what it is asked for by.
pub fn sealed_id(sealed: &[u8]) -> Digest {
    hash_domain(DOM_SEALED, sealed)
}

/// Whom a sealed message is for, if it is one sent to a wallet.
pub fn sealed_to(sealed: &[u8]) -> Option<Digest> {
    digest_from_bytes(sealed.strip_prefix(&[SENT])?.get(..32)?)
}

/// The id of the message a sealed message answers, if it is an answer.
pub fn sealed_answers(sealed: &[u8]) -> Option<Digest> {
    digest_from_bytes(sealed.strip_prefix(&[ANSWER])?.get(..32)?)
}

/// The key a message is sealed under: of the secret agreed and of whom
/// it is for.
fn key_of(secret: &[u8; mlkem::SS_LEN], to: &[u8]) -> [u8; aead::KEY_LEN] {
    let mut input = [0u8; mlkem::SS_LEN + 32];
    input[..mlkem::SS_LEN].copy_from_slice(secret);
    input[mlkem::SS_LEN..].copy_from_slice(to);
    crate::keccak::sha3_256(&input)
}

/// What whoever answers signs: the message it answers, the
/// encapsulation the answer is sealed under, its kind and what it
/// says. (So that it is this answer to that message, and no other.)
fn signed_of(answers: &[u8], ct: &[u8], kind: u8, body: &[u8]) -> [u8; 32] {
    let mut h = crate::keccak::Sponge::shake256();
    h.absorb(answers).absorb(ct).absorb(&[kind]).absorb(body);
    h.squeezed()
}

/// Seals `body`, of `kind`, to the wallet that announced `to`. Nothing
/// in it says who sends it: it carries `reply`, a Kyber key made for
/// this message alone, which its answer is sealed to; and the answer
/// comes back the way the message went, so that the wallet it is for
/// need not know where its sender is, or who. `chance` is 32 random
/// bytes. None if `body` is longer than a message may be.
pub fn seal(to: &Announced<'_>, reply: &[u8], kind: u8, body: &[u8], chance: &[u8; 32]) -> Option<Vec<u8>> {
    if body.len() > MAX_BODY || reply.len() != mlkem::EK_LEN {
        return None;
    }
    let (secret, ct) = mlkem::encapsulate_with(to.kyber(), chance)?;
    let id = digest_to_bytes(&to.id());
    let mut inner = Vec::with_capacity(mlkem::EK_LEN + 1 + body.len());
    inner.extend_from_slice(reply);
    inner.push(kind);
    inner.extend_from_slice(body);
    let mut out = Vec::with_capacity(OVERHEAD + body.len());
    out.push(SENT);
    out.extend_from_slice(&id);
    out.extend_from_slice(&ct);
    // (No nonce but nothing: the key is of this encapsulation alone.)
    let sealed = aead::seal(&key_of(&secret, &id), &[0; aead::NONCE_LEN], &out, &inner);
    out.extend_from_slice(&sealed);
    Some(out)
}

/// Seals the answer to the message of id `answers`, to the key that
/// message carried for it (`reply`), signed by `signer`, the wallet
/// the message was for: whoever sent the message knows whom it sent it
/// to, and takes the answer from that wallet alone.
pub fn seal_answer(
    signer: &mldsa::SecretKey,
    reply: &[u8],
    answers: &Digest,
    kind: u8,
    body: &[u8],
    chance: &[u8; 32],
) -> Option<Vec<u8>> {
    if body.len() > MAX_BODY {
        return None;
    }
    let (secret, ct) = mlkem::encapsulate_with(reply, chance)?;
    let id = digest_to_bytes(answers);
    let mut inner = Vec::with_capacity(mldsa::PK_LEN + 1 + body.len() + mldsa::SIG_LEN);
    inner.extend_from_slice(signer.public_key());
    inner.push(kind);
    inner.extend_from_slice(body);
    inner.extend_from_slice(&signer.sign(&signed_of(&id, &ct, kind, body), CTX_MESSAGE));
    let mut out = Vec::with_capacity(ANSWER_OVERHEAD + body.len());
    out.push(ANSWER);
    out.extend_from_slice(&id);
    out.extend_from_slice(&ct);
    let sealed = aead::seal(&key_of(&secret, &id), &[0; aead::NONCE_LEN], &out, &inner);
    out.extend_from_slice(&sealed);
    Some(out)
}

/// A message opened.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Opened {
    /// The message's own id ([`sealed_id`]): what its answer names.
    pub id: Digest,
    /// Who sent it, by a key that was checked: of an answer, the
    /// wallet that answers. Of a message sent to this wallet, nobody:
    /// it does not say.
    pub from: Option<Digest>,
    /// Of an answer: the id of the message it answers.
    pub answers: Option<Digest>,
    /// Of a message sent to this wallet: the key its answer is sealed
    /// to.
    pub reply: Vec<u8>,
    /// The node it came by, which its answer goes back by: said by
    /// whoever took it from that node.
    pub by: Option<std::net::SocketAddrV4>,
    pub kind: u8,
    pub body: Vec<u8>,
}

/// Opens a message sealed to the wallet of id `own`, with the Kyber key
/// it was sealed to. None if it is not for this wallet, was not sealed
/// to this key, or was changed on the way.
pub fn open(kyber: &mlkem::SecretKey, own: &Digest, sealed: &[u8]) -> Option<Opened> {
    if sealed.len() < OVERHEAD || sealed.len() > MAX_SEALED || sealed[0] != SENT {
        return None;
    }
    let (head, rest) = sealed.split_at(1 + 32 + mlkem::CT_LEN);
    let (to, ct) = head[1..].split_at(32);
    if to != digest_to_bytes(own) {
        return None;
    }
    let secret = kyber.decapsulate(ct)?;
    let inner = aead::open(&key_of(&secret, to), &[0; aead::NONCE_LEN], head, rest)?;
    let (reply, said) = inner.split_at_checked(mlkem::EK_LEN)?;
    let (kind, body) = said.split_first()?;
    if !mlkem::valid_public_key(reply) {
        return None;
    }
    let (id, reply, body) = (sealed_id(sealed), reply.to_vec(), body.to_vec());
    Some(Opened { id, from: None, answers: None, reply, by: None, kind: *kind, body })
}

/// Opens the answer to the message of id `answers`, with the key that
/// message carried for it. None if it is not an answer to that
/// message, was not sealed to that key, was changed on the way, or is
/// not signed by the key it carries: whose that key is, is
/// [`Opened::from`], for whoever sent the message to hold against whom
/// it sent it to.
pub fn open_answer(reply: &mlkem::SecretKey, answers: &Digest, sealed: &[u8]) -> Option<Opened> {
    if sealed.len() < ANSWER_OVERHEAD || sealed.len() > MAX_SEALED || sealed[0] != ANSWER {
        return None;
    }
    let (head, rest) = sealed.split_at(1 + 32 + mlkem::CT_LEN);
    let (of, ct) = head[1..].split_at(32);
    if of != digest_to_bytes(answers) {
        return None;
    }
    let secret = reply.decapsulate(ct)?;
    let inner = aead::open(&key_of(&secret, of), &[0; aead::NONCE_LEN], head, rest)?;
    let (key, said) = inner.split_at_checked(mldsa::PK_LEN)?;
    let (said, signature) = said.split_at_checked(said.len().checked_sub(mldsa::SIG_LEN)?)?;
    let (kind, body) = said.split_first()?;
    if !mldsa::verify(key, &signed_of(of, ct, *kind, body), CTX_MESSAGE, signature) {
        return None;
    }
    let from = Some(crate::address::id_of(key));
    let (id, answers, body) = (sealed_id(sealed), Some(*answers), body.to_vec());
    Some(Opened { id, from, answers, reply: Vec::new(), by: None, kind: *kind, body })
}

/// Which of `nodes` nodes a wallet of id `id` is to be reached at in
/// the epoch `epoch` (the chain's height over the length of a window):
/// up to three of them, each chosen by a hash of the id, the epoch and
/// a count, none twice. Whoever has the id and the nodes finds the
/// same, and at every epoch they are others.
pub fn points(id: &Digest, epoch: u32, nodes: usize) -> Vec<usize> {
    let mut chosen: Vec<usize> = Vec::with_capacity(3);
    let mut k = 0u32;
    while chosen.len() < nodes.min(3) {
        let mut input = [0u8; 40];
        input[..32].copy_from_slice(id);
        input[32..36].copy_from_slice(&epoch.to_le_bytes());
        input[36..].copy_from_slice(&k.to_le_bytes());
        let drawn = hash_domain(DOM_POINT, &input);
        let index = u32::from_le_bytes(drawn[..4].try_into().expect("four bytes")) as usize % nodes;
        if !chosen.contains(&index) {
            chosen.push(index);
        }
        k += 1;
    }
    chosen
}

/// For how many blocks either side of where one epoch gives way to
/// the next a wallet is reached by the nodes of both: time enough for
/// a way to be opened to the new ones, and for whoever sends to be a
/// block ahead or behind.
pub const OVERLAP: u32 = 2;

/// The epochs a wallet is to be reached by the nodes of, when the
/// chain is `height` blocks high: the one that height is of, and for
/// [`OVERLAP`] blocks either side of where one epoch gives way to the
/// next, the other too. Whoever sends looks where the epoch of its own
/// chain says, and its chain may be a block ahead or behind: the
/// wallet is there either way.
pub fn reached_epochs(height: u32) -> Vec<u32> {
    use crate::consensus::EPOCH;
    let (epoch, into) = (height / EPOCH, height % EPOCH);
    let mut epochs = vec![epoch];
    if into < OVERLAP && epoch > 0 {
        epochs.push(epoch - 1);
    }
    if into >= EPOCH - OVERLAP {
        epochs.push(epoch + 1);
    }
    epochs
}

/// Which of `nodes` nodes a wallet of id `id` is to be reached at when
/// the chain is `height` blocks high: those of each epoch it is to be
/// reached by the nodes of, none twice, those of its own epoch first.
pub fn reached_points(id: &Digest, height: u32, nodes: usize) -> Vec<usize> {
    let mut all: Vec<usize> = Vec::new();
    for epoch in reached_epochs(height) {
        for point in points(id, epoch, nodes) {
            if !all.contains(&point) {
                all.push(point);
            }
        }
    }
    all
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Where one epoch gives way to the next a wallet is reached by the
    /// nodes of both: whoever sends, a few blocks ahead of it or
    /// behind, finds it at the nodes its own chain says.
    #[test]
    fn a_wallet_is_reached_by_the_nodes_of_both_epochs_where_they_meet() {
        use crate::consensus::EPOCH;
        const GRACE: u32 = OVERLAP;
        assert_eq!(reached_epochs(0), [0]);
        assert_eq!(reached_epochs(GRACE), [0]);
        assert_eq!(reached_epochs(EPOCH - GRACE - 1), [0]);
        assert_eq!(reached_epochs(EPOCH - GRACE), [0, 1]);
        assert_eq!(reached_epochs(EPOCH - 1), [0, 1]);
        assert_eq!(reached_epochs(EPOCH), [1, 0]);
        assert_eq!(reached_epochs(EPOCH + GRACE - 1), [1, 0]);
        assert_eq!(reached_epochs(EPOCH + GRACE), [1]);
        assert_eq!(reached_epochs(7 * EPOCH + 70), [7]);
        let id = crate::address::id_of(mldsa::keygen(&[5; 32]).public_key());
        for height in 0..3 * EPOCH {
            let reached = reached_points(&id, height, 50);
            // Whoever sends, its chain up to GRACE blocks ahead or
            // behind, looks at nodes the wallet is reached at.
            for theirs in height.saturating_sub(GRACE)..=height + GRACE {
                let looked = points(&id, theirs / EPOCH, 50);
                assert!(looked.iter().all(|p| reached.contains(p)), "at {height}, a sender at {theirs}");
            }
            assert!(reached.len() <= 6 && reached[..3] == points(&id, height / EPOCH, 50)[..]);
        }
        // Mostly it is three nodes, and never one twice.
        assert_eq!(reached_points(&id, 70, 50).len(), 3);
        let mut of_two = reached_points(&id, EPOCH, 2);
        of_two.sort_unstable();
        assert_eq!(of_two, [0, 1]);
    }

    fn wallet(seed: u8) -> (mldsa::SecretKey, mlkem::SecretKey) {
        (mldsa::keygen(&[seed; 32]), mlkem::keygen(&[seed.wrapping_add(100); 64]))
    }

    fn said(w: &(mldsa::SecretKey, mlkem::SecretKey), seq: u64, expires: u64, bind: u64) -> Vec<u8> {
        announce(&w.0, w.1.public_key().try_into().unwrap(), seq, expires, bind)
    }

    /// An announcement is taken from the key that signed it, while it
    /// holds; changed anywhere, or past its time, it is nothing.
    #[test]
    fn an_announcement_is_its_signers() {
        let alice = wallet(1);
        let bytes = said(&alice, 7, 2000, 99);
        assert_eq!(bytes.len(), ANNOUNCE_LEN);
        let read = Announced::read(&bytes, 1000).unwrap();
        assert_eq!((read.seq(), read.expires(), read.bind()), (7, 2000, 99));
        assert_eq!(read.id(), id_of(alice.0.public_key()));
        assert_eq!(read.kyber(), alice.1.public_key());
        assert_eq!(Announced::read(&bytes, 2000), None);
        assert_eq!(Announced::read(&bytes[1..], 1000), None);
        // Each part of it is under the signature: the key to seal to,
        // the numbers, the token; and the key that signs is the id.
        for at in [0, mldsa::PK_LEN, SIGNED.end - 20, SIGNED.end - 12, SIGNED.end - 4, SIGNED.end, ANNOUNCE_LEN - 1] {
            let mut changed = bytes.clone();
            changed[at] ^= 1;
            assert_eq!(Announced::read(&changed, 1000), None, "byte {at}");
        }
    }

    /// A message sealed to a wallet is opened by it and by nobody else,
    /// and changed on the way it is nothing. It says nothing of who
    /// sent it: only a key to answer to.
    #[test]
    fn a_message_is_for_one_wallet_and_says_nothing_of_its_sender() {
        let (alice, bob, carol) = (wallet(1), wallet(2), wallet(3));
        let to_bob = said(&bob, 1, 5000, 0);
        let bob_said = Announced::read(&to_bob, 1000).unwrap();
        let reply = mlkem::keygen(&[7; 64]);
        let sealed = seal(&bob_said, reply.public_key(), KIND_SLATE, b"a slate", &[9; 32]).unwrap();
        assert_eq!(sealed.len(), OVERHEAD + 7);
        assert_eq!((sealed_to(&sealed), sealed_answers(&sealed)), (Some(bob_said.id()), None));
        let opened = open(&bob.1, &bob_said.id(), &sealed).unwrap();
        assert_eq!((opened.from, opened.kind, &opened.body[..]), (None, KIND_SLATE, &b"a slate"[..]));
        assert_eq!((opened.id, &opened.reply[..]), (sealed_id(&sealed), reply.public_key()));
        // Nothing of Alice is in it, sealed or opened: not her key, nor
        // anything made of it.
        let key = alice.0.public_key();
        assert!(!sealed.windows(32).any(|w| w == &key[..32]));
        assert!(!opened.reply.windows(32).any(|w| w == &key[..32]));
        // Not for Carol, nor to be opened with her key; nor with a key
        // of Bob's that it was not sealed to.
        let carol_id = id_of(carol.0.public_key());
        assert_eq!(open(&carol.1, &carol_id, &sealed), None);
        assert_eq!(open(&carol.1, &bob_said.id(), &sealed), None);
        assert_eq!(open(&mlkem::keygen(&[50; 64]), &bob_said.id(), &sealed), None);
        // Changed anywhere, or cut short.
        for at in [0, 1, 20, 40, 1 + 32 + mlkem::CT_LEN, sealed.len() - 1] {
            let mut changed = sealed.clone();
            changed[at] ^= 1;
            assert_eq!(open(&bob.1, &bob_said.id(), &changed), None, "byte {at}");
        }
        assert_eq!(open(&bob.1, &bob_said.id(), &sealed[..sealed.len() - 1]), None);
        // No longer than a message may be; and a key to answer to that
        // is one.
        assert_eq!(seal(&bob_said, reply.public_key(), KIND_SLATE, &vec![0; MAX_BODY + 1], &[9; 32]), None);
        assert!(seal(&bob_said, reply.public_key(), KIND_SLATE, &vec![0; MAX_BODY], &[9; 32]).is_some());
        assert_eq!(seal(&bob_said, &reply.public_key()[1..], KIND_SLATE, b"x", &[9; 32]), None);
    }

    /// The answer to a message goes to the key the message carried, and
    /// says who answers, by a key that is checked: whoever sent the
    /// message takes it from the wallet it sent to, and from no other.
    /// It answers that message and no other.
    #[test]
    fn an_answer_is_its_signers_and_to_one_message() {
        let (bob, carol) = (wallet(2), wallet(3));
        let bob_said_bytes = said(&bob, 1, 5000, 0);
        let bob_said = Announced::read(&bob_said_bytes, 1000).unwrap();
        let reply = mlkem::keygen(&[7; 64]);
        let sent = seal(&bob_said, reply.public_key(), KIND_SLATE, b"a slate", &[9; 32]).unwrap();
        let got = open(&bob.1, &bob_said.id(), &sent).unwrap();
        // Bob answers.
        let answer = seal_answer(&bob.0, &got.reply, &got.id, KIND_SLATE, b"its answer", &[4; 32]).unwrap();
        assert_eq!(answer.len(), ANSWER_OVERHEAD + 10);
        assert_eq!((sealed_answers(&answer), sealed_to(&answer)), (Some(got.id), None));
        let back = open_answer(&reply, &got.id, &answer).unwrap();
        assert_eq!((back.from, back.answers), (Some(id_of(bob.0.public_key())), Some(got.id)));
        assert_eq!((back.kind, &back.body[..], back.reply.len()), (KIND_SLATE, &b"its answer"[..], 0));
        // Carol, who saw the message pass, answers in Bob's place: it
        // opens, and is Carol's. (Whoever sent the message holds that
        // against whom it sent it to.)
        let forged = seal_answer(&carol.0, reply.public_key(), &got.id, KIND_SLATE, b"pay me", &[4; 32]).unwrap();
        assert_eq!(open_answer(&reply, &got.id, &forged).unwrap().from, Some(id_of(carol.0.public_key())));
        // Not the answer to another message; not to be opened with
        // another key; not changed; and no message sent to a wallet.
        let other = sealed_id(b"another message");
        assert_eq!(open_answer(&reply, &other, &answer), None);
        assert_eq!(open_answer(&mlkem::keygen(&[8; 64]), &got.id, &answer), None);
        for at in [0, 5, 1 + 32 + mlkem::CT_LEN + 3, answer.len() - 1] {
            let mut changed = answer.clone();
            changed[at] ^= 1;
            assert_eq!(open_answer(&reply, &got.id, &changed), None, "byte {at}");
        }
        assert_eq!(open_answer(&reply, &got.id, &sent), None);
        assert_eq!(open(&bob.1, &bob_said.id(), &answer), None);
    }

    /// A wallet's points are of its id and the epoch: the same for
    /// whoever reckons them, others at another epoch, as many as there
    /// are nodes up to three, and none twice.
    #[test]
    fn points_are_found_by_anyone_and_move() {
        let id = id_of(mldsa::keygen(&[1; 32]).public_key());
        let other = id_of(mldsa::keygen(&[2; 32]).public_key());
        assert_eq!(points(&id, 5, 2).len(), 2);
        assert_eq!(points(&id, 5, 1), [0]);
        assert_eq!(points(&id, 5, 0), [] as [usize; 0]);
        let at = points(&id, 5, 50);
        assert_eq!(at.len(), 3);
        assert_eq!(at, points(&id, 5, 50));
        assert!(at[0] != at[1] && at[1] != at[2] && at[0] != at[2] && at.iter().all(|i| *i < 50));
        assert_ne!(at, points(&id, 6, 50));
        assert_ne!(at, points(&other, 5, 50));
    }
}
