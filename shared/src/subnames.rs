//! Names under a name: `label@name`, which the chain knows nothing of.
//!
//! The chain keeps names, a few a block ([`crate::name`]): not one for
//! everybody. Whoever holds a name gives out names under it, as many as
//! it likes, to whomever it likes: `alice@mailhub` is the wallet that
//! the holder of `mailhub` says it is. It says so in a certificate
//! ([`certify`]): the label, the name, the id of the wallet, a number
//! that rises and a time it holds until, under the signature of the
//! key the name's value on the chain is the id of. Whoever reads the
//! chain checks it with that and nothing else.
//!
//! The key a name is held by is worth keeping where nothing can get at
//! it, and a key that signs certificates all day is not there. So the
//! holder of a name may say, once and for a time, that another key
//! signs for that name ([`delegate`]): for that name alone, not for
//! whatever else the holder's key holds. A certificate signed by such
//! a key goes with what the holder said of it, and the two are checked
//! together ([`read`]). What was said holds until its time is past, or
//! until the name is another key's on the chain: there is nowhere it
//! is taken back sooner.
//!
//! A certificate is given to the wallet it names, which shows it to
//! the nodes the full name is reached at ([`point`]) for as long as it
//! is there itself: nothing is kept anywhere for a wallet that is not.
//! Whoever pays `alice@mailhub` asks those nodes, and is given the
//! certificate with what the wallet announces.

use crate::address::id_of;
use crate::hash::{Digest, digest_from_bytes, digest_to_bytes, hash_domain};
use crate::mldsa::{self, PK_LEN, SIG_LEN};
use crate::name::{NAME_MAX, valid_name};

/// Domain tag of where a full name is reached: `H(label ‖ '@' ‖ name)`.
pub const DOM_SUBNAME: u32 = 62;
/// How long a certificate is signed for, in seconds, and how long
/// before another is signed in its place while its signer runs: so
/// that a signer may be away most of a week and nothing lapses.
pub const HOLDS: u64 = 7 * 86_400;
pub const RENEWED: u64 = 86_400;
/// The furthest ahead a certificate, or the word that a key signs for
/// a name, may hold: one that says longer is not taken.
pub const MOST_HOLDS: u64 = 90 * 86_400;
/// The longest a certificate with what goes with it is.
pub const MAX_BUNDLE: usize = 2 + 2 * (2 + 2 * NAME_MAX + 48 + PK_LEN + SIG_LEN);

const CTX_CERT: &[u8] = b"tab subname";
const CTX_DELEGATE: &[u8] = b"tab subname delegate";

/// A full name as it is written, in its two parts: the label and the
/// name, each as a name of the chain is. None of what is not one.
pub fn split(full: &str) -> Option<(&str, &str)> {
    let (label, name) = full.split_once('@')?;
    (valid_name(label.as_bytes()) && valid_name(name.as_bytes())).then_some((label, name))
}

/// The id a full name is reached by the nodes of: as a wallet's id
/// says where the wallet is reached ([`crate::msg::points`]).
pub fn point(label: &[u8], name: &[u8]) -> Digest {
    let mut full = Vec::with_capacity(label.len() + 1 + name.len());
    full.extend_from_slice(label);
    full.push(b'@');
    full.extend_from_slice(name);
    hash_domain(DOM_SUBNAME, &full)
}

fn put(out: &mut Vec<u8>, name: &[u8]) {
    out.push(name.len() as u8);
    out.extend_from_slice(name);
}

/// A certificate: `label@name` is the wallet of id `holder`, by the
/// key `key`, until `expires` (Unix seconds) unless one of a higher
/// `seq` says otherwise.
pub fn certify(key: &mldsa::SecretKey, label: &[u8], name: &[u8], holder: &Digest, seq: u64, expires: u64) -> Vec<u8> {
    let mut out = Vec::with_capacity(2 + label.len() + name.len() + 48 + PK_LEN + SIG_LEN);
    put(&mut out, label);
    put(&mut out, name);
    out.extend_from_slice(&digest_to_bytes(holder));
    out.extend_from_slice(&seq.to_le_bytes());
    out.extend_from_slice(&expires.to_le_bytes());
    out.extend_from_slice(key.public_key());
    let signature = key.sign(&out, CTX_CERT);
    out.extend_from_slice(&signature);
    out
}

/// The word of the holder of `name`, whose key is `key`, that the key
/// of id `signer` signs certificates for that name until `expires`.
pub fn delegate(key: &mldsa::SecretKey, name: &[u8], signer: &Digest, expires: u64) -> Vec<u8> {
    let mut out = Vec::with_capacity(1 + name.len() + 40 + PK_LEN + SIG_LEN);
    put(&mut out, name);
    out.extend_from_slice(&digest_to_bytes(signer));
    out.extend_from_slice(&expires.to_le_bytes());
    out.extend_from_slice(key.public_key());
    let signature = key.sign(&out, CTX_DELEGATE);
    out.extend_from_slice(&signature);
    out
}

/// A certificate as it travels: with the word of the name's holder
/// that its signer signs for the name, if the holder did not sign it
/// itself.
pub fn bundle(certificate: &[u8], delegation: Option<&[u8]>) -> Vec<u8> {
    let mut out = Vec::with_capacity(2 + certificate.len() + delegation.map_or(0, <[u8]>::len));
    out.extend_from_slice(&(certificate.len() as u16).to_le_bytes());
    out.extend_from_slice(certificate);
    out.extend_from_slice(delegation.unwrap_or_default());
    out
}

/// A certificate that was checked, with what went with it: sound,
/// signed, and in its time. Whether it is the name's is for whoever
/// reads the chain to say ([`Checked::by`]).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Checked {
    pub label: Vec<u8>,
    pub name: Vec<u8>,
    /// The wallet the full name is.
    pub holder: Digest,
    pub seq: u64,
    /// Until when it holds: the sooner of the certificate's time and
    /// that of the word its signer signs by.
    pub expires: u64,
    /// The id of the key that answers for it: the certificate's own
    /// signer, or the key that said the signer signs for the name.
    /// It is the name's certificate if this is the name's value on the
    /// chain.
    pub by: Digest,
    /// Whether another key than that one signed it.
    pub delegated: bool,
}

impl Checked {
    /// The id the full name is reached by the nodes of.
    pub fn point(&self) -> Digest {
        point(&self.label, &self.name)
    }

    /// The full name, as it is written.
    pub fn full(&self) -> String {
        format!("{}@{}", String::from_utf8_lossy(&self.label), String::from_utf8_lossy(&self.name))
    }
}

struct Reader<'a>(&'a [u8]);

impl<'a> Reader<'a> {
    fn take(&mut self, n: usize) -> Option<&'a [u8]> {
        let (head, rest) = self.0.split_at_checked(n)?;
        self.0 = rest;
        Some(head)
    }

    fn name(&mut self) -> Option<&'a [u8]> {
        let n = self.take(1)?[0] as usize;
        self.take(n).filter(|name| valid_name(name))
    }

    fn u64(&mut self) -> Option<u64> {
        Some(u64::from_le_bytes(self.take(8)?.try_into().ok()?))
    }

    /// What is left but for a key and a signature at its end, which
    /// are the key's over all before them: the key.
    fn signed(&mut self, whole: &'a [u8], ctx: &[u8]) -> Option<&'a [u8]> {
        let (key, signature) = (self.take(PK_LEN)?, self.take(SIG_LEN)?);
        let over = &whole[..whole.len() - SIG_LEN];
        (self.0.is_empty() && mldsa::verify(key, over, ctx, signature)).then_some(key)
    }
}

/// Whether a time to hold until is one to take, at `now`.
fn in_time(expires: u64, now: u64) -> bool {
    expires > now && expires <= now + MOST_HOLDS
}

/// Reads and checks a certificate with what goes with it, at `now`
/// (Unix seconds). None if it is not one, is not signed by the key it
/// carries, is past its time or says too long a one; or if it goes
/// with the word of another key that is not sound in the same ways,
/// is of another name, or names another signer.
pub fn read(bundle: &[u8], now: u64) -> Option<Checked> {
    let mut r = Reader(bundle);
    let len = u16::from_le_bytes(r.take(2)?.try_into().ok()?) as usize;
    let (certificate, delegation) = (r.take(len)?, r.0);
    let mut r = Reader(certificate);
    let (label, name) = (r.name()?, r.name()?);
    let holder = digest_from_bytes(r.take(32)?)?;
    let (seq, expires) = (r.u64()?, r.u64()?);
    let signer = id_of(r.signed(certificate, CTX_CERT)?);
    if !in_time(expires, now) {
        return None;
    }
    let (label, name) = (label.to_vec(), name.to_vec());
    if delegation.is_empty() {
        return Some(Checked { label, name, holder, seq, expires, by: signer, delegated: false });
    }
    let word = delegated(delegation, now).filter(|word| word.name == name && word.signer == signer)?;
    Some(Checked { label, name, holder, seq, expires: expires.min(word.expires), by: word.by, delegated: true })
}

/// The word of a name's holder that another key signs for the name,
/// read and checked.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Delegated {
    pub name: Vec<u8>,
    /// The id of the key that signs for the name.
    pub signer: Digest,
    pub expires: u64,
    /// The id of the key that says so: the name's holder, if this is
    /// what the name says on the chain.
    pub by: Digest,
}

/// Reads and checks the word that a key signs for a name, at `now`:
/// none if it is not one, is not signed by the key it carries, or is
/// past its time or says too long a one.
pub fn delegated(delegation: &[u8], now: u64) -> Option<Delegated> {
    let mut r = Reader(delegation);
    let (name, signer) = (r.name()?.to_vec(), digest_from_bytes(r.take(32)?)?);
    let expires = r.u64()?;
    let by = id_of(r.signed(delegation, CTX_DELEGATE)?);
    in_time(expires, now).then_some(Delegated { name, signer, expires, by })
}

#[cfg(test)]
mod tests {
    use super::*;

    const NOW: u64 = 1_800_000_000;

    fn key(seed: u8) -> (mldsa::SecretKey, Digest) {
        let key = mldsa::keygen(&[seed; 32]);
        let id = id_of(key.public_key());
        (key, id)
    }

    /// A full name is a label and a name, each as the chain's names
    /// are; and each full name is reached somewhere of its own.
    #[test]
    fn a_full_name_is_a_label_under_a_name() {
        assert_eq!(split("alice@mailhub"), Some(("alice", "mailhub")));
        for not in ["alice", "@mailhub", "alice@", "Alice@mailhub", "alice@mail.hub", "a@b@c", "a b@c", ""] {
            assert_eq!(split(not), None, "{not}");
        }
        let long = "a".repeat(NAME_MAX);
        assert!(split(&format!("{long}@{long}")).is_some() && split(&format!("{long}a@{long}")).is_none());
        assert_ne!(point(b"alice", b"mailhub"), point(b"alic", b"emailhub"));
        assert_ne!(point(b"alice", b"mailhub"), point(b"mailhub", b"alice"));
        assert_eq!(point(b"alice", b"mailhub"), point(b"alice", b"mailhub"));
    }

    /// A certificate is its signer's: read by anyone, with nothing but
    /// what it carries; and nothing of it can be other than was signed.
    #[test]
    fn a_certificate_is_its_signers() {
        let ((owner, owner_id), (_, alice)) = (key(1), key(2));
        let cert = certify(&owner, b"alice", b"mailhub", &alice, 9, NOW + HOLDS);
        let whole = bundle(&cert, None);
        assert!(whole.len() <= MAX_BUNDLE);
        let read_ = read(&whole, NOW).unwrap();
        assert_eq!(
            (read_.full(), read_.holder, read_.seq, read_.expires),
            ("alice@mailhub".into(), alice, 9, NOW + HOLDS)
        );
        assert_eq!((read_.by, read_.delegated, read_.point()), (owner_id, false, point(b"alice", b"mailhub")));
        // Past its time, or of too long a one.
        assert_eq!(read(&whole, NOW + HOLDS), None);
        assert!(read(&whole, NOW + HOLDS - 1).is_some());
        assert_eq!(
            read(&bundle(&certify(&owner, b"alice", b"mailhub", &alice, 9, NOW + MOST_HOLDS + 1), None), NOW),
            None
        );
        // Changed anywhere, cut short, or with more after it.
        for at in [2, 3, 9, 20, 48, 60, 70, whole.len() - 1] {
            let mut changed = whole.clone();
            changed[at] ^= 1;
            assert_eq!(read(&changed, NOW), None, "byte {at}");
        }
        assert_eq!(read(&whole[..whole.len() - 1], NOW), None);
        assert_eq!(read(&[&whole[..], &[0]].concat(), NOW), None);
        assert_eq!(read(&[], NOW), None);
        // Signed by another: sound, and another's.
        let (other, other_id) = key(3);
        let forged = bundle(&certify(&other, b"alice", b"mailhub", &alice, 10, NOW + HOLDS), None);
        assert_eq!(read(&forged, NOW).unwrap().by, other_id);
    }

    /// The holder of a name says that another key signs for it: what
    /// that key signs for that name answers to the holder, until what
    /// was said is past its time; and for no other name.
    #[test]
    fn another_key_signs_for_a_name_by_its_holders_word() {
        let ((owner, owner_id), (signer, signer_id), (_, alice)) = (key(1), key(4), key(2));
        let word = delegate(&owner, b"mailhub", &signer_id, NOW + 30 * 86_400);
        let cert = certify(&signer, b"alice", b"mailhub", &alice, 3, NOW + HOLDS);
        let whole = bundle(&cert, Some(&word));
        assert!(whole.len() <= MAX_BUNDLE);
        let checked = read(&whole, NOW).unwrap();
        assert_eq!(
            (checked.by, checked.delegated, checked.holder, checked.expires),
            (owner_id, true, alice, NOW + HOLDS)
        );
        // Without the word, it is the signer's own and nobody else's.
        assert_eq!(read(&bundle(&cert, None), NOW).unwrap().by, signer_id);
        // The word holds for less long than the certificate: so does
        // the whole.
        let short = delegate(&owner, b"mailhub", &signer_id, NOW + 3600);
        assert_eq!(read(&bundle(&cert, Some(&short)), NOW).unwrap().expires, NOW + 3600);
        assert_eq!(read(&bundle(&cert, Some(&short)), NOW + 3600), None);
        // For another name, or of another signer: not for this.
        let other_name = delegate(&owner, b"mailhut", &signer_id, NOW + 3600);
        assert_eq!(read(&bundle(&cert, Some(&other_name)), NOW), None);
        let other_signer = delegate(&owner, b"mailhub", &alice, NOW + 3600);
        assert_eq!(read(&bundle(&cert, Some(&other_signer)), NOW), None);
        // And a certificate of the signer's for a name it was given no
        // word for.
        let elsewhere = certify(&signer, b"alice", b"google", &alice, 3, NOW + HOLDS);
        assert_eq!(read(&bundle(&elsewhere, Some(&word)), NOW), None);
        // The word changed, or cut short.
        let mut changed = whole.clone();
        let at = 2 + cert.len() + 12;
        changed[at] ^= 1;
        assert_eq!(read(&changed, NOW), None);
        assert_eq!(read(&whole[..whole.len() - 1], NOW), None);
    }
}
