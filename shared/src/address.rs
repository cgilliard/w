//! The text form of an identity: the 32-byte id in bech32m with the
//! human-readable part `tab`, so an address reads `tab1…`, 62
//! characters, case-insensitive, with a 30-bit checksum that detects
//! any four errors and most others.
//!
//! The id is a digest of 32 bytes, the one a name's record holds: the
//! hash of a Dilithium (ML-DSA-65) public key under [`DOM_ID`]
//! ([`id_of`]).
//!
//! Nothing here is on the heap but the text of an address, where one
//! is asked for.

use crate::hash::{DOM_ID, Digest, digest_from_bytes, digest_to_bytes, hash_domain};

/// The id of a Dilithium public key.
pub fn id_of(dilithium_public_key: &[u8]) -> Digest {
    hash_domain(DOM_ID, dilithium_public_key)
}

/// The human-readable part of every address.
pub const HRP: &str = "tab";
/// Characters of an address: the prefix, the separator, 52 data
/// characters and 6 of checksum.
pub const LEN: usize = HRP.len() + 1 + DATA + 6;
/// Five-bit groups of 32 bytes.
const DATA: usize = 52;

const CHARSET: &[u8; 32] = b"qpzry9x8gf2tvdw0s3jn54khce6mua7l";
const BECH32M: u32 = 0x2bc8_30a3;

fn polymod(values: impl IntoIterator<Item = u8>) -> u32 {
    const GEN: [u32; 5] = [0x3b6a_57b2, 0x2650_8e6d, 0x1ea1_19fa, 0x3d42_33dd, 0x2a14_62b3];
    let mut chk = 1u32;
    for v in values {
        let top = chk >> 25;
        chk = ((chk & 0x1ff_ffff) << 5) ^ u32::from(v);
        for (i, g) in GEN.iter().enumerate() {
            if (top >> i) & 1 == 1 {
                chk ^= g;
            }
        }
    }
    chk
}

/// The prefix as the checksum takes it: its high bits, a zero, its low
/// bits.
fn hrp_expand() -> impl Iterator<Item = u8> {
    HRP.bytes().map(|b| b >> 5).chain([0]).chain(HRP.bytes().map(|b| b & 31))
}

/// The address of an id.
pub fn encode(id: &Digest) -> String {
    let bytes = digest_to_bytes(id);
    let mut data = [0u8; DATA];
    let (mut acc, mut bits, mut n) = (0u32, 0u32, 0);
    for b in bytes {
        acc = (acc << 8) | u32::from(b);
        bits += 8;
        while bits >= 5 {
            bits -= 5;
            data[n] = ((acc >> bits) & 31) as u8;
            n += 1;
        }
    }
    if bits > 0 {
        data[n] = ((acc << (5 - bits)) & 31) as u8;
    }
    let pm = polymod(hrp_expand().chain(data).chain([0; 6])) ^ BECH32M;
    let mut out = String::with_capacity(LEN);
    out.push_str(HRP);
    out.push('1');
    for d in &data {
        out.push(CHARSET[*d as usize] as char);
    }
    for i in 0..6 {
        out.push(CHARSET[((pm >> (5 * (5 - i))) & 31) as usize] as char);
    }
    out
}

/// The id of an address, if it is one: the prefix, the checksum and the
/// length must all hold.
pub fn decode(s: &str) -> Option<Digest> {
    let text = s.as_bytes();
    if text.len() != LEN || (text.iter().any(u8::is_ascii_lowercase) && text.iter().any(u8::is_ascii_uppercase)) {
        return None;
    }
    let (hrp, rest) = text.split_at(HRP.len());
    if !hrp.eq_ignore_ascii_case(HRP.as_bytes()) || rest[0] != b'1' {
        return None;
    }
    // Its data and its checksum: five bits a character.
    let mut data = [0u8; DATA + 6];
    for (d, c) in data.iter_mut().zip(&rest[1..]) {
        *d = CHARSET.iter().position(|x| *x == c.to_ascii_lowercase())? as u8;
    }
    if polymod(hrp_expand().chain(data)) != BECH32M {
        return None;
    }
    let (mut acc, mut bits, mut n) = (0u32, 0u32, 0);
    let mut bytes = [0u8; 32];
    for d in &data[..DATA] {
        acc = (acc << 5) | u32::from(*d);
        bits += 5;
        if bits >= 8 {
            bits -= 8;
            *bytes.get_mut(n)? = ((acc >> bits) & 0xff) as u8;
            n += 1;
        }
    }
    // The last group pads with zero bits only.
    if n != 32 || bits >= 5 || (acc & ((1 << bits) - 1)) != 0 {
        return None;
    }
    digest_from_bytes(&bytes)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn addresses_round_trip_and_catch_errors() {
        let id: Digest = core::array::from_fn(|i| (123 * (i as u32 + 1)) as u8);
        let a = encode(&id);
        assert_eq!(a.len(), LEN);
        assert!(a.starts_with("tab1"));
        assert_eq!(decode(&a), Some(id));
        assert_eq!(decode(&a.to_uppercase()), Some(id));
        // One wrong character, a swapped pair, a missing character, mixed
        // case and another prefix are all refused.
        let mut bytes: Vec<u8> = a.bytes().collect();
        bytes[10] = if bytes[10] == b'q' { b'p' } else { b'q' };
        assert_eq!(decode(std::str::from_utf8(&bytes).unwrap()), None);
        let mut swapped = a.clone().into_bytes();
        swapped.swap(20, 21);
        if swapped != a.as_bytes() {
            assert_eq!(decode(std::str::from_utf8(&swapped).unwrap()), None);
        }
        assert_eq!(decode(&a[..a.len() - 1]), None);
        let mixed = format!("{}{}", &a[..5].to_uppercase(), &a[5..]);
        assert_eq!(decode(&mixed), None);
        assert_eq!(decode(&format!("tbb{}", &a[3..])), None);
        assert_eq!(decode(&format!("tab2{}", &a[4..])), None);
        // Every id is one address; the zero id too.
        let zero = [0u8; 32];
        assert_eq!(decode(&encode(&zero)), Some(zero));
        assert_ne!(encode(&zero), a);
    }

    #[test]
    fn ids_come_from_keys() {
        let pk = crate::mldsa::keygen(&[9u8; 32]);
        let id = id_of(pk.public_key());
        assert_eq!(id, id_of(pk.public_key()));
        assert_ne!(id, id_of(crate::mldsa::keygen(&[10u8; 32]).public_key()));
        assert_ne!(id, id_of(&pk.public_key()[1..]));
        assert_eq!(decode(&encode(&id)), Some(id));
    }

    /// The addresses of known keys do not change from build to build,
    /// nor what those keys sign.
    #[test]
    fn the_references_addresses_are_these() {
        for (seed, address, signed) in REFERENCE {
            let key = crate::mldsa::keygen(&[*seed; 32]);
            assert_eq!(encode(&id_of(key.public_key())), *address, "seed {seed}");
            let signature = key.sign(b"message", b"ctx");
            let sum = signature.iter().fold(0u64, |a, b| a.wrapping_mul(1_000_003).wrapping_add(*b as u64));
            assert_eq!(sum, *signed, "seed {seed}");
        }
    }

    /// Of the keys `mldsa::keygen(&[seed; 32])`: the address of each,
    /// and its signature of `message` under
    /// `ctx` folded to a number (each byte added to a million and three
    /// times what came before).
    const REFERENCE: &[(u8, &str, u64)] = &[
        (1, "tab169556w08ak4fjkznqsyd83lcrpqm694r2mcws686hhypkvrtpj8sy0x0vj", 15574511451408669866),
        (2, "tab1p05jv60hh37gy20qgyfay3hfcvut6czu2xcr6gp78dadxm843ntsdfee8u", 15418332651188232661),
        (9, "tab1w88x5m3udnszhtcl00fn3k5y945w429d7sv4fwwgugrsgw8hnanstrm4u7", 4747689551428418270),
        (255, "tab1plhws0azdnjjxen60s9m52k5wx7nuqphjdc3p4p2kux3r9jey92qf7jeth", 11402255765264279335),
    ];
}
