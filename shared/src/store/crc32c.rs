//! CRC-32C (Castagnoli), eight bytes at a step.
//!
//! The checksum of every page and root record of the store. It is there
//! to catch what a disk does by accident: a write cut short, a page
//! written to the wrong place, bits that rot. It is no defence against
//! anyone who can write the file.

const POLY: u32 = 0x82f6_3b78;

/// `TABLES[0]` is the byte-at-a-time table; `TABLES[k][b]` is the checksum
/// of the byte `b` followed by `k` zero bytes.
const TABLES: [[u32; 256]; 8] = {
    let mut t = [[0u32; 256]; 8];
    let mut i = 0;
    while i < 256 {
        let mut c = i as u32;
        let mut k = 0;
        while k < 8 {
            c = if c & 1 == 1 { (c >> 1) ^ POLY } else { c >> 1 };
            k += 1;
        }
        t[0][i] = c;
        i += 1;
    }
    let mut k = 1;
    while k < 8 {
        let mut i = 0;
        while i < 256 {
            let prev = t[k - 1][i];
            t[k][i] = (prev >> 8) ^ t[0][(prev & 0xff) as usize];
            i += 1;
        }
        k += 1;
    }
    t
};

/// A checksum being computed over bytes given in pieces.
#[derive(Clone, Copy)]
pub struct Crc(u32);

impl Default for Crc {
    fn default() -> Crc {
        Crc::new()
    }
}

impl Crc {
    pub const fn new() -> Crc {
        Crc(!0)
    }

    pub fn update(&mut self, bytes: &[u8]) {
        let mut c = self.0;
        let mut chunks = bytes.chunks_exact(8);
        for ch in &mut chunks {
            let lo = c ^ u32::from_le_bytes([ch[0], ch[1], ch[2], ch[3]]);
            c = TABLES[7][(lo & 0xff) as usize]
                ^ TABLES[6][((lo >> 8) & 0xff) as usize]
                ^ TABLES[5][((lo >> 16) & 0xff) as usize]
                ^ TABLES[4][(lo >> 24) as usize]
                ^ TABLES[3][ch[4] as usize]
                ^ TABLES[2][ch[5] as usize]
                ^ TABLES[1][ch[6] as usize]
                ^ TABLES[0][ch[7] as usize];
        }
        for b in chunks.remainder() {
            c = (c >> 8) ^ TABLES[0][((c ^ *b as u32) & 0xff) as usize];
        }
        self.0 = c;
    }

    pub fn finish(self) -> u32 {
        !self.0
    }
}

/// The checksum of `parts`, one after another.
pub fn crc32c(parts: &[&[u8]]) -> u32 {
    let mut c = Crc::new();
    for p in parts {
        c.update(p);
    }
    c.finish()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_util::Rng;

    /// The bit-at-a-time definition.
    fn slow(bytes: &[u8]) -> u32 {
        let mut c = !0u32;
        for b in bytes {
            c ^= *b as u32;
            for _ in 0..8 {
                c = if c & 1 == 1 { (c >> 1) ^ POLY } else { c >> 1 };
            }
        }
        !c
    }

    #[test]
    fn known_values() {
        // The check value of the CRC catalogue, and those of RFC 3720.
        assert_eq!(crc32c(&[b"123456789"]), 0xe306_9283);
        assert_eq!(crc32c(&[&[0u8; 32]]), 0x8a91_36aa);
        assert_eq!(crc32c(&[&[0xffu8; 32]]), 0x62a8_ab43);
        let up: Vec<u8> = (0..32).collect();
        assert_eq!(crc32c(&[&up]), 0x46dd_794e);
        assert_eq!(crc32c(&[]), 0);
    }

    #[test]
    fn every_length_and_any_split_agree_with_the_definition() {
        let mut rng = Rng::new(0xc3c);
        let bytes: Vec<u8> = (0..300).map(|_| rng.next_u64() as u8).collect();
        for len in 0..bytes.len() {
            let want = slow(&bytes[..len]);
            assert_eq!(crc32c(&[&bytes[..len]]), want, "{len}");
            let cut = rng.next_u64() as usize % (len + 1);
            assert_eq!(crc32c(&[&bytes[..cut], &bytes[cut..len]]), want, "{len} cut at {cut}");
        }
        // One bit changed anywhere changes it.
        let base = crc32c(&[&bytes]);
        for i in 0..bytes.len() * 8 {
            let mut b = bytes.clone();
            b[i / 8] ^= 1 << (i % 8);
            assert_ne!(crc32c(&[&b]), base);
        }
    }
}
