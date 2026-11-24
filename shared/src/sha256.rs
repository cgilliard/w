//! SHA-256 (FIPS 180-4).
//!
//! The chain's own hash is Poseidon2; this one is for what must be read
//! outside it: a header's auxiliary bytes are the SHA-256 Merkle root of
//! sixteen leaves, and a consensus file is named by its SHA-256, so that
//! any tool can check either.
//!
//! The input is taken as it comes ([`Sha256::update`]) and nothing is
//! copied but a block's worth: hashing a megabyte holds 104 bytes.

const K: [u32; 64] = [
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5, 0xd807aa98,
    0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174, 0xe49b69c1, 0xefbe4786,
    0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da, 0x983e5152, 0xa831c66d, 0xb00327c8,
    0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967, 0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13,
    0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85, 0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819,
    0xd6990624, 0xf40e3585, 0x106aa070, 0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a,
    0x5b9cca4f, 0x682e6ff3, 0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7,
    0xc67178f2,
];

/// A hash in the making.
#[derive(Clone)]
pub struct Sha256 {
    state: [u32; 8],
    /// The bytes of a block not yet whole.
    block: [u8; 64],
    /// Bytes taken so far.
    len: u64,
}

impl Default for Sha256 {
    fn default() -> Self {
        Sha256::new()
    }
}

impl Sha256 {
    pub fn new() -> Sha256 {
        Sha256 {
            state: [0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19],
            block: [0; 64],
            len: 0,
        }
    }

    fn compress(state: &mut [u32; 8], block: &[u8; 64]) {
        let mut w = [0u32; 64];
        for (i, word) in block.chunks_exact(4).enumerate() {
            w[i] = u32::from_be_bytes(word.try_into().unwrap());
        }
        for i in 16..64 {
            let s0 = w[i - 15].rotate_right(7) ^ w[i - 15].rotate_right(18) ^ (w[i - 15] >> 3);
            let s1 = w[i - 2].rotate_right(17) ^ w[i - 2].rotate_right(19) ^ (w[i - 2] >> 10);
            w[i] = w[i - 16].wrapping_add(s0).wrapping_add(w[i - 7]).wrapping_add(s1);
        }
        let [mut a, mut b, mut c, mut d, mut e, mut f, mut g, mut h] = *state;
        for i in 0..64 {
            let s1 = e.rotate_right(6) ^ e.rotate_right(11) ^ e.rotate_right(25);
            let ch = (e & f) ^ (!e & g);
            let t1 = h.wrapping_add(s1).wrapping_add(ch).wrapping_add(K[i]).wrapping_add(w[i]);
            let s0 = a.rotate_right(2) ^ a.rotate_right(13) ^ a.rotate_right(22);
            let maj = (a & b) ^ (a & c) ^ (b & c);
            let t2 = s0.wrapping_add(maj);
            (h, g, f, e, d, c, b, a) = (g, f, e, d.wrapping_add(t1), c, b, a, t1.wrapping_add(t2));
        }
        for (s, x) in state.iter_mut().zip([a, b, c, d, e, f, g, h]) {
            *s = s.wrapping_add(x);
        }
    }

    /// Takes more of the input.
    pub fn update(&mut self, mut data: &[u8]) {
        let held = (self.len % 64) as usize;
        self.len += data.len() as u64;
        if held > 0 {
            let take = data.len().min(64 - held);
            self.block[held..held + take].copy_from_slice(&data[..take]);
            data = &data[take..];
            if held + take < 64 {
                return;
            }
            Sha256::compress(&mut self.state, &self.block);
        }
        let mut blocks = data.chunks_exact(64);
        for block in &mut blocks {
            Sha256::compress(&mut self.state, block.try_into().unwrap());
        }
        let rest = blocks.remainder();
        self.block[..rest.len()].copy_from_slice(rest);
    }

    /// The hash of everything taken.
    pub fn finish(mut self) -> [u8; 32] {
        let held = (self.len % 64) as usize;
        let bits = self.len.wrapping_mul(8);
        self.block[held] = 0x80;
        self.block[held + 1..].fill(0);
        if held >= 56 {
            Sha256::compress(&mut self.state, &self.block);
            self.block = [0; 64];
        }
        self.block[56..].copy_from_slice(&bits.to_be_bytes());
        Sha256::compress(&mut self.state, &self.block);
        let mut out = [0u8; 32];
        for (o, s) in out.chunks_exact_mut(4).zip(self.state) {
            o.copy_from_slice(&s.to_be_bytes());
        }
        out
    }
}

/// SHA-256 of `data`.
pub fn sha256(data: &[u8]) -> [u8; 32] {
    let mut h = Sha256::new();
    h.update(data);
    h.finish()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn hex(h: &[u8; 32]) -> String {
        h.iter().map(|b| format!("{b:02x}")).collect()
    }

    /// The standard's own examples, and the lengths around a block's
    /// edge, where the padding takes a block of its own.
    #[test]
    fn the_standards_examples() {
        assert_eq!(hex(&sha256(b"")), "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855");
        assert_eq!(hex(&sha256(b"abc")), "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad");
        assert_eq!(
            hex(&sha256(b"abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq")),
            "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1"
        );
        assert_eq!(
            hex(&sha256(&[b'a'; 1_000_000])),
            "cdc76e5c9914fb9281a1c7e284d73e67f1809a48a497200e046d39ccc7112cd0"
        );
        // 55, 56 and 64 bytes of 'a': the padding fits, does not, and
        // follows a whole block.
        assert_eq!(hex(&sha256(&[b'a'; 55])), "9f4390f8d30c2dd92ec9f095b65e2b9ae9b0a925a5258e241c9f1e910f734318");
        assert_eq!(hex(&sha256(&[b'a'; 56])), "b35439a4ac6f0948b6d6f9e3c6af0f5f590ce20f1bde7090ef7970686ec6738a");
        assert_eq!(hex(&sha256(&[b'a'; 64])), "ffe054fe7ae0cb6dc65c3af9b61d5209f439851db43d0ba5997337df154668eb");
    }

    /// However the input is cut, the hash is that of the whole.
    #[test]
    fn the_input_comes_in_any_pieces() {
        let data: Vec<u8> = (0..1000u32).map(|i| (i * 7 + 3) as u8).collect();
        let whole = sha256(&data);
        for piece in [1, 3, 55, 63, 64, 65, 127, 128, 999] {
            let mut h = Sha256::new();
            data.chunks(piece).for_each(|c| h.update(c));
            assert_eq!(h.finish(), whole, "in pieces of {piece}");
        }
        let mut h = Sha256::default();
        h.update(&[]);
        h.update(&data[..70]);
        h.update(&[]);
        h.update(&data[70..]);
        assert_eq!(h.finish(), whole);
        assert_ne!(sha256(&data[..999]), whole);
    }
}
