//! Blake3: the hash everything in this crate is made with.
//!
//! This is the function of the Blake3 specification, checked against its
//! official test vectors in all three modes ([`hash`], [`keyed_hash`],
//! [`derive_key`]); any Blake3 library gives the same bytes. Outputs are
//! 32 bytes: the extended output is not here.
//!
//! # Shape
//!
//! An input is cut into chunks of 1,024 bytes and a chunk into blocks of
//! 64. [`compress`] takes a chaining value of eight words, a block, a
//! counter, the block's length and flags. A chunk is its blocks
//! compressed one into the next, from the key; chunks are joined in
//! pairs by one more compression each, a binary tree whose left side is
//! always the largest whole power of two of chunks. The last compression
//! of all carries the `ROOT` flag.
//!
//! So an input of one block is one compression, and two digests hashed
//! together are one compression: what a Merkle tree and a circuit pay
//! for ([`compressions`]).
//!
//! # Speed
//!
//! [`compress`] is portable. [`keyed_hash_many`] hashes many short
//! inputs of one length, which is what building a Merkle tree is; on
//! x86-64 with AVX2 it takes eight at a time, a lane each. Long inputs
//! are hashed a block at a time on every target: nothing here hashes
//! enough of them to want more.

pub const OUT_LEN: usize = 32;
pub const KEY_LEN: usize = 32;
pub const BLOCK_LEN: usize = 64;
pub const CHUNK_LEN: usize = 1024;

pub const IV: [u32; 8] =
    [0x6A09E667, 0xBB67AE85, 0x3C6EF372, 0xA54FF53A, 0x510E527F, 0x9B05688C, 0x1F83D9AB, 0x5BE0CD19];

pub const CHUNK_START: u32 = 1 << 0;
pub const CHUNK_END: u32 = 1 << 1;
pub const PARENT: u32 = 1 << 2;
pub const ROOT: u32 = 1 << 3;
pub const KEYED_HASH: u32 = 1 << 4;
pub const DERIVE_KEY_CONTEXT: u32 = 1 << 5;
pub const DERIVE_KEY_MATERIAL: u32 = 1 << 6;

const PERMUTATION: [usize; 16] = [2, 6, 3, 10, 7, 0, 4, 13, 1, 11, 12, 5, 9, 14, 15, 8];

/// Which message word each round reads in each place: the permutation
/// applied once more for each round.
pub const SCHEDULE: [[usize; 16]; 7] = {
    let mut s = [[0usize; 16]; 7];
    let mut i = 0;
    while i < 16 {
        s[0][i] = i;
        i += 1;
    }
    let mut r = 1;
    while r < 7 {
        let mut i = 0;
        while i < 16 {
            s[r][i] = s[r - 1][PERMUTATION[i]];
            i += 1;
        }
        r += 1;
    }
    s
};

/// The four columns, then the four diagonals, a round mixes.
pub const QUARTERS: [[usize; 4]; 8] = [
    [0, 4, 8, 12],
    [1, 5, 9, 13],
    [2, 6, 10, 14],
    [3, 7, 11, 15],
    [0, 5, 10, 15],
    [1, 6, 11, 12],
    [2, 7, 8, 13],
    [3, 4, 9, 14],
];

/// The compression function, truncated to the chaining value it leaves.
#[inline(always)]
pub fn compress(cv: &[u32; 8], m: &[u32; 16], counter: u64, block_len: u32, flags: u32) -> [u32; 8] {
    let mut v = [
        cv[0],
        cv[1],
        cv[2],
        cv[3],
        cv[4],
        cv[5],
        cv[6],
        cv[7],
        IV[0],
        IV[1],
        IV[2],
        IV[3],
        counter as u32,
        (counter >> 32) as u32,
        block_len,
        flags,
    ];
    for s in &SCHEDULE {
        for (q, [a, b, c, d]) in QUARTERS.iter().copied().enumerate() {
            v[a] = v[a].wrapping_add(v[b]).wrapping_add(m[s[2 * q]]);
            v[d] = (v[d] ^ v[a]).rotate_right(16);
            v[c] = v[c].wrapping_add(v[d]);
            v[b] = (v[b] ^ v[c]).rotate_right(12);
            v[a] = v[a].wrapping_add(v[b]).wrapping_add(m[s[2 * q + 1]]);
            v[d] = (v[d] ^ v[a]).rotate_right(8);
            v[c] = v[c].wrapping_add(v[d]);
            v[b] = (v[b] ^ v[c]).rotate_right(7);
        }
    }
    std::array::from_fn(|i| v[i] ^ v[i + 8])
}

/// Bytes as little-endian words, zeros after the last byte.
pub fn words<const N: usize>(bytes: &[u8]) -> [u32; N] {
    debug_assert!(bytes.len() <= 4 * N);
    let mut out = [0u32; N];
    for (i, b) in bytes.iter().enumerate() {
        out[i / 4] |= (*b as u32) << (8 * (i % 4));
    }
    out
}

/// Words as the bytes they came from.
pub fn bytes(cv: &[u32; 8]) -> [u8; OUT_LEN] {
    let mut out = [0u8; OUT_LEN];
    for (i, w) in cv.iter().enumerate() {
        out[4 * i..4 * i + 4].copy_from_slice(&w.to_le_bytes());
    }
    out
}

/// How many compressions hashing `len` bytes takes.
pub fn compressions(len: usize) -> usize {
    let chunks = len.div_ceil(CHUNK_LEN).max(1);
    // Every chunk but the last is 16 blocks; the tree joins the chunks
    // with one compression fewer than there are.
    let last = len - (chunks - 1) * CHUNK_LEN;
    (chunks - 1) * 16 + last.div_ceil(BLOCK_LEN).max(1) + (chunks - 1)
}

/// One chunk: at most 1,024 bytes, the `counter`-th of its input. With
/// `root`, it is the whole input.
fn chunk(key: &[u32; 8], input: &[u8], counter: u64, flags: u32, root: bool) -> [u32; 8] {
    debug_assert!(input.len() <= CHUNK_LEN);
    let n = input.len().div_ceil(BLOCK_LEN).max(1);
    let mut cv = *key;
    for i in 0..n {
        let block = &input[i * BLOCK_LEN..input.len().min((i + 1) * BLOCK_LEN)];
        let mut f = flags;
        if i == 0 {
            f |= CHUNK_START;
        }
        if i == n - 1 {
            f |= CHUNK_END;
            if root {
                f |= ROOT;
            }
        }
        cv = compress(&cv, &words(block), counter, block.len() as u32, f);
    }
    cv
}

/// Bytes of the left side of a tree over `len` bytes, more than a chunk:
/// the largest power of two of whole chunks that leaves something over.
fn left_len(len: usize) -> usize {
    let full = (len - 1) / CHUNK_LEN;
    CHUNK_LEN << full.ilog2()
}

fn parent(key: &[u32; 8], left: &[u32; 8], right: &[u32; 8], flags: u32) -> [u32; 8] {
    let m: [u32; 16] = std::array::from_fn(|i| if i < 8 { left[i] } else { right[i - 8] });
    compress(key, &m, 0, BLOCK_LEN as u32, flags | PARENT)
}

/// The chaining value of a subtree that is not the whole input.
fn subtree(key: &[u32; 8], input: &[u8], counter: u64, flags: u32) -> [u32; 8] {
    if input.len() <= CHUNK_LEN {
        return chunk(key, input, counter, flags, false);
    }
    let (l, r) = input.split_at(left_len(input.len()));
    let left = subtree(key, l, counter, flags);
    let right = subtree(key, r, counter + (l.len() / CHUNK_LEN) as u64, flags);
    parent(key, &left, &right, flags)
}

fn root(key: &[u32; 8], input: &[u8], flags: u32) -> [u32; 8] {
    if input.len() <= CHUNK_LEN {
        return chunk(key, input, 0, flags, true);
    }
    let (l, r) = input.split_at(left_len(input.len()));
    let left = subtree(key, l, 0, flags);
    let right = subtree(key, r, (l.len() / CHUNK_LEN) as u64, flags);
    parent(key, &left, &right, flags | ROOT)
}

/// The Blake3 hash of `input`.
pub fn hash(input: &[u8]) -> [u8; OUT_LEN] {
    bytes(&root(&IV, input, 0))
}

/// Blake3's keyed hash of `input` under `key`.
pub fn keyed_hash(key: &[u8; KEY_LEN], input: &[u8]) -> [u8; OUT_LEN] {
    bytes(&root(&words(key), input, KEYED_HASH))
}

/// [`keyed_hash`] under a key given as its eight words.
pub fn keyed_hash_words(key: &[u32; 8], input: &[u8]) -> [u8; OUT_LEN] {
    bytes(&root(key, input, KEYED_HASH))
}

/// Blake3's key derivation: a key for `context` from `material`.
pub fn derive_key(context: &str, material: &[u8]) -> [u8; OUT_LEN] {
    let context_key = root(&IV, context.as_bytes(), DERIVE_KEY_CONTEXT);
    bytes(&root(&context_key, material, DERIVE_KEY_MATERIAL))
}

/// [`keyed_hash_words`] of each of the `out.len()` inputs of `item_len`
/// bytes that `input` is, one after another. An item is a chunk at most.
pub fn keyed_hash_many(key: &[u32; 8], input: &[u8], item_len: usize, out: &mut [[u8; OUT_LEN]]) {
    assert!(item_len <= CHUNK_LEN && input.len() == item_len * out.len());
    #[allow(unused_mut)]
    let mut done = 0;
    #[cfg(all(target_arch = "x86_64", target_feature = "avx2"))]
    if item_len.is_multiple_of(BLOCK_LEN) && item_len > 0 {
        while done + 8 <= out.len() {
            // SAFETY: the target has AVX2 (the cfg above), and eight whole
            // items of whole blocks lie at `done`.
            unsafe { avx2::hash8(key, input[done * item_len..].as_ptr(), item_len, &mut out[done..done + 8]) };
            done += 8;
        }
    }
    for (i, o) in out.iter_mut().enumerate().skip(done) {
        *o = keyed_hash_words(key, &input[i * item_len..(i + 1) * item_len]);
    }
}

#[cfg(all(target_arch = "x86_64", target_feature = "avx2"))]
mod avx2 {
    use super::*;
    use std::arch::x86_64::*;

    /// Rows to columns: `v[i]` word `j` becomes `v[j]` word `i`.
    #[inline(always)]
    unsafe fn transpose(v: &mut [__m256i; 8]) {
        unsafe {
            let ab_0145 = _mm256_unpacklo_epi32(v[0], v[1]);
            let ab_2367 = _mm256_unpackhi_epi32(v[0], v[1]);
            let cd_0145 = _mm256_unpacklo_epi32(v[2], v[3]);
            let cd_2367 = _mm256_unpackhi_epi32(v[2], v[3]);
            let ef_0145 = _mm256_unpacklo_epi32(v[4], v[5]);
            let ef_2367 = _mm256_unpackhi_epi32(v[4], v[5]);
            let gh_0145 = _mm256_unpacklo_epi32(v[6], v[7]);
            let gh_2367 = _mm256_unpackhi_epi32(v[6], v[7]);
            let abcd_04 = _mm256_unpacklo_epi64(ab_0145, cd_0145);
            let abcd_15 = _mm256_unpackhi_epi64(ab_0145, cd_0145);
            let abcd_26 = _mm256_unpacklo_epi64(ab_2367, cd_2367);
            let abcd_37 = _mm256_unpackhi_epi64(ab_2367, cd_2367);
            let efgh_04 = _mm256_unpacklo_epi64(ef_0145, gh_0145);
            let efgh_15 = _mm256_unpackhi_epi64(ef_0145, gh_0145);
            let efgh_26 = _mm256_unpacklo_epi64(ef_2367, gh_2367);
            let efgh_37 = _mm256_unpackhi_epi64(ef_2367, gh_2367);
            v[0] = _mm256_permute2x128_si256(abcd_04, efgh_04, 0x20);
            v[1] = _mm256_permute2x128_si256(abcd_15, efgh_15, 0x20);
            v[2] = _mm256_permute2x128_si256(abcd_26, efgh_26, 0x20);
            v[3] = _mm256_permute2x128_si256(abcd_37, efgh_37, 0x20);
            v[4] = _mm256_permute2x128_si256(abcd_04, efgh_04, 0x31);
            v[5] = _mm256_permute2x128_si256(abcd_15, efgh_15, 0x31);
            v[6] = _mm256_permute2x128_si256(abcd_26, efgh_26, 0x31);
            v[7] = _mm256_permute2x128_si256(abcd_37, efgh_37, 0x31);
        }
    }

    macro_rules! rotr {
        ($x:expr, $n:literal) => {
            _mm256_or_si256(_mm256_srli_epi32($x, $n), _mm256_slli_epi32($x, 32 - $n))
        };
    }

    /// Eight keyed hashes at once: the inputs are `item_len` bytes each,
    /// whole blocks and a chunk at most, one after another from `input`.
    pub unsafe fn hash8(key: &[u32; 8], input: *const u8, item_len: usize, out: &mut [[u8; OUT_LEN]]) {
        unsafe {
            let n = item_len / BLOCK_LEN;
            let mut h: [__m256i; 8] = std::array::from_fn(|i| _mm256_set1_epi32(key[i] as i32));
            for blk in 0..n {
                let at =
                    |j: usize, half: usize| input.add(j * item_len + blk * BLOCK_LEN + 32 * half) as *const __m256i;
                let mut lo: [__m256i; 8] = std::array::from_fn(|j| _mm256_loadu_si256(at(j, 0)));
                let mut hi: [__m256i; 8] = std::array::from_fn(|j| _mm256_loadu_si256(at(j, 1)));
                transpose(&mut lo);
                transpose(&mut hi);
                let m: [__m256i; 16] = std::array::from_fn(|i| if i < 8 { lo[i] } else { hi[i - 8] });
                let mut flags = KEYED_HASH;
                if blk == 0 {
                    flags |= CHUNK_START;
                }
                if blk == n - 1 {
                    flags |= CHUNK_END | ROOT;
                }
                let mut v: [__m256i; 16] = std::array::from_fn(|i| match i {
                    0..8 => h[i],
                    8..12 => _mm256_set1_epi32(IV[i - 8] as i32),
                    12 | 13 => _mm256_setzero_si256(),
                    14 => _mm256_set1_epi32(BLOCK_LEN as i32),
                    _ => _mm256_set1_epi32(flags as i32),
                });
                for s in &SCHEDULE {
                    for (q, [a, b, c, d]) in QUARTERS.iter().copied().enumerate() {
                        v[a] = _mm256_add_epi32(_mm256_add_epi32(v[a], v[b]), m[s[2 * q]]);
                        v[d] = rotr!(_mm256_xor_si256(v[d], v[a]), 16);
                        v[c] = _mm256_add_epi32(v[c], v[d]);
                        v[b] = rotr!(_mm256_xor_si256(v[b], v[c]), 12);
                        v[a] = _mm256_add_epi32(_mm256_add_epi32(v[a], v[b]), m[s[2 * q + 1]]);
                        v[d] = rotr!(_mm256_xor_si256(v[d], v[a]), 8);
                        v[c] = _mm256_add_epi32(v[c], v[d]);
                        v[b] = rotr!(_mm256_xor_si256(v[b], v[c]), 7);
                    }
                }
                for i in 0..8 {
                    h[i] = _mm256_xor_si256(v[i], v[i + 8]);
                }
            }
            transpose(&mut h);
            for (j, o) in out.iter_mut().enumerate() {
                _mm256_storeu_si256(o.as_mut_ptr() as *mut __m256i, h[j]);
            }
        }
    }
}

#[cfg(test)]
#[path = "tests/blake3_vectors.rs"]
mod vectors;

#[cfg(test)]
mod tests {
    use super::*;

    fn hex(d: &[u8]) -> String {
        d.iter().map(|b| format!("{b:02x}")).collect()
    }

    #[test]
    fn the_official_vectors() {
        assert_eq!(vectors::CASES.len(), 35);
        for (len, hash_hex, keyed_hex, derived_hex) in vectors::CASES {
            let input: Vec<u8> = (0..*len).map(|i| (i % 251) as u8).collect();
            assert_eq!(hex(&hash(&input)), *hash_hex, "hash of {len} bytes");
            assert_eq!(hex(&keyed_hash(vectors::KEY, &input)), *keyed_hex, "keyed hash of {len} bytes");
            assert_eq!(hex(&derive_key(vectors::CONTEXT, &input)), *derived_hex, "derived key of {len} bytes");
        }
    }

    #[test]
    fn known_answers() {
        assert_eq!(hex(&hash(b"")), "af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262");
        assert_eq!(hex(&hash(b"abc")), "6437b3ac38465133ffb63b75273a8db548c558465d79db03fd359c6cd5bd9d85");
    }

    #[test]
    fn many_at_once_is_one_at_a_time() {
        let key: [u32; 8] = std::array::from_fn(|i| 0x9E3779B9u32.wrapping_mul(i as u32 + 1));
        for item_len in [64, 128, 256, 1024, 32, 100, 1] {
            let n = 21;
            let input: Vec<u8> = (0..item_len * n).map(|i| (i * 7 + i / 251) as u8).collect();
            let mut out = vec![[0u8; 32]; n];
            keyed_hash_many(&key, &input, item_len, &mut out);
            for (i, o) in out.iter().enumerate() {
                let one = keyed_hash_words(&key, &input[i * item_len..(i + 1) * item_len]);
                assert_eq!(*o, one, "length {item_len}, item {i}");
            }
        }
    }

    #[test]
    fn compressions_are_counted() {
        for (len, n) in [(0, 1), (1, 1), (64, 1), (65, 2), (1024, 16), (1025, 18), (2048, 33), (2049, 35)] {
            assert_eq!(compressions(len), n, "{len} bytes");
        }
    }
}
