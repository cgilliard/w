//! Fiat-Shamir: a proof's transcript, as a chain of hashes.
//!
//! The transcript is a 32-byte state. Every step replaces it with the
//! hash of the state and the step's data, in the domain of the kind of
//! step it is ([`crate::hash`]):
//!
//! | step | data | gives |
//! |---|---|---|
//! | absorb | up to 992 bytes of what the prover sent | |
//! | challenge | none | the new state, as a challenge |
//! | grind | a nonce of 8 bytes | accepted if the new state ends in enough zero bits |
//!
//! A challenge is the state the step leaves, so it depends on everything
//! before it, and the step after starts from it.
//!
//! # For a circuit
//!
//! Every step's input begins with the output of the step before: a
//! verifier in a circuit replays a transcript as rows that each take the
//! last row's output ([`crate::recursion`]), and nothing else has to be
//! carried. The kind of step is the key the hash starts from, which a
//! row's program gives, so the input is the state and the data and
//! nothing between them: the state is half a block, and data that is
//! field elements or digests lies on the words of the blocks, an element
//! four words. Two elements absorbed are one compression; a challenge is
//! one; a digest is one.
//!
//! # Grinding
//!
//! Before a challenge whose soundness error is larger than the security
//! level allows, the prover must find a nonce that makes the next state
//! end in `bits` zero bits ([`Challenger::grind`]). An attempt to steer
//! that challenge then costs `2^bits` hashes more, which takes `bits`
//! off the error ([`crate::pcs`] says where and how many).

use crate::blake3::CHUNK_LEN;
use crate::field::{F, as_bytes};
use crate::hash::{DOM_ABSORB, DOM_CHALLENGE, DOM_GRIND, DOM_TRANSCRIPT, Digest, hash_domain};
use crate::parallel::{par_map_min, threads};

/// Bytes absorbed in one step: with the state, a chunk.
const PIECE: usize = CHUNK_LEN - 32;

/// One step of a transcript, as a recording one keeps it: the domain it
/// was hashed in and its whole input, the state first.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Step {
    pub domain: u32,
    pub input: Vec<u8>,
}

#[derive(Clone)]
pub struct Challenger {
    state: Digest,
    /// Compressions made so far: what a circuit replaying it pays.
    pub compressions: usize,
    /// Every step, in order, if the transcript is a recording one: what
    /// a circuit replaying it hashes.
    pub log: Option<Vec<Step>>,
}

/// The state after a step in `domain` with `data`, from `state`.
fn step(state: &Digest, domain: u32, data: &[u8]) -> Digest {
    let mut buf = [0u8; CHUNK_LEN];
    buf[..32].copy_from_slice(state);
    buf[32..32 + data.len()].copy_from_slice(data);
    hash_domain(domain, &buf[..32 + data.len()])
}

/// Whether a state ends in `bits` zero bits: its first eight bytes, as a
/// little-endian number, are a multiple of `2^bits`.
fn ground(state: &Digest, bits: usize) -> bool {
    u64::from_le_bytes(state[..8].try_into().unwrap()).trailing_zeros() as usize >= bits
}

impl Challenger {
    /// A transcript of the protocol `label` names.
    pub fn new(label: &[u8]) -> Challenger {
        Challenger { state: hash_domain(DOM_TRANSCRIPT, label), compressions: 0, log: None }
    }

    /// The same transcript, keeping every step ([`Challenger::log`]).
    pub fn recording(label: &[u8]) -> Challenger {
        Challenger { log: Some(Vec::new()), ..Challenger::new(label) }
    }

    fn step(&mut self, domain: u32, data: &[u8]) {
        self.compressions += crate::blake3::compressions(32 + data.len());
        if let Some(log) = &mut self.log {
            log.push(Step { domain, input: [&self.state[..], data].concat() });
        }
        self.state = step(&self.state, domain, data);
    }

    pub fn absorb(&mut self, data: &[u8]) {
        for piece in data.chunks(PIECE) {
            self.step(DOM_ABSORB, piece);
        }
    }

    /// Field elements, as their bytes in one run.
    pub fn absorb_fs(&mut self, xs: &[F]) {
        self.absorb(&as_bytes(xs));
    }

    pub fn challenge(&mut self) -> F {
        self.step(DOM_CHALLENGE, &[]);
        F::from_bytes(self.state[..16].try_into().unwrap())
    }

    /// An index below `2^bits`, `bits` at most 31.
    pub fn index(&mut self, bits: usize) -> usize {
        self.index_and_low(bits).0
    }

    /// [`Challenger::index`], and the low 31 bits of the state it is the
    /// low bits of: what a circuit reads the index from.
    pub fn index_and_low(&mut self, bits: usize) -> (usize, u32) {
        assert!(bits <= 31);
        self.step(DOM_CHALLENGE, &[]);
        let low = u32::from_le_bytes(self.state[..4].try_into().unwrap()) & 0x7FFF_FFFF;
        ((low & ((1u32 << bits) - 1)) as usize, low)
    }

    /// The smallest nonce that grinds `bits` bits, taken into the
    /// transcript. With no bits to grind nothing is hashed and the nonce
    /// is zero.
    pub fn grind(&mut self, bits: usize) -> u64 {
        if bits == 0 {
            return 0;
        }
        self.grind_from(bits, 0)
    }

    /// The smallest nonce not below `from` that grinds `bits` bits, one
    /// at least: for a prover that chooses among nonces.
    pub fn grind_from(&mut self, bits: usize, from: u64) -> u64 {
        assert!(bits > 0 && bits < 64);
        const BATCH: u64 = 1 << 12;
        let state = self.state;
        let lanes = threads() as u64;
        let mut base = from;
        let nonce = loop {
            // Each lane tries a batch; the smallest hit of the round wins,
            // so the nonce does not depend on how many lanes there are.
            let hits = par_map_min(lanes as usize, 1, |lane| {
                let from = base + lane as u64 * BATCH;
                (from..from + BATCH).find(|n| ground(&step(&state, DOM_GRIND, &n.to_le_bytes()), bits))
            });
            if let Some(n) = hits.into_iter().flatten().min() {
                break n;
            }
            base += lanes * BATCH;
        };
        assert!(self.check_grind(bits, nonce));
        nonce
    }

    /// The verifier's side of [`Challenger::grind`]: takes the nonce into
    /// the transcript and says whether it grinds `bits` bits.
    pub fn check_grind(&mut self, bits: usize, nonce: u64) -> bool {
        if bits == 0 {
            return nonce == 0;
        }
        self.step(DOM_GRIND, &nonce.to_le_bytes());
        ground(&self.state, bits)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_challenge_depends_on_everything_before_it() {
        let run = |label: &[u8], data: &[&[u8]]| {
            let mut c = Challenger::new(label);
            for d in data {
                c.absorb(d);
            }
            c.challenge()
        };
        let base = run(b"t", &[b"abc", b"def"]);
        assert_eq!(base, run(b"t", &[b"abc", b"def"]));
        assert_ne!(base, run(b"u", &[b"abc", b"def"]));
        assert_ne!(base, run(b"t", &[b"abd", b"def"]));
        assert_ne!(base, run(b"t", &[b"abc", b"dee"]));
        // Where one absorb ends and the next begins is part of it.
        assert_ne!(base, run(b"t", &[b"abcdef"]));
        assert_ne!(base, run(b"t", &[b"ab", b"cdef"]));
        // Challenges in a row differ.
        let mut c = Challenger::new(b"t");
        let (x, y) = (c.challenge(), c.challenge());
        assert_ne!(x, y);
    }

    #[test]
    fn a_step_is_a_hash_of_the_state_and_data_in_its_domain() {
        let mut c = Challenger::recording(b"label");
        let start = hash_domain(DOM_TRANSCRIPT, b"label");
        c.absorb(b"xyz");
        let after = hash_domain(DOM_ABSORB, &[&start[..], b"xyz"].concat());
        let last = hash_domain(DOM_CHALLENGE, &after);
        assert_eq!(c.challenge(), F::from_bytes(last[..16].try_into().unwrap()));
        assert_eq!(c.compressions, 2);
        // The same step in another domain is another: nothing absorbed
        // can pass for a challenge, nor a nonce for data.
        assert_ne!(hash_domain(DOM_ABSORB, &after), last);
        let nonce = 5u64.to_le_bytes();
        assert_ne!(step(&last, DOM_GRIND, &nonce), step(&last, DOM_ABSORB, &nonce));
        // What was kept is what was hashed, and a chain.
        let log = c.log.unwrap();
        assert_eq!(log[0], Step { domain: DOM_ABSORB, input: [&start[..], b"xyz"].concat() });
        assert_eq!(log[1], Step { domain: DOM_CHALLENGE, input: after.to_vec() });
        assert_eq!(hash_domain(log[0].domain, &log[0].input)[..], log[1].input[..32]);
    }

    #[test]
    fn elements_lie_on_the_blocks() {
        // Two elements absorbed are one compression, four more a second,
        // and a digest one: the state is half a block.
        let mut c = Challenger::new(b"t");
        c.absorb_fs(&[F(1), F(2)]);
        assert_eq!(c.compressions, 1);
        c.absorb_fs(&[F(1), F(2), F(3), F(4), F(5), F(6)]);
        assert_eq!(c.compressions, 3);
        c.absorb(&[7; 32]);
        assert_eq!(c.compressions, 4);
        c.challenge();
        assert_eq!(c.compressions, 5);
    }

    #[test]
    fn long_data_is_absorbed_in_pieces_of_a_chunk() {
        let data = vec![5u8; 2000];
        let mut c = Challenger::new(b"t");
        c.absorb(&data);
        let mut d = Challenger::new(b"t");
        d.absorb(&data[..992]);
        d.absorb(&data[992..1984]);
        d.absorb(&data[1984..]);
        assert_eq!(c.challenge(), d.challenge());
        assert_eq!(c.compressions, 16 + 16 + 1 + 1);
    }

    #[test]
    fn grinding_is_checked() {
        let mut p = Challenger::new(b"t");
        p.absorb(b"proof");
        let mut v = p.clone();
        let nonce = p.grind(12);
        // The smallest nonce: none below it grinds.
        for n in 0..nonce {
            assert!(!v.clone().check_grind(12, n));
        }
        assert!(v.clone().check_grind(12, nonce));
        assert!(!v.clone().check_grind(40, nonce));
        assert!(v.check_grind(12, nonce));
        assert_eq!(p.challenge(), v.challenge());
        // No bits: nothing is hashed, and only zero is the nonce.
        let before = p.compressions;
        assert_eq!(p.grind(0), 0);
        assert_eq!(p.compressions, before);
        assert!(p.clone().check_grind(0, 0) && !p.clone().check_grind(0, 1));
    }
}
