//! How an address shows that it receives what is sent to it.
//!
//! A datagram says where it came from, and can lie. Were chunks sent to
//! whoever a request claims to be from, a request of a few hundred bytes
//! would send megabytes to an address of its sender's choosing. So the
//! serving side answers a request for chunks only if it carries a token:
//! a number the serving side gave to that address before, in a small
//! datagram of the layer above. Whoever holds it did receive something
//! sent there.
//!
//! The token is a keyed hash of the address under a secret, so nothing
//! is remembered for each address. The secret is replaced from time to
//! time, and the one before it is still honoured: a token lasts between
//! one and two of those times, and an address that was someone's once
//! is not theirs to speak for for good.

use crate::sha256::Sha256;
use std::net::{IpAddr, SocketAddr};

pub struct Tokens {
    now: [u8; 32],
    before: [u8; 32],
}

impl Tokens {
    /// With a secret from the operating system's random source.
    pub fn new(secret: [u8; 32]) -> Tokens {
        Tokens { now: secret, before: secret }
    }

    /// Takes a new secret. Tokens of the one it replaces are honoured
    /// until the next.
    pub fn rotate(&mut self, secret: [u8; 32]) {
        self.before = core::mem::replace(&mut self.now, secret);
    }

    /// The token to give `addr`.
    pub fn issue(&self, addr: &SocketAddr) -> u64 {
        token(&self.now, addr)
    }

    /// Whether `token` was given to `addr`, under this secret or the
    /// one before.
    pub fn check(&self, addr: &SocketAddr, t: u64) -> bool {
        // Both are computed whichever matches.
        let (a, b) = (token(&self.now, addr), token(&self.before, addr));
        (a == t) | (b == t)
    }
}

fn token(secret: &[u8; 32], addr: &SocketAddr) -> u64 {
    let mut h = Sha256::new();
    h.update(secret);
    match addr.ip() {
        IpAddr::V4(ip) => {
            h.update(&[4]);
            h.update(&ip.octets());
        }
        IpAddr::V6(ip) => {
            h.update(&[6]);
            h.update(&ip.octets());
        }
    }
    h.update(&addr.port().to_le_bytes());
    u64::from_le_bytes(h.finish()[..8].try_into().unwrap())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_token_is_its_addresss_and_lasts_one_change_of_secret() {
        let a: SocketAddr = "10.0.0.1:4000".parse().unwrap();
        let other_port: SocketAddr = "10.0.0.1:4001".parse().unwrap();
        let other_host: SocketAddr = "10.0.0.2:4000".parse().unwrap();
        let v6: SocketAddr = "[::ffff:10.0.0.1]:4000".parse().unwrap();
        let mut t = Tokens::new([1; 32]);
        let mine = t.issue(&a);
        assert!(t.check(&a, mine));
        assert_eq!(mine, t.issue(&a));
        for b in [other_port, other_host, v6] {
            assert!(!t.check(&b, mine));
            assert_ne!(t.issue(&b), mine);
        }
        assert!(!t.check(&a, mine ^ 1) && !t.check(&a, 0));
        // Another secret gives other tokens.
        assert_ne!(Tokens::new([2; 32]).issue(&a), mine);
        // Honoured once the secret changes, with the new one; not twice.
        t.rotate([2; 32]);
        let newer = t.issue(&a);
        assert!(t.check(&a, mine) && t.check(&a, newer) && newer != mine);
        t.rotate([3; 32]);
        assert!(!t.check(&a, mine) && t.check(&a, newer));
    }
}
