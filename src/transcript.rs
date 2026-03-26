//! Fiat-Shamir transcript for non-interactive proofs.
//!
//! Maintains a running SHA-256 state. Absorbing data binds the challenge
//! to all prior messages; squeezing derives a pseudorandom field element
//! or index from the current state.

use sha2::{Sha256, Digest};
use ark_ff::{BigInteger, PrimeField};

pub struct Transcript {
    state: Vec<u8>,
}

impl Transcript {
    /// Initialise transcript with `state = SHA256(label)`.
    pub fn new(label: &[u8]) -> Self {
        Self { state: Sha256::digest(label).to_vec() }
    }

    /// Absorb arbitrary bytes: `state = SHA256(state || label || data)`.
    pub fn absorb_bytes(&mut self, label: &[u8], data: &[u8]) {
        let mut h = Sha256::new();
        h.update(&self.state);
        h.update(label);
        h.update(data);
        self.state = h.finalize().to_vec();
    }

    /// Absorb a prime-field element (serialised as little-endian bytes).
    pub fn absorb_field<F: PrimeField>(&mut self, label: &[u8], val: &F) {
        let bytes = val.into_bigint().to_bytes_le();
        self.absorb_bytes(label, &bytes);
    }

    /// Squeeze a field challenge: advances state and maps it to `F`.
    ///
    /// `state = SHA256(state || label || "squeeze")`
    /// Returns `F::from_le_bytes_mod_order(&new_state)`.
    pub fn squeeze_field<F: PrimeField>(&mut self, label: &[u8]) -> F {
        let mut h = Sha256::new();
        h.update(&self.state);
        h.update(label);
        h.update(b"squeeze");
        self.state = h.finalize().to_vec();
        F::from_le_bytes_mod_order(&self.state)
    }

    /// Squeeze a deterministic index in `0..n`.
    ///
    /// `state = SHA256(state || label || "index")`
    /// Returns `u64::from_le_bytes(state[..8]) % n`.
    pub fn squeeze_index(&mut self, label: &[u8], n: usize) -> usize {
        assert!(n > 0, "squeeze_index: n must be > 0");
        let mut h = Sha256::new();
        h.update(&self.state);
        h.update(label);
        h.update(b"index");
        self.state = h.finalize().to_vec();
        let mut bytes = [0u8; 8];
        bytes.copy_from_slice(&self.state[..8]);
        (u64::from_le_bytes(bytes) as usize) % n
    }
}

// ── Tests ──────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use ark_bls12_381::Fr as Fp;

    #[test]
    fn test_transcript_deterministic() {
        // Same absorb sequence → same squeeze output
        let make = || {
            let mut t = Transcript::new(b"test");
            t.absorb_bytes(b"msg", b"hello");
            t.squeeze_field::<Fp>(b"challenge")
        };
        assert_eq!(make(), make());
    }

    #[test]
    fn test_transcript_different_labels() {
        // Same data but different squeeze labels → different challenges
        let squeeze = |lbl: &[u8]| {
            let mut t = Transcript::new(b"test");
            t.absorb_bytes(b"msg", b"data");
            t.squeeze_field::<Fp>(lbl)
        };
        assert_ne!(squeeze(b"challenge_A"), squeeze(b"challenge_B"));
    }

    #[test]
    fn test_squeeze_index_in_range() {
        let mut t = Transcript::new(b"test");
        for n in [1usize, 2, 7, 16, 100, 1000] {
            for seed in 0u8..20 {
                t.absorb_bytes(b"rnd", &[seed]);
                let idx = t.squeeze_index(b"query", n);
                assert!(idx < n, "squeeze_index({n}) returned {idx}");
            }
        }
    }
}
