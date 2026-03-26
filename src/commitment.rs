//! Mock KZG polynomial commitment scheme for the RedShift protocol.
//!
//! This is a **field-arithmetic mock** of KZG (Kate–Zaverucha–Goldberg).
//! Real KZG works over elliptic-curve groups with bilinear pairings:
//!
//! ```text
//! commit(f) = [f(τ)]₁          (G1 point)
//! open(f,z) = [(f(τ)-f(z))/(τ-z)]₁  (G1 point)
//! verify:  e(C - [y]₁, [1]₂) = e(π, [τ-z]₂)
//! ```
//!
//! Here we replace all G1/G2 group operations with plain field multiplications,
//! so every "commitment" and "proof" is just a field element `F`.  The verify
//! equation becomes the algebraic identity that underlies the real pairing check:
//!
//! ```text
//! proof * (τ − z) + y == commitment
//! ```
//!
//! This lets us test the full commit/open/verify flow in the scalar field today;
//! swapping in real `ark-ec` group operations later requires only changing the
//! three primitive operations (commit, open, verify) — the rest of the protocol
//! is identical.

use ark_ff::Field;
use crate::polynomial::evaluate_on_domain;

// ── Structs ──────────────────────────────────────────────────────────────────

/// Structured Reference String (SRS): `[τ⁰, τ¹, ..., τ^d]` in the scalar field.
///
/// In real KZG these would be elliptic-curve points `[τ^i]₁`.
pub struct CommitmentKey<F: Field> {
    pub powers: Vec<F>,
}

/// A commitment to a polynomial — here just `f(τ)` as a field element.
#[derive(Debug, PartialEq)]
pub struct Commitment<F: Field> {
    pub value: F,
}

/// An opening proof — here just `q(τ)` as a field element, where
/// `q(x) = (f(x) − f(z)) / (x − z)` is the quotient polynomial.
#[derive(Debug, PartialEq)]
pub struct OpeningProof<F: Field> {
    pub value: F,
}

// ── Public API ────────────────────────────────────────────────────────────────

/// Generate the SRS: `powers = [1, τ, τ², ..., τ^max_degree]`.
pub fn setup<F: Field>(max_degree: usize, tau: F) -> CommitmentKey<F> {
    let mut powers = Vec::with_capacity(max_degree + 1);
    let mut current = F::one();
    for _ in 0..=max_degree {
        powers.push(current);
        current *= tau;
    }
    CommitmentKey { powers }
}

/// Commit to a polynomial: `com(f) = Σ coeffs[i] · powers[i]`.
///
/// # Panics
/// Panics if `poly_coeffs.len() > ck.powers.len()`.
pub fn commit<F: Field>(poly_coeffs: &[F], ck: &CommitmentKey<F>) -> Commitment<F> {
    assert!(
        poly_coeffs.len() <= ck.powers.len(),
        "polynomial degree ({}) exceeds SRS capacity ({})",
        poly_coeffs.len().saturating_sub(1),
        ck.powers.len().saturating_sub(1),
    );
    let value = poly_coeffs
        .iter()
        .zip(ck.powers.iter())
        .fold(F::zero(), |acc, (&c, &p)| acc + c * p);
    Commitment { value }
}

/// Open the commitment at `point`:
/// 1. Evaluate `f(point)` via Horner.
/// 2. Compute the quotient `q(x) = (f(x) − f(point)) / (x − point)` via
///    Ruffini's rule (synthetic division).
/// 3. Commit to `q` to produce the proof.
///
/// Returns `(f(point), OpeningProof)`.
pub fn open<F: Field>(
    poly_coeffs: &[F],
    point: F,
    ck: &CommitmentKey<F>,
) -> (F, OpeningProof<F>) {
    let value = evaluate_on_domain(poly_coeffs, &[point])[0];
    let quotient = compute_quotient(poly_coeffs, point);
    let proof_commit = commit(&quotient, ck);
    (value, OpeningProof { value: proof_commit.value })
}

/// Verify an opening:
///
/// ```text
/// proof.value · (τ − point) + value == commitment.value
/// ```
///
/// where `τ = ck.powers[1]`.  This is the field-arithmetic analogue of the
/// KZG pairing equation.
///
/// # Panics
/// Panics if the SRS has fewer than 2 powers (need at least `τ¹`).
pub fn verify<F: Field>(
    commitment: &Commitment<F>,
    point: F,
    value: F,
    proof: &OpeningProof<F>,
    ck: &CommitmentKey<F>,
) -> bool {
    assert!(
        ck.powers.len() >= 2,
        "SRS must contain at least τ¹ for verification"
    );
    let tau = ck.powers[1];
    proof.value * (tau - point) + value == commitment.value
}

// ── Private helpers ───────────────────────────────────────────────────────────

/// Ruffini's rule (synthetic division):
/// compute `q(x) = (f(x) − f(z)) / (x − z)`.
///
/// `coeffs` are in **ascending** order (`coeffs[i]` = coefficient of `xⁱ`).
/// Returns quotient coefficients in ascending order.
///
/// Algorithm (descending pass):
/// ```text
/// b[0] = c_n                         (leading coeff)
/// b[k] = c_{n-k} + z · b[k-1]       (for k = 1 … n)
/// b[n] = f(z)                        (remainder, discarded)
/// quotient (descending) = b[0..n-1]
/// ```
fn compute_quotient<F: Field>(coeffs: &[F], point: F) -> Vec<F> {
    let n = coeffs.len();
    if n <= 1 {
        // constant or empty polynomial — quotient is zero
        return vec![];
    }
    let mut b = vec![F::zero(); n];
    b[0] = *coeffs.last().unwrap(); // c_n
    for i in 1..n {
        b[i] = coeffs[n - 1 - i] + point * b[i - 1];
    }
    // b[0..n-1] = quotient in descending order; b[n-1] = f(z) (remainder)
    let mut quotient = b[..n - 1].to_vec();
    quotient.reverse(); // convert to ascending order
    quotient
}

// ── Tests ─────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use ark_bls12_381::Fr as Fp;

    // helper: build a deterministic SRS with tau = 7
    fn ck(max_degree: usize) -> CommitmentKey<Fp> {
        setup(max_degree, Fp::from(7u64))
    }

    // ── setup ────────────────────────────────────────────────────────────────

    #[test]
    fn test_setup_powers() {
        // tau = 3  →  powers = [1, 3, 9, 27, 81]
        let tau = Fp::from(3u64);
        let c = setup(4, tau);
        assert_eq!(c.powers.len(), 5);
        assert_eq!(c.powers[0], Fp::from(1u64));
        assert_eq!(c.powers[1], Fp::from(3u64));
        assert_eq!(c.powers[2], Fp::from(9u64));
        assert_eq!(c.powers[3], Fp::from(27u64));
        assert_eq!(c.powers[4], Fp::from(81u64));
    }

    #[test]
    fn test_setup_degree_zero() {
        let c = setup(0, Fp::from(5u64));
        assert_eq!(c.powers, vec![Fp::from(1u64)]);
    }

    // ── commit ───────────────────────────────────────────────────────────────

    #[test]
    fn test_commit_inner_product() {
        // f(x) = 2 + 3x,  tau = 7
        // com = 2·1 + 3·7 = 2 + 21 = 23
        let coeffs = vec![Fp::from(2u64), Fp::from(3u64)];
        let c = commit(&coeffs, &ck(4));
        assert_eq!(c.value, Fp::from(23u64));
    }

    // ── compute_quotient (internal correctness) ───────────────────────────────

    #[test]
    fn test_quotient_x_squared_minus_one() {
        // f(x) = x² − 1 = [-1, 0, 1] in ascending, z = 1
        // f(1) = 0  →  q(x) = (x²−1)/(x−1) = x + 1 = [1, 1]
        let coeffs = vec![-Fp::from(1u64), Fp::from(0u64), Fp::from(1u64)];
        let q = compute_quotient(&coeffs, Fp::from(1u64));
        assert_eq!(q, vec![Fp::from(1u64), Fp::from(1u64)]);
    }

    #[test]
    fn test_quotient_ascending_order() {
        // f(x) = 1 + 2x + 3x²,  z = 5
        // f(5) = 1 + 10 + 75 = 86
        // q(x) = (3x² + 2x − 85) / (x − 5) = 3x + 17  →  [17, 3]
        let coeffs = vec![Fp::from(1u64), Fp::from(2u64), Fp::from(3u64)];
        let q = compute_quotient(&coeffs, Fp::from(5u64));
        assert_eq!(q, vec![Fp::from(17u64), Fp::from(3u64)]);
    }

    // ── commit / open / verify ────────────────────────────────────────────────

    #[test]
    fn test_commit_open_verify_passes() {
        // f(x) = 1 + 2x + 3x²,  tau = 7,  z = 5
        // f(7) = 1 + 14 + 147 = 162  →  commitment.value = 162
        // f(5) = 86
        // q(x) = 3x + 17,  q(7) = 21 + 17 = 38  →  proof.value = 38
        // verify: 38·(7−5) + 86 = 76 + 86 = 162 ✓
        let coeffs = vec![Fp::from(1u64), Fp::from(2u64), Fp::from(3u64)];
        let ck = ck(4);
        let commitment = commit(&coeffs, &ck);

        assert_eq!(commitment.value, Fp::from(162u64));

        let point = Fp::from(5u64);
        let (value, proof) = open(&coeffs, point, &ck);

        assert_eq!(value, Fp::from(86u64));
        assert_eq!(proof.value, Fp::from(38u64));
        assert!(verify(&commitment, point, value, &proof, &ck));
    }

    #[test]
    fn test_verify_wrong_value_fails() {
        let coeffs = vec![Fp::from(1u64), Fp::from(2u64), Fp::from(3u64)];
        let ck = ck(4);
        let commitment = commit(&coeffs, &ck);
        let point = Fp::from(5u64);
        let (correct_value, proof) = open(&coeffs, point, &ck);

        let wrong_value = correct_value + Fp::from(1u64);
        assert!(!verify(&commitment, point, wrong_value, &proof, &ck));
    }

    #[test]
    fn test_verify_wrong_point_fails() {
        // Open at z=5, then verify claims it was opened at z=6
        let coeffs = vec![Fp::from(1u64), Fp::from(2u64), Fp::from(3u64)];
        let ck = ck(4);
        let commitment = commit(&coeffs, &ck);
        let (value, proof) = open(&coeffs, Fp::from(5u64), &ck);

        // Present the proof under a different point
        assert!(!verify(&commitment, Fp::from(6u64), value, &proof, &ck));
    }

    #[test]
    fn test_constant_polynomial() {
        // f(x) = 42,  quotient is zero → proof.value = 0
        let coeffs = vec![Fp::from(42u64)];
        let ck = setup(4, Fp::from(7u64));
        let commitment = commit(&coeffs, &ck);
        let (value, proof) = open(&coeffs, Fp::from(99u64), &ck);
        assert_eq!(value, Fp::from(42u64));
        assert_eq!(proof.value, Fp::from(0u64));
        assert!(verify(&commitment, Fp::from(99u64), value, &proof, &ck));
    }
}
