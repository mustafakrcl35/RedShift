//! Polynomial utilities for the RedShift protocol.
//!
//! - `fri_fold_coeffs`       — FRI folding on coefficient vectors (kept for compatibility)
//! - `fri_fold_evaluations`  — FRI folding on evaluation tables (the real FRI step)
//! - `evaluate_on_domain`    — Horner evaluation at a set of points
//! - `vanishing_poly`        — Z_H(X) = ∏(X - d) for d ∈ domain
//!
//! All functions are generic over `F: Field` (arkworks).

use ark_ff::Field;

// TODO: implement quotient polynomial (f − g) / Z_H using ark-poly DensePolynomial

// ── Coefficient-based helpers ─────────────────────────────────────────────────

/// FRI folding step on **coefficient vectors** (pedagogical / unit-test helper).
///
/// Split `f(X) = f_even(X²) + X · f_odd(X²)` and combine:
/// `f'(X) = f_even(X) + α · f_odd(X)`.
///
/// Output length: `⌈n/2⌉`.
///
/// > In production FRI the prover works with *evaluations*, not coefficients —
/// > see [`fri_fold_evaluations`].
///
/// # Panics
/// Panics if `coeffs` is empty.
pub fn fri_fold_coeffs<F: Field>(coeffs: &[F], alpha: F) -> Vec<F> {
    assert!(!coeffs.is_empty(), "fri_fold_coeffs: empty coefficient vector");

    let n = coeffs.len();
    let half = (n + 1) / 2; // ⌈n/2⌉

    (0..half)
        .map(|i| {
            let even = coeffs[2 * i];
            let odd = if 2 * i + 1 < n { coeffs[2 * i + 1] } else { F::zero() };
            even + alpha * odd
        })
        .collect()
}

/// FRI folding step on **evaluation tables** — the real FRI round.
///
/// Given evaluations of `f` over a multiplicative subgroup
/// `D = {ω⁰, ω¹, ..., ω^(n-1)}` (size `n`, `n` even), produce evaluations
/// of the folded polynomial `f₁` over the halved subgroup
/// `D' = {ω⁰, ω², ..., ω^(n-2)}` (size `n/2`).
///
/// # Folding formula
///
/// Pairs `(xᵢ, −xᵢ)` for `i = 0, ..., n/2 − 1` where `−xᵢ = domain[i + n/2]`
/// (true for any multiplicative subgroup because `ω^(n/2) = −1`):
///
/// ```text
/// f₁(xᵢ²) = (f(xᵢ) + f(−xᵢ)) / 2  +  α · (f(xᵢ) − f(−xᵢ)) / (2·xᵢ)
/// ```
///
/// - The `(f + f̄) / 2` part extracts the even part of `f`.
/// - The `α · (f − f̄) / (2x)` part folds in the odd part with challenge `α`.
///
/// One fold halves the degree: if `f` has degree `< d`, then `f₁` has degree
/// `< d/2`.  After `log₂(d)` rounds, the remaining polynomial is constant
/// (degree 0), which the verifier can check cheaply.
///
/// # Panics
/// Panics if `evaluations.len() != domain.len()`, `n < 2`, or `n` is odd.
pub fn fri_fold_evaluations<F: Field>(evaluations: &[F], domain: &[F], alpha: F) -> Vec<F> {
    let n = evaluations.len();
    assert_eq!(n, domain.len(), "evaluations and domain must have the same length");
    assert!(n >= 2 && n % 2 == 0, "domain size must be even and ≥ 2 (got {n})");

    let half = n / 2;
    // 2⁻¹ in the field (char > 2 for all supported curves)
    let two_inv = F::from(2u64)
        .inverse()
        .expect("field characteristic must be > 2");

    (0..half)
        .map(|i| {
            // xᵢ = domain[i],  −xᵢ = domain[i + half]  (ω^(n/2) = −1)
            let f_pos = evaluations[i];           // f(xᵢ)
            let f_neg = evaluations[i + half];    // f(−xᵢ)
            let x_inv = domain[i]
                .inverse()
                .expect("domain elements must be nonzero");

            // f₁(xᵢ²) = (f_pos + f_neg + α · (f_pos − f_neg) · xᵢ⁻¹) / 2
            (f_pos + f_neg + alpha * (f_pos - f_neg) * x_inv) * two_inv
        })
        .collect()
}

/// Evaluate a polynomial (coefficient vector) at each point in `domain`.
///
/// Uses Horner's method: `f(x) = c₀ + x·(c₁ + x·(c₂ + …))`.
/// Returns a vector of length `domain.len()`.
pub fn evaluate_on_domain<F: Field>(coeffs: &[F], domain: &[F]) -> Vec<F> {
    domain.iter().map(|&x| horner(coeffs, x)).collect()
}

/// Compute the vanishing polynomial `Z_H(X) = ∏_{d ∈ domain} (X − d)`.
///
/// Returns coefficients in ascending order: `[c₀, c₁, ..., cₙ]`.
pub fn vanishing_poly<F: Field>(domain: &[F]) -> Vec<F> {
    let mut result = vec![F::one()]; // start with polynomial "1"

    for &d in domain {
        // Multiply by (X − d)
        let mut next = vec![F::zero(); result.len() + 1];
        for (i, &c) in result.iter().enumerate() {
            next[i + 1] += c;   //  c · X
            next[i] -= c * d;   //  c · (−d)
        }
        result = next;
    }
    result
}

/// Horner's method evaluation at a single point.
/// `coeffs[0]` is the constant term; `coeffs[n-1]` is the leading coefficient.
fn horner<F: Field>(coeffs: &[F], x: F) -> F {
    coeffs.iter().rev().fold(F::zero(), |acc, &c| acc * x + c)
}

// ── Tests ─────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use ark_bls12_381::Fr as Fp;
    use ark_ff::One;
    use ark_poly::{EvaluationDomain, Radix2EvaluationDomain};
    use crate::domain::multiplicative_subgroup;

    // ── fri_fold_coeffs (coefficient-based, renamed from fri_fold) ────────────

    #[test]
    fn fri_fold_coeffs_halves_even_length() {
        let coeffs: Vec<Fp> = vec![1, 2, 3, 4].into_iter().map(Fp::from).collect();
        let folded = fri_fold_coeffs(&coeffs, Fp::from(5u64));
        assert_eq!(folded.len(), 2);
    }

    #[test]
    fn fri_fold_coeffs_halves_odd_length() {
        let coeffs: Vec<Fp> = (1u64..=5).map(Fp::from).collect();
        let folded = fri_fold_coeffs(&coeffs, Fp::from(7u64));
        assert_eq!(folded.len(), 3); // ⌈5/2⌉ = 3
    }

    #[test]
    fn fri_fold_coeffs_correct_values() {
        // coeffs = [1, 2, 3, 4], α = 0 → even = [1, 3]
        let coeffs: Vec<Fp> = vec![1, 2, 3, 4].into_iter().map(Fp::from).collect();
        let f0 = fri_fold_coeffs(&coeffs, Fp::from(0u64));
        assert_eq!(f0, vec![Fp::from(1u64), Fp::from(3u64)]);

        // α = 1 → even + odd = [1+2, 3+4] = [3, 7]
        let f1 = fri_fold_coeffs(&coeffs, Fp::from(1u64));
        assert_eq!(f1, vec![Fp::from(3u64), Fp::from(7u64)]);
    }

    #[test]
    fn fri_fold_coeffs_single_element() {
        let folded = fri_fold_coeffs(&[Fp::from(42u64)], Fp::from(99u64));
        assert_eq!(folded, vec![Fp::from(42u64)]);
    }

    // ── fri_fold_evaluations (evaluation-based, the real FRI step) ────────────

    #[test]
    fn test_fri_fold_eval_length() {
        // n = 8 → output length 4
        let domain = multiplicative_subgroup::<Fp>(3); // 8 elements
        let evals = vec![Fp::from(1u64); 8];
        let folded = fri_fold_evaluations(&evals, &domain, Fp::from(5u64));
        assert_eq!(folded.len(), 4, "output must have n/2 elements");
    }

    #[test]
    fn test_fri_fold_eval_low_degree() {
        // f(x) = x  (degree 1).  After one FRI fold with challenge α,
        // f₁ must be the constant polynomial α.
        //
        // Proof sketch: f_even(X²) = 0, f_odd(X²) = 1 for f(x) = x.
        // f₁(X²) = f_even(X²) + α·f_odd(X²) = 0 + α·1 = α.
        let domain = multiplicative_subgroup::<Fp>(2); // {1, ω, ω²=-1, ω³=-ω}
        let evals = domain.clone();                    // f(x) = x → eval = domain
        let alpha = Fp::from(7u64);

        let folded = fri_fold_evaluations(&evals, &domain, alpha);

        assert_eq!(folded.len(), 2);
        for (i, &v) in folded.iter().enumerate() {
            assert_eq!(v, alpha, "fold of f(x)=x must be constant α at index {i}");
        }
    }

    #[test]
    fn test_fri_fold_eval_constant_poly() {
        // f(x) = c (constant).  Folding a constant preserves it regardless of α:
        //   f_pos = f_neg = c → f_plus = 2c, f_minus = 0
        //   result = 2c / 2 = c
        let domain = multiplicative_subgroup::<Fp>(3); // 8 elements
        let c = Fp::from(13u64);
        let evals = vec![c; 8];
        let alpha = Fp::from(42u64);

        let folded = fri_fold_evaluations(&evals, &domain, alpha);

        assert_eq!(folded.len(), 4);
        for (i, &v) in folded.iter().enumerate() {
            assert_eq!(v, c, "constant polynomial must fold to itself at index {i}");
        }
    }

    #[test]
    fn test_fri_fold_eval_consistency() {
        // Evaluate a degree-3 polynomial, fold once, verify output length halves
        // and round-trips: re-evaluate a polynomial with the folded coefficients
        // and compare against the directly folded evaluations.
        //
        // f(x) = 1 + 2x + 3x² + 4x³
        let coeffs = vec![Fp::from(1u64), Fp::from(2u64), Fp::from(3u64), Fp::from(4u64)];
        let domain = multiplicative_subgroup::<Fp>(3); // 8-element domain
        let evals = evaluate_on_domain(&coeffs, &domain);
        let alpha = Fp::from(5u64);

        let folded = fri_fold_evaluations(&evals, &domain, alpha);
        assert_eq!(folded.len(), 4);

        // The folded polynomial's coefficients (conceptually) can be derived:
        // f_even coeffs = [1, 3],  f_odd coeffs = [2, 4]
        // folded poly = f_even + α * f_odd = [1 + 5*2, 3 + 5*4] = [11, 23]
        let expected_folded_coeffs = vec![Fp::from(11u64), Fp::from(23u64)];
        // Halved domain: {ω⁰, ω², ω⁴, ω⁶} = first 4 even-indexed elements squared
        let half_domain: Vec<Fp> = domain.iter().take(4).map(|&x| x * x).collect();
        let expected_evals = evaluate_on_domain(&expected_folded_coeffs, &half_domain);

        assert_eq!(folded, expected_evals, "folded evaluations must match re-evaluated folded polynomial");
    }

    // ── evaluate_on_domain ────────────────────────────────────────────────────

    #[test]
    fn evaluate_constant_poly() {
        let coeffs = vec![Fp::from(7u64)];
        let domain = Radix2EvaluationDomain::<Fp>::new(4).unwrap();
        let points: Vec<Fp> = domain.elements().collect();
        let evals = evaluate_on_domain(&coeffs, &points);
        assert!(evals.iter().all(|&v| v == Fp::from(7u64)));
    }

    #[test]
    fn evaluate_linear_poly() {
        // f(x) = 2 + 3x → f(1) = 5
        let coeffs = vec![Fp::from(2u64), Fp::from(3u64)];
        let evals = evaluate_on_domain(&coeffs, &[Fp::from(1u64)]);
        assert_eq!(evals[0], Fp::from(5u64));
    }

    #[test]
    fn evaluate_on_domain_length_matches() {
        let coeffs: Vec<Fp> = (0u64..6).map(Fp::from).collect();
        let domain = Radix2EvaluationDomain::<Fp>::new(8).unwrap();
        let points: Vec<Fp> = domain.elements().collect();
        assert_eq!(evaluate_on_domain(&coeffs, &points).len(), points.len());
    }

    // ── vanishing_poly ────────────────────────────────────────────────────────

    #[test]
    fn vanishing_poly_degree() {
        let domain = Radix2EvaluationDomain::<Fp>::new(4).unwrap();
        let points: Vec<Fp> = domain.elements().collect();
        assert_eq!(vanishing_poly(&points).len(), 5); // degree 4 → 5 coefficients
    }

    #[test]
    fn vanishing_poly_roots_vanish() {
        let domain = Radix2EvaluationDomain::<Fp>::new(4).unwrap();
        let points: Vec<Fp> = domain.elements().collect();
        let z = vanishing_poly(&points);
        for &d in &points {
            assert_eq!(horner(&z, d), Fp::from(0u64));
        }
    }

    #[test]
    fn vanishing_poly_nonzero_outside() {
        let domain = Radix2EvaluationDomain::<Fp>::new(4).unwrap();
        let points: Vec<Fp> = domain.elements().collect();
        let z = vanishing_poly(&points);
        assert_ne!(horner(&z, Fp::from(2u64)), Fp::from(0u64));
    }

    #[test]
    fn vanishing_poly_leading_coeff_is_one() {
        let domain = Radix2EvaluationDomain::<Fp>::new(4).unwrap();
        let points: Vec<Fp> = domain.elements().collect();
        let z = vanishing_poly(&points);
        assert_eq!(*z.last().unwrap(), Fp::one());
    }
}
