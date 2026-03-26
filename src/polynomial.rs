//! Polynomial utilities for the RedShift protocol.
//!
//! This module provides helpers on top of `ark-poly` that are used across
//! the prover and verifier:
//!
//! - `fri_fold`            — FRI folding step (even/odd coefficient split + alpha combine)
//! - `evaluate_on_domain`  — evaluate a coefficient vector on an arbitrary set of points
//! - `vanishing_poly`      — compute Z_H(X) = ∏(X - d) for d in domain as a coefficient vector
//!
//! All functions are generic over `F: Field` from the arkworks ecosystem.

use ark_ff::Field;

// TODO: implement quotient polynomial computation (f - g) / Z_H using ark-poly DensePolynomial

/// FRI folding step.
///
/// Given a polynomial `f(X)` represented as coefficient vector `coeffs` of length `n`,
/// split into even and odd parts:
///
/// ```text
/// f(X) = f_even(X²) + X · f_odd(X²)
/// ```
///
/// then combine with challenge `alpha`:
///
/// ```text
/// f'(X) = f_even(X) + alpha · f_odd(X)
/// ```
///
/// The result is a coefficient vector of length `ceil(n / 2)`.
///
/// # Panics
/// Panics if `coeffs` is empty.
pub fn fri_fold<F: Field>(coeffs: &[F], alpha: F) -> Vec<F> {
    assert!(!coeffs.is_empty(), "fri_fold: empty coefficient vector");

    let n = coeffs.len();
    let half = (n + 1) / 2; // ceil(n / 2)

    (0..half)
        .map(|i| {
            let even = coeffs[2 * i];
            let odd = if 2 * i + 1 < n { coeffs[2 * i + 1] } else { F::zero() };
            even + alpha * odd
        })
        .collect()
}

/// Evaluate a polynomial (given as a coefficient vector) at each point in `domain`.
///
/// Uses Horner's method: `f(x) = c_0 + x*(c_1 + x*(c_2 + ... ))`
///
/// Returns a vector of length `domain.len()`.
pub fn evaluate_on_domain<F: Field>(coeffs: &[F], domain: &[F]) -> Vec<F> {
    domain.iter().map(|&x| horner(coeffs, x)).collect()
}

/// Compute the vanishing polynomial Z_H over `domain`.
///
/// `Z_H(X) = ∏_{d ∈ domain} (X - d)`
///
/// Returns the coefficient vector of the resulting degree-`|domain|` polynomial
/// in ascending order: `[coeff_0, coeff_1, ..., coeff_n]`.
///
/// Uses the standard iterative multiplication of linear factors.
pub fn vanishing_poly<F: Field>(domain: &[F]) -> Vec<F> {
    // Start with the constant polynomial 1
    let mut result = vec![F::one()];

    for &d in domain {
        // Multiply current polynomial by (X - d)
        let mut next = vec![F::zero(); result.len() + 1];
        for (i, &c) in result.iter().enumerate() {
            next[i + 1] += c;       // c * X
            next[i] -= c * d;       // c * (-d)
        }
        result = next;
    }

    result
}

/// Horner's method evaluation of a polynomial at a single point.
///
/// `coeffs[0]` is the constant term, `coeffs[n-1]` is the leading coefficient.
fn horner<F: Field>(coeffs: &[F], x: F) -> F {
    coeffs.iter().rev().fold(F::zero(), |acc, &c| acc * x + c)
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_bls12_381::Fr as Fp;
    use ark_ff::One;
    use ark_poly::{EvaluationDomain, Radix2EvaluationDomain};

    // ── fri_fold ────────────────────────────────────────────────────────────────

    #[test]
    fn fri_fold_halves_even_length() {
        // n=4 → result length 2
        let coeffs: Vec<Fp> = vec![Fp::from(1u64), Fp::from(2u64), Fp::from(3u64), Fp::from(4u64)];
        let alpha = Fp::from(5u64);
        let folded = fri_fold(&coeffs, alpha);
        assert_eq!(folded.len(), 2, "even-length fold should produce n/2 elements");
    }

    #[test]
    fn fri_fold_halves_odd_length() {
        // n=5 → result length 3  (ceil(5/2))
        let coeffs: Vec<Fp> = (1u64..=5).map(Fp::from).collect();
        let alpha = Fp::from(7u64);
        let folded = fri_fold(&coeffs, alpha);
        assert_eq!(folded.len(), 3, "odd-length fold should produce ceil(n/2) elements");
    }

    #[test]
    fn fri_fold_correct_values() {
        // coeffs = [1, 2, 3, 4], alpha = 0
        // even = [1, 3], odd = [2, 4]
        // fold(alpha=0) = even + 0*odd = [1, 3]
        let coeffs: Vec<Fp> = vec![Fp::from(1u64), Fp::from(2u64), Fp::from(3u64), Fp::from(4u64)];
        let folded_zero = fri_fold(&coeffs, Fp::from(0u64));
        assert_eq!(folded_zero, vec![Fp::from(1u64), Fp::from(3u64)]);

        // fold(alpha=1) = even + 1*odd = [1+2, 3+4] = [3, 7]
        let folded_one = fri_fold(&coeffs, Fp::from(1u64));
        assert_eq!(folded_one, vec![Fp::from(3u64), Fp::from(7u64)]);
    }

    #[test]
    fn fri_fold_single_element() {
        let coeffs = vec![Fp::from(42u64)];
        let folded = fri_fold(&coeffs, Fp::from(99u64));
        assert_eq!(folded.len(), 1);
        assert_eq!(folded[0], Fp::from(42u64));
    }

    // ── evaluate_on_domain ───────────────────────────────────────────────────────

    #[test]
    fn evaluate_constant_poly() {
        // f(x) = 7 for all x
        let coeffs = vec![Fp::from(7u64)];
        let domain = Radix2EvaluationDomain::<Fp>::new(4).unwrap();
        let points: Vec<Fp> = domain.elements().collect();
        let evals = evaluate_on_domain(&coeffs, &points);
        assert!(evals.iter().all(|&v| v == Fp::from(7u64)));
    }

    #[test]
    fn evaluate_linear_poly() {
        // f(x) = 2 + 3x  →  f(1) = 5
        let coeffs = vec![Fp::from(2u64), Fp::from(3u64)];
        let points = vec![Fp::from(1u64)];
        let evals = evaluate_on_domain(&coeffs, &points);
        assert_eq!(evals[0], Fp::from(5u64));
    }

    #[test]
    fn evaluate_on_domain_length_matches() {
        let coeffs: Vec<Fp> = (0u64..6).map(Fp::from).collect();
        let domain = Radix2EvaluationDomain::<Fp>::new(8).unwrap();
        let points: Vec<Fp> = domain.elements().collect();
        let evals = evaluate_on_domain(&coeffs, &points);
        assert_eq!(evals.len(), points.len());
    }

    // ── vanishing_poly ───────────────────────────────────────────────────────────

    #[test]
    fn vanishing_poly_degree() {
        let domain = Radix2EvaluationDomain::<Fp>::new(4).unwrap();
        let points: Vec<Fp> = domain.elements().collect(); // 4 points
        let z = vanishing_poly(&points);
        // Z_H has degree |domain| = 4, so coefficient vector length = 5
        assert_eq!(z.len(), 5);
    }

    #[test]
    fn vanishing_poly_roots_vanish() {
        // Z_H(d) = 0 for every d in domain
        let domain = Radix2EvaluationDomain::<Fp>::new(4).unwrap();
        let points: Vec<Fp> = domain.elements().collect();
        let z = vanishing_poly(&points);
        for &d in &points {
            assert_eq!(horner(&z, d), Fp::from(0u64), "Z_H should vanish on domain point {d:?}");
        }
    }

    #[test]
    fn vanishing_poly_nonzero_outside() {
        // Z_H(x) ≠ 0 for x not in the domain (use x = 2)
        let domain = Radix2EvaluationDomain::<Fp>::new(4).unwrap();
        let points: Vec<Fp> = domain.elements().collect();
        let z = vanishing_poly(&points);
        let outside = Fp::from(2u64);
        assert_ne!(horner(&z, outside), Fp::from(0u64));
    }

    #[test]
    fn vanishing_poly_leading_coeff_is_one() {
        let domain = Radix2EvaluationDomain::<Fp>::new(4).unwrap();
        let points: Vec<Fp> = domain.elements().collect();
        let z = vanishing_poly(&points);
        // Leading coefficient of a monic product of linear factors is 1
        assert_eq!(*z.last().unwrap(), Fp::one());
    }
}
