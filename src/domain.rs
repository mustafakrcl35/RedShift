//! Evaluation domains for the RedShift protocol.
//!
//! RedShift (and FRI in general) requires two kinds of domains:
//!
//! - **Multiplicative subgroup** `H = {ω⁰, ω¹, ..., ω^(n-1)}`
//!   Used as the *constraint domain* (the domain where polynomial identities
//!   are checked).  `ω` is the primitive `n`-th root of unity in `F`.
//!
//! - **Coset** `η · H = {η, η·ω, ..., η·ω^(n-1)}`
//!   The blow-up evaluation domain for FRI.  Choosing `η ∉ H` (typically
//!   the field generator) ensures the codeword symbols are disjoint from
//!   the constraint domain, preventing trivial attacks.
//!
//! Both rely on `FftField` which guarantees the existence of `2^k`-th roots
//! of unity for any `k ≤ TWO_ADICITY`.  For BLS12-381's scalar field,
//! `TWO_ADICITY = 32`, so domains up to size `2^32` are supported.

use ark_ff::FftField;

/// Generate the multiplicative subgroup of order `2^log_size`.
///
/// `H = {ω⁰, ω¹, ..., ω^(n-1)}`  where `ω` is the primitive `n`-th root of
/// unity and `n = 2^log_size`.
///
/// Elements are ordered `[1, ω, ω², ..., ω^(n-1)]`.
///
/// # Panics
/// Panics if the field does not have a root of unity of the requested order
/// (i.e., `log_size > F::TWO_ADICITY`).
pub fn multiplicative_subgroup<F: FftField>(log_size: u32) -> Vec<F> {
    let n = 1usize << log_size;
    let omega = F::get_root_of_unity(n as u64)
        .expect("field must have a root of unity of the requested order");

    let mut domain = Vec::with_capacity(n);
    let mut curr = F::one();
    for _ in 0..n {
        domain.push(curr);
        curr *= omega;
    }
    domain
}

/// Generate the coset `η · H` of order `2^log_size`.
///
/// Used as the FRI evaluation domain: evaluating `f` on `η · H` instead of
/// `H` itself ensures no evaluation point coincides with a constraint check
/// point (assuming `η ∉ H`, e.g., `η = F::GENERATOR`).
///
/// # Panics
/// Same conditions as [`multiplicative_subgroup`].
pub fn coset<F: FftField>(log_size: u32, shift: F) -> Vec<F> {
    multiplicative_subgroup::<F>(log_size)
        .into_iter()
        .map(|x| shift * x)
        .collect()
}

// ── Tests ─────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use ark_bls12_381::Fr as Fp;
    use ark_ff::{Field, One};

    // ── multiplicative_subgroup ───────────────────────────────────────────────

    #[test]
    fn test_subgroup_size() {
        // Domain must have exactly 2^log_size elements for each log_size
        for log_size in [1u32, 2, 3, 4, 8] {
            let expected = 1usize << log_size;
            let domain = multiplicative_subgroup::<Fp>(log_size);
            assert_eq!(domain.len(), expected, "subgroup size must be 2^{log_size}");
        }
    }

    #[test]
    fn test_subgroup_starts_at_one() {
        let domain = multiplicative_subgroup::<Fp>(4);
        assert_eq!(domain[0], Fp::one(), "ω⁰ must be 1");
    }

    #[test]
    fn test_subgroup_closure() {
        // ω^n = 1, and consecutive elements satisfy domain[i+1] = domain[i] * ω
        let log_size = 4u32;
        let n = 1usize << log_size;
        let domain = multiplicative_subgroup::<Fp>(log_size);
        let omega = domain[1]; // primitive n-th root of unity

        // ω^n = 1
        assert_eq!(
            omega.pow([n as u64]),
            Fp::one(),
            "ω^n must equal 1"
        );

        // Consecutive step: domain[i] * ω = domain[i+1]
        for i in 0..n - 1 {
            assert_eq!(
                domain[i] * omega,
                domain[i + 1],
                "domain[{i}] * ω must equal domain[{}]", i + 1
            );
        }

        // Wrap-around: domain[n-1] * ω = domain[0] = 1
        assert_eq!(domain[n - 1] * omega, Fp::one(), "domain must wrap around to 1");
    }

    #[test]
    fn test_subgroup_elements_are_distinct() {
        use std::collections::HashSet;
        let domain = multiplicative_subgroup::<Fp>(4);
        let unique: HashSet<Fp> = domain.iter().cloned().collect();
        assert_eq!(unique.len(), domain.len(), "all subgroup elements must be distinct");
    }

    // ── coset ─────────────────────────────────────────────────────────────────

    #[test]
    fn test_coset_size() {
        let c = coset::<Fp>(3, Fp::from(3u64));
        assert_eq!(c.len(), 8, "coset must have 2^log_size elements");
    }

    #[test]
    fn test_coset_first_element_is_shift() {
        // coset[0] = shift * ω⁰ = shift * 1 = shift
        let shift = Fp::from(5u64);
        let c = coset::<Fp>(3, shift);
        assert_eq!(c[0], shift, "first coset element must equal the shift");
    }

    #[test]
    fn test_coset_disjoint() {
        // η·H ∩ H = ∅  when η ∉ H.
        // We use η = 3; for BLS12-381's Fr, small integers are not
        // 2^k-th roots of unity (they are enormous field elements).
        use std::collections::HashSet;
        let log_size = 3u32;
        let shift = Fp::from(3u64);
        let subgroup = multiplicative_subgroup::<Fp>(log_size);
        let coset_elems = coset::<Fp>(log_size, shift);

        let subgroup_set: HashSet<Fp> = subgroup.into_iter().collect();
        for elem in &coset_elems {
            assert!(
                !subgroup_set.contains(elem),
                "coset element {elem:?} must not be in the subgroup"
            );
        }
    }
}
