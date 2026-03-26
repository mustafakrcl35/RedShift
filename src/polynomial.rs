//! Polynomial utilities for the RedShift protocol.
//!
//! This module provides helpers on top of `ark-poly` that are used across
//! the prover and verifier:
//!
//! - Splitting a polynomial into even/odd coefficient halves (FRI folding step)
//! - Evaluating a polynomial on a coset or arbitrary domain
//! - Computing the vanishing polynomial Z_H(X) = X^n - 1 for a domain H
//! - Quotient polynomial division: (f - g) / Z_H

// TODO: implement polynomial folding (even/odd split) for FRI
// TODO: implement vanishing polynomial Z_H(X) = X^n - 1
// TODO: implement quotient polynomial computation (f - g) / Z_H
