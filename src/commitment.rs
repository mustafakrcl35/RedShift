//! Polynomial commitment scheme for the RedShift protocol.
//!
//! RedShift uses a univariate polynomial commitment scheme.  The original
//! paper describes a KZG-style (Kate–Zaverucha–Goldberg) commitment where:
//!
//! - `commit(f)`   → [f(τ)]₁  (a G1 point, computed with a structured reference string)
//! - `open(f, z)`  → π = [f(τ) - f(z)] / (τ - z)  (a single G1 point)
//! - `verify(C, z, y, π)` → checks the pairing equation e(C - [y]₁, [1]₂) = e(π, [τ]₂ - [z]₂)
//!
//! Alternatively, a FRI-based (hash-only) commitment can be used.

// TODO: define CommitmentKey / VerificationKey structs (SRS for KZG)
// TODO: implement commit(poly, srs) -> Commitment
// TODO: implement open(poly, point, srs) -> Proof
// TODO: implement verify(commitment, point, value, proof, vk) -> bool
// TODO: add batch opening / batch verification
