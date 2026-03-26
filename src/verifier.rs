//! RedShift verifier.
//!
//! The verifier receives a proof and a set of public inputs, then checks:
//! 1. All polynomial commitments are well-formed.
//! 2. The Fiat-Shamir challenges are reproduced correctly (transcript).
//! 3. Every opening proof is valid against the corresponding commitment.
//! 4. The constraint polynomial identity holds at the queried points.
//!
//! The verifier runs in O(log N) field operations and a constant number
//! of pairing checks, making it succinct.

// TODO: define VerifyingKey struct
// TODO: implement verify(proof, public_inputs, vk) -> bool
// TODO: implement batch_verify for multiple proofs
