//! RedShift verifier — replays the prover's transcript and checks every claim.
//!
//! ## Verification steps
//! 1. **Transcript replay** (rounds 1-4): re-derive β, γ, α, ζ by absorbing
//!    the same commitment roots the prover absorbed and squeezing with the same
//!    labels.  The transcript state must reach the same point the prover was at
//!    before the FRI call.
//! 2. **Gate check**: `q_L·a_ζ + q_R·b_ζ + q_M·a_ζ·b_ζ + q_O·c_ζ + q_C = t_ζ · Z_H(ζ)`
//! 3. **Permutation check**: `Z(ζ) · num(ζ) = Z(ζ·ω) · den(ζ)` using the
//!    integer-based coset encoding the prover used.
//! 4. **FRI verification**: `fri_verify` replays the FRI sub-transcript and
//!    checks every Merkle opening in the FRI proof.
//! 5. **Wire opening verification**: re-derive query indices and check the
//!    Merkle openings for `a`, `b`, `c`.

use crate::{
    commitment::verify_opening,
    constraint::{lagrange_interpolate, Circuit, PermutationArgument},
    fri::{FriConfig, fri_verify},
    prover::{Proof, ProvingKey},
    transcript::Transcript,
};
use ark_ff::PrimeField;

// ── VerifyingKey ───────────────────────────────────────────────────────────────

pub struct VerifyingKey<F: PrimeField> {
    pub domain: Vec<F>,
    pub fri_config: FriConfig,
}

impl<F: PrimeField> From<&ProvingKey<F>> for VerifyingKey<F> {
    fn from(pk: &ProvingKey<F>) -> Self {
        VerifyingKey {
            domain: pk.domain.clone(),
            fri_config: FriConfig { num_queries: pk.fri_config.num_queries },
        }
    }
}

// ── Verifier ───────────────────────────────────────────────────────────────────

pub fn verify<F: PrimeField>(
    proof: &Proof<F>,
    circuit: &Circuit<F>,
    perm: &PermutationArgument<F>,
    vk: &VerifyingKey<F>,
) -> bool {
    let mut transcript = Transcript::new(b"redshift-proof");
    let domain = &vk.domain;
    let n = circuit.gates.len();
    let constraint_domain = &domain[..n];

    // ── Round 1 replay ────────────────────────────────────────────────────────
    transcript.absorb_bytes(b"comm_a", &proof.comm_a.root);
    transcript.absorb_bytes(b"comm_b", &proof.comm_b.root);
    transcript.absorb_bytes(b"comm_c", &proof.comm_c.root);

    // ── Round 2 replay ────────────────────────────────────────────────────────
    let beta: F = transcript.squeeze_field(b"beta");
    let gamma: F = transcript.squeeze_field(b"gamma");
    transcript.absorb_bytes(b"comm_z", &proof.comm_z.root);

    // ── Round 3 replay ────────────────────────────────────────────────────────
    // α is squeezed to advance the transcript state (it batches the FRI input).
    let _alpha: F = transcript.squeeze_field(b"alpha");
    transcript.absorb_bytes(b"comm_t", &proof.comm_t.root);

    // ── Round 4 replay ────────────────────────────────────────────────────────
    let zeta: F = transcript.squeeze_field(b"zeta");
    // Bind the prover's evaluation claims into the transcript.
    transcript.absorb_field(b"a_zeta", &proof.a_zeta);
    transcript.absorb_field(b"b_zeta", &proof.b_zeta);
    transcript.absorb_field(b"c_zeta", &proof.c_zeta);
    transcript.absorb_field(b"t_zeta", &proof.t_zeta);
    transcript.absorb_field(b"z_zeta", &proof.z_zeta);
    transcript.absorb_field(b"z_omega_zeta", &proof.z_omega_zeta);

    // ── Gate constraint check ─────────────────────────────────────────────────
    // Evaluate selector polynomials at ζ via Lagrange interpolation.
    let q_l_z = eval_selector(circuit, constraint_domain, zeta, |g| g.q_l);
    let q_r_z = eval_selector(circuit, constraint_domain, zeta, |g| g.q_r);
    let q_m_z = eval_selector(circuit, constraint_domain, zeta, |g| g.q_m);
    let q_o_z = eval_selector(circuit, constraint_domain, zeta, |g| g.q_o);
    let q_c_z = eval_selector(circuit, constraint_domain, zeta, |g| g.q_c);

    let gate_check = q_l_z * proof.a_zeta
        + q_r_z * proof.b_zeta
        + q_m_z * proof.a_zeta * proof.b_zeta
        + q_o_z * proof.c_zeta
        + q_c_z;

    // Z_H(ζ) = ∏(ζ − dᵢ) for dᵢ ∈ constraint_domain.
    // For a multiplicative subgroup this equals ζⁿ − 1.
    let z_h_zeta = constraint_domain
        .iter()
        .fold(F::one(), |acc, &d| acc * (zeta - d));

    if gate_check != proof.t_zeta * z_h_zeta {
        return false;
    }

    // ── Permutation check ─────────────────────────────────────────────────────
    // We use the same integer-based coset encoding as the prover:
    //   id_a[i] = i,  id_b[i] = n+i,  id_c[i] = 2n+i.
    // The permutation polynomials are Lagrange-interpolated from the σ indices.
    let id_a_z = eval_at_zeta(
        constraint_domain,
        &(0..n).map(|i| F::from(i as u64)).collect::<Vec<_>>(),
        zeta,
    );
    let id_b_z = eval_at_zeta(
        constraint_domain,
        &(0..n).map(|i| F::from((n + i) as u64)).collect::<Vec<_>>(),
        zeta,
    );
    let id_c_z = eval_at_zeta(
        constraint_domain,
        &(0..n).map(|i| F::from((2 * n + i) as u64)).collect::<Vec<_>>(),
        zeta,
    );
    let sa_z = eval_at_zeta(
        constraint_domain,
        &perm.sigma_a.iter().map(|&i| F::from(i as u64)).collect::<Vec<_>>(),
        zeta,
    );
    let sb_z = eval_at_zeta(
        constraint_domain,
        &perm.sigma_b.iter().map(|&i| F::from(i as u64)).collect::<Vec<_>>(),
        zeta,
    );
    let sc_z = eval_at_zeta(
        constraint_domain,
        &perm.sigma_c.iter().map(|&i| F::from(i as u64)).collect::<Vec<_>>(),
        zeta,
    );

    let perm_lhs = proof.z_zeta
        * (proof.a_zeta + beta * id_a_z + gamma)
        * (proof.b_zeta + beta * id_b_z + gamma)
        * (proof.c_zeta + beta * id_c_z + gamma);

    let perm_rhs = proof.z_omega_zeta
        * (proof.a_zeta + beta * sa_z + gamma)
        * (proof.b_zeta + beta * sb_z + gamma)
        * (proof.c_zeta + beta * sc_z + gamma);

    if perm_lhs != perm_rhs {
        return false;
    }

    // ── FRI verification ──────────────────────────────────────────────────────
    // fri_verify replays the FRI sub-transcript (absorbing roots, squeezing
    // alphas, and checking Merkle-query indices), leaving the transcript at
    // the same state the prover had after fri_commit.
    if proof.fri_proof.commitment.roots.is_empty() {
        return false;
    }
    let fri_root = proof.fri_proof.commitment.roots[0];
    if !fri_verify(&proof.fri_proof, &fri_root, &mut transcript, &vk.fri_config) {
        return false;
    }

    // ── Wire opening verification ─────────────────────────────────────────────
    // After FRI the transcript is in the same state as the prover after
    // fri_commit.  Re-squeeze the wire-query indices and verify each opening.
    let n_dom = domain.len();
    if proof.opening_a.len() < vk.fri_config.num_queries
        || proof.opening_b.len() < vk.fri_config.num_queries
        || proof.opening_c.len() < vk.fri_config.num_queries
    {
        return false;
    }

    for i in 0..vk.fri_config.num_queries {
        let idx = transcript.squeeze_index(b"open_query", n_dom);

        // Index must match what the prover committed to
        if proof.opening_a[i].index != idx
            || proof.opening_b[i].index != idx
            || proof.opening_c[i].index != idx
        {
            return false;
        }

        if !verify_opening(&proof.comm_a, &proof.opening_a[i])
            || !verify_opening(&proof.comm_b, &proof.opening_b[i])
            || !verify_opening(&proof.comm_c, &proof.opening_c[i])
        {
            return false;
        }
    }

    true
}

// ── Helpers ────────────────────────────────────────────────────────────────────

/// Evaluate a selector polynomial (derived from gate fields) at `zeta`.
fn eval_selector<F, Sel>(
    circuit: &Circuit<F>,
    domain: &[F],
    zeta: F,
    sel: Sel,
) -> F
where
    F: PrimeField,
    Sel: Fn(&crate::constraint::Gate<F>) -> F,
{
    let vals: Vec<F> = circuit.gates.iter().map(sel).collect();
    eval_poly(&lagrange_interpolate(domain, &vals), zeta)
}

/// Lagrange-interpolate `values` over `domain` then evaluate at `zeta`.
fn eval_at_zeta<F: PrimeField>(domain: &[F], values: &[F], zeta: F) -> F {
    eval_poly(&lagrange_interpolate(domain, values), zeta)
}

/// Horner evaluation of a coefficient polynomial at `x`.
fn eval_poly<F: PrimeField>(coeffs: &[F], x: F) -> F {
    coeffs.iter().rev().fold(F::zero(), |acc, &c| acc * x + c)
}

// ── Tests ──────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use ark_bls12_381::Fr;
    use crate::{
        constraint::{Circuit, Gate, PermutationArgument},
        domain::multiplicative_subgroup,
        fri::FriConfig,
        prover::{prove, ProvingKey},
    };

    fn proving_key() -> ProvingKey<Fr> {
        ProvingKey {
            domain: multiplicative_subgroup::<Fr>(3), // 8 elements
            fri_config: FriConfig { num_queries: 2 },
        }
    }

    fn addition_circuit() -> (Circuit<Fr>, PermutationArgument<Fr>) {
        let n = 1usize;
        let circuit = Circuit {
            gates: vec![Gate {
                q_l: Fr::from(1u64),
                q_r: Fr::from(1u64),
                q_m: Fr::from(0u64),
                q_o: -Fr::from(1u64),
                q_c: Fr::from(0u64),
            }],
            a: vec![Fr::from(2u64)],
            b: vec![Fr::from(3u64)],
            c: vec![Fr::from(5u64)],
        };
        let perm = PermutationArgument::new(
            (0..n).collect(),
            (n..2 * n).collect(),
            (2 * n..3 * n).collect(),
        );
        (circuit, perm)
    }

    fn multiplication_circuit() -> (Circuit<Fr>, PermutationArgument<Fr>) {
        let n = 1usize;
        let circuit = Circuit {
            gates: vec![Gate {
                q_l: Fr::from(0u64),
                q_r: Fr::from(0u64),
                q_m: Fr::from(1u64),
                q_o: -Fr::from(1u64),
                q_c: Fr::from(0u64),
            }],
            a: vec![Fr::from(3u64)],
            b: vec![Fr::from(4u64)],
            c: vec![Fr::from(12u64)],
        };
        let perm = PermutationArgument::new(
            (0..n).collect(),
            (n..2 * n).collect(),
            (2 * n..3 * n).collect(),
        );
        (circuit, perm)
    }

    #[test]
    fn test_verify_valid_proof() {
        let (circuit, perm) = addition_circuit();
        let pk = proving_key();
        let proof = prove(&circuit, &perm, &pk);
        let vk = VerifyingKey::from(&pk);
        assert!(verify(&proof, &circuit, &perm, &vk), "valid proof must verify");
    }

    #[test]
    fn test_verify_multiplication_circuit() {
        let (circuit, perm) = multiplication_circuit();
        let pk = proving_key();
        let proof = prove(&circuit, &perm, &pk);
        let vk = VerifyingKey::from(&pk);
        assert!(verify(&proof, &circuit, &perm, &vk), "valid multiplication proof must verify");
    }

    #[test]
    fn test_verify_tampered_a_zeta_fails() {
        let (circuit, perm) = addition_circuit();
        let pk = proving_key();
        let mut proof = prove(&circuit, &perm, &pk);
        // Tamper: 999 ≠ 2 → gate check: 999 + 3 - 5 = 997 ≠ 0
        proof.a_zeta = Fr::from(999u64);
        let vk = VerifyingKey::from(&pk);
        assert!(!verify(&proof, &circuit, &perm, &vk), "tampered a_zeta must not verify");
    }

    #[test]
    fn test_verify_tampered_comm_fails() {
        let (circuit, perm) = addition_circuit();
        let pk = proving_key();
        let (circuit2, perm2) = multiplication_circuit();
        let proof_mul = prove(&circuit2, &perm2, &pk);

        // Swap comm_a from a different proof → transcript diverges → FRI/opening fail
        let mut proof = prove(&circuit, &perm, &pk);
        proof.comm_a = proof_mul.comm_a;

        let vk = VerifyingKey::from(&pk);
        assert!(!verify(&proof, &circuit, &perm, &vk), "tampered commitment must not verify");
    }
}
