//! RedShift prover — assembles a full PIOP proof.
//!
//! ## Round structure
//! 1. **Wire commitments**: Lagrange-interpolate a/b/c, commit evaluations.
//! 2. **Permutation**: Derive β,γ; compute grand-product Z; commit.
//! 3. **Quotient**: Derive α; compute T = f_gate / Z_H; commit.
//! 4. **Evaluation**: Derive ζ; evaluate all polys at ζ (and Z at ζ·ω).
//! 5. **FRI**: Low-degree test on a linear combination of wire evaluations.
//! 6. **Query openings**: Open wire commitments at transcript-derived indices.

use crate::{
    commitment::{commit, open, Commitment, OpeningProof},
    constraint::{lagrange_interpolate, Circuit, PermutationArgument},
    fri::{fri_commit, FriConfig, FriProof},
    polynomial::evaluate_on_domain,
    transcript::Transcript,
};
use ark_ff::PrimeField;

// ── Public types ───────────────────────────────────────────────────────────────

pub struct ProvingKey<F: PrimeField> {
    /// Multiplicative subgroup H used as the evaluation / FRI domain.
    pub domain: Vec<F>,
    pub fri_config: FriConfig,
}

pub struct Proof<F: PrimeField> {
    // ── Wire polynomial commitments (Round 1) ──
    pub comm_a: Commitment,
    pub comm_b: Commitment,
    pub comm_c: Commitment,

    // ── Quotient polynomial commitment (Round 3) ──
    pub comm_t: Commitment,

    // ── Permutation grand-product commitment (Round 2) ──
    pub comm_z: Commitment,

    // ── FRI low-degree proof (Round 5) ──
    pub fri_proof: FriProof<F>,

    // ── Polynomial evaluations at challenge point ζ (Round 4) ──
    pub a_zeta: F,
    pub b_zeta: F,
    pub c_zeta: F,
    pub t_zeta: F,
    pub z_zeta: F,
    /// Z(ζ · ωH) — needed for the permutation argument boundary condition.
    pub z_omega_zeta: F,

    // ── Merkle opening proofs at query indices (Round 6) ──
    pub opening_a: Vec<OpeningProof>,
    pub opening_b: Vec<OpeningProof>,
    pub opening_c: Vec<OpeningProof>,
}

// ── Prover ─────────────────────────────────────────────────────────────────────

pub fn prove<F: PrimeField>(
    circuit: &Circuit<F>,
    perm: &PermutationArgument<F>,
    pk: &ProvingKey<F>,
) -> Proof<F> {
    let mut transcript = Transcript::new(b"redshift-proof");
    let domain = &pk.domain;
    let n = circuit.gates.len();
    assert!(!domain.is_empty() && domain.len() >= n, "domain must have at least n elements");

    // The constraint domain is the first n elements of pk.domain.
    // These are consecutive powers of the subgroup generator, giving n distinct
    // points suitable for Lagrange interpolation and vanishing-polynomial checks.
    let constraint_domain = &domain[..n];

    // ── Round 1: wire polynomials ──────────────────────────────────────────────

    // Interpolate witness values over the constraint domain, then evaluate the
    // resulting (low-degree) polynomials over the full FRI domain.
    let (a_coeffs, b_coeffs, c_coeffs) = circuit.wire_polynomials(constraint_domain);

    let a_evals = evaluate_on_domain(&a_coeffs, domain);
    let b_evals = evaluate_on_domain(&b_coeffs, domain);
    let c_evals = evaluate_on_domain(&c_coeffs, domain);

    let (comm_a, tree_a) = commit(&a_evals);
    let (comm_b, tree_b) = commit(&b_evals);
    let (comm_c, tree_c) = commit(&c_evals);

    transcript.absorb_bytes(b"comm_a", &comm_a.root);
    transcript.absorb_bytes(b"comm_b", &comm_b.root);
    transcript.absorb_bytes(b"comm_c", &comm_c.root);

    // ── Round 2: permutation grand product ────────────────────────────────────

    let beta: F = transcript.squeeze_field(b"beta");
    let gamma: F = transcript.squeeze_field(b"gamma");

    // grand_product returns n+1 values: Z(ω⁰) … Z(ωⁿ).
    // Interpolate only the first n evaluations over the constraint domain.
    let z_all = perm.grand_product(circuit, beta, gamma);
    let z_coeffs = lagrange_interpolate(constraint_domain, &z_all[..n]);
    let z_full_evals = evaluate_on_domain(&z_coeffs, domain);

    let (comm_z, _tree_z) = commit(&z_full_evals);
    transcript.absorb_bytes(b"comm_z", &comm_z.root);

    // ── Round 3: quotient polynomial ──────────────────────────────────────────

    // α is used to linearly combine gate and permutation terms (here it batches
    // the wire evaluations for the FRI input in Round 5).
    let alpha: F = transcript.squeeze_field(b"alpha");

    let t_coeffs = circuit
        .quotient_poly(constraint_domain)
        .expect("circuit must be satisfied — quotient_poly returned None");
    let t_evals = evaluate_on_domain(&t_coeffs, domain);

    let (comm_t, _tree_t) = commit(&t_evals);
    transcript.absorb_bytes(b"comm_t", &comm_t.root);

    // ── Round 4: evaluation challenge ─────────────────────────────────────────

    let zeta: F = transcript.squeeze_field(b"zeta");

    let a_zeta = eval_poly(&a_coeffs, zeta);
    let b_zeta = eval_poly(&b_coeffs, zeta);
    let c_zeta = eval_poly(&c_coeffs, zeta);
    let t_zeta = eval_poly(&t_coeffs, zeta);
    let z_zeta = eval_poly(&z_coeffs, zeta);

    // ωH = generator of the constraint domain (= constraint_domain[1] if n ≥ 2).
    let omega_h = if n > 1 { constraint_domain[1] } else { F::one() };
    let z_omega_zeta = eval_poly(&z_coeffs, zeta * omega_h);

    // Bind evaluation openings into the transcript so the FRI challenge depends
    // on the committed values.
    transcript.absorb_field(b"a_zeta", &a_zeta);
    transcript.absorb_field(b"b_zeta", &b_zeta);
    transcript.absorb_field(b"c_zeta", &c_zeta);
    transcript.absorb_field(b"t_zeta", &t_zeta);
    transcript.absorb_field(b"z_zeta", &z_zeta);
    transcript.absorb_field(b"z_omega_zeta", &z_omega_zeta);

    // ── Round 5: FRI low-degree test ──────────────────────────────────────────

    // Batch a, b, c, t into a single polynomial using the α challenge:
    //   f_fri = a + α·b + α²·c + α³·t
    // This polynomial is low-degree iff each constituent is.
    let fri_evals: Vec<F> = a_evals
        .iter()
        .zip(b_evals.iter())
        .zip(c_evals.iter())
        .zip(t_evals.iter())
        .map(|(((a, b), c), t)| *a + alpha * (*b + alpha * (*c + alpha * t)))
        .collect();

    let fri_proof = fri_commit(fri_evals, pk.domain.clone(), &mut transcript, &pk.fri_config);

    // ── Round 6: Merkle query openings ────────────────────────────────────────

    let n_dom = domain.len();
    let mut opening_a = Vec::with_capacity(pk.fri_config.num_queries);
    let mut opening_b = Vec::with_capacity(pk.fri_config.num_queries);
    let mut opening_c = Vec::with_capacity(pk.fri_config.num_queries);

    for _ in 0..pk.fri_config.num_queries {
        let idx = transcript.squeeze_index(b"open_query", n_dom);
        opening_a.push(open(&tree_a, idx, &a_evals));
        opening_b.push(open(&tree_b, idx, &b_evals));
        opening_c.push(open(&tree_c, idx, &c_evals));
    }

    Proof {
        comm_a,
        comm_b,
        comm_c,
        comm_t,
        comm_z,
        fri_proof,
        a_zeta,
        b_zeta,
        c_zeta,
        t_zeta,
        z_zeta,
        z_omega_zeta,
        opening_a,
        opening_b,
        opening_c,
    }
}

// ── Horner evaluation ──────────────────────────────────────────────────────────

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
    };

    fn proving_key() -> ProvingKey<Fr> {
        ProvingKey {
            domain: multiplicative_subgroup::<Fr>(3), // 8 elements — covers 1-gate circuits
            fri_config: FriConfig { num_queries: 2 },
        }
    }

    /// a + b = c  →  2 + 3 = 5, identity permutation.
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

    /// a · b = c  →  3 · 4 = 12, identity permutation.
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
    fn test_prove_addition_circuit() {
        let (circuit, perm) = addition_circuit();
        let pk = proving_key();
        let proof = prove(&circuit, &perm, &pk);

        // a_zeta = eval_poly([2], ζ) = 2 ≠ 0
        assert_ne!(proof.a_zeta, Fr::from(0u64), "a_zeta must be nonzero (witness a=2)");
        // Sanity: correct number of query openings
        assert_eq!(proof.opening_a.len(), pk.fri_config.num_queries);
        assert_eq!(proof.opening_b.len(), pk.fri_config.num_queries);
        assert_eq!(proof.opening_c.len(), pk.fri_config.num_queries);
    }

    #[test]
    fn test_prove_multiplication_circuit() {
        let (circuit, perm) = multiplication_circuit();
        let pk = proving_key();
        let proof = prove(&circuit, &perm, &pk);

        // b_zeta = eval_poly([4], ζ) = 4 ≠ 0
        assert_ne!(proof.b_zeta, Fr::from(0u64), "b_zeta must be nonzero (witness b=4)");
        assert_eq!(proof.opening_a.len(), pk.fri_config.num_queries);
    }

    #[test]
    fn test_prove_wire_commitments_differ() {
        // Two different circuits must produce different wire commitments.
        let (circ_add, perm_add) = addition_circuit();
        let (circ_mul, perm_mul) = multiplication_circuit();
        let pk = proving_key();

        let p_add = prove(&circ_add, &perm_add, &pk);
        let p_mul = prove(&circ_mul, &perm_mul, &pk);

        assert_ne!(
            p_add.comm_a.root,
            p_mul.comm_a.root,
            "different witnesses must produce different a-commitments"
        );
    }

    #[test]
    fn test_prove_deterministic() {
        // Same inputs → identical proof (deterministic Fiat-Shamir).
        let (circuit, perm) = addition_circuit();
        let pk = proving_key();

        let p1 = prove(&circuit, &perm, &pk);
        let p2 = prove(&circuit, &perm, &pk);

        assert_eq!(p1.comm_a.root, p2.comm_a.root);
        assert_eq!(p1.a_zeta, p2.a_zeta);
        assert_eq!(p1.fri_proof.commitment.roots, p2.fri_proof.commitment.roots);
    }
}
