//! Multi-round FRI (Fast Reed-Solomon IOP) commit and verify.
//!
//! ## Commit phase
//! Repeatedly folds the evaluation vector in half using a transcript-derived
//! challenge `α`, committing each layer to a SHA-256 Merkle tree.  Stops when
//! a single element remains (the constant `final_value`).
//!
//! ## Query phase
//! Derives `num_queries` indices from the transcript and opens each layer's
//! Merkle tree at the corresponding position.
//!
//! ## Verify
//! Replays the transcript to reconstruct all challenges and query indices,
//! then checks every Merkle opening proof.

use crate::{
    commitment::{commit, hash_leaf, open, verify_opening, Commitment, OpeningProof},
    polynomial::fri_fold_evaluations,
    transcript::Transcript,
};
use ark_ff::{BigInteger, PrimeField};

// ── Config & proof types ───────────────────────────────────────────────────────

pub struct FriConfig {
    /// Number of query repetitions (security parameter).
    pub num_queries: usize,
}

pub struct FriCommitment<F: PrimeField> {
    /// Merkle roots for each fold layer (length = log₂(initial domain size)).
    pub roots: Vec<[u8; 32]>,
    /// Constant value after all folding rounds.
    pub final_value: F,
}

pub struct FriQuery<F: PrimeField> {
    /// Query index into the initial (layer-0) evaluation vector.
    pub index: usize,
    /// Per-layer: (evaluation at queried position, Merkle opening proof).
    pub layers: Vec<(F, OpeningProof)>,
}

pub struct FriProof<F: PrimeField> {
    pub commitment: FriCommitment<F>,
    pub queries: Vec<FriQuery<F>>,
}

// ── Commit ─────────────────────────────────────────────────────────────────────

/// Run the FRI commit and query phases, returning a proof.
///
/// `evaluations` and `domain` must have the same power-of-two length ≥ 2.
pub fn fri_commit<F: PrimeField>(
    evaluations: Vec<F>,
    domain: Vec<F>,
    transcript: &mut Transcript,
    config: &FriConfig,
) -> FriProof<F> {
    let mut cur_evals = evaluations;
    let mut cur_domain = domain;

    let mut roots: Vec<[u8; 32]> = Vec::new();
    let mut trees = Vec::new();
    let mut all_evals: Vec<Vec<F>> = Vec::new();

    // ── Commit phase ──────────────────────────────────────────────────────────
    while cur_evals.len() > 1 {
        let (_c, tree) = commit(&cur_evals);
        let root = tree.root();

        // Bind root to transcript, store for queries
        transcript.absorb_bytes(b"fri_root", &root);
        roots.push(root);
        trees.push(tree);
        all_evals.push(cur_evals.clone());

        // Derive folding challenge
        let alpha: F = transcript.squeeze_field(b"fri_alpha");

        // Fold: domain halves (x → x²), evaluations halve
        let next_evals = fri_fold_evaluations(&cur_evals, &cur_domain, alpha);
        let next_domain: Vec<F> = cur_domain
            .iter()
            .take(cur_domain.len() / 2)
            .map(|&x| x * x)
            .collect();

        cur_evals = next_evals;
        cur_domain = next_domain;
    }

    let final_value = cur_evals[0];
    let num_layers = all_evals.len();
    let initial_n = all_evals.first().map(|v| v.len()).unwrap_or(1);

    // ── Query phase ───────────────────────────────────────────────────────────
    let mut queries = Vec::new();
    for _ in 0..config.num_queries {
        let index = transcript.squeeze_index(b"fri_query", initial_n);
        let mut layers = Vec::new();
        let mut q = index;

        for l in 0..num_layers {
            let n_l = all_evals[l].len();
            let q_l = q % n_l;
            let value = all_evals[l][q_l];
            let proof = open(&trees[l], q_l, &all_evals[l]);
            layers.push((value, proof));

            // Index in next layer: q_l folds to q_l % (n_l / 2)
            if n_l > 1 {
                q = q_l % (n_l / 2);
            }
        }

        queries.push(FriQuery { index, layers });
    }

    FriProof {
        commitment: FriCommitment { roots, final_value },
        queries,
    }
}

// ── Verify ─────────────────────────────────────────────────────────────────────

/// Verify a FRI proof.
///
/// The verifier transcript must be initialised identically to the prover's
/// (same label).  Returns `true` iff all Merkle opening proofs are valid and
/// all query indices match the transcript-derived values.
pub fn fri_verify<F: PrimeField>(
    proof: &FriProof<F>,
    initial_root: &[u8; 32],
    transcript: &mut Transcript,
    config: &FriConfig,
) -> bool {
    let roots = &proof.commitment.roots;

    if roots.is_empty() || &roots[0] != initial_root {
        return false;
    }

    // Replay commit-phase transcript: absorb each root and squeeze the alpha
    // that the prover used to fold, advancing the state identically.
    for root in roots.iter() {
        transcript.absorb_bytes(b"fri_root", root);
        let _alpha: F = transcript.squeeze_field(b"fri_alpha");
    }

    // Reconstruct initial domain size: prover did log₂(initial_n) fold rounds.
    let num_rounds = roots.len();
    let initial_n = 1usize << num_rounds;

    // Verify each query
    for qi in 0..config.num_queries {
        let expected_index = transcript.squeeze_index(b"fri_query", initial_n);

        let Some(query) = proof.queries.get(qi) else {
            return false;
        };

        // Query index must match transcript
        if query.index != expected_index {
            return false;
        }

        // Each query must cover exactly one entry per layer
        if query.layers.len() != num_rounds {
            return false;
        }

        for (l, (value, op_proof)) in query.layers.iter().enumerate() {
            let n_l = initial_n >> l;
            let commitment = Commitment { root: roots[l], size: n_l };

            // The stored field element must hash to the leaf recorded in the proof
            let expected_hash = hash_leaf(&value.into_bigint().to_bytes_le());
            if op_proof.value_hash != expected_hash {
                return false;
            }

            // Merkle path must authenticate the leaf against the layer root
            if !verify_opening(&commitment, op_proof) {
                return false;
            }
        }
    }

    true
}

// ── Tests ──────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use ark_bls12_381::Fr as Fp;
    use crate::{
        domain::multiplicative_subgroup,
        polynomial::evaluate_on_domain,
        transcript::Transcript,
    };

    /// degree-4 polynomial evaluated over a 16-element multiplicative subgroup.
    fn degree4_setup() -> (Vec<Fp>, Vec<Fp>) {
        // f(x) = 1 + 2x + 3x² + 4x³ + 5x⁴
        let coeffs: Vec<Fp> = (1u64..=5).map(Fp::from).collect();
        let domain = multiplicative_subgroup::<Fp>(4); // 2⁴ = 16
        let evals = evaluate_on_domain(&coeffs, &domain);
        (evals, domain)
    }

    #[test]
    fn test_fri_full_low_degree() {
        // A degree-4 polynomial over a 16-point domain should verify.
        let (evals, domain) = degree4_setup();
        let config = FriConfig { num_queries: 10 };

        let mut prover_t = Transcript::new(b"fri_test");
        let proof = fri_commit(evals, domain, &mut prover_t, &config);

        let initial_root = proof.commitment.roots[0];
        let mut verifier_t = Transcript::new(b"fri_test");
        assert!(
            fri_verify(&proof, &initial_root, &mut verifier_t, &config),
            "valid FRI proof must verify"
        );
    }

    #[test]
    fn test_fri_round_count() {
        // n = 16 → log₂(16) = 4 fold rounds → 4 Merkle commitments.
        let (evals, domain) = degree4_setup();
        let config = FriConfig { num_queries: 1 };

        let mut transcript = Transcript::new(b"fri_test");
        let proof = fri_commit(evals, domain, &mut transcript, &config);

        assert_eq!(
            proof.commitment.roots.len(),
            4,
            "expected log₂(16)=4 rounds, got {}",
            proof.commitment.roots.len()
        );
    }

    #[test]
    fn test_transcript_challenge_consistency() {
        // Identical inputs → identical query indices (determinism).
        // Both resulting proofs must verify.
        let (evals, domain) = degree4_setup();
        let config = FriConfig { num_queries: 5 };

        let mut t1 = Transcript::new(b"fri_test");
        let proof1 = fri_commit(evals.clone(), domain.clone(), &mut t1, &config);

        let mut t2 = Transcript::new(b"fri_test");
        let proof2 = fri_commit(evals, domain, &mut t2, &config);

        for (q1, q2) in proof1.queries.iter().zip(proof2.queries.iter()) {
            assert_eq!(q1.index, q2.index, "query indices must be deterministic");
        }

        let mut vt1 = Transcript::new(b"fri_test");
        let mut vt2 = Transcript::new(b"fri_test");
        assert!(fri_verify(&proof1, &proof1.commitment.roots[0], &mut vt1, &config));
        assert!(fri_verify(&proof2, &proof2.commitment.roots[0], &mut vt2, &config));
    }
}
