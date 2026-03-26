//! Merkle tree based polynomial commitment for the RedShift protocol.
//!
//! RedShift uses a hash-based (transparent, no trusted setup) commitment:
//!
//! 1. Evaluate `f` over a blow-up domain → Reed-Solomon codeword `{f(d) | d ∈ D}`
//! 2. Hash each evaluation and build a **Merkle tree** → root = commitment
//! 3. Open at index `i`: reveal `f(D[i])` + Merkle authentication path
//! 4. FRI low-degree test (see `polynomial::fri_fold`) confirms the codeword
//!    is close to a low-degree polynomial
//!
//! This module implements steps 2-3.  FRI lives in `polynomial.rs`.
//!
//! # Hash function
//! Uses Rust's `DefaultHasher` for simplicity (non-cryptographic).
//! In production replace with SHA-256, Blake2, or a ZK-friendly hash
//! (Poseidon, Rescue) that can be verified inside a circuit.

use ark_ff::Field;
use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};

// ── Hash primitives ───────────────────────────────────────────────────────────

/// Hash a field element to a `u64`.
///
/// `ark-ff` field types implement `Hash` as a supertrait of `Field`,
/// so the `+ Hash` bound is always satisfied for any `F: Field`.
pub fn hash_field_element<F: Field + Hash>(val: &F) -> u64 {
    let mut h = DefaultHasher::new();
    val.hash(&mut h);
    h.finish()
}

/// Combine two child hashes into a parent hash.
pub fn hash_pair(left: u64, right: u64) -> u64 {
    let mut h = DefaultHasher::new();
    left.hash(&mut h);
    right.hash(&mut h);
    h.finish()
}

// ── MerkleTree ────────────────────────────────────────────────────────────────

/// A complete binary Merkle tree stored in a 1-indexed flat array.
///
/// For `n` leaves (always a power of two after padding), the layout is:
///
/// ```text
/// index : 1        2        3        4   5   6   7
///         root     L-child  R-child  L0  L1  L2  L3   (n=4)
///
/// parent(i)       = i >> 1
/// left_child(i)   = 2*i
/// right_child(i)  = 2*i + 1
/// sibling(i)      = i ^ 1          (flips last bit)
/// leaves          = nodes[n .. 2n-1]
/// ```
pub struct MerkleTree {
    /// Leaf hashes, padded to the next power of two with `0`.
    pub leaves: Vec<u64>,
    /// All nodes, 1-indexed (`nodes[0]` is unused padding).
    pub nodes: Vec<u64>,
}

impl MerkleTree {
    /// Build a Merkle tree from pre-computed leaf hashes.
    ///
    /// Leaf count is padded to the next power of two by appending `0`.
    ///
    /// # Panics
    /// Panics if `leaf_hashes` is empty.
    pub fn new(leaf_hashes: Vec<u64>) -> Self {
        assert!(!leaf_hashes.is_empty(), "MerkleTree: leaf_hashes must not be empty");

        let n = leaf_hashes.len().next_power_of_two();
        let mut leaves = leaf_hashes;
        leaves.resize(n, 0u64); // pad with zeros

        // Allocate 2*n slots; nodes[0] is unused (1-indexed tree).
        let mut nodes = vec![0u64; 2 * n];

        // Place leaves at positions n, n+1, ..., 2n-1.
        for (i, &h) in leaves.iter().enumerate() {
            nodes[n + i] = h;
        }

        // Build internal nodes bottom-up (index n-1 down to 1).
        for i in (1..n).rev() {
            nodes[i] = hash_pair(nodes[2 * i], nodes[2 * i + 1]);
        }

        MerkleTree { leaves, nodes }
    }

    /// Return the Merkle root.
    pub fn root(&self) -> u64 {
        self.nodes[1]
    }

    /// Generate an authentication path for the leaf at `index`.
    ///
    /// Returns sibling hashes from leaf level up to (but not including) the root.
    /// Path length equals `log2(leaves.len())`.
    ///
    /// # Panics
    /// Panics if `index >= leaves.len()`.
    pub fn proof(&self, index: usize) -> Vec<u64> {
        let n = self.leaves.len();
        assert!(index < n, "proof: index {index} out of bounds (tree has {n} leaves)");

        let mut path = Vec::new();
        let mut pos = n + index; // position of leaf in nodes array

        while pos > 1 {
            // pos ^ 1 flips the last bit → yields the sibling node
            path.push(self.nodes[pos ^ 1]);
            pos >>= 1; // ascend to parent
        }

        path
    }

    /// Verify an authentication path.
    ///
    /// Re-derives the root from `leaf` and `proof`, then compares with `root`.
    /// `index` determines left/right ordering at each level.
    pub fn verify(root: u64, index: usize, leaf: u64, proof: &[u64]) -> bool {
        // The tree has 2^(path length) leaves.
        let n = 1usize << proof.len();
        let mut pos = n + index;
        let mut current = leaf;

        for &sibling in proof {
            current = if pos & 1 == 0 {
                // pos is a left child (even): parent = hash(pos, sibling)
                hash_pair(current, sibling)
            } else {
                // pos is a right child (odd): parent = hash(sibling, pos)
                hash_pair(sibling, current)
            };
            pos >>= 1;
        }

        current == root
    }
}

// ── Commitment API ────────────────────────────────────────────────────────────

/// Commitment to a polynomial: the Merkle root over the evaluation codeword.
pub struct Commitment {
    /// Merkle root (= polynomial commitment).
    pub root: u64,
    /// Number of original (pre-padding) evaluation points.
    pub size: usize,
}

/// Opening proof for a single position in the evaluation codeword.
pub struct OpeningProof {
    /// Index into the evaluation vector.
    pub index: usize,
    /// Hash of the revealed field element at `index`.
    pub value_hash: u64,
    /// Merkle authentication path (sibling hashes, leaf → root direction).
    pub path: Vec<u64>,
}

/// Commit to a polynomial by hashing its Reed-Solomon evaluation codeword
/// and building a Merkle tree over those hashes.
///
/// `evaluations` = `[f(d₀), f(d₁), ..., f(d_{n-1})]` over a blow-up domain.
///
/// Returns the commitment (root + size) and the full Merkle tree (needed for
/// `open`).
///
/// # Panics
/// Panics if `evaluations` is empty.
pub fn commit<F: Field + Hash>(evaluations: &[F]) -> (Commitment, MerkleTree) {
    assert!(!evaluations.is_empty(), "commit: evaluations must not be empty");

    let leaf_hashes: Vec<u64> = evaluations.iter().map(hash_field_element).collect();
    let size = evaluations.len();
    let tree = MerkleTree::new(leaf_hashes);
    let commitment = Commitment { root: tree.root(), size };

    (commitment, tree)
}

/// Open the commitment at a given evaluation index.
///
/// Returns the hash of `evaluations[index]` together with the Merkle
/// authentication path needed to verify it against the commitment.
///
/// # Panics
/// Panics if `index >= evaluations.len()`.
pub fn open<F: Field + Hash>(
    tree: &MerkleTree,
    index: usize,
    evaluations: &[F],
) -> OpeningProof {
    assert!(
        index < evaluations.len(),
        "open: index {index} out of bounds (evaluations: {})",
        evaluations.len()
    );

    OpeningProof {
        index,
        value_hash: hash_field_element(&evaluations[index]),
        path: tree.proof(index),
    }
}

/// Verify an opening proof against a commitment.
pub fn verify_opening(commitment: &Commitment, proof: &OpeningProof) -> bool {
    MerkleTree::verify(commitment.root, proof.index, proof.value_hash, &proof.path)
}

// ── Tests ─────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use ark_bls12_381::Fr as Fp;
    use ark_poly::{EvaluationDomain, Radix2EvaluationDomain};
    use crate::polynomial::evaluate_on_domain;

    /// f(x) = 1 + 2x evaluated over 4 roots of unity (BLS12-381 Fr).
    fn sample_evals() -> Vec<Fp> {
        let coeffs = vec![Fp::from(1u64), Fp::from(2u64)];
        let domain = Radix2EvaluationDomain::<Fp>::new(4).unwrap();
        let points: Vec<Fp> = domain.elements().collect();
        evaluate_on_domain(&coeffs, &points)
    }

    // ── hash primitives ───────────────────────────────────────────────────────

    #[test]
    fn test_hash_pair_order_matters() {
        // hash_pair is not commutative — left ≠ right must give different results
        assert_ne!(hash_pair(1, 2), hash_pair(2, 1));
    }

    // ── MerkleTree construction ───────────────────────────────────────────────

    #[test]
    fn test_merkle_tree_root_deterministic() {
        let hashes = vec![1u64, 2, 3, 4];
        let t1 = MerkleTree::new(hashes.clone());
        let t2 = MerkleTree::new(hashes);
        assert_eq!(t1.root(), t2.root(), "same input must produce the same root");
    }

    #[test]
    fn test_merkle_tree_four_leaves_structure() {
        // 4 leaves → nodes has 8 slots (1-indexed); root = hash_pair(hash_pair(h0,h1), hash_pair(h2,h3))
        let leaves = vec![10u64, 20, 30, 40];
        let tree = MerkleTree::new(leaves);

        assert_eq!(tree.leaves.len(), 4);
        assert_eq!(tree.nodes.len(), 8);

        let l = hash_pair(10, 20);
        let r = hash_pair(30, 40);
        assert_eq!(tree.root(), hash_pair(l, r));
    }

    #[test]
    fn test_merkle_tree_pads_to_power_of_two() {
        // 3 leaves → padded to 4
        let tree = MerkleTree::new(vec![1u64, 2, 3]);
        assert_eq!(tree.leaves.len(), 4);
        assert_eq!(tree.leaves[3], 0u64, "padding should be zero");
    }

    #[test]
    fn test_merkle_single_leaf() {
        // n=1: root = the leaf itself, proof is empty
        let tree = MerkleTree::new(vec![42u64]);
        assert_eq!(tree.root(), 42u64);
        assert_eq!(tree.proof(0), Vec::<u64>::new());
        assert!(MerkleTree::verify(42u64, 0, 42u64, &[]));
    }

    #[test]
    fn test_merkle_two_leaves() {
        let tree = MerkleTree::new(vec![7u64, 13]);
        let expected_root = hash_pair(7, 13);
        assert_eq!(tree.root(), expected_root);

        // index 0: sibling = 13
        let p0 = tree.proof(0);
        assert_eq!(p0, vec![13u64]);
        assert!(MerkleTree::verify(expected_root, 0, 7, &p0));

        // index 1: sibling = 7
        let p1 = tree.proof(1);
        assert_eq!(p1, vec![7u64]);
        assert!(MerkleTree::verify(expected_root, 1, 13, &p1));
    }

    // ── open / verify ─────────────────────────────────────────────────────────

    #[test]
    fn test_merkle_open_verify_passes() {
        let leaves = vec![10u64, 20, 30, 40];
        let tree = MerkleTree::new(leaves.clone());
        let root = tree.root();

        for index in 0..4 {
            let path = tree.proof(index);
            assert!(
                MerkleTree::verify(root, index, leaves[index], &path),
                "valid proof for index {index} should verify"
            );
        }
    }

    #[test]
    fn test_merkle_verify_wrong_index_fails() {
        let leaves = vec![10u64, 20, 30, 40];
        let tree = MerkleTree::new(leaves.clone());
        let root = tree.root();

        // proof built for index 0, claimed to be for index 1
        let path = tree.proof(0);
        assert!(
            !MerkleTree::verify(root, 1, leaves[0], &path),
            "proof for index 0 should not verify at index 1"
        );
    }

    #[test]
    fn test_merkle_verify_wrong_value_fails() {
        let leaves = vec![10u64, 20, 30, 40];
        let tree = MerkleTree::new(leaves.clone());
        let root = tree.root();

        let path = tree.proof(2);
        let tampered = leaves[2].wrapping_add(1);
        assert!(
            !MerkleTree::verify(root, 2, tampered, &path),
            "tampered leaf hash should not verify"
        );
    }

    // ── commit / open / verify_opening (field element API) ───────────────────

    #[test]
    fn test_commit_open_api() {
        let evals = sample_evals();
        let (commitment, tree) = commit(&evals);

        assert_eq!(commitment.size, evals.len());

        // Every index must open and verify
        for i in 0..evals.len() {
            let proof = open(&tree, i, &evals);
            assert_eq!(proof.index, i);
            assert_eq!(proof.value_hash, hash_field_element(&evals[i]));
            assert!(
                verify_opening(&commitment, &proof),
                "opening at index {i} should verify"
            );
        }
    }

    #[test]
    fn test_commit_deterministic() {
        let evals = sample_evals();
        let (c1, _) = commit(&evals);
        let (c2, _) = commit(&evals);
        assert_eq!(c1.root, c2.root, "same evaluations must commit to the same root");
    }

    #[test]
    fn test_opening_tampered_value_fails() {
        let evals = sample_evals();
        let (commitment, tree) = commit(&evals);

        let mut proof = open(&tree, 0, &evals);
        proof.value_hash = proof.value_hash.wrapping_add(1); // tamper
        assert!(
            !verify_opening(&commitment, &proof),
            "tampered value_hash should fail verification"
        );
    }
}
