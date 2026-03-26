//! SHA-256 Merkle tree based polynomial commitment for RedShift.
//!
//! Workflow:
//! 1. Evaluate `f` over a coset domain → Reed-Solomon codeword
//! 2. Hash each field element with SHA-256: `leaf_i = SHA256(bytes(f(d_i)))`
//! 3. Build a Merkle tree over the leaves → `root = commitment`
//! 4. Open at index `i`: reveal `f(d_i)` + Merkle authentication path
//!
//! Using SHA-256 (instead of `DefaultHasher`) gives collision resistance and
//! deterministic behaviour across platforms and Rust versions.
//!
//! Field elements are serialised to bytes via
//! `PrimeField::into_bigint().to_bytes_le()` — the canonical little-endian
//! representation used throughout the arkworks ecosystem.

use sha2::{Digest, Sha256};
use ark_ff::{BigInteger, PrimeField};

// ── Hash primitives ───────────────────────────────────────────────────────────

/// SHA-256 hash of arbitrary bytes → 32-byte digest.
///
/// Used for leaf nodes: `hash_leaf(&field_to_bytes(val))`.
pub fn hash_leaf(data: &[u8]) -> [u8; 32] {
    Sha256::digest(data).into()
}

/// SHA-256 of two 32-byte children concatenated → parent hash.
///
/// Left/right order is preserved so that `hash_nodes(l, r) ≠ hash_nodes(r, l)`.
pub fn hash_nodes(left: &[u8; 32], right: &[u8; 32]) -> [u8; 32] {
    let mut h = Sha256::new();
    h.update(left);
    h.update(right);
    h.finalize().into()
}

/// Serialise a prime-field element to canonical little-endian bytes.
fn field_to_bytes<F: PrimeField>(val: &F) -> Vec<u8> {
    val.into_bigint().to_bytes_le()
}

// ── MerkleTree ────────────────────────────────────────────────────────────────

/// Complete binary Merkle tree over 32-byte (SHA-256) hashes.
///
/// 1-indexed flat layout (n = padded leaf count, always a power of two):
///
/// ```text
/// nodes[1]              = root
/// nodes[2], nodes[3]    = children of root
/// nodes[n .. 2n-1]      = leaves
/// ```
///
/// Padding: if the original leaf count is not a power of two, the tree is
/// padded with `[0u8; 32]` to reach the next power of two.
pub struct MerkleTree {
    /// Leaf hashes (padded to next power of two with `[0u8; 32]`).
    pub leaves: Vec<[u8; 32]>,
    /// All nodes, 1-indexed (`nodes[0]` unused).
    pub nodes: Vec<[u8; 32]>,
}

impl MerkleTree {
    /// Build a Merkle tree from pre-computed leaf hashes.
    ///
    /// # Panics
    /// Panics if `leaf_hashes` is empty.
    pub fn new(leaf_hashes: Vec<[u8; 32]>) -> Self {
        assert!(!leaf_hashes.is_empty(), "MerkleTree: leaf_hashes must not be empty");

        let n = leaf_hashes.len().next_power_of_two();
        let mut leaves = leaf_hashes;
        leaves.resize(n, [0u8; 32]); // pad with zero-hash

        let mut nodes = vec![[0u8; 32]; 2 * n];

        // Place leaves at positions n … 2n-1
        for (i, h) in leaves.iter().enumerate() {
            nodes[n + i] = *h;
        }

        // Build internal nodes bottom-up
        for i in (1..n).rev() {
            nodes[i] = hash_nodes(&nodes[2 * i], &nodes[2 * i + 1]);
        }

        MerkleTree { leaves, nodes }
    }

    /// Return the Merkle root (= commitment).
    pub fn root(&self) -> [u8; 32] {
        self.nodes[1]
    }

    /// Generate an authentication path for the leaf at `index`.
    ///
    /// Returns sibling hashes from leaf level up to (but not including) root.
    /// Path length = `log₂(leaves.len())`.
    ///
    /// # Panics
    /// Panics if `index >= leaves.len()`.
    pub fn proof(&self, index: usize) -> Vec<[u8; 32]> {
        let n = self.leaves.len();
        assert!(index < n, "proof: index {index} out of bounds (tree has {n} leaves)");

        let mut path = Vec::new();
        let mut pos = n + index;
        while pos > 1 {
            path.push(self.nodes[pos ^ 1]); // sibling
            pos >>= 1;                       // parent
        }
        path
    }

    /// Verify an authentication path against a root.
    ///
    /// Re-derives the root from `leaf` and `proof`, then compares with `root`.
    pub fn verify(root: [u8; 32], index: usize, leaf: [u8; 32], proof: &[[u8; 32]]) -> bool {
        let n = 1usize << proof.len();
        let mut pos = n + index;
        let mut current = leaf;

        for sibling in proof {
            current = if pos & 1 == 0 {
                hash_nodes(&current, sibling)   // pos is left child
            } else {
                hash_nodes(sibling, &current)   // pos is right child
            };
            pos >>= 1;
        }

        current == root
    }
}

// ── Commitment API ────────────────────────────────────────────────────────────

/// Commitment to a polynomial: SHA-256 Merkle root over the codeword.
pub struct Commitment {
    /// Merkle root (32 bytes).
    pub root: [u8; 32],
    /// Number of original (pre-padding) evaluation points.
    pub size: usize,
}

/// Opening proof: the hash of a single codeword symbol + Merkle path.
pub struct OpeningProof {
    /// Index into the evaluation vector.
    pub index: usize,
    /// `SHA256(bytes(evaluations[index]))`.
    pub value_hash: [u8; 32],
    /// Merkle authentication path (sibling hashes, leaf → root).
    pub path: Vec<[u8; 32]>,
}

/// Commit to a polynomial by hashing its evaluation codeword into a Merkle tree.
///
/// # Panics
/// Panics if `evaluations` is empty.
pub fn commit<F: PrimeField>(evaluations: &[F]) -> (Commitment, MerkleTree) {
    assert!(!evaluations.is_empty(), "commit: evaluations must not be empty");

    let leaf_hashes: Vec<[u8; 32]> = evaluations
        .iter()
        .map(|v| hash_leaf(&field_to_bytes(v)))
        .collect();
    let size = evaluations.len();
    let tree = MerkleTree::new(leaf_hashes);
    let commitment = Commitment { root: tree.root(), size };

    (commitment, tree)
}

/// Open the commitment at `index`.
///
/// # Panics
/// Panics if `index >= evaluations.len()`.
pub fn open<F: PrimeField>(
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
        value_hash: hash_leaf(&field_to_bytes(&evaluations[index])),
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

    /// Deterministic test hash from a single-byte seed.
    fn h(seed: u8) -> [u8; 32] {
        hash_leaf(&[seed])
    }

    /// f(x) = 1 + 2x evaluated over 4 roots of unity.
    fn sample_evals() -> Vec<Fp> {
        let coeffs = vec![Fp::from(1u64), Fp::from(2u64)];
        let domain = Radix2EvaluationDomain::<Fp>::new(4).unwrap();
        let points: Vec<Fp> = domain.elements().collect();
        evaluate_on_domain(&coeffs, &points)
    }

    // ── hash primitives ───────────────────────────────────────────────────────

    #[test]
    fn test_hash_nodes_order_matters() {
        // Merkle parent hash must be non-commutative
        let a = h(1);
        let b = h(2);
        assert_ne!(hash_nodes(&a, &b), hash_nodes(&b, &a));
    }

    #[test]
    fn test_hash_leaf_deterministic() {
        assert_eq!(hash_leaf(b"hello"), hash_leaf(b"hello"));
        assert_ne!(hash_leaf(b"hello"), hash_leaf(b"world"));
    }

    // ── MerkleTree construction ───────────────────────────────────────────────

    #[test]
    fn test_merkle_tree_root_deterministic() {
        let leaves = vec![h(1), h(2), h(3), h(4)];
        let t1 = MerkleTree::new(leaves.clone());
        let t2 = MerkleTree::new(leaves);
        assert_eq!(t1.root(), t2.root());
    }

    #[test]
    fn test_merkle_tree_four_leaves_structure() {
        // root = hash_nodes(hash_nodes(h0,h1), hash_nodes(h2,h3))
        let (l0, l1, l2, l3) = (h(10), h(20), h(30), h(40));
        let tree = MerkleTree::new(vec![l0, l1, l2, l3]);

        assert_eq!(tree.leaves.len(), 4);
        assert_eq!(tree.nodes.len(), 8); // 2*4 (1-indexed)

        let expected = hash_nodes(&hash_nodes(&l0, &l1), &hash_nodes(&l2, &l3));
        assert_eq!(tree.root(), expected);
    }

    #[test]
    fn test_merkle_tree_pads_to_power_of_two() {
        // 3 leaves → padded to 4
        let tree = MerkleTree::new(vec![h(1), h(2), h(3)]);
        assert_eq!(tree.leaves.len(), 4);
        assert_eq!(tree.leaves[3], [0u8; 32]);
    }

    #[test]
    fn test_merkle_single_leaf() {
        let leaf = h(42);
        let tree = MerkleTree::new(vec![leaf]);
        assert_eq!(tree.root(), leaf);
        assert!(tree.proof(0).is_empty());
        assert!(MerkleTree::verify(leaf, 0, leaf, &[]));
    }

    #[test]
    fn test_merkle_two_leaves() {
        let (l0, l1) = (h(7), h(13));
        let tree = MerkleTree::new(vec![l0, l1]);
        let expected_root = hash_nodes(&l0, &l1);
        assert_eq!(tree.root(), expected_root);

        // index 0: sibling = l1
        let p0 = tree.proof(0);
        assert_eq!(p0, vec![l1]);
        assert!(MerkleTree::verify(expected_root, 0, l0, &p0));

        // index 1: sibling = l0
        let p1 = tree.proof(1);
        assert_eq!(p1, vec![l0]);
        assert!(MerkleTree::verify(expected_root, 1, l1, &p1));
    }

    // ── open / verify ─────────────────────────────────────────────────────────

    #[test]
    fn test_merkle_open_verify_passes() {
        let leaves = vec![h(10), h(20), h(30), h(40)];
        let tree = MerkleTree::new(leaves.clone());
        let root = tree.root();

        for index in 0..4 {
            let path = tree.proof(index);
            assert!(
                MerkleTree::verify(root, index, leaves[index], &path),
                "valid proof at index {index} must verify"
            );
        }
    }

    #[test]
    fn test_merkle_verify_wrong_index_fails() {
        let leaves = vec![h(10), h(20), h(30), h(40)];
        let tree = MerkleTree::new(leaves.clone());
        let root = tree.root();

        // proof built for index 0, claimed for index 1
        let path = tree.proof(0);
        assert!(!MerkleTree::verify(root, 1, leaves[0], &path));
    }

    #[test]
    fn test_merkle_verify_wrong_value_fails() {
        let leaves = vec![h(10), h(20), h(30), h(40)];
        let tree = MerkleTree::new(leaves);
        let root = tree.root();

        let path = tree.proof(2);
        let tampered = h(99); // different from h(30)
        assert!(!MerkleTree::verify(root, 2, tampered, &path));
    }

    // ── commit / open / verify_opening (field element API) ───────────────────

    #[test]
    fn test_commit_open_api() {
        let evals = sample_evals();
        let (commitment, tree) = commit(&evals);
        assert_eq!(commitment.size, evals.len());

        for i in 0..evals.len() {
            let proof = open(&tree, i, &evals);
            assert_eq!(proof.index, i);
            assert_eq!(proof.value_hash, hash_leaf(&field_to_bytes(&evals[i])));
            assert!(verify_opening(&commitment, &proof), "opening at index {i} must verify");
        }
    }

    #[test]
    fn test_commit_deterministic() {
        let evals = sample_evals();
        let (c1, _) = commit(&evals);
        let (c2, _) = commit(&evals);
        assert_eq!(c1.root, c2.root);
    }

    #[test]
    fn test_opening_tampered_value_fails() {
        let evals = sample_evals();
        let (commitment, tree) = commit(&evals);
        let mut proof = open(&tree, 0, &evals);
        proof.value_hash = h(0xff); // tamper
        assert!(!verify_opening(&commitment, &proof));
    }
}
