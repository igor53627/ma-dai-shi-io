//! Somewhere Extractable Hash (SEH) implementation
//!
//! Based on the Hubáček-Wichs construction, adapted for Ma-Dai-Shi.
//! SEH is a Merkle-tree-like structure over FHE ciphertexts that supports:
//!
//! - `Hash`: Compute a digest of a sequence of values
//! - `Open`: Create an opening proof for a specific position
//! - `Verify`: Check that an opening is valid
//! - `ConsisP/ConsisV`: Prove/verify prefix consistency between two digests
//!
//! ## Security
//!
//! Relies on LWE-based FHE for the "somewhere extractable" property.

use super::fhe::{FheCiphertext, FheParams, FheScheme, StubFhe};
use sha2::{Digest, Sha256};

/// SEH parameters
#[derive(Clone, Debug)]
pub struct SehParams {
    /// Number of elements to hash
    pub num_elements: usize,
    /// Tree arity (typically 2 for binary tree)
    pub arity: usize,
    /// FHE parameters for ciphertext encryption
    pub fhe_params: FheParams,
}

impl Default for SehParams {
    fn default() -> Self {
        Self {
            num_elements: 16,
            arity: 2,
            fhe_params: FheParams::default(),
        }
    }
}

/// SEH digest (root hash)
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SehDigest {
    /// Root hash value
    pub root: [u8; 32],
    /// Height of the Merkle tree
    pub height: usize,
}

/// SEH opening for a specific position
#[derive(Clone, Debug)]
pub struct SehOpening {
    /// Position being opened
    pub position: usize,
    /// Leaf value (FHE ciphertext of the element)
    pub leaf_ciphertext: FheCiphertext,
    /// Sibling hashes along the path to the root
    pub sibling_hashes: Vec<[u8; 32]>,
}

/// SEH prefix consistency proof
#[derive(Clone, Debug)]
pub struct SehProof {
    /// Common prefix nodes
    pub common_nodes: Vec<[u8; 32]>,
    /// Depth at which the proofs diverge
    pub diverge_depth: usize,
}

/// Trait for Somewhere Extractable Hash schemes
pub trait SehScheme: Clone {
    /// FHE scheme used for ciphertext leaves
    type Fhe: FheScheme;

    /// Generate SEH parameters
    fn gen(&self, params: &SehParams) -> SehParams;

    /// Hash a sequence of boolean values
    fn hash(&self, params: &SehParams, values: &[bool]) -> (SehDigest, Vec<FheCiphertext>);

    /// Open the hash at a specific position
    fn open(
        &self,
        params: &SehParams,
        values: &[bool],
        ciphertexts: &[FheCiphertext],
        position: usize,
    ) -> SehOpening;

    /// Verify an opening against a digest
    fn verify(&self, params: &SehParams, digest: &SehDigest, opening: &SehOpening) -> bool;

    /// Create a prefix consistency proof between two digests
    fn consis_prove(
        &self,
        params: &SehParams,
        digest1: &SehDigest,
        digest2: &SehDigest,
        prefix_len: usize,
    ) -> SehProof;

    /// Verify a prefix consistency proof
    fn consis_verify(
        &self,
        params: &SehParams,
        digest1: &SehDigest,
        digest2: &SehDigest,
        proof: &SehProof,
    ) -> bool;
}

/// Stub SEH implementation using simple Merkle tree
///
/// WARNING: This is a simplified implementation for development.
/// A production version would use FHE ciphertexts at leaves.
#[derive(Clone, Debug)]
pub struct StubSeh {
    fhe: StubFhe,
}

impl Default for StubSeh {
    fn default() -> Self {
        Self::new()
    }
}

impl StubSeh {
    pub fn new() -> Self {
        Self { fhe: StubFhe }
    }

    #[allow(dead_code)]
    fn compute_tree_height(num_elements: usize) -> usize {
        if num_elements <= 1 {
            return 0;
        }
        let mut height = 0;
        let mut size = 1;
        while size < num_elements {
            size *= 2;
            height += 1;
        }
        height
    }

    fn hash_pair(left: &[u8; 32], right: &[u8; 32]) -> [u8; 32] {
        let mut hasher = Sha256::new();
        hasher.update(left);
        hasher.update(right);
        hasher.finalize().into()
    }

    fn build_tree(&self, leaves: &[[u8; 32]]) -> Vec<Vec<[u8; 32]>> {
        let mut layers = vec![leaves.to_vec()];

        while layers.last().map(|l| l.len()).unwrap_or(0) > 1 {
            let prev_layer = layers.last().unwrap();
            let mut new_layer = Vec::new();

            for chunk in prev_layer.chunks(2) {
                let left = chunk[0];
                let right = if chunk.len() > 1 {
                    chunk[1]
                } else {
                    [0u8; 32]
                };
                new_layer.push(Self::hash_pair(&left, &right));
            }

            layers.push(new_layer);
        }

        layers
    }
}

impl SehScheme for StubSeh {
    type Fhe = StubFhe;

    fn gen(&self, params: &SehParams) -> SehParams {
        params.clone()
    }

    fn hash(&self, params: &SehParams, values: &[bool]) -> (SehDigest, Vec<FheCiphertext>) {
        let (_, pk) = self.fhe.keygen(&params.fhe_params);

        let ciphertexts: Vec<FheCiphertext> = values
            .iter()
            .map(|&v| self.fhe.encrypt_bit(&pk, v))
            .collect();

        let leaf_hashes: Vec<[u8; 32]> = ciphertexts
            .iter()
            .map(|ct| {
                let mut hasher = Sha256::new();
                hasher.update(&ct.data);
                hasher.finalize().into()
            })
            .collect();

        let padded_len = leaf_hashes.len().next_power_of_two();
        let mut padded_leaves = leaf_hashes;
        padded_leaves.resize(padded_len, [0u8; 32]);

        let tree = self.build_tree(&padded_leaves);
        let root = tree.last().and_then(|l| l.first()).copied().unwrap_or([0u8; 32]);
        let height = tree.len().saturating_sub(1);

        (SehDigest { root, height }, ciphertexts)
    }

    fn open(
        &self,
        params: &SehParams,
        _values: &[bool],
        ciphertexts: &[FheCiphertext],
        position: usize,
    ) -> SehOpening {
        let leaf_hashes: Vec<[u8; 32]> = ciphertexts
            .iter()
            .map(|ct| {
                let mut hasher = Sha256::new();
                hasher.update(&ct.data);
                hasher.finalize().into()
            })
            .collect();

        let padded_len = leaf_hashes.len().next_power_of_two();
        let mut padded_leaves = leaf_hashes;
        padded_leaves.resize(padded_len, [0u8; 32]);

        let tree = self.build_tree(&padded_leaves);

        let mut sibling_hashes = Vec::new();
        let mut idx = position;

        for layer in &tree[..tree.len().saturating_sub(1)] {
            let sibling_idx = if idx % 2 == 0 { idx + 1 } else { idx - 1 };
            let sibling = layer.get(sibling_idx).copied().unwrap_or([0u8; 32]);
            sibling_hashes.push(sibling);
            idx /= 2;
        }

        let leaf_ct = ciphertexts.get(position).cloned().unwrap_or_else(|| {
            let (_, pk) = self.fhe.keygen(&params.fhe_params);
            self.fhe.encrypt_bit(&pk, false)
        });

        SehOpening {
            position,
            leaf_ciphertext: leaf_ct,
            sibling_hashes,
        }
    }

    fn verify(&self, _params: &SehParams, digest: &SehDigest, opening: &SehOpening) -> bool {
        let mut hasher = Sha256::new();
        hasher.update(&opening.leaf_ciphertext.data);
        let mut current: [u8; 32] = hasher.finalize().into();

        let mut idx = opening.position;

        for sibling in &opening.sibling_hashes {
            current = if idx % 2 == 0 {
                Self::hash_pair(&current, sibling)
            } else {
                Self::hash_pair(sibling, &current)
            };
            idx /= 2;
        }

        current == digest.root
    }

    fn consis_prove(
        &self,
        _params: &SehParams,
        digest1: &SehDigest,
        digest2: &SehDigest,
        prefix_len: usize,
    ) -> SehProof {
        SehProof {
            common_nodes: vec![digest1.root, digest2.root],
            diverge_depth: prefix_len,
        }
    }

    fn consis_verify(
        &self,
        _params: &SehParams,
        digest1: &SehDigest,
        digest2: &SehDigest,
        proof: &SehProof,
    ) -> bool {
        proof.common_nodes.len() == 2
            && proof.common_nodes[0] == digest1.root
            && proof.common_nodes[1] == digest2.root
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_seh_hash_deterministic() {
        let seh = StubSeh::new();
        let params = SehParams::default();
        let values = vec![true, false, true, false];

        let (digest1, _) = seh.hash(&params, &values);
        let (digest2, _) = seh.hash(&params, &values);

        assert_eq!(digest1.root, digest2.root);
    }

    #[test]
    fn test_seh_open_verify() {
        let seh = StubSeh::new();
        let params = SehParams::default();
        let values = vec![true, false, true, false];

        let (digest, ciphertexts) = seh.hash(&params, &values);

        for pos in 0..values.len() {
            let opening = seh.open(&params, &values, &ciphertexts, pos);
            assert!(seh.verify(&params, &digest, &opening));
        }
    }

    #[test]
    fn test_seh_invalid_opening() {
        let seh = StubSeh::new();
        let params = SehParams::default();
        let values = vec![true, false, true, false];

        let (digest, ciphertexts) = seh.hash(&params, &values);
        let mut opening = seh.open(&params, &values, &ciphertexts, 0);

        opening.sibling_hashes[0] = [1u8; 32];

        assert!(!seh.verify(&params, &digest, &opening));
    }
}
