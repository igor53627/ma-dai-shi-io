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
//!
//! ## Genericity
//!
//! SEH is generic over the FHE scheme via `SehScheme<F: FheScheme>`.
//! The default implementation uses `DefaultFhe` which switches between
//! `StubFhe` (fast, insecure) and `TfheFhe` (real LWE) based on cargo features.

use super::fhe::{DefaultFhe, FheCiphertext, FheParams, FheScheme, StubFhe};
use sha2::{Digest, Sha256};
use std::fmt::Debug;

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

/// SEH digest (root hash with internal tree structure)
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SehDigest {
    /// Root hash value
    pub root: [u8; 32],
    /// Height of the Merkle tree
    pub height: usize,
    /// Internal Merkle tree layers (layer 0 = leaves, last = root)
    /// Stored for prefix consistency proofs
    pub tree_layers: Vec<Vec<[u8; 32]>>,
}

/// SEH opening for a specific position (generic over ciphertext type)
#[derive(Clone, Debug)]
pub struct SehOpening<Ct: Clone + Debug> {
    /// Position being opened
    pub position: usize,
    /// Leaf value (FHE ciphertext of the element)
    pub leaf_ciphertext: Ct,
    /// Sibling hashes along the path to the root
    pub sibling_hashes: Vec<[u8; 32]>,
}

/// Merkle authentication path for a single position
#[derive(Clone, Debug)]
pub struct MerklePath {
    /// Position this path authenticates
    pub position: usize,
    /// Sibling hashes from leaf to root
    pub siblings: Vec<[u8; 32]>,
}

/// SEH prefix consistency proof
///
/// Proves that two SEH digests share the same values for positions 0..prefix_len.
/// Uses Merkle paths to demonstrate that the subtrees covering the prefix are identical.
#[derive(Clone, Debug)]
pub struct SehProof {
    /// Length of the shared prefix
    pub prefix_len: usize,
    /// Hash of the subtree covering the prefix (should match in both trees)
    pub prefix_subtree_hash: [u8; 32],
    /// Merkle path from prefix subtree to root in digest1
    pub path_to_root1: Vec<[u8; 32]>,
    /// Merkle path from prefix subtree to root in digest2
    pub path_to_root2: Vec<[u8; 32]>,
}

/// Trait for converting ciphertexts to bytes for hashing
pub trait CiphertextBytes {
    fn to_bytes(&self) -> Vec<u8>;
}

// ============================================================================
// Multi-Level Key Hierarchy (Ma-Dai-Shi Section 4.2)
// ============================================================================

/// A single level's FHE key pair in the SEH hierarchy
///
/// In Ma-Dai-Shi's construction, each tree level has its own key pair.
/// Level 0 keys encrypt leaves, level h keys are for the root.
#[derive(Clone, Debug)]
pub struct SehLevelKey<F: FheScheme> {
    /// Secret key for this level (used for extraction)
    pub sk: F::SecretKey,
    /// Public key for this level (used for encryption)
    pub pk: F::PublicKey,
}

/// Multi-level key hierarchy for SEH
///
/// Stores independent FHE key pairs for each tree level, enabling
/// the "somewhere extractable" property where extraction at one
/// position doesn't reveal other positions.
///
/// ## Usage
///
/// ```ignore
/// let seh = GenericSeh::<StubFhe>::default();
/// let params = SehParams::default();
/// let keys = seh.gen_key_hierarchy(&params);
///
/// // Use multi-key hash
/// let (digest, cts) = seh.hash_multikey(&params, &keys, &values);
/// ```
#[derive(Clone, Debug)]
pub struct SehKeyHierarchy<F: FheScheme> {
    /// Key pairs per level: level 0 = leaves, level h = root
    pub levels: Vec<SehLevelKey<F>>,
}

impl<F: FheScheme> SehKeyHierarchy<F> {
    /// Get the number of levels in the hierarchy
    pub fn height(&self) -> usize {
        self.levels.len().saturating_sub(1)
    }

    /// Get the leaf-level (level 0) public key
    pub fn leaf_pk(&self) -> Option<&F::PublicKey> {
        self.levels.first().map(|k| &k.pk)
    }

    /// Get the root-level public key
    pub fn root_pk(&self) -> Option<&F::PublicKey> {
        self.levels.last().map(|k| &k.pk)
    }
}

/// Routing ciphertexts for SEH extraction (placeholder for future use)
///
/// In the full Ma-Dai-Shi construction, routing ciphertexts contain
/// encrypted decryption keys that allow an extractor to "follow" a
/// path from root to leaf while keeping the path hidden.
///
/// ## Current Status
///
/// This is a placeholder structure. The current SEH implementation
/// doesn't use routing for extraction - it's here to prepare for
/// future full Ma-Dai-Shi compliance.
#[derive(Clone, Debug)]
pub struct SehRouting<F: FheScheme> {
    /// Routing ciphertexts per level and node
    /// routing[level][node_index] = encrypted key material for children
    pub routing: Vec<Vec<Vec<F::Ciphertext>>>,
}

impl<F: FheScheme> Default for SehRouting<F> {
    fn default() -> Self {
        Self {
            routing: Vec::new(),
        }
    }
}

impl<F: FheScheme> SehRouting<F> {
    /// Check if routing data is populated
    pub fn is_empty(&self) -> bool {
        self.routing.is_empty()
    }
}

impl CiphertextBytes for FheCiphertext {
    fn to_bytes(&self) -> Vec<u8> {
        self.data.clone()
    }
}

#[cfg(feature = "tfhe-backend")]
impl CiphertextBytes for super::fhe::TfheCiphertextWrapper {
    fn to_bytes(&self) -> Vec<u8> {
        bincode::serialize(&self.0).expect("tfhe ciphertext serialization failed")
    }
}

/// Trait for Somewhere Extractable Hash schemes (generic over FHE)
pub trait SehScheme<F: FheScheme>: Clone
where
    F::Ciphertext: CiphertextBytes,
{
    /// Generate SEH parameters
    fn gen(&self, params: &SehParams) -> SehParams;

    /// Hash a sequence of boolean values
    fn hash(&self, params: &SehParams, values: &[bool]) -> (SehDigest, Vec<F::Ciphertext>);

    /// Open the hash at a specific position
    fn open(
        &self,
        params: &SehParams,
        values: &[bool],
        ciphertexts: &[F::Ciphertext],
        position: usize,
    ) -> SehOpening<F::Ciphertext>;

    /// Verify an opening against a digest
    fn verify(
        &self,
        params: &SehParams,
        digest: &SehDigest,
        opening: &SehOpening<F::Ciphertext>,
    ) -> bool;

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

/// Generic SEH implementation using Merkle tree over FHE ciphertexts
///
/// This implementation works with any FHE backend that implements `FheScheme`
/// and whose ciphertexts implement `CiphertextBytes`.
#[derive(Clone, Debug)]
pub struct GenericSeh<F: FheScheme> {
    fhe: F,
}

impl<F: FheScheme + Default> Default for GenericSeh<F> {
    fn default() -> Self {
        Self::new(F::default())
    }
}

impl<F: FheScheme> GenericSeh<F> {
    pub fn new(fhe: F) -> Self {
        Self { fhe }
    }

    /// Compute the height of a binary Merkle tree for n elements
    pub fn compute_tree_height(num_elements: usize) -> usize {
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

    fn build_tree(leaves: &[[u8; 32]]) -> Vec<Vec<[u8; 32]>> {
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

    // ========================================================================
    // Multi-Key Hierarchy Methods (Ma-Dai-Shi Section 4.2)
    // ========================================================================

    /// Generate a multi-level key hierarchy for SEH
    ///
    /// Creates independent FHE key pairs for each tree level (0 to height).
    /// Level 0 is for leaves, higher levels are for internal nodes.
    ///
    /// This enables the "somewhere extractable" property from Ma-Dai-Shi
    /// Section 4.2, where extraction at one position doesn't reveal others.
    pub fn gen_key_hierarchy(&self, params: &SehParams) -> SehKeyHierarchy<F> {
        let height = Self::compute_tree_height(params.num_elements);
        let mut levels = Vec::with_capacity(height + 1);

        for _ in 0..=height {
            let (sk, pk) = self.fhe.keygen(&params.fhe_params);
            levels.push(SehLevelKey { sk, pk });
        }

        SehKeyHierarchy { levels }
    }

    /// Hash values using a multi-level key hierarchy
    ///
    /// Uses the leaf-level key (level 0) for encrypting values.
    /// The resulting digest and ciphertexts are compatible with the
    /// standard `open`/`verify` methods.
    ///
    /// ## Difference from `hash()`
    ///
    /// - `hash()`: Generates a fresh single key pair internally
    /// - `hash_multikey()`: Uses the provided key hierarchy
    ///
    /// This allows the caller to retain the key hierarchy for future
    /// extraction operations (when implemented).
    pub fn hash_multikey(
        &self,
        _params: &SehParams,
        keys: &SehKeyHierarchy<F>,
        values: &[bool],
    ) -> (SehDigest, Vec<F::Ciphertext>)
    where
        F::Ciphertext: CiphertextBytes,
    {
        let pk_leaf = keys
            .leaf_pk()
            .expect("key hierarchy must have at least one level");

        let ciphertexts: Vec<F::Ciphertext> = values
            .iter()
            .map(|&v| self.fhe.encrypt_bit(pk_leaf, v))
            .collect();

        self.hash_from_ciphertexts(&ciphertexts)
    }

    /// Hash values with multi-key hierarchy and routing data (placeholder)
    ///
    /// This prepares for full Ma-Dai-Shi SEH compliance by returning
    /// routing ciphertexts alongside the digest. Currently, the routing
    /// structure is empty - it will be populated when extraction is implemented.
    pub fn hash_multikey_with_routing(
        &self,
        params: &SehParams,
        keys: &SehKeyHierarchy<F>,
        values: &[bool],
    ) -> (SehDigest, Vec<F::Ciphertext>, SehRouting<F>)
    where
        F::Ciphertext: CiphertextBytes,
    {
        let (digest, ciphertexts) = self.hash_multikey(params, keys, values);

        let routing = SehRouting::default();

        (digest, ciphertexts, routing)
    }

    /// Build digest from pre-encrypted ciphertexts
    ///
    /// Internal helper that builds the Merkle tree from ciphertexts
    /// without generating new keys.
    fn hash_from_ciphertexts(&self, ciphertexts: &[F::Ciphertext]) -> (SehDigest, Vec<F::Ciphertext>)
    where
        F::Ciphertext: CiphertextBytes,
    {
        let leaf_hashes: Vec<[u8; 32]> = ciphertexts
            .iter()
            .map(|ct| {
                let mut hasher = Sha256::new();
                hasher.update(&ct.to_bytes());
                hasher.finalize().into()
            })
            .collect();

        let padded_len = leaf_hashes.len().next_power_of_two();
        let mut padded_leaves = leaf_hashes;
        padded_leaves.resize(padded_len, [0u8; 32]);

        let tree = Self::build_tree(&padded_leaves);
        let root = tree
            .last()
            .and_then(|l| l.first())
            .copied()
            .unwrap_or([0u8; 32]);
        let height = tree.len().saturating_sub(1);

        (
            SehDigest {
                root,
                height,
                tree_layers: tree,
            },
            ciphertexts.to_vec(),
        )
    }
}

impl<F> SehScheme<F> for GenericSeh<F>
where
    F: FheScheme + Clone,
    F::Ciphertext: CiphertextBytes,
{
    fn gen(&self, params: &SehParams) -> SehParams {
        params.clone()
    }

    fn hash(&self, params: &SehParams, values: &[bool]) -> (SehDigest, Vec<F::Ciphertext>) {
        let (_, pk) = self.fhe.keygen(&params.fhe_params);

        let ciphertexts: Vec<F::Ciphertext> = values
            .iter()
            .map(|&v| self.fhe.encrypt_bit(&pk, v))
            .collect();

        let leaf_hashes: Vec<[u8; 32]> = ciphertexts
            .iter()
            .map(|ct| {
                let mut hasher = Sha256::new();
                hasher.update(&ct.to_bytes());
                hasher.finalize().into()
            })
            .collect();

        let padded_len = leaf_hashes.len().next_power_of_two();
        let mut padded_leaves = leaf_hashes;
        padded_leaves.resize(padded_len, [0u8; 32]);

        let tree = Self::build_tree(&padded_leaves);
        let root = tree
            .last()
            .and_then(|l| l.first())
            .copied()
            .unwrap_or([0u8; 32]);
        let height = tree.len().saturating_sub(1);

        (
            SehDigest {
                root,
                height,
                tree_layers: tree,
            },
            ciphertexts,
        )
    }

    fn open(
        &self,
        _params: &SehParams,
        _values: &[bool],
        ciphertexts: &[F::Ciphertext],
        position: usize,
    ) -> SehOpening<F::Ciphertext> {
        let leaf_hashes: Vec<[u8; 32]> = ciphertexts
            .iter()
            .map(|ct| {
                let mut hasher = Sha256::new();
                hasher.update(&ct.to_bytes());
                hasher.finalize().into()
            })
            .collect();

        let padded_len = leaf_hashes.len().next_power_of_two();
        let mut padded_leaves = leaf_hashes;
        padded_leaves.resize(padded_len, [0u8; 32]);

        let tree = Self::build_tree(&padded_leaves);

        let mut sibling_hashes = Vec::new();
        let mut idx = position;

        for layer in &tree[..tree.len().saturating_sub(1)] {
            let sibling_idx = if idx % 2 == 0 { idx + 1 } else { idx - 1 };
            let sibling = layer.get(sibling_idx).copied().unwrap_or([0u8; 32]);
            sibling_hashes.push(sibling);
            idx /= 2;
        }

        let leaf_ct = ciphertexts
            .get(position)
            .cloned()
            .unwrap_or_else(|| {
                panic!(
                    "SEH open: position {} out of bounds (len={})",
                    position,
                    ciphertexts.len()
                )
            });

        SehOpening {
            position,
            leaf_ciphertext: leaf_ct,
            sibling_hashes,
        }
    }

    fn verify(
        &self,
        _params: &SehParams,
        digest: &SehDigest,
        opening: &SehOpening<F::Ciphertext>,
    ) -> bool {
        let mut hasher = Sha256::new();
        hasher.update(&opening.leaf_ciphertext.to_bytes());
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
        if prefix_len == 0 || digest1.tree_layers.is_empty() || digest2.tree_layers.is_empty() {
            return SehProof {
                prefix_len: 0,
                prefix_subtree_hash: [0u8; 32],
                path_to_root1: vec![],
                path_to_root2: vec![],
            };
        }

        // Find the level where prefix_len leaves form a complete subtree
        // For a prefix of length n, we need to find the smallest subtree containing positions 0..n
        let prefix_len_padded = prefix_len.next_power_of_two();
        let subtree_level = (prefix_len_padded as f64).log2().ceil() as usize;

        // Get the hash of the prefix subtree from both trees
        // At level `subtree_level`, the first node covers positions 0..prefix_len_padded
        let prefix_hash1 = digest1
            .tree_layers
            .get(subtree_level)
            .and_then(|layer| layer.first())
            .copied()
            .unwrap_or([0u8; 32]);

        let _prefix_hash2 = digest2
            .tree_layers
            .get(subtree_level)
            .and_then(|layer| layer.first())
            .copied()
            .unwrap_or([0u8; 32]);

        // If prefix subtrees don't match, the proof will fail verification
        // We still generate it - verification will catch the mismatch

        // Collect sibling path from subtree level to root for digest1
        let mut path1 = Vec::new();
        let mut idx = 0usize; // We're at position 0 of the subtree level
        for level in subtree_level..digest1.height {
            let sibling_idx = if idx % 2 == 0 { idx + 1 } else { idx - 1 };
            let sibling = digest1
                .tree_layers
                .get(level)
                .and_then(|layer| layer.get(sibling_idx))
                .copied()
                .unwrap_or([0u8; 32]);
            path1.push(sibling);
            idx /= 2;
        }

        // Collect sibling path from subtree level to root for digest2
        let mut path2 = Vec::new();
        idx = 0;
        for level in subtree_level..digest2.height {
            let sibling_idx = if idx % 2 == 0 { idx + 1 } else { idx - 1 };
            let sibling = digest2
                .tree_layers
                .get(level)
                .and_then(|layer| layer.get(sibling_idx))
                .copied()
                .unwrap_or([0u8; 32]);
            path2.push(sibling);
            idx /= 2;
        }

        SehProof {
            prefix_len,
            prefix_subtree_hash: prefix_hash1,
            path_to_root1: path1,
            path_to_root2: path2,
        }
    }

    fn consis_verify(
        &self,
        _params: &SehParams,
        digest1: &SehDigest,
        digest2: &SehDigest,
        proof: &SehProof,
    ) -> bool {
        if proof.prefix_len == 0 {
            return true; // Empty prefix is trivially consistent
        }

        // Verify that the prefix subtree hash, combined with path1, produces digest1.root
        let mut current = proof.prefix_subtree_hash;
        let mut idx = 0usize;
        for sibling in &proof.path_to_root1 {
            current = if idx % 2 == 0 {
                Self::hash_pair(&current, sibling)
            } else {
                Self::hash_pair(sibling, &current)
            };
            idx /= 2;
        }
        if current != digest1.root {
            return false;
        }

        // Verify that the same prefix subtree hash, combined with path2, produces digest2.root
        current = proof.prefix_subtree_hash;
        idx = 0;
        for sibling in &proof.path_to_root2 {
            current = if idx % 2 == 0 {
                Self::hash_pair(&current, sibling)
            } else {
                Self::hash_pair(sibling, &current)
            };
            idx /= 2;
        }
        if current != digest2.root {
            return false;
        }

        // Also verify the prefix subtree hash matches what's stored in both digests
        let prefix_len_padded = proof.prefix_len.next_power_of_two();
        let subtree_level = (prefix_len_padded as f64).log2().ceil() as usize;

        let stored_hash1 = digest1
            .tree_layers
            .get(subtree_level)
            .and_then(|layer| layer.first())
            .copied();

        let stored_hash2 = digest2
            .tree_layers
            .get(subtree_level)
            .and_then(|layer| layer.first())
            .copied();

        match (stored_hash1, stored_hash2) {
            (Some(h1), Some(h2)) => {
                h1 == proof.prefix_subtree_hash && h2 == proof.prefix_subtree_hash
            }
            _ => false,
        }
    }
}

/// Type alias for SEH using the stub FHE backend (backward compatible)
pub type StubSeh = GenericSeh<StubFhe>;

/// Type alias for SEH using the default FHE backend
pub type DefaultSeh = GenericSeh<DefaultFhe>;

/// Legacy SehOpening type alias for backward compatibility
pub type StubSehOpening = SehOpening<FheCiphertext>;

impl StubSeh {
    #[deprecated(note = "Use GenericSeh::new(StubFhe) or StubSeh::default() instead")]
    pub fn new_legacy() -> Self {
        Self::new(StubFhe)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_seh_hash_deterministic() {
        let seh = StubSeh::default();
        let params = SehParams::default();
        let values = vec![true, false, true, false];

        let (digest1, _) = SehScheme::hash(&seh, &params, &values);
        let (digest2, _) = SehScheme::hash(&seh, &params, &values);

        assert_eq!(digest1.root, digest2.root);
    }

    #[test]
    fn test_seh_open_verify() {
        let seh = StubSeh::default();
        let params = SehParams::default();
        let values = vec![true, false, true, false];

        let (digest, ciphertexts) = SehScheme::hash(&seh, &params, &values);

        for pos in 0..values.len() {
            let opening = SehScheme::open(&seh, &params, &values, &ciphertexts, pos);
            assert!(SehScheme::verify(&seh, &params, &digest, &opening));
        }
    }

    #[test]
    fn test_seh_invalid_opening() {
        let seh = StubSeh::default();
        let params = SehParams::default();
        let values = vec![true, false, true, false];

        let (digest, ciphertexts) = SehScheme::hash(&seh, &params, &values);
        let mut opening = SehScheme::open(&seh, &params, &values, &ciphertexts, 0);

        opening.sibling_hashes[0] = [1u8; 32];

        assert!(!SehScheme::verify(&seh, &params, &digest, &opening));
    }

    #[test]
    fn test_default_seh_works() {
        let seh = DefaultSeh::default();
        let params = SehParams::default();
        let values = vec![true, false, true, false];

        let (digest, ciphertexts) = SehScheme::hash(&seh, &params, &values);
        let opening = SehScheme::open(&seh, &params, &values, &ciphertexts, 0);
        assert!(SehScheme::verify(&seh, &params, &digest, &opening));
    }

    #[test]
    fn test_seh_digest_stores_tree_layers() {
        let seh = StubSeh::default();
        let params = SehParams::default();
        let values = vec![true, false, true, false];

        let (digest, _) = SehScheme::hash(&seh, &params, &values);

        assert!(!digest.tree_layers.is_empty());
        assert_eq!(digest.tree_layers.last().unwrap().len(), 1);
        assert_eq!(digest.tree_layers.last().unwrap()[0], digest.root);
    }

    #[test]
    fn test_seh_prefix_consistency_same_values() {
        let seh = StubSeh::default();
        let params = SehParams::default();
        let values = vec![true, false, true, false];

        let (digest1, _) = SehScheme::hash(&seh, &params, &values);
        let (digest2, _) = SehScheme::hash(&seh, &params, &values);

        let proof = SehScheme::consis_prove(&seh, &params, &digest1, &digest2, 4);
        assert!(SehScheme::consis_verify(&seh, &params, &digest1, &digest2, &proof));
    }

    #[test]
    fn test_seh_prefix_consistency_shared_prefix() {
        let seh = StubSeh::default();
        let params = SehParams {
            num_elements: 8,
            ..Default::default()
        };

        // Two sequences that share the first 4 values
        let values1 = vec![true, false, true, false, true, true, false, false];
        let values2 = vec![true, false, true, false, false, false, true, true];

        let (digest1, _) = SehScheme::hash(&seh, &params, &values1);
        let (digest2, _) = SehScheme::hash(&seh, &params, &values2);

        // Prove consistency for prefix of length 4
        let proof = SehScheme::consis_prove(&seh, &params, &digest1, &digest2, 4);

        // Verification should succeed because prefix subtrees match
        assert!(SehScheme::consis_verify(
            &seh, &params, &digest1, &digest2, &proof
        ));
    }

    #[test]
    fn test_seh_prefix_consistency_different_prefix() {
        let seh = StubSeh::default();
        let params = SehParams {
            num_elements: 8,
            ..Default::default()
        };

        // Two sequences with different first value
        let values1 = vec![true, false, true, false, true, true, false, false];
        let values2 = vec![false, false, true, false, true, true, false, false];

        let (digest1, _) = SehScheme::hash(&seh, &params, &values1);
        let (digest2, _) = SehScheme::hash(&seh, &params, &values2);

        // Prove consistency for prefix of length 4 (but values differ)
        let proof = SehScheme::consis_prove(&seh, &params, &digest1, &digest2, 4);

        // Verification should fail because prefix subtrees don't match
        assert!(!SehScheme::consis_verify(
            &seh, &params, &digest1, &digest2, &proof
        ));
    }

    #[test]
    fn test_seh_prefix_consistency_empty() {
        let seh = StubSeh::default();
        let params = SehParams::default();
        let values1 = vec![true, false, true, false];
        let values2 = vec![false, true, false, true];

        let (digest1, _) = SehScheme::hash(&seh, &params, &values1);
        let (digest2, _) = SehScheme::hash(&seh, &params, &values2);

        // Empty prefix should always be consistent
        let proof = SehScheme::consis_prove(&seh, &params, &digest1, &digest2, 0);
        assert!(SehScheme::consis_verify(
            &seh, &params, &digest1, &digest2, &proof
        ));
    }

    #[test]
    fn test_seh_proof_contains_merkle_paths() {
        let seh = StubSeh::default();
        let params = SehParams {
            num_elements: 8,
            ..Default::default()
        };
        let values = vec![true, false, true, false, true, true, false, false];

        let (digest1, _) = SehScheme::hash(&seh, &params, &values);
        let (digest2, _) = SehScheme::hash(&seh, &params, &values);

        let proof = SehScheme::consis_prove(&seh, &params, &digest1, &digest2, 4);

        assert_eq!(proof.prefix_len, 4);
        assert_ne!(proof.prefix_subtree_hash, [0u8; 32]);
    }

    // ========================================================================
    // Multi-Key Hierarchy Tests (Issue #8)
    // ========================================================================

    #[test]
    fn test_gen_key_hierarchy_creates_correct_levels() {
        let seh = StubSeh::default();
        let params = SehParams {
            num_elements: 8,
            ..Default::default()
        };

        let keys = seh.gen_key_hierarchy(&params);

        let expected_height = GenericSeh::<StubFhe>::compute_tree_height(8);
        assert_eq!(keys.levels.len(), expected_height + 1);
        assert_eq!(keys.height(), expected_height);
    }

    #[test]
    fn test_key_hierarchy_accessors() {
        let seh = StubSeh::default();
        let params = SehParams {
            num_elements: 4,
            ..Default::default()
        };

        let keys = seh.gen_key_hierarchy(&params);

        assert!(keys.leaf_pk().is_some());
        assert!(keys.root_pk().is_some());
    }

    #[test]
    fn test_hash_multikey_produces_valid_digest() {
        let seh = StubSeh::default();
        let params = SehParams::default();
        let values = vec![true, false, true, false];

        let keys = seh.gen_key_hierarchy(&params);
        let (digest, ciphertexts) = seh.hash_multikey(&params, &keys, &values);

        assert!(!digest.tree_layers.is_empty());
        assert_eq!(ciphertexts.len(), values.len());

        for pos in 0..values.len() {
            let opening = SehScheme::open(&seh, &params, &values, &ciphertexts, pos);
            assert!(SehScheme::verify(&seh, &params, &digest, &opening));
        }
    }

    #[test]
    fn test_hash_multikey_with_routing_returns_empty_routing() {
        let seh = StubSeh::default();
        let params = SehParams::default();
        let values = vec![true, false, true, false];

        let keys = seh.gen_key_hierarchy(&params);
        let (digest, ciphertexts, routing) = seh.hash_multikey_with_routing(&params, &keys, &values);

        assert!(routing.is_empty());
        assert_eq!(ciphertexts.len(), values.len());
        assert!(!digest.tree_layers.is_empty());
    }

    #[test]
    fn test_multikey_digest_matches_standard_structure() {
        let seh = StubSeh::default();
        let params = SehParams::default();
        let values = vec![true, false, true, false];

        let keys = seh.gen_key_hierarchy(&params);
        let (multikey_digest, _) = seh.hash_multikey(&params, &keys, &values);

        assert_eq!(
            multikey_digest.tree_layers.last().unwrap()[0],
            multikey_digest.root
        );
    }

    #[test]
    fn test_multikey_same_hierarchy_same_values_same_digest() {
        let seh = StubSeh::default();
        let params = SehParams::default();
        let values = vec![true, false, true, false];

        let keys = seh.gen_key_hierarchy(&params);

        let (digest1, _) = seh.hash_multikey(&params, &keys, &values);
        let (digest2, _) = seh.hash_multikey(&params, &keys, &values);

        assert_eq!(digest1.root, digest2.root);
    }

    #[test]
    fn test_multikey_different_values_different_digest() {
        let seh = StubSeh::default();
        let params = SehParams::default();
        let values1 = vec![true, false, true, false];
        let values2 = vec![false, true, false, true];

        let keys = seh.gen_key_hierarchy(&params);

        let (digest1, _) = seh.hash_multikey(&params, &keys, &values1);
        let (digest2, _) = seh.hash_multikey(&params, &keys, &values2);

        assert_ne!(digest1.root, digest2.root);
    }
}
