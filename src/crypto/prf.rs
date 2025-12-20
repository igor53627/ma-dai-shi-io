//! Puncturable PRF implementation using GGM tree
//!
//! The GGM (Goldreich-Goldwasser-Micali) construction builds a PRF from a PRG.
//! It supports efficient puncturing: given a key and a point x, produce a
//! "punctured key" that can evaluate on all inputs except x.
//!
//! ## Usage in Ma-Dai-Shi
//!
//! Two PRFs are used:
//! - `PRF_m` (WirePrf): generates wire encryption masks
//! - `PRF_σ` (MacPrf): generates MAC keys/tags

use super::prg::{Prg, Sha256Prg};
use sha2::{Digest, Sha256};

/// A punctured key that can evaluate everywhere except at the punctured point
#[derive(Clone, Debug)]
pub struct PuncturedKey {
    /// Sibling seeds along the path to the punctured point
    pub sibling_seeds: Vec<[u8; 32]>,
    /// The punctured point (as bit string)
    pub punctured_point: Vec<bool>,
    /// Depth of the GGM tree
    pub depth: usize,
}

/// Trait for Puncturable PRFs
pub trait PuncturablePrf: Clone {
    /// The key type
    type Key: Clone;

    /// Generate a fresh PRF key
    fn keygen(&self) -> Self::Key;

    /// Evaluate the PRF at a point
    fn eval(&self, key: &Self::Key, input: &[bool]) -> [u8; 32];

    /// Puncture the key at a specific point
    ///
    /// Returns a punctured key that can evaluate on all inputs except the given point.
    fn puncture(&self, key: &Self::Key, point: &[bool]) -> PuncturedKey;

    /// Evaluate using a punctured key
    ///
    /// Returns None if the input equals the punctured point.
    fn eval_punctured(&self, pkey: &PuncturedKey, input: &[bool]) -> Option<[u8; 32]>;
}

/// GGM-tree based puncturable PRF
#[derive(Clone, Debug)]
pub struct GgmPrf {
    prg: Sha256Prg,
    depth: usize,
}

impl GgmPrf {
    /// Create a new GGM PRF with specified depth
    pub fn new(depth: usize) -> Self {
        Self {
            prg: Sha256Prg,
            depth,
        }
    }

    /// Walk the GGM tree from root to leaf
    fn tree_walk(&self, root: &[u8; 32], path: &[bool]) -> [u8; 32] {
        let mut current = *root;

        for &bit in path.iter().take(self.depth) {
            let (left, right) = self.prg.expand_double(&current);
            current = if bit { right } else { left };
        }

        current
    }
}

impl PuncturablePrf for GgmPrf {
    type Key = [u8; 32];

    fn keygen(&self) -> Self::Key {
        use rand::RngCore;
        let mut key = [0u8; 32];
        rand::thread_rng().fill_bytes(&mut key);
        key
    }

    fn eval(&self, key: &Self::Key, input: &[bool]) -> [u8; 32] {
        let padded: Vec<bool> = input
            .iter()
            .copied()
            .chain(std::iter::repeat(false))
            .take(self.depth)
            .collect();

        let leaf_seed = self.tree_walk(key, &padded);

        let mut hasher = Sha256::new();
        hasher.update(leaf_seed);
        hasher.update(b"output");
        hasher.finalize().into()
    }

    fn puncture(&self, key: &Self::Key, point: &[bool]) -> PuncturedKey {
        let padded: Vec<bool> = point
            .iter()
            .copied()
            .chain(std::iter::repeat(false))
            .take(self.depth)
            .collect();

        let mut sibling_seeds = Vec::with_capacity(self.depth);
        let mut current = *key;

        for &bit in padded.iter() {
            let (left, right) = self.prg.expand_double(&current);

            if bit {
                sibling_seeds.push(left);
                current = right;
            } else {
                sibling_seeds.push(right);
                current = left;
            }
        }

        PuncturedKey {
            sibling_seeds,
            punctured_point: padded,
            depth: self.depth,
        }
    }

    fn eval_punctured(&self, pkey: &PuncturedKey, input: &[bool]) -> Option<[u8; 32]> {
        let padded: Vec<bool> = input
            .iter()
            .copied()
            .chain(std::iter::repeat(false))
            .take(self.depth)
            .collect();

        if padded == pkey.punctured_point {
            return None;
        }

        let mut diverge_idx = None;
        for (i, (&input_bit, &punct_bit)) in padded.iter().zip(&pkey.punctured_point).enumerate() {
            if input_bit != punct_bit {
                diverge_idx = Some(i);
                break;
            }
        }

        let diverge_idx = diverge_idx?;

        let mut current = pkey.sibling_seeds[diverge_idx];

        for &bit in padded.iter().skip(diverge_idx + 1) {
            let (left, right) = self.prg.expand_double(&current);
            current = if bit { right } else { left };
        }

        let mut hasher = Sha256::new();
        hasher.update(current);
        hasher.update(b"output");
        Some(hasher.finalize().into())
    }
}

/// Wire encryption PRF (PRF_m in the paper)
pub type WirePrf = GgmPrf;

/// MAC key PRF (PRF_σ in the paper)
pub type MacPrf = GgmPrf;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_ggm_prf_deterministic() {
        let prf = GgmPrf::new(8);
        let key = prf.keygen();
        let input = vec![true, false, true, false];

        let out1 = prf.eval(&key, &input);
        let out2 = prf.eval(&key, &input);

        assert_eq!(out1, out2);
    }

    #[test]
    fn test_ggm_prf_different_inputs() {
        let prf = GgmPrf::new(8);
        let key = prf.keygen();

        let out1 = prf.eval(&key, &[true, false]);
        let out2 = prf.eval(&key, &[false, true]);

        assert_ne!(out1, out2);
    }

    #[test]
    fn test_ggm_puncture_blocks_point() {
        let prf = GgmPrf::new(4);
        let key = prf.keygen();
        let punct_point = vec![true, false, true, false];

        let pkey = prf.puncture(&key, &punct_point);

        assert!(prf.eval_punctured(&pkey, &punct_point).is_none());
    }

    #[test]
    fn test_ggm_puncture_allows_other_points() {
        let prf = GgmPrf::new(4);
        let key = prf.keygen();
        let punct_point = vec![true, false, true, false];
        let other_point = vec![false, false, true, false];

        let pkey = prf.puncture(&key, &punct_point);

        let normal_eval = prf.eval(&key, &other_point);
        let punct_eval = prf.eval_punctured(&pkey, &other_point).unwrap();

        assert_eq!(normal_eval, punct_eval);
    }

    #[test]
    fn test_ggm_puncture_consistency() {
        let prf = GgmPrf::new(8);
        let key = prf.keygen();
        let punct_point = vec![true, true, false, false];

        let pkey = prf.puncture(&key, &punct_point);

        for i in 0..16u8 {
            let input: Vec<bool> = (0..4).map(|j| (i >> j) & 1 == 1).collect();

            if input == punct_point {
                assert!(prf.eval_punctured(&pkey, &input).is_none());
            } else {
                let normal = prf.eval(&key, &input);
                let punct = prf.eval_punctured(&pkey, &input).unwrap();
                assert_eq!(normal, punct);
            }
        }
    }
}
