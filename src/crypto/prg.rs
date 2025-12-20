//! Pseudorandom Generator (PRG) implementation
//!
//! Used for key stretching and mask generation in the LiO construction.
//! The PRG is modeled as a keyed hash function (BLAKE3 or SHA-256).

use sha2::{Digest, Sha256};

/// Trait for Pseudorandom Generators
pub trait Prg {
    /// Expand a seed into a longer output
    fn expand(&self, seed: &[u8], output_len: usize) -> Vec<u8>;

    /// Generate two child seeds from a parent seed (for GGM tree)
    fn expand_double(&self, seed: &[u8; 32]) -> ([u8; 32], [u8; 32]) {
        let output = self.expand(seed, 64);
        let mut left = [0u8; 32];
        let mut right = [0u8; 32];
        left.copy_from_slice(&output[..32]);
        right.copy_from_slice(&output[32..]);
        (left, right)
    }
}

/// SHA-256 based PRG implementation
///
/// Uses HKDF-style expansion: PRG(seed, i) = H(seed || i) for each block.
#[derive(Clone, Debug, Default)]
pub struct Sha256Prg;

impl Prg for Sha256Prg {
    fn expand(&self, seed: &[u8], output_len: usize) -> Vec<u8> {
        let mut output = Vec::with_capacity(output_len);
        let mut counter = 0u64;

        while output.len() < output_len {
            let mut hasher = Sha256::new();
            hasher.update(seed);
            hasher.update(counter.to_le_bytes());
            let block = hasher.finalize();

            let remaining = output_len - output.len();
            let to_copy = remaining.min(32);
            output.extend_from_slice(&block[..to_copy]);

            counter += 1;
        }

        output
    }
}

/// Generate a random seed
pub fn random_seed() -> [u8; 32] {
    use rand::RngCore;
    let mut seed = [0u8; 32];
    rand::thread_rng().fill_bytes(&mut seed);
    seed
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_prg_deterministic() {
        let prg = Sha256Prg;
        let seed = [0u8; 32];

        let out1 = prg.expand(&seed, 64);
        let out2 = prg.expand(&seed, 64);

        assert_eq!(out1, out2);
    }

    #[test]
    fn test_prg_different_seeds() {
        let prg = Sha256Prg;
        let seed1 = [0u8; 32];
        let mut seed2 = [0u8; 32];
        seed2[0] = 1;

        let out1 = prg.expand(&seed1, 64);
        let out2 = prg.expand(&seed2, 64);

        assert_ne!(out1, out2);
    }

    #[test]
    fn test_prg_expand_double() {
        let prg = Sha256Prg;
        let seed = [42u8; 32];

        let (left, right) = prg.expand_double(&seed);

        assert_ne!(left, right);
        assert_ne!(left, seed);
    }

    #[test]
    fn test_prg_output_length() {
        let prg = Sha256Prg;
        let seed = [0u8; 32];

        assert_eq!(prg.expand(&seed, 16).len(), 16);
        assert_eq!(prg.expand(&seed, 64).len(), 64);
        assert_eq!(prg.expand(&seed, 100).len(), 100);
    }
}
