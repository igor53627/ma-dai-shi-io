//! Cryptographic primitives for Ma-Dai-Shi iO
//!
//! This module defines the cryptographic building blocks required for the
//! Local iO (LiO) construction from §5 of the Ma-Dai-Shi paper.
//!
//! ## Required Primitives
//!
//! 1. **FHE (Fully Homomorphic Encryption)** - LWE-based encryption supporting
//!    homomorphic evaluation of small circuits.
//!
//! 2. **SEH (Somewhere Extractable Hash)** - Merkle-tree-like hash with FHE
//!    ciphertexts, supporting prefix consistency proofs.
//!
//! 3. **Puncturable PRF** - GGM-tree-based PRF that can be punctured at
//!    specific points for the security reduction.
//!
//! 4. **PRG (Pseudorandom Generator)** - For key stretching and mask generation.
//!
//! 5. **Small-Circuit iO** - Obfuscator for fixed, small gadget circuits
//!    (treated as an assumption in this implementation).

pub mod fhe;
pub mod obf;
pub mod prf;
pub mod prg;
pub mod seh;

pub use fhe::{FheCiphertext, FheParams, FheScheme, StubFhe};
pub use obf::{SmallObf, StubSmallObf};
pub use prf::{GgmPrf, MacPrf, PuncturablePrf, PuncturedKey, WirePrf};
pub use prg::{Prg, Sha256Prg};
pub use seh::{SehDigest, SehOpening, SehParams, SehProof, SehScheme, StubSeh};
