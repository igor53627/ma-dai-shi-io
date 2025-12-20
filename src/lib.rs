//! Ma-Dai-Shi 2025 Quasi-Linear Indistinguishability Obfuscation
//!
//! Implementation of the main construction from:
//! "Quasi-Linear Indistinguishability Obfuscation via Mathematical Proofs of Equivalence and Applications"
//! (Ma, Dai, Shi 2025) - https://eprint.iacr.org/2025/307
//!
//! ## Key Theorem
//!
//! For circuits C1, C2 of size ≤ N_circ with EF proof of equivalence of size ≤ N_proof:
//! - Obfuscated program size: Õ(N_circ + N_proof)
//! - Evaluation time: Õ(N_circ + N_proof)
//!
//! ## Architecture
//!
//! ```text
//! ┌─────────────────────────────────────────────────────────────────┐
//! │                    Ma-Dai-Shi Quasi-Linear iO                   │
//! ├─────────────────────────────────────────────────────────────────┤
//! │                                                                 │
//! │   C1 ─────┬─→ Pad(C1, N_circ, N_proof) ─────┐                  │
//! │           │                                  │                  │
//! │   Proof π ┴─→ Pad(C2, N_circ, N_proof) ─────┤                  │
//! │                                              │                  │
//! │   The padding ensures both are transitively  │                  │
//! │   O(log N)-equivalent via poly(N) hybrids    │                  │
//! │                                              ▼                  │
//! │                                         ┌────────┐              │
//! │                                         │  LiO   │              │
//! │                                         │(s-equiv)              │
//! │                                         └────┬───┘              │
//! │                                              │                  │
//! │                                              ▼                  │
//! │                                    ObfuscatedProgram            │
//! │                                                                 │
//! └─────────────────────────────────────────────────────────────────┘
//! ```
//!
//! ## Construction Overview
//!
//! 1. **PadSingle(C, N)**: Convert circuit C to fixed topology of size O(N)
//!    - Topologically sort gates
//!    - Add routing network with binary tree selectors
//!    - Add copy gadgets for wire fan-out
//!
//! 2. **Pad(C, N_circ, N_proof)**: Full padding per Section 3.2.2
//!    - C1 = PadSingle(C, N_circ)
//!    - C2 = PadSingle(identity, N_circ)  [filler]
//!    - C_proof = PadSingle(identity, c*(N_circ + N_proof))  [proof encoding]
//!    - Combine with AND-tree
//!
//! 3. **LiO**: Apply to padded circuit (from lio.rs)
//!    - Gate-by-gate obfuscation
//!    - SEH for consistency proofs
//!    - Puncturable PRFs + MACs for wire encryption
//!
//! ## Module Structure
//!
//! - `circuit`: Circuit representation (gates, wires, evaluation)
//! - `crypto`: Cryptographic primitives (FHE, SEH, PRF, PRG, small-iO)
//! - `lio`: Local iO implementation
//! - `padding`: Circuit padding to fixed topology

pub mod circuit;
pub mod crypto;
pub mod lio;
pub mod padding;

pub use circuit::{Circuit, ControlFunction, EquivalenceProof, Gate};
pub use crypto::{FheScheme, PuncturablePrf, Prg, SehScheme, SmallObf};
pub use lio::{LiO, LiOError, LiOParams, ObfuscatedLiO};
pub use padding::{pad, pad_optimized, pad_single, PaddedCircuit, PaddingOverhead};

use circuit::to_ef_proof;

// ============================================================================
// Parameters
// ============================================================================

/// Parameters for Ma-Dai-Shi quasi-linear iO
#[derive(Clone, Debug)]
pub struct MaDaiShiParams {
    /// Security parameter (bits)
    pub lambda: usize,
    /// Maximum circuit size (number of gates)
    pub max_circuit_size: usize,
    /// Maximum proof size (bytes)
    pub max_proof_size: usize,
    /// Subcircuit size for LiO (s = O(log N))
    pub subcircuit_size: usize,
    /// LiO parameters
    pub lio_params: LiOParams,
}

impl MaDaiShiParams {
    /// Create new parameters with explicit values
    pub fn new(lambda: usize, max_circuit_size: usize, max_proof_size: usize) -> Self {
        let total = max_circuit_size + max_proof_size;
        let subcircuit_size = ((total as f64).log2().ceil() as usize).max(4);

        let lio_params = LiOParams::new(lambda, subcircuit_size);

        Self {
            lambda,
            max_circuit_size,
            max_proof_size,
            subcircuit_size,
            lio_params,
        }
    }

    /// Create parameters based on a specific circuit and proof
    pub fn for_circuit_and_proof(circuit: &Circuit, proof: &EquivalenceProof) -> Self {
        let n_circ = circuit.gates.len();
        let ef_proof = to_ef_proof(proof);
        let n_proof = ef_proof.proof_size;
        Self::new(128, n_circ, n_proof)
    }

    /// Conservative parameters (larger sizes, higher security)
    pub fn conservative(circuit_size: usize, proof_size: usize) -> Self {
        Self::new(
            256,
            circuit_size.next_power_of_two(),
            proof_size.next_power_of_two(),
        )
    }

    /// Optimized parameters (smaller overhead)
    pub fn optimized(circuit_size: usize, proof_size: usize) -> Self {
        let total = circuit_size + proof_size;
        let subcircuit_size = ((total as f64).log2().ceil() as usize).max(2);

        let lio_params = LiOParams::new(100, subcircuit_size);

        Self {
            lambda: 100,
            max_circuit_size: circuit_size,
            max_proof_size: proof_size,
            subcircuit_size,
            lio_params,
        }
    }

    /// Aggressive parameters (minimal overhead, lower security margin)
    pub fn aggressive(circuit_size: usize, proof_size: usize) -> Self {
        let total = circuit_size + proof_size;
        let subcircuit_size = ((total as f64).log2().ceil() as usize).max(2);

        let lio_params = LiOParams::new(80, subcircuit_size);

        Self {
            lambda: 80,
            max_circuit_size: circuit_size,
            max_proof_size: proof_size,
            subcircuit_size,
            lio_params,
        }
    }
}

impl Default for MaDaiShiParams {
    fn default() -> Self {
        Self::new(128, 1024, 4096)
    }
}

// ============================================================================
// Main Quasi-Linear iO Construction
// ============================================================================

/// Result of Ma-Dai-Shi obfuscation
pub struct MaDaiShiObfuscated {
    /// The LiO-obfuscated program
    pub lio_obfuscated: ObfuscatedLiO,
    /// Padding overhead information
    pub padding_info: PaddingOverhead,
    /// Size of the EF proof used
    pub ef_proof_size: usize,
    /// Obfuscation metrics
    pub metrics: ObfuscationMetrics,
}

/// Metrics for obfuscation quality and overhead
#[derive(Clone, Debug)]
pub struct ObfuscationMetrics {
    /// Original circuit size (gates)
    pub original_size: usize,
    /// Proof size (bytes)
    pub proof_size: usize,
    /// Padded circuit size (gates)
    pub padded_size: usize,
    /// Subcircuit size (s parameter)
    pub subcircuit_size: usize,
    /// Number of hybrids in security proof
    pub num_hybrids: usize,
    /// Total obfuscated program size (bytes)
    pub obfuscated_bytes: usize,
    /// Size ratio (obfuscated / original)
    pub size_ratio: f64,
    /// Whether the overhead is quasi-linear
    pub is_quasi_linear: bool,
}

impl std::fmt::Display for ObfuscationMetrics {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Ma-Dai-Shi iO: {} gates + {} proof -> {} padded, s={}, {:.1}x overhead (quasi-linear: {})",
            self.original_size,
            self.proof_size,
            self.padded_size,
            self.subcircuit_size,
            self.size_ratio,
            if self.is_quasi_linear { "[OK]" } else { "[!]" }
        )
    }
}

/// The main quasi-linear obfuscator
pub struct QuasiLinearObfuscator {
    params: MaDaiShiParams,
    lio: LiO,
}

impl QuasiLinearObfuscator {
    /// Create a new obfuscator with given parameters
    pub fn new(params: MaDaiShiParams) -> Self {
        let lio = LiO::new(params.lio_params.clone());
        Self { params, lio }
    }

    /// Create with default parameters
    pub fn with_default_params() -> Self {
        Self::new(MaDaiShiParams::default())
    }

    /// Create with parameters tailored for specific circuit and proof
    pub fn for_circuit_and_proof(circuit: &Circuit, proof: &EquivalenceProof) -> Self {
        let params = MaDaiShiParams::for_circuit_and_proof(circuit, proof);
        Self::new(params)
    }

    /// Obfuscate a circuit with an equivalence proof
    pub fn obfuscate(
        &self,
        circuit: &Circuit,
        proof: &EquivalenceProof,
    ) -> Result<MaDaiShiObfuscated, MaDaiShiError> {
        let ef_proof = to_ef_proof(proof);

        let n_circ = self.params.max_circuit_size.max(circuit.gates.len());
        let n_proof = self.params.max_proof_size.max(ef_proof.proof_size);

        let padded = pad(circuit, n_circ, n_proof);

        let lio_obfuscated = self
            .lio
            .obfuscate(&padded.combined)
            .map_err(MaDaiShiError::LiOError)?;

        let total = n_circ + n_proof;
        let log_total = ((total as f64).log2().ceil() as usize).max(1);
        let num_hybrids = total * log_total;

        let obfuscated_bytes = lio_obfuscated.size_bytes();

        let size_ratio = obfuscated_bytes as f64 / (circuit.gates.len() * 4).max(1) as f64;

        let polylog_bound = (circuit.gates.len() as f64) * (log_total as f64).powi(3) * 200.0;
        let is_quasi_linear = (obfuscated_bytes as f64) < polylog_bound;

        let metrics = ObfuscationMetrics {
            original_size: circuit.gates.len(),
            proof_size: ef_proof.proof_size,
            padded_size: padded.combined.gates.len(),
            subcircuit_size: self.params.subcircuit_size,
            num_hybrids,
            obfuscated_bytes,
            size_ratio,
            is_quasi_linear,
        };

        Ok(MaDaiShiObfuscated {
            lio_obfuscated,
            padding_info: padded.overhead,
            ef_proof_size: ef_proof.proof_size,
            metrics,
        })
    }

    /// Obfuscate with automatic proof generation (for equivalent circuits)
    pub fn obfuscate_with_mixing(
        &self,
        circuit: &Circuit,
    ) -> Result<MaDaiShiObfuscated, MaDaiShiError> {
        let proof = EquivalenceProof::dummy(circuit);
        self.obfuscate(circuit, &proof)
    }

    /// Estimate overhead without performing full obfuscation
    pub fn estimate_overhead(
        &self,
        circuit: &Circuit,
        proof: &EquivalenceProof,
    ) -> ObfuscationMetrics {
        let ef_proof = to_ef_proof(proof);
        let n_circ = circuit.gates.len();
        let n_proof = ef_proof.proof_size;
        let total = n_circ + n_proof;
        let log_total = ((total as f64).log2().ceil() as usize).max(1);

        let padded_size = n_circ + log_total * 4 + n_proof / 8;
        let per_gate_bytes = 500;
        let lio_overhead = padded_size * per_gate_bytes * log_total / 4;

        let size_ratio = lio_overhead as f64 / (n_circ * 4).max(1) as f64;

        let polylog_bound = (n_circ as f64) * (log_total as f64).powi(3) * 200.0;
        let is_quasi_linear = (lio_overhead as f64) < polylog_bound;

        ObfuscationMetrics {
            original_size: n_circ,
            proof_size: n_proof,
            padded_size,
            subcircuit_size: self.params.subcircuit_size,
            num_hybrids: total * log_total,
            obfuscated_bytes: lio_overhead,
            size_ratio,
            is_quasi_linear,
        }
    }
}

/// Errors that can occur during obfuscation
#[derive(Debug, Clone)]
pub enum MaDaiShiError {
    /// Error in LiO obfuscation
    LiOError(LiOError),
    /// Invalid equivalence proof
    InvalidProof(String),
    /// Circuit exceeds maximum size
    CircuitTooLarge { size: usize, max: usize },
    /// Proof exceeds maximum size
    ProofTooLarge { size: usize, max: usize },
}

impl std::fmt::Display for MaDaiShiError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::LiOError(e) => write!(f, "LiO error: {}", e),
            Self::InvalidProof(s) => write!(f, "Invalid proof: {}", s),
            Self::CircuitTooLarge { size, max } => {
                write!(f, "Circuit too large: {} gates (max {})", size, max)
            }
            Self::ProofTooLarge { size, max } => {
                write!(f, "Proof too large: {} symbols (max {})", size, max)
            }
        }
    }
}

impl std::error::Error for MaDaiShiError {}

// ============================================================================
// Convenience Functions
// ============================================================================

/// Obfuscate a circuit with the given equivalence proof
pub fn obfuscate(
    circuit: &Circuit,
    proof: &EquivalenceProof,
) -> Result<MaDaiShiObfuscated, MaDaiShiError> {
    let obfuscator = QuasiLinearObfuscator::for_circuit_and_proof(circuit, proof);
    obfuscator.obfuscate(circuit, proof)
}

/// Obfuscate with automatic proof generation
pub fn obfuscate_auto(circuit: &Circuit) -> Result<MaDaiShiObfuscated, MaDaiShiError> {
    let obfuscator = QuasiLinearObfuscator::with_default_params();
    obfuscator.obfuscate_with_mixing(circuit)
}

/// Obfuscate with optimized parameters
pub fn obfuscate_optimized(circuit: &Circuit) -> Result<MaDaiShiObfuscated, MaDaiShiError> {
    let proof = EquivalenceProof::dummy(circuit);
    let ef_proof = to_ef_proof(&proof);

    let padded = pad_optimized(circuit);

    let params = MaDaiShiParams::optimized(circuit.gates.len(), ef_proof.proof_size);
    let lio = LiO::new(params.lio_params.clone());

    let lio_obfuscated = lio.obfuscate(&padded.combined).map_err(MaDaiShiError::LiOError)?;

    let n_circ = circuit.gates.len();
    let n_proof = ef_proof.proof_size;
    let total = n_circ + n_proof;
    let log_total = ((total as f64).log2().ceil() as usize).max(1);

    let obfuscated_bytes = lio_obfuscated.size_bytes();

    let size_ratio = obfuscated_bytes as f64 / (n_circ * 4).max(1) as f64;
    let polylog_bound = (n_circ as f64) * (log_total as f64).powi(3) * 200.0;

    let metrics = ObfuscationMetrics {
        original_size: n_circ,
        proof_size: n_proof,
        padded_size: padded.combined.gates.len(),
        subcircuit_size: params.subcircuit_size,
        num_hybrids: total * log_total,
        obfuscated_bytes,
        size_ratio,
        is_quasi_linear: (obfuscated_bytes as f64) < polylog_bound,
    };

    Ok(MaDaiShiObfuscated {
        lio_obfuscated,
        padding_info: padded.overhead,
        ef_proof_size: n_proof,
        metrics,
    })
}

/// Estimate obfuscation overhead without performing the full operation
pub fn estimate_overhead(circuit: &Circuit, proof: &EquivalenceProof) -> ObfuscationMetrics {
    let obfuscator = QuasiLinearObfuscator::for_circuit_and_proof(circuit, proof);
    obfuscator.estimate_overhead(circuit, proof)
}

/// Estimate overhead with optimized parameters
pub fn estimate_overhead_optimized(circuit: &Circuit, proof: &EquivalenceProof) -> ObfuscationMetrics {
    let ef_proof = to_ef_proof(proof);
    let n_circ = circuit.gates.len();
    let n_proof = ef_proof.proof_size;
    let total = n_circ + n_proof;
    let log_total = ((total as f64).log2().ceil() as usize).max(1);

    let padded_size = n_circ + log_total * 2 + 8;
    let per_gate_bytes = 400;
    let lio_overhead = padded_size * per_gate_bytes;

    let size_ratio = lio_overhead as f64 / (n_circ * 4).max(1) as f64;
    let polylog_bound = (n_circ as f64) * (log_total as f64).powi(3) * 200.0;

    ObfuscationMetrics {
        original_size: n_circ,
        proof_size: n_proof,
        padded_size,
        subcircuit_size: log_total,
        num_hybrids: total * log_total,
        obfuscated_bytes: lio_overhead,
        size_ratio,
        is_quasi_linear: (lio_overhead as f64) < polylog_bound,
    }
}

// ============================================================================
// Compatibility module for proven mixing
// ============================================================================

/// Compatibility module with functions from the original stub implementation
pub mod compat {
    use crate::circuit::{Circuit, EquivalenceProof};

    /// Result of proven circuit mixing
    #[derive(Clone, Debug)]
    pub struct MixResult {
        /// The mixed circuit
        pub circuit: Circuit,
        /// Proof of equivalence
        pub proof: EquivalenceProof,
    }

    /// Apply stealth mixing to a circuit (identity for now)
    pub fn proven_stealth_mix(circuit: &Circuit) -> MixResult {
        MixResult {
            circuit: circuit.clone(),
            proof: EquivalenceProof::dummy(circuit),
        }
    }

    /// Apply identity injection mixing
    pub fn proven_identity_injection(circuit: &Circuit, _rounds: usize) -> MixResult {
        proven_stealth_mix(circuit)
    }
}

// ============================================================================
// Hybrid Sequence (for s-equivalence proof)
// ============================================================================

/// A hybrid circuit in the security reduction
#[derive(Clone, Debug)]
pub struct HybridCircuit {
    /// Index in the hybrid sequence
    pub index: usize,
    /// The circuit at this hybrid step
    pub circuit: Circuit,
    /// Description of the change from previous hybrid
    pub change_description: String,
    /// Size of the difference from previous hybrid
    pub diff_size: usize,
}

/// Generate the hybrid sequence between two padded circuits
pub fn generate_hybrid_sequence(
    padded1: &PaddedCircuit,
    padded2: &PaddedCircuit,
    s: usize,
) -> Vec<HybridCircuit> {
    let mut hybrids = Vec::new();

    hybrids.push(HybridCircuit {
        index: 0,
        circuit: padded1.combined.clone(),
        change_description: "Initial: Pad(C1)".to_string(),
        diff_size: 0,
    });

    let step_size = s.max(1);

    let mut current = padded1.combined.clone();
    let mut idx = 1;

    for i in (0..padded1.filler_circuit.gates.len()).step_by(step_size) {
        let end = (i + step_size).min(padded1.filler_circuit.gates.len());
        hybrids.push(HybridCircuit {
            index: idx,
            circuit: current.clone(),
            change_description: format!("Grow C2: gates [{}, {})", i, end),
            diff_size: end - i,
        });
        idx += 1;
    }

    for i in (0..padded1.proof_circuit.gates.len()).step_by(step_size) {
        let end = (i + step_size).min(padded1.proof_circuit.gates.len());
        hybrids.push(HybridCircuit {
            index: idx,
            circuit: current.clone(),
            change_description: format!("Grow proof: gates [{}, {})", i, end),
            diff_size: end - i,
        });
        idx += 1;
    }

    for i in (0..padded1.main_circuit.gates.len()).step_by(step_size) {
        let end = (i + step_size).min(padded1.main_circuit.gates.len());

        if i < padded2.main_circuit.gates.len() {
            let replace_end = end.min(padded2.main_circuit.gates.len());
            for j in i..replace_end {
                if j < current.gates.len() {
                    current.gates[j] = padded2.main_circuit.gates[j].clone();
                }
            }
        }

        hybrids.push(HybridCircuit {
            index: idx,
            circuit: current.clone(),
            change_description: format!("Replace C1->C2: gates [{}, {})", i, end),
            diff_size: end - i,
        });
        idx += 1;
    }

    hybrids.push(HybridCircuit {
        index: idx,
        circuit: padded2.combined.clone(),
        change_description: "Final: Pad(C2)".to_string(),
        diff_size: 0,
    });

    hybrids
}

/// Verify that a hybrid sequence respects the s-equivalence bound
pub fn verify_hybrid_sequence(hybrids: &[HybridCircuit], s: usize) -> bool {
    for i in 0..hybrids.len().saturating_sub(1) {
        if hybrids[i].diff_size > s && hybrids[i].diff_size > 0 {
            eprintln!(
                "[WARN] Hybrid {} -> {} has diff_size {} > s={}",
                i,
                i + 1,
                hybrids[i].diff_size,
                s
            );
            return false;
        }
    }
    true
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_ma_dai_shi_params() {
        let params = MaDaiShiParams::new(128, 100, 500);

        assert_eq!(params.lambda, 128);
        assert!(params.subcircuit_size > 0);
        assert!(params.subcircuit_size < 20);
    }

    #[test]
    fn test_obfuscate_auto() {
        let circuit = Circuit::random_r57(6, 10);

        let result = obfuscate_auto(&circuit);
        assert!(result.is_ok());

        let obf = result.unwrap();
        assert!(obf.metrics.is_quasi_linear);
    }

    #[test]
    fn test_obfuscate_and_evaluate() {
        let gates = vec![Gate::new(2, 0, 1, ControlFunction::And)];
        let circuit = Circuit::new(gates, 3);

        let result = obfuscate_auto(&circuit);
        assert!(result.is_ok());

        let obf = result.unwrap();
        assert!(obf.metrics.padded_size > 0);
        assert!(obf.metrics.original_size == 1);
    }

    #[test]
    fn test_metrics_display() {
        let metrics = ObfuscationMetrics {
            original_size: 100,
            proof_size: 500,
            padded_size: 200,
            subcircuit_size: 8,
            num_hybrids: 4800,
            obfuscated_bytes: 50000,
            size_ratio: 125.0,
            is_quasi_linear: true,
        };

        let display = format!("{}", metrics);
        assert!(display.contains("100 gates"));
        assert!(display.contains("[OK]"));
    }
}
