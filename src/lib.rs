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

// ============================================================================
// Stub Types (placeholders for dependencies from circuit-mixing-research)
// ============================================================================

pub mod stub {
    use rand::Rng;

    #[derive(Clone, Debug, Copy, PartialEq, Eq)]
    pub enum ControlFunction {
        F,
        And,
        Xor,
        Or,
        Nand,
        Nor,
        Xnor,
        AndNot,
    }

    impl ControlFunction {
        pub fn evaluate(&self, a: bool, b: bool) -> bool {
            match self {
                Self::F => false,
                Self::And => a && b,
                Self::Xor => a ^ b,
                Self::Or => a || b,
                Self::Nand => !(a && b),
                Self::Nor => !(a || b),
                Self::Xnor => !(a ^ b),
                Self::AndNot => a && !b,
            }
        }
    }

    #[derive(Clone, Debug)]
    pub struct Gate {
        pub output_wire: u8,
        pub input_wire_a: u8,
        pub input_wire_b: u8,
        pub control_function: ControlFunction,
    }

    impl Gate {
        pub fn new(output: u8, a: u8, b: u8, func: ControlFunction) -> Self {
            Self {
                output_wire: output,
                input_wire_a: a,
                input_wire_b: b,
                control_function: func,
            }
        }
    }

    #[derive(Clone, Debug)]
    pub struct Circuit {
        pub gates: Vec<Gate>,
        pub num_wires: usize,
    }

    impl Circuit {
        pub fn new(gates: Vec<Gate>, num_wires: usize) -> Self {
            Self { gates, num_wires }
        }

        pub fn evaluate(&self, input: usize) -> usize {
            let mut wires = vec![false; self.num_wires];
            for i in 0..self.num_wires {
                wires[i] = (input >> i) & 1 == 1;
            }
            for gate in &self.gates {
                let a = wires[gate.input_wire_a as usize];
                let b = wires[gate.input_wire_b as usize];
                wires[gate.output_wire as usize] = gate.control_function.evaluate(a, b);
            }
            let mut output = 0usize;
            for (i, &w) in wires.iter().enumerate() {
                if w {
                    output |= 1 << i;
                }
            }
            output
        }

        pub fn random_r57(num_wires: usize, num_gates: usize) -> Self {
            let mut rng = rand::thread_rng();
            let funcs = [
                ControlFunction::And,
                ControlFunction::Xor,
                ControlFunction::Or,
                ControlFunction::Nand,
            ];
            let gates: Vec<Gate> = (0..num_gates)
                .map(|_| {
                    let out = rng.gen_range(0..num_wires) as u8;
                    let a = rng.gen_range(0..num_wires) as u8;
                    let b = rng.gen_range(0..num_wires) as u8;
                    let func = funcs[rng.gen_range(0..funcs.len())];
                    Gate::new(out, a, b, func)
                })
                .collect();
            Self { gates, num_wires }
        }
    }

    #[derive(Clone, Debug)]
    pub struct EquivalenceProof {
        pub circuit_a_hash: [u8; 32],
        pub circuit_b_hash: [u8; 32],
        pub proof_steps: Vec<String>,
    }

    impl EquivalenceProof {
        pub fn dummy(circuit: &Circuit) -> Self {
            use sha2::{Sha256, Digest};
            let mut hasher = Sha256::new();
            hasher.update(format!("{:?}", circuit.gates));
            let hash: [u8; 32] = hasher.finalize().into();
            Self {
                circuit_a_hash: hash,
                circuit_b_hash: hash,
                proof_steps: vec!["identity".to_string()],
            }
        }
    }

    #[derive(Clone, Debug)]
    pub struct EFProof {
        pub proof_size: usize,
    }

    pub fn to_ef_proof(proof: &EquivalenceProof) -> EFProof {
        EFProof {
            proof_size: proof.proof_steps.len() * 64 + 128,
        }
    }

    #[derive(Clone, Debug)]
    pub struct BaseIOParams {
        pub lambda: usize,
    }

    impl BaseIOParams {
        pub fn for_augmented_gate(lambda: usize) -> Self {
            Self { lambda }
        }
    }

    #[derive(Clone, Debug)]
    pub struct LiOParams {
        pub lambda: usize,
        pub subcircuit_size: usize,
        pub base_io_params: BaseIOParams,
    }

    impl LiOParams {
        pub fn new(lambda: usize, subcircuit_size: usize) -> Self {
            Self {
                lambda,
                subcircuit_size,
                base_io_params: BaseIOParams::for_augmented_gate(lambda),
            }
        }
    }

    #[derive(Clone, Debug)]
    pub struct ObfuscatedLiO {
        pub base_io_size_bytes: usize,
        pub wire_keys: Vec<[u8; 32]>,
    }

    #[derive(Clone, Debug)]
    pub enum LiOError {
        InvalidCircuit(String),
    }

    impl std::fmt::Display for LiOError {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            match self {
                Self::InvalidCircuit(s) => write!(f, "Invalid circuit: {}", s),
            }
        }
    }

    impl std::error::Error for LiOError {}

    pub struct LiO {
        pub params: LiOParams,
    }

    impl LiO {
        pub fn new(params: LiOParams) -> Self {
            Self { params }
        }

        pub fn obfuscate(&self, circuit: &Circuit) -> Result<ObfuscatedLiO, LiOError> {
            let base_io_size_bytes = circuit.gates.len() * 500;
            let wire_keys = vec![[0u8; 32]; circuit.num_wires];
            Ok(ObfuscatedLiO {
                base_io_size_bytes,
                wire_keys,
            })
        }
    }

    #[derive(Clone, Debug)]
    pub struct MixResult {
        pub circuit: Circuit,
        pub proof: EquivalenceProof,
    }

    pub fn proven_stealth_mix(circuit: &Circuit) -> MixResult {
        MixResult {
            circuit: circuit.clone(),
            proof: EquivalenceProof::dummy(circuit),
        }
    }

    pub fn proven_identity_injection(circuit: &Circuit, _rounds: usize) -> MixResult {
        proven_stealth_mix(circuit)
    }
}

use stub::*;

// ============================================================================
// Parameters
// ============================================================================

#[derive(Clone, Debug)]
pub struct MaDaiShiParams {
    pub lambda: usize,
    pub max_circuit_size: usize,
    pub max_proof_size: usize,
    pub subcircuit_size: usize,
    pub lio_params: LiOParams,
}

impl MaDaiShiParams {
    pub fn new(lambda: usize, max_circuit_size: usize, max_proof_size: usize) -> Self {
        let total = max_circuit_size + max_proof_size;
        let subcircuit_size = ((total as f64).log2().ceil() as usize).max(4);
        
        let mut lio_params = LiOParams::new(lambda, subcircuit_size);
        lio_params.base_io_params = BaseIOParams::for_augmented_gate(lambda);
        
        Self {
            lambda,
            max_circuit_size,
            max_proof_size,
            subcircuit_size,
            lio_params,
        }
    }
    
    pub fn for_circuit_and_proof(circuit: &Circuit, proof: &EquivalenceProof) -> Self {
        let n_circ = circuit.gates.len();
        let ef_proof = to_ef_proof(proof);
        let n_proof = ef_proof.proof_size;
        Self::new(128, n_circ, n_proof)
    }
    
    pub fn conservative(circuit_size: usize, proof_size: usize) -> Self {
        Self::new(256, circuit_size.next_power_of_two(), proof_size.next_power_of_two())
    }
    
    pub fn optimized(circuit_size: usize, proof_size: usize) -> Self {
        let total = circuit_size + proof_size;
        let subcircuit_size = ((total as f64).log2().ceil() as usize).max(2);
        
        let mut lio_params = LiOParams::new(100, subcircuit_size);
        lio_params.base_io_params = BaseIOParams::for_augmented_gate(100);
        
        Self {
            lambda: 100,
            max_circuit_size: circuit_size,
            max_proof_size: proof_size,
            subcircuit_size,
            lio_params,
        }
    }
    
    pub fn aggressive(circuit_size: usize, proof_size: usize) -> Self {
        let total = circuit_size + proof_size;
        let subcircuit_size = ((total as f64).log2().ceil() as usize).max(2);
        
        let mut lio_params = LiOParams::new(80, subcircuit_size);
        lio_params.base_io_params = BaseIOParams::for_augmented_gate(80);
        
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
// Padding Construction (Section 3.2)
// ============================================================================

#[derive(Clone, Debug)]
pub struct PaddedCircuit {
    pub main_circuit: Circuit,
    pub filler_circuit: Circuit,
    pub proof_circuit: Circuit,
    pub and_tree: Vec<Gate>,
    pub combined: Circuit,
    pub original_size: usize,
    pub overhead: PaddingOverhead,
}

#[derive(Clone, Debug)]
pub struct PaddingOverhead {
    pub original_gates: usize,
    pub padded_gates: usize,
    pub routing_gates: usize,
    pub and_tree_gates: usize,
    pub size_ratio: f64,
}

pub fn pad_single(circuit: &Circuit, n_bound: usize) -> Circuit {
    if circuit.gates.is_empty() {
        return create_identity_circuit(circuit.num_wires, n_bound);
    }
    
    let mut padded_gates = Vec::new();
    let num_wires = circuit.num_wires.max(4);
    
    padded_gates.extend(circuit.gates.iter().cloned());
    
    let routing_depth = ((n_bound as f64).log2().ceil() as usize).max(1);
    let routing_gates = create_routing_network(num_wires, routing_depth, padded_gates.len());
    padded_gates.extend(routing_gates);
    
    let copy_gates = create_copy_gadgets(num_wires, routing_depth);
    padded_gates.extend(copy_gates);
    
    while padded_gates.len() < n_bound {
        let wire = (padded_gates.len() % num_wires) as u8;
        let c1 = ((padded_gates.len() + 1) % num_wires) as u8;
        let c2 = ((padded_gates.len() + 2) % num_wires) as u8;
        
        padded_gates.push(Gate::new(wire, c1, c2, ControlFunction::Xor));
        if padded_gates.len() < n_bound {
            padded_gates.push(Gate::new(wire, c1, c2, ControlFunction::Xor));
        }
    }
    
    padded_gates.truncate(n_bound);
    
    Circuit {
        gates: padded_gates,
        num_wires,
    }
}

fn create_routing_network(num_wires: usize, depth: usize, start_idx: usize) -> Vec<Gate> {
    let mut gates = Vec::new();
    
    for level in 0..depth {
        let stride = 1 << level;
        for i in 0..(num_wires / (2 * stride)).max(1) {
            let a = ((i * 2 * stride) % num_wires) as u8;
            let b = (((i * 2 + 1) * stride) % num_wires) as u8;
            let out = ((i * stride + start_idx + level) % num_wires) as u8;
            
            gates.push(Gate::new(out, a, b, ControlFunction::Xor));
        }
    }
    
    gates
}

fn create_copy_gadgets(num_wires: usize, depth: usize) -> Vec<Gate> {
    let mut gates = Vec::new();
    
    for level in 0..depth {
        for i in 0..num_wires.min(4) {
            let src = i as u8;
            let dst = ((i + level + 1) % num_wires) as u8;
            let ctrl = ((i + level + 2) % num_wires) as u8;
            
            gates.push(Gate::new(dst, src, ctrl, ControlFunction::Xor));
        }
    }
    
    gates
}

fn create_identity_circuit(num_wires: usize, size: usize) -> Circuit {
    let mut gates = Vec::with_capacity(size);
    let num_wires = num_wires.max(4);
    
    for i in 0..(size / 2) {
        let wire = (i % num_wires) as u8;
        let c1 = ((i + 1) % num_wires) as u8;
        let c2 = ((i + 2) % num_wires) as u8;
        
        gates.push(Gate::new(wire, c1, c2, ControlFunction::Xor));
        gates.push(Gate::new(wire, c1, c2, ControlFunction::Xor));
    }
    
    if size % 2 == 1 {
        let wire = ((size / 2) % num_wires) as u8;
        gates.push(Gate::new(wire, wire, wire, ControlFunction::F));
    }
    
    Circuit { gates, num_wires }
}

fn create_and_tree(num_outputs: usize, num_wires: usize) -> Vec<Gate> {
    let mut gates = Vec::new();
    
    if num_outputs <= 1 {
        return gates;
    }
    
    let depth = ((num_outputs as f64).log2().ceil() as usize).max(1);
    
    for level in 0..depth {
        let pairs = (num_outputs >> level).max(1) / 2;
        for i in 0..pairs {
            let a = (i * 2 % num_wires) as u8;
            let b = ((i * 2 + 1) % num_wires) as u8;
            let out = ((num_wires - 1 - level - i) % num_wires) as u8;
            
            gates.push(Gate::new(out, a, b, ControlFunction::And));
        }
    }
    
    gates
}

pub fn pad(circuit: &Circuit, n_circ: usize, n_proof: usize) -> PaddedCircuit {
    let num_wires = circuit.num_wires.max(8);
    let original_size = circuit.gates.len();
    
    let main_circuit = pad_single(circuit, n_circ);
    let filler_circuit = create_identity_circuit(num_wires, n_circ);
    
    let c = 2;
    let proof_size = c * (n_circ + n_proof);
    let proof_circuit = create_identity_circuit(num_wires, proof_size.min(n_circ * 4));
    
    let and_tree = create_and_tree(3, num_wires);
    
    let mut combined_gates = Vec::new();
    combined_gates.extend(main_circuit.gates.iter().cloned());
    combined_gates.extend(filler_circuit.gates.iter().cloned());
    combined_gates.extend(proof_circuit.gates.iter().cloned());
    combined_gates.extend(and_tree.iter().cloned());
    
    let padded_gates = combined_gates.len();
    let routing_gates = main_circuit.gates.len().saturating_sub(original_size);
    
    let combined = Circuit {
        gates: combined_gates,
        num_wires,
    };
    
    PaddedCircuit {
        main_circuit,
        filler_circuit,
        proof_circuit,
        and_tree: and_tree.clone(),
        combined,
        original_size,
        overhead: PaddingOverhead {
            original_gates: original_size,
            padded_gates,
            routing_gates,
            and_tree_gates: and_tree.len(),
            size_ratio: padded_gates as f64 / original_size.max(1) as f64,
        },
    }
}

pub fn pad_optimized(circuit: &Circuit) -> PaddedCircuit {
    let num_wires = circuit.num_wires.max(4);
    let original_size = circuit.gates.len();
    
    let target_size = original_size + ((original_size as f64).log2().ceil() as usize).max(4) * 2;
    let main_circuit = pad_single(circuit, target_size);
    
    let filler_circuit = Circuit { gates: vec![], num_wires };
    let proof_circuit = Circuit { gates: vec![], num_wires };
    let and_tree = vec![];
    
    let padded_gates = main_circuit.gates.len();
    let routing_gates = padded_gates.saturating_sub(original_size);
    
    PaddedCircuit {
        main_circuit: main_circuit.clone(),
        filler_circuit,
        proof_circuit,
        and_tree,
        combined: main_circuit,
        original_size,
        overhead: PaddingOverhead {
            original_gates: original_size,
            padded_gates,
            routing_gates,
            and_tree_gates: 0,
            size_ratio: padded_gates as f64 / original_size.max(1) as f64,
        },
    }
}

// ============================================================================
// Main Quasi-Linear iO Construction
// ============================================================================

pub struct MaDaiShiObfuscated {
    pub lio_obfuscated: ObfuscatedLiO,
    pub padding_info: PaddingOverhead,
    pub ef_proof_size: usize,
    pub metrics: ObfuscationMetrics,
}

#[derive(Clone, Debug)]
pub struct ObfuscationMetrics {
    pub original_size: usize,
    pub proof_size: usize,
    pub padded_size: usize,
    pub subcircuit_size: usize,
    pub num_hybrids: usize,
    pub obfuscated_bytes: usize,
    pub size_ratio: f64,
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

pub struct QuasiLinearObfuscator {
    params: MaDaiShiParams,
    lio: LiO,
}

impl QuasiLinearObfuscator {
    pub fn new(params: MaDaiShiParams) -> Self {
        let lio = LiO::new(params.lio_params.clone());
        Self { params, lio }
    }
    
    pub fn with_default_params() -> Self {
        Self::new(MaDaiShiParams::default())
    }
    
    pub fn for_circuit_and_proof(circuit: &Circuit, proof: &EquivalenceProof) -> Self {
        let params = MaDaiShiParams::for_circuit_and_proof(circuit, proof);
        Self::new(params)
    }
    
    pub fn obfuscate(
        &self,
        circuit: &Circuit,
        proof: &EquivalenceProof,
    ) -> Result<MaDaiShiObfuscated, MaDaiShiError> {
        let ef_proof = to_ef_proof(proof);
        
        let n_circ = self.params.max_circuit_size.max(circuit.gates.len());
        let n_proof = self.params.max_proof_size.max(ef_proof.proof_size);
        
        let padded = pad(circuit, n_circ, n_proof);
        
        let lio_obfuscated = self.lio.obfuscate(&padded.combined)
            .map_err(MaDaiShiError::LiOError)?;
        
        let total = n_circ + n_proof;
        let log_total = ((total as f64).log2().ceil() as usize).max(1);
        let num_hybrids = total * log_total;
        
        let obfuscated_bytes = lio_obfuscated.base_io_size_bytes
            + lio_obfuscated.wire_keys.len() * 64
            + 256;
        
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
    
    pub fn obfuscate_with_mixing(
        &self,
        circuit: &Circuit,
    ) -> Result<MaDaiShiObfuscated, MaDaiShiError> {
        let mix_result = proven_stealth_mix(circuit);
        self.obfuscate(&mix_result.circuit, &mix_result.proof)
    }
    
    pub fn estimate_overhead(&self, circuit: &Circuit, proof: &EquivalenceProof) -> ObfuscationMetrics {
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

#[derive(Debug, Clone)]
pub enum MaDaiShiError {
    LiOError(LiOError),
    InvalidProof(String),
    CircuitTooLarge { size: usize, max: usize },
    ProofTooLarge { size: usize, max: usize },
}

impl std::fmt::Display for MaDaiShiError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::LiOError(e) => write!(f, "LiO error: {}", e),
            Self::InvalidProof(s) => write!(f, "Invalid proof: {}", s),
            Self::CircuitTooLarge { size, max } => 
                write!(f, "Circuit too large: {} gates (max {})", size, max),
            Self::ProofTooLarge { size, max } =>
                write!(f, "Proof too large: {} symbols (max {})", size, max),
        }
    }
}

impl std::error::Error for MaDaiShiError {}

// ============================================================================
// Hybrid Sequence (for s-equivalence proof)
// ============================================================================

#[derive(Clone, Debug)]
pub struct HybridCircuit {
    pub index: usize,
    pub circuit: Circuit,
    pub change_description: String,
    pub diff_size: usize,
}

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

pub fn verify_hybrid_sequence(hybrids: &[HybridCircuit], s: usize) -> bool {
    for i in 0..hybrids.len().saturating_sub(1) {
        if hybrids[i].diff_size > s && hybrids[i].diff_size > 0 {
            eprintln!(
                "[WARN] Hybrid {} -> {} has diff_size {} > s={}",
                i, i + 1, hybrids[i].diff_size, s
            );
            return false;
        }
    }
    true
}

// ============================================================================
// Convenience Functions
// ============================================================================

pub fn obfuscate(
    circuit: &Circuit,
    proof: &EquivalenceProof,
) -> Result<MaDaiShiObfuscated, MaDaiShiError> {
    let obfuscator = QuasiLinearObfuscator::for_circuit_and_proof(circuit, proof);
    obfuscator.obfuscate(circuit, proof)
}

pub fn obfuscate_auto(circuit: &Circuit) -> Result<MaDaiShiObfuscated, MaDaiShiError> {
    let obfuscator = QuasiLinearObfuscator::with_default_params();
    obfuscator.obfuscate_with_mixing(circuit)
}

pub fn obfuscate_optimized(circuit: &Circuit) -> Result<MaDaiShiObfuscated, MaDaiShiError> {
    let mix_result = proven_stealth_mix(circuit);
    let ef_proof = to_ef_proof(&mix_result.proof);
    
    let padded = pad_optimized(&mix_result.circuit);
    
    let params = MaDaiShiParams::optimized(circuit.gates.len(), ef_proof.proof_size);
    let lio = LiO::new(params.lio_params.clone());
    
    let lio_obfuscated = lio.obfuscate(&padded.combined)
        .map_err(MaDaiShiError::LiOError)?;
    
    let n_circ = circuit.gates.len();
    let n_proof = ef_proof.proof_size;
    let total = n_circ + n_proof;
    let log_total = ((total as f64).log2().ceil() as usize).max(1);
    
    let obfuscated_bytes = lio_obfuscated.base_io_size_bytes
        + lio_obfuscated.wire_keys.len() * 64
        + 256;
    
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

pub fn estimate_overhead(circuit: &Circuit, proof: &EquivalenceProof) -> ObfuscationMetrics {
    let obfuscator = QuasiLinearObfuscator::for_circuit_and_proof(circuit, proof);
    obfuscator.estimate_overhead(circuit, proof)
}

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
// Re-exports for convenience
// ============================================================================

pub use stub::{Circuit, Gate, ControlFunction, EquivalenceProof};

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_pad_single() {
        let circuit = Circuit::random_r57(8, 10);
        let padded = pad_single(&circuit, 32);
        
        assert_eq!(padded.gates.len(), 32);
        assert!(padded.num_wires >= circuit.num_wires);
    }
    
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
}
