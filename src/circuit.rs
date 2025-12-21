//! Circuit representation for Ma-Dai-Shi iO
//!
//! Defines the core circuit abstractions used throughout the obfuscation pipeline.
//!
//! # Wire Index Type
//!
//! Wire indices are stored as `u16`, supporting circuits up to 65,536 wires.
//! This balances memory efficiency with practical circuit sizes.

use rand::Rng;

/// Boolean gate control functions
#[derive(Clone, Debug, Copy, PartialEq, Eq)]
pub enum ControlFunction {
    /// Constant false
    F,
    /// Logical AND
    And,
    /// Logical XOR
    Xor,
    /// Logical OR
    Or,
    /// Logical NAND
    Nand,
    /// Logical NOR
    Nor,
    /// Logical XNOR
    Xnor,
    /// a AND (NOT b)
    AndNot,
}

impl ControlFunction {
    /// Evaluate the gate function on two boolean inputs
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

    /// Returns all available control functions
    pub fn all() -> &'static [ControlFunction] {
        &[
            Self::F,
            Self::And,
            Self::Xor,
            Self::Or,
            Self::Nand,
            Self::Nor,
            Self::Xnor,
            Self::AndNot,
        ]
    }
}

/// A single gate in a boolean circuit
#[derive(Clone, Debug)]
pub struct Gate {
    /// Wire index where output is written
    pub output_wire: u16,
    /// First input wire index
    pub input_wire_a: u16,
    /// Second input wire index
    pub input_wire_b: u16,
    /// The boolean function computed by this gate
    pub control_function: ControlFunction,
}

impl Gate {
    /// Create a new gate
    pub fn new(output: u16, a: u16, b: u16, func: ControlFunction) -> Self {
        Self {
            output_wire: output,
            input_wire_a: a,
            input_wire_b: b,
            control_function: func,
        }
    }
}

/// A boolean circuit as a sequence of gates
#[derive(Clone, Debug)]
pub struct Circuit {
    /// Ordered list of gates (topologically sorted)
    pub gates: Vec<Gate>,
    /// Total number of wires in the circuit
    pub num_wires: usize,
}

impl Circuit {
    /// Create a new circuit
    pub fn new(gates: Vec<Gate>, num_wires: usize) -> Self {
        Self { gates, num_wires }
    }

    /// Evaluate the circuit on a given input
    ///
    /// Input bits are encoded in the least significant bits of `input`.
    /// Output is similarly encoded in the result.
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

    /// Generate a random circuit (for testing)
    ///
    /// Uses a subset of control functions similar to R57 circuits.
    ///
    /// # Panics
    /// Panics if `num_wires > u16::MAX` since wire indices are stored as `u16`.
    pub fn random_r57(num_wires: usize, num_gates: usize) -> Self {
        assert!(
            num_wires <= u16::MAX as usize,
            "num_wires={} exceeds u16::MAX={}",
            num_wires,
            u16::MAX
        );
        let mut rng = rand::thread_rng();
        let funcs = [
            ControlFunction::And,
            ControlFunction::Xor,
            ControlFunction::Or,
            ControlFunction::Nand,
        ];
        let gates: Vec<Gate> = (0..num_gates)
            .map(|_| {
                let out = rng.gen_range(0..num_wires) as u16;
                let a = rng.gen_range(0..num_wires) as u16;
                let b = rng.gen_range(0..num_wires) as u16;
                let func = funcs[rng.gen_range(0..funcs.len())];
                Gate::new(out, a, b, func)
            })
            .collect();
        Self { gates, num_wires }
    }

    /// Create an identity circuit that doesn't modify any wires
    pub fn identity(num_wires: usize) -> Self {
        Self {
            gates: vec![],
            num_wires,
        }
    }

    /// Get the number of gates in this circuit
    pub fn size(&self) -> usize {
        self.gates.len()
    }
}

/// Proof of equivalence between two circuits
///
/// In the full Ma-Dai-Shi construction, this would be an EF (Equivalence Framework)
/// proof that can be verified by a polynomial-time verifier.
#[derive(Clone, Debug)]
pub struct EquivalenceProof {
    /// Hash of the first circuit
    pub circuit_a_hash: [u8; 32],
    /// Hash of the second circuit
    pub circuit_b_hash: [u8; 32],
    /// Proof steps (symbolic representation)
    pub proof_steps: Vec<String>,
}

impl EquivalenceProof {
    /// Create a dummy proof (for testing/development)
    ///
    /// This should only be used when the circuits are known to be equivalent.
    pub fn dummy(circuit: &Circuit) -> Self {
        use sha2::{Digest, Sha256};
        let mut hasher = Sha256::new();
        hasher.update(format!("{:?}", circuit.gates));
        let hash: [u8; 32] = hasher.finalize().into();
        Self {
            circuit_a_hash: hash,
            circuit_b_hash: hash,
            proof_steps: vec!["identity".to_string()],
        }
    }

    /// Get the proof size in bytes (for parameter estimation)
    pub fn size(&self) -> usize {
        64 + self.proof_steps.len() * 64
    }
}

/// EF (Equivalence Framework) proof wrapper
#[derive(Clone, Debug)]
pub struct EFProof {
    /// Size of the proof in bytes
    pub proof_size: usize,
}

/// Convert an EquivalenceProof to an EFProof for size estimation
pub fn to_ef_proof(proof: &EquivalenceProof) -> EFProof {
    EFProof {
        proof_size: proof.proof_steps.len() * 64 + 128,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_control_functions() {
        assert!(!ControlFunction::F.evaluate(true, true));
        assert!(ControlFunction::And.evaluate(true, true));
        assert!(!ControlFunction::And.evaluate(true, false));
        assert!(ControlFunction::Xor.evaluate(true, false));
        assert!(!ControlFunction::Xor.evaluate(true, true));
        assert!(ControlFunction::Or.evaluate(false, true));
        assert!(ControlFunction::Nand.evaluate(true, false));
    }

    #[test]
    fn test_circuit_evaluate() {
        let gates = vec![Gate::new(2, 0, 1, ControlFunction::And)];
        let circuit = Circuit::new(gates, 3);

        assert_eq!(circuit.evaluate(0b11), 0b111);
        assert_eq!(circuit.evaluate(0b01), 0b001);
        assert_eq!(circuit.evaluate(0b10), 0b010);
    }

    #[test]
    fn test_random_circuit() {
        let circuit = Circuit::random_r57(8, 10);
        assert_eq!(circuit.gates.len(), 10);
        assert_eq!(circuit.num_wires, 8);
    }

    #[test]
    fn test_large_circuit_over_256_wires() {
        let num_wires = 300;
        let circuit = Circuit::random_r57(num_wires, 20);
        assert_eq!(circuit.num_wires, num_wires);

        for gate in &circuit.gates {
            assert!(gate.output_wire < num_wires as u16);
            assert!(gate.input_wire_a < num_wires as u16);
            assert!(gate.input_wire_b < num_wires as u16);
        }
    }
}
