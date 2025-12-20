//! Small-circuit indistinguishability obfuscation
//!
//! This module provides the `SmallObf` trait for obfuscating small, fixed gadget circuits.
//! In the Ma-Dai-Shi construction, each gate is turned into a small universal circuit
//! that is then obfuscated.
//!
//! ## Security Assumption
//!
//! This implementation treats small-circuit iO as an **explicit cryptographic assumption**.
//! The stub implementation uses conventional encryption (NOT cryptographically iO).
//!
//! A production implementation would require:
//! - A concrete iO candidate (e.g., from functional encryption or multilinear maps)
//! - Or integration with an external iO implementation
//!
//! ## Paper Reference
//!
//! See §5.2 of Ma-Dai-Shi 2025 for the gate gadget construction.

use std::fmt::Debug;

/// Trait for small-circuit indistinguishability obfuscation
///
/// WARNING: Implementing true iO is an open research problem.
/// This trait defines the interface; actual security depends on the implementation.
pub trait SmallObf: Clone + Debug {
    /// The type of programs that can be obfuscated
    type Program: Clone + Debug;

    /// The type of obfuscated programs
    type Obfuscated: Clone + Debug;

    /// Obfuscate a program
    ///
    /// The obfuscated program should compute the same function as the original,
    /// but reveal nothing about the implementation details.
    fn obfuscate(&self, prog: &Self::Program) -> Self::Obfuscated;

    /// Evaluate an obfuscated program on input
    fn eval(&self, obf: &Self::Obfuscated, input: &[u8]) -> Vec<u8>;
}

/// A simple bytecode program (for stub implementation)
#[derive(Clone, Debug)]
pub struct BytecodeProgram {
    /// The bytecode instructions
    pub instructions: Vec<u8>,
    /// Number of input bytes
    pub input_size: usize,
    /// Number of output bytes
    pub output_size: usize,
}

impl BytecodeProgram {
    /// Create a new bytecode program
    pub fn new(instructions: Vec<u8>, input_size: usize, output_size: usize) -> Self {
        Self {
            instructions,
            input_size,
            output_size,
        }
    }

    /// Create a program that computes XOR of all input bytes
    pub fn xor_all(input_size: usize) -> Self {
        Self {
            instructions: vec![0x01],
            input_size,
            output_size: 1,
        }
    }

    /// Create a program that copies input to output
    pub fn identity(size: usize) -> Self {
        Self {
            instructions: vec![0x00],
            input_size: size,
            output_size: size,
        }
    }
}

/// An "obfuscated" bytecode program (stub implementation)
#[derive(Clone, Debug)]
pub struct ObfuscatedBytecode {
    /// Encrypted bytecode (in real iO, this would be truly obfuscated)
    pub encrypted_data: Vec<u8>,
    /// Encryption key (in real iO, this would be incorporated into the obfuscation)
    pub key: [u8; 32],
    /// Program metadata
    pub input_size: usize,
    pub output_size: usize,
}

/// Stub small-circuit obfuscator
///
/// WARNING: This is NOT cryptographically secure iO.
/// It uses simple XOR encryption as a placeholder.
/// This maintains the correct interface while real iO research progresses.
#[derive(Clone, Debug, Default)]
pub struct StubSmallObf;

impl SmallObf for StubSmallObf {
    type Program = BytecodeProgram;
    type Obfuscated = ObfuscatedBytecode;

    fn obfuscate(&self, prog: &Self::Program) -> Self::Obfuscated {
        use rand::RngCore;

        let mut key = [0u8; 32];
        rand::thread_rng().fill_bytes(&mut key);

        let encrypted_data: Vec<u8> = prog
            .instructions
            .iter()
            .enumerate()
            .map(|(i, &b)| b ^ key[i % 32])
            .collect();

        ObfuscatedBytecode {
            encrypted_data,
            key,
            input_size: prog.input_size,
            output_size: prog.output_size,
        }
    }

    fn eval(&self, obf: &Self::Obfuscated, input: &[u8]) -> Vec<u8> {
        let decrypted: Vec<u8> = obf
            .encrypted_data
            .iter()
            .enumerate()
            .map(|(i, &b)| b ^ obf.key[i % 32])
            .collect();

        match decrypted.first() {
            Some(0x00) => input.to_vec(),
            Some(0x01) => {
                let xor_result = input.iter().fold(0u8, |acc, &b| acc ^ b);
                vec![xor_result]
            }
            Some(op) if (op & 0xF0) == 0x10 => {
                let gate_type = op & 0x0F;
                let b = input.first().copied().unwrap_or(0);
                let a = (b & 0x01) != 0;
                let c = (b & 0x02) != 0;
                let out = match gate_type {
                    GateGadget::AND => a && c,
                    GateGadget::XOR => a ^ c,
                    GateGadget::OR => a || c,
                    GateGadget::NAND => !(a && c),
                    GateGadget::NOR => !(a || c),
                    GateGadget::XNOR => !(a ^ c),
                    GateGadget::ANDNOT => a && !c,
                    GateGadget::FALSE => false,
                    _ => false,
                };
                vec![out as u8]
            }
            _ => vec![0u8; obf.output_size],
        }
    }
}

/// Gate gadget for LiO construction
///
/// Represents the "universal gate" circuit that is obfuscated in the LiO scheme.
/// For a 2-input boolean gate, this encapsulates:
/// - Input wire labels (encrypted)
/// - Output wire label computation
/// - MAC verification
#[derive(Clone, Debug)]
pub struct GateGadget {
    /// Gate type (AND, XOR, etc.)
    pub gate_type: u8,
    /// Input wire indices
    pub input_wires: (usize, usize),
    /// Output wire index
    pub output_wire: usize,
}

impl GateGadget {
    /// Gate type constants
    pub const AND: u8 = 0;
    pub const XOR: u8 = 1;
    pub const OR: u8 = 2;
    pub const NAND: u8 = 3;
    pub const NOR: u8 = 4;
    pub const XNOR: u8 = 5;
    pub const ANDNOT: u8 = 6;
    pub const FALSE: u8 = 7;

    /// Create a new gate gadget
    pub fn new(gate_type: u8, input_wires: (usize, usize), output_wire: usize) -> Self {
        Self {
            gate_type,
            input_wires,
            output_wire,
        }
    }

    /// Evaluate the gate on plaintext inputs
    pub fn evaluate(&self, a: bool, b: bool) -> bool {
        match self.gate_type {
            Self::AND => a && b,
            Self::XOR => a ^ b,
            Self::OR => a || b,
            Self::NAND => !(a && b),
            Self::NOR => !(a || b),
            Self::XNOR => !(a ^ b),
            Self::ANDNOT => a && !b,
            Self::FALSE => false,
            _ => false,
        }
    }

    /// Convert the gate gadget to a bytecode program for SmallObf
    ///
    /// The bytecode format uses opcode 0x10 | gate_type to identify gate operations.
    /// Input: 1 byte where bit 0 = a, bit 1 = b
    /// Output: 1 byte where bit 0 = result
    pub fn to_bytecode_program(&self) -> BytecodeProgram {
        BytecodeProgram {
            instructions: vec![0x10 | self.gate_type],
            input_size: 1,
            output_size: 1,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_stub_obf_identity() {
        let obf = StubSmallObf;
        let prog = BytecodeProgram::identity(4);

        let obfuscated = obf.obfuscate(&prog);
        let input = vec![1, 2, 3, 4];
        let output = obf.eval(&obfuscated, &input);

        assert_eq!(output, input);
    }

    #[test]
    fn test_stub_obf_xor() {
        let obf = StubSmallObf;
        let prog = BytecodeProgram::xor_all(3);

        let obfuscated = obf.obfuscate(&prog);
        let input = vec![0b1010, 0b1100, 0b0011];
        let output = obf.eval(&obfuscated, &input);

        assert_eq!(output, vec![0b1010 ^ 0b1100 ^ 0b0011]);
    }

    #[test]
    fn test_gate_gadget_evaluate() {
        let and_gate = GateGadget::new(GateGadget::AND, (0, 1), 2);
        assert!(and_gate.evaluate(true, true));
        assert!(!and_gate.evaluate(true, false));

        let xor_gate = GateGadget::new(GateGadget::XOR, (0, 1), 2);
        assert!(xor_gate.evaluate(true, false));
        assert!(!xor_gate.evaluate(true, true));
    }

    #[test]
    fn test_gate_gadget_to_bytecode_and_eval() {
        let obf = StubSmallObf;

        for gate_type in [
            GateGadget::AND,
            GateGadget::XOR,
            GateGadget::OR,
            GateGadget::NAND,
            GateGadget::NOR,
            GateGadget::XNOR,
        ] {
            let gadget = GateGadget::new(gate_type, (0, 1), 2);
            let bytecode = gadget.to_bytecode_program();
            let obfuscated = obf.obfuscate(&bytecode);

            for a in [false, true] {
                for b in [false, true] {
                    let packed = (a as u8) | ((b as u8) << 1);
                    let out = obf.eval(&obfuscated, &[packed]);
                    let expected = gadget.evaluate(a, b);
                    assert_eq!(
                        (out[0] & 1) == 1,
                        expected,
                        "Gate type {} failed for ({}, {})",
                        gate_type,
                        a,
                        b
                    );
                }
            }
        }
    }
}
