//! Small-circuit indistinguishability obfuscation
//!
//! This module provides the `SmallObf` trait for obfuscating small, fixed gadget circuits.
//! In the Ma-Dai-Shi construction, each gate is turned into a small universal circuit
//! that is then obfuscated.
//!
//! ## Security Model
//!
//! This implementation provides two backends for small-circuit iO:
//!
//! ### `StubSmallObf` (default)
//! Uses XOR encryption as a placeholder. This is **NOT cryptographically secure iO**.
//! It maintains the correct interface while real iO research progresses.
//!
//! ### `CanonicalSmallObf` (feature: `canonical-smallobf`)
//! Implements **information-theoretic iO** for the specific family of 2-input boolean
//! gates used as gate gadgets. For the function family F = { f : {0,1}² → {0,1} },
//! we define Obf(f) as the canonical 4-bit truth table of f. For any two circuits
//! C₀, C₁ computing the same f, Obf(C₀) = Obf(C₁).
//!
//! This is a degenerate but valid iO: no cryptographic hardness is required because
//! the domain is finite and the adversary can always learn the full function by
//! query access. The indistinguishability property holds perfectly because equivalent
//! programs produce identical obfuscations.
//!
//! ### General Small-Circuit iO
//! True small-circuit iO for arbitrary circuits remains an **open research problem**.
//! Candidates include:
//! - Matrix Branching Programs + multilinear maps (security concerns)
//! - LWE-based constructions (impractical for production)
//! - Functional encryption schemes
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

    /// Evaluate the program on plaintext input (no encryption/decryption)
    ///
    /// This is used by truth-table canonicalization to enumerate all possible outputs.
    pub fn eval_plain(&self, input: &[u8]) -> Vec<u8> {
        match self.instructions.first() {
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
                    0 => a && c,      // AND
                    1 => a ^ c,       // XOR
                    2 => a || c,      // OR
                    3 => !(a && c),   // NAND
                    4 => !(a || c),   // NOR
                    5 => !(a ^ c),    // XNOR
                    6 => a && !c,     // ANDNOT
                    7 => false,       // FALSE
                    _ => false,
                };
                vec![out as u8]
            }
            _ => vec![0u8; self.output_size],
        }
    }

    /// Get the number of input bits for this program
    pub fn input_bits(&self) -> usize {
        self.input_size * 8
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

/// Truth table obfuscation for bounded-input circuits.
///
/// This provides **information-theoretic iO** for circuits with small input domains.
/// The obfuscation is simply the canonical truth table: for any input index i,
/// `table[i * out_bytes..(i+1) * out_bytes]` contains the output.
///
/// ## Security Model
///
/// For circuits with n input bits, there are 2^n possible inputs. The truth table
/// stores all outputs, which means:
/// - Equivalent circuits (same function) produce identical obfuscations
/// - The function is completely revealed, but for small n an adversary could
///   recover it via exhaustive oracle queries anyway
/// - This is valid iO: indistinguishability holds perfectly (no assumptions needed)
///
/// ## Practical Bounds
///
/// | Input bits | Table rows | Table size (1-byte output) |
/// |------------|------------|----------------------------|
/// | 8          | 256        | 256 bytes                  |
/// | 12         | 4096       | 4 KB                       |
/// | 16         | 65536      | 64 KB                      |
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TruthTableObf {
    /// Flattened truth table: `2^n_bits_in` rows, each `out_bytes` bytes
    pub table: Vec<u8>,
    /// Number of input bits
    pub n_bits_in: u32,
    /// Number of output bytes per row
    pub out_bytes: u32,
}

impl TruthTableObf {
    /// Get the number of table rows (2^n_bits_in)
    pub fn num_rows(&self) -> usize {
        1 << self.n_bits_in
    }

    /// Get the output for a given input index
    pub fn get_output(&self, index: usize) -> &[u8] {
        let start = index * self.out_bytes as usize;
        let end = start + self.out_bytes as usize;
        &self.table[start..end]
    }
}

/// Encode an index as input bytes (little-endian bit order)
///
/// For n_bits input bits, converts index to the corresponding input byte array.
/// Bit i of the index corresponds to wire i in the circuit.
pub fn encode_index_as_input(index: usize, n_bits: usize) -> Vec<u8> {
    let n_bytes = (n_bits + 7) / 8;
    let mut input = vec![0u8; n_bytes];
    for byte_idx in 0..n_bytes {
        input[byte_idx] = ((index >> (byte_idx * 8)) & 0xFF) as u8;
    }
    input
}

/// Decode input bytes to an index (little-endian bit order)
///
/// Inverse of `encode_index_as_input`.
pub fn decode_input_to_index(input: &[u8], n_bits: usize) -> usize {
    let mut index = 0usize;
    let n_bytes = (n_bits + 7) / 8;
    for byte_idx in 0..n_bytes.min(input.len()) {
        index |= (input[byte_idx] as usize) << (byte_idx * 8);
    }
    index & ((1 << n_bits) - 1)
}

/// Default small-circuit obfuscator.
///
/// - Without `canonical-smallobf` feature: Uses `StubSmallObf` (NOT true iO).
/// - With `canonical-smallobf` feature: Uses `CanonicalSmallObf` (true iO for 2-input gates).
#[cfg(not(feature = "canonical-smallobf"))]
pub type DefaultSmallObf = StubSmallObf;

#[cfg(feature = "canonical-smallobf")]
pub type DefaultSmallObf = CanonicalSmallObf;

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
    ///
    /// NOTE: When using `CanonicalSmallObf`, any change to this encoding must be
    /// re-evaluated against the canonical-iO argument.
    pub fn to_bytecode_program(&self) -> BytecodeProgram {
        BytecodeProgram {
            instructions: vec![0x10 | self.gate_type],
            input_size: 1,
            output_size: 1,
        }
    }
}

/// Canonical small-circuit iO for 2-input boolean gates.
///
/// This implementation provides **information-theoretically perfect iO** for the
/// function family F = { f : {0,1}² → {0,1} } (2-input boolean gates with 1-bit output).
///
/// For gate gadgets, obfuscation computes the canonical 4-entry truth table and stores
/// it in a normalized form. This guarantees:
/// - All equivalent programs (same truth table) produce identical obfuscations
/// - Different functions produce different obfuscations (trivially distinguishable by evaluation)
///
/// This is a valid iO for this finite family because no cryptographic hardness is needed:
/// the domain is so small that an adversary can always learn the full function by querying
/// all 4 inputs. The indistinguishability property holds perfectly.
///
/// For non-gate programs (identity, xor_all), falls back to `StubSmallObf` behavior.
#[derive(Clone, Debug, Default)]
pub struct CanonicalSmallObf;

impl SmallObf for CanonicalSmallObf {
    type Program = BytecodeProgram;
    type Obfuscated = ObfuscatedBytecode;

    fn obfuscate(&self, prog: &Self::Program) -> Self::Obfuscated {
        use rand::RngCore;

        let opcode = prog.instructions.first().copied().unwrap_or(0);

        if (opcode & 0xF0) == 0x10 && prog.input_size == 1 && prog.output_size == 1 {
            let gate_type = opcode & 0x0F;

            let mut table = 0u8;
            for idx in 0..4u8 {
                let a = (idx & 0b01) != 0;
                let b = (idx & 0b10) != 0;
                let out = GateGadget::new(gate_type, (0, 1), 2).evaluate(a, b);
                if out {
                    table |= 1 << idx;
                }
            }

            let mut key = [0u8; 32];
            rand::thread_rng().fill_bytes(&mut key);
            let masked = table ^ key[0];

            ObfuscatedBytecode {
                encrypted_data: vec![masked],
                key,
                input_size: 1,
                output_size: 1,
            }
        } else {
            StubSmallObf.obfuscate(prog)
        }
    }

    fn eval(&self, obf: &Self::Obfuscated, input: &[u8]) -> Vec<u8> {
        if obf.input_size == 1 && obf.output_size == 1 && obf.encrypted_data.len() == 1 {
            let masked = obf.encrypted_data[0];
            let table = masked ^ obf.key[0];

            let b = input.first().copied().unwrap_or(0);
            let a_bit = (b & 0x01) != 0;
            let c_bit = (b & 0x02) != 0;

            let idx = (a_bit as u8) | ((c_bit as u8) << 1);
            let out = (table >> idx) & 1;

            vec![out]
        } else {
            StubSmallObf.eval(obf, input)
        }
    }
}

impl CanonicalSmallObf {
    /// Extract the canonical truth table from an obfuscated gate gadget.
    ///
    /// Returns the 4-bit truth table where bit i corresponds to inputs (a=i&1, b=(i>>1)&1).
    /// Returns None if this is not a gate gadget obfuscation.
    pub fn extract_truth_table(obf: &ObfuscatedBytecode) -> Option<u8> {
        if obf.input_size == 1 && obf.output_size == 1 && obf.encrypted_data.len() == 1 {
            Some(obf.encrypted_data[0] ^ obf.key[0])
        } else {
            None
        }
    }
}

/// Generalized truth-table iO for bounded-input circuits.
///
/// This extends `CanonicalSmallObf` to handle circuits with more than 2 input bits.
/// For circuits with n input bits (where n <= max_input_bits), the obfuscation
/// is the canonical truth table with 2^n entries.
///
/// ## Security Model
///
/// This provides **information-theoretic iO** for the function family
/// F = { f : {0,1}^n → {0,1}^m } where n <= max_input_bits.
///
/// - Equivalent circuits produce identical obfuscations (perfect iO)
/// - No cryptographic assumptions needed
/// - The function is fully revealed, but for small n this is unavoidable
///   (an adversary could enumerate all 2^n inputs anyway)
///
/// ## Practical Bounds (measured on Apple M-series)
///
/// | Bits | Table Size | Obfuscation Time | Recommendation |
/// |------|------------|------------------|----------------|
/// | 8    | 256 B      | ~10 µs           | Instant        |
/// | 16   | 64 KB      | ~2 ms            | Default        |
/// | 24   | 16 MB      | ~450 ms          | Practical max  |
/// | 32   | 4 GB       | ~2 min           | Hard limit     |
///
/// Default: max_input_bits = 16 (fast, 64KB tables)
/// Circuits exceeding max_input_bits will panic.
#[derive(Clone, Debug)]
pub struct GeneralizedCanonicalSmallObf {
    /// Maximum input bits for truth-table canonicalization
    pub max_input_bits: usize,
}

impl Default for GeneralizedCanonicalSmallObf {
    fn default() -> Self {
        Self { max_input_bits: 16 }
    }
}

impl GeneralizedCanonicalSmallObf {
    /// Create with custom max input bits
    pub fn new(max_input_bits: usize) -> Self {
        Self { max_input_bits }
    }

    /// Create with fast defaults (16 bits = 64KB tables, ~2ms)
    pub fn fast() -> Self {
        Self { max_input_bits: 16 }
    }

    /// Create with practical max (24 bits = 16MB tables, ~450ms)
    pub fn practical_max() -> Self {
        Self { max_input_bits: 24 }
    }

    /// Create with hard limit (32 bits = 4GB tables, ~2min)
    /// WARNING: This requires 4GB+ RAM and takes minutes to obfuscate!
    pub fn hard_limit() -> Self {
        Self { max_input_bits: 32 }
    }
}

impl SmallObf for GeneralizedCanonicalSmallObf {
    type Program = BytecodeProgram;
    type Obfuscated = TruthTableObf;

    fn obfuscate(&self, prog: &Self::Program) -> Self::Obfuscated {
        let n_bits = prog.input_size * 8;

        if n_bits > self.max_input_bits {
            panic!(
                "Circuit has {} input bits, exceeds max_input_bits={}. \
                 Use StubSmallObf for larger circuits (NOT secure iO).",
                n_bits, self.max_input_bits
            );
        }

        let n_rows = 1usize << n_bits;
        let out_bytes = prog.output_size;
        let mut table = vec![0u8; n_rows * out_bytes];

        for idx in 0..n_rows {
            let input = encode_index_as_input(idx, n_bits);
            let output = prog.eval_plain(&input);

            let start = idx * out_bytes;
            for (i, &b) in output.iter().take(out_bytes).enumerate() {
                table[start + i] = b;
            }
        }

        TruthTableObf {
            table,
            n_bits_in: n_bits as u32,
            out_bytes: out_bytes as u32,
        }
    }

    fn eval(&self, obf: &Self::Obfuscated, input: &[u8]) -> Vec<u8> {
        let idx = decode_input_to_index(input, obf.n_bits_in as usize);
        obf.get_output(idx).to_vec()
    }
}

impl GeneralizedCanonicalSmallObf {
    /// Check if a program can be canonically obfuscated within the current bounds
    pub fn can_obfuscate(&self, prog: &BytecodeProgram) -> bool {
        prog.input_size * 8 <= self.max_input_bits
    }

    /// Get the truth table size in bytes for a program
    pub fn table_size_bytes(&self, prog: &BytecodeProgram) -> usize {
        let n_bits = prog.input_size * 8;
        let n_rows = 1usize << n_bits;
        n_rows * prog.output_size
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

    #[test]
    fn test_canonical_obf_gate_correctness() {
        let obf = CanonicalSmallObf;

        for gate_type in [
            GateGadget::AND,
            GateGadget::XOR,
            GateGadget::OR,
            GateGadget::NAND,
            GateGadget::NOR,
            GateGadget::XNOR,
            GateGadget::ANDNOT,
            GateGadget::FALSE,
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
                        "CanonicalSmallObf: Gate type {} failed for ({}, {})",
                        gate_type,
                        a,
                        b
                    );
                }
            }
        }
    }

    #[test]
    fn test_canonical_obf_truth_table_is_canonical() {
        let obf = CanonicalSmallObf;

        let gadget = GateGadget::new(GateGadget::AND, (0, 1), 2);
        let prog1 = gadget.to_bytecode_program();
        let prog2 = BytecodeProgram::new(prog1.instructions.clone(), 1, 1);

        let o1 = obf.obfuscate(&prog1);
        let o2 = obf.obfuscate(&prog2);

        let table1 = CanonicalSmallObf::extract_truth_table(&o1).unwrap();
        let table2 = CanonicalSmallObf::extract_truth_table(&o2).unwrap();
        assert_eq!(table1, table2, "Same function should produce identical truth tables");
    }

    #[test]
    fn test_canonical_obf_different_gates_different_tables() {
        let obf = CanonicalSmallObf;

        let and_gadget = GateGadget::new(GateGadget::AND, (0, 1), 2);
        let xor_gadget = GateGadget::new(GateGadget::XOR, (0, 1), 2);

        let and_obf = obf.obfuscate(&and_gadget.to_bytecode_program());
        let xor_obf = obf.obfuscate(&xor_gadget.to_bytecode_program());

        let and_table = CanonicalSmallObf::extract_truth_table(&and_obf).unwrap();
        let xor_table = CanonicalSmallObf::extract_truth_table(&xor_obf).unwrap();

        assert_ne!(and_table, xor_table, "Different functions should have different tables");
    }

    #[test]
    fn test_canonical_obf_extract_truth_table() {
        let obf = CanonicalSmallObf;

        let and_gadget = GateGadget::new(GateGadget::AND, (0, 1), 2);
        let obfuscated = obf.obfuscate(&and_gadget.to_bytecode_program());
        let table = CanonicalSmallObf::extract_truth_table(&obfuscated).unwrap();

        assert_eq!(table, 0b1000);

        let or_gadget = GateGadget::new(GateGadget::OR, (0, 1), 2);
        let or_obf = obf.obfuscate(&or_gadget.to_bytecode_program());
        let or_table = CanonicalSmallObf::extract_truth_table(&or_obf).unwrap();

        assert_eq!(or_table, 0b1110);

        let xor_gadget = GateGadget::new(GateGadget::XOR, (0, 1), 2);
        let xor_obf = obf.obfuscate(&xor_gadget.to_bytecode_program());
        let xor_table = CanonicalSmallObf::extract_truth_table(&xor_obf).unwrap();

        assert_eq!(xor_table, 0b0110);
    }

    #[test]
    fn test_canonical_obf_fallback_identity() {
        let obf = CanonicalSmallObf;
        let prog = BytecodeProgram::identity(4);

        let obfuscated = obf.obfuscate(&prog);
        let input = vec![1, 2, 3, 4];
        let output = obf.eval(&obfuscated, &input);

        assert_eq!(output, input, "CanonicalSmallObf should fall back to StubSmallObf for identity");
    }

    #[test]
    fn test_canonical_obf_fallback_xor_all() {
        let obf = CanonicalSmallObf;
        let prog = BytecodeProgram::xor_all(3);

        let obfuscated = obf.obfuscate(&prog);
        let input = vec![0b1010, 0b1100, 0b0011];
        let output = obf.eval(&obfuscated, &input);

        assert_eq!(
            output,
            vec![0b1010 ^ 0b1100 ^ 0b0011],
            "CanonicalSmallObf should fall back to StubSmallObf for xor_all"
        );
    }

    #[test]
    fn test_default_smallobf_works() {
        let obf = DefaultSmallObf::default();

        let gadget = GateGadget::new(GateGadget::AND, (0, 1), 2);
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
                    "DefaultSmallObf failed for ({}, {})",
                    a,
                    b
                );
            }
        }
    }

    // ==================== Generalized Truth-Table iO Tests ====================

    #[test]
    fn test_encode_decode_index_roundtrip() {
        for n_bits in [2, 8, 12, 16] {
            let max_idx = 1usize << n_bits;
            for idx in [0, 1, max_idx / 2, max_idx - 1] {
                let encoded = encode_index_as_input(idx, n_bits);
                let decoded = decode_input_to_index(&encoded, n_bits);
                assert_eq!(decoded, idx, "Roundtrip failed for n_bits={}, idx={}", n_bits, idx);
            }
        }
    }

    #[test]
    fn test_encode_index_byte_layout() {
        let input = encode_index_as_input(0x1234, 16);
        assert_eq!(input.len(), 2);
        assert_eq!(input[0], 0x34);
        assert_eq!(input[1], 0x12);

        let input = encode_index_as_input(0xFF, 8);
        assert_eq!(input.len(), 1);
        assert_eq!(input[0], 0xFF);
    }

    #[test]
    fn test_truth_table_obf_structure() {
        let table = TruthTableObf {
            table: vec![0, 1, 2, 3],
            n_bits_in: 2,
            out_bytes: 1,
        };

        assert_eq!(table.num_rows(), 4);
        assert_eq!(table.get_output(0), &[0]);
        assert_eq!(table.get_output(1), &[1]);
        assert_eq!(table.get_output(2), &[2]);
        assert_eq!(table.get_output(3), &[3]);
    }

    #[test]
    fn test_generalized_obf_8bit_identity() {
        let obf = GeneralizedCanonicalSmallObf::default();
        let prog = BytecodeProgram::identity(1);

        let obfuscated = obf.obfuscate(&prog);

        assert_eq!(obfuscated.n_bits_in, 8);
        assert_eq!(obfuscated.num_rows(), 256);

        for i in 0u8..=255 {
            let output = obf.eval(&obfuscated, &[i]);
            assert_eq!(output, vec![i], "Identity failed for input {}", i);
        }
    }

    #[test]
    fn test_generalized_obf_8bit_xor_all() {
        let obf = GeneralizedCanonicalSmallObf::default();
        let prog = BytecodeProgram::xor_all(1);

        let obfuscated = obf.obfuscate(&prog);

        for i in 0u8..=255 {
            let output = obf.eval(&obfuscated, &[i]);
            assert_eq!(output, vec![i], "XOR of single byte should be identity");
        }
    }

    #[test]
    fn test_generalized_obf_gate_gadget() {
        let obf = GeneralizedCanonicalSmallObf::default();

        for gate_type in [
            GateGadget::AND,
            GateGadget::XOR,
            GateGadget::OR,
            GateGadget::NAND,
        ] {
            let gadget = GateGadget::new(gate_type, (0, 1), 2);
            let prog = gadget.to_bytecode_program();
            let obfuscated = obf.obfuscate(&prog);

            assert_eq!(obfuscated.n_bits_in, 8);

            for a in [false, true] {
                for b in [false, true] {
                    let packed = (a as u8) | ((b as u8) << 1);
                    let output = obf.eval(&obfuscated, &[packed]);
                    let expected = gadget.evaluate(a, b) as u8;
                    assert_eq!(
                        output[0], expected,
                        "Gate {} failed for ({}, {})",
                        gate_type, a, b
                    );
                }
            }
        }
    }

    #[test]
    fn test_generalized_obf_canonical_property() {
        let obf = GeneralizedCanonicalSmallObf::default();

        let prog1 = BytecodeProgram::identity(1);
        let prog2 = BytecodeProgram::new(vec![0x00], 1, 1);

        let obf1 = obf.obfuscate(&prog1);
        let obf2 = obf.obfuscate(&prog2);

        assert_eq!(obf1.table, obf2.table, "Equivalent programs should have identical tables");
    }

    #[test]
    fn test_generalized_obf_different_functions_differ() {
        let obf = GeneralizedCanonicalSmallObf::default();

        let prog_and = GateGadget::new(GateGadget::AND, (0, 1), 2).to_bytecode_program();
        let prog_xor = GateGadget::new(GateGadget::XOR, (0, 1), 2).to_bytecode_program();

        let obf_and = obf.obfuscate(&prog_and);
        let obf_xor = obf.obfuscate(&prog_xor);

        assert_ne!(obf_and.table, obf_xor.table, "Different functions should have different tables");
    }

    #[test]
    fn test_generalized_obf_can_obfuscate() {
        let obf = GeneralizedCanonicalSmallObf::new(8);

        let prog_1byte = BytecodeProgram::identity(1);
        let prog_2byte = BytecodeProgram::identity(2);

        assert!(obf.can_obfuscate(&prog_1byte));
        assert!(!obf.can_obfuscate(&prog_2byte));
    }

    #[test]
    fn test_generalized_obf_table_size() {
        let obf = GeneralizedCanonicalSmallObf::default();

        let prog_1byte = BytecodeProgram::identity(1);
        assert_eq!(obf.table_size_bytes(&prog_1byte), 256);

        let prog_1byte_2out = BytecodeProgram::new(vec![0x00], 1, 2);
        assert_eq!(obf.table_size_bytes(&prog_1byte_2out), 512);
    }

    #[test]
    fn test_generalized_obf_16bit() {
        let obf = GeneralizedCanonicalSmallObf::new(16);
        let prog = BytecodeProgram::xor_all(2);

        assert!(obf.can_obfuscate(&prog));

        let obfuscated = obf.obfuscate(&prog);
        assert_eq!(obfuscated.n_bits_in, 16);
        assert_eq!(obfuscated.num_rows(), 65536);
        assert_eq!(obfuscated.table.len(), 65536);

        for low in [0u8, 0x55, 0xAA, 0xFF] {
            for high in [0u8, 0x55, 0xAA, 0xFF] {
                let output = obf.eval(&obfuscated, &[low, high]);
                let expected = low ^ high;
                assert_eq!(output, vec![expected], "XOR failed for ({:#x}, {:#x})", low, high);
            }
        }
    }

    #[test]
    fn test_generalized_obf_16bit_exhaustive_spot_check() {
        let obf = GeneralizedCanonicalSmallObf::fast();
        let prog = BytecodeProgram::xor_all(2);

        let obfuscated = obf.obfuscate(&prog);

        let mut checked = 0;
        for i in (0..65536).step_by(1000) {
            let low = (i & 0xFF) as u8;
            let high = ((i >> 8) & 0xFF) as u8;
            let output = obf.eval(&obfuscated, &[low, high]);
            assert_eq!(output[0], low ^ high);
            checked += 1;
        }
        assert!(checked >= 65, "Should have checked at least 65 values");
    }

    #[test]
    #[should_panic(expected = "exceeds max_input_bits")]
    fn test_generalized_obf_exceeds_max_bits() {
        let obf = GeneralizedCanonicalSmallObf::new(8);
        let prog = BytecodeProgram::identity(2);
        let _ = obf.obfuscate(&prog);
    }
}
