//! Local Indistinguishability Obfuscation (LiO)
//!
//! Implementation of the LiO construction from §5 of Ma-Dai-Shi 2025.
//!
//! LiO provides security for circuits that differ in only s = O(log N) gates.
//! The full Ma-Dai-Shi iO is achieved by combining LiO with padding that
//! ensures any two equivalent circuits become transitively s-equivalent.
//!
//! ## Construction Overview
//!
//! For each gate g in the circuit:
//! 1. Generate wire encryption keys using puncturable PRF
//! 2. Create encrypted truth table entries
//! 3. Add MAC tags for verification
//! 4. Wrap in small-circuit iO for the gate gadget
//!
//! ## Security
//!
//! LiO security relies on:
//! - FHE (for SEH construction)
//! - Puncturable PRF (for wire keys)
//! - PRG (for mask generation)
//! - Small-circuit iO (for gate gadgets)
//!
//! # WARNING: Current Implementation Status (Milestone 0/1)
//!
//! **This implementation is NOT cryptographically secure.** It provides:
//!
//! - [OK] Functional correctness: `ObfuscatedLiO::evaluate(x) == Circuit::evaluate(x)`
//! - [OK] Real GGM-based PRF and SHA-256 PRG
//! - [!] Wire labels are NOT real: uses `(a, b, LSB(wire_a), LSB(wire_b))` instead of
//!   per-wire random λ-bit labels as required by the paper
//! - [!] MACs are generated but NEVER verified during evaluation
//! - [!] SEH digest is computed but NEVER used for consistency checks
//! - [!] SmallObf (gate gadget iO) is NOT integrated
//! - [!] PRF puncturing is implemented but NOT used
//!
//! ## What's Real vs. Stub
//!
//! | Component | Status | Notes |
//! |-----------|--------|-------|
//! | GGM PRF | Real | Standard textbook construction over SHA-256 PRG |
//! | SHA-256 PRG | Real | H(seed ∥ ctr) expansion, RO model |
//! | Wire encryption | Partial | PRF-masked truth tables, but wrong label structure |
//! | MAC tags | Stub | Generated but never checked |
//! | SEH | Stub | API exists, not enforced |
//! | SmallObf | Stub | Not integrated into gate evaluation |

use crate::circuit::{Circuit, Gate};
use crate::crypto::{
    GgmPrf, MacPrf, PuncturablePrf, Prg, SehDigest, SehParams, SehScheme, Sha256Prg, StubSeh,
    StubSmallObf, WirePrf,
};

/// LiO parameters
#[derive(Clone, Debug)]
pub struct LiOParams {
    /// Security parameter (bits)
    pub lambda: usize,
    /// Subcircuit size bound (s in the paper)
    pub subcircuit_size: usize,
    /// PRF tree depth for wire encryption
    pub prf_depth: usize,
}

impl LiOParams {
    /// Create new LiO parameters
    pub fn new(lambda: usize, subcircuit_size: usize) -> Self {
        let prf_depth = subcircuit_size * 2 + 8;
        Self {
            lambda,
            subcircuit_size,
            prf_depth,
        }
    }
}

impl Default for LiOParams {
    fn default() -> Self {
        Self::new(128, 8)
    }
}

/// An obfuscated gate in the LiO construction
#[derive(Clone, Debug)]
pub struct ObfuscatedGate {
    /// Encrypted truth table (4 entries for 2-input gate)
    /// Each entry: (encrypted_output_label, mac_tag)
    pub encrypted_table: Vec<([u8; 32], [u8; 32])>,
    /// Gate index in the circuit
    pub gate_index: usize,
    /// Input wire indices
    pub input_wires: (usize, usize),
    /// Output wire index
    pub output_wire: usize,
}

impl ObfuscatedGate {
    /// Create a new obfuscated gate
    pub fn new(
        gate: &Gate,
        gate_index: usize,
        wire_prf: &WirePrf,
        mac_prf: &MacPrf,
        wire_prf_key: &[u8; 32],
        mac_prf_key: &[u8; 32],
    ) -> Self {
        let mut encrypted_table = Vec::with_capacity(4);

        for ab in 0..4u8 {
            let a = (ab >> 0) & 1 == 1;
            let b = (ab >> 1) & 1 == 1;
            let output = gate.control_function.evaluate(a, b);

            let input_label: Vec<bool> = vec![
                a,
                b,
                (gate.input_wire_a as usize & 1) == 1,
                (gate.input_wire_b as usize & 1) == 1,
            ];

            let _output_label: Vec<bool> = vec![output, (gate.output_wire as usize & 1) == 1];

            let wire_mask = wire_prf.eval(wire_prf_key, &input_label);

            let mut encrypted_output = [0u8; 32];
            for i in 0..32 {
                encrypted_output[i] = wire_mask[i] ^ if output { 0xFF } else { 0x00 };
            }

            let mac_key = mac_prf.eval(mac_prf_key, &input_label);
            let prg = Sha256Prg;
            let mac_tag_bytes = prg.expand(&mac_key, 32);
            let mut mac_tag = [0u8; 32];
            mac_tag.copy_from_slice(&mac_tag_bytes);

            encrypted_table.push((encrypted_output, mac_tag));
        }

        Self {
            encrypted_table,
            gate_index,
            input_wires: (gate.input_wire_a as usize, gate.input_wire_b as usize),
            output_wire: gate.output_wire as usize,
        }
    }

    /// Evaluate the obfuscated gate given input wire values
    pub fn evaluate(
        &self,
        input_a: bool,
        input_b: bool,
        wire_prf: &WirePrf,
        wire_prf_key: &[u8; 32],
    ) -> bool {
        let table_index = (input_a as usize) | ((input_b as usize) << 1);
        let (encrypted_output, _mac_tag) = &self.encrypted_table[table_index];

        let input_label: Vec<bool> = vec![
            input_a,
            input_b,
            (self.input_wires.0 & 1) == 1,
            (self.input_wires.1 & 1) == 1,
        ];

        let wire_mask = wire_prf.eval(wire_prf_key, &input_label);

        let decrypted = encrypted_output[0] ^ wire_mask[0];

        decrypted != 0
    }
}

/// The result of LiO obfuscation
#[derive(Clone, Debug)]
pub struct ObfuscatedLiO {
    /// Obfuscated gates
    pub gates: Vec<ObfuscatedGate>,
    /// Wire PRF key (in real impl, this would be distributed across gates)
    pub wire_prf_key: [u8; 32],
    /// MAC PRF key
    pub mac_prf_key: [u8; 32],
    /// PRF for wire encryption
    pub wire_prf: WirePrf,
    /// PRF for MAC generation
    pub mac_prf: MacPrf,
    /// Number of wires in the original circuit
    pub num_wires: usize,
    /// SEH digest for wire consistency
    pub seh_digest: Option<SehDigest>,
}

impl ObfuscatedLiO {
    /// Get the size of the obfuscated program in bytes
    pub fn size_bytes(&self) -> usize {
        let gate_size = 4 * 64;
        let key_size = 64;
        let seh_size = 32;

        self.gates.len() * gate_size + key_size + seh_size
    }

    /// Evaluate the obfuscated program on input
    pub fn evaluate(&self, input: usize) -> usize {
        let mut wires = vec![false; self.num_wires];

        for i in 0..self.num_wires {
            wires[i] = (input >> i) & 1 == 1;
        }

        for gate in &self.gates {
            let a = wires[gate.input_wires.0];
            let b = wires[gate.input_wires.1];

            let output = gate.evaluate(a, b, &self.wire_prf, &self.wire_prf_key);

            wires[gate.output_wire] = output;
        }

        let mut output = 0usize;
        for (i, &w) in wires.iter().enumerate() {
            if w {
                output |= 1 << i;
            }
        }
        output
    }
}

/// LiO obfuscator
#[derive(Clone, Debug)]
pub struct LiO {
    /// Parameters
    pub params: LiOParams,
    /// Wire encryption PRF
    wire_prf: WirePrf,
    /// MAC PRF
    mac_prf: MacPrf,
    /// SEH scheme
    seh: StubSeh,
    /// Small-circuit obfuscator
    #[allow(dead_code)]
    small_obf: StubSmallObf,
}

impl LiO {
    /// Create a new LiO obfuscator
    pub fn new(params: LiOParams) -> Self {
        let wire_prf = GgmPrf::new(params.prf_depth);
        let mac_prf = GgmPrf::new(params.prf_depth);
        let seh = StubSeh::new();
        let small_obf = StubSmallObf;

        Self {
            params,
            wire_prf,
            mac_prf,
            seh,
            small_obf,
        }
    }

    /// Obfuscate a circuit
    pub fn obfuscate(&self, circuit: &Circuit) -> Result<ObfuscatedLiO, LiOError> {
        if circuit.num_wires == 0 {
            return Err(LiOError::InvalidCircuit(
                "Circuit has no wires".to_string(),
            ));
        }

        let wire_prf_key = self.wire_prf.keygen();
        let mac_prf_key = self.mac_prf.keygen();

        let mut obfuscated_gates = Vec::with_capacity(circuit.gates.len());

        for (idx, gate) in circuit.gates.iter().enumerate() {
            let obf_gate = ObfuscatedGate::new(
                gate,
                idx,
                &self.wire_prf,
                &self.mac_prf,
                &wire_prf_key,
                &mac_prf_key,
            );
            obfuscated_gates.push(obf_gate);
        }

        let initial_wire_values: Vec<bool> = (0..circuit.num_wires).map(|_| false).collect();
        let seh_params = SehParams {
            num_elements: circuit.num_wires,
            ..Default::default()
        };
        let (seh_digest, _ciphertexts) = self.seh.hash(&seh_params, &initial_wire_values);

        Ok(ObfuscatedLiO {
            gates: obfuscated_gates,
            wire_prf_key,
            mac_prf_key,
            wire_prf: self.wire_prf.clone(),
            mac_prf: self.mac_prf.clone(),
            num_wires: circuit.num_wires,
            seh_digest: Some(seh_digest),
        })
    }
}

/// Errors during LiO obfuscation
#[derive(Clone, Debug)]
pub enum LiOError {
    /// Invalid circuit structure
    InvalidCircuit(String),
    /// Cryptographic operation failed
    CryptoError(String),
}

impl std::fmt::Display for LiOError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::InvalidCircuit(s) => write!(f, "Invalid circuit: {}", s),
            Self::CryptoError(s) => write!(f, "Crypto error: {}", s),
        }
    }
}

impl std::error::Error for LiOError {}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::circuit::ControlFunction;

    #[test]
    fn test_lio_obfuscate_simple() {
        let gates = vec![Gate::new(2, 0, 1, ControlFunction::And)];
        let circuit = Circuit::new(gates, 3);

        let lio = LiO::new(LiOParams::default());
        let result = lio.obfuscate(&circuit);

        assert!(result.is_ok());
        let obf = result.unwrap();
        assert_eq!(obf.gates.len(), 1);
    }

    #[test]
    fn test_lio_evaluate_and() {
        let gates = vec![Gate::new(2, 0, 1, ControlFunction::And)];
        let circuit = Circuit::new(gates, 3);

        let lio = LiO::new(LiOParams::default());
        let obf = lio.obfuscate(&circuit).unwrap();

        assert_eq!(obf.evaluate(0b11) & 0b100, 0b100);
        assert_eq!(obf.evaluate(0b01) & 0b100, 0);
        assert_eq!(obf.evaluate(0b10) & 0b100, 0);
        assert_eq!(obf.evaluate(0b00) & 0b100, 0);
    }

    #[test]
    fn test_lio_evaluate_xor() {
        let gates = vec![Gate::new(2, 0, 1, ControlFunction::Xor)];
        let circuit = Circuit::new(gates, 3);

        let lio = LiO::new(LiOParams::default());
        let obf = lio.obfuscate(&circuit).unwrap();

        assert_eq!(obf.evaluate(0b11) & 0b100, 0);
        assert_eq!(obf.evaluate(0b01) & 0b100, 0b100);
        assert_eq!(obf.evaluate(0b10) & 0b100, 0b100);
        assert_eq!(obf.evaluate(0b00) & 0b100, 0);
    }

    #[test]
    fn test_lio_evaluate_complex() {
        let gates = vec![
            Gate::new(2, 0, 1, ControlFunction::And),
            Gate::new(3, 2, 0, ControlFunction::Xor),
        ];
        let circuit = Circuit::new(gates, 4);

        let lio = LiO::new(LiOParams::default());
        let obf = lio.obfuscate(&circuit).unwrap();

        for input in 0..4 {
            let expected = circuit.evaluate(input);
            let actual = obf.evaluate(input);
            assert_eq!(actual, expected, "Mismatch for input {}", input);
        }
    }

    #[test]
    fn test_lio_random_circuit() {
        let circuit = Circuit::random_r57(4, 5);

        let lio = LiO::new(LiOParams::default());
        let obf = lio.obfuscate(&circuit).unwrap();

        for input in 0..16 {
            let expected = circuit.evaluate(input);
            let actual = obf.evaluate(input);
            assert_eq!(actual, expected, "Mismatch for input {}", input);
        }
    }
}
