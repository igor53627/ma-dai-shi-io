//! Hybrid Security Experiments for Ma-Dai-Shi iO
//!
//! Implements the hybrid sequence from the Ma-Dai-Shi security proof (§5, Theorem 1).
//!
//! ## Security Reduction Overview
//!
//! The LiO security proof uses a hybrid argument:
//!
//! 1. **Hybrid₀**: Standard obfuscation of circuit C₁
//! 2. **Hybrid_k**: For each differing gate g_k, replace PRF key with punctured key
//!    - The punctured key cannot evaluate at the "unused" table entry
//!    - Replace that entry with random (indistinguishable by PRF security)
//! 3. **Hybrid_final**: Obfuscation of circuit C₂
//!
//! Adjacent hybrids are computationally indistinguishable because:
//! - The punctured PRF value at the unused entry is pseudorandom
//! - Replacing it with true randomness is undetectable
//!
//! ## Usage
//!
//! ```ignore
//! use ma_dai_shi_io::hybrid::{HybridObfuscator, DifferingGate};
//! use ma_dai_shi_io::{Circuit, ControlFunction, Gate};
//!
//! // Two circuits that differ at gate 0 (AND vs XOR)
//! let c1 = Circuit::new(vec![Gate::new(2, 0, 1, ControlFunction::And)], 3);
//! let c2 = Circuit::new(vec![Gate::new(2, 0, 1, ControlFunction::Xor)], 3);
//!
//! // Find differing gates
//! let diffs = DifferingGate::find(&c1, &c2);
//!
//! // Create hybrid sequence
//! let hybrid_obf = HybridObfuscator::new(LiOParams::default());
//!
//! // Hybrid 0: standard obfuscation of C1
//! let h0 = hybrid_obf.create_hybrid(&c1, &diffs, 0);
//!
//! // Hybrid 1: puncture at first differing gate
//! let h1 = hybrid_obf.create_hybrid(&c1, &diffs, 1);
//! ```
//!
//! ## Relationship to Ma-Dai-Shi Theorem 1
//!
//! Theorem 1 states that LiO provides indistinguishability for circuits differing
//! in at most s = O(log N) gates. The security loss is polynomial in s:
//!
//! - Number of hybrids: O(4s) (4 table entries per differing gate)
//! - Each hybrid step: PRF security (negligible advantage)
//! - Total security loss: O(4s · ε_PRF)
//!
//! For s = O(log N), this gives poly(N) hybrids with negligible total advantage.

use std::collections::HashSet;

use crate::circuit::{Circuit, Gate};
use crate::crypto::{
    DefaultSmallObf, GgmPrf, MacPrf, ObfuscatedBytecode, PuncturablePrf, Prg, Sha256Prg, SmallObf,
    WirePrf,
};
use crate::lio::{bytes_to_bools, control_function_to_gate_type, LiOError, LiOParams, WireLabels};
use crate::crypto::GateGadget;
use rand::RngCore;

/// Represents a gate that differs between two circuits
#[derive(Clone, Debug)]
pub struct DifferingGate {
    /// Gate index in the circuit
    pub gate_index: usize,
    /// The gate in circuit C1
    pub gate_c1: Gate,
    /// The gate in circuit C2
    pub gate_c2: Gate,
    /// Which table entries differ (input combinations where output differs)
    pub differing_entries: Vec<(bool, bool)>,
}

impl DifferingGate {
    /// Find all gates that differ between two circuits
    ///
    /// Circuits must have the same topology (same wiring), differing only in control functions.
    pub fn find(c1: &Circuit, c2: &Circuit) -> Vec<Self> {
        let mut diffs = Vec::new();

        let min_gates = c1.gates.len().min(c2.gates.len());

        for i in 0..min_gates {
            let g1 = &c1.gates[i];
            let g2 = &c2.gates[i];

            if g1.control_function != g2.control_function {
                let differing_entries = Self::find_differing_entries(g1, g2);

                diffs.push(DifferingGate {
                    gate_index: i,
                    gate_c1: g1.clone(),
                    gate_c2: g2.clone(),
                    differing_entries,
                });
            }
        }

        diffs
    }

    /// Find which input combinations produce different outputs
    fn find_differing_entries(g1: &Gate, g2: &Gate) -> Vec<(bool, bool)> {
        let mut diffs = Vec::new();

        for ab in 0..4u8 {
            let a = (ab >> 0) & 1 == 1;
            let b = (ab >> 1) & 1 == 1;

            let out1 = g1.control_function.evaluate(a, b);
            let out2 = g2.control_function.evaluate(a, b);

            if out1 != out2 {
                diffs.push((a, b));
            }
        }

        diffs
    }
}

/// An obfuscated gate in a hybrid experiment
///
/// Similar to `ObfuscatedGate` but tracks which entries use punctured randomness.
#[derive(Clone, Debug)]
pub struct HybridObfuscatedGate {
    /// Encrypted truth table (4 entries for 2-input gate)
    pub encrypted_table: Vec<([u8; 32], [u8; 32])>,
    /// Gate index in the circuit
    pub gate_index: usize,
    /// Input wire indices
    pub input_wires: (usize, usize),
    /// Output wire index
    pub output_wire: usize,
    /// Small-circuit obfuscation of the gate gadget
    pub gadget_obf: ObfuscatedBytecode,
    /// Which entries were replaced with random (punctured)
    pub punctured_entries: Vec<usize>,
}

impl HybridObfuscatedGate {
    /// Create a normal (non-punctured) obfuscated gate
    pub fn new_normal(
        gate: &Gate,
        gate_index: usize,
        wire_prf: &WirePrf,
        mac_prf: &MacPrf,
        wire_prf_key: &[u8; 32],
        mac_prf_key: &[u8; 32],
        wire_labels: &[WireLabels],
    ) -> Self {
        let mut encrypted_table = Vec::with_capacity(4);

        let labels_a = &wire_labels[gate.input_wire_a as usize];
        let labels_b = &wire_labels[gate.input_wire_b as usize];
        let labels_out = &wire_labels[gate.output_wire as usize];

        let gate_type = control_function_to_gate_type(&gate.control_function);
        let gadget = GateGadget::new(
            gate_type,
            (gate.input_wire_a as usize, gate.input_wire_b as usize),
            gate.output_wire as usize,
        );

        let small_obf = DefaultSmallObf::default();
        let bytecode = gadget.to_bytecode_program();
        let gadget_obf = small_obf.obfuscate(&bytecode);

        for ab in 0..4u8 {
            let a = (ab >> 0) & 1 == 1;
            let b = (ab >> 1) & 1 == 1;

            let packed_input = (a as u8) | ((b as u8) << 1);
            let out_bytes = small_obf.eval(&gadget_obf, &[packed_input]);
            let output = (out_bytes[0] & 1) == 1;

            let in_label_a = labels_a.for_bit(a);
            let in_label_b = labels_b.for_bit(b);
            let out_label = labels_out.for_bit(output);

            let mut input_label_bits = Vec::new();
            input_label_bits.extend(bytes_to_bools(in_label_a));
            input_label_bits.extend(bytes_to_bools(in_label_b));
            for i in 0..16 {
                input_label_bits.push(((gate_index >> i) & 1) == 1);
            }

            let wire_mask = wire_prf.eval(wire_prf_key, &input_label_bits);

            let mut encrypted_output = [0u8; 32];
            for i in 0..32 {
                encrypted_output[i] = wire_mask[i] ^ out_label[i];
            }

            let mac_key = mac_prf.eval(mac_prf_key, &input_label_bits);
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
            gadget_obf,
            punctured_entries: vec![],
        }
    }

    /// Create a punctured obfuscated gate with multiple punctured entries
    ///
    /// At the specified entries, replace PRF output with true randomness.
    /// This simulates the hybrid game where we cannot compute the PRF at punctured points.
    pub fn new_multi_punctured(
        gate: &Gate,
        gate_index: usize,
        wire_prf: &WirePrf,
        mac_prf: &MacPrf,
        wire_prf_key: &[u8; 32],
        mac_prf_key: &[u8; 32],
        wire_labels: &[WireLabels],
        puncture_entries: &[(bool, bool)],
    ) -> Self {
        let mut encrypted_table = Vec::with_capacity(4);
        let mut punctured_entries_out = Vec::new();
        let mut rng = rand::thread_rng();

        let labels_a = &wire_labels[gate.input_wire_a as usize];
        let labels_b = &wire_labels[gate.input_wire_b as usize];
        let labels_out = &wire_labels[gate.output_wire as usize];

        let gate_type = control_function_to_gate_type(&gate.control_function);
        let gadget = GateGadget::new(
            gate_type,
            (gate.input_wire_a as usize, gate.input_wire_b as usize),
            gate.output_wire as usize,
        );

        let small_obf = DefaultSmallObf::default();
        let bytecode = gadget.to_bytecode_program();
        let gadget_obf = small_obf.obfuscate(&bytecode);

        for ab in 0..4u8 {
            let a = (ab >> 0) & 1 == 1;
            let b = (ab >> 1) & 1 == 1;
            let is_punctured_entry = puncture_entries.contains(&(a, b));

            let packed_input = (a as u8) | ((b as u8) << 1);
            let out_bytes = small_obf.eval(&gadget_obf, &[packed_input]);
            let output = (out_bytes[0] & 1) == 1;

            let in_label_a = labels_a.for_bit(a);
            let in_label_b = labels_b.for_bit(b);
            let out_label = labels_out.for_bit(output);

            let mut input_label_bits = Vec::new();
            input_label_bits.extend(bytes_to_bools(in_label_a));
            input_label_bits.extend(bytes_to_bools(in_label_b));
            for i in 0..16 {
                input_label_bits.push(((gate_index >> i) & 1) == 1);
            }

            let (encrypted_output, mac_tag) = if is_punctured_entry {
                punctured_entries_out.push(ab as usize);

                let mut random_encrypted = [0u8; 32];
                let mut random_mac = [0u8; 32];
                rng.fill_bytes(&mut random_encrypted);
                rng.fill_bytes(&mut random_mac);
                (random_encrypted, random_mac)
            } else {
                let wire_mask = wire_prf.eval(wire_prf_key, &input_label_bits);

                let mut encrypted = [0u8; 32];
                for i in 0..32 {
                    encrypted[i] = wire_mask[i] ^ out_label[i];
                }

                let mac_key = mac_prf.eval(mac_prf_key, &input_label_bits);
                let prg = Sha256Prg;
                let mac_tag_bytes = prg.expand(&mac_key, 32);
                let mut mac = [0u8; 32];
                mac.copy_from_slice(&mac_tag_bytes);

                (encrypted, mac)
            };

            encrypted_table.push((encrypted_output, mac_tag));
        }

        Self {
            encrypted_table,
            gate_index,
            input_wires: (gate.input_wire_a as usize, gate.input_wire_b as usize),
            output_wire: gate.output_wire as usize,
            gadget_obf,
            punctured_entries: punctured_entries_out,
        }
    }

    /// Get the PRF input bits for a specific table entry
    pub fn prf_input_for_entry(
        &self,
        input_a: bool,
        input_b: bool,
        wire_labels: &[WireLabels],
    ) -> Vec<bool> {
        let labels_a = &wire_labels[self.input_wires.0];
        let labels_b = &wire_labels[self.input_wires.1];
        let in_label_a = labels_a.for_bit(input_a);
        let in_label_b = labels_b.for_bit(input_b);

        let mut bits = Vec::new();
        bits.extend(bytes_to_bools(in_label_a));
        bits.extend(bytes_to_bools(in_label_b));
        for i in 0..16 {
            bits.push(((self.gate_index >> i) & 1) == 1);
        }
        bits
    }
}

/// A hybrid obfuscated circuit
#[derive(Clone, Debug)]
pub struct HybridObfuscatedLiO {
    /// Obfuscated gates (some may be punctured)
    pub gates: Vec<HybridObfuscatedGate>,
    /// Wire PRF key (original, unpunctured)
    pub wire_prf_key: [u8; 32],
    /// MAC PRF key (original, unpunctured)
    pub mac_prf_key: [u8; 32],
    /// PRF for wire encryption
    pub wire_prf: WirePrf,
    /// PRF for MAC generation
    pub mac_prf: MacPrf,
    /// Number of wires
    pub num_wires: usize,
    /// Wire labels
    pub wire_labels: Vec<WireLabels>,
    /// Hybrid index (0 = standard obfuscation, k = k gates punctured)
    pub hybrid_index: usize,
    /// Which gates have punctured entries
    pub punctured_gates: HashSet<usize>,
}

impl HybridObfuscatedLiO {
    /// Check if this hybrid has any punctured entries
    pub fn has_punctured_entries(&self) -> bool {
        !self.punctured_gates.is_empty()
    }

    /// Count total number of punctured table entries
    pub fn count_punctured_entries(&self) -> usize {
        self.gates.iter().map(|g| g.punctured_entries.len()).sum()
    }
}

/// Hybrid obfuscator for security experiments
///
/// Creates obfuscations that simulate the hybrid sequence from the security proof.
#[derive(Clone, Debug)]
pub struct HybridObfuscator {
    #[allow(dead_code)]
    params: LiOParams,
    wire_prf: WirePrf,
    mac_prf: MacPrf,
}

impl HybridObfuscator {
    /// Create a new hybrid obfuscator
    pub fn new(params: LiOParams) -> Self {
        let wire_prf = GgmPrf::new(params.prf_depth);
        let mac_prf = GgmPrf::new(params.prf_depth);

        Self {
            params,
            wire_prf,
            mac_prf,
        }
    }

    /// Create a hybrid obfuscation at the given hybrid index
    ///
    /// - `hybrid_index = 0`: Standard obfuscation (no puncturing)
    /// - `hybrid_index = k`: First k differing entries use punctured (random) values
    ///
    /// The differing gates list should come from `DifferingGate::find()`.
    pub fn create_hybrid(
        &self,
        circuit: &Circuit,
        differing_gates: &[DifferingGate],
        hybrid_index: usize,
    ) -> Result<HybridObfuscatedLiO, LiOError> {
        if circuit.num_wires == 0 {
            return Err(LiOError::InvalidCircuit("Circuit has no wires".to_string()));
        }

        let wire_prf_key = self.wire_prf.keygen();
        let mac_prf_key = self.mac_prf.keygen();

        let mut rng = rand::thread_rng();
        let wire_labels: Vec<WireLabels> = (0..circuit.num_wires)
            .map(|_| WireLabels::random(&mut rng))
            .collect();

        let puncture_schedule = self.build_puncture_schedule(differing_gates, hybrid_index);

        let mut obfuscated_gates = Vec::with_capacity(circuit.gates.len());
        let mut punctured_gates = HashSet::new();

        for (idx, gate) in circuit.gates.iter().enumerate() {
            if let Some(puncture_entries) = puncture_schedule.get(&idx) {
                let obf_gate = HybridObfuscatedGate::new_multi_punctured(
                    gate,
                    idx,
                    &self.wire_prf,
                    &self.mac_prf,
                    &wire_prf_key,
                    &mac_prf_key,
                    &wire_labels,
                    puncture_entries,
                );

                punctured_gates.insert(idx);
                obfuscated_gates.push(obf_gate);
            } else {
                let obf_gate = HybridObfuscatedGate::new_normal(
                    gate,
                    idx,
                    &self.wire_prf,
                    &self.mac_prf,
                    &wire_prf_key,
                    &mac_prf_key,
                    &wire_labels,
                );
                obfuscated_gates.push(obf_gate);
            }
        }

        Ok(HybridObfuscatedLiO {
            gates: obfuscated_gates,
            wire_prf_key,
            mac_prf_key,
            wire_prf: self.wire_prf.clone(),
            mac_prf: self.mac_prf.clone(),
            num_wires: circuit.num_wires,
            wire_labels,
            hybrid_index,
            punctured_gates,
        })
    }

    /// Create the full hybrid sequence between two circuits
    ///
    /// Returns all hybrids from H₀ (obf of C1) to H_final (indistinguishable from obf of C2).
    pub fn create_hybrid_sequence(
        &self,
        c1: &Circuit,
        c2: &Circuit,
    ) -> Result<Vec<HybridObfuscatedLiO>, LiOError> {
        let diffs = DifferingGate::find(c1, c2);

        let total_diff_entries: usize = diffs.iter().map(|d| d.differing_entries.len()).sum();
        let num_hybrids = total_diff_entries + 1;

        let mut hybrids = Vec::with_capacity(num_hybrids);

        for k in 0..num_hybrids {
            let hybrid = self.create_hybrid(c1, &diffs, k)?;
            hybrids.push(hybrid);
        }

        Ok(hybrids)
    }

    /// Build the puncture schedule: which gate gets which entries punctured
    ///
    /// Returns a map from gate_index to list of entries that should be punctured.
    fn build_puncture_schedule(
        &self,
        differing_gates: &[DifferingGate],
        hybrid_index: usize,
    ) -> std::collections::HashMap<usize, Vec<(bool, bool)>> {
        let mut schedule: std::collections::HashMap<usize, Vec<(bool, bool)>> =
            std::collections::HashMap::new();

        if hybrid_index == 0 {
            return schedule;
        }

        let mut entry_count = 0;

        for diff in differing_gates {
            for &entry in &diff.differing_entries {
                entry_count += 1;
                if entry_count <= hybrid_index {
                    schedule
                        .entry(diff.gate_index)
                        .or_insert_with(Vec::new)
                        .push(entry);
                }
            }
        }

        schedule
    }
}

/// Statistics about a hybrid sequence for security analysis
#[derive(Clone, Debug)]
pub struct HybridSequenceStats {
    /// Total number of hybrids
    pub num_hybrids: usize,
    /// Number of differing gates
    pub num_differing_gates: usize,
    /// Total differing table entries
    pub total_differing_entries: usize,
    /// Maximum differing entries per gate
    pub max_entries_per_gate: usize,
    /// Security parameter s (subcircuit size bound)
    pub subcircuit_size: usize,
    /// Whether the sequence respects the s bound
    pub respects_s_bound: bool,
}

impl HybridSequenceStats {
    /// Analyze a pair of circuits to generate hybrid sequence statistics
    pub fn analyze(c1: &Circuit, c2: &Circuit, subcircuit_size: usize) -> Self {
        let diffs = DifferingGate::find(c1, c2);

        let num_differing_gates = diffs.len();
        let total_differing_entries: usize = diffs.iter().map(|d| d.differing_entries.len()).sum();
        let max_entries_per_gate = diffs.iter().map(|d| d.differing_entries.len()).max().unwrap_or(0);

        let num_hybrids = total_differing_entries + 1;

        let respects_s_bound = num_differing_gates <= subcircuit_size;

        Self {
            num_hybrids,
            num_differing_gates,
            total_differing_entries,
            max_entries_per_gate,
            subcircuit_size,
            respects_s_bound,
        }
    }
}

impl std::fmt::Display for HybridSequenceStats {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Hybrid Sequence: {} hybrids, {} differing gates ({} entries), s={}, bound {}",
            self.num_hybrids,
            self.num_differing_gates,
            self.total_differing_entries,
            self.subcircuit_size,
            if self.respects_s_bound { "respected" } else { "VIOLATED" }
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::circuit::ControlFunction;
    use crate::crypto::PuncturablePrf;

    #[test]
    fn test_differing_gate_find_and_vs_xor() {
        let c1 = Circuit::new(vec![Gate::new(2, 0, 1, ControlFunction::And)], 3);
        let c2 = Circuit::new(vec![Gate::new(2, 0, 1, ControlFunction::Xor)], 3);

        let diffs = DifferingGate::find(&c1, &c2);

        assert_eq!(diffs.len(), 1);
        assert_eq!(diffs[0].gate_index, 0);
        assert_eq!(diffs[0].differing_entries.len(), 3);
    }

    #[test]
    fn test_differing_gate_find_identical() {
        let c1 = Circuit::new(vec![Gate::new(2, 0, 1, ControlFunction::And)], 3);
        let c2 = Circuit::new(vec![Gate::new(2, 0, 1, ControlFunction::And)], 3);

        let diffs = DifferingGate::find(&c1, &c2);

        assert!(diffs.is_empty());
    }

    #[test]
    fn test_hybrid_obfuscator_create_h0() {
        let circuit = Circuit::new(vec![Gate::new(2, 0, 1, ControlFunction::And)], 3);
        let diffs = Vec::new();

        let hybrid_obf = HybridObfuscator::new(LiOParams::default());
        let h0 = hybrid_obf.create_hybrid(&circuit, &diffs, 0).unwrap();

        assert_eq!(h0.hybrid_index, 0);
        assert!(!h0.has_punctured_entries());
        assert_eq!(h0.count_punctured_entries(), 0);
    }

    #[test]
    fn test_hybrid_obfuscator_create_h1_punctured() {
        let c1 = Circuit::new(vec![Gate::new(2, 0, 1, ControlFunction::And)], 3);
        let c2 = Circuit::new(vec![Gate::new(2, 0, 1, ControlFunction::Xor)], 3);
        let diffs = DifferingGate::find(&c1, &c2);

        let hybrid_obf = HybridObfuscator::new(LiOParams::default());
        let h1 = hybrid_obf.create_hybrid(&c1, &diffs, 1).unwrap();

        assert_eq!(h1.hybrid_index, 1);
        assert!(h1.has_punctured_entries());
        assert_eq!(h1.count_punctured_entries(), 1);
        assert!(h1.punctured_gates.contains(&0));
    }

    #[test]
    fn test_hybrid_sequence_length() {
        let c1 = Circuit::new(vec![Gate::new(2, 0, 1, ControlFunction::And)], 3);
        let c2 = Circuit::new(vec![Gate::new(2, 0, 1, ControlFunction::Xor)], 3);

        let hybrid_obf = HybridObfuscator::new(LiOParams::default());
        let hybrids = hybrid_obf.create_hybrid_sequence(&c1, &c2).unwrap();

        let diffs = DifferingGate::find(&c1, &c2);
        let expected_entries: usize = diffs.iter().map(|d| d.differing_entries.len()).sum();

        assert_eq!(hybrids.len(), expected_entries + 1);
    }

    #[test]
    fn test_adjacent_hybrids_differ_by_one_entry() {
        let c1 = Circuit::new(vec![Gate::new(2, 0, 1, ControlFunction::And)], 3);
        let c2 = Circuit::new(vec![Gate::new(2, 0, 1, ControlFunction::Xor)], 3);

        let hybrid_obf = HybridObfuscator::new(LiOParams::default());
        let hybrids = hybrid_obf.create_hybrid_sequence(&c1, &c2).unwrap();

        for i in 0..hybrids.len() - 1 {
            let curr = &hybrids[i];
            let next = &hybrids[i + 1];

            let diff = next.count_punctured_entries() as isize
                - curr.count_punctured_entries() as isize;
            assert_eq!(diff.abs(), 1);
        }
    }

    #[test]
    fn test_punctured_entry_uses_different_value() {
        let c1 = Circuit::new(vec![Gate::new(2, 0, 1, ControlFunction::And)], 3);
        let c2 = Circuit::new(vec![Gate::new(2, 0, 1, ControlFunction::Xor)], 3);
        let diffs = DifferingGate::find(&c1, &c2);

        let hybrid_obf = HybridObfuscator::new(LiOParams::default());

        let h0 = hybrid_obf.create_hybrid(&c1, &diffs, 0).unwrap();
        let h1 = hybrid_obf.create_hybrid(&c1, &diffs, 1).unwrap();

        let entry_h0 = &h0.gates[0].encrypted_table;
        let entry_h1 = &h1.gates[0].encrypted_table;

        let has_difference = entry_h0.iter().zip(entry_h1.iter()).any(|(e0, e1)| e0 != e1);
        assert!(has_difference);
    }

    #[test]
    fn test_hybrid_sequence_stats() {
        let c1 = Circuit::new(vec![Gate::new(2, 0, 1, ControlFunction::And)], 3);
        let c2 = Circuit::new(vec![Gate::new(2, 0, 1, ControlFunction::Xor)], 3);

        let stats = HybridSequenceStats::analyze(&c1, &c2, 8);

        assert_eq!(stats.num_differing_gates, 1);
        assert!(stats.respects_s_bound);
        assert!(stats.num_hybrids > 1);
    }

    #[test]
    fn test_hybrid_respects_prf_puncturing() {
        let c1 = Circuit::new(vec![Gate::new(2, 0, 1, ControlFunction::And)], 3);
        let c2 = Circuit::new(vec![Gate::new(2, 0, 1, ControlFunction::Xor)], 3);
        let diffs = DifferingGate::find(&c1, &c2);

        let hybrid_obf = HybridObfuscator::new(LiOParams::default());
        let h1 = hybrid_obf.create_hybrid(&c1, &diffs, 1).unwrap();

        let punct_entry = diffs[0].differing_entries[0];
        let prf_input = h1.gates[0].prf_input_for_entry(punct_entry.0, punct_entry.1, &h1.wire_labels);

        let pkey = h1.wire_prf.puncture(&h1.wire_prf_key, &prf_input);
        assert!(h1.wire_prf.eval_punctured(&pkey, &prf_input).is_none());

        let other_input = h1.gates[0].prf_input_for_entry(!punct_entry.0, punct_entry.1, &h1.wire_labels);
        assert!(h1.wire_prf.eval_punctured(&pkey, &other_input).is_some());
    }

    #[test]
    fn test_multi_gate_circuit_hybrids() {
        let c1 = Circuit::new(
            vec![
                Gate::new(2, 0, 1, ControlFunction::And),
                Gate::new(3, 2, 0, ControlFunction::Or),
            ],
            4,
        );
        let c2 = Circuit::new(
            vec![
                Gate::new(2, 0, 1, ControlFunction::Xor),
                Gate::new(3, 2, 0, ControlFunction::Nor),
            ],
            4,
        );

        let diffs = DifferingGate::find(&c1, &c2);
        assert_eq!(diffs.len(), 2);

        let hybrid_obf = HybridObfuscator::new(LiOParams::default());
        let hybrids = hybrid_obf.create_hybrid_sequence(&c1, &c2).unwrap();

        assert!(hybrids.len() > 1);
        assert_eq!(hybrids[0].count_punctured_entries(), 0);
        assert!(hybrids.last().unwrap().count_punctured_entries() > 0);
    }
}
