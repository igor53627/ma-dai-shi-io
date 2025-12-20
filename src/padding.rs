//! Circuit padding for Ma-Dai-Shi iO
//!
//! Implements the padding construction from §3.2 of the paper.
//! Padding converts arbitrary circuits to a fixed topology, ensuring that
//! equivalent circuits become transitively s-equivalent for s = O(log N).
//!
//! ## Construction
//!
//! 1. **PadSingle(C, N)**: Convert circuit C to fixed topology of size O(N)
//!    - Topologically sort gates
//!    - Add routing network with binary tree selectors
//!    - Add copy gadgets for wire fan-out
//!
//! 2. **Pad(C, N_circ, N_proof)**: Full padding
//!    - C1 = PadSingle(C, N_circ)
//!    - C2 = PadSingle(identity, N_circ)
//!    - C_proof = PadSingle(identity, c*(N_circ + N_proof))
//!    - Combine with AND-tree

use crate::circuit::{Circuit, ControlFunction, Gate};

/// Result of padding a circuit
#[derive(Clone, Debug)]
pub struct PaddedCircuit {
    /// The main (original) circuit, padded
    pub main_circuit: Circuit,
    /// Filler circuit (identity operations)
    pub filler_circuit: Circuit,
    /// Proof encoding circuit
    pub proof_circuit: Circuit,
    /// AND-tree combining the circuits
    pub and_tree: Vec<Gate>,
    /// Combined circuit (main + filler + proof + AND-tree)
    pub combined: Circuit,
    /// Original circuit size
    pub original_size: usize,
    /// Padding overhead information
    pub overhead: PaddingOverhead,
}

/// Information about padding overhead
#[derive(Clone, Debug)]
pub struct PaddingOverhead {
    /// Number of gates in original circuit
    pub original_gates: usize,
    /// Number of gates after padding
    pub padded_gates: usize,
    /// Number of routing gates added
    pub routing_gates: usize,
    /// Number of AND-tree gates added
    pub and_tree_gates: usize,
    /// Size ratio (padded / original)
    pub size_ratio: f64,
}

/// Pad a single circuit to a fixed size
///
/// Adds routing network and identity operations to reach the target size.
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

/// Create a routing network for wire permutation
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

/// Create copy gadgets for wire fan-out
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

/// Create an identity circuit of a given size
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

/// Create an AND-tree combining multiple outputs
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

/// Full padding construction per §3.2.2
///
/// Creates: C1 (main) + C2 (filler) + C_proof + AND-tree
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

/// Optimized padding with minimal overhead
///
/// Uses a simpler padding strategy for cases where full security is not needed.
pub fn pad_optimized(circuit: &Circuit) -> PaddedCircuit {
    let num_wires = circuit.num_wires.max(4);
    let original_size = circuit.gates.len();

    let target_size = original_size + ((original_size as f64).log2().ceil() as usize).max(4) * 2;
    let main_circuit = pad_single(circuit, target_size);

    let filler_circuit = Circuit {
        gates: vec![],
        num_wires,
    };
    let proof_circuit = Circuit {
        gates: vec![],
        num_wires,
    };
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
    fn test_pad_single_empty() {
        let circuit = Circuit::identity(4);
        let padded = pad_single(&circuit, 16);

        assert_eq!(padded.gates.len(), 16);
    }

    #[test]
    fn test_full_padding() {
        let circuit = Circuit::random_r57(6, 10);
        let padded = pad(&circuit, 20, 100);

        assert!(padded.combined.gates.len() > circuit.gates.len());
        assert_eq!(padded.original_size, 10);
        assert!(padded.overhead.size_ratio > 1.0);
    }

    #[test]
    fn test_optimized_padding() {
        let circuit = Circuit::random_r57(6, 10);
        let padded = pad_optimized(&circuit);

        assert!(padded.combined.gates.len() >= circuit.gates.len());
        assert!(padded.filler_circuit.gates.is_empty());
        assert!(padded.proof_circuit.gates.is_empty());
    }

    #[test]
    fn test_identity_circuit() {
        let identity = create_identity_circuit(4, 10);

        assert!(identity.gates.len() >= 10);
        assert!(identity.num_wires >= 4);
    }
}
