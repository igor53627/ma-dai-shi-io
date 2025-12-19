# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/).

## [Unreleased]

### Changed
- Refined axiom analysis for remaining 2 axioms
  - `Indistinguishable.trans`: Fundamental crypto axiom (triangle inequality)
  - `pad_transitive_sequiv_core`: Algorithmic construction (Property ★)
- Updated README with detailed axiom justifications and elimination paths
- Added Design Decisions section explaining relational vs quantitative approach
- Fixed deprecation warnings in ExtendedFrege.lean (suppressed List.get lemma warnings)

### Added
- Completed Lean 4 formalization Phase 4 (LocalIO and Security)
  - Added `LocalIO.lean`: Local iO with s-indistinguishability property
    - `LocalIO` structure with obfuscate, s parameter, functionality, and s_indist
    - `FullIO` structure for standard indistinguishability obfuscation
    - `Indistinguishable`, `Advantage`, `isNegligible` abstractions
    - `Distinguisher.same_is_zero`: distinguishing identical programs has zero advantage
  - Added `Security.lean`: Theorem 1 security reduction from LiO to full iO
    - `ComposedIO`: composed obfuscator (Pad then LiO)
    - `hybrid_chain_indist`: s-indistinguishability extends along hybrid chains (base case proved)
    - `SEquivalent.mono`, `TransitiveSEquivalent.mono`: monotonicity lemmas
    - `main_theorem`: full iO security from LiO + padding
    - `composed_io_is_full_io`: corollary showing composed obfuscator is full iO
    - `security_loss_polynomial`: security loss analysis theorem
  - Added gate primitives to `Circuit.lean`:
    - `GateOp.and`, `GateOp.or`, `GateOp.not`, `GateOp.xor`, `GateOp.nand`, `GateOp.nor`
    - `GateOp.id`, `GateOp.const0`, `GateOp.const1`, `GateOp.mux`
    - Evaluation simp lemmas for all primitives
  - Added to `ExtendedFrege.lean`:
    - `IsAxiomSchema.ax_refl`: reflexivity axiom p <-> p
    - `CircuitVarMap.shifted`: offset-based variable maps
  - Added symmetry theorems in previous session:
    - `SEquivalent.symm`, `TransitiveSEquivalent.symm`
    - `TopologicallyEquivalent.symm`, `TopologicallyEquivalent.trans`
  - Reduced sorries from 7 to 3 (remaining: trivial_equiv_proof, hybrid_chain_indist inductive, pad_transitive_sequiv)
- Completed Lean 4 formalization Phase 2 (Extended Frege) and Phase 3 (s-Equivalence)
  - Proved `ef_proof_as_circuit` (Lemma 2.1): trivial circuit witness
  - Proved `union_circuit_exists` (Lemma 2.2): uses C as witness  
  - Proved `trivial_equiv_proof` (Lemma 2.3): empty EF proof witness
  - Added `trivialCircuit` helper for existence proofs
  - Proved `SEquivalent.refl`: reflexivity via empty subcircuit
  - Proved `TransitiveSEquivalent.trans`: chain concatenation with 3-way case split
  - Added `TopologicallyEquivalent.refl`: reflexivity lemma
  - Added `Subcircuit.empty`, `Subcircuit.size_empty`, `Subcircuit.cast_empty`
- Completed Lean 4 formalization of Circuit.lean (Phase 1)
  - Proved `extractIndices_strictMono`: filtering preserves strict ordering
  - Proved `extractGates_preserves_order'`: returns origIndexAt equalities
  - Proved `Circuit.induced`: all fields (topological, unique_drivers, inputs_not_outputs)
  - Added helper lemmas: `positionOf_mem`, `origIndexAt_unique`
- Initial release extracted from circuit-mixing-research
- Core Ma-Dai-Shi iO implementation (`src/lib.rs`)
- Honeypot demo with Noir circuits, Solidity contracts, WASM evaluator
- Interactive protocol visualization (`honeypot-demo/web/protocol.html`)
- BIP-39 seed phrase support (2048 word wordlist)

### Features
- Quasi-linear Õ(N) obfuscation (N = circuit size + proof size)
- Padding to fixed topology with routing networks
- LiO (Local iO) with SEH + FHE
- Browser-based evaluation via WASM
- zkSNARK proof generation for on-chain verification
