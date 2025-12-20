# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/).

## [Unreleased]

### Error Handling, Wire Indices & Benchmarks (Milestone 4)
- **Issue #15**: Changed `evaluate()` to return `Result<_, LiOError>` instead of panicking
  - Added `LiOError::MacVerificationFailed { gate_index, table_index }` variant
  - Added `LiOError::LabelMismatch { gate_index }` variant
  - Added `LiOError::SehVerificationFailed` variant
  - Added `evaluate_unchecked()` convenience method that panics on failure
  - Updated all tests to use `.unwrap()` or pattern matching
- **Issue #14**: Upgraded wire indices from `u8` to `u16`
  - `Gate` struct now uses `u16` for `output_wire`, `input_wire_a`, `input_wire_b`
  - Supports circuits up to 65,536 wires (previously 256)
  - Updated `padding.rs` to use `u16` throughout
  - Added test `test_large_circuit_over_256_wires` with 300-wire circuit
- **Issue #16**: Added Criterion benchmarks
  - `benches/obfuscation.rs`: obfuscation time vs gates, wires, size overhead
  - `benches/evaluation.rs`: evaluation time, SEH verification, correctness check
  - Run with `cargo bench --bench obfuscation` or `cargo bench --bench evaluation`
- Total: 47 tests pass

### SEH, SmallObf & PRF Puncturing Integration (Milestone 3)
- SEH fully integrated into ObfuscatedLiO:
  - `seh_params`, `seh_ciphertexts`, `seh_committed_values` fields stored
  - `verify_seh()` method validates all SEH openings against digest
  - `seh_opening(position)` returns SEH opening for inspection
  - `evaluate_with_seh_check(input)` verifies SEH before evaluation
  - `seh_consistency_proof/verify` for prefix consistency between obfuscations
- SmallObf integrated per-gate:
  - `GateGadget::to_bytecode_program()` converts gates to bytecode
  - `StubSmallObf::eval()` extended with gate gadget opcodes (0x10-0x17)
  - `ObfuscatedGate::gadget_obf` field contains obfuscated gate gadget
  - Gate evaluation now goes through SmallObf interface
- PRF puncturing exposed for security analysis:
  - `ObfuscatedGate::prf_input_for_entry()` returns exact PRF input bits
  - Test demonstrates punctured key blocks correct input while allowing others
- Added 8 new tests for SEH, SmallObf, and PRF functionality
- Total: 46 tests pass

### Real FHE Integration & Wire Labels (Milestone 2)
- Added real LWE-based FHE backend via `tfhe` crate (optional, `tfhe-backend` feature)
  - `TfheFhe` wrapper implementing `FheScheme` trait
  - `DefaultFhe` type alias switching between `StubFhe` and `TfheFhe` based on feature
- Generalized SEH over FHE backends:
  - `GenericSeh<F>` works with any `FheScheme` implementation
  - `SehOpening<Ct>` is now generic over ciphertext type
  - `CiphertextBytes` trait for serializing ciphertexts for Merkle hashing
  - `DefaultSeh` alias uses `DefaultFhe`
- Implemented proper per-wire labels as required by the paper:
  - `WireLabels` struct with two random 32-byte labels (L_i^0, L_i^1) per wire
  - Gate tables now encrypt output labels keyed by input labels
  - PRF input built from full label bytes (256+256 bits) plus gate index
- Integrated MAC verification into evaluation:
  - MACs are now verified during `ObfuscatedGate::evaluate()`
  - Panics on tampered table entries (integrity check)
  - Added test `test_lio_mac_verification_detects_tampering`
- Cargo features:
  - `stub-fhe` (default): Fast stub FHE for development
  - `tfhe-backend`: Real LWE-based FHE (slow compile)
- Updated documentation in `lib.rs` and `lio.rs` with implementation status

### Core Library Refactoring (Milestone 0 & 1)
- Refactored stub types into modular architecture with proper trait abstractions
- Created `src/circuit.rs` - Circuit/Gate/ControlFunction with evaluation and random generation
- Created `src/crypto/` module with cryptographic primitive traits:
  - `fhe.rs` - FHE trait with StubFhe implementation
  - `prf.rs` - GGM-based Puncturable PRF implementation (real crypto!)
  - `prg.rs` - SHA-256 based PRG implementation (real crypto!)
  - `seh.rs` - Somewhere Extractable Hash trait with StubSeh
  - `obf.rs` - Small-circuit iO trait (documented assumption)
- Created `src/lio.rs` - Local iO implementation with:
  - Real PRF-based wire encryption (GGM tree)
  - Real MAC generation using PRG
  - Encrypted truth tables per gate
  - Correct evaluation verified against plaintext circuits
- Created `src/padding.rs` - Circuit padding with routing networks
- Added `src/lib.rs` compatibility module for proven_stealth_mix
- All 34 unit tests pass, 7 integration tests pass

### Honeypot Demo Improvements
- Added `simple_hash` to WASM matching Noir circuit commitment scheme
- Added `generate_noir_witness()` for generating Noir-compatible witness JSON
- Added `compute_program_hash()` for hash verification
- Replaced mock ObfProg with real generated program (`web/data/obf_prog.json`)
- Updated web UI to load real obfuscated program
- Added `scripts/generate_obf_prog.py` for generating ObfuscatedProgram JSON
- Hash alignment verified: WASM, Noir, and Python all produce hash=136 for 16 identity matrices
- Added Vite build system for web app (ESNext target, WASM support)
- Integrated @aztec/bb.js and @noir-lang/noir_js for browser-based proof generation
- Added UltraHonkBackend for zkSNARK proof generation
- Modularized web app into src/app.js and src/noir-prover.js

### Lean 4 Formalization Complete
- **Status**: 0 sorries, 0 errors, 2 documented axioms
- **Main theorem**: `main_theorem` in Security.lean proves LiO + Pad = full iO

#### Files Added
- `LocalIO.lean`: Local iO, hybrid indistinguishability, `HybridIndistinguishable`
- `Security.lean`: Theorem 1 security reduction, `hybrid_chain_indist`

#### Key Theorems Proven
- `main_theorem`: Full iO security from LiO + padding
- `composed_io_is_full_io`: Composed obfuscator is full iO
- `hybrid_chain_from_seq`: Build hybrid chains from sequences
- `HybridIndistinguishable.toIndistinguishable`: Collapse chains (via axiom)
- `pad_preserves_functionality`: Padding preserves circuit semantics
- `SEquivalent.refl/symm`, `TransitiveSEquivalent.symm/trans`
- `Circuit.induced`: Subcircuit extraction with all invariants

#### Axioms (2)
| Axiom | Purpose |
|-------|---------|
| `Indistinguishable.trans` | Transitivity of computational indistinguishability |
| `pad_transitive_sequiv_core` | Property ★: Padded circuits are transitively s-equivalent |

### Initial Release
- Core Ma-Dai-Shi iO implementation (`src/lib.rs`)
- Honeypot demo with Noir circuits, Solidity contracts, WASM evaluator
- Interactive protocol visualization
- BIP-39 seed phrase support

### Features
- Quasi-linear Õ(N) obfuscation (N = circuit size + proof size)
- Padding to fixed topology with routing networks
- LiO (Local iO) with SEH + FHE
- Browser-based evaluation via WASM
- zkSNARK proof generation for on-chain verification
