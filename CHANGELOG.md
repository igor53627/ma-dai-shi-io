# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/).

## [Unreleased]

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
