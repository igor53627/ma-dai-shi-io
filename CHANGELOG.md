# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/).

## [Unreleased]

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
