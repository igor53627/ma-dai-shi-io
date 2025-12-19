# Ma-Dai-Shi 2025 - Lean 4 Formalization

Minimal Lean 4 formalization of core definitions from:

**"Quasi-Linear Indistinguishability Obfuscation via Mathematical Proofs of Equivalence and Applications"**
- Paper: [eprint.iacr.org/2025/307](https://eprint.iacr.org/2025/307)

## Structure

```
MaDaiShi/
  Circuit.lean        -- Section 2.1: Circuits as DAGs
  ExtendedFrege.lean  -- Section 2.2: Extended Frege proof system
  SEquivalence.lean   -- Section 2.3: s-equivalence (Def 1-2)
  Padding.lean        -- Section 3.2: Lemma 3.1 (padding correctness)
```

## Key Definitions Formalized

| Definition                         | Section    | File                |
|------------------------------------|------------|---------------------|
| `TopologicallyEquivalent`          | 2.1        | Circuit.lean        |
| `FunctionallyEquivalent`           | 2.1        | Circuit.lean        |
| `SEquivalent s C C'`               | 2.3 Def 1  | SEquivalence.lean   |
| `TransitiveSEquivalent s l C C'`   | 2.3 Def 2  | SEquivalence.lean   |
| `EFProof`                          | 2.2        | ExtendedFrege.lean  |
| `EquivalenceProof C C'`            | 2.2        | ExtendedFrege.lean  |

## Key Theorems (Stated, not proven)

| Theorem                                              | Status   |
|------------------------------------------------------|----------|
| Lemma 2.1: EF proof -> circuit                       | `sorry`  |
| Lemma 2.3: Trivial equivalence proof                 | `sorry`  |
| Lemma 3.1: Padding preserves functionality           | `sorry`  |
| Lemma 3.1: Padding yields transitive O(log N)-equiv  | `sorry`  |

## Building

```bash
lake update
lake build
```

Requires Lean 4.14.0 and mathlib.

## Usage

Reference these definitions when implementing the Rust code in `src/`. The Lean definitions provide:
1. Precise mathematical specifications
2. Type-level invariants to guide implementation
3. A path toward full verification (future work)
