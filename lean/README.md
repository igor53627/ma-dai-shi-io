# Ma-Dai-Shi 2025 - Lean 4 Formalization

Formal verification of core definitions and theorems from:

**"Quasi-Linear Indistinguishability Obfuscation via Mathematical Proofs of Equivalence and Applications"**
- Paper: [eprint.iacr.org/2025/307](https://eprint.iacr.org/2025/307)

## Structure

```
MaDaiShi/
  Circuit.lean        -- Section 2.1: Circuits as DAGs with evaluation semantics
  ExtendedFrege.lean  -- Section 2.2: Extended Frege proof system
  SEquivalence.lean   -- Section 2.3: s-equivalence (Def 1-2)
  Padding.lean        -- Section 3.2: Lemma 3.1 (padding correctness)
  LocalIO.lean        -- Section 4: Local iO and hybrid indistinguishability
  Security.lean       -- Theorem 1: Main security reduction
```

## Build Status

**All files compile without `sorry` markers.**

The formalization uses **2 axioms** representing foundational concepts that would
require either probabilistic semantics or substantial algorithmic implementation.

## Axioms

| Axiom | File | Purpose |
|-------|------|---------|
| `Indistinguishable.trans` | LocalIO.lean | Transitivity of computational indistinguishability |
| `pad_transitive_sequiv_core` | Padding.lean | Property ★: Padded circuits are transitively s-equivalent |

### Axiom 1: `Indistinguishable.trans` (Cryptographic Foundation)

**Location:** LocalIO.lean, line 92

**Statement:** If P ≈ P' and P' ≈ P'', then P ≈ P''.

**Why it's an axiom:** The current model treats `Indistinguishable` as a *relational*
concept capturing the logical structure of hybrid arguments. The quantitative semantics
(advantages, negligible functions) would require:
- Distinguishing advantage depending on security parameter κ
- Formalizing the triangle inequality for statistical distance
- Proving sum of negligible functions is negligible

**Justification:** This is the standard transitivity property used in all hybrid-style
cryptographic proofs. The axiom is well-justified by:
```
|Pr[D(P)=1] - Pr[D(P'')=1]| ≤ |Pr[D(P)=1] - Pr[D(P')=1]| + |Pr[D(P')=1] - Pr[D(P'')=1]|
```
Combined with closure of negligible functions under addition.

**Usage:** Used by `HybridIndistinguishable.toIndistinguishable` to collapse hybrid chains.

### Axiom 2: `pad_transitive_sequiv_core` (Algorithmic Construction)

**Location:** Padding.lean, line 123

**Statement:** Given circuits C₁, C₂ with an EF proof π of equivalence, their padded
versions Pad(C₁) and Pad(C₂) are transitively O(log N)-equivalent via N hybrids.

**Why it's an axiom:** This represents the core algorithmic construction from Section 3.2
of the Ma-Dai-Shi paper. Proving it would require implementing:
1. **Routing networks** (Beneš permutation networks) to map gates to fixed positions
2. **Selector gadgets** with O(log N) depth to enable/disable gates
3. **Copy gadgets** using binary trees for fan-out
4. **Explicit hybrid chain construction** guided by the EF proof structure

**Current `Pad` implementation:** Uses `Classical.choose` with a trivial witness (returns
the original circuit). The size and functionality bounds are satisfied, but the topological
properties needed for s-equivalence require the full algorithmic construction.

**Justification:** This is Property ★ from the paper, proven in Section 3.2. The key insight
is that Pad produces circuits with *identical topology* for the same (Ncirc, Nproof), differing
only in a subcircuit of size O(log N) at each hybrid step.

**Effort to eliminate:** XL (multi-day to multi-week project) requiring formalization of
routing networks, gadgets, and explicit hybrid chain extraction from EF proofs

## Key Definitions

| Definition                         | Section    | File                | Status     |
|------------------------------------|------------|---------------------|------------|
| `Circuit.eval`                     | 2.1        | Circuit.lean        | [OK]       |
| `FunctionallyEquivalent`           | 2.1        | Circuit.lean        | [OK]       |
| `TopologicallyEquivalent`          | 2.1        | Circuit.lean        | [OK]       |
| `Subcircuit.inp/out`               | 2.1        | Circuit.lean        | [OK]       |
| `Circuit.induced`                  | 2.1        | Circuit.lean        | [OK]       |
| `Formula.eval`                     | 2.2        | ExtendedFrege.lean  | [OK]       |
| `EFProof`                          | 2.2        | ExtendedFrege.lean  | [OK]       |
| `EquivalenceProof`                 | 2.2        | ExtendedFrege.lean  | [OK]       |
| `SEquivalent s C C'`               | 2.3 Def 1  | SEquivalence.lean   | [OK]       |
| `TransitiveSEquivalent s l C C'`   | 2.3 Def 2  | SEquivalence.lean   | [OK]       |
| `PadSingle`, `Pad`                 | 3.2        | Padding.lean        | [OK]       |
| `LocalIO`                          | 4          | LocalIO.lean        | [OK]       |
| `HybridIndistinguishable`          | 4          | LocalIO.lean        | [OK]       |

## Key Theorems

| Theorem                                              | File               | Status      |
|------------------------------------------------------|--------------------|-------------|
| `FunctionallyEquivalent'.refl/symm/trans`            | Circuit.lean       | [OK]        |
| `TopologicallyEquivalent.functionallyEquivalent`     | Circuit.lean       | [OK]        |
| `Circuit.induced` (all invariants)                   | Circuit.lean       | [OK]        |
| `SEquivalent.refl/symm`                              | SEquivalence.lean  | [OK]        |
| `TransitiveSEquivalent.symm/trans`                   | SEquivalence.lean  | [OK]        |
| Lemma 2.1: `ef_proof_as_circuit`                     | ExtendedFrege.lean | [OK]*       |
| Lemma 2.2: `union_circuit_exists`                    | ExtendedFrege.lean | [OK]*       |
| Lemma 2.3: `trivial_equiv_proof`                     | ExtendedFrege.lean | [OK]        |
| Lemma 3.1a: `pad_preserves_functionality`            | Padding.lean       | [OK]        |
| Lemma 3.1b: `pad_transitive_sequiv`                  | Padding.lean       | via axiom   |
| `hybrid_chain_from_seq`                              | LocalIO.lean       | [OK]        |
| `HybridIndistinguishable.trans`                      | LocalIO.lean       | [OK]        |
| `hybrid_chain_indist`                                | Security.lean      | [OK]        |
| **Theorem 1**: `main_theorem`                        | Security.lean      | [OK]        |
| `composed_io_is_full_io`                             | Security.lean      | [OK]        |

`[OK]*` = Proven with trivial witnesses; size bounds satisfied, full semantics deferred.

## Proof Structure

The main theorem (`main_theorem` in Security.lean) states:

> Given a local iO with s = O(log N), two circuits C₁, C₂ with an EF proof π,
> then LiO(Pad(C₁)) and LiO(Pad(C₂)) are computationally indistinguishable.

The proof proceeds as follows:

1. **Padding** (Padding.lean): `pad_transitive_sequiv` shows that Pad(C₁) and Pad(C₂)
   are transitively O(log N)-equivalent via poly(N) hybrids (via axiom).

2. **Hybrid Chain** (Security.lean): `hybrid_chain_indist` builds a chain of
   obfuscated programs and shows indistinguishability using:
   - `SEquivalent.mono` to lift s-equivalence to lio.s
   - `lio.s_indist` to get indistinguishability for each step
   - `hybrid_chain_from_seq` to build `HybridIndistinguishable`
   - `HybridIndistinguishable.toIndistinguishable` to get final result (via axiom)

## Building

```bash
lake update
lake build
```

Requires Lean 4.14.0 and mathlib.

## Design Decisions

### Relational vs Quantitative Indistinguishability

This formalization uses a **relational** model of computational indistinguishability rather
than a fully quantitative one. The current `Advantage` and `isNegligible` definitions provide
intuition but have a limitation: `D.distinguish P P'` doesn't depend on the security parameter κ,
so `isNegligible` degenerates to requiring `numerator = 0`.

The alternative (Option B from our analysis) would require:
- κ-dependent distinguisher output
- Probability theory formalization
- Explicit advantage arithmetic

For the logical structure of the Ma-Dai-Shi proof, the relational approach is sufficient
and cleaner. The axiom `Indistinguishable.trans` explicitly captures what we need.

### Trivial Pad Witnesses

The `Pad` function uses `Classical.choose` with a trivial witness (the original circuit).
This satisfies size bounds and functional equivalence, but the *topological* properties
(s-equivalence of padded circuits) are axiomatized via `pad_transitive_sequiv_core`.

This design separates:
- **What we can prove now**: Size bounds, functionality
- **What requires algorithmic implementation**: Topology-preserving padding construction

## Future Work

### Eliminating `Indistinguishable.trans`

**Effort: L (days to week)**

Option A (Recommended): Accept as fundamental axiom. It's the standard transitivity of
equivalence relations used in all hybrid arguments.

Option B (Full formalization): Extend the `Advantage` model:
- Make `Distinguisher.distinguish` depend on security parameter κ
- Formalize advantage arithmetic and the triangle inequality
- Prove closure of negligible functions under addition

### Eliminating `pad_transitive_sequiv_core`

**Effort: XL (weeks)**

1. Implement routing networks (Beneš permutation networks) as circuits
2. Implement selector gadgets with O(log N) depth
3. Implement copy gadgets using binary trees
4. Redefine `Pad` to use these combinators
5. Prove that `Pad C₁` and `Pad C₂` have identical topology for fixed (Ncirc, Nproof)
6. Extract explicit hybrid chain from EF proof structure
7. Prove each hybrid step is O(log N)-equivalent

## References

- [Ma-Dai-Shi 2025 Paper](https://eprint.iacr.org/2025/307)
- [GitHub Issues](https://github.com/igor53627/ma-dai-shi-io/issues) for tracking
