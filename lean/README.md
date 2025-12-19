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
```

## Key Definitions Formalized

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
| `TransitiveSEquivalent s ℓ C C'`   | 2.3 Def 2  | SEquivalence.lean   | [OK]       |
| `PadSingle`, `Pad`                 | 3.2        | Padding.lean        | [OK]       |

## Key Theorems

| Theorem                                              | File               | Status      |
|------------------------------------------------------|--------------------|-------------|
| `FunctionallyEquivalent'.refl`                       | Circuit.lean       | [OK]        |
| `FunctionallyEquivalent'.symm`                       | Circuit.lean       | `sorry`     |
| `FunctionallyEquivalent'.trans`                      | Circuit.lean       | `sorry`     |
| `Circuit.induced.topological`                        | Circuit.lean       | `sorry`     |
| `SEquivalent.toTransitive`                           | SEquivalence.lean  | [OK]        |
| `TransitiveSEquivalent.trans`                        | SEquivalence.lean  | `sorry`     |
| Lemma 2.1: `ef_proof_as_circuit`                     | ExtendedFrege.lean | `sorry`     |
| Lemma 2.3: `trivial_equiv_proof`                     | ExtendedFrege.lean | `sorry`     |
| Lemma 3.1a: `pad_preserves_functionality`            | Padding.lean       | via axiom   |
| Lemma 3.1b: `pad_transitive_sequiv` (Property ★)     | Padding.lean       | `sorry`     |
| `pad_size_quasi_linear`                              | Padding.lean       | via axiom   |

## Design Decisions

1. **Topological list representation**: Gates stored in topological order, avoiding general DAG machinery
2. **Explicit bounds**: Using concrete functions (`O_log`, `O_tilde`, `poly`) instead of mathlib's `IsBigO`
3. **Existence-first approach**: Padding uses `Classical.choose` from existence lemmas, deferring constructive implementation
4. **Proper invariants**: `Circuit` requires explicit proofs of `inputWires_nodup`, `outputWires_nodup`, and `topological`

## Building

```bash
lake update
lake build
```

Requires Lean 4.14.0 and mathlib.

## Remaining Work

### Phase 1 (Circuit semantics)
- [ ] `Circuit.induced.topological` - subgraph inherits topo-order
- [ ] `FunctionallyEquivalent'.symm/trans` - cast chasing proofs
- [ ] `TopologicallyEquivalent.functionallyEquivalent`

### Phase 2 (Extended Frege)
- [ ] `ef_proof_as_circuit` (Lemma 2.1)
- [ ] `trivial_equiv_proof` (Lemma 2.3)

### Phase 3 (s-Equivalence)
- [ ] `TransitiveSEquivalent.trans` - chain concatenation

### Phase 4 (Padding)
- [ ] `exists_PadSingle` - routing network construction
- [ ] `exists_Pad` - full padding construction
- [ ] `pad_transitive_sequiv` - hybrid argument from EF proof

## References

- [GitHub Issues](https://github.com/igor53627/ma-dai-shi-io/issues) for tracking
- Oracle consultation recommended for complex proofs
