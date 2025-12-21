# Ma-Dai-Shi Lean 4 Formalization: Technical Details

This document provides in-depth technical documentation of the Lean 4 formalization
of the Ma-Dai-Shi 2025 quasi-linear iO construction.

## Architecture Overview

```
MaDaiShi.lean (root module)
    |
    +-- Circuit.lean         -- DAG circuits, evaluation, topological equivalence
    +-- ExtendedFrege.lean   -- EF proof system, formulas, derivations
    +-- SEquivalence.lean    -- s-equivalence (Def 1-2), hybrid chains
    +-- Padding.lean         -- Pad algorithm, Lemma 3.1
    +-- PaddingConstruction.lean -- Skeleton-based padding, Config/Mode
    +-- LocalIO.lean         -- Local iO, indistinguishability, Theorem 1 setup
    +-- Security.lean        -- Main theorem, security reduction
```

## Core Definitions

### Circuit.lean

**`Circuit din dout`**: A circuit with fan-in `din` and fan-out `dout`.

```lean
structure Circuit (din dout : Nat) where
  gates : List (Gate din dout)
  inputWires : List WireId
  outputWires : List WireId
  inputWires_nodup : inputWires.Nodup
  outputWires_nodup : outputWires.Nodup
  topological : ∀ (i : Nat) (hi : i < gates.length) (k : Fin din), ...
  inputs_not_outputs : ...
  unique_drivers : ...
```

Key invariants:
- **Topological ordering**: Gate i only reads from inputs or outputs of gates j < i
- **Unique drivers**: Each wire is produced by at most one gate
- **No input-output conflict**: Primary inputs are never produced by gates

**`Circuit.eval`**: Evaluates a circuit on boolean inputs.

```lean
def Circuit.eval (C : Circuit din dout) 
    (x : Fin C.inputWires.length → Bool) : Fin C.outputWires.length → Bool
```

**`Circuit.withOps`**: Replace gate operations while preserving topology.

```lean
def Circuit.withOps (C : Circuit din dout)
    (ops : Fin C.gates.length → GateOp din dout) : Circuit din dout
```

This is crucial for the padding construction - it allows varying gate operations
on a fixed skeleton topology.

**`TopologicallyEquivalent`**: Same graph structure, possibly different operations.

**`FunctionallyEquivalent'`**: Same input-output behavior.

**`Subcircuit`** and **`Circuit.induced`**: Extract a subset of gates as a standalone circuit.

### SEquivalence.lean

**`SEquivalent s C C'`** (Definition 1): Two topologically equivalent circuits
are s-equivalent if they differ on at most s gates, and the induced subcircuits
on those gates are functionally equivalent.

```lean
def SEquivalent (s : Nat) (C C' : Circuit din dout) : Prop :=
  ∃ (topo : TopologicallyEquivalent C C') (S : Subcircuit C),
    S.size ≤ s ∧
    (∀ i ∉ S.gateIndices, (C.gates.get i).op = (C'.gates.get ...).op) ∧
    FunctionallyEquivalent' (C.induced S) (C'.induced (S.cast ...)) ...
```

**`TransitiveSEquivalent s ℓ C C'`** (Definition 2): A chain of ℓ+1 circuits
where consecutive pairs are s-equivalent.

```lean
def TransitiveSEquivalent (s ℓ : Nat) (C C' : Circuit din dout) : Prop :=
  ∃ hybrids : Fin (ℓ + 1) → Circuit din dout,
    hybrids 0 = C ∧
    hybrids ℓ = C' ∧
    ∀ i : Fin ℓ, SEquivalent s (hybrids i.castSucc) (hybrids i.succ)
```

### Padding.lean

**`Pad C Ncirc Nproof h`**: The padding algorithm from Section 3.2.

Currently uses `Classical.choose` with a trivial witness (the original circuit).
The key properties are:
- Size bound: `Pad.size ≤ O_tilde(Ncirc + Nproof)`
- Functionality preserved: `FunctionallyEquivalent' (Pad C ...) C`

**`pad_transitive_sequiv_core`** (AXIOM): The core algorithmic construction.

```lean
axiom pad_transitive_sequiv_core {din dout : Nat}
    (C₁ C₂ : Circuit din dout) (Ncirc Nproof : Nat)
    (hC₁ : C₁.size ≤ Ncirc) (hC₂ : C₂.size ≤ Ncirc)
    (π : EquivalenceProof C₁ C₂) (hπ : π.proof.size ≤ Nproof) :
    TransitiveSEquivalent (O_log (Ncirc + Nproof)) (Ncirc + Nproof)
      (Pad C₁ ...) (Pad C₂ ...)
```

This is Property ★ from the paper. See issue #19 for elimination plan.

### PaddingConstruction.lean

This file demonstrates the proof structure for eliminating the axiom.

**`PadSkeleton`**: Canonical circuit topology depending only on parameters.

```lean
noncomputable def PadSkeleton (din dout numInputs numOutputs Ncirc Nproof : Nat) 
    : Circuit din dout
```

Currently uses 0 gates (placeholder). With a full implementation, this would have
O(N log N) gates implementing Beneš networks and selector/copy gadgets.

**`Config` and `Mode`**: Hybrid chain configuration.

```lean
inductive Mode where
  | C1 : Mode  -- Block interprets C₁
  | C2 : Mode  -- Block interprets C₂

structure Config (ℓ : Nat) where
  mode : Fin ℓ → Mode
```

**`Config.atStep i`**: Configuration at hybrid step i (blocks 0..i-1 in C2 mode).

**`Hybrid`**: The i-th hybrid circuit.

```lean
noncomputable def Hybrid (C₁ C₂ : Circuit din dout) (Ncirc Nproof : Nat)
    (hC₁ : C₁.size ≤ Ncirc) (hC₂ : C₂.size ≤ Ncirc)
    (i : Fin (numBlocks Ncirc Nproof + 1)) : Circuit din dout
```

**`pad_transitive_sequiv_core_v2`**: The theorem version (proven with trivial skeleton).

### LocalIO.lean

**`Advantage`**: Rational number representing distinguishing advantage.

```lean
structure Advantage where
  numerator : Nat
  denominator : Nat
  denom_pos : 0 < denominator
```

**`isNegligible`**: Standard cryptographic negligibility (asymptotic).

```lean
def isNegligible (adv : SecurityParam → Advantage) : Prop :=
  ∀ c : Nat, ∃ N : Nat, ∀ κ ≥ N, 
    (adv κ).numerator * κ^c ≤ (adv κ).denominator
```

**`Distinguisher`**: PPT distinguisher with triangle inequality.

```lean
structure Distinguisher where
  distinguish : SecurityParam → ObfuscatedProgram → ObfuscatedProgram → Advantage
  triangle : ∀ κ P P' P'', 
    distinguish κ P P'' ≤ (distinguish κ P P').add (distinguish κ P' P'')
```

**`Indistinguishable P P'`**: All PPT distinguishers have negligible advantage.

```lean
def Indistinguishable (P P' : ObfuscatedProgram) : Prop :=
  ∀ D : Distinguisher, isNegligible (fun κ => D.distinguish κ P P')
```

**`Indistinguishable.trans`** (THEOREM, not axiom):

```lean
theorem Indistinguishable.trans (h1 : Indistinguishable P P') 
    (h2 : Indistinguishable P' P'') : Indistinguishable P P'' := by
  intro D
  have hsum := negligible_add (h1 D) (h2 D)
  have hle := fun κ => D.triangle κ P P' P''
  exact negligible_of_le hsum hle
```

### Security.lean

**`main_theorem`** (Theorem 1): The main security result.

```lean
theorem main_theorem {din dout : Nat}
    (lio : LocalIO din dout)
    (C₁ C₂ : Circuit din dout)
    (π : EquivalenceProof C₁ C₂)
    ... :
    Indistinguishable 
      (lio.obfuscate (Pad C₁ Ncirc Nproof hC₁))
      (lio.obfuscate (Pad C₂ Ncirc Nproof hC₂))
```

## Proof Techniques

### Eliminating the Indistinguishable.trans Axiom

The key insight is that with the asymptotic definition of negligibility,
the class of negligible functions is closed under:
1. **Addition**: `negligible_add` - sum of negligibles is negligible
2. **Monotonicity**: `negligible_of_le` - if f ≤ g pointwise and g is negligible, f is negligible

Combined with the triangle inequality (a property of any distinguisher by definition),
transitivity follows directly.

### The Skeleton+withOps Pattern

The `PaddingConstruction.lean` file introduces a key pattern:

1. Define a canonical **skeleton** that depends only on parameters (Ncirc, Nproof)
2. Use `Circuit.withOps` to create actual circuits by assigning gate operations
3. All circuits built from the same skeleton are **topologically equivalent**
4. This makes s-equivalence proofs tractable

```lean
theorem skeleton_withOps_topo_invariant (Skel : Circuit din dout)
    (ops₁ ops₂ : Fin Skel.gates.length → GateOp din dout) :
    TopologicallyEquivalent (Skel.withOps ops₁) (Skel.withOps ops₂)
```

### Hybrid Chain Construction

The hybrid argument proceeds as:

1. Define `Config.atStep i` where blocks 0..i-1 are in C2 mode
2. `Hybrid i` uses the skeleton with operations from `PadOpsCfg` at config i
3. Consecutive hybrids differ only on block i (O(log N) gates)
4. Each step is s-equivalent via the Ma-Dai-Shi construction

## Asymptotic Bounds

| Bound | Definition | Meaning |
|-------|------------|---------|
| `O_log n` | `Nat.log2 n + 1` | Logarithmic |
| `O_tilde n` | `n * (Nat.log2 n + 1)` | Quasi-linear |
| `poly n` | `n * n` | Polynomial (placeholder) |

## File Dependencies

```
Circuit.lean
    ↓
ExtendedFrege.lean ← Circuit.lean
    ↓
SEquivalence.lean ← Circuit.lean
    ↓
Padding.lean ← Circuit.lean, SEquivalence.lean, ExtendedFrege.lean
    ↓
PaddingConstruction.lean ← Circuit.lean, SEquivalence.lean, ExtendedFrege.lean, Padding.lean
    ↓
LocalIO.lean ← Circuit.lean, SEquivalence.lean, Padding.lean
    ↓
Security.lean ← all above
```

## Testing the Build

```bash
cd lean
~/.elan/bin/lake build
```

Verify no sorries:
```bash
grep -n "sorry" MaDaiShi/*.lean
# Should return empty
```

Count axioms:
```bash
grep -n "^axiom" MaDaiShi/*.lean
# Should show only pad_transitive_sequiv_core
```

## References

- [Ma-Dai-Shi 2025](https://eprint.iacr.org/2025/307) - The original paper
- [Lean 4 Documentation](https://lean-lang.org/documentation/)
- [Mathlib4](https://github.com/leanprover-community/mathlib4) - Mathematical library
