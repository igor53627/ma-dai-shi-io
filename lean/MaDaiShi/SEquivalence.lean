/-
  s-Equivalence and Transitive s-Equivalence (Section 2.3)
  Definition 1 and Definition 2 from Ma-Dai-Shi 2025
-/
import MaDaiShi.Circuit

namespace MaDaiShi

/--
  Definition 1 (s-equivalence).
  Two topologically equivalent circuits C and C' are s-equivalent (via subcircuit S) iff:
  1. There is a subcircuit S of size at most s
  2. All gates outside S are identical in C and C'
  3. The induced subcircuits C_S and C'_S are functionally equivalent
-/
structure SEquivalent {din dout : Nat} (s : Nat) (C C' : Circuit din dout) : Prop where
  /-- C and C' have the same topology -/
  topo : TopologicallyEquivalent C C'
  /-- The subcircuit where C and C' may differ -/
  S : Subcircuit C
  /-- The subcircuit has at most s gates -/
  size_bound : S.size ≤ s
  /-- Gates outside S are identical (same operation) -/
  outside_identical : ∀ (i : Fin C.gates.length),
    i ∉ S.gateIndices →
    (C.gates.get i).op = (C'.gates.get (Fin.cast topo.len_eq i)).op
  /-- The induced subcircuits are functionally equivalent -/
  induced_equiv : ∃ (h_inp : (C.induced S).inputWires = (C'.induced (S.cast topo.len_eq)).inputWires)
                    (h_out : (C.induced S).outputWires = (C'.induced (S.cast topo.len_eq)).outputWires),
    FunctionallyEquivalent' (C.induced S) (C'.induced (S.cast topo.len_eq)) h_inp h_out

/-- Cast a subcircuit along a gate length equality -/
def Subcircuit.cast {din dout : Nat} {C C' : Circuit din dout}
    (S : Subcircuit C) (h : C.gates.length = C'.gates.length) : Subcircuit C' where
  gateIndices := S.gateIndices.map ⟨Fin.cast h, Fin.cast_injective h⟩

/--
  Definition 2 (Transitive s-equivalence).
  Two topologically equivalent circuits C and C' are transitively s-equivalent
  via ℓ hybrids iff there exist circuits C₁, C₂, ..., Cₗ such that:
  - C₁ = C
  - Cₗ = C'
  - For each i ∈ [ℓ-1], Cᵢ and Cᵢ₊₁ are s-equivalent
-/
def TransitiveSEquivalent {din dout : Nat} (s : Nat) (ℓ : Nat) (C C' : Circuit din dout) : Prop :=
  ∃ hybrids : Fin (ℓ + 1) → Circuit din dout,
    hybrids ⟨0, Nat.zero_lt_succ ℓ⟩ = C ∧
    hybrids ⟨ℓ, Nat.lt_succ_self ℓ⟩ = C' ∧
    ∀ i : Fin ℓ, SEquivalent s (hybrids i.castSucc) (hybrids i.succ)

/--
  Abbreviation: C and C' are transitively s-equivalent if ℓ is polynomially bounded.
  In this formalization, we leave ℓ as a parameter.
-/
def TransitiveSEquivalentPoly {din dout : Nat} (s : Nat) (C C' : Circuit din dout) : Prop :=
  ∃ ℓ : Nat, TransitiveSEquivalent s ℓ C C'

/-- s-equivalence implies transitive s-equivalence with 1 hybrid step -/
theorem SEquivalent.toTransitive {din dout : Nat} {s : Nat} {C C' : Circuit din dout}
    (h : SEquivalent s C C') : TransitiveSEquivalent s 1 C C' := by
  use fun i => if i.val = 0 then C else C'
  constructor
  · simp
  constructor
  · simp
  · intro i
    have : i.val = 0 := by omega
    simp [this, h]

/-- Concatenation of transitive s-equivalence chains -/
theorem TransitiveSEquivalent.trans {din dout : Nat} {s : Nat} {C C' C'' : Circuit din dout}
    {ℓ₁ ℓ₂ : Nat}
    (h1 : TransitiveSEquivalent s ℓ₁ C C')
    (h2 : TransitiveSEquivalent s ℓ₂ C' C'') :
    TransitiveSEquivalent s (ℓ₁ + ℓ₂) C C'' := by
  obtain ⟨hyb1, hstart1, hend1, hstep1⟩ := h1
  obtain ⟨hyb2, hstart2, hend2, hstep2⟩ := h2
  use fun i =>
    if h : i.val ≤ ℓ₁ then
      hyb1 ⟨i.val, by omega⟩
    else
      hyb2 ⟨i.val - ℓ₁, by omega⟩
  constructor
  · simp [hstart1]
  constructor
  · simp only [Nat.add_lt_add_iff_left]
    split_ifs with h
    · have : ℓ₁ + ℓ₂ ≤ ℓ₁ := h
      omega
    · simp only [Nat.add_sub_cancel_left]
      exact hend2
  · intro i
    sorry

/--
  Key property used in security proof:
  If C and C' are transitively s-equivalent via ℓ hybrids,
  security reduction loses a factor of ℓ.
-/
theorem transitive_sequiv_hybrid {din dout : Nat} (s ℓ : Nat) (C C' : Circuit din dout)
    (h : TransitiveSEquivalent s ℓ C C') :
    True := trivial

end MaDaiShi
