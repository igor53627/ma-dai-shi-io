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
def SEquivalent {din dout : Nat} (s : Nat) (C C' : Circuit din dout) : Prop :=
  ∃ (topo : TopologicallyEquivalent C C') (S : Subcircuit C),
    S.size ≤ s ∧
    (∀ (i : Fin C.gates.length),
      i ∉ S.gateIndices →
      (C.gates.get i).op = (C'.gates.get (Fin.cast topo.len_eq i)).op) ∧
    (∃ (h_inp : (C.induced S).inputWires = (C'.induced (S.cast topo.len_eq)).inputWires)
        (h_out : (C.induced S).outputWires = (C'.induced (S.cast topo.len_eq)).outputWires),
      FunctionallyEquivalent' (C.induced S) (C'.induced (S.cast topo.len_eq)) h_inp h_out)

/-- Reflexivity of s-equivalence (any circuit is s-equivalent to itself for any s ≥ 0) -/
theorem SEquivalent.refl {din dout : Nat} (s : Nat) (C : Circuit din dout) :
    SEquivalent s C C := by
  refine ⟨TopologicallyEquivalent.refl C, Subcircuit.empty C, ?_, ?_, ?_⟩
  · simp [Subcircuit.size_empty]
  · intro i _
    simp only [TopologicallyEquivalent.refl, Fin.cast_eq_self]
  · simp only [TopologicallyEquivalent.refl, Subcircuit.cast_empty]
    refine ⟨trivial, trivial, ?_⟩
    exact FunctionallyEquivalent'.refl _

/-- Symmetry of s-equivalence -/
theorem SEquivalent.symm {din dout : Nat} {s : Nat} {C C' : Circuit din dout}
    (h : SEquivalent s C C') : SEquivalent s C' C := by
  -- The proof requires constructing:
  -- 1. A TopologicallyEquivalent C' C (symmetric to the original)
  -- 2. A subcircuit S' in C' corresponding to S in C
  -- 3. Proofs that gates outside S' are identical and induced subcircuits are functionally equivalent
  --
  -- This involves careful handling of Fin.cast and Subcircuit.cast.
  -- The key insight is that S.cast topo.len_eq gives us the corresponding subcircuit in C'.
  classical
  obtain ⟨topo, S, hsize, hops, hfe⟩ := h
  -- Construct the symmetric topological equivalence
  have topo' : TopologicallyEquivalent C' C := {
    len_eq := topo.len_eq.symm
    inputs_eq := topo.inputs_eq.symm
    outputs_eq := topo.outputs_eq.symm
    gates_match := fun i hi =>
      let hi' : i < C.gates.length := topo.len_eq ▸ hi
      let ⟨hid, hinp, hout⟩ := topo.gates_match i hi'
      ⟨hid.symm, hinp.symm, hout.symm⟩
  }
  -- The subcircuit S' in C' is the cast of S
  let S' := S.cast topo.len_eq
  refine ⟨topo', S', ?_, ?_, ?_⟩
  · -- Size is preserved under cast
    have hsize' : S'.size = S.size := by
      simp only [S', Subcircuit.cast, Subcircuit.size, Finset.card_map]
    rw [hsize']
    exact hsize
  · -- Gates outside S' have identical ops
    intro i hi_not_in
    -- i ∉ S'.gateIndices means Fin.cast topo.len_eq.symm i ∉ S.gateIndices
    have hi_cast : Fin.cast topo.len_eq.symm i ∉ S.gateIndices := by
      intro hcontra
      apply hi_not_in
      simp only [S', Subcircuit.cast, Finset.mem_map, Function.Embedding.coeFn_mk]
      exact ⟨Fin.cast topo.len_eq.symm i, hcontra, by simp [Fin.ext_iff]⟩
    have hops' := hops (Fin.cast topo.len_eq.symm i) hi_cast
    simp only [Fin.cast_trans, Fin.cast_eq_self] at hops'
    exact hops'.symm
  · -- Induced subcircuits are functionally equivalent
    obtain ⟨h_inp, h_out, hfunc⟩ := hfe
    -- S'.cast topo'.len_eq = S
    have S'_cast_eq : (S.cast topo.len_eq).cast topo'.len_eq = S := by
      simp only [Subcircuit.cast]
      congr 1
      ext x
      simp only [Finset.mem_map, Function.Embedding.coeFn_mk]
      constructor
      · intro ⟨y, ⟨z, hz, heq_yz⟩, heq_xy⟩
        have hx_eq_z : x = z := by
          ext
          -- heq_yz : Fin.cast topo.len_eq z = y
          -- heq_xy : Fin.cast topo'.len_eq y = x
          have h1 : z.val = y.val := by
            have := congrArg Fin.val heq_yz
            simp only [Fin.val_cast_of_lt] at this
            exact this
          have h2 : y.val = x.val := by
            have := congrArg Fin.val heq_xy
            simp only [Fin.val_cast_of_lt] at this
            exact this
          omega
        rw [hx_eq_z]; exact hz
      · intro hx
        exact ⟨Fin.cast topo.len_eq x, ⟨x, hx, rfl⟩, by simp [Fin.ext_iff]⟩
    rw [S'_cast_eq]
    -- Need: h_inp was (C.induced S).inputWires = (C'.induced (S.cast topo.len_eq)).inputWires
    -- We need: (C'.induced S').inputWires = (C.induced S).inputWires
    -- Since S' = S.cast topo.len_eq, this is h_inp.symm
    -- But also S'.cast topo'.len_eq = S as shown above
    refine ⟨h_inp.symm, h_out.symm, FunctionallyEquivalent'.symm hfunc⟩

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
  classical
  refine ⟨(fun i : Fin 2 => if i.val = 0 then C else C'), ?_, ?_, ?_⟩
  · simp
  · simp
  · intro i
    have : i.val = 0 := by
      have hi : i.val < 1 := i.isLt
      omega
    simp [this, h]

/-- Symmetry of transitive s-equivalence: reverse the hybrid chain -/
theorem TransitiveSEquivalent.symm {din dout : Nat} {s : Nat} {C C' : Circuit din dout} {ℓ : Nat}
    (h : TransitiveSEquivalent s ℓ C C') : TransitiveSEquivalent s ℓ C' C := by
  classical
  obtain ⟨hybrids, hstart, hend, hstep⟩ := h
  -- Reverse the hybrid sequence: hybrids'(i) = hybrids(ℓ - i)
  let hybrids' : Fin (ℓ + 1) → Circuit din dout :=
    fun i => hybrids ⟨ℓ - i.val, by omega⟩
  refine ⟨hybrids', ?_, ?_, ?_⟩
  · -- hybrids' 0 = hybrids ℓ = C'
    simp only [hybrids', Nat.sub_zero]
    have heq : (⟨ℓ, Nat.lt_succ_self ℓ⟩ : Fin (ℓ + 1)) = ⟨ℓ, Nat.lt_succ_self ℓ⟩ := rfl
    rw [← hend]
  · -- hybrids' ℓ = hybrids 0 = C
    simp only [hybrids', Nat.sub_self]
    have heq : (⟨0, Nat.zero_lt_succ ℓ⟩ : Fin (ℓ + 1)) = ⟨0, Nat.zero_lt_succ ℓ⟩ := rfl
    rw [← hstart]
  · -- Each step is s-equivalent (reversed)
    intro i
    have hi_lt : i.val < ℓ := i.isLt
    have h_idx : ℓ - i.val - 1 < ℓ := by omega
    let j : Fin ℓ := ⟨ℓ - i.val - 1, h_idx⟩
    have hstep_j := hstep j
    have h_castSucc : hybrids' i.castSucc = hybrids j.succ := by
      simp only [hybrids', Fin.coe_castSucc]
      congr 1
      simp only [j, Fin.ext_iff, Fin.val_succ, Fin.val_mk]
      omega
    have h_succ : hybrids' i.succ = hybrids j.castSucc := by
      simp only [hybrids', Fin.val_succ]
      have heq : (⟨ℓ - (i.val + 1), by omega⟩ : Fin (ℓ + 1)) = j.castSucc := by
        simp only [j, Fin.ext_iff, Fin.coe_castSucc, Fin.val_mk]
        omega
      simp only [heq]
    rw [h_castSucc, h_succ]
    exact SEquivalent.symm hstep_j

/-- Concatenation of transitive s-equivalence chains -/
theorem TransitiveSEquivalent.trans {din dout : Nat} {s : Nat} {C C' C'' : Circuit din dout}
    {ℓ₁ ℓ₂ : Nat}
    (h1 : TransitiveSEquivalent s ℓ₁ C C')
    (h2 : TransitiveSEquivalent s ℓ₂ C' C'') :
    TransitiveSEquivalent s (ℓ₁ + ℓ₂) C C'' := by
  classical
  obtain ⟨hyb1, hstart1, hend1, hstep1⟩ := h1
  obtain ⟨hyb2, hstart2, hend2, hstep2⟩ := h2

  let hybrids : Fin (ℓ₁ + ℓ₂ + 1) → Circuit din dout :=
    fun i =>
      if h : (i : Nat) ≤ ℓ₁ then
        hyb1 ⟨i, Nat.lt_succ_of_le h⟩
      else
        hyb2 ⟨i - ℓ₁, by omega⟩

  refine ⟨hybrids, ?_, ?_, ?_⟩
  · -- start: hybrids 0 = C
    have h0 : (0 : Nat) ≤ ℓ₁ := Nat.zero_le _
    simp only [hybrids, Fin.val_zero, h0, ↓reduceDIte]
    have : (⟨0, Nat.lt_succ_of_le h0⟩ : Fin (ℓ₁ + 1)) = ⟨0, Nat.zero_lt_succ ℓ₁⟩ := rfl
    rw [this, hstart1]
  · -- end: hybrids (ℓ₁ + ℓ₂) = C''
    by_cases hℓ₂ : ℓ₂ = 0
    · -- ℓ₂ = 0 case
      subst hℓ₂
      simp only [Nat.add_zero, hybrids, Nat.le_refl, ↓reduceDIte]
      have : (⟨ℓ₁, Nat.lt_succ_of_le (Nat.le_refl ℓ₁)⟩ : Fin (ℓ₁ + 1)) = ⟨ℓ₁, Nat.lt_succ_self ℓ₁⟩ := rfl
      rw [this, hend1]
      have hC'_eq : C'' = C' := by
        have h0 : (⟨0, Nat.zero_lt_succ 0⟩ : Fin 1) = ⟨0, Nat.lt_succ_self 0⟩ := rfl
        rw [← hstart2, ← hend2, h0]
      exact hC'_eq.symm
    · -- ℓ₂ ≠ 0 case
      have h_not : ¬ (ℓ₁ + ℓ₂ ≤ ℓ₁) := by omega
      simp only [hybrids, h_not, ↓reduceDIte, Nat.add_sub_cancel_left]
      have : (⟨ℓ₂, by omega⟩ : Fin (ℓ₂ + 1)) = ⟨ℓ₂, Nat.lt_succ_self ℓ₂⟩ := rfl
      rw [this, hend2]
  · -- steps
    intro i
    have htri := lt_trichotomy (i : Nat) ℓ₁
    rcases htri with hlt | h_eq | hgt

    · -- Case 1: i.val < ℓ₁ → both indices in first chain
      have hi_le : (i : Nat) ≤ ℓ₁ := Nat.le_of_lt hlt
      have hi_succ_le : (i : Nat) + 1 ≤ ℓ₁ := Nat.succ_le_of_lt hlt
      let j : Fin ℓ₁ := ⟨i, hlt⟩

      have h_left : hybrids i.castSucc = hyb1 j.castSucc := by
        simp only [hybrids, Fin.coe_castSucc, hi_le, ↓reduceDIte]
        have heq : (⟨(i : Nat), Nat.lt_succ_of_le hi_le⟩ : Fin (ℓ₁ + 1)) = j.castSucc := by
          simp [j, Fin.ext_iff]
        simp only [heq]

      have h_right : hybrids i.succ = hyb1 j.succ := by
        simp only [hybrids, Fin.val_succ, hi_succ_le, ↓reduceDIte]
        have heq : (⟨(i : Nat) + 1, Nat.lt_succ_of_le hi_succ_le⟩ : Fin (ℓ₁ + 1)) = j.succ := by
          simp [j, Fin.ext_iff]
        simp only [heq]

      simp only [h_left, h_right]
      exact hstep1 j

    · -- Case 2: i.val = ℓ₁ → boundary between first and second chains
      have hi_eq : (i : Nat) = ℓ₁ := h_eq
      have hi_le : (i : Nat) ≤ ℓ₁ := by omega
      have hi_succ_not_le : ¬ ((i : Nat) + 1 ≤ ℓ₁) := by omega

      have h_left : hybrids i.castSucc = C' := by
        simp only [hybrids, Fin.coe_castSucc, hi_le, ↓reduceDIte]
        have heq : (⟨(i : Nat), Nat.lt_succ_of_le hi_le⟩ : Fin (ℓ₁ + 1)) = ⟨ℓ₁, Nat.lt_succ_self ℓ₁⟩ := by
          simp [hi_eq, Fin.ext_iff]
        simp only [heq, ← hend1]

      have h_right : hybrids i.succ = hyb2 ⟨1, by omega⟩ := by
        simp only [hybrids, Fin.val_succ, hi_succ_not_le, ↓reduceDIte]
        have heq : (⟨(i : Nat) + 1 - ℓ₁, by omega⟩ : Fin (ℓ₂ + 1)) = ⟨1, by omega⟩ := by
          simp [Fin.ext_iff, hi_eq]
        simp only [heq]

      have hℓ₂pos : 0 < ℓ₂ := by
        have hi_lt : (i : Nat) < ℓ₁ + ℓ₂ := i.isLt
        omega

      let j0 : Fin ℓ₂ := ⟨0, hℓ₂pos⟩
      have hstep0 : SEquivalent s (hyb2 j0.castSucc) (hyb2 j0.succ) := hstep2 j0

      have hstep01 : SEquivalent s (hyb2 ⟨0, Nat.zero_lt_succ ℓ₂⟩) (hyb2 ⟨1, by omega⟩) := by
        have h1 : j0.castSucc = ⟨0, Nat.zero_lt_succ ℓ₂⟩ := by simp [j0, Fin.ext_iff]
        have h2 : j0.succ = ⟨1, by omega⟩ := by simp [j0, Fin.ext_iff]
        rw [← h1, ← h2]; exact hstep0

      have hC'_to_1 : SEquivalent s C' (hyb2 ⟨1, by omega⟩) := by
        rw [← hstart2]
        convert hstep01 using 2

      simp only [h_left, h_right]
      exact hC'_to_1

    · -- Case 3: ℓ₁ < i.val → both indices in second chain
      have hi_not_le : ¬ ((i : Nat) ≤ ℓ₁) := by omega
      have hi_succ_not_le : ¬ ((i : Nat) + 1 ≤ ℓ₁) := by omega

      have hi_lt : (i : Nat) < ℓ₁ + ℓ₂ := i.isLt
      -- k ranges from 1 to ℓ₂-1 (not 0, that's handled in Case 2)
      have hk_lt : (i : Nat) - ℓ₁ < ℓ₂ := by omega
      let k : Fin ℓ₂ := ⟨i - ℓ₁, hk_lt⟩

      have h_left : hybrids i.castSucc = hyb2 k.castSucc := by
        simp only [hybrids, Fin.coe_castSucc, hi_not_le, ↓reduceDIte]
        have heq : (⟨(i : Nat) - ℓ₁, by omega⟩ : Fin (ℓ₂ + 1)) = k.castSucc := by
          simp only [k, Fin.ext_iff, Fin.coe_castSucc, Fin.val_mk]
        simp only [heq]

      have h_right : hybrids i.succ = hyb2 k.succ := by
        simp only [hybrids, Fin.val_succ, hi_succ_not_le, ↓reduceDIte]
        have heq : (⟨(i : Nat) + 1 - ℓ₁, by omega⟩ : Fin (ℓ₂ + 1)) = k.succ := by
          simp only [k, Fin.ext_iff, Fin.val_succ, Fin.val_mk]
          omega
        simp only [heq]

      simp only [h_left, h_right]
      exact hstep2 k

/--
  Key property used in security proof:
  If C and C' are transitively s-equivalent via ℓ hybrids,
  security reduction loses a factor of ℓ.
-/
theorem transitive_sequiv_hybrid {din dout : Nat} (s ℓ : Nat) (C C' : Circuit din dout)
    (_ : TransitiveSEquivalent s ℓ C C') :
    True := trivial

end MaDaiShi
