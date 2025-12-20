/-
  Security Reduction (Theorem 1)
  From Local iO to Full iO via Padding
-/
import MaDaiShi.Circuit
import MaDaiShi.SEquivalence
import MaDaiShi.ExtendedFrege
import MaDaiShi.Padding
import MaDaiShi.LocalIO

namespace MaDaiShi

/-
  Theorem 1 (Main Theorem - Informal Statement):
  
  If there exists a local iO with s = O(log N) that is secure against
  sub-exponential adversaries, then there exists a full iO that is
  secure against polynomial-time adversaries.
  
  The construction: iO(C) = LiO(Pad(C, N_circ, N_proof))
  
  Security reduction:
  - For functionally equivalent C₁, C₂ with EF proof π
  - Pad(C₁) and Pad(C₂) are transitively O(log N)-equivalent via poly(N) hybrids
  - Each step is s-indistinguishable by LiO security
  - Hybrid argument gives full indistinguishability with poly(N) security loss
-/

/-- The composed obfuscator: first pad, then apply local iO. -/
noncomputable def ComposedIO {din dout : Nat} 
    (lio : LocalIO din dout) 
    (Ncirc Nproof : Nat) 
    (C : Circuit din dout) 
    (h : C.size ≤ Ncirc) : ObfuscatedProgram :=
  lio.obfuscate (Pad C Ncirc Nproof h)

/--
  Key lemma: SEquivalent s implies SEquivalent s' for s ≤ s'.
  Monotonicity of s-equivalence in the locality parameter.
-/
theorem SEquivalent.mono {din dout : Nat} {s s' : Nat} {C C' : Circuit din dout}
    (h : SEquivalent s C C') (hss : s ≤ s') :
    SEquivalent s' C C' := by
  obtain ⟨topo, S, hsize, hops, hfe⟩ := h
  exact ⟨topo, S, Nat.le_trans hsize hss, hops, hfe⟩

/--
  Lemma: s-indistinguishability extends along hybrid chain.
  
  If LiO is s-indistinguishable and C₁, ..., Cₗ is a chain where
  each consecutive pair is s-equivalent, then LiO(C₁) and LiO(Cₗ)
  are indistinguishable (with security loss factor ℓ).
  
  This proof uses the relational `HybridIndistinguishable` machinery:
  1. Build a chain of obfuscated programs from the hybrid circuits
  2. Use `hybrid_chain_from_seq` to get `HybridIndistinguishable`
  3. Apply `HybridIndistinguishable.toIndistinguishable` to get `Indistinguishable`
-/
theorem hybrid_chain_indist {din dout : Nat}
    (lio : LocalIO din dout)
    (s ℓ : Nat)
    (C C' : Circuit din dout)
    (htrans : TransitiveSEquivalent s ℓ C C')
    (hs : s ≤ lio.s) :
    Indistinguishable (lio.obfuscate C) (lio.obfuscate C') := by
  obtain ⟨hybrids, hstart, hend, hstep⟩ := htrans
  -- Build the sequence of obfuscated programs
  let P : Fin (ℓ + 1) → ObfuscatedProgram := fun i => lio.obfuscate (hybrids i)
  -- Each step is s-equivalent, so by LiO's s_indist, each step is indistinguishable
  have h_each_step : ∀ (i : Fin ℓ), SEquivalent lio.s (hybrids i.castSucc) (hybrids i.succ) := by
    intro i
    exact SEquivalent.mono (hstep i) hs
  have h_each_indist : ∀ (i : Fin ℓ), Indistinguishable (P i.castSucc) (P i.succ) := by
    intro i
    exact lio.s_indist _ _ (h_each_step i)
  -- Use the hybrid chain lemma to get HybridIndistinguishable
  have h_hybrid : HybridIndistinguishable (P ⟨0, Nat.zero_lt_succ ℓ⟩) (P ⟨ℓ, Nat.lt_succ_self ℓ⟩) :=
    hybrid_chain_from_seq P h_each_indist
  -- Convert back to Indistinguishable
  have h_indist := HybridIndistinguishable.toIndistinguishable h_hybrid
  -- Substitute start and end
  simp only [P] at h_indist
  rw [hstart, hend] at h_indist
  exact h_indist

/--
  Corollary: TransitiveSEquivalent s implies TransitiveSEquivalent s' for s ≤ s'.
-/
theorem TransitiveSEquivalent.mono {din dout : Nat} {s s' ℓ : Nat} {C C' : Circuit din dout}
    (h : TransitiveSEquivalent s ℓ C C') (hss : s ≤ s') :
    TransitiveSEquivalent s' ℓ C C' := by
  obtain ⟨hybrids, hstart, hend, hstep⟩ := h
  exact ⟨hybrids, hstart, hend, fun i => SEquivalent.mono (hstep i) hss⟩

/--
  Theorem 1 (Formal Statement):
  
  Given:
  - A local iO with locality parameter s = O(log(N_circ + N_proof))
  - Two circuits C₁, C₂ of size ≤ N_circ
  - An EF proof π of size ≤ N_proof showing C₁ ≡ C₂
  
  Then:
  - Pad(C₁) and Pad(C₂) are transitively s-equivalent
  - LiO(Pad(C₁)) and LiO(Pad(C₂)) are computationally indistinguishable
  
  This gives us full iO from local iO + padding.
-/
theorem main_theorem {din dout : Nat}
    (lio : LocalIO din dout)
    (C₁ C₂ : Circuit din dout)
    (Ncirc Nproof : Nat)
    (hC₁ : C₁.size ≤ Ncirc)
    (hC₂ : C₂.size ≤ Ncirc)
    (π : EquivalenceProof C₁ C₂)
    (hπ : π.proof.size ≤ Nproof)
    (hlio : lio.s = O_log (Ncirc + Nproof)) :
    Indistinguishable 
      (lio.obfuscate (Pad C₁ Ncirc Nproof hC₁)) 
      (lio.obfuscate (Pad C₂ Ncirc Nproof hC₂)) := by
  obtain ⟨s, ℓ, hs_eq, _, htrans⟩ := pad_transitive_sequiv C₁ C₂ Ncirc Nproof hC₁ hC₂ π hπ
  have hs_le : s ≤ lio.s := by rw [hlio, hs_eq]
  exact hybrid_chain_indist lio s ℓ _ _ htrans hs_le

/--
  Corollary: The composed obfuscator is a full iO.
  
  For any two functionally equivalent circuits with an EF proof,
  the composed obfuscator produces indistinguishable outputs.
-/
theorem composed_io_is_full_io {din dout : Nat}
    (lio : LocalIO din dout)
    (Ncirc Nproof : Nat)
    (hlio : lio.s = O_log (Ncirc + Nproof)) :
    ∀ C₁ C₂ : Circuit din dout,
    ∀ (hC₁ : C₁.size ≤ Ncirc) (hC₂ : C₂.size ≤ Ncirc),
    ∀ π : EquivalenceProof C₁ C₂,
    π.proof.size ≤ Nproof →
    Indistinguishable 
      (ComposedIO lio Ncirc Nproof C₁ hC₁) 
      (ComposedIO lio Ncirc Nproof C₂ hC₂) := by
  intro C₁ C₂ hC₁ hC₂ π hπ
  exact main_theorem lio C₁ C₂ Ncirc Nproof hC₁ hC₂ π hπ hlio

/--
  Security loss analysis:
  - Local iO has advantage ε against s-distinguishers
  - Hybrid chain has ℓ = poly(N) steps
  - Full iO advantage ≤ ℓ * ε = poly(N) * ε
  
  For sub-exponential security (ε = 2^{-N^c}), this gives:
  - Full advantage ≤ poly(N) * 2^{-N^c} = negl(N)
-/
theorem security_loss_polynomial {din dout : Nat}
    (Ncirc Nproof : Nat)
    (C₁ C₂ : Circuit din dout)
    (hC₁ : C₁.size ≤ Ncirc)
    (hC₂ : C₂.size ≤ Ncirc)
    (π : EquivalenceProof C₁ C₂)
    (hπ : π.proof.size ≤ Nproof) :
    ∃ ℓ : Nat, ℓ ≤ poly (Ncirc + Nproof) ∧
    ∃ s : Nat, s = O_log (Ncirc + Nproof) ∧
    TransitiveSEquivalent s ℓ (Pad C₁ Ncirc Nproof hC₁) (Pad C₂ Ncirc Nproof hC₂) := by
  obtain ⟨s, ℓ, hs, hℓ, htrans⟩ := pad_transitive_sequiv C₁ C₂ Ncirc Nproof hC₁ hC₂ π hπ
  exact ⟨ℓ, hℓ, s, hs, htrans⟩

/--
  The key insight: logarithmic locality enables polynomial security loss,
  which is acceptable when starting from sub-exponential security.
-/
theorem log_locality_enables_polynomial_reduction (N : Nat) :
    O_log N = Nat.log2 N + 1 := rfl

end MaDaiShi
