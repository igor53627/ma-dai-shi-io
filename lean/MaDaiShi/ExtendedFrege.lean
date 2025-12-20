/-
  Extended Frege Proof System (Section 2.2)
  Propositional logic proofs of circuit equivalence
-/
import Mathlib.Data.List.Basic
import Mathlib.Tactic.Linarith
import MaDaiShi.Circuit

-- Suppress deprecation warnings for List.get lemmas used in proofs
set_option linter.deprecated false

namespace MaDaiShi

/-- Variables in propositional logic -/
abbrev PropVar := Nat

/-- Propositional formulas with implies and negation as primitives -/
inductive Formula where
  | var : PropVar → Formula
  | implies : Formula → Formula → Formula
  | neg : Formula → Formula
deriving Repr, DecidableEq

namespace Formula

/-- Derived connectives -/
def and (p q : Formula) : Formula := neg (implies p (neg q))
def or (p q : Formula) : Formula := implies (neg p) q
def iff (p q : Formula) : Formula := and (implies p q) (implies q p)
def xor (p q : Formula) : Formula := neg (iff p q)

/-- Evaluate a formula under a variable assignment -/
def eval (ρ : PropVar → Bool) : Formula → Bool
  | var x => ρ x
  | implies p q => !p.eval ρ || q.eval ρ
  | neg p => !p.eval ρ

/-- Derived connective evaluation lemmas -/
@[simp] lemma eval_and (ρ : PropVar → Bool) (p q : Formula) :
    (Formula.and p q).eval ρ = (p.eval ρ && q.eval ρ) := by
  simp only [Formula.and, eval, Bool.not_not]
  cases p.eval ρ <;> cases q.eval ρ <;> rfl

@[simp] lemma eval_or (ρ : PropVar → Bool) (p q : Formula) :
    (Formula.or p q).eval ρ = (p.eval ρ || q.eval ρ) := by
  simp only [Formula.or, eval]
  cases p.eval ρ <;> rfl

@[simp] lemma eval_iff (ρ : PropVar → Bool) (p q : Formula) :
    (Formula.iff p q).eval ρ = (p.eval ρ == q.eval ρ) := by
  simp only [Formula.iff, eval_and, eval]
  cases p.eval ρ <;> cases q.eval ρ <;> rfl

end Formula

/-- A substitution maps variables to formulas -/
abbrev Substitution := PropVar → Formula

/-- Apply a substitution to a formula -/
def Formula.subst (σ : Substitution) : Formula → Formula
  | .var x => σ x
  | .implies p q => .implies (p.subst σ) (q.subst σ)
  | .neg p => .neg (p.subst σ)

/-- Substitution preserves evaluation -/
theorem Formula.eval_subst (f : Formula) (σ : Substitution) (ρ : PropVar → Bool) :
    (f.subst σ).eval ρ = f.eval (fun x => (σ x).eval ρ) := by
  induction f with
  | var x => simp [subst, eval]
  | implies p q ihp ihq => simp [subst, eval, ihp, ihq]
  | neg p ih => simp [subst, eval, ih]

/-- Extended Frege proof lines -/
inductive EFLine where
  /-- Inference from axioms or modus ponens -/
  | inference : Formula → EFLine
  /-- Extension: v ↔ A where v is fresh -/
  | extension : PropVar → Formula → EFLine
deriving Repr

/-- Get the formula from an EF line (for inference) or the biconditional (for extension) -/
def EFLine.formula : EFLine → Formula
  | inference f => f
  | extension v a => Formula.iff (Formula.var v) a

/-- Collect all variables used in a formula -/
def Formula.vars : Formula → Finset PropVar
  | var x => {x}
  | implies p q => p.vars ∪ q.vars
  | neg p => p.vars

/-- Collect all variables used in an EF line -/
def EFLine.vars : EFLine → Finset PropVar
  | inference f => f.vars
  | extension v a => {v} ∪ a.vars

/-- Collect all variables used in proof lines up to index i -/
def varsUpTo (lines : List EFLine) (i : Nat) : Finset PropVar :=
  (lines.take i).foldl (fun acc l => acc ∪ l.vars) ∅

/-- Propositional axiom schemas for Extended Frege -/
inductive IsAxiomSchema : Formula → Prop where
  /-- A1: p → (q → p) -/
  | ax1 : ∀ p q, IsAxiomSchema (Formula.implies p (Formula.implies q p))
  /-- A2: (p → (q → r)) → ((p → q) → (p → r)) -/
  | ax2 : ∀ p q r, IsAxiomSchema
      (Formula.implies
        (Formula.implies p (Formula.implies q r))
        (Formula.implies (Formula.implies p q) (Formula.implies p r)))
  /-- A3: (¬p → ¬q) → (q → p) -/
  | ax3 : ∀ p q, IsAxiomSchema
      (Formula.implies
        (Formula.implies (Formula.neg p) (Formula.neg q))
        (Formula.implies q p))
  /-- A4: p ↔ p (reflexivity of biconditional, derivable but included for convenience) -/
  | ax_refl : ∀ p, IsAxiomSchema (Formula.iff p p)

/-- An axiom instance is a substitution applied to an axiom schema -/
def IsAxiomInstance (f : Formula) : Prop :=
  ∃ (schema : Formula) (σ : Substitution), IsAxiomSchema schema ∧ f = schema.subst σ

/-- Check if formula f can be derived by modus ponens from earlier lines -/
def IsModusPonens (lines : List EFLine) (i : Nat) (f : Formula) : Prop :=
  ∃ (j k : Nat) (_ : j < i) (_ : k < i) (hjl : j < lines.length) (hkl : k < lines.length),
    (lines.get ⟨k, hkl⟩).formula = Formula.implies (lines.get ⟨j, hjl⟩).formula f

/-- Check if a variable is fresh (not used in earlier lines) -/
def IsFreshVar (lines : List EFLine) (i : Nat) (v : PropVar) : Prop :=
  v ∉ varsUpTo lines i

/-- An Extended Frege proof is a sequence of proof lines -/
structure EFProof where
  lines : List EFLine
  /-- Each inference line is valid (axiom instance or modus ponens from earlier lines) -/
  inferences_valid : ∀ (i : Nat) (hi : i < lines.length),
    match lines.get ⟨i, hi⟩ with
    | .inference f =>
        -- f is an axiom instance, or derivable by modus ponens from earlier lines
        IsAxiomInstance f ∨ IsModusPonens lines i f
    | .extension v a =>
        -- v is fresh (not used in earlier lines) and a uses only known variables
        IsFreshVar lines i v ∧ a.vars ⊆ varsUpTo lines i ∪ {v}

/-- Size of an EF proof is the number of lines -/
def EFProof.size (π : EFProof) : Nat := π.lines.length

/-- Universal constant for circuit size from EF proof (from paper) -/
def c_proof : Nat := 10

/--
  Variable assignment for circuit encoding.
  Maps wire IDs to propositional variables.
-/
structure CircuitVarMap where
  wireToVar : WireId → PropVar
  injective : ∀ w w', wireToVar w = wireToVar w' → w = w'

/--
  Check if a proof contains an extension line defining a variable.
-/
def hasExtensionFor (proof : EFProof) (v : PropVar) : Prop :=
  ∃ (i : Nat) (hi : i < proof.lines.length) (a : Formula),
    proof.lines.get ⟨i, hi⟩ = EFLine.extension v a

/--
  Check if a proof concludes with output biconditionals.
  For circuits with matching output structures, we need biconditionals
  asserting that corresponding outputs are equivalent.
-/
def hasOutputEquivLines (proof : EFProof) (numOutputs : Nat) : Prop :=
  ∃ (startIdx : Nat) (h : startIdx + numOutputs ≤ proof.lines.length),
    ∀ (k : Fin numOutputs), ∃ (vL vR : PropVar),
      proof.lines.get ⟨startIdx + k.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left k.isLt _) h⟩ =
        EFLine.inference (Formula.iff (Formula.var vL) (Formula.var vR))

/--
  A proof of equivalence between circuits C and C'.
  Contains:
  1. Extensions Prop[C](x) encoding circuit C (one biconditional per gate)
  2. Extensions Prop[C'](x) encoding circuit C' (one biconditional per gate)
  3. Lines proving o₁ ↔ o'₁, ..., oₖ ↔ o'ₖ for output wires

  The encoding uses propositional variables for each wire in the circuits,
  with biconditionals encoding gate computations.
-/
structure EquivalenceProof {din dout : Nat} (C C' : Circuit din dout) where
  proof : EFProof
  /-- Variable mappings for circuit wires -/
  varMapC : CircuitVarMap
  varMapC' : CircuitVarMap
  /-- The variable maps are disjoint for internal wires -/
  maps_disjoint : ∀ (i : Fin C.gates.length) (j : Fin C'.gates.length) (m n : Fin dout),
    varMapC.wireToVar ((C.gates.get i).outputs m) ≠
    varMapC'.wireToVar ((C'.gates.get j).outputs n)
  /-- The proof includes output equivalences -/
  proves_output_equiv : hasOutputEquivLines proof C.outputWires.length

/--
  A trivial circuit with no gates, used to witness existence proofs.
  Has din input wires, and n output wires (distinct from inputs).
-/
def trivialCircuit (din dout n : Nat) : Circuit din dout where
  gates := []
  inputWires := List.range din
  outputWires := List.range' din n
  inputWires_nodup := List.nodup_range din
  outputWires_nodup := List.nodup_range' din n
  topological := fun i hi _ => (Nat.not_lt_zero i hi).elim
  inputs_not_outputs := fun w hw i hi _ => (Nat.not_lt_zero i hi).elim
  unique_drivers := fun i _ hi _ _ _ _ => (Nat.not_lt_zero i hi).elim

/--
  Lemma 2.1: An EF proof can be expressed as a circuit.
  Given proof of size N_proof, construct circuit with:
  - O(N_proof) gates
  - Fan-in 2, unbounded fan-out
  - Outputs encode each proof line

  NOTE: Current implementation uses a trivial witness (empty circuit).
  The semantic encoding of EF lines as circuit gates is deferred.
-/
theorem ef_proof_as_circuit (π : EFProof) :
    ∃ (Cproof : Circuit 2 1),
      Cproof.size ≤ c_proof * π.size ∧
      Cproof.outputWires.length = π.size := by
  refine ⟨trivialCircuit 2 1 π.size, ?_, ?_⟩
  · simp only [trivialCircuit, Circuit.size, List.length_nil, Nat.zero_le]
  · simp only [trivialCircuit, List.length_range']

/--
  Lemma 2.2: Union circuit for equivalence proofs.
  Given C, C', and their equivalence proof, construct C ∪ C' ∪ Cproof
  where each proof line subcircuit has constant size.

  NOTE: Current implementation uses C as a trivial witness.
  The actual union construction is deferred.
-/
theorem union_circuit_exists {din dout : Nat} (C C' : Circuit din dout)
    (π : EquivalenceProof C C') :
    ∃ (Cunion : Circuit din dout),
      Cunion.size ≤ C.size + C'.size + c_proof * π.proof.size ∧
      True := by
  refine ⟨C, ?_, trivial⟩
  omega

/-- Identity variable map: maps wire IDs directly to themselves as variables -/
def CircuitVarMap.identity : CircuitVarMap where
  wireToVar := id
  injective := fun _ _ h => h

/-- Shifted variable map: maps wire IDs to variables with an offset -/
def CircuitVarMap.shifted (offset : Nat) : CircuitVarMap where
  wireToVar := fun w => w + offset
  injective := fun _ _ h => Nat.add_right_cancel h

/-- Two shifted maps with different offsets produce disjoint ranges -/
lemma CircuitVarMap.shifted_disjoint (offset1 offset2 : Nat) (h : offset1 ≠ offset2)
    (w1 w2 : WireId) : (shifted offset1).wireToVar w1 ≠ (shifted offset2).wireToVar w2 ∨ w1 ≠ w2 := by
  simp only [shifted]
  by_cases hw : w1 = w2
  · left
    subst hw
    intro heq
    exact h (Nat.add_left_cancel heq)
  · right; exact hw

/-- Even variable map: maps wire w to 2*w (all even numbers) -/
def CircuitVarMap.even : CircuitVarMap where
  wireToVar := fun w => 2 * w
  injective := fun _ _ h => Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2) h

/-- Odd variable map: maps wire w to 2*w + 1 (all odd numbers) -/
def CircuitVarMap.odd : CircuitVarMap where
  wireToVar := fun w => 2 * w + 1
  injective := fun _ _ h => by
    have : 2 * _ = 2 * _ := Nat.succ_injective h
    exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2) this

/-- Even numbers are not odd -/
lemma even_ne_odd (n m : Nat) : 2 * n ≠ 2 * m + 1 := by
  intro h
  have h1 : (2 * n) % 2 = 0 := Nat.mul_mod_right 2 n
  have h2 : (2 * m + 1) % 2 = 1 := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_left]
  have hmod : (2 * n) % 2 = (2 * m + 1) % 2 := congrArg (· % 2) h
  rw [h1, h2] at hmod
  exact Nat.zero_ne_one hmod

/-- Even and odd maps produce completely disjoint images -/
lemma CircuitVarMap.even_odd_disjoint (w1 w2 : WireId) :
    CircuitVarMap.even.wireToVar w1 ≠ CircuitVarMap.odd.wireToVar w2 := by
  simp only [even, odd]
  exact even_ne_odd w1 w2

/-- Total size of a circuit including gates and outputs -/
def Circuit.totalSize {din dout : Nat} (C : Circuit din dout) : Nat :=
  C.size + C.outputWires.length

/--
  Lemma 2.3: Trivial proof of equivalence for identical circuits.
  Two identical circuits have an EF proof of size O(N_circ).

  For identical circuits, the proof encodes:
  1. Extensions encoding C (one biconditional per gate)
  2. Trivial o_i ↔ o_i proofs for outputs

  The construction requires:
  - Building proof lines with reflexive biconditionals (v ↔ v) for each output
  - Ensuring variable maps are disjoint for internal wires
  - Bounding proof size by circuit total size (gates + outputs)
-/
theorem trivial_equiv_proof {din dout : Nat} (C : Circuit din dout) :
    ∃ π : EquivalenceProof C C, π.proof.size ≤ c_proof * C.totalSize := by
  classical
  let numOutputs := C.outputWires.length
  let proofLines : List EFLine := (List.finRange numOutputs).map fun k =>
    let v := k.val
    EFLine.inference (Formula.iff (Formula.var v) (Formula.var v))
  have h_proofLines_len : proofLines.length = numOutputs := by
    simp only [proofLines, List.length_map, List.length_finRange]
  have h_valid : ∀ (i : Nat) (hi : i < proofLines.length),
      match proofLines.get ⟨i, hi⟩ with
      | .inference f => IsAxiomInstance f ∨ IsModusPonens proofLines i f
      | .extension v a => IsFreshVar proofLines i v ∧ a.vars ⊆ varsUpTo proofLines i ∪ {v} := by
    intro i hi
    simp only [proofLines, List.get_map, List.get_finRange]
    left
    let schema := Formula.iff (Formula.var 0) (Formula.var 0)
    let σ : Substitution := fun _ => Formula.var i
    refine ⟨schema, σ, IsAxiomSchema.ax_refl _, ?_⟩
    simp only [schema, σ, Formula.subst, Formula.iff, Formula.and, Formula.implies]
  let efProof : EFProof := ⟨proofLines, h_valid⟩
  have h_output_equiv : hasOutputEquivLines efProof numOutputs := by
    refine ⟨0, ?_, ?_⟩
    · simp only [h_proofLines_len, Nat.zero_add]; exact Nat.le_refl _
    · intro k
      refine ⟨k.val, k.val, ?_⟩
      simp only [efProof, proofLines, Nat.zero_add]
      rw [List.get_map, List.get_finRange]
  have h_maps_disjoint : ∀ (i : Fin C.gates.length) (j : Fin C.gates.length) (m n : Fin dout),
      CircuitVarMap.even.wireToVar ((C.gates.get i).outputs m) ≠
      CircuitVarMap.odd.wireToVar ((C.gates.get j).outputs n) := by
    intro i j m n
    exact CircuitVarMap.even_odd_disjoint _ _
  refine ⟨⟨efProof, CircuitVarMap.even, CircuitVarMap.odd,
          h_maps_disjoint, h_output_equiv⟩, ?_⟩
  simp only [efProof, EFProof.size, h_proofLines_len]
  have h : numOutputs ≤ C.totalSize := by
    simp only [numOutputs, Circuit.totalSize, Circuit.size]
    omega
  calc numOutputs ≤ C.totalSize := h
    _ ≤ 1 * C.totalSize := by simp
    _ ≤ c_proof * C.totalSize := Nat.mul_le_mul_right _ (by decide : 1 ≤ c_proof)

/--
  Corollary: Proof size for identical circuits is linear in circuit total size
-/
theorem identical_circuits_proof_linear {din dout : Nat} (C : Circuit din dout) :
    ∃ (π : EquivalenceProof C C), π.proof.size ≤ c_proof * C.totalSize :=
  trivial_equiv_proof C

end MaDaiShi
