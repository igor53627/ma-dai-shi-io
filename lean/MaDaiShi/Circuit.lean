/-
  Circuit Definitions (Section 2.1)
  Circuits as directed acyclic graphs with gates and wires
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.Basic

namespace MaDaiShi

/-- A wire identifier in a circuit -/
abbrev WireId := Nat

/-- A gate identifier in a circuit -/
abbrev GateId := Nat

/-- Gate operation: maps input wire values to output wire values -/
structure GateOp (fanIn fanOut : Nat) where
  eval : (Fin fanIn → Bool) → (Fin fanOut → Bool)

/-- A gate in a circuit with bounded fan-in and fan-out -/
structure Gate (fanIn fanOut : Nat) where
  id : GateId
  inputs : Fin fanIn → WireId
  outputs : Fin fanOut → WireId
  op : GateOp fanIn fanOut

/-- Wire valuation: assigns boolean values to wires -/
abbrev WireValuation := WireId → Bool

/--
  A circuit with bounded fan-in din and fan-out dout.
  Gates are stored in topological order: gate i can only read from
  primary inputs or outputs of gates j < i.
-/
structure Circuit (din dout : Nat) where
  gates : List (Gate din dout)
  inputWires : List WireId
  outputWires : List WireId
  /-- All input wire IDs are distinct -/
  inputWires_nodup : inputWires.Nodup
  /-- All output wire IDs are distinct -/
  outputWires_nodup : outputWires.Nodup
  /-- Topological ordering: each gate's inputs come from primary inputs or earlier gate outputs -/
  topological : ∀ (i : Nat) (hi : i < gates.length) (k : Fin din),
    let w := (gates.get ⟨i, hi⟩).inputs k
    w ∈ inputWires ∨ ∃ (j : Nat) (hj : j < i) (m : Fin dout),
      (gates.get ⟨j, Nat.lt_trans hj hi⟩).outputs m = w

/-- Size of a circuit is the number of gates -/
def Circuit.size {din dout : Nat} (C : Circuit din dout) : Nat := C.gates.length

/-- Evaluate a single gate given current wire valuation -/
def Gate.evalWith {din dout : Nat} (g : Gate din dout) (σ : WireValuation) : Fin dout → Bool :=
  g.op.eval (fun k => σ (g.inputs k))

/-- Update wire valuation with a gate's outputs -/
def updateValuation {din dout : Nat} (σ : WireValuation) (g : Gate din dout) : WireValuation :=
  fun w =>
    match (List.finRange dout).find? (fun k => g.outputs k == w) with
    | some k => g.evalWith σ k
    | none => σ w

/-- Evaluate all gates in order, threading wire valuation -/
def evalGates {din dout : Nat} (gates : List (Gate din dout)) (σ : WireValuation) : WireValuation :=
  gates.foldl (fun σ' g => updateValuation σ' g) σ

/-- Initialize wire valuation from primary inputs -/
def initValuation {din dout : Nat} (C : Circuit din dout) (x : Fin C.inputWires.length → Bool) : WireValuation :=
  fun w =>
    match C.inputWires.indexOf? w with
    | some idx =>
        if h : idx < C.inputWires.length then x ⟨idx, h⟩ else false
    | none => false

/-- Evaluate a circuit: map input values to output values -/
def Circuit.eval {din dout : Nat} (C : Circuit din dout)
    (x : Fin C.inputWires.length → Bool) : Fin C.outputWires.length → Bool :=
  fun k =>
    let σ₀ := initValuation C x
    let σ := evalGates C.gates σ₀
    σ (C.outputWires.get k)

/-- Two circuits are topologically equivalent if their graph structures are identical -/
structure TopologicallyEquivalent {din dout : Nat} (C C' : Circuit din dout) : Prop where
  len_eq : C.gates.length = C'.gates.length
  inputs_eq : C.inputWires = C'.inputWires
  outputs_eq : C.outputWires = C'.outputWires
  gates_match : ∀ (i : Nat) (hi : i < C.gates.length),
    let g := C.gates.get ⟨i, hi⟩
    let g' := C'.gates.get ⟨i, len_eq ▸ hi⟩
    g.id = g'.id ∧ g.inputs = g'.inputs ∧ g.outputs = g'.outputs

/--
  Functional equivalence: two circuits compute the same function.
  Explicit about input/output length equality and proper casting.
-/
def FunctionallyEquivalent {din dout : Nat} (C C' : Circuit din dout)
    (h_inp : C.inputWires.length = C'.inputWires.length)
    (h_out : C.outputWires.length = C'.outputWires.length) : Prop :=
  ∀ (x : Fin C.inputWires.length → Bool),
    let x' : Fin C'.inputWires.length → Bool := fun i => x (Fin.cast h_inp.symm i)
    let y  : Fin C.outputWires.length → Bool := C.eval x
    let y' : Fin C.outputWires.length → Bool := fun k => C'.eval x' (Fin.cast h_out k)
    y = y'

/-- Simplified functional equivalence for circuits with identical wire structure -/
def FunctionallyEquivalent' {din dout : Nat} (C C' : Circuit din dout)
    (h_inp : C.inputWires = C'.inputWires)
    (h_out : C.outputWires = C'.outputWires) : Prop :=
  ∀ (x : Fin C.inputWires.length → Bool),
    let len_inp_eq := congrArg List.length h_inp
    let len_out_eq := congrArg List.length h_out
    let x' : Fin C'.inputWires.length → Bool := fun i => x (Fin.cast len_inp_eq.symm i)
    let y  : Fin C.outputWires.length → Bool := C.eval x
    let y' : Fin C.outputWires.length → Bool := fun k => C'.eval x' (Fin.cast len_out_eq k)
    y = y'

/-- A subcircuit is a subset of gates from the original circuit -/
structure Subcircuit {din dout : Nat} (C : Circuit din dout) where
  gateIndices : Finset (Fin C.gates.length)

/-- Size of a subcircuit -/
def Subcircuit.size {din dout : Nat} {C : Circuit din dout} (S : Subcircuit C) : Nat :=
  S.gateIndices.card

/-- Collect all input wires of gates in a subcircuit -/
def Subcircuit.allInputWires {din dout : Nat} {C : Circuit din dout} (S : Subcircuit C) : Finset WireId :=
  S.gateIndices.biUnion fun i =>
    Finset.image (fun k => (C.gates.get i).inputs k) Finset.univ

/-- Collect all output wires of gates in a subcircuit -/
def Subcircuit.allOutputWires {din dout : Nat} {C : Circuit din dout} (S : Subcircuit C) : Finset WireId :=
  S.gateIndices.biUnion fun i =>
    Finset.image (fun k => (C.gates.get i).outputs k) Finset.univ

/-- Input wires of a subcircuit S: wires that enter S from outside -/
def Subcircuit.inp {din dout : Nat} {C : Circuit din dout} (S : Subcircuit C) : Finset WireId :=
  S.allInputWires \ S.allOutputWires

/-- Output wires of a subcircuit S: wires that leave S to outside -/
def Subcircuit.out {din dout : Nat} {C : Circuit din dout} (S : Subcircuit C) : Finset WireId :=
  S.allOutputWires \ S.allInputWires

/-- Extract gates from subcircuit indices (preserving topological order) -/
def Subcircuit.extractGates {din dout : Nat} {C : Circuit din dout} (S : Subcircuit C) : List (Gate din dout) :=
  (List.finRange C.gates.length).filterMap fun i =>
    if i ∈ S.gateIndices then some (C.gates.get i) else none

/-- Membership lemma for extractGates -/
lemma Subcircuit.mem_extractGates {din dout : Nat} {C : Circuit din dout} {S : Subcircuit C}
    {g : Gate din dout} (hg : g ∈ S.extractGates) :
    ∃ i : Fin C.gates.length, i ∈ S.gateIndices ∧ g = C.gates.get i := by
  simp only [extractGates, List.mem_filterMap] at hg
  obtain ⟨i, _, hi⟩ := hg
  split at hi <;> simp_all

/-- The induced circuit on subcircuit S -/
def Circuit.induced {din dout : Nat} (C : Circuit din dout) (S : Subcircuit C) : Circuit din dout where
  gates := S.extractGates
  inputWires := S.inp.toList
  outputWires := S.out.toList
  inputWires_nodup := Finset.nodup_toList _
  outputWires_nodup := Finset.nodup_toList _
  topological := by
    intro i hi k
    -- Each gate in extractGates came from some original gate in S
    -- Its inputs are either in S.inp (external) or outputs of earlier gates in S
    sorry

/-- Reflexivity of functional equivalence -/
theorem FunctionallyEquivalent'.refl {din dout : Nat} (C : Circuit din dout) :
    FunctionallyEquivalent' C C rfl rfl := by
  intro x
  simp only [Fin.cast_refl, id_eq]

/-- Symmetry of functional equivalence -/
theorem FunctionallyEquivalent'.symm {din dout : Nat} {C C' : Circuit din dout}
    {h_inp : C.inputWires = C'.inputWires} {h_out : C.outputWires = C'.outputWires}
    (h : FunctionallyEquivalent' C C' h_inp h_out) :
    FunctionallyEquivalent' C' C h_inp.symm h_out.symm := by
  intro x
  have len_inp_eq : C.inputWires.length = C'.inputWires.length := congrArg List.length h_inp
  have len_out_eq : C.outputWires.length = C'.outputWires.length := congrArg List.length h_out
  have hx := h (fun i => x (Fin.cast len_inp_eq i))
  simp only [FunctionallyEquivalent'] at hx ⊢
  funext k
  have := congrFun hx (Fin.cast len_out_eq.symm k)
  simp only [Fin.cast_trans, Fin.cast_refl] at this ⊢
  sorry

/-- Transitivity of functional equivalence -/
theorem FunctionallyEquivalent'.trans {din dout : Nat} {C C' C'' : Circuit din dout}
    {h_inp : C.inputWires = C'.inputWires} {h_out : C.outputWires = C'.outputWires}
    {h_inp' : C'.inputWires = C''.inputWires} {h_out' : C'.outputWires = C''.outputWires}
    (h1 : FunctionallyEquivalent' C C' h_inp h_out)
    (h2 : FunctionallyEquivalent' C' C'' h_inp' h_out') :
    FunctionallyEquivalent' C C'' (h_inp.trans h_inp') (h_out.trans h_out') := by
  intro x
  have len_inp_eq := congrArg List.length h_inp
  have len_inp_eq' := congrArg List.length h_inp'
  have len_out_eq := congrArg List.length h_out
  have len_out_eq' := congrArg List.length h_out'
  have eq1 := h1 x
  have eq2 := h2 (fun i => x (Fin.cast len_inp_eq.symm i))
  simp only [FunctionallyEquivalent'] at eq1 eq2 ⊢
  funext k
  sorry

/-- Topologically equivalent circuits with same gate operations are functionally equivalent -/
theorem TopologicallyEquivalent.functionallyEquivalent {din dout : Nat} {C C' : Circuit din dout}
    (htopo : TopologicallyEquivalent C C')
    (hops : ∀ (i : Nat) (hi : i < C.gates.length),
      (C.gates.get ⟨i, hi⟩).op = (C'.gates.get ⟨i, htopo.len_eq ▸ hi⟩).op) :
    FunctionallyEquivalent' C C' htopo.inputs_eq htopo.outputs_eq := by
  intro x
  simp only [FunctionallyEquivalent']
  sorry

end MaDaiShi
