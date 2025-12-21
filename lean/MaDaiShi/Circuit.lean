/-
  Circuit Definitions (Section 2.1)
  Circuits as directed acyclic graphs with gates and wires
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Data.Matrix.Notation

namespace MaDaiShi

/-- A wire identifier in a circuit -/
abbrev WireId := Nat

/-- A gate identifier in a circuit -/
abbrev GateId := Nat

/-- Gate operation: maps input wire values to output wire values -/
structure GateOp (fanIn fanOut : Nat) where
  eval : (Fin fanIn → Bool) → (Fin fanOut → Bool)

namespace GateOp

/-- AND gate: 2 inputs, 1 output -/
def and : GateOp 2 1 where
  eval := fun inputs => fun _ => inputs 0 && inputs 1

/-- OR gate: 2 inputs, 1 output -/
def or : GateOp 2 1 where
  eval := fun inputs => fun _ => inputs 0 || inputs 1

/-- NOT gate: 1 input, 1 output -/
def not : GateOp 1 1 where
  eval := fun inputs => fun _ => !inputs 0

/-- XOR gate: 2 inputs, 1 output -/
def xor : GateOp 2 1 where
  eval := fun inputs => fun _ => inputs 0 ^^ inputs 1

/-- NAND gate: 2 inputs, 1 output (universal gate) -/
def nand : GateOp 2 1 where
  eval := fun inputs => fun _ => !(inputs 0 && inputs 1)

/-- NOR gate: 2 inputs, 1 output -/
def nor : GateOp 2 1 where
  eval := fun inputs => fun _ => !(inputs 0 || inputs 1)

/-- Identity gate: passes input through unchanged -/
def id : GateOp 1 1 where
  eval := fun inputs => fun _ => inputs 0

/-- Constant 0 gate: no inputs, outputs false -/
def const0 : GateOp 0 1 where
  eval := fun _ => fun _ => false

/-- Constant 1 gate: no inputs, outputs true -/
def const1 : GateOp 0 1 where
  eval := fun _ => fun _ => true

/-- Selector/MUX gate: 3 inputs (sel, a, b), outputs a if sel=false, b if sel=true -/
def mux : GateOp 3 1 where
  eval := fun inputs => fun _ => if inputs 0 then inputs 2 else inputs 1

/-- Evaluation lemmas for gate operations -/
@[simp] lemma and_eval (x y : Bool) :
    (GateOp.and.eval ![x, y]) 0 = (x && y) := rfl

@[simp] lemma or_eval (x y : Bool) :
    (GateOp.or.eval ![x, y]) 0 = (x || y) := rfl

@[simp] lemma not_eval (x : Bool) :
    (GateOp.not.eval ![x]) 0 = !x := rfl

@[simp] lemma xor_eval (x y : Bool) :
    (GateOp.xor.eval ![x, y]) 0 = (x ^^ y) := rfl

@[simp] lemma nand_eval (x y : Bool) :
    (GateOp.nand.eval ![x, y]) 0 = !(x && y) := rfl

@[simp] lemma id_eval (x : Bool) :
    (GateOp.id.eval ![x]) 0 = x := rfl

end GateOp

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
  /-- Primary inputs are never produced by any gate -/
  inputs_not_outputs : ∀ w ∈ inputWires, ∀ (i : Nat) (hi : i < gates.length) (m : Fin dout),
    (gates.get ⟨i, hi⟩).outputs m ≠ w
  /-- Each wire is produced by at most one gate (unique drivers) -/
  unique_drivers : ∀ (i j : Nat) (hi : i < gates.length) (hj : j < gates.length)
    (mi : Fin dout) (mj : Fin dout),
    (gates.get ⟨i, hi⟩).outputs mi = (gates.get ⟨j, hj⟩).outputs mj → i = j

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

/-- Cast a subcircuit along a gate length equality -/
def Subcircuit.cast {din dout : Nat} {C C' : Circuit din dout}
    (S : Subcircuit C) (h : C.gates.length = C'.gates.length) : Subcircuit C' where
  gateIndices := S.gateIndices.map ⟨Fin.cast h, Fin.cast_injective h⟩

/-- Empty subcircuit -/
def Subcircuit.empty {din dout : Nat} (C : Circuit din dout) : Subcircuit C where
  gateIndices := ∅

/-- Size of empty subcircuit is 0 -/
@[simp] lemma Subcircuit.size_empty {din dout : Nat} (C : Circuit din dout) :
    (Subcircuit.empty C).size = 0 := Finset.card_empty

/-- Cast of empty subcircuit is empty -/
@[simp] lemma Subcircuit.cast_empty {din dout : Nat} {C C' : Circuit din dout}
    (h : C.gates.length = C'.gates.length) :
    (Subcircuit.empty C).cast h = Subcircuit.empty C' := by
  simp only [cast, empty, Finset.map_empty]

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

/-- Extract the indices of gates in the subcircuit (in order) -/
def Subcircuit.extractIndices {din dout : Nat} {C : Circuit din dout} (S : Subcircuit C) :
    List (Fin C.gates.length) :=
  (List.finRange C.gates.length).filter fun i => i ∈ S.gateIndices

/-- Extract gates from subcircuit indices (preserving topological order) -/
def Subcircuit.extractGates {din dout : Nat} {C : Circuit din dout} (S : Subcircuit C) : List (Gate din dout) :=
  S.extractIndices.map fun i => C.gates.get i

/-- extractGates equals filterMap formulation -/
lemma Subcircuit.extractGates_eq_filterMap {din dout : Nat} {C : Circuit din dout} (S : Subcircuit C) :
    S.extractGates = (List.finRange C.gates.length).filterMap fun i =>
      if i ∈ S.gateIndices then some (C.gates.get i) else none := by
  simp only [extractGates, extractIndices]
  induction (List.finRange C.gates.length) with
  | nil => simp
  | cons a l ih =>
    simp only [List.filter_cons, List.filterMap_cons]
    split <;> simp_all

/-- Membership lemma for extractGates -/
lemma Subcircuit.mem_extractGates {din dout : Nat} {C : Circuit din dout} {S : Subcircuit C}
    {g : Gate din dout} (hg : g ∈ S.extractGates) :
    ∃ i : Fin C.gates.length, i ∈ S.gateIndices ∧ g = C.gates.get i := by
  simp only [extractGates, List.mem_map] at hg
  obtain ⟨i, hi_mem, hi_eq⟩ := hg
  rw [extractIndices, List.mem_filter] at hi_mem
  have hi_in : i ∈ S.gateIndices := decide_eq_true_iff.mp hi_mem.2
  exact ⟨i, hi_in, hi_eq.symm⟩

/-- Get the original index of a gate in extractGates -/
lemma Subcircuit.extractGates_get_orig {din dout : Nat} {C : Circuit din dout} {S : Subcircuit C}
    (j : Nat) (hj : j < S.extractGates.length) :
    ∃ i : Fin C.gates.length, i ∈ S.gateIndices ∧ S.extractGates.get ⟨j, hj⟩ = C.gates.get i := by
  have hmem : S.extractGates.get ⟨j, hj⟩ ∈ S.extractGates := List.get_mem _ _ _
  exact mem_extractGates hmem

/-- The original index at a position in extractIndices -/
def Subcircuit.origIndexAt {din dout : Nat} {C : Circuit din dout} (S : Subcircuit C)
    (p : Nat) (hp : p < S.extractIndices.length) : Fin C.gates.length :=
  S.extractIndices.get ⟨p, hp⟩

/-- The original index at position j is exactly origIndexAt j -/
lemma Subcircuit.extractGates_get_orig_unique {din dout : Nat} {C : Circuit din dout} {S : Subcircuit C}
    (j : Nat) (hj : j < S.extractGates.length) :
    let hj_idx : j < S.extractIndices.length := by simp [extractGates] at hj; exact hj
    S.extractGates.get ⟨j, hj⟩ = C.gates.get (S.origIndexAt j hj_idx) ∧
    S.origIndexAt j hj_idx ∈ S.gateIndices := by
  intro hj_idx
  constructor
  · simp only [extractGates, origIndexAt, List.get_eq_getElem, List.getElem_map]
  · simp only [origIndexAt, extractIndices]
    have h_mem := List.get_mem (List.filter (· ∈ S.gateIndices) (List.finRange C.gates.length)) j hj_idx
    rw [List.mem_filter] at h_mem
    exact decide_eq_true_iff.mp h_mem.2

/-- extractIndices is strictly increasing -/
lemma Subcircuit.extractIndices_strictMono {din dout : Nat} {C : Circuit din dout} {S : Subcircuit C}
    {p q : Nat} (hp : p < S.extractIndices.length) (hq : q < S.extractIndices.length)
    (hpq : p < q) :
    S.extractIndices.get ⟨p, hp⟩ < S.extractIndices.get ⟨q, hq⟩ := by
  simp only [extractIndices]
  have h_pairwise : List.Pairwise (· < ·) (List.finRange C.gates.length) :=
    List.pairwise_lt_finRange C.gates.length
  have h_filtered : List.Pairwise (· < ·)
      (List.filter (· ∈ S.gateIndices) (List.finRange C.gates.length)) :=
    h_pairwise.filter _
  exact List.pairwise_iff_getElem.mp h_filtered p q hp hq hpq

/-- extractGates preserves order: if original indices satisfy i < j, their positions in extractGates do too.
    Also provides that origIndexAt at those positions equals the original indices. -/
lemma Subcircuit.extractGates_preserves_order' {din dout : Nat} {C : Circuit din dout} {S : Subcircuit C}
    {i j : Fin C.gates.length} (hi : i ∈ S.gateIndices) (hj : j ∈ S.gateIndices) (hij : i < j) :
    ∃ (pi pj : Nat) (hpi : pi < S.extractGates.length) (hpj : pj < S.extractGates.length),
      pi < pj ∧
      S.extractGates.get ⟨pi, hpi⟩ = C.gates.get i ∧
      S.extractGates.get ⟨pj, hpj⟩ = C.gates.get j ∧
      S.origIndexAt pi (by simp [extractGates] at hpi; exact hpi) = i ∧
      S.origIndexAt pj (by simp [extractGates] at hpj; exact hpj) = j := by
  have hi_in : i ∈ S.extractIndices := by
    rw [extractIndices, List.mem_filter]
    exact ⟨List.mem_finRange i, decide_eq_true_iff.mpr hi⟩
  have hj_in : j ∈ S.extractIndices := by
    rw [extractIndices, List.mem_filter]
    exact ⟨List.mem_finRange j, decide_eq_true_iff.mpr hj⟩
  obtain ⟨pi, hpi_lt, hpi_get⟩ := List.getElem_of_mem hi_in
  obtain ⟨pj, hpj_lt, hpj_get⟩ := List.getElem_of_mem hj_in
  have hpi_pj : pi < pj := by
    by_contra h_not_lt
    push_neg at h_not_lt
    rcases Nat.lt_or_eq_of_le h_not_lt with hpj_lt_pi | heq
    · have := extractIndices_strictMono hpj_lt hpi_lt hpj_lt_pi
      rw [List.get_eq_getElem, List.get_eq_getElem] at this
      rw [hpi_get, hpj_get] at this
      exact Nat.lt_irrefl _ (Nat.lt_trans hij this)
    · subst heq
      rw [hpi_get] at hpj_get
      exact Nat.lt_irrefl _ (hpj_get ▸ hij)
  have hpi_eg : pi < S.extractGates.length := by
    simp only [extractGates, List.length_map]
    exact hpi_lt
  have hpj_eg : pj < S.extractGates.length := by
    simp only [extractGates, List.length_map]
    exact hpj_lt
  refine ⟨pi, pj, hpi_eg, hpj_eg, hpi_pj, ?_, ?_, ?_, ?_⟩
  · simp only [extractGates]
    rw [List.get_eq_getElem, List.getElem_map, hpi_get]
  · simp only [extractGates]
    rw [List.get_eq_getElem, List.getElem_map, hpj_get]
  · simp only [origIndexAt, List.get_eq_getElem, hpi_get]
  · simp only [origIndexAt, List.get_eq_getElem, hpj_get]

/-- extractGates preserves order (simpler version without origIndexAt info) -/
lemma Subcircuit.extractGates_preserves_order {din dout : Nat} {C : Circuit din dout} {S : Subcircuit C}
    {i j : Fin C.gates.length} (hi : i ∈ S.gateIndices) (hj : j ∈ S.gateIndices) (hij : i < j) :
    ∃ (pi pj : Nat) (hpi : pi < S.extractGates.length) (hpj : pj < S.extractGates.length),
      pi < pj ∧
      S.extractGates.get ⟨pi, hpi⟩ = C.gates.get i ∧
      S.extractGates.get ⟨pj, hpj⟩ = C.gates.get j := by
  obtain ⟨pi, pj, hpi, hpj, h_lt, h_gate_i, h_gate_j, _, _⟩ :=
    extractGates_preserves_order' hi hj hij
  exact ⟨pi, pj, hpi, hpj, h_lt, h_gate_i, h_gate_j⟩

/-- extractIndices has no duplicates -/
lemma Subcircuit.extractIndices_nodup {din dout : Nat} {C : Circuit din dout} (S : Subcircuit C) :
    S.extractIndices.Nodup := by
  simp only [extractIndices]
  exact List.Nodup.filter _ (List.nodup_finRange _)

/-- origIndexAt is strictly monotone -/
lemma Subcircuit.origIndexAt_strictMono {din dout : Nat} {C : Circuit din dout} {S : Subcircuit C}
    {p q : Nat} (hp : p < S.extractIndices.length) (hq : q < S.extractIndices.length)
    (hpq : p < q) :
    S.origIndexAt p hp < S.origIndexAt q hq :=
  extractIndices_strictMono hp hq hpq

/-- origIndexAt is injective -/
lemma Subcircuit.origIndexAt_injective {din dout : Nat} {C : Circuit din dout} {S : Subcircuit C}
    {p q : Nat} (hp : p < S.extractIndices.length) (hq : q < S.extractIndices.length)
    (h_eq : S.origIndexAt p hp = S.origIndexAt q hq) :
    p = q := by
  by_contra h_ne
  rcases Nat.lt_trichotomy p q with hlt | heq | hgt
  · have := origIndexAt_strictMono hp hq hlt
    exact Nat.lt_irrefl _ (h_eq ▸ this)
  · exact h_ne heq
  · have := origIndexAt_strictMono hq hp hgt
    exact Nat.lt_irrefl _ (h_eq.symm ▸ this)

/-- For ι in gateIndices, find its unique position in extractIndices -/
lemma Subcircuit.positionOf_mem {din dout : Nat} {C : Circuit din dout} {S : Subcircuit C}
    (ι : Fin C.gates.length) (hι : ι ∈ S.gateIndices) :
    ∃! (p : Nat), ∃ (hp : p < S.extractIndices.length), S.origIndexAt p hp = ι := by
  have hι_in : ι ∈ S.extractIndices := by
    rw [extractIndices, List.mem_filter]
    exact ⟨List.mem_finRange ι, decide_eq_true_iff.mpr hι⟩
  obtain ⟨p, hp_lt, hp_get⟩ := List.getElem_of_mem hι_in
  refine ⟨p, ⟨hp_lt, ?_⟩, ?_⟩
  · simp only [origIndexAt, List.get_eq_getElem, hp_get]
  · intro q ⟨hq_lt, hq_eq⟩
    have heq : S.extractIndices.get ⟨p, hp_lt⟩ = S.extractIndices.get ⟨q, hq_lt⟩ := by
      simp only [origIndexAt, List.get_eq_getElem] at hq_eq
      simp only [List.get_eq_getElem, hp_get, hq_eq]
    have h_nodup := S.extractIndices_nodup
    have hfin : (⟨p, hp_lt⟩ : Fin S.extractIndices.length) = ⟨q, hq_lt⟩ :=
      List.Nodup.get_inj_iff h_nodup |>.mp heq
    exact (Fin.mk.inj hfin).symm

/-- If origIndexAt p = ι, then p is the unique position of ι -/
lemma Subcircuit.origIndexAt_unique {din dout : Nat} {C : Circuit din dout} {S : Subcircuit C}
    {p q : Nat} (hp : p < S.extractIndices.length) (hq : q < S.extractIndices.length)
    (ι : Fin C.gates.length) (hp_eq : S.origIndexAt p hp = ι) (hq_eq : S.origIndexAt q hq = ι) :
    p = q := by
  apply origIndexAt_injective hp hq
  rw [hp_eq, hq_eq]

/-- extractGates at position p equals C.gates.get (origIndexAt p) -/
lemma Subcircuit.extractGates_get_eq_origIndex {din dout : Nat} {C : Circuit din dout} {S : Subcircuit C}
    (p : Nat) (hp : p < S.extractGates.length) :
    S.extractGates.get ⟨p, hp⟩ = C.gates.get (S.origIndexAt p (by simp [extractGates, List.length_map] at hp; exact hp)) := by
  simp only [extractGates, origIndexAt, List.get_eq_getElem, List.getElem_map]

/-- extractGates is injective on original indices -/
lemma Subcircuit.extractGates_pos_injective {din dout : Nat} {C : Circuit din dout} {S : Subcircuit C}
    {pi pj : Nat} (hpi : pi < S.extractGates.length) (hpj : pj < S.extractGates.length)
    (h_orig_eq : S.origIndexAt pi (by simp [extractGates] at hpi; exact hpi) =
                 S.origIndexAt pj (by simp [extractGates] at hpj; exact hpj)) :
    pi = pj :=
  origIndexAt_injective _ _ h_orig_eq

/-- The induced circuit on subcircuit S -/
noncomputable def Circuit.induced {din dout : Nat} (C : Circuit din dout) (S : Subcircuit C) : Circuit din dout where
  gates := S.extractGates
  inputWires := S.inp.toList
  outputWires := S.out.toList
  inputWires_nodup := Finset.nodup_toList _
  outputWires_nodup := Finset.nodup_toList _
  inputs_not_outputs := by
    classical
    intro w hw_inp i hi m
    simp only [Finset.mem_toList] at hw_inp
    have hw_not_out := (Finset.mem_sdiff.mp hw_inp).2
    intro heq
    apply hw_not_out
    obtain ⟨ι, hιS, hgate_eq⟩ := S.extractGates_get_orig i hi
    simp only [Subcircuit.allOutputWires, Finset.mem_biUnion, Finset.mem_image, Finset.mem_univ,
               true_and]
    refine ⟨ι, hιS, m, ?_⟩
    rw [← hgate_eq]; exact heq
  unique_drivers := by
    classical
    intro i j hi hj mi mj heq
    have hi_idx : i < S.extractIndices.length := by simp [Subcircuit.extractGates] at hi; exact hi
    have hj_idx : j < S.extractIndices.length := by simp [Subcircuit.extractGates] at hj; exact hj
    obtain ⟨hgate_i, _⟩ := S.extractGates_get_orig_unique i hi
    obtain ⟨hgate_j, _⟩ := S.extractGates_get_orig_unique j hj
    let ιi := S.origIndexAt i hi_idx
    let ιj := S.origIndexAt j hj_idx
    have heq' : (C.gates.get ιi).outputs mi = (C.gates.get ιj).outputs mj := by
      rw [← hgate_i, ← hgate_j]; exact heq
    have h_same := C.unique_drivers ιi.val ιj.val ιi.isLt ιj.isLt mi mj heq'
    have hι_eq : ιi = ιj := Fin.ext h_same
    exact S.origIndexAt_injective hi_idx hj_idx hι_eq
  topological := by
    classical
    intro i hi k
    -- Get the original gate index ι in C
    have hi_idx : i < S.extractIndices.length := by simp [Subcircuit.extractGates] at hi; exact hi
    let ι := S.origIndexAt i hi_idx
    -- The gate at position i in extractGates is C.gates[ι]
    have hgate : S.extractGates.get ⟨i, hi⟩ = C.gates.get ι := (S.extractGates_get_orig_unique i hi).1
    -- The wire w is the k-th input of this gate
    let w := (S.extractGates.get ⟨i, hi⟩).inputs k
    -- From the original circuit's topological property
    have htopo := C.topological ι.val ι.isLt k
    cases htopo with
    | inl hw_inp =>
      -- Case 1: w is a primary input of C
      left
      simp only [Finset.mem_toList, Subcircuit.inp, Finset.mem_sdiff]
      constructor
      · -- w is in allInputWires
        simp only [Subcircuit.allInputWires, Finset.mem_biUnion, Finset.mem_image, Finset.mem_univ,
                   true_and]
        have hιS := (S.extractGates_get_orig_unique i hi).2
        refine ⟨ι, hιS, k, ?_⟩
        simp only [hgate, w]
      · -- w is not in allOutputWires (because C.inputs_not_outputs)
        simp only [Subcircuit.allOutputWires, Finset.mem_biUnion, Finset.mem_image, Finset.mem_univ,
                   true_and]
        intro ⟨κ, _, m, hout⟩
        have hwC : w ∈ C.inputWires := by simp only [w, hgate]; exact hw_inp
        exact C.inputs_not_outputs w hwC κ.val κ.isLt m hout
    | inr hw_output =>
      -- Case 2: w is output of gate j (where j < ι in C)
      obtain ⟨j, hj_lt, m, hw_out⟩ := hw_output
      let κ : Fin C.gates.length := ⟨j, Nat.lt_trans hj_lt ι.isLt⟩
      -- w as output of κ
      have hw_from_κ : (C.gates.get κ).outputs m = w := by
        simp only [w, hgate, κ]
        exact hw_out
      by_cases hκS : κ ∈ S.gateIndices
      · -- Case 2a: gate κ is in the subcircuit
        right
        -- Find position of κ in extractIndices using preserves_order'
        -- κ < ι as Fins (since j < ι.val)
        have hκ_lt_ι : κ < ι := hj_lt
        have hιS := (S.extractGates_get_orig_unique i hi).2
        obtain ⟨pκ, pι, hpκ_lt, hpι_lt, hpκ_lt_pι, hgate_κ, hgate_ι, hpκ_orig, hpι_orig⟩ :=
          S.extractGates_preserves_order' hκS hιS hκ_lt_ι
        -- pι should equal i (the position of ι in extractGates)
        have hi_eq_pι : i = pι := by
          apply S.origIndexAt_injective hi_idx (by simp [Subcircuit.extractGates] at hpι_lt; exact hpι_lt)
          exact hpι_orig.symm
        refine ⟨pκ, ?_, m, ?_⟩
        · rw [hi_eq_pι]; exact hpκ_lt_pι
        · simp only [w, hgate]
          rw [← hw_out, ← hgate_κ]
      · -- Case 2b: gate κ is NOT in the subcircuit
        -- Then w is an input wire of the subcircuit (comes from outside)
        left
        simp only [Finset.mem_toList, Subcircuit.inp, Finset.mem_sdiff]
        constructor
        · -- w is in allInputWires
          simp only [Subcircuit.allInputWires, Finset.mem_biUnion, Finset.mem_image, Finset.mem_univ,
                     true_and]
          have hιS := (S.extractGates_get_orig_unique i hi).2
          refine ⟨ι, hιS, k, ?_⟩
          simp only [hgate, w]
        · -- w is not in allOutputWires
          simp only [Subcircuit.allOutputWires, Finset.mem_biUnion, Finset.mem_image, Finset.mem_univ,
                     true_and]
          intro ⟨τ, hτS, n, hout_τ⟩
          -- If τ produces w, then τ = κ by unique_drivers
          have hw_eq : (C.gates.get τ).outputs n = w := hout_τ
          have h_drivers := C.unique_drivers τ.val κ.val τ.isLt κ.isLt n m (hw_eq.trans hw_from_κ.symm)
          have hτ_eq_κ : τ = κ := Fin.ext h_drivers
          rw [hτ_eq_κ] at hτS
          exact hκS hτS

/-- Reflexivity of functional equivalence -/
theorem FunctionallyEquivalent'.refl {din dout : Nat} (C : Circuit din dout) :
    FunctionallyEquivalent' C C rfl rfl := by
  intro x
  rfl

/-- Symmetry of functional equivalence -/
theorem FunctionallyEquivalent'.symm {din dout : Nat} {C C' : Circuit din dout}
    {h_inp : C.inputWires = C'.inputWires} {h_out : C.outputWires = C'.outputWires}
    (h : FunctionallyEquivalent' C C' h_inp h_out) :
    FunctionallyEquivalent' C' C h_inp.symm h_out.symm := by
  classical
  intro x
  have len_inp_eq : C.inputWires.length = C'.inputWires.length := congrArg List.length h_inp
  have len_out_eq : C.outputWires.length = C'.outputWires.length := congrArg List.length h_out
  have hx := h (fun i => x (Fin.cast len_inp_eq i))
  simp only [FunctionallyEquivalent'] at hx ⊢
  funext k
  have hk := congrFun hx.symm (Fin.cast len_out_eq.symm k)
  simp only [Fin.cast_trans, Fin.cast_eq_self] at hk
  convert hk using 2

/-- Transitivity of functional equivalence -/
theorem FunctionallyEquivalent'.trans {din dout : Nat} {C C' C'' : Circuit din dout}
    {h_inp : C.inputWires = C'.inputWires} {h_out : C.outputWires = C'.outputWires}
    {h_inp' : C'.inputWires = C''.inputWires} {h_out' : C'.outputWires = C''.outputWires}
    (h1 : FunctionallyEquivalent' C C' h_inp h_out)
    (h2 : FunctionallyEquivalent' C' C'' h_inp' h_out') :
    FunctionallyEquivalent' C C'' (h_inp.trans h_inp') (h_out.trans h_out') := by
  classical
  intro x
  have len_inp_eq := congrArg List.length h_inp
  have len_out_eq := congrArg List.length h_out
  have eq1 := h1 x
  have eq2 := h2 (fun i => x (Fin.cast len_inp_eq.symm i))
  simp only [FunctionallyEquivalent'] at eq1 eq2 ⊢
  funext k
  have hk1 := congrFun eq1 k
  have hk2 := congrFun eq2 (Fin.cast len_out_eq k)
  simp only [Fin.cast_trans] at hk2 ⊢
  simp only [hk1, hk2]

/-- Helper: initValuation is determined by the input wire list -/
lemma initValuation_eq_of_inputs_eq {din dout : Nat} {C C' : Circuit din dout}
    (h_inp : C.inputWires = C'.inputWires)
    (x : Fin C.inputWires.length → Bool) :
    initValuation C x = initValuation C' (fun i => x (Fin.cast (congrArg List.length h_inp).symm i)) := by
  funext w
  simp only [initValuation, h_inp]
  split <;> simp_all

/-- Helper: evalGates with identical gate lists produces identical valuations -/
lemma evalGates_eq_of_gates_eq {din dout : Nat}
    (gates gates' : List (Gate din dout))
    (h_eq : gates = gates')
    (σ : WireValuation) :
    evalGates gates σ = evalGates gates' σ := by
  subst h_eq
  rfl

/-- Topologically equivalent circuits with same gate operations are functionally equivalent -/
theorem TopologicallyEquivalent.functionallyEquivalent {din dout : Nat} {C C' : Circuit din dout}
    (htopo : TopologicallyEquivalent C C')
    (hops : ∀ (i : Nat) (hi : i < C.gates.length),
      (C.gates.get ⟨i, hi⟩).op = (C'.gates.get ⟨i, htopo.len_eq ▸ hi⟩).op) :
    FunctionallyEquivalent' C C' htopo.inputs_eq htopo.outputs_eq := by
  classical
  intro x
  simp only [FunctionallyEquivalent']
  have len_inp_eq := congrArg List.length htopo.inputs_eq
  have len_out_eq := congrArg List.length htopo.outputs_eq
  funext k
  simp only [Circuit.eval]
  have hσ₀ : initValuation C x = initValuation C' (fun i => x (Fin.cast len_inp_eq.symm i)) :=
    initValuation_eq_of_inputs_eq htopo.inputs_eq x
  have hgates_eq : C.gates = C'.gates := by
    apply List.ext_get
    · exact htopo.len_eq
    · intro i hi hi'
      have hmatch := htopo.gates_match i hi
      have hop := hops i hi
      rcases hmatch with ⟨hid, hinputs, houtputs⟩
      -- Use functional extensionality-style proof
      have h : C.gates.get ⟨i, hi⟩ = C'.gates.get ⟨i, hi'⟩ := by
        have heq : C.gates.get ⟨i, hi⟩ = { id := (C.gates.get ⟨i, hi⟩).id,
                                           inputs := (C.gates.get ⟨i, hi⟩).inputs,
                                           outputs := (C.gates.get ⟨i, hi⟩).outputs,
                                           op := (C.gates.get ⟨i, hi⟩).op } := rfl
        have heq' : C'.gates.get ⟨i, hi'⟩ = { id := (C'.gates.get ⟨i, hi'⟩).id,
                                              inputs := (C'.gates.get ⟨i, hi'⟩).inputs,
                                              outputs := (C'.gates.get ⟨i, hi'⟩).outputs,
                                              op := (C'.gates.get ⟨i, hi'⟩).op } := rfl
        rw [heq, heq', hid, hinputs, houtputs, hop]
      exact h
  have hσ : evalGates C.gates (initValuation C x) =
            evalGates C'.gates (initValuation C' (fun i => x (Fin.cast len_inp_eq.symm i))) := by
    rw [hσ₀, hgates_eq]
  rw [hσ]
  -- Final step: C.outputWires.get k = C'.outputWires.get (Fin.cast len_out_eq k)
  -- follows from htopo.outputs_eq : C.outputWires = C'.outputWires
  have hout_eq : C.outputWires = C'.outputWires := htopo.outputs_eq
  simp only [List.get_eq_getElem]
  -- Need: C.outputWires[k.val] = C'.outputWires[(Fin.cast len_out_eq k).val]
  -- Since (Fin.cast len_out_eq k).val = k.val and C.outputWires = C'.outputWires
  have hk_val : k.val = (Fin.cast len_out_eq k).val := rfl
  simp only [hout_eq, hk_val]

/-- Reflexivity of topological equivalence -/
theorem TopologicallyEquivalent.refl {din dout : Nat} (C : Circuit din dout) :
    TopologicallyEquivalent C C where
  len_eq := rfl
  inputs_eq := rfl
  outputs_eq := rfl
  gates_match := fun _ _ => ⟨rfl, rfl, rfl⟩

/-- Symmetry of topological equivalence -/
theorem TopologicallyEquivalent.symm {din dout : Nat} {C C' : Circuit din dout}
    (h : TopologicallyEquivalent C C') : TopologicallyEquivalent C' C where
  len_eq := h.len_eq.symm
  inputs_eq := h.inputs_eq.symm
  outputs_eq := h.outputs_eq.symm
  gates_match := fun i hi =>
    let hi' : i < C.gates.length := h.len_eq ▸ hi
    let ⟨hid, hinp, hout⟩ := h.gates_match i hi'
    ⟨hid.symm, hinp.symm, hout.symm⟩

/-- Transitivity of topological equivalence -/
theorem TopologicallyEquivalent.trans {din dout : Nat} {C C' C'' : Circuit din dout}
    (h1 : TopologicallyEquivalent C C') (h2 : TopologicallyEquivalent C' C'') :
    TopologicallyEquivalent C C'' where
  len_eq := h1.len_eq.trans h2.len_eq
  inputs_eq := h1.inputs_eq.trans h2.inputs_eq
  outputs_eq := h1.outputs_eq.trans h2.outputs_eq
  gates_match := fun i hi =>
    let hi' : i < C'.gates.length := h1.len_eq ▸ hi
    let ⟨hid1, hinp1, hout1⟩ := h1.gates_match i hi
    let ⟨hid2, hinp2, hout2⟩ := h2.gates_match i hi'
    ⟨hid1.trans hid2, hinp1.trans hinp2, hout1.trans hout2⟩

/-!
## Circuit.withOps: Replacing gate operations on a fixed topology

This is a key combinator for the padding construction. It allows us to
vary gate operations while preserving the circuit topology (gate IDs,
input/output wires, and circuit structure).

The crucial property is that circuits produced by `withOps` on the same
base circuit are always topologically equivalent.
-/

/-- Replace gate operations while keeping gate IDs, inputs, outputs, and topology fixed.

This is the key combinator for constructing padded circuits with identical topology.
Given a circuit C and a function assigning new operations to each gate position,
produces a new circuit with the same topology but different gate operations.
-/
def Circuit.withOps {din dout : Nat} (C : Circuit din dout)
    (ops : Fin C.gates.length → GateOp din dout) : Circuit din dout where
  gates := (List.finRange C.gates.length).map fun i =>
    let g := C.gates.get i
    { id := g.id, inputs := g.inputs, outputs := g.outputs, op := ops i }
  inputWires := C.inputWires
  outputWires := C.outputWires
  inputWires_nodup := C.inputWires_nodup
  outputWires_nodup := C.outputWires_nodup
  topological := by
    intro i hi k
    simp only [List.length_map, List.length_finRange] at hi
    simp only [List.get_eq_getElem, List.getElem_map, List.getElem_finRange]
    exact C.topological i hi k
  inputs_not_outputs := by
    intro w hw i hi m
    simp only [List.length_map, List.length_finRange] at hi
    simp only [List.get_eq_getElem, List.getElem_map, List.getElem_finRange]
    exact C.inputs_not_outputs w hw i hi m
  unique_drivers := by
    intro i j hi hj mi mj heq
    simp only [List.length_map, List.length_finRange] at hi hj
    simp only [List.get_eq_getElem, List.getElem_map, List.getElem_finRange] at heq
    exact C.unique_drivers i j hi hj mi mj heq

/-- withOps preserves gate list length -/
@[simp] lemma Circuit.withOps_length {din dout : Nat} (C : Circuit din dout)
    (ops : Fin C.gates.length → GateOp din dout) :
    (C.withOps ops).gates.length = C.gates.length := by
  simp only [withOps, List.length_map, List.length_finRange]

/-- withOps preserves circuit size -/
@[simp] lemma Circuit.withOps_size {din dout : Nat} (C : Circuit din dout)
    (ops : Fin C.gates.length → GateOp din dout) :
    (C.withOps ops).size = C.size := by
  simp only [size, withOps_length]

/-- withOps preserves input wires -/
@[simp] lemma Circuit.withOps_inputWires {din dout : Nat} (C : Circuit din dout)
    (ops : Fin C.gates.length → GateOp din dout) :
    (C.withOps ops).inputWires = C.inputWires := rfl

/-- withOps preserves output wires -/
@[simp] lemma Circuit.withOps_outputWires {din dout : Nat} (C : Circuit din dout)
    (ops : Fin C.gates.length → GateOp din dout) :
    (C.withOps ops).outputWires = C.outputWires := rfl

/-- Get the gate at position i in withOps -/
lemma Circuit.withOps_gate {din dout : Nat} (C : Circuit din dout)
    (ops : Fin C.gates.length → GateOp din dout) (i : Fin C.gates.length) :
    (C.withOps ops).gates.get (Fin.cast (withOps_length C ops).symm i) =
    { id := (C.gates.get i).id,
      inputs := (C.gates.get i).inputs,
      outputs := (C.gates.get i).outputs,
      op := ops i } := by
  simp only [withOps, List.get_eq_getElem, List.getElem_map, List.getElem_finRange]
  rfl

/-- withOps produces topologically equivalent circuit -/
theorem Circuit.withOps_topo_equiv {din dout : Nat} (C : Circuit din dout)
    (ops : Fin C.gates.length → GateOp din dout) :
    TopologicallyEquivalent C (C.withOps ops) where
  len_eq := (withOps_length C ops).symm
  inputs_eq := rfl
  outputs_eq := rfl
  gates_match := by
    intro i hi
    simp only [withOps, List.get_eq_getElem, List.getElem_map, List.getElem_finRange]
    exact ⟨rfl, rfl, rfl⟩

/-- Two circuits built with withOps on the same base are topologically equivalent -/
theorem Circuit.withOps_withOps_topo_equiv {din dout : Nat} (C : Circuit din dout)
    (ops₁ ops₂ : Fin C.gates.length → GateOp din dout) :
    TopologicallyEquivalent (C.withOps ops₁) (C.withOps ops₂) :=
  (withOps_topo_equiv C ops₁).symm.trans (withOps_topo_equiv C ops₂)

/-- If ops agree everywhere, withOps produces the same gates -/
lemma Circuit.withOps_eq_of_ops_eq {din dout : Nat} (C : Circuit din dout)
    (ops₁ ops₂ : Fin C.gates.length → GateOp din dout)
    (h : ops₁ = ops₂) :
    C.withOps ops₁ = C.withOps ops₂ := by
  simp only [h]

end MaDaiShi
