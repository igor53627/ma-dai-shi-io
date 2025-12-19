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
deriving DecidableEq

/-- A gate in a circuit with bounded fan-in and fan-out -/
structure Gate (fanIn fanOut : Nat) where
  id : GateId
  inputs : Fin fanIn → WireId
  outputs : Fin fanOut → WireId
  op : GateOp fanIn fanOut
deriving DecidableEq

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
  simp only [extractIndices, List.mem_filter, List.mem_finRange, true_and] at hi_mem
  exact ⟨i, hi_mem, hi_eq.symm⟩

/-- Get the original index of a gate in extractGates -/
lemma Subcircuit.extractGates_get_orig {din dout : Nat} {C : Circuit din dout} {S : Subcircuit C}
    (j : Nat) (hj : j < S.extractGates.length) :
    ∃ i : Fin C.gates.length, i ∈ S.gateIndices ∧ S.extractGates.get ⟨j, hj⟩ = C.gates.get i := by
  have hmem : S.extractGates.get ⟨j, hj⟩ ∈ S.extractGates := List.get_mem _ _ _
  exact mem_extractGates hmem

/-- The original index at position j is exactly origIndexAt j -/
lemma Subcircuit.extractGates_get_orig_unique {din dout : Nat} {C : Circuit din dout} {S : Subcircuit C}
    (j : Nat) (hj : j < S.extractGates.length) :
    let hj_idx : j < S.extractIndices.length := by simp [extractGates] at hj; exact hj
    S.extractGates.get ⟨j, hj⟩ = C.gates.get (S.origIndexAt j hj_idx) ∧
    S.origIndexAt j hj_idx ∈ S.gateIndices := by
  intro hj_idx
  constructor
  · simp only [extractGates, List.get_map, origIndexAt]
  · simp only [origIndexAt, extractIndices]
    have h_mem := List.get_mem (List.filter (· ∈ S.gateIndices) (List.finRange C.gates.length)) j hj_idx
    simp only [List.mem_filter, List.mem_finRange, true_and] at h_mem
    exact h_mem

/-- extractIndices is strictly increasing -/
lemma Subcircuit.extractIndices_strictMono {din dout : Nat} {C : Circuit din dout} {S : Subcircuit C}
    {p q : Nat} (hp : p < S.extractIndices.length) (hq : q < S.extractIndices.length)
    (hpq : p < q) :
    S.extractIndices.get ⟨p, hp⟩ < S.extractIndices.get ⟨q, hq⟩ := by
  simp only [extractIndices]
  -- extractIndices is a sublist of finRange, and finRange is sorted
  -- For a filtered list from a sorted list, smaller positions give smaller values
  -- This is because filter preserves relative order
  -- Proof: use that l.filter p is a sublist of l, and sublists of sorted lists are sorted
  sorry

/-- extractGates preserves order: if original indices satisfy i < j, their positions in extractGates do too -/
lemma Subcircuit.extractGates_preserves_order {din dout : Nat} {C : Circuit din dout} {S : Subcircuit C}
    {i j : Fin C.gates.length} (hi : i ∈ S.gateIndices) (hj : j ∈ S.gateIndices) (hij : i < j) :
    ∃ (pi pj : Nat) (hpi : pi < S.extractGates.length) (hpj : pj < S.extractGates.length),
      pi < pj ∧
      S.extractGates.get ⟨pi, hpi⟩ = C.gates.get i ∧
      S.extractGates.get ⟨pj, hpj⟩ = C.gates.get j := by
  -- i and j are in extractIndices (since they're in gateIndices)
  -- Their positions pi, pj satisfy pi < pj because extractIndices is strictly mono
  have hi_in : i ∈ S.extractIndices := by
    simp only [extractIndices, List.mem_filter, List.mem_finRange, true_and]
    exact hi
  have hj_in : j ∈ S.extractIndices := by
    simp only [extractIndices, List.mem_filter, List.mem_finRange, true_and]
    exact hj
  -- Get positions
  obtain ⟨pi, hpi_lt, hpi_get⟩ := List.getElem_of_mem hi_in
  obtain ⟨pj, hpj_lt, hpj_get⟩ := List.getElem_of_mem hj_in
  -- Show pi < pj using strict monotonicity
  have hpi_pj : pi < pj := by
    by_contra h_not_lt
    push_neg at h_not_lt
    cases Nat.lt_or_eq_of_le h_not_lt with
    | inl hpj_lt_pi =>
      have := extractIndices_strictMono hpj_lt hpi_lt hpj_lt_pi
      simp only [← hpi_get, ← hpj_get] at this
      have : j < i := this
      exact Nat.lt_irrefl _ (Nat.lt_trans hij this)
    | inr heq =>
      subst heq
      simp only [← hpi_get, ← hpj_get] at hij
      exact Nat.lt_irrefl _ hij
  -- Now extractGates positions
  have hpi_eg : pi < S.extractGates.length := by
    simp only [extractGates, List.length_map]
    exact hpi_lt
  have hpj_eg : pj < S.extractGates.length := by
    simp only [extractGates, List.length_map]
    exact hpj_lt
  refine ⟨pi, pj, hpi_eg, hpj_eg, hpi_pj, ?_, ?_⟩
  · simp only [extractGates, List.get_map]
    congr 1
    exact hpi_get.symm
  · simp only [extractGates, List.get_map]
    congr 1
    exact hpj_get.symm

/-- extractIndices has no duplicates -/
lemma Subcircuit.extractIndices_nodup {din dout : Nat} {C : Circuit din dout} (S : Subcircuit C) :
    S.extractIndices.Nodup := by
  simp only [extractIndices]
  exact List.Nodup.filter _ (List.nodup_finRange _)

/-- The original index at a position in extractIndices -/
def Subcircuit.origIndexAt {din dout : Nat} {C : Circuit din dout} (S : Subcircuit C)
    (p : Nat) (hp : p < S.extractIndices.length) : Fin C.gates.length :=
  S.extractIndices.get ⟨p, hp⟩

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
  -- If p ≠ q, then by strict monotonicity origIndexAt p ≠ origIndexAt q
  by_contra h_ne
  cases Nat.lt_trichotomous p q with
  | inl hlt =>
    have := origIndexAt_strictMono hp hq hlt
    exact Nat.lt_irrefl _ (h_eq ▸ this)
  | inr h =>
    cases h with
    | inl heq => exact h_ne heq
    | inr hgt =>
      have := origIndexAt_strictMono hq hp hgt
      exact Nat.lt_irrefl _ (h_eq.symm ▸ this)

/-- extractGates at position p equals C.gates.get (origIndexAt p) -/
lemma Subcircuit.extractGates_get_eq_origIndex {din dout : Nat} {C : Circuit din dout} {S : Subcircuit C}
    (p : Nat) (hp : p < S.extractGates.length) :
    S.extractGates.get ⟨p, hp⟩ = C.gates.get (S.origIndexAt p (by simp [extractGates, List.length_map] at hp; exact hp)) := by
  simp only [extractGates, List.get_map, origIndexAt]

/-- extractGates is injective on original indices -/
lemma Subcircuit.extractGates_pos_injective {din dout : Nat} {C : Circuit din dout} {S : Subcircuit C}
    {pi pj : Nat} (hpi : pi < S.extractGates.length) (hpj : pj < S.extractGates.length)
    (h_orig_eq : S.origIndexAt pi (by simp [extractGates] at hpi; exact hpi) =
                 S.origIndexAt pj (by simp [extractGates] at hpj; exact hpj)) :
    pi = pj :=
  origIndexAt_injective _ _ h_orig_eq

/-- The induced circuit on subcircuit S -/
def Circuit.induced {din dout : Nat} (C : Circuit din dout) (S : Subcircuit C) : Circuit din dout where
  gates := S.extractGates
  inputWires := S.inp.toList
  outputWires := S.out.toList
  inputWires_nodup := Finset.nodup_toList _
  outputWires_nodup := Finset.nodup_toList _
  inputs_not_outputs := by
    classical
    intro w hw_inp i hi m
    -- w ∈ S.inp means w ∈ S.allInputWires \ S.allOutputWires
    simp only [Finset.mem_toList] at hw_inp
    have hw_not_out := (Finset.mem_sdiff.mp hw_inp).2
    intro heq
    -- If gate i outputs w, then w ∈ S.allOutputWires
    apply hw_not_out
    obtain ⟨ι, hιS, hgate_eq⟩ := S.extractGates_get_orig i hi
    simp only [Subcircuit.allOutputWires, Finset.mem_biUnion, Finset.mem_image, Finset.mem_univ,
               true_and]
    exact ⟨ι, hιS, m, by rw [← hgate_eq]; exact heq.symm⟩
  unique_drivers := by
    classical
    intro i j hi hj mi mj heq
    -- Get the canonical original indices using origIndexAt
    have hi_idx : i < S.extractIndices.length := by simp [Subcircuit.extractGates] at hi; exact hi
    have hj_idx : j < S.extractIndices.length := by simp [Subcircuit.extractGates] at hj; exact hj
    -- The gates at positions i and j
    have ⟨hgate_i, _⟩ := S.extractGates_get_orig_unique i hi
    have ⟨hgate_j, _⟩ := S.extractGates_get_orig_unique j hj
    -- The outputs are equal
    have heq' : (C.gates.get (S.origIndexAt i hi_idx)).outputs mi =
                (C.gates.get (S.origIndexAt j hj_idx)).outputs mj := by
      simp only [← hgate_i, ← hgate_j] at heq
      exact heq
    -- Use C.unique_drivers to show the original indices are equal
    have h_same := C.unique_drivers (S.origIndexAt i hi_idx).val (S.origIndexAt j hj_idx).val
      (S.origIndexAt i hi_idx).isLt (S.origIndexAt j hj_idx).isLt mi mj heq'
    have hι_eq : S.origIndexAt i hi_idx = S.origIndexAt j hj_idx := Fin.ext h_same
    exact S.origIndexAt_injective hi_idx hj_idx hι_eq
  topological := by
    classical
    intro i hi k
    -- Get the canonical original gate index using origIndexAt
    have hi_idx : i < S.extractIndices.length := by simp [Subcircuit.extractGates] at hi; exact hi
    let ι := S.origIndexAt i hi_idx
    have ⟨hgate_eq, hιS⟩ := S.extractGates_get_orig_unique i hi
    -- The wire we're checking
    let w := (S.extractGates.get ⟨i, hi⟩).inputs k
    -- Rewrite using the original gate
    have hw_eq : w = (C.gates.get ι).inputs k := by simp [w, hgate_eq]
    -- Apply original topological condition
    have htopo := C.topological ι.val ι.isLt k
    rw [← hw_eq] at htopo
    -- Case split: either from primary inputs or from earlier gate
    rcases htopo with hw_inp | ⟨j, hj_lt, m, hm_out⟩
    · -- Case 1: w comes from C.inputWires
      have hw_allInp : w ∈ S.allInputWires := by
        simp only [Subcircuit.allInputWires, Finset.mem_biUnion, Finset.mem_image, Finset.mem_univ,
                   true_and]
        exact ⟨ι, hιS, k, rfl⟩
      have hw_notOut : w ∉ S.allOutputWires := by
        intro hw_out
        simp only [Subcircuit.allOutputWires, Finset.mem_biUnion, Finset.mem_image,
                   Finset.mem_univ, true_and] at hw_out
        obtain ⟨ι', _, m', hm'⟩ := hw_out
        have := C.inputs_not_outputs w hw_inp ι'.val ι'.isLt m'
        exact this hm'.symm
      left
      simp only [Finset.mem_toList]
      exact Finset.mem_sdiff.mpr ⟨hw_allInp, hw_notOut⟩
    · -- Case 2: w is output of gate j < ι in original circuit
      let jFin : Fin C.gates.length := ⟨j, Nat.lt_trans hj_lt ι.isLt⟩
      by_cases hjS : jFin ∈ S.gateIndices
      · -- Gate j is in S: find its position and show it's earlier than i
        right
        -- jFin < ι and both in S.gateIndices, so position of jFin < i
        have hj_lt_ι : jFin < ι := hj_lt
        obtain ⟨pj, ppj, hpj_lt, hpj_get_i, hpj_get_j⟩ :=
          S.extractGates_preserves_order hjS hιS hj_lt_ι
        -- pj is the position of jFin in extractGates, and pj < pi where pi is position of ι
        -- But we need to show pj < i
        -- hpj_get_j says extractGates.get pj = C.gates.get jFin
        -- hpj_get_i says extractGates.get pi = C.gates.get ι
        -- Since ι = origIndexAt i, and extractGates.get i = C.gates.get ι,
        -- we have pi = i (the positions are the same)
        -- Actually extractGates_preserves_order returns pi such that extractGates.get pi = C.gates.get ι
        -- We need to verify pi = i
        have hpi_eq_i : ppj = i := by
          -- extractGates.get ppj = C.gates.get ι
          -- extractGates.get i = C.gates.get (origIndexAt i) = C.gates.get ι
          -- By injectivity of origIndexAt, the positions must be equal
          have h1 : S.extractGates.get ⟨ppj, hpj_lt⟩ = C.gates.get ι := hpj_get_i
          have h2 : S.extractGates.get ⟨i, hi⟩ = C.gates.get ι := hgate_eq
          -- origIndexAt ppj = ι and origIndexAt i = ι
          sorry
        subst hpi_eq_i
        refine ⟨pj, hpj_lt, hpj_lt, m, ?_⟩
        simp only [hpj_get_j]
        exact hm_out
      · -- Gate j is not in S: w is external to S, so w ∈ S.inp
        left
        have hw_allInp : w ∈ S.allInputWires := by
          simp only [Subcircuit.allInputWires, Finset.mem_biUnion, Finset.mem_image,
                     Finset.mem_univ, true_and]
          exact ⟨ι, hιS, k, rfl⟩
        have hw_notOut : w ∉ S.allOutputWires := by
          intro hw_out
          simp only [Subcircuit.allOutputWires, Finset.mem_biUnion, Finset.mem_image,
                     Finset.mem_univ, true_and] at hw_out
          obtain ⟨ι', hι'S, m', hm'⟩ := hw_out
          have h_same := C.unique_drivers ι'.val j ι'.isLt (Nat.lt_trans hj_lt ι.isLt) m' m
          have : ι'.val = j := h_same (hm'.symm.trans hm_out)
          have : jFin = ι' := Fin.ext this.symm
          rw [this] at hjS
          exact hjS hι'S
        simp only [Finset.mem_toList]
        exact Finset.mem_sdiff.mpr ⟨hw_allInp, hw_notOut⟩

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
  classical
  intro x
  have len_inp_eq : C.inputWires.length = C'.inputWires.length := congrArg List.length h_inp
  have len_out_eq : C.outputWires.length = C'.outputWires.length := congrArg List.length h_out
  -- Instantiate h with reindexed input
  have hx := h (fun i => x (Fin.cast len_inp_eq i))
  simp only [FunctionallyEquivalent'] at hx ⊢
  funext k
  -- Use hx at the corresponding index
  have hk := congrFun hx.symm (Fin.cast len_out_eq.symm k)
  simp only [Fin.cast_trans, Fin.cast_eq_self] at hk
  convert hk using 2
  · funext i
    simp only [Fin.cast_trans, Fin.cast_eq_self]
  · simp only [Fin.cast_trans, Fin.cast_eq_self]

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
  have len_inp_eq' := congrArg List.length h_inp'
  have len_out_eq := congrArg List.length h_out
  have len_out_eq' := congrArg List.length h_out'
  -- First equivalence
  have eq1 := h1 x
  -- Second equivalence with reindexed input
  have eq2 := h2 (fun i => x (Fin.cast len_inp_eq.symm i))
  simp only [FunctionallyEquivalent'] at eq1 eq2 ⊢
  funext k
  -- Chain the two equalities
  have hk1 := congrFun eq1 k
  have hk2 := congrFun eq2 (Fin.cast len_out_eq k)
  simp only [Fin.cast_trans] at hk2 ⊢
  rw [hk1, hk2]
  congr 1
  · funext i
    simp only [Fin.cast_trans]
  · simp only [Fin.cast_trans]

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
  -- The goal reduces to showing C.eval x = C'.eval x' where x' is x reindexed
  -- Since inputs_eq, the reindexing is trivial
  have len_inp_eq := congrArg List.length htopo.inputs_eq
  have len_out_eq := congrArg List.length htopo.outputs_eq
  funext k
  simp only [Circuit.eval]
  -- Show initValuation produces same result
  have hσ₀ : initValuation C x = initValuation C' (fun i => x (Fin.cast len_inp_eq.symm i)) :=
    initValuation_eq_of_inputs_eq htopo.inputs_eq x
  -- Show evalGates produces same result when gates have same structure and ops
  have hgates_eq : C.gates = C'.gates := by
    apply List.ext_get
    · exact htopo.len_eq
    · intro i hi hi'
      have hmatch := htopo.gates_match i hi
      have hop := hops i hi
      rcases hmatch with ⟨hid, hinputs, houtputs⟩
      ext
      · exact hid
      · exact hinputs
      · exact houtputs
      · exact hop
  have hσ : evalGates C.gates (initValuation C x) =
            evalGates C'.gates (initValuation C' (fun i => x (Fin.cast len_inp_eq.symm i))) := by
    rw [hσ₀, hgates_eq]
  -- Finally, output wires are the same
  simp only [htopo.outputs_eq] at *
  rw [hσ]
  congr 1
  simp only [Fin.cast_trans, Fin.cast_eq_self]

end MaDaiShi
