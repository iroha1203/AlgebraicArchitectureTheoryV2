import Formal.SHIGURE.Part1.ContextSelectedProofs

/-! # Evaluating expressions in the selected signature

A comparison identifies the full carrier of each retained sort. It reads
exactly the same primitive facts. The resulting agreement includes scopes
with no inhabitants, quantified witnesses, and all arguments of a Law.
-/

universe u

namespace SHIGURE
namespace DeclarationContext.Selected

variable {P : PrimitivePresentation.{u}} {U : DeclarationContext P}

section Selection

variable {X : P.signature.SortType → Type u} {Y : SortName U → Type u}

/-- The correspondence identifies each retained carrier as a whole. -/
abbrev CarrierEquiv (U : DeclarationContext P) (X : P.signature.SortType → Type u) (Y : SortName U → Type u) :=
  ∀ s (keep : Declaration.sort s ∈ U.declarations), X s ≃ Y ⟨s, keep⟩

/-- Each original position maps to its selected position with the corresponding value. -/
def selectAssignment (e : CarrierEquiv U X Y) {Γ : List P.signature.SortType}
    (keep : Declaration.sorts Γ ⊆ U.declarations) (a : Assignment X Γ) : Assignment Y (context Γ keep) :=
  ⟨fun {s} i => e s.val s.property (a (ambientVar keep i))⟩

/-- The inverse assignment reads original values from the selected positions. -/
def ambientAssignment (e : CarrierEquiv U X Y) {Γ : List P.signature.SortType}
    (keep : Declaration.sorts Γ ⊆ U.declarations) (a : Assignment Y (context Γ keep)) : Assignment X Γ :=
  ⟨fun i => (e _ (varKept keep i)).symm (a (selectVar keep i))⟩

/-- Selecting an assignment reads its ambient coordinate through the carrier equivalence. -/
theorem selectAssignment_apply (e : CarrierEquiv U X Y) {Γ : List P.signature.SortType}
    (keep : Declaration.sorts Γ ⊆ U.declarations) (a : Assignment X Γ)
    {s : SortName U} (i : Var (context Γ keep) s) :
    selectAssignment e keep a i = e s.val s.property (a (ambientVar keep i)) :=
  rfl

/-- Reading an ambient assignment takes the inverse carrier equivalence at the selected coordinate. -/
theorem ambientAssignment_apply (e : CarrierEquiv U X Y) {Γ : List P.signature.SortType}
    (keep : Declaration.sorts Γ ⊆ U.declarations) (a : Assignment Y (context Γ keep))
    {s : P.signature.SortType} (i : Var Γ s) :
    ambientAssignment e keep a i = (e s (varKept keep i)).symm (a (selectVar keep i)) :=
  rfl

/-- The selected value at a retained variable is its original value under the carrier equivalence. -/
@[simp] theorem selectAssignment_selectVar (e : CarrierEquiv U X Y) {Γ : List P.signature.SortType}
    (keep : Declaration.sorts Γ ⊆ U.declarations) (a : Assignment X Γ) {s : P.signature.SortType} (i : Var Γ s) :
    selectAssignment e keep a (selectVar keep i) = e s (varKept keep i) (a i) := by
  change e s _ (a (ambientVar keep (selectVar keep i))) = _
  rw [ambientVar_selectVar keep i]

/-- Reading back a selected assignment is the original assignment. -/
@[simp] theorem ambientAssignment_selectAssignment (e : CarrierEquiv U X Y) {Γ : List P.signature.SortType}
    (keep : Declaration.sorts Γ ⊆ U.declarations) (a : Assignment X Γ) :
    ambientAssignment e keep (selectAssignment e keep a) = a := by
  apply Assignment.ext
  intro s i
  change (e s _).symm (selectAssignment e keep a (selectVar keep i)) = a i
  rw [selectAssignment_selectVar e keep a i, Equiv.symm_apply_apply]

/-- Selecting the inverse assignment recovers the selected assignment. -/
@[simp] theorem selectAssignment_ambientAssignment (e : CarrierEquiv U X Y) {Γ : List P.signature.SortType}
    (keep : Declaration.sorts Γ ⊆ U.declarations) (a : Assignment Y (context Γ keep)) :
    selectAssignment e keep (ambientAssignment e keep a) = a := by
  apply Assignment.ext
  intro s i
  change e s.val s.property ((e s.val _).symm (a (selectVar keep (ambientVar keep i)))) = a i
  rw [selectVar_ambientVar keep i, Equiv.apply_symm_apply]

/-- The correspondence of retained assignments is a bijection. -/
def assignmentEquiv (e : CarrierEquiv U X Y) {Γ : List P.signature.SortType}
    (keep : Declaration.sorts Γ ⊆ U.declarations) : Assignment X Γ ≃ Assignment Y (context Γ keep) where
  toFun := selectAssignment e keep
  invFun := ambientAssignment e keep
  left_inv := ambientAssignment_selectAssignment e keep
  right_inv := selectAssignment_ambientAssignment e keep

/-- The assignment equivalence in Proposition 3.2 sends an assignment to its
selected values using the carrier equivalences on the retained sorts. -/
theorem assignmentEquiv_apply (e : CarrierEquiv U X Y) {Γ : List P.signature.SortType}
    (keep : Declaration.sorts Γ ⊆ U.declarations) (a : Assignment X Γ) :
    assignmentEquiv e keep a = selectAssignment e keep a :=
  rfl

/-- Selecting an assignment commutes with reading a subcontext of its variable positions. -/
theorem selectAssignment_pull (e : CarrierEquiv U X Y) {Γ Δ : List P.signature.SortType}
    (keepΓ : Declaration.sorts Γ ⊆ U.declarations) (keepΔ : Declaration.sorts Δ ⊆ U.declarations)
    (a : Assignment X Δ) (ρ : Renaming Γ Δ) :
    (selectAssignment e keepΔ a).pull (selectRenaming keepΓ keepΔ ρ) = selectAssignment e keepΓ (a.pull ρ) := by
  apply Assignment.ext
  intro s i
  change e s.val _ (a (ambientVar keepΔ (selectVar keepΔ (ρ (ambientVar keepΓ i))))) = _
  rw [ambientVar_selectVar keepΔ (ρ (ambientVar keepΓ i))]
  rfl

/-- Selecting an extended assignment keeps the bound witness as the new first coordinate. -/
theorem selectAssignment_cons (e : CarrierEquiv U X Y) {Γ : List P.signature.SortType} {s : P.signature.SortType}
    (keepS : Declaration.sort s ∈ U.declarations) (keepΓ : Declaration.sorts Γ ⊆ U.declarations)
    (x : X s) (a : Assignment X Γ) :
    selectAssignment e (Declaration.sorts_cons_subset keepS keepΓ) (Assignment.cons x a) =
      Assignment.cons (s := (⟨s, keepS⟩ : SortName U)) (e s keepS x) (selectAssignment e keepΓ a) := by
  apply Assignment.ext
  intro t i
  cases i <;> rfl

/-- Moving an input tuple to the selected operation uses its selected arity. -/
def selectArgs (e : CarrierEquiv U X Y) (op : Operation P.signature)
    (keep : Declaration.ofOperation op ∈ U.declarations) (a : Assignment X op.arity.inputs) :
    Assignment Y (operation op keep).arity.inputs :=
  cast (congrArg (fun profile => Assignment Y profile.inputs) (operation_arity op keep).symm)
    (selectAssignment e (operationInputs op keep) a)

/-- Moving an output value to the selected operation uses its selected result sort. -/
def selectResult (e : CarrierEquiv U X Y) (op : Operation P.signature)
    (keep : Declaration.ofOperation op ∈ U.declarations) (x : X op.arity.output) :
    Y (operation op keep).arity.output :=
  cast (congrArg (fun profile => Y profile.output) (operation_arity op keep).symm)
    (e op.arity.output (operationOutput op keep) x)

/-- In the graph comparison for Proposition 3.2, select the input values and
transport the tuple along the arity equality for the retained operation. -/
theorem selectArgs_eq_cast (e : CarrierEquiv U X Y) (op : Operation P.signature)
    (keep : Declaration.ofOperation op ∈ U.declarations) (a : Assignment X op.arity.inputs) :
    selectArgs e op keep a =
      cast (congrArg (fun profile => Assignment Y profile.inputs) (operation_arity op keep).symm)
        (selectAssignment e (operationInputs op keep) a) :=
  rfl

/-- In the graph comparison for Proposition 3.2, select the output value and
transport it along the arity equality for the retained operation. -/
theorem selectResult_eq_cast (e : CarrierEquiv U X Y) (op : Operation P.signature)
    (keep : Declaration.ofOperation op ∈ U.declarations) (x : X op.arity.output) :
    selectResult e op keep x =
      cast (congrArg (fun profile => Y profile.output) (operation_arity op keep).symm)
        (e op.arity.output (operationOutput op keep) x) :=
  rfl

/-- For a retained total operation, the output comparison of Proposition 3.2
is the equivalence on its output carrier. The missing-graph example uses this form. -/
theorem selectResult_total (e : CarrierEquiv U X Y) (f : P.signature.Total)
    (keep : Declaration.total f ∈ U.declarations) (x : X (P.signature.totalArity f).output) :
    selectResult e (.total f) keep x =
      e _ (operationOutput (.total f) keep) x :=
  rfl

end Selection

section CarrierTransport

variable {X Y : P.signature.SortType → Type u} {Z : SortName U → Type u}

/-- Compare the assignments used in Proposition 3.2 when the two carrier
transports agree pointwise. In the structure round trip this agreement comes
from the equality of the original and round-trip carriers. -/
theorem selectAssignment_mapCarrier (e : CarrierEquiv U Y Z) (f : CarrierMap U X Y) (g : CarrierEquiv U X Z)
    (agree : ∀ s keep x, e s keep (f s keep x) = g s keep x) {Γ : List P.signature.SortType}
    (kept : Declaration.sorts Γ ⊆ U.declarations) (a : Assignment X Γ) :
    selectAssignment e kept (mapAssignment f kept a) = selectAssignment g kept a := by
  apply Assignment.ext
  intro s i
  change e s.val s.property (mapAssignment f kept a (ambientVar kept i)) =
    g s.val s.property (a (ambientVar kept i))
  rw [mapAssignment_apply]
  exact agree s.val s.property (a (ambientVar kept i))

/-- Transport the input side of the graph comparison in Proposition 3.2.
The retained operation supplies its input support. The structure round trip
proves `agree` by identifying the carrier transports at every kept sort. -/
theorem selectArgs_mapCarrier (e : CarrierEquiv U Y Z) (f : CarrierMap U X Y) (g : CarrierEquiv U X Z)
    (agree : ∀ s keep x, e s keep (f s keep x) = g s keep x) (op : Operation P.signature)
    (kept : Declaration.ofOperation op ∈ U.declarations) (a : Assignment X op.arity.inputs) :
    selectArgs e op kept (mapAssignment f (operationInputs op kept) a) = selectArgs g op kept a := by
  simp only [selectArgs, selectAssignment_mapCarrier e f g agree]

/-- Transport the output side of the graph comparison in Proposition 3.2.
The retained operation supplies its output support. The structure round trip
proves `agree` by identifying the carrier transports at every kept sort. -/
theorem selectResult_mapCarrier (e : CarrierEquiv U Y Z) (f : CarrierMap U X Y) (g : CarrierEquiv U X Z)
    (agree : ∀ s keep x, e s keep (f s keep x) = g s keep x) (op : Operation P.signature)
    (kept : Declaration.ofOperation op ∈ U.declarations) (x : X op.arity.output) :
    selectResult e op kept (f _ (operationOutput op kept) x) = selectResult g op kept x := by
  simp only [selectResult, agree]

end CarrierTransport

variable {X : P.signature.SortType → Type u} {Y : SortName U → Type u}

/-- The primitive evaluations have the same facts after the given carrier identifications. -/
structure EvaluationMatches (E : RestrictedEvaluation U X) (B : Structure (signature U))
    (e : CarrierEquiv U X B.carrier) : Prop where
  /-- Retained relation facts agree. -/
  relation (r : P.signature.Rel) (keep : Declaration.relation r ∈ U.declarations)
    (a : Assignment X (P.signature.relInputs r)) :
    B.relation ⟨r, keep⟩ (selectAssignment e (relationInputs r keep) a) ↔ E.relation r keep a
  /-- Retained domains have the same defined inputs. -/
  domain (p : P.signature.Partial) (keep : Declaration.partialOp p ∈ U.declarations)
    (a : Assignment X (P.signature.partialArity p).inputs) :
    B.partialDomain ⟨p, keep⟩ (selectAssignment e (operationInputs (.partialOp p) keep) a) ↔ E.domain p keep a
  /-- Retained graphs give the same values. -/
  graph (op : Operation P.signature) (keep : Declaration.ofOperation op ∈ U.declarations)
    (a : Assignment X op.arity.inputs) (x : X op.arity.output) :
    B.Graph (operation op keep) (selectArgs e op keep a) (selectResult e op keep x) ↔ E.graph op keep a x

namespace EvaluationMatches

variable {E : RestrictedEvaluation U X} {B : Structure (signature U)} {e : CarrierEquiv U X B.carrier}
  (same : EvaluationMatches E B e)

include same

/-- The atomic step of Proposition 3.2 uses the carrier equivalences for equality
and the supplied primitive comparisons for retained relation, domain and graph atoms. -/
theorem atomic_iff {Γ : List P.signature.SortType} (a : Atomic P.signature Γ)
    (keep : Declaration.atomicSupport a ⊆ U.declarations) (x : Assignment X Γ) :
    (selectAtomic a keep).Holds B (selectAssignment e ((Declaration.sorts_subset_atomicSupport a).trans keep) x) ↔ E.atomic x a keep := by
  let free : Declaration.sorts Γ ⊆ U.declarations := (Declaration.sorts_subset_atomicSupport a).trans keep
  cases a with
  | eq l r =>
    rw [selectAtomic_eq, Atomic.holds_eq, RestrictedEvaluation.atomic_eq_iff]
    rw [selectAssignment_selectVar, selectAssignment_selectVar]
    exact ⟨fun h => (e _ _).injective h, fun h => congrArg (e _ _) h⟩
  | rel r vars =>
    let k : Declaration.relation r ∈ U.declarations := keep (Declaration.relation_mem_atomicSupport r vars)
    rw [selectAtomic_rel, Atomic.holds_rel, RestrictedEvaluation.atomic_rel_iff]
    erw [selectAssignment_pull e (relationInputs r k) free x vars]
    exact same.relation r k (x.pull vars)
  | domain p vars =>
    let k : Declaration.partialOp p ∈ U.declarations := keep (Declaration.domain_mem_atomicSupport p vars)
    rw [selectAtomic_domain, Atomic.holds_domain, RestrictedEvaluation.atomic_domain_iff]
    erw [selectAssignment_pull e (operationInputs (.partialOp p) k) free x vars]
    exact same.domain p k (x.pull vars)
  | graph op vars y =>
    let k : Declaration.ofOperation op ∈ U.declarations := keep (Declaration.graph_mem_atomicSupport op vars y)
    have args := selectAssignment_pull e (operationInputs op k) free x vars
    have out := selectAssignment_selectVar e free x y
    rw [selectAtomic_graph, RestrictedEvaluation.atomic_graph_iff]
    cases op <;> simp only [selectGraph_total, selectGraph_partialOp, selectGraph_quantity, Atomic.holds_graph]
    all_goals
      erw [args, out]
      simpa only [selectArgs_eq_cast, selectResult_eq_cast, cast_eq] using
        same.graph _ k (x.pull vars) (x y)

/-- Any supported formula has the same truth in the actual selected structure. -/
theorem formula_iff {Γ : List P.signature.SortType} (p : Formula P.signature Γ) :
    ∀ (keep : Declaration.formulaSupport p ⊆ U.declarations) (x : Assignment X Γ),
      (selectFormula p keep).Holds B (selectAssignment e ((Declaration.sorts_subset_formulaSupport p).trans keep) x) ↔ E.holds p keep x := by
  induction p with
  | atom a =>
    intro keep x
    rw [selectFormula_atom, Formula.holds_atom, RestrictedEvaluation.holds_atom_iff]
    exact same.atomic_iff a ((Declaration.formulaSupport_atom a).ge.trans keep) x
  | truth =>
    intro keep x
    rw [selectFormula_truth, Formula.holds_truth_iff, RestrictedEvaluation.holds_truth_iff]
  | falsehood =>
    intro keep x
    rw [selectFormula_falsehood, Formula.holds_falsehood_iff, RestrictedEvaluation.holds_falsehood_iff]
  | conj p q hp hq =>
    intro keep x
    rw [selectFormula_conj, Formula.holds_conj, RestrictedEvaluation.holds_conj_iff]
    exact and_congr (hp ((Declaration.binarySupport_left (Declaration.formula_conj p q)).trans keep) x)
      (hq ((Declaration.binarySupport_right (Declaration.formula_conj p q)).trans keep) x)
  | disj p q hp hq =>
    intro keep x
    rw [selectFormula_disj, Formula.holds_disj, RestrictedEvaluation.holds_disj_iff]
    exact or_congr (hp ((Declaration.binarySupport_left (Declaration.formula_disj p q)).trans keep) x)
      (hq ((Declaration.binarySupport_right (Declaration.formula_disj p q)).trans keep) x)
  | @ex Γ s p ih =>
    intro keep x
    let kept : Declaration.sort s ∈ U.declarations := keep (Declaration.boundSort_mem_formulaSupport p)
    let free : Declaration.sorts Γ ⊆ U.declarations := (Declaration.sorts_subset_formulaSupport p.ex).trans keep
    rw [selectFormula_ex, Formula.holds_ex, RestrictedEvaluation.holds_ex_iff]
    constructor
    · rintro ⟨y, truth⟩
      refine ⟨(e s kept).symm y, (ih (existsSupport keep) _).1 ?_⟩
      rw [selectAssignment_cons e kept free, Equiv.apply_symm_apply]
      exact truth
    · rintro ⟨y, truth⟩
      refine ⟨e s kept y, ?_⟩
      have typed := (ih (existsSupport keep) (Assignment.cons y x)).2 truth
      rw [selectAssignment_cons e kept free] at typed
      exact typed

/-- A supported Law has exactly the same input and conclusion tests in the selected signature. -/
theorem law_iff (law : Law P.signature) (keep : Declaration.lawBody law ⊆ U.declarations) :
    (selectLaw law keep).Holds B ↔ E.satisfies law keep := by
  constructor
  · intro held x input
    exact (same.formula_iff law.conclusion (lawConclusionSupport keep) x).1
      (held _ ((same.formula_iff law.input (lawInputSupport keep) x).2 input))
  · intro held x input
    let free := lawSortSupport keep
    obtain ⟨a, rfl⟩ := (assignmentEquiv e free).surjective x
    exact (same.formula_iff law.conclusion (lawConclusionSupport keep) a).2
      (held a ((same.formula_iff law.input (lawInputSupport keep) a).1 input))

end EvaluationMatches
end DeclarationContext.Selected
end SHIGURE
