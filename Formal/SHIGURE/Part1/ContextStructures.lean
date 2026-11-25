import Formal.SHIGURE.Part1.ContextEvaluation

/-! # Structures over a declaration context

Only retained primitive data occur in a context structure. Graphs encode the
actual operations by functionality and existence on their domains. The
ambient sort index lets us reuse typed syntax and quantifiers. Every erased
sort is assigned the same inert carrier, so it contributes no object data.

## Implementation notes

Using the ordinary structure directly would require transporting dependent
partial-value functions at each overlap. Graphs can be assembled as facts;
their unique functions and the ordinary selected-signature structure are
recovered in ContextPrimitiveValues and ContextSelectedStructures.
-/

universe u

namespace SHIGURE
namespace DeclarationContext

variable {P : PrimitivePresentation.{u}} {U : DeclarationContext P}

/-- A Law's written support includes the support of its input formula. -/
theorem lawInputSupport {law : Law P.signature} (support : Declaration.lawBody law ⊆ U.declarations) :
    Declaration.formulaSupport law.input ⊆ U.declarations :=
  (Declaration.formulaSupport_input_subset_lawBody law).trans support

/-- A Law's written support includes the support of its conclusion. -/
theorem lawConclusionSupport {law : Law P.signature} (support : Declaration.lawBody law ⊆ U.declarations) :
    Declaration.formulaSupport law.conclusion ⊆ U.declarations :=
  (Declaration.formulaSupport_conclusion_subset_lawBody law).trans support

/-- The Law's assignment context is part of both of its sides' supports. -/
theorem lawSortSupport {law : Law P.signature} (support : Declaration.lawBody law ⊆ U.declarations) :
    Declaration.sorts law.context ⊆ U.declarations :=
  (Declaration.sorts_subset_lawBody law).trans support

/-- A graph axiom can be written in any context keeping its primitive symbol. -/
theorem graphRuleSupport (rule : GraphAxiom P.signature)
    (kept : Declaration.graphRuleName rule ∈ U.declarations) :
    Declaration.lawBody rule.toLaw ⊆ U.declarations := by
  cases rule with
  | functional op =>
    rw [Declaration.graphRuleName_functional] at kept
    have inputs := operationInputs op kept
    have output := operationOutput op kept
    simp only [GraphAxiom.toLaw_functional, Declaration.lawBody_eq, Declaration.formula_conj,
      Declaration.formula_atom, Declaration.atomic_eq, Declaration.atomic_graph,
      Set.union_self, Set.union_empty]
    exact Set.union_subset (Declaration.sorts_cons_subset output (Declaration.sorts_cons_subset output inputs))
      (Set.singleton_subset_iff.mpr kept)
  | totality f =>
    rw [Declaration.graphRuleName_totality, ← Declaration.ofOperation_total] at kept
    have inputs := operationInputs (.total f) kept
    have output := operationOutput (.total f) kept
    simp only [GraphAxiom.toLaw_totality, GraphAxiom.hasOutput_eq_ex_graph, Declaration.lawBody_eq,
      Declaration.formula_truth, Declaration.formula_ex, Declaration.formula_atom, Declaration.atomic_graph,
      Set.union_empty, Set.union_subset_iff, Set.singleton_subset_iff]
    exact ⟨inputs, output, kept⟩
  | quantityTotality q =>
    rw [Declaration.graphRuleName_quantityTotality, ← Declaration.ofOperation_quantity] at kept
    have inputs := operationInputs (.quantity q) kept
    have output := operationOutput (.quantity q) kept
    simp only [GraphAxiom.toLaw_quantityTotality, GraphAxiom.hasOutput_eq_ex_graph, Declaration.lawBody_eq,
      Declaration.formula_truth, Declaration.formula_ex, Declaration.formula_atom, Declaration.atomic_graph,
      Set.union_empty, Set.union_subset_iff, Set.singleton_subset_iff]
    exact ⟨inputs, output, kept⟩
  | graphImpliesDomain p =>
    rw [Declaration.graphRuleName_graphImpliesDomain] at kept
    have inputs := operationInputs (.partialOp p) (by rwa [Declaration.ofOperation_partialOp])
    have output := operationOutput (.partialOp p) (by rwa [Declaration.ofOperation_partialOp])
    simp only [GraphAxiom.toLaw_graphImpliesDomain, Declaration.lawBody_eq, Declaration.formula_atom,
      Declaration.atomic_graph, Declaration.atomic_domain, Declaration.ofOperation_partialOp, Set.union_subset_iff, Set.singleton_subset_iff]
    exact ⟨⟨Declaration.sorts_cons_subset output inputs, kept⟩, kept⟩
  | domainImpliesGraph p =>
    rw [Declaration.graphRuleName_domainImpliesGraph] at kept
    have inputs := operationInputs (.partialOp p) (by rwa [Declaration.ofOperation_partialOp])
    have output := operationOutput (.partialOp p) (by rwa [Declaration.ofOperation_partialOp])
    simp only [GraphAxiom.toLaw_domainImpliesGraph, GraphAxiom.hasOutput_eq_ex_graph, Declaration.lawBody_eq,
      Declaration.formula_atom, Declaration.formula_ex, Declaration.atomic_graph, Declaration.atomic_domain, Declaration.ofOperation_partialOp,
      Set.union_subset_iff, Set.singleton_subset_iff]
    exact ⟨⟨inputs, kept⟩, output, kept⟩

/-- Onto maps at the retained sorts give an onto map on any supported assignment space. -/
theorem mapAssignment_surjective {X Y : P.signature.SortType → Type u} (f : CarrierMap U X Y)
    (surj : ∀ s kept, Function.Surjective (f s kept)) {Γ : List P.signature.SortType}
    (keep : Declaration.sorts Γ ⊆ U.declarations) : Function.Surjective (mapAssignment f keep) := by
  intro y
  let x : Assignment X Γ := ⟨fun var => Classical.choose (surj _ (varKept keep var) (y var))⟩
  refine ⟨x, Assignment.ext ?_⟩
  intro s var
  rw [mapAssignment_apply]
  exact Classical.choose_spec (surj _ (varKept keep var) (y var))

/-- A retained sort keeps its whole carrier; every other sort has a canonical inert carrier. -/
noncomputable def selectedCarrier (U : DeclarationContext P) (X : P.signature.SortType → Type u)
    (s : P.signature.SortType) : Type u := by
  classical
  exact if Declaration.sort s ∈ U.declarations then X s else PUnit

/-- A retained carrier is the original carrier as a type, including empty cases. -/
theorem selectedCarrier_kept (X : P.signature.SortType → Type u) {s : P.signature.SortType}
    (kept : Declaration.sort s ∈ U.declarations) : selectedCarrier U X s = X s := by
  classical
  simp only [selectedCarrier, if_pos kept]

/-- An omitted carrier always has the same inert type. -/
theorem selectedCarrier_omitted (X : P.signature.SortType → Type u) {s : P.signature.SortType}
    (omitted : Declaration.sort s ∉ U.declarations) : selectedCarrier U X s = PUnit := by
  classical
  simp only [selectedCarrier, if_neg omitted]

/-- Identify each retained carrier with the original type. -/
noncomputable def selectedMap (U : DeclarationContext P) (X : P.signature.SortType → Type u) :
    CarrierMap U (selectedCarrier U X) X :=
  fun _ kept => cast (selectedCarrier_kept X kept)

/-- The retained carrier identification computes by transport along its exact type equality. -/
theorem selectedMap_apply (U : DeclarationContext P) (X : P.signature.SortType → Type u)
    (s : P.signature.SortType) (kept : Declaration.sort s ∈ U.declarations) (x : selectedCarrier U X s) :
    selectedMap U X s kept x = cast (selectedCarrier_kept X kept) x :=
  rfl

/-- Retention does not omit any element of a selected carrier. -/
theorem selectedMap_bijective (X : P.signature.SortType → Type u) (s : P.signature.SortType)
    (kept : Declaration.sort s ∈ U.declarations) : Function.Bijective (selectedMap U X s kept) :=
  (Equiv.cast (selectedCarrier_kept X kept)).bijective

end DeclarationContext

namespace RestrictedEvaluation

open DeclarationContext

variable {P : PrimitivePresentation.{u}} {U V : DeclarationContext P} {X Y : P.signature.SortType → Type u}

/-- A supported Law holds when its conclusion holds at every input satisfying its premise. -/
def satisfies (A : RestrictedEvaluation U X) (law : Law P.signature)
    (support : Declaration.lawBody law ⊆ U.declarations) : Prop :=
  ∀ e : Assignment X law.context, A.holds law.input (lawInputSupport support) e →
    A.holds law.conclusion (lawConclusionSupport support) e

/-- A restricted Law compares the evaluations of its input and conclusion. -/
theorem satisfies_iff (A : RestrictedEvaluation U X) (law : Law P.signature)
    (support : Declaration.lawBody law ⊆ U.declarations) :
    A.satisfies law support ↔
      ∀ e : Assignment X law.context, A.holds law.input (lawInputSupport support) e →
        A.holds law.conclusion (lawConclusionSupport support) e :=
  Iff.rfl

/-- An evaluation is structural exactly when its retained graph axioms hold. -/
def Structural (A : RestrictedEvaluation U X) : Prop :=
  ∀ rule : GraphAxiom P.signature, ∀ kept : Declaration.graphRuleName rule ∈ U.declarations,
    A.satisfies rule.toLaw (graphRuleSupport rule kept)

/-- Structural evaluation is exactly the satisfaction of the graph axioms at retained primitives. -/
theorem structural_iff (A : RestrictedEvaluation U X) :
    A.Structural ↔ ∀ (rule : GraphAxiom P.signature) (kept : Declaration.graphRuleName rule ∈ U.declarations),
      A.satisfies rule.toLaw (graphRuleSupport rule kept) :=
  Iff.rfl

/-- A structural evaluation satisfies the graph axiom of each retained primitive. -/
theorem structural_rule (A : RestrictedEvaluation U X) (valid : A.Structural)
    (rule : GraphAxiom P.signature) (kept : Declaration.graphRuleName rule ∈ U.declarations) :
    A.satisfies rule.toLaw (graphRuleSupport rule kept) :=
  (A.structural_iff.1 valid) rule kept

/-- Truth of a supported Law transfers along restriction because the assignments correspond bijectively. -/
theorem satisfies_pullback_iff (A : RestrictedEvaluation U Y) (inside : V ≤ U) (f : CarrierMap V X Y)
    (bij : ∀ s kept, Function.Bijective (f s kept)) (law : Law P.signature)
    (support : Declaration.lawBody law ⊆ V.declarations) :
    (A.pullback inside f).satisfies law support ↔ A.satisfies law (fun _ hd => inside (support hd)) := by
  simp only [satisfies_iff]
  constructor
  · intro held e input
    obtain ⟨localE, rfl⟩ := mapAssignment_surjective f (fun s kept => (bij s kept).2)
      (lawSortSupport support) e
    have localInput := (A.holds_pullback_iff inside f bij law.input (lawInputSupport support) localE).2 input
    exact (A.holds_pullback_iff inside f bij law.conclusion (lawConclusionSupport support) localE).1
      (held localE localInput)
  · intro original e input
    have before := (A.holds_pullback_iff inside f bij law.input (lawInputSupport support) e).1 input
    exact (A.holds_pullback_iff inside f bij law.conclusion (lawConclusionSupport support) e).2
      (original (mapAssignment f (lawSortSupport support) e) before)

/-- A structural interpretation remains structural after forgetting declarations. -/
theorem structural_pullback (A : RestrictedEvaluation U Y) (inside : V ≤ U) (f : CarrierMap V X Y)
    (bij : ∀ s kept, Function.Bijective (f s kept)) (valid : A.Structural) :
    (A.pullback inside f).Structural := by
  rw [structural_iff]
  intro rule kept
  exact (A.satisfies_pullback_iff inside f bij rule.toLaw (graphRuleSupport rule kept)).2
    (A.structural_rule valid rule (inside kept))

/-- Reading the supported Law from an ambient structure gives its original satisfaction. -/
theorem satisfies_restrict_iff (U : DeclarationContext P) (A : Structure P.signature)
    (law : Law P.signature) (support : Declaration.lawBody law ⊆ U.declarations) :
    (restrict U A).satisfies law support ↔ law.Holds A := by
  rw [satisfies_iff, Law.holds_iff]
  constructor
  · intro held e he
    exact (restrict_holds_iff U A law.conclusion (lawConclusionSupport support) e).1
      (held e ((restrict_holds_iff U A law.input (lawInputSupport support) e).2 he))
  · intro held e he
    exact (restrict_holds_iff U A law.conclusion (lawConclusionSupport support) e).2
      (held e ((restrict_holds_iff U A law.input (lawInputSupport support) e).1 he))

/-- An ambient structure provides a structural interpretation on any retained context. -/
theorem restrict_structural (U : DeclarationContext P) (A : Structure P.signature) : (restrict U A).Structural := by
  rw [structural_iff]
  intro rule kept
  exact (satisfies_restrict_iff U A rule.toLaw (graphRuleSupport rule kept)).2 (rule.holds_toLaw A)

end RestrictedEvaluation

open DeclarationContext

/-- A structure over the restricted presentation, with exactly its retained interpretations. -/
structure ContextStructure {P : PrimitivePresentation.{u}} (U : DeclarationContext P) where
  /-- Each original sort has a type; the erased slots carry no chosen data. -/
  carrier : P.signature.SortType → Type u
  /-- A forgotten slot has the canonical inert carrier. -/
  omitted (s : P.signature.SortType) : Declaration.sort s ∉ U.declarations → carrier s = PUnit
  /-- The relation, domain and graph of each retained primitive. -/
  evaluation : RestrictedEvaluation U carrier
  /-- Retained operation graphs satisfy exactly their structural graph axioms. -/
  structural : evaluation.Structural

namespace ContextStructure

variable {P : PrimitivePresentation.{u}} {U V W : DeclarationContext P}

/-- Equality of the carrier family and of its transported evaluation gives structural equality. -/
theorem ext {A B : ContextStructure U} (carrier : A.carrier = B.carrier)
    (eval : cast (congrArg (RestrictedEvaluation U) carrier) A.evaluation = B.evaluation) : A = B := by
  cases A with
  | mk X omittedX RX validX =>
    cases B with
    | mk Y omittedY RY validY =>
      cases carrier
      cases eval
      rfl

/-- Omitted slots match automatically, so only retained carrier equalities need proofs. -/
theorem carrier_ext {A B : ContextStructure U}
    (keep : ∀ s, Declaration.sort s ∈ U.declarations → A.carrier s = B.carrier s) : A.carrier = B.carrier := by
  funext s
  by_cases hs : Declaration.sort s ∈ U.declarations
  · exact keep s hs
  · exact (A.omitted s hs).trans (B.omitted s hs).symm

/-- The reduct takes exactly the retained carriers and their primitive interpretation. -/
noncomputable def restrict (A : ContextStructure U) (inside : V ≤ U) : ContextStructure V where
  carrier := selectedCarrier V A.carrier
  omitted _ := selectedCarrier_omitted _
  evaluation := A.evaluation.pullback inside (selectedMap V A.carrier)
  structural := A.evaluation.structural_pullback inside _ (selectedMap_bijective A.carrier) A.structural

/-- Each local carrier identifies with its original retained carrier. -/
theorem restrict_carrier (A : ContextStructure U) (inside : V ≤ U) {s : P.signature.SortType}
    (kept : Declaration.sort s ∈ V.declarations) : (A.restrict inside).carrier s = A.carrier s :=
  selectedCarrier_kept A.carrier kept

/-- Read a full-signature structure at the retained declarations. -/
noncomputable def ofStructure (U : DeclarationContext P) (A : Structure P.signature) : ContextStructure U where
  carrier := selectedCarrier U A.carrier
  omitted _ := selectedCarrier_omitted _
  evaluation := (RestrictedEvaluation.restrict U A).pullback (le_refl U) (selectedMap U A.carrier)
  structural := (RestrictedEvaluation.restrict U A).structural_pullback (le_refl U) _
    (selectedMap_bijective A.carrier) (RestrictedEvaluation.restrict_structural U A)

/-- A retained graph in the reduct is the original graph on the same input and result values. -/
theorem ofStructure_graph_iff (U : DeclarationContext P) (A : Structure P.signature)
    (op : Operation P.signature) (keep : Declaration.ofOperation op ∈ U.declarations)
    (e : Assignment (ofStructure U A).carrier op.arity.inputs) (y : (ofStructure U A).carrier op.arity.output) :
    (ofStructure U A).evaluation.graph op keep e y ↔ A.Graph op
      (mapAssignment (selectedMap U A.carrier) (operationInputs op keep) e)
      (selectedMap U A.carrier _ (operationOutput op keep) y) :=
  Iff.rfl

/-- Retaining the support of a Law preserves its original satisfaction. -/
theorem ofStructure_satisfies_iff (U : DeclarationContext P) (A : Structure P.signature)
    (law : Law P.signature) (kept : Declaration.lawBody law ⊆ U.declarations) :
    (ofStructure U A).evaluation.satisfies law kept ↔ law.Holds A :=
  ((RestrictedEvaluation.restrict U A).satisfies_pullback_iff (le_refl U) _
    (selectedMap_bijective A.carrier) law kept).trans (RestrictedEvaluation.satisfies_restrict_iff U A law kept)

/-- Restriction evaluates by transporting to the original interpretations. -/
theorem restrict_evaluation (A : ContextStructure U) (inside : V ≤ U) :
    (A.restrict inside).evaluation = A.evaluation.pullback inside (selectedMap V A.carrier) :=
  rfl

/-- Keeping the whole declared context is precisely the identity restriction. -/
theorem restrict_id (A : ContextStructure U) : A.restrict (le_refl U) = A := by
  have same := carrier_ext (A := A.restrict (le_refl U)) (B := A)
    (fun s kept => A.restrict_carrier (le_refl U) (s := s) kept)
  apply ext same
  rw [RestrictedEvaluation.cast_evaluation _ same, restrict_evaluation, RestrictedEvaluation.pullback_comp]
  refine (RestrictedEvaluation.pullback_congr _ _ ?_).trans A.evaluation.pullback_id
  intro s kept x
  simp only [selectedMap_apply, cast_cast]
  rfl

/-- Repeated restrictions are strictly equal to their composite restriction. -/
theorem restrict_comp (A : ContextStructure U) (inside : V ≤ U) (smaller : W ≤ V) :
    (A.restrict inside).restrict smaller = A.restrict (smaller.trans inside) := by
  have same := carrier_ext (A := (A.restrict inside).restrict smaller)
    (B := A.restrict (smaller.trans inside)) (fun s kept =>
      ((A.restrict inside).restrict_carrier smaller (s := s) kept).trans
        ((A.restrict_carrier inside (smaller kept)).trans
          (A.restrict_carrier (smaller.trans inside) kept).symm))
  apply ext same
  rw [RestrictedEvaluation.cast_evaluation _ same]
  simp only [restrict_evaluation, RestrictedEvaluation.pullback_comp]
  apply RestrictedEvaluation.pullback_congr
  intro s kept x
  simp only [selectedMap_apply, cast_cast]

/-- Equal structures give equal evaluations when pulled back along the corresponding carrier maps. -/
theorem pullback_along_eq {A B : ContextStructure U} (same : A = B) (inside : V ≤ U)
    {X : P.signature.SortType → Type u} (f : CarrierMap V X A.carrier) (g : CarrierMap V X B.carrier)
    (agree : ∀ s kept x, cast (congrArg (fun M => M.carrier s) same) (f s kept x) = g s kept x) :
    A.evaluation.pullback inside f = B.evaluation.pullback inside g := by
  subst B
  exact A.evaluation.pullback_congr inside agree

/-- Pulling a reduct back along reidentified carrier maps reads the original evaluator directly. -/
theorem restrict_evaluation_view (A : ContextStructure U) (inside : V ≤ U)
    {X : P.signature.SortType → Type u} (f : CarrierMap V X A.carrier) :
    (A.restrict inside).evaluation.pullback (le_refl V)
        (fun s keep x => cast (A.restrict_carrier inside (s := s) keep).symm (f s keep x)) =
      A.evaluation.pullback inside f := by
  rw [restrict_evaluation, RestrictedEvaluation.pullback_comp]
  apply RestrictedEvaluation.pullback_congr
  intro s keep x
  simp only [selectedMap_apply, cast_cast]
  rfl

/-- Equality with a reduct follows from carrier equality and equality of the aligned primitive views. -/
theorem restrict_eq_of_view (A : ContextStructure U) (B : ContextStructure V) (inside : V ≤ U)
    (carriers : ∀ s, Declaration.sort s ∈ V.declarations → A.carrier s = B.carrier s)
    (view : A.evaluation.pullback inside (fun _ _ x => x) =
      B.evaluation.pullback (le_refl V) (fun s keep => cast (carriers s keep))) :
    A.restrict inside = B := by
  have same := carrier_ext (A := A.restrict inside) (B := B)
    (fun s keep => (A.restrict_carrier inside keep).trans (carriers s keep))
  apply ext same
  calc
    _ = (A.evaluation.pullback inside (fun _ _ x => x)).pullback (le_refl V)
          (fun s keep => cast (carriers s keep).symm) := by
      rw [RestrictedEvaluation.cast_evaluation _ same, restrict_evaluation,
        RestrictedEvaluation.pullback_comp, RestrictedEvaluation.pullback_comp]
      apply RestrictedEvaluation.pullback_congr
      intro s keep x
      simp only [selectedMap_apply, cast_cast]
    _ = B.evaluation := by
      rw [view, RestrictedEvaluation.pullback_comp]
      refine (RestrictedEvaluation.pullback_congr _ _ ?_).trans B.evaluation.pullback_id
      intro s keep x
      simp only [cast_cast]
      rfl

/-- The graph of a supported term uses only the retained scope. -/
def evaluates (A : ContextStructure U) {Γ : List P.signature.SortType} {s : P.signature.SortType}
    (t : U.TermIn Γ s) (e : Assignment A.carrier Γ) (result : A.carrier s) : Prop :=
  A.evaluation.holds t.val.graph ((Declaration.termContext_le_iff t.val).1 t.property)
    (Assignment.cons result e)

/-- The evaluation of a supported term is satisfaction of its value graph. -/
theorem evaluates_iff (A : ContextStructure U) {Γ : List P.signature.SortType} {s : P.signature.SortType}
    (t : U.TermIn Γ s) (e : Assignment A.carrier Γ) (result : A.carrier s) :
    A.evaluates t e result ↔
      A.evaluation.holds t.val.graph ((Declaration.termContext_le_iff t.val).1 t.property)
        (Assignment.cons result e) :=
  Iff.rfl

/-- The defined inputs of a supported term are exactly those with an evaluation result. -/
def termDomain (A : ContextStructure U) {Γ : List P.signature.SortType} {s : P.signature.SortType}
    (t : U.TermIn Γ s) : Set (Assignment A.carrier Γ) :=
  {e | ∃ result, A.evaluates t e result}

/-- A supported formula has the same truth before and after forgetting. -/
theorem restrict_holds_iff (A : ContextStructure U) (inside : V ≤ U) {Γ : List P.signature.SortType}
    (p : Formula P.signature Γ) (keep : Declaration.formulaSupport p ⊆ V.declarations)
    (e : Assignment (A.restrict inside).carrier Γ) :
    (A.restrict inside).evaluation.holds p keep e ↔ A.evaluation.holds p (fun _ hd => inside (keep hd))
      (mapAssignment (selectedMap V A.carrier) ((Declaration.sorts_subset_formulaSupport p).trans keep) e) :=
  A.evaluation.holds_pullback_iff inside _ (selectedMap_bijective A.carrier) p keep e

/-- A supported Law has the same satisfaction before and after forgetting. -/
theorem restrict_satisfies_iff (A : ContextStructure U) (inside : V ≤ U) (law : Law P.signature)
    (keep : Declaration.lawBody law ⊆ V.declarations) :
    (A.restrict inside).evaluation.satisfies law keep ↔ A.evaluation.satisfies law (fun _ hd => inside (keep hd)) :=
  A.evaluation.satisfies_pullback_iff inside _ (selectedMap_bijective A.carrier) law keep

/-- All the assignments and the result sort of a supported term survive restriction. -/
theorem termSortSupport {Γ : List P.signature.SortType} {s : P.signature.SortType} (t : U.TermIn Γ s) :
    Declaration.sorts (s :: Γ) ⊆ U.declarations :=
  (Declaration.sorts_subset_formulaSupport t.val.graph).trans ((Declaration.termContext_le_iff t.val).1 t.property)

/-- Term evaluation commutes with restriction on every input and result. -/
theorem restrict_evaluates_iff (A : ContextStructure U) (inside : V ≤ U)
    {Γ : List P.signature.SortType} {s : P.signature.SortType} (t : V.TermIn Γ s)
    (e : Assignment (A.restrict inside).carrier Γ) (y : (A.restrict inside).carrier s) :
    (A.restrict inside).evaluates t e y ↔
      A.evaluates ⟨t.val, t.property.trans inside⟩
        (mapAssignment (selectedMap V A.carrier)
          ((tailSortsSubset s Γ).trans (termSortSupport t)) e)
        (selectedMap V A.carrier s (varKept (termSortSupport t) .here) y) := by
  unfold evaluates
  rw [restrict_holds_iff, mapAssignment_cons]

/-- Forgetting preserves the domain of every supported term at the retained inputs. -/
theorem restrict_termDomain_iff (A : ContextStructure U) (inside : V ≤ U)
    {Γ : List P.signature.SortType} {s : P.signature.SortType} (t : V.TermIn Γ s)
    (e : Assignment (A.restrict inside).carrier Γ) :
    e ∈ (A.restrict inside).termDomain t ↔
      mapAssignment (selectedMap V A.carrier) ((tailSortsSubset s Γ).trans (termSortSupport t)) e ∈
        A.termDomain ⟨t.val, t.property.trans inside⟩ := by
  constructor
  · rintro ⟨y, evaluated⟩
    exact ⟨_, (A.restrict_evaluates_iff inside t e y).1 evaluated⟩
  · rintro ⟨y, evaluated⟩
    obtain ⟨y', rfl⟩ := (selectedMap_bijective A.carrier s (varKept (termSortSupport t) .here)).2 y
    exact ⟨y', (A.restrict_evaluates_iff inside t e y').2 evaluated⟩

end ContextStructure
end SHIGURE
