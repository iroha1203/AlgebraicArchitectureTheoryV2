import Formal.SHIGURE.Part1.ContextSelectedEvaluation
import Formal.SHIGURE.Part1.ContextPrimitiveValues
import Formal.SHIGURE.Part1.ContextModels
import Formal.SHIGURE.Part1.Models

/-! # Context structures and the ordinary selected-signature structures

The graph presentation is useful for assembling partial operations without
inventing values at their undefined inputs. The ordinary presentation keeps
only the selected indices and names its operations by the unique functions
of these graphs. The two descriptions read the same primitive facts.
-/

universe u

namespace SHIGURE
namespace DeclarationContext.Selected

variable {P : PrimitivePresentation.{u}} {U : DeclarationContext P}

/-- Align the input to a retained operation with its ambient variables. -/
private def retainedCarrierEquiv (A : ContextStructure U) : CarrierEquiv U A.carrier (fun s => A.carrier s.val) :=
  fun s _ => Equiv.refl (A.carrier s)

/-- Read a context structure as an ordinary structure over the actual selected signature. -/
noncomputable def readStructure (A : ContextStructure U) : Structure (signature U) where
  carrier s := A.carrier s.val
  total f e := A.toRestrictedStructure.total f.val f.property
    (ambientAssignment (retainedCarrierEquiv A) (operationInputs (.total f.val) (Declaration.ofOperation_total_mem f.val f.property)) e)
  relation r := {e | A.evaluation.relation r.val r.property
    (ambientAssignment (retainedCarrierEquiv A) (relationInputs r.val r.property) e)}
  partialDomain p := {e | A.evaluation.domain p.val p.property
    (ambientAssignment (retainedCarrierEquiv A) (operationInputs (.partialOp p.val) (Declaration.ofOperation_partialOp_mem p.val p.property)) e)}
  partialValue p e := A.toRestrictedStructure.partialValue p.val p.property
    ⟨ambientAssignment (retainedCarrierEquiv A) (operationInputs (.partialOp p.val) (Declaration.ofOperation_partialOp_mem p.val p.property)) e.val, e.property⟩
  quantity q e := A.toRestrictedStructure.quantity q.val q.property
    (ambientAssignment (retainedCarrierEquiv A) (operationInputs (.quantity q.val) (Declaration.ofOperation_quantity_mem q.val q.property)) e)

/-- Reading a structure takes the original carrier at each retained sort. -/
theorem readStructure_carrier_eq (A : ContextStructure U) (s : SortName U) :
    (readStructure A).carrier s = A.carrier s.val :=
  rfl

/-- Identify the carrier at a retained name with the corresponding carrier of the read structure. -/
def readCarrierEquiv (A : ContextStructure U) : CarrierEquiv U A.carrier (readStructure A).carrier :=
  fun s keep => Equiv.cast (readStructure_carrier_eq A ⟨s, keep⟩).symm

/-- The carrier equivalence of a read structure is the cast along its retained carrier equality. -/
theorem readCarrierEquiv_eq_cast (A : ContextStructure U) (s : P.signature.SortType)
    (keep : Declaration.sort s ∈ U.declarations) :
    readCarrierEquiv A s keep = Equiv.cast (readStructure_carrier_eq A ⟨s, keep⟩).symm :=
  rfl

/-- Reading a retained relation takes the original relation on the ambient input tuple. -/
theorem readStructure_relation (A : ContextStructure U) (r : Rel U)
    (e : Assignment (readStructure A).carrier ((signature U).relInputs r)) :
    (readStructure A).relation r e ↔
      A.evaluation.relation r.val r.property
        (ambientAssignment (readCarrierEquiv A) (relationInputs r.val r.property) e) :=
  Iff.rfl

/-- Reading a retained partial domain takes the original domain on the ambient input tuple. -/
theorem readStructure_domain (A : ContextStructure U) (p : Partial U)
    (e : Assignment (readStructure A).carrier ((signature U).partialArity p).inputs) :
    (readStructure A).partialDomain p e ↔
      A.evaluation.domain p.val p.property (ambientAssignment (readCarrierEquiv A)
        (operationInputs (.partialOp p.val) (Declaration.ofOperation_partialOp_mem p.val p.property)) e) :=
  Iff.rfl

/-- Reading a retained total graph takes its restricted graph on the ambient input tuple. -/
theorem readStructure_graph_total (A : ContextStructure U) (f : Total U)
    (e : Assignment (readStructure A).carrier ((signature U).totalArity f).inputs)
    (y : (readStructure A).carrier ((signature U).totalArity f).output) :
    (readStructure A).Graph (.total f) e y ↔
      let kept := Declaration.ofOperation_total_mem f.val f.property
      A.toRestrictedStructure.graph (.total f.val) kept
        (ambientAssignment (readCarrierEquiv A) (operationInputs (.total f.val) kept) e)
        ((readCarrierEquiv A _ (operationOutput (.total f.val) kept)).symm y) := by
  rw [Structure.graph_total_iff, RestrictedStructure.graph_total_iff]
  rfl

/-- Reading a retained partial graph takes its restricted graph on the ambient input tuple. -/
theorem readStructure_graph_partial (A : ContextStructure U) (p : Partial U)
    (e : Assignment (readStructure A).carrier ((signature U).partialArity p).inputs)
    (y : (readStructure A).carrier ((signature U).partialArity p).output) :
    (readStructure A).Graph (.partialOp p) e y ↔
      let kept := Declaration.ofOperation_partialOp_mem p.val p.property
      A.toRestrictedStructure.graph (.partialOp p.val) kept
        (ambientAssignment (readCarrierEquiv A) (operationInputs (.partialOp p.val) kept) e)
        ((readCarrierEquiv A _ (operationOutput (.partialOp p.val) kept)).symm y) := by
  rw [Structure.graph_partial_iff, RestrictedStructure.graph_partial_iff]
  rfl

/-- Reading a retained quantity graph takes its restricted graph on the ambient input tuple. -/
theorem readStructure_graph_quantity (A : ContextStructure U) (q : Quantity U)
    (e : Assignment (readStructure A).carrier ((signature U).quantityArity q).inputs)
    (y : (readStructure A).carrier ((signature U).quantityArity q).output) :
    (readStructure A).Graph (.quantity q) e y ↔
      let kept := Declaration.ofOperation_quantity_mem q.val q.property
      A.toRestrictedStructure.graph (.quantity q.val) kept
        (ambientAssignment (readCarrierEquiv A) (operationInputs (.quantity q.val) kept) e)
        ((readCarrierEquiv A _ (operationOutput (.quantity q.val) kept)).symm y) := by
  rw [Structure.graph_quantity_iff, RestrictedStructure.graph_quantity_iff]
  rfl

/-- Construct the primitive comparisons used by Proposition 3.2 from any
context structure. The selected relations, domains and graphs use exactly
the declarations and input and output sorts retained by the context. -/
theorem readStructure_matches (A : ContextStructure U) :
    EvaluationMatches A.evaluation (readStructure A) (readCarrierEquiv A) where
  relation r keep e := by
    rw [readStructure_relation, ambientAssignment_selectAssignment]
  domain p keep e := by
    rw [readStructure_domain, ambientAssignment_selectAssignment]
  graph op keep e y := by
    cases op with
    | total f =>
      refine (graph_select_congr (readStructure A) (readCarrierEquiv A) (.total f) keep _
        (operation_total f keep) e y).trans ?_
      erw [cast_eq, cast_eq, readStructure_graph_total]
      dsimp only
      rw [ambientAssignment_selectAssignment (readCarrierEquiv A) (operationInputs (.total f) keep) e,
        Equiv.symm_apply_apply, ← RestrictedStructure.evaluation_graph, A.toRestrictedStructure_evaluation]
    | partialOp p =>
      refine (graph_select_congr (readStructure A) (readCarrierEquiv A) (.partialOp p) keep _
        (operation_partialOp p keep) e y).trans ?_
      erw [cast_eq, cast_eq, readStructure_graph_partial]
      dsimp only
      rw [ambientAssignment_selectAssignment (readCarrierEquiv A) (operationInputs (.partialOp p) keep) e,
        Equiv.symm_apply_apply, ← RestrictedStructure.evaluation_graph, A.toRestrictedStructure_evaluation]
    | quantity q =>
      refine (graph_select_congr (readStructure A) (readCarrierEquiv A) (.quantity q) keep _
        (operation_quantity q keep) e y).trans ?_
      erw [cast_eq, cast_eq, readStructure_graph_quantity]
      dsimp only
      rw [ambientAssignment_selectAssignment (readCarrierEquiv A) (operationInputs (.quantity q) keep) e,
        Equiv.symm_apply_apply, ← RestrictedStructure.evaluation_graph, A.toRestrictedStructure_evaluation]

/-- A supported term's full value graph is the same formula in the ordinary selected structure. -/
theorem read_evaluates_iff (A : ContextStructure U) {Γ : List P.signature.SortType}
    {s : P.signature.SortType} (t : U.TermIn Γ s) (e : Assignment A.carrier Γ) (y : A.carrier s) :
    (selectFormula t.val.graph ((Declaration.termContext_le_iff t.val).1 t.property)).Holds (readStructure A)
      (selectAssignment (readCarrierEquiv A) (ContextStructure.termSortSupport t) (Assignment.cons y e)) ↔
    A.evaluates t e y :=
  ((readStructure_matches A).formula_iff t.val.graph ((Declaration.termContext_le_iff t.val).1 t.property)
    (Assignment.cons y e)).trans (A.evaluates_iff t e y).symm

/-- Reindex a selected structure's carriers by original names, with one canonical slot for an omitted sort. -/
noncomputable def extendedCarrier (B : Structure (signature U)) (s : P.signature.SortType) : Type u := by
  classical
  exact if h : Declaration.sort s ∈ U.declarations then B.carrier ⟨s, h⟩ else PUnit

/-- A retained carrier stays exactly the full type carried by the selected structure. -/
theorem extendedCarrier_kept (B : Structure (signature U)) (s : P.signature.SortType)
    (keep : Declaration.sort s ∈ U.declarations) : extendedCarrier B s = B.carrier ⟨s, keep⟩ := by
  classical
  simp only [extendedCarrier, dif_pos keep]

/-- The original-name representation introduces no choice of carriers for erased sorts. -/
theorem extendedCarrier_omitted (B : Structure (signature U)) (s : P.signature.SortType)
    (omitted : Declaration.sort s ∉ U.declarations) : extendedCarrier B s = PUnit := by
  classical
  simp only [extendedCarrier, dif_neg omitted]

/-- Each kept type corresponds to the selected structure's carrier. -/
noncomputable def extendedEquiv (B : Structure (signature U)) : CarrierEquiv U (extendedCarrier B) B.carrier :=
  fun s keep => Equiv.cast (extendedCarrier_kept B s keep)

/-- The full-carrier comparison for a retained original sort in Proposition 3.2
is the equivalence obtained from its carrier type equality. -/
theorem extendedEquiv_eq_cast (B : Structure (signature U)) (s : P.signature.SortType)
    (keep : Declaration.sort s ∈ U.declarations) :
    extendedEquiv B s keep = Equiv.cast (extendedCarrier_kept B s keep) :=
  rfl

/-- Read the selected structure's primitive facts with their original names. -/
noncomputable def extendedEvaluation (B : Structure (signature U)) : RestrictedEvaluation U (extendedCarrier B) where
  relation r keep e := B.relation ⟨r, keep⟩ (selectAssignment (extendedEquiv B) (relationInputs r keep) e)
  domain p keep e := B.partialDomain ⟨p, keep⟩ (selectAssignment (extendedEquiv B) (operationInputs (.partialOp p) (Declaration.ofOperation_partialOp_mem p keep)) e)
  graph op keep e y := B.Graph (operation op keep) (selectArgs (extendedEquiv B) op keep e)
    (selectResult (extendedEquiv B) op keep y)

/-- Reading the retained names of an ordinary structure gives exactly its primitive facts. -/
theorem extendedEvaluation_matches (B : Structure (signature U)) :
    EvaluationMatches (extendedEvaluation B) B (extendedEquiv B) :=
  ⟨fun _ _ _ => Iff.rfl, fun _ _ _ => Iff.rfl, fun _ _ _ _ => Iff.rfl⟩

/-- Every ordinary selected structure gives a context structure with the same interpretations. -/
noncomputable def writeStructure (B : Structure (signature U)) : ContextStructure U where
  carrier := extendedCarrier B
  omitted := extendedCarrier_omitted B
  evaluation := extendedEvaluation B
  structural := by
    rw [RestrictedEvaluation.structural_iff]
    intro rule keep
    exact ((extendedEvaluation_matches B).law_iff rule.toLaw (graphRuleSupport rule keep)).1
      ((selectRule_toLaw rule keep).symm ▸ (selectRule rule keep).holds_toLaw B)

/-- The written structure has the original-name carrier family of the selected structure. -/
theorem writeStructure_carrier_eq (B : Structure (signature U)) :
    (writeStructure B).carrier = extendedCarrier B :=
  rfl

/-- Compare the evaluation of a written structure on any propositionally equal carrier family. -/
theorem writeStructure_cast_evaluation (B : Structure (signature U))
    {X : P.signature.SortType → Type u} (h : (writeStructure B).carrier = X) :
    cast (congrArg (RestrictedEvaluation U) h) (writeStructure B).evaluation =
      cast (congrArg (RestrictedEvaluation U) ((writeStructure_carrier_eq B).symm.trans h)) (extendedEvaluation B) :=
  rfl

/-- The written carrier at each retained name identifies with the corresponding selected carrier.

Implementation notes: use the composite carrier equality to transport points. This
keeps the written structure abstract in downstream proofs that compare its evaluation.
Using the extended carrier equivalence directly would require those proofs to reduce
the written structure to identify the carrier types. -/
noncomputable def writeCarrierEquiv (B : Structure (signature U)) :
    CarrierEquiv U (writeStructure B).carrier B.carrier :=
  fun s keep => Equiv.cast
    ((congrFun (writeStructure_carrier_eq B) s).trans (extendedCarrier_kept B s keep))

/-- The carrier equivalence of a written structure is the cast along its retained carrier equality. -/
theorem writeCarrierEquiv_eq_cast (B : Structure (signature U)) (s : P.signature.SortType)
    (keep : Declaration.sort s ∈ U.declarations) :
    writeCarrierEquiv B s keep = Equiv.cast
      ((congrFun (writeStructure_carrier_eq B) s).trans (extendedCarrier_kept B s keep)) :=
  rfl

/-- The written structure uses the extended evaluation on its identified original-name carriers. -/
theorem writeStructure_evaluation (B : Structure (signature U)) :
    (writeStructure B).evaluation = (extendedEvaluation B).pullback (le_refl U)
      (fun s _ => cast (congrFun (writeStructure_carrier_eq B) s)) := by
  have written := writeStructure_cast_evaluation B (X := (writeStructure B).carrier) rfl
  exact written.trans (RestrictedEvaluation.cast_evaluation _ (writeStructure_carrier_eq B).symm)

/-- A written structure retains exactly the selected relation, domain and graph facts. -/
theorem writeStructure_matches (B : Structure (signature U)) :
    EvaluationMatches (writeStructure B).evaluation B (writeCarrierEquiv B) := by
  let f : CarrierMap U (writeStructure B).carrier (extendedCarrier B) :=
    fun s _ => cast (congrFun (writeStructure_carrier_eq B) s)
  have component : ∀ s keep x, extendedEquiv B s keep (f s keep x) = writeCarrierEquiv B s keep x := by
    intro s keep x
    simp only [writeCarrierEquiv_eq_cast, extendedEquiv_eq_cast, f, Equiv.cast_apply, cast_cast]
  rw [writeStructure_evaluation]
  constructor
  · intro r keep a
    rw [RestrictedEvaluation.pullback_relation, ← (extendedEvaluation_matches B).relation r keep,
      selectAssignment_mapCarrier _ f _ component]
  · intro p keep a
    rw [RestrictedEvaluation.pullback_domain, ← (extendedEvaluation_matches B).domain p keep,
      selectAssignment_mapCarrier _ f _ component]
  · intro op keep a y
    rw [RestrictedEvaluation.pullback_graph, ← (extendedEvaluation_matches B).graph op keep,
      selectArgs_mapCarrier _ f _ component, selectResult_mapCarrier _ f _ component]

/-- Reading the selected names sends a context model to a model of the ordinary restricted theory. -/
noncomputable def readModel (A : Models U) : Model (theory U) :=
  ⟨readStructure A.obj, fun name => by
    let old : U.scopedTheory.LawName := ⟨⟨name.val.val, name.property⟩, name.val.property⟩
    exact ((readStructure_matches A.obj).law_iff (U.scopedTheory.law old)
      (Declaration.lawBody_subset_of_mem old.property)).2 (A.satisfies_required old)⟩

/-- An ordinary model yields a context model with the same retained Law satisfaction. -/
noncomputable def writeModel (A : Model (theory U)) : Models U :=
  ⟨writeStructure A.obj, fun name => by
    let selected : (theory U).LawName := ⟨⟨name.val.val, name.property⟩, name.val.property⟩
    exact ((writeStructure_matches A.obj).law_iff (U.scopedTheory.law name)
      (Declaration.lawBody_subset_of_mem name.property)).1 (A.property selected)⟩

end DeclarationContext.Selected
end SHIGURE
