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

/-- The selected type at a retained sort is the original context carrier. -/
def readCarrierEquiv (A : ContextStructure U) : CarrierEquiv U A.carrier (fun s => A.carrier s.val) :=
  fun s _ => Equiv.refl (A.carrier s)

/-- Read a context structure as an ordinary structure over the actual selected signature. -/
noncomputable def readStructure (A : ContextStructure U) : Structure (signature U) where
  carrier s := A.carrier s.val
  total f e := A.toRestrictedStructure.total f.val f.property
    (ambientAssignment (readCarrierEquiv A) (operationInputs (.total f.val) f.property) e)
  relation r := {e | A.evaluation.relation r.val r.property
    (ambientAssignment (readCarrierEquiv A) (relationInputs r.val r.property) e)}
  partialDomain p := {e | A.evaluation.domain p.val p.property
    (ambientAssignment (readCarrierEquiv A) (operationInputs (.partialOp p.val) p.property) e)}
  partialValue p e := A.toRestrictedStructure.partialValue p.val p.property
    ⟨ambientAssignment (readCarrierEquiv A) (operationInputs (.partialOp p.val) p.property) e.val, e.property⟩
  quantity q e := A.toRestrictedStructure.quantity q.val q.property
    (ambientAssignment (readCarrierEquiv A) (operationInputs (.quantity q.val) q.property) e)

/-- The ordinary structure interprets exactly the primitive facts of the context structure. -/
theorem readStructure_matches (A : ContextStructure U) :
    EvaluationMatches A.evaluation (readStructure A) (readCarrierEquiv A) where
  relation r keep e := by
    change A.evaluation.relation r keep
      (ambientAssignment (readCarrierEquiv A) (relationInputs r keep)
        (selectAssignment (readCarrierEquiv A) (relationInputs r keep) e)) ↔ A.evaluation.relation r keep e
    rw [ambientAssignment_selectAssignment (readCarrierEquiv A) (relationInputs r keep) e]
  domain p keep e := by
    change A.evaluation.domain p keep
      (ambientAssignment (readCarrierEquiv A) (operationInputs (.partialOp p) keep)
        (selectAssignment (readCarrierEquiv A) (operationInputs (.partialOp p) keep) e)) ↔
      A.evaluation.domain p keep e
    rw [ambientAssignment_selectAssignment (readCarrierEquiv A) (operationInputs (.partialOp p) keep) e]
  graph op keep e y := by
    cases op with
    | total f =>
      erw [Structure.graph_total_iff]
      change A.toRestrictedStructure.total f keep
        (ambientAssignment (readCarrierEquiv A) (operationInputs (.total f) keep)
          (selectAssignment (readCarrierEquiv A) (operationInputs (.total f) keep) e)) = y ↔ _
      rw [ambientAssignment_selectAssignment (readCarrierEquiv A) (operationInputs (.total f) keep) e]
      exact Iff.of_eq (congrArg (fun R => R.graph (.total f) keep e y) A.toRestrictedStructure_evaluation)
    | partialOp p =>
      erw [Structure.graph_partial_iff]
      have input := ambientAssignment_selectAssignment (readCarrierEquiv A) (operationInputs (.partialOp p) keep) e
      change (∃ he : A.evaluation.domain p keep
          (ambientAssignment (readCarrierEquiv A) (operationInputs (.partialOp p) keep)
            (selectAssignment (readCarrierEquiv A) (operationInputs (.partialOp p) keep) e)),
          A.toRestrictedStructure.partialValue p keep ⟨_, he⟩ = y) ↔ _
      rw [input]
      exact Iff.of_eq (congrArg (fun R => R.graph (.partialOp p) keep e y) A.toRestrictedStructure_evaluation)
    | quantity q =>
      erw [Structure.graph_quantity_iff]
      change A.toRestrictedStructure.quantity q keep
        (ambientAssignment (readCarrierEquiv A) (operationInputs (.quantity q) keep)
          (selectAssignment (readCarrierEquiv A) (operationInputs (.quantity q) keep) e)) = y ↔ _
      rw [ambientAssignment_selectAssignment (readCarrierEquiv A) (operationInputs (.quantity q) keep) e]
      exact Iff.of_eq (congrArg (fun R => R.graph (.quantity q) keep e y) A.toRestrictedStructure_evaluation)

/-- A supported term's full value graph is the same formula in the ordinary selected structure. -/
theorem read_evaluates_iff (A : ContextStructure U) {Γ : List P.signature.SortType}
    {s : P.signature.SortType} (t : U.TermIn Γ s) (e : Assignment A.carrier Γ) (y : A.carrier s) :
    (selectFormula t.val.graph ((Declaration.termContext_le_iff t.val).1 t.property)).Holds (readStructure A)
      (selectAssignment (readCarrierEquiv A) (ContextStructure.termSortSupport t) (Assignment.cons y e)) ↔
    A.evaluates t e y :=
  (readStructure_matches A).formula_iff t.val.graph ((Declaration.termContext_le_iff t.val).1 t.property)
    (Assignment.cons y e)

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

/-- Read the selected structure's primitive facts with their original names. -/
noncomputable def extendedEvaluation (B : Structure (signature U)) : RestrictedEvaluation U (extendedCarrier B) where
  relation r keep e := B.relation ⟨r, keep⟩ (selectAssignment (extendedEquiv B) (relationInputs r keep) e)
  domain p keep e := B.partialDomain ⟨p, keep⟩ (selectAssignment (extendedEquiv B) (operationInputs (.partialOp p) keep) e)
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
  structural rule keep := ((extendedEvaluation_matches B).law_iff rule.toLaw (graphRuleSupport rule keep)).1
    ((selectRule_toLaw rule keep).symm ▸ (selectRule rule keep).holds_toLaw B)

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
    exact ((extendedEvaluation_matches A.obj).law_iff (U.scopedTheory.law name)
      (Declaration.lawBody_subset_of_mem name.property)).1 (A.property selected)⟩

end DeclarationContext.Selected
end SHIGURE
