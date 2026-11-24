import Formal.SHIGURE.Part1.ContextMorphisms

/-! # Primitive values in a context structure

The carried graphs and domains have their usual function-valued
interpretations. This follows from the graph rules and the already proved
unique realization of total and partial graphs.
-/

universe u

namespace SHIGURE
namespace ContextStructure

open DeclarationContext

variable {P : PrimitivePresentation.{u}} {U : DeclarationContext P} (A : ContextStructure U)

/-- Each retained graph is functional on the entire supported input product. -/
theorem graph_rightUnique (op : Operation P.signature) (kept : Declaration.ofOperation op ∈ U.declarations) :
    Relator.RightUnique (A.evaluation.graph op kept) := by
  intro e y z hy hz
  have held := A.structural (.functional op) kept
  change ∀ x : Assignment A.carrier (op.arity.output :: op.arity.output :: op.arity.inputs),
    (A.evaluation.graph op kept (x.pull (fun i => .there (.there i))) (x .here) ∧
      A.evaluation.graph op kept (x.pull (fun i => .there (.there i))) (x (.there .here))) →
    x .here = x (.there .here) at held
  apply held (Assignment.cons y (Assignment.cons z e))
  simpa only [Assignment.pull_cons_there, Assignment.pull_id, Assignment.cons_here, Assignment.cons_there]
    using And.intro hy hz

/-- A total operation's graph has a value for every input. -/
theorem total_graph_valid (f : P.signature.Total) (kept : Declaration.total f ∈ U.declarations) :
    GraphPresentation.IsTotal (A.evaluation.graph (.total f) kept) := by
  refine ⟨A.graph_rightUnique (.total f) kept, fun e => ?_⟩
  have held := A.structural (.totality f) kept e True.intro
  change ∃ y, A.evaluation.graph (.total f) kept
    ((Assignment.cons y e).pull (fun i => .there i)) ((Assignment.cons y e) .here) at held
  simpa only [Assignment.pull_cons_there, Assignment.pull_id, Assignment.cons_here] using held

/-- A quantity's graph has a value for every input. -/
theorem quantity_graph_valid (q : P.signature.Quantity) (kept : Declaration.quantity q ∈ U.declarations) :
    GraphPresentation.IsTotal (A.evaluation.graph (.quantity q) kept) := by
  refine ⟨A.graph_rightUnique (.quantity q) kept, fun e => ?_⟩
  have held := A.structural (.quantityTotality q) kept e True.intro
  change ∃ y, A.evaluation.graph (.quantity q) kept
    ((Assignment.cons y e).pull (fun i => .there i)) ((Assignment.cons y e) .here) at held
  simpa only [Assignment.pull_cons_there, Assignment.pull_id, Assignment.cons_here] using held

/-- A partial graph has unique values exactly on its declared domain. -/
theorem partial_graph_valid (p : P.signature.Partial) (kept : Declaration.partialOp p ∈ U.declarations) :
    GraphPresentation.IsPartial {e | A.evaluation.domain p kept e} (A.evaluation.graph (.partialOp p) kept) := by
  refine ⟨A.graph_rightUnique (.partialOp p) kept, ?_, ?_⟩
  · intro e y graph
    have held := A.structural (.graphImpliesDomain p) kept (Assignment.cons y e)
    change A.evaluation.graph (.partialOp p) kept ((Assignment.cons y e).pull (fun i => .there i))
        ((Assignment.cons y e) .here) → A.evaluation.domain p kept
        ((Assignment.cons y e).pull (fun i => .there i)) at held
    simpa only [Assignment.pull_cons_there, Assignment.pull_id, Assignment.cons_here] using held graph
  · intro e domain
    have held := A.structural (.domainImpliesGraph p) kept e domain
    change ∃ y, A.evaluation.graph (.partialOp p) kept
      ((Assignment.cons y e).pull (fun i => .there i)) ((Assignment.cons y e) .here) at held
    simpa only [Assignment.pull_cons_there, Assignment.pull_id, Assignment.cons_here] using held

/-- Read the literal functions, relations and domains of a context structure. -/
noncomputable def toRestrictedStructure : RestrictedStructure U where
  carrier := A.carrier
  total f kept := ((GraphPresentation.isTotal_iff_existsUnique _).1 (A.total_graph_valid f kept)).exists.choose
  relation r kept := {e | A.evaluation.relation r kept e}
  partialDomain p kept := {e | A.evaluation.domain p kept e}
  partialValue p kept := ((GraphPresentation.isPartial_iff_existsUnique _ _).1 (A.partial_graph_valid p kept)).exists.choose
  quantity q kept := ((GraphPresentation.isTotal_iff_existsUnique _).1 (A.quantity_graph_valid q kept)).exists.choose

/-- The ordinary primitive interpretations recover exactly the original evaluation graphs. -/
theorem toRestrictedStructure_evaluation : A.toRestrictedStructure.evaluation = A.evaluation := by
  apply RestrictedEvaluation.ext
  · intros; rfl
  · intros; rfl
  · intro op kept e y
    cases op with
    | total f =>
      exact (((GraphPresentation.isTotal_iff_existsUnique _).1 (A.total_graph_valid f kept)).exists.choose_spec e y).symm
    | partialOp p =>
      exact (((GraphPresentation.isPartial_iff_existsUnique _ _).1
        (A.partial_graph_valid p kept)).exists.choose_spec e y).symm
    | quantity q =>
      exact (((GraphPresentation.isTotal_iff_existsUnique _).1
        (A.quantity_graph_valid q kept)).exists.choose_spec e y).symm

/-- Each retained primitive value of a total operation is preserved by a context arrow. -/
theorem Hom.total_comm {A B : ContextStructure U} (f : Hom A B) (op : P.signature.Total)
    (kept : Declaration.total op ∈ U.declarations) (e : Assignment A.carrier (P.signature.totalArity op).inputs) :
    f.onSort _ (operationOutput (.total op) kept) (A.toRestrictedStructure.total op kept e) =
      B.toRestrictedStructure.total op kept (mapAssignment f.onSort (operationInputs (.total op) kept) e) := by
  have graph : A.evaluation.graph (.total op) kept e (A.toRestrictedStructure.total op kept e) := by
    rw [← A.toRestrictedStructure_evaluation]
    rfl
  have mapped := f.graph_mem (.total op) kept e _ graph
  rw [← B.toRestrictedStructure_evaluation] at mapped
  exact mapped.symm

end ContextStructure
end SHIGURE
