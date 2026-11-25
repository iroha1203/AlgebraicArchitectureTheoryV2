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
  have held := A.evaluation.structural_rule A.structural (.functional op)
    (by simpa only [Declaration.graphRuleName_functional] using kept)
  simp only [RestrictedEvaluation.satisfies_iff, GraphAxiom.toLaw_functional,
    RestrictedEvaluation.holds_conj_iff, RestrictedEvaluation.holds_atom_iff,
    RestrictedEvaluation.atomic_graph_iff, RestrictedEvaluation.atomic_eq_iff] at held
  apply held (Assignment.cons y (Assignment.cons z e))
  simpa only [Assignment.pull_cons_there, Assignment.pull_id, Assignment.cons_here, Assignment.cons_there]
    using And.intro hy hz

/-- A total operation's graph has a value for every input. -/
theorem total_graph_valid (f : P.signature.Total) (kept : Declaration.total f ∈ U.declarations) :
    GraphPresentation.IsTotal (A.evaluation.graph (.total f) (Declaration.ofOperation_total_mem f kept)) := by
  let opKept := Declaration.ofOperation_total_mem f kept
  refine ⟨A.graph_rightUnique (.total f) opKept, fun e => ?_⟩
  have held := A.evaluation.structural_rule A.structural (.totality f)
    (by simpa only [Declaration.graphRuleName_totality] using kept)
  simp only [RestrictedEvaluation.satisfies_iff, GraphAxiom.toLaw_totality, GraphAxiom.hasOutput_eq_ex_graph,
    RestrictedEvaluation.holds_truth_iff, true_implies, RestrictedEvaluation.holds_ex_iff,
    RestrictedEvaluation.holds_atom_iff, RestrictedEvaluation.atomic_graph_iff,
    Assignment.pull_cons_there, Assignment.pull_id, Assignment.cons_here] at held
  exact held e

/-- A quantity's graph has a value for every input. -/
theorem quantity_graph_valid (q : P.signature.Quantity) (kept : Declaration.quantity q ∈ U.declarations) :
    GraphPresentation.IsTotal (A.evaluation.graph (.quantity q) (Declaration.ofOperation_quantity_mem q kept)) := by
  let opKept := Declaration.ofOperation_quantity_mem q kept
  refine ⟨A.graph_rightUnique (.quantity q) opKept, fun e => ?_⟩
  have held := A.evaluation.structural_rule A.structural (.quantityTotality q)
    (by simpa only [Declaration.graphRuleName_quantityTotality] using kept)
  simp only [RestrictedEvaluation.satisfies_iff, GraphAxiom.toLaw_quantityTotality, GraphAxiom.hasOutput_eq_ex_graph,
    RestrictedEvaluation.holds_truth_iff, true_implies, RestrictedEvaluation.holds_ex_iff,
    RestrictedEvaluation.holds_atom_iff, RestrictedEvaluation.atomic_graph_iff,
    Assignment.pull_cons_there, Assignment.pull_id, Assignment.cons_here] at held
  exact held e

/-- A partial graph has unique values exactly on its declared domain. -/
theorem partial_graph_valid (p : P.signature.Partial) (kept : Declaration.partialOp p ∈ U.declarations) :
    GraphPresentation.IsPartial {e | A.evaluation.domain p kept e} (A.evaluation.graph (.partialOp p) (Declaration.ofOperation_partialOp_mem p kept)) := by
  let opKept := Declaration.ofOperation_partialOp_mem p kept
  refine ⟨A.graph_rightUnique (.partialOp p) opKept, ?_, ?_⟩
  · intro e y graph
    have held := A.evaluation.structural_rule A.structural (.graphImpliesDomain p)
      (by simpa only [Declaration.graphRuleName_graphImpliesDomain] using kept)
    simp only [RestrictedEvaluation.satisfies_iff, GraphAxiom.toLaw_graphImpliesDomain,
      RestrictedEvaluation.holds_atom_iff, RestrictedEvaluation.atomic_graph_iff,
      RestrictedEvaluation.atomic_domain_iff] at held
    have atInput := held (Assignment.cons y e)
    simp only [Assignment.pull_cons_there, Assignment.pull_id, Assignment.cons_here] at atInput
    exact atInput graph
  · intro e domain
    have held := A.evaluation.structural_rule A.structural (.domainImpliesGraph p)
      (by simpa only [Declaration.graphRuleName_domainImpliesGraph] using kept)
    simp only [RestrictedEvaluation.satisfies_iff, GraphAxiom.toLaw_domainImpliesGraph,
      GraphAxiom.hasOutput_eq_ex_graph, RestrictedEvaluation.holds_ex_iff,
      RestrictedEvaluation.holds_atom_iff, RestrictedEvaluation.atomic_domain_iff,
      RestrictedEvaluation.atomic_graph_iff, Assignment.pull_cons_there, Assignment.pull_id,
      Assignment.cons_here] at held
    exact held e domain

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
  · intros
    rw [RestrictedStructure.evaluation_relation]
    rfl
  · intros
    rw [RestrictedStructure.evaluation_domain]
    rfl
  · intro op kept e y
    rw [RestrictedStructure.evaluation_graph]
    cases op with
    | total f =>
      rw [RestrictedStructure.graph_total_iff]
      exact (((GraphPresentation.isTotal_iff_existsUnique _).1 (A.total_graph_valid f (Declaration.ofOperation_total f ▸ kept))).exists.choose_spec e y).symm
    | partialOp p =>
      rw [RestrictedStructure.graph_partial_iff]
      exact (((GraphPresentation.isPartial_iff_existsUnique _ _).1
        (A.partial_graph_valid p (Declaration.ofOperation_partialOp p ▸ kept))).exists.choose_spec e y).symm
    | quantity q =>
      rw [RestrictedStructure.graph_quantity_iff]
      exact (((GraphPresentation.isTotal_iff_existsUnique _).1
        (A.quantity_graph_valid q (Declaration.ofOperation_quantity q ▸ kept))).exists.choose_spec e y).symm

/-- Each retained primitive value of a total operation is preserved by a context arrow. -/
theorem Hom.total_comm {A B : ContextStructure U} (f : Hom A B) (op : P.signature.Total)
    (kept : Declaration.total op ∈ U.declarations) (e : Assignment A.carrier (P.signature.totalArity op).inputs) :
    f.onSort _ (operationOutput (.total op) (Declaration.ofOperation_total_mem op kept)) (A.toRestrictedStructure.total op kept e) =
      B.toRestrictedStructure.total op kept (mapAssignment f.onSort (operationInputs (.total op) (Declaration.ofOperation_total_mem op kept)) e) := by
  let opKept := Declaration.ofOperation_total_mem op kept
  have graph : A.evaluation.graph (.total op) opKept e (A.toRestrictedStructure.total op kept e) := by
    rw [← A.toRestrictedStructure_evaluation, RestrictedStructure.evaluation_graph,
      RestrictedStructure.graph_total_iff]
  have mapped := f.graph_mem (.total op) opKept e _ graph
  rw [← B.toRestrictedStructure_evaluation, RestrictedStructure.evaluation_graph,
    RestrictedStructure.graph_total_iff] at mapped
  exact mapped.symm

end ContextStructure
end SHIGURE
