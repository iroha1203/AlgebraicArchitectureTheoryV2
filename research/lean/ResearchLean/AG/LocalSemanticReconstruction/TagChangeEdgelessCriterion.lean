import ResearchLean.AG.LocalSemanticReconstruction.FinitePermutationReadingCriteria
import ResearchLean.AG.LocalSemanticReconstruction.TagChangeFiniteReconstruction
import Formal.Util.AssertStandardAxioms

/-! Specialize the general D criterion to the fixed edgeless tag index. -/

namespace AAT.AG.LocalSemanticReconstruction

open RealizationReconstruction

namespace TagChangeEdgelessCriterion

/-- The tagged source objects form a named graph with no operations between
distinct vertices. -/
def graph : FixedFDirectedMultigraph where
  Vertex := TagChange.TaggedArchitectureIndex
  Edge := Empty
  source := Empty.elim
  target := Empty.elim

def identity : FixedFGraphAutomorphism graph where
  vertex := Equiv.refl _
  edge := Equiv.refl _
  source_rename := by intro e; exact e.elim
  target_rename := by intro e; exact e.elim

theorem reachable_iff_eq (first second : graph.Vertex) :
    FixedFUndirectedReachable graph first second ↔ first = second := by
  constructor
  · intro reachable
    induction reachable with
    | rel first second step =>
        obtain ⟨edge, _, _⟩ := step
        exact edge.elim
    | refl vertex => rfl
    | symm first second _ ih => exact ih.symm
    | trans first second third _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  · intro h
    subst second
    exact Relation.EqvGen.refl _

/-- Components of the edgeless tagged graph are exactly its source objects. -/
noncomputable def componentEquiv :
    FixedFComponent graph ≃ TagChange.TaggedArchitectureIndex where
  toFun := Quotient.lift id (by
    intro first second h
    exact (reachable_iff_eq first second).1 h)
  invFun := fixedFComponentMk graph
  left_inv := by
    intro component
    refine Quotient.inductionOn component ?_
    intro source
    rfl
  right_inv := by intro source; rfl

theorem component_finite_iff :
    Finite (FixedFComponent graph) ↔
      Finite TagChange.TaggedArchitectureIndex := by
  constructor
  · intro h
    letI := h
    exact Finite.of_injective componentEquiv.symm componentEquiv.symm.injective
  · intro h
    letI := h
    exact Finite.of_injective componentEquiv componentEquiv.injective

/-- The same common finite-reading D criterion says that a determining
finite tag selection exists precisely when the actual source index is finite. -/
theorem finite_determining_iff :
    (∃ S : Finset graph.Vertex,
      FiniteReading.Determining
        (FinitePermutationReadingCriteria.readAt graph Bool identity) S
        (FinitePermutationReadingCriteria.EdgeCoherent graph Bool S)) ↔
      Finite TagChange.TaggedArchitectureIndex := by
  exact (FinitePermutationReadingCriteria.exists_finite_determining_iff
    graph Bool identity).trans component_finite_iff

/-- The actual architecture-object index is infinite, so the same D
predicate admits no finite determining reading on the tagged graph. -/
theorem no_finite_determining :
    ¬ ∃ S : Finset graph.Vertex,
      FiniteReading.Determining
        (FinitePermutationReadingCriteria.readAt graph Bool identity) S
        (FinitePermutationReadingCriteria.EdgeCoherent graph Bool S) := by
  intro h
  letI : Finite TagChange.TaggedArchitectureIndex :=
    finite_determining_iff.mp h
  exact not_finite TagChange.TaggedArchitectureIndex

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.TagChangeEdgelessCriterion

end TagChangeEdgelessCriterion

end AAT.AG.LocalSemanticReconstruction
