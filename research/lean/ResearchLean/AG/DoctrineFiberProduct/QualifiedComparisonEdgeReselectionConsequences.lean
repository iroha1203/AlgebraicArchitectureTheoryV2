import ResearchLean.AG.DoctrineFiberProduct.QualifiedComparisonEdgeReselection
import ResearchLean.AG.DoctrineFiberProduct.UpperGeometryCanonicalAuthoredFullPairedTransport

/-!
# Downstream consequences and fixed decisions for G-118(C2)

The central edge-family classification is kept in
`QualifiedComparisonEdgeReselection`.  This module records its proof-use in
the path, authored-comparator, raw-cochain, fixed generated, and inverse
canonical-authored routes required by the GOAL.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u v

open CategoryTheory AtomFoundation GeometryTransport CrossStageCoherence
open TransportCoherence

set_option maxHeartbeats 6000000

namespace UpperGeometryCompatibleProblemInputData

/-- The source family supplies the generated reselected path-leg triangle. -/
theorem sourceCoefficientTrivialUpperEdgeReselection_generatedPath_legTriangle
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (source : SourceCoefficientTrivialUpperEdgeReselection input) :
    ReselectedPathLegTriangle
      input.generatedGeometryCompatibleUpperRefinementBCSolution
      (input.generatedBaseOfSourceCoefficientTrivialUpperEdgeReselection source)
      (input.generatedPulledOfSourceCoefficientTrivialUpperEdgeReselection source) :=
  CoefficientTrivialUpperReselectionEndpointIntertwining.reselectedPath_legTriangle
    (input.sourceCoefficientTrivialUpperEdgeReselection_generated_endpointIntertwining
      source)

/-- The source family also preserves the authored comparator pasting. -/
theorem sourceCoefficientTrivialUpperEdgeReselection_generatedAuthoredComparator_pasting
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (source : SourceCoefficientTrivialUpperEdgeReselection input) :
    ReselectedAuthoredComparatorPasting
      input.generatedGeometryCompatibleUpperRefinementBCSolution
      (input.generatedBaseOfSourceCoefficientTrivialUpperEdgeReselection source)
      (input.generatedPulledOfSourceCoefficientTrivialUpperEdgeReselection source) :=
  CoefficientTrivialUpperReselectionEndpointIntertwining.reselectedAuthoredComparator_pasting
    (input.sourceCoefficientTrivialUpperEdgeReselection_generated_endpointIntertwining
      source)

/-- The source family generates the complete paired relation. -/
theorem sourceCoefficientTrivialUpperEdgeReselection_generatedPaired
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (source : SourceCoefficientTrivialUpperEdgeReselection input) :
    PairedCoefficientTrivialUpperReselection
      input.generatedGeometryCompatibleUpperRefinementBCSolution
      (input.generatedBaseOfSourceCoefficientTrivialUpperEdgeReselection source)
      (input.generatedPulledOfSourceCoefficientTrivialUpperEdgeReselection source) :=
  CoefficientTrivialUpperReselectionEndpointIntertwining.toPaired
    (input.sourceCoefficientTrivialUpperEdgeReselection_generated_endpointIntertwining
      source)

end UpperGeometryCompatibleProblemInputData

namespace UpperDecisionWitness

/-- At the fixed twist edge the two generated comparator reselections are an
actual member of the qualified comparison subgroup. -/
theorem generatedComparatorUpperReselections_twist_mem_qualifiedComparison :
    (generatedBaseComparatorCoefficientTrivialUpperReselection.toUpperEdgeReselection
        PUnit.unit PUnit.unit DecisionEdge.twist,
      generatedPulledComparatorCoefficientTrivialUpperReselection.toUpperEdgeReselection
        PUnit.unit PUnit.unit DecisionEdge.twist) ∈
      qualifiedComparisonSubgroup (solution.component PUnit.unit) :=
  generatedComparatorUpperReselections_endpointIntertwining_fires
    (i := PUnit.unit) (j := PUnit.unit) DecisionEdge.twist

/-- Replacing the fixed pulled comparator by the identity fails qualified
membership at the same twist edge. -/
theorem generatedBaseComparatorPulledIdentity_twist_not_mem_qualifiedComparison :
    ¬ (generatedBaseComparatorCoefficientTrivialUpperReselection.toUpperEdgeReselection
          PUnit.unit PUnit.unit DecisionEdge.twist,
        (CoefficientTrivialUpperEdgeReselection.one
          problem.data.generatedPulledRouteTransport).toUpperEdgeReselection
            PUnit.unit PUnit.unit DecisionEdge.twist) ∈
        qualifiedComparisonSubgroup (solution.component PUnit.unit) := by
  intro membership
  apply generatedBaseComparatorPulledIdentity_not_endpointIntertwining
  intro i j edge
  cases i
  cases j
  cases edge
  exact membership

/-- The inverse canonical-authored presentation retains the fixed negative
identity decision: the canonical base companion cannot pair with pulled
identity. -/
theorem canonicalCompanionBaseComparatorPulledIdentity_not_endpointIntertwining :
    ¬ UpperGeometryCompatibleProblemInputData.CanonicalAuthoredCoefficientTrivialUpperReselectionEndpointIntertwining
      problem.data.canonicalCompanionUpperRefinementBCSolution
      canonicalCompanionBaseComparatorCoefficientTrivialUpperReselection
      (CoefficientTrivialUpperEdgeReselection.one
        problem.data.canonicalAuthoredPulledRouteTransport) := by
  intro canonicalEndpoint
  apply generatedBaseComparatorPulledIdentity_not_endpointIntertwining
  intro i j edge
  have generatedEdge :=
    problem.data.canonicalAuthoredEndpointIntertwining_forward_transport
      canonicalEndpoint (i := i) (j := j) edge
  have solutionEquality :
      problem.data.canonicalSolutionForward
          problem.data.canonicalCompanionUpperRefinementBCSolution =
        problem.data.generatedGeometryCompatibleUpperRefinementBCSolution :=
    problem.data.canonicalGeneratedUpperRefinementBCSolutionEquiv_companion
  rw [solutionEquality] at generatedEdge
  simpa only [
      canonicalCompanionBaseComparatorCoefficientTrivialUpperReselection,
      solution,
      problem.data.canonicalAuthoredBaseCoefficientTrivialReselectionForward_backward,
      problem.data.canonicalAuthoredPulledCoefficientTrivialReselectionForward_one]
    using generatedEdge

end UpperDecisionWitness

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
