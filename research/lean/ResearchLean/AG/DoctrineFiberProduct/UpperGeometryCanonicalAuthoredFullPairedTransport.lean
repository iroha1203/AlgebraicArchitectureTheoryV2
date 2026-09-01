import ResearchLean.AG.DoctrineFiberProduct.UpperGeometryCanonicalAuthoredPairedComparatorRawTransport

/-!
# Full paired transport and the named canonical companion for G-115

This module assembles the four fieldwise transport theorems into the full
canonical-authored/generated paired equivalence.  The assembly deliberately
uses every supplied conjunct; it does not regenerate either destination
relation from endpoint intertwining through `toPaired`.

It also records that endpoint conjugation preserves the identity reselection
and uses this structural fact to transport the named nonidentity decision pair
back to its canonical-authored companion.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u v

open CategoryTheory AtomFoundation GeometryTransport CrossStageCoherence
open TransportCoherence

set_option maxHeartbeats 6000000

namespace UpperGeometryCompatibleProblemInputData

/-- The native canonical-authored four-conjunct relation is carried forward
fieldwise to the generated routes. -/
theorem canonicalAuthoredPairedCoefficientTrivialUpperReselection_forward_transport
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    {solution : CanonicalUpperRefinementBCSolution input}
    {base : CanonicalAuthoredBaseCoefficientTrivialUpperEdgeReselection input}
    {pulled :
      CanonicalAuthoredPulledCoefficientTrivialUpperEdgeReselection input}
    (paired : CanonicalAuthoredPairedCoefficientTrivialUpperReselection
      solution base pulled) :
    PairedCoefficientTrivialUpperReselection
      (input.canonicalSolutionForward solution)
      (input.canonicalAuthoredBaseCoefficientTrivialReselectionForward base)
      (input.canonicalAuthoredPulledCoefficientTrivialReselectionForward
        pulled) := by
  exact ⟨
    input.canonicalAuthoredEndpointIntertwining_forward_transport paired.1,
    input.canonicalAuthoredReselectedPathLegTriangle_forward_transport
      paired.2.1,
    input.canonicalAuthoredReselectedAuthoredComparatorPasting_forward_transport
      paired.2.2.1,
    input.canonicalAuthoredRawCochainComponentCoefficientTrivial_forward_transport
      paired.2.2.2⟩

/-- The generated four-conjunct relation is returned fieldwise to the
independently authored canonical routes. -/
theorem canonicalAuthoredPairedCoefficientTrivialUpperReselection_backward_transport
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    {solution : GeometryCompatibleUpperRefinementBCSolution input}
    {base : GeneratedBaseCoefficientTrivialUpperEdgeReselection input}
    {pulled : GeneratedPulledCoefficientTrivialUpperEdgeReselection input}
    (paired : PairedCoefficientTrivialUpperReselection solution base pulled) :
    CanonicalAuthoredPairedCoefficientTrivialUpperReselection
      (input.generatedSolutionBackward solution)
      (input.canonicalAuthoredBaseCoefficientTrivialReselectionBackward base)
      (input.canonicalAuthoredPulledCoefficientTrivialReselectionBackward
        pulled) := by
  exact ⟨
    input.canonicalAuthoredEndpointIntertwining_backward_transport paired.1,
    input.canonicalAuthoredReselectedPathLegTriangle_backward_transport
      paired.2.1,
    input.canonicalAuthoredReselectedAuthoredComparatorPasting_backward_transport
      paired.2.2.1,
    input.canonicalAuthoredRawCochainComponentCoefficientTrivial_backward_transport
      paired.2.2.2⟩

/-- Canonical-authored pairing is equivalent to generated pairing after the
actual solution and both reselections are transported forward. -/
theorem canonicalAuthoredPairedCoefficientTrivialUpperReselection_iff_forward
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    {solution : CanonicalUpperRefinementBCSolution input}
    {base : CanonicalAuthoredBaseCoefficientTrivialUpperEdgeReselection input}
    {pulled :
      CanonicalAuthoredPulledCoefficientTrivialUpperEdgeReselection input} :
    CanonicalAuthoredPairedCoefficientTrivialUpperReselection
        solution base pulled ↔
      PairedCoefficientTrivialUpperReselection
        (input.canonicalSolutionForward solution)
        (input.canonicalAuthoredBaseCoefficientTrivialReselectionForward base)
        (input.canonicalAuthoredPulledCoefficientTrivialReselectionForward
          pulled) := by
  constructor
  · exact input.canonicalAuthoredPairedCoefficientTrivialUpperReselection_forward_transport
  · intro paired
    have returned :=
      input.canonicalAuthoredPairedCoefficientTrivialUpperReselection_backward_transport
        paired
    simpa only [input.generatedSolutionBackward_canonicalSolutionForward,
      input.canonicalAuthoredBaseCoefficientTrivialReselectionBackward_forward,
      input.canonicalAuthoredPulledCoefficientTrivialReselectionBackward_forward]
      using returned

/-- Forward endpoint conjugation carries the canonical-authored base identity
reselection to the generated base identity reselection. -/
theorem canonicalAuthoredBaseCoefficientTrivialReselectionForward_one
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) :
    input.canonicalAuthoredBaseCoefficientTrivialReselectionForward
        (CoefficientTrivialUpperEdgeReselection.one
          input.canonicalAuthoredBaseRouteTransport) =
      CoefficientTrivialUpperEdgeReselection.one
        input.generatedBaseRouteTransport := by
  apply CoefficientTrivialUpperEdgeReselection.ext
  funext i j edge
  change
    input.canonicalAuthoredBaseCompositeFiberAutForwardAt j 1 = 1
  change
    CompositeFiberAut.conjugationEquiv
      (input.canonicalAuthoredBaseToGeneratedRouteExactGeometryIsoAt j) 1 = 1
  simpa only [CompositeFiberAut.conjugationMulEquiv_apply] using
    CompositeFiberAut.conjugationMulEquiv_map_one
      (input.canonicalAuthoredBaseToGeneratedRouteExactGeometryIsoAt j)

/-- Forward endpoint conjugation carries the canonical-authored pulled
identity reselection to the generated pulled identity reselection. -/
theorem canonicalAuthoredPulledCoefficientTrivialReselectionForward_one
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) :
    input.canonicalAuthoredPulledCoefficientTrivialReselectionForward
        (CoefficientTrivialUpperEdgeReselection.one
          input.canonicalAuthoredPulledRouteTransport) =
      CoefficientTrivialUpperEdgeReselection.one
        input.generatedPulledRouteTransport := by
  apply CoefficientTrivialUpperEdgeReselection.ext
  funext i j edge
  change
    input.canonicalAuthoredPulledCompositeFiberAutForwardAt j 1 = 1
  change
    CompositeFiberAut.conjugationEquiv
      (input.canonicalAuthoredPulledToGeneratedRouteExactGeometryIsoAt j) 1 = 1
  simpa only [CompositeFiberAut.conjugationMulEquiv_apply] using
    CompositeFiberAut.conjugationMulEquiv_map_one
      (input.canonicalAuthoredPulledToGeneratedRouteExactGeometryIsoAt j)

end UpperGeometryCompatibleProblemInputData

namespace UpperDecisionWitness

/-- The actual canonical-authored base companion of the named generated
comparator reselection. -/
noncomputable def canonicalCompanionBaseComparatorCoefficientTrivialUpperReselection :
    UpperGeometryCompatibleProblemInputData.CanonicalAuthoredBaseCoefficientTrivialUpperEdgeReselection
      problem.data :=
  problem.data.canonicalAuthoredBaseCoefficientTrivialReselectionBackward
    generatedBaseComparatorCoefficientTrivialUpperReselection

/-- The actual canonical-authored pulled companion of the named generated
comparator reselection. -/
noncomputable def canonicalCompanionPulledComparatorCoefficientTrivialUpperReselection :
    UpperGeometryCompatibleProblemInputData.CanonicalAuthoredPulledCoefficientTrivialUpperEdgeReselection
      problem.data :=
  problem.data.canonicalAuthoredPulledCoefficientTrivialReselectionBackward
    generatedPulledComparatorCoefficientTrivialUpperReselection

/-- The named generated full pair transports to a native canonical-authored
full pair on the named companion solution. -/
theorem canonicalCompanionComparatorUpperReselections_paired_fires :
    UpperGeometryCompatibleProblemInputData.CanonicalAuthoredPairedCoefficientTrivialUpperReselection
      problem.data.canonicalCompanionUpperRefinementBCSolution
      canonicalCompanionBaseComparatorCoefficientTrivialUpperReselection
      canonicalCompanionPulledComparatorCoefficientTrivialUpperReselection := by
  change
    UpperGeometryCompatibleProblemInputData.CanonicalAuthoredPairedCoefficientTrivialUpperReselection
      (problem.data.generatedSolutionBackward solution)
      (problem.data.canonicalAuthoredBaseCoefficientTrivialReselectionBackward
        generatedBaseComparatorCoefficientTrivialUpperReselection)
      (problem.data.canonicalAuthoredPulledCoefficientTrivialReselectionBackward
        generatedPulledComparatorCoefficientTrivialUpperReselection)
  exact
    problem.data.canonicalAuthoredPairedCoefficientTrivialUpperReselection_backward_transport
      generatedComparatorUpperReselections_paired_fires

/-- The canonical-authored base companion remains genuinely nonidentity; an
identity collapse would transport forward to the already refuted generated
identity collapse. -/
theorem canonicalCompanionBaseComparatorCoefficientTrivialUpperReselection_ne_one :
    canonicalCompanionBaseComparatorCoefficientTrivialUpperReselection ≠
      CoefficientTrivialUpperEdgeReselection.one
        problem.data.canonicalAuthoredBaseRouteTransport := by
  intro equality
  change
    problem.data.canonicalAuthoredBaseCoefficientTrivialReselectionBackward
        generatedBaseComparatorCoefficientTrivialUpperReselection =
      CoefficientTrivialUpperEdgeReselection.one
        problem.data.canonicalAuthoredBaseRouteTransport at equality
  have transported := congrArg
    problem.data.canonicalAuthoredBaseCoefficientTrivialReselectionForward
    equality
  rw [problem.data.canonicalAuthoredBaseCoefficientTrivialReselectionForward_backward,
    problem.data.canonicalAuthoredBaseCoefficientTrivialReselectionForward_one]
    at transported
  exact generatedBaseComparatorCoefficientTrivialUpperReselection_ne_one
    transported

end UpperDecisionWitness

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
