import ResearchLean.AG.DoctrineFiberProduct.UpperGeometryCompatibleGlobalMate
import ResearchLean.AG.DoctrineFiberProduct.UpperGeometryCanonicalAuthoredTransportLaws
import ResearchLean.AG.DoctrineFiberProduct.UpperGeometryCompatibleSolutionEquivalence
import ResearchLean.AG.DoctrineFiberProduct.UpperGeometryPairedCoefficientTrivialReselection

/-!
# Qualified comparison transport: F0 typing surface

This cycle scaffold checks the universe, endpoint, and variance alignment of the
fixed G-118 source map before the comparison stabilizer is constructed.  It
adds no certificate or conclusion-bearing structure: the examples below only
ask Lean to elaborate the already reviewed G-115 producers at the exact types
named by the G-118 card.

Implementation notes: the source map is checked through the public bundled
group homomorphisms, complete geometry mate, exact endpoint isomorphisms, and
the fixed decision datum.  Replacing these with new wrappers would obscure
their provenance, so this scaffold keeps the existing declarations literal.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u v

noncomputable section

open CategoryTheory AtomFoundation GeometryTransport CrossStageCoherence
open TransportCoherence

namespace QualifiedComparisonTransportTyping

section GeneralInput

variable {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
variable {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
variable (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex)

example :
    CompositeFiberAut (input.sourceGeometry i).package →*
      CompositeFiberAut (input.generatedBaseRouteGeometryAt i) :=
  input.generatedBaseCompositeFiberAutHomAt i

example :
    CompositeFiberAut (input.sourceGeometry i).package →*
      CompositeFiberAut (input.generatedPulledRouteGeometryAt i) :=
  input.generatedPulledCompositeFiberAutHomAt i

example :
    GeometryTotalHom (input.generatedBaseRouteGeometryAt i)
      (input.generatedPulledRouteGeometryAt i) :=
  input.generatedCompatibleUpperGeometryMateAt i

example :
    GeomReadHom (input.generatedBaseRouteGeometryAt i)
      (input.generatedPulledRouteGeometryAt i)
      (input.generatedCompatibleUpperGeometryMateAt i).base :=
  (input.generatedCompatibleUpperGeometryMateAt i).geometry

example (baseChange pulledChange :
    CompositeFiberAut (input.sourceGeometry i).package) : Prop :=
  (CompositeFiberAut.hom
      (input.generatedBaseCompositeFiberAutHomAt i baseChange)).comp
        (input.generatedCompatibleUpperGeometryMateAt i) =
    (input.generatedCompatibleUpperGeometryMateAt i).comp
      (CompositeFiberAut.hom
        (input.generatedPulledCompositeFiberAutHomAt i pulledChange))

example (automorphism : CompositeFiberAut (input.sourceGeometry i).package) :
    ((exactGeometryToRefinementGeometry U).map
      (CompositeFiberAut.hom
        (input.generatedBaseCompositeFiberAutAt i automorphism))).comp
        (input.generatedBaseRouteLegAt i) =
      input.generatedBaseGeometryComparatorCandidateAt i automorphism :=
  input.generatedBaseCompositeFiberAutAt_fac i automorphism

example (automorphism : CompositeFiberAut (input.sourceGeometry i).package) :
    ((exactGeometryToRefinementGeometry U).map
      (CompositeFiberAut.hom
        (input.generatedPulledCompositeFiberAutAt i automorphism))).comp
        (input.generatedPulledRouteLegAt i) =
      input.generatedPulledGeometryComparatorCandidateAt i automorphism :=
  input.generatedPulledCompositeFiberAutAt_fac i automorphism

example :
    input.canonicalAuthoredBaseRouteGeometryAt i ≅
      input.generatedBaseRouteGeometryAt i :=
  input.canonicalAuthoredBaseToGeneratedRouteExactGeometryIsoAt i

example :
    input.canonicalAuthoredPulledRouteGeometryAt i ≅
      input.generatedPulledRouteGeometryAt i :=
  input.canonicalAuthoredPulledToGeneratedRouteExactGeometryIsoAt i

example :
    CompositeFiberAut (input.canonicalAuthoredBaseRouteGeometryAt i) ≃*
      CompositeFiberAut (input.generatedBaseRouteGeometryAt i) :=
  CompositeFiberAut.conjugationMulEquiv
    (input.canonicalAuthoredBaseToGeneratedRouteExactGeometryIsoAt i)

example :
    CompositeFiberAut (input.canonicalAuthoredPulledRouteGeometryAt i) ≃*
      CompositeFiberAut (input.generatedPulledRouteGeometryAt i) :=
  CompositeFiberAut.conjugationMulEquiv
    (input.canonicalAuthoredPulledToGeneratedRouteExactGeometryIsoAt i)

example :
    (input.canonicalAuthoredBaseToGeneratedRouteExactGeometryHomAt
      i).geometry.coefficientHom = RingHom.id k :=
  input.canonicalAuthoredBaseToGeneratedRouteExactGeometryHomAt_coefficient_id i

example :
    (input.canonicalAuthoredBaseToGeneratedRouteExactGeometryInvAt
      i).geometry.coefficientHom = RingHom.id k :=
  input.canonicalAuthoredBaseToGeneratedRouteExactGeometryInvAt_coefficient_id i

example :
    (input.canonicalAuthoredPulledToGeneratedRouteExactGeometryHomAt
      i).geometry.coefficientHom = RingHom.id k :=
  input.canonicalAuthoredPulledToGeneratedRouteExactGeometryHomAt_coefficient_id i

example :
    (input.canonicalAuthoredPulledToGeneratedRouteExactGeometryInvAt
      i).geometry.coefficientHom = RingHom.id k :=
  input.canonicalAuthoredPulledToGeneratedRouteExactGeometryInvAt_coefficient_id i

example :
    UpperGeometryCompatibleProblemInputData.CanonicalUpperRefinementBCSolution input :=
  input.canonicalCompanionUpperRefinementBCSolution

example :
    UpperGeometryCompatibleProblemInputData.GeometryCompatibleUpperRefinementBCSolution input :=
  input.generatedGeometryCompatibleUpperRefinementBCSolution

example :
    UpperGeometryCompatibleProblemInputData.CanonicalUpperRefinementBCSolution input ≃
      UpperGeometryCompatibleProblemInputData.GeometryCompatibleUpperRefinementBCSolution input :=
  input.canonicalGeneratedUpperRefinementBCSolutionEquiv

example :
    input.canonicalSolutionForwardAt
        input.canonicalCompanionUpperRefinementBCSolution i =
      ((input.canonicalAuthoredBaseToGeneratedRouteExactGeometryInvAt i).comp
        (input.canonicalCompanionUpperRefinementBCSolution.component i)).comp
          (input.canonicalAuthoredPulledToGeneratedRouteExactGeometryHomAt i) :=
  input.canonicalSolutionForwardAt_exact_normalization
    input.canonicalCompanionUpperRefinementBCSolution i

example :
    input.generatedSolutionBackwardAt
        input.generatedGeometryCompatibleUpperRefinementBCSolution i =
      ((input.canonicalAuthoredBaseToGeneratedRouteExactGeometryHomAt i).comp
        (input.generatedGeometryCompatibleUpperRefinementBCSolution.component i)).comp
          (input.canonicalAuthoredPulledToGeneratedRouteExactGeometryInvAt i) :=
  input.generatedSolutionBackwardAt_exact_normalization
    input.generatedGeometryCompatibleUpperRefinementBCSolution i

example (cell : P.TwoCell) :
    (CompositeFiberAut.hom
      (input.generatedPulledIdentityComparatorTransport.comparator
        cell)).geometry.coefficientHom = RingHom.id k :=
  input.generatedPulledIdentityComparator_coefficient_id cell

end GeneralInput

section FixedDecisionDatum

example :
    UpperGeometryCompatibleProblemInputData.GeometryCompatibleUpperRefinementBCSolution
      UpperDecisionWitness.problem.data :=
  UpperDecisionWitness.solution

example :
    UpperGeometryCompatibleProblemInputData.GeometryCompatibleUpperRefinementBCSolution
      upperDecisionProblem.data :=
  upperDecisionSolution

example : UpperDecisionWitness.solution = upperDecisionSolution := rfl

example :
    UpperDecisionWitness.solution.component PUnit.unit =
      upperDecisionSolution.component PUnit.unit := rfl

example :
    UpperComparatorDescentAt
      UpperDecisionWitness.problem.data.generatedBaseRouteTransport
      UpperDecisionWitness.problem.data.generatedPulledRouteTransport
      UpperDecisionWitness.solution.component
      UpperDecisionWitness.DecisionCell.comparison :=
  UpperDecisionWitness.upperDecisionSolution_comparatorDescentAt

example :
    ¬ UpperComparatorDescentAt
      UpperDecisionWitness.problem.data.generatedBaseRouteTransport
      UpperDecisionWitness.problem.data.generatedPulledIdentityComparatorTransport
      UpperDecisionWitness.solution.component
      UpperDecisionWitness.DecisionCell.comparison :=
  UpperDecisionWitness.generatedBaseIdentityPair_not_comparatorDescentAt

example :
    UpperGeometryCompatibleProblemInputData.CoefficientTrivialUpperReselectionEndpointIntertwining
      UpperDecisionWitness.solution
      UpperDecisionWitness.generatedBaseComparatorCoefficientTrivialUpperReselection
      UpperDecisionWitness.generatedPulledComparatorCoefficientTrivialUpperReselection :=
  UpperDecisionWitness.generatedComparatorUpperReselections_endpointIntertwining_fires

example :
    ¬ UpperGeometryCompatibleProblemInputData.CoefficientTrivialUpperReselectionEndpointIntertwining
      UpperDecisionWitness.solution
      UpperDecisionWitness.generatedBaseComparatorCoefficientTrivialUpperReselection
      (CoefficientTrivialUpperEdgeReselection.one
        UpperDecisionWitness.problem.data.generatedPulledRouteTransport) :=
  UpperDecisionWitness.generatedBaseComparatorPulledIdentity_not_endpointIntertwining

end FixedDecisionDatum

end QualifiedComparisonTransportTyping

end

end AAT.AG.DoctrineFiberProduct
