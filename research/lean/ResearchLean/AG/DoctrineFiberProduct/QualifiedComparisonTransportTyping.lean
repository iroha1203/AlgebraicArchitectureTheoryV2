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
    input.canonicalAuthoredBaseRouteGeometryAt i ≅
      input.generatedBaseRouteGeometryAt i :=
  input.canonicalAuthoredBaseToGeneratedRouteExactGeometryIsoAt i

example :
    input.canonicalAuthoredPulledRouteGeometryAt i ≅
      input.generatedPulledRouteGeometryAt i :=
  input.canonicalAuthoredPulledToGeneratedRouteExactGeometryIsoAt i

example :
    UpperGeometryCompatibleProblemInputData.CanonicalUpperRefinementBCSolution input :=
  input.canonicalCompanionUpperRefinementBCSolution

example :
    UpperGeometryCompatibleProblemInputData.GeometryCompatibleUpperRefinementBCSolution input :=
  input.generatedGeometryCompatibleUpperRefinementBCSolution

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

#check UpperDecisionWitness.upperDecisionSolution_comparatorDescentAt
#check UpperDecisionWitness.generatedBaseIdentityPair_not_comparatorDescentAt
#check UpperDecisionWitness.generatedComparatorUpperReselections_endpointIntertwining_fires
#check UpperDecisionWitness.generatedBaseComparatorPulledIdentity_not_endpointIntertwining

end FixedDecisionDatum

#check CompositeFiberAut.conjugationMulEquiv
#check UpperGeometryCompatibleProblemInputData.canonicalSolutionForwardAt_exact_normalization
#check UpperGeometryCompatibleProblemInputData.generatedSolutionBackwardAt_exact_normalization

end QualifiedComparisonTransportTyping

end

end AAT.AG.DoctrineFiberProduct
