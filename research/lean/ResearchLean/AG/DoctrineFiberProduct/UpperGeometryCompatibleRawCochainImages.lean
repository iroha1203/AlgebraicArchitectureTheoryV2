import ResearchLean.AG.DoctrineFiberProduct.UpperGeometryCompatibleCanonicalComparators

/-!
# Raw-cochain images on the two compatible routes

The generated route cochains are not additional input.  Each is the pointwise
image of the source raw cochain under the corresponding generated
composite-fiber group homomorphism.  The proof uses preservation of products
and inverses together with the two canonical-comparator pullback theorems.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u v

open CategoryTheory AtomFoundation GeometryTransport CrossStageCoherence
open TransportCoherence

namespace UpperGeometryCompatibleProblemInputData

/-- The generated base raw cochain is the pointwise image of the source raw cochain. -/
theorem generatedBaseRouteRawDefectCochain_eq_image
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (cell : P.TwoCell) :
    input.generatedBaseRouteRawDefectCochain cell =
      input.generatedBaseCompositeFiberAutHomAt (P.twoTarget cell)
        (input.compatibleSourceRawDefectCochain cell) := by
  rw [input.generatedBaseRouteRawDefectCochain_apply,
    input.compatibleSourceRawDefectCochain_apply]
  unfold upperRawTwoCellDefect
  rw [map_mul, map_inv, input.generatedBaseCompositeFiberAutHomAt_apply,
    input.generatedBaseRouteCanonicalComparator_eq_pullback]
  rfl

/-- The generated pulled raw cochain is independently the source cochain image. -/
theorem generatedPulledRouteRawDefectCochain_eq_image
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (cell : P.TwoCell) :
    input.generatedPulledRouteRawDefectCochain cell =
      input.generatedPulledCompositeFiberAutHomAt (P.twoTarget cell)
        (input.compatibleSourceRawDefectCochain cell) := by
  rw [input.generatedPulledRouteRawDefectCochain_apply,
    input.compatibleSourceRawDefectCochain_apply]
  unfold upperRawTwoCellDefect
  rw [map_mul, map_inv, input.generatedPulledCompositeFiberAutHomAt_apply,
    input.generatedPulledRouteCanonicalComparator_eq_pullback]
  rfl

end UpperGeometryCompatibleProblemInputData

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
