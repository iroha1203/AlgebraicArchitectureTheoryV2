import ResearchLean.AG.DoctrineFiberProduct.UpperGeometryCompatibleRawCochainImages
import ResearchLean.AG.CrossStageCoherence.Unification

/-!
# Pseudofunctor coherence on compatible finite routes

The literal empty source path is identified with the canonical identity lift
through the genuine geometry-fiber unitor.  For each two-cell, the genuine
pseudofunctor-compositor normalization on both generated routes is then
identified with the Cartesian pullback of the corresponding source
normalization.  Thus the finite route coherence is not inferred merely from
group map laws or recursive path evaluation.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u v

open CategoryTheory AtomFoundation GeometryTransport CrossStageCoherence
open TransportCoherence

set_option maxHeartbeats 3000000

namespace UpperGeometryCompatibleProblemInputData

/-- The genuine geometry-fiber unitor normalizes the canonical identity lift
to the literal empty path in the authored source transport. -/
theorem compatibleSourceRoutePathNil_unitor
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (i : P.Vertex) :
    geomFiberLift
          (𝟙 (packagePoint (input.sourceGeometry i).package.core))
          (geomFiberMk (input.sourceGeometry i).package) ≫
        (geomFiberUnitorApp
          (packagePoint (input.sourceGeometry i).package.core)
          (geomFiberMk (input.sourceGeometry i).package)).hom.1 =
      input.compatibleSourceRouteData.lift.pathLift (.nil i) := by
  simpa only [TwoLayerLiftData.pathLift] using
    geomFiberUnitorApp_hom_fac
      (packagePoint (input.sourceGeometry i).package.core)
      (geomFiberMk (input.sourceGeometry i).package)

/-- The package projection of the same unitor normalization is the literal
empty-path package identity. -/
theorem compatibleSourceRoutePathNil_unitor_base
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (i : P.Vertex) :
    (geomFiberLift
          (𝟙 (packagePoint (input.sourceGeometry i).package.core))
          (geomFiberMk (input.sourceGeometry i).package)).base.comp
        (geomFiberUnitorApp
          (packagePoint (input.sourceGeometry i).package.core)
          (geomFiberMk (input.sourceGeometry i).package)).hom.1.base =
      (input.compatibleSourceRouteData.lift.pathLift (.nil i)).base := by
  exact congrArg GeometryTotalHom.base
    (input.compatibleSourceRoutePathNil_unitor i)

/-- The generated base-route pseudofunctor compositor normalization is the
Cartesian pullback of the source normalization. -/
theorem generatedBaseRoutePseudofunctorComparator_eq_pullback
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (cell : P.TwoCell) :
    pseudofunctorCanonicalComparator input.generatedBaseRouteData 1 cell =
      input.generatedBaseCompositeFiberAutAt (P.twoTarget cell)
        (pseudofunctorCanonicalComparator
          input.compatibleSourceRouteData 1 cell) := by
  rw [pseudofunctorCanonicalComparator_eq_upper,
    input.generatedBaseRouteCanonicalComparator_eq_pullback,
    pseudofunctorCanonicalComparator_eq_upper]

/-- The pulled route satisfies the independently generated compositor
normalization compatibility. -/
theorem generatedPulledRoutePseudofunctorComparator_eq_pullback
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (cell : P.TwoCell) :
    pseudofunctorCanonicalComparator input.generatedPulledRouteData 1 cell =
      input.generatedPulledCompositeFiberAutAt (P.twoTarget cell)
        (pseudofunctorCanonicalComparator
          input.compatibleSourceRouteData 1 cell) := by
  rw [pseudofunctorCanonicalComparator_eq_upper,
    input.generatedPulledRouteCanonicalComparator_eq_pullback,
    pseudofunctorCanonicalComparator_eq_upper]

end UpperGeometryCompatibleProblemInputData

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
