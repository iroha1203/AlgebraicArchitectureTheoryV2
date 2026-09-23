import ResearchLean.AG.FullGeometryNormalization.SemanticDerivedBarAlphaTriangle
import ResearchLean.AG.FullGeometryNormalization.SemanticDerivedCoreEndpointProjection

/-!
# Projection of the semantic comparison after the right lift

The complete geometry triangle, the via-base core endpoint comparison, and
the bottom tower comparison give the left side of the core projection square
after the top and right lifts.
-/

namespace AAT.AG.FullGeometryNormalization

universe u v

open CategoryTheory AtomFoundation GeometryTransport CrossStageCoherence
open DoctrineFiberProduct

set_option maxHeartbeats 3000000

/-- The projected complete comparison, after the top lift and selected right
core lift, is the left geometry pull lift followed by bottom core transport. -/
theorem semanticDerivedBarAlpha_left_post_fac
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U) (Q : AATCorePackage U)
    (k : Type v) [CommRing k] (g : FixedCoefficientGeometryAt Q k)
    (endpoint_eq : packagePoint Q = input.square.southwest)
    (square_isPullback : IsPullback input.square.left input.square.top
      input.square.bottom input.square.right) :
    (geometryProjection U).map
        (geomFiberLift input.square.top
          (semanticDerivedLeftPulledGeometryAt input Q k g endpoint_eq)) ≫
      ((geometryFiberProjection input.square.northeast).map
        (semanticDerivedBarAlphaIsoAt input Q k g endpoint_eq
          square_isPullback).hom).1 ≫
      (semanticDerivedViaBaseCoreIsoAt input Q k g endpoint_eq).hom.1 ≫
      (exact_bottom_semantic_global_selected_lift input.square.right
        ((coreFiberTransportFunctor input.square.bottom).obj
          ((geometryFiberProjection input.square.southwest).obj
            (semanticDerivedSouthwestGeometryFiber input Q k g endpoint_eq)))).hom =
    (geometryProjection U).map
        (semanticGeometryPullLift input.square.left
          (semanticDerivedSouthwestGeometryFiber input Q k g endpoint_eq)) ≫
      coreFiberLift input.square.bottom
        ((geometryFiberProjection input.square.southwest).obj
          (semanticDerivedSouthwestGeometryFiber input Q k g endpoint_eq)) := by
  have hvia := semanticDerivedViaBaseCoreIsoAt_right_fac
    input Q k g endpoint_eq
  have htriangle := congrArg (geometryProjection U).map
    (semanticDerivedBarAlphaIsoAt_triangle
      input Q k g endpoint_eq square_isPullback)
  have hbottom := towerTransportComparisonApp_hom_fac
    input.square.bottom
    (semanticDerivedSouthwestGeometryFiber input Q k g endpoint_eq)
  simp only [Functor.map_comp] at htriangle
  change
    (geometryProjection U).map
        (geomFiberLift input.square.top
          (semanticDerivedLeftPulledGeometryAt input Q k g endpoint_eq)) ≫
      (geometryProjection U).map
        (semanticDerivedBarAlphaIsoAt input Q k g endpoint_eq
          square_isPullback).hom.1 ≫
      (semanticDerivedViaBaseCoreIsoAt input Q k g endpoint_eq).hom.1 ≫
      (exact_bottom_semantic_global_selected_lift input.square.right
        ((coreFiberTransportFunctor input.square.bottom).obj
          ((geometryFiberProjection input.square.southwest).obj
            (semanticDerivedSouthwestGeometryFiber input Q k g endpoint_eq)))).hom = _
  rw [hvia]
  let topLift := (geometryProjection U).map
    (geomFiberLift input.square.top
      (semanticDerivedLeftPulledGeometryAt input Q k g endpoint_eq))
  let bar := (geometryProjection U).map
    (semanticDerivedBarAlphaIsoAt input Q k g endpoint_eq
      square_isPullback).hom.1
  let pullRight := (geometryProjection U).map
    (semanticGeometryPullLift input.square.right
      (semanticDerivedTargetGeometryAt input Q k g endpoint_eq))
  let pullLeft := (geometryProjection U).map
    (semanticGeometryPullLift input.square.left
      (semanticDerivedSouthwestGeometryFiber input Q k g endpoint_eq))
  let bottomLift := (geometryProjection U).map
    (geomFiberLift input.square.bottom
      (semanticDerivedSouthwestGeometryFiber input Q k g endpoint_eq))
  let tower := (towerTransportComparisonApp input.square.bottom
    (semanticDerivedSouthwestGeometryFiber input Q k g endpoint_eq)).hom.1
  change topLift ≫ (bar ≫ (pullRight ≫ tower)) =
    pullLeft ≫ coreFiberLift input.square.bottom
      ((geometryFiberProjection input.square.southwest).obj
        (semanticDerivedSouthwestGeometryFiber input Q k g endpoint_eq))
  calc
    _ = (topLift ≫ (bar ≫ pullRight)) ≫ tower := by
      simp only [Category.assoc]
    _ = (pullLeft ≫ bottomLift) ≫ tower :=
      congrArg (fun h => h ≫ tower) htriangle
    _ = pullLeft ≫ (bottomLift ≫ tower) := Category.assoc _ _ _
    _ = _ := congrArg (fun h => pullLeft ≫ h) hbottom

end AAT.AG.FullGeometryNormalization

#assert_standard_axioms_only AAT.AG.FullGeometryNormalization
