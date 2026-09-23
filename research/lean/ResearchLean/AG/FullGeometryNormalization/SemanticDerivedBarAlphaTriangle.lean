import ResearchLean.AG.FullGeometryNormalization.SemanticDerivedLiteralMateFactor

/-!
# The semantic complete-geometry Beck--Chevalley triangle

The unit, literal Cartesian mate, and counit combine to identify the two
actual routes from the northwest geometry to the southeast geometry.
-/

namespace AAT.AG.FullGeometryNormalization

universe u v

open CategoryTheory AtomFoundation GeometryTransport CrossStageCoherence
open DoctrineFiberProduct

set_option maxHeartbeats 3000000

noncomputable local instance semanticTriangleAtomDecidableEq
    (U : AtomCarrier.{u}) : DecidableEq U.Atom := Classical.decEq _

/-- Naturality of top transport at the pulled bottom unit. -/
private theorem semanticDerivedTopPush_unit_fac
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U) (Q : AATCorePackage U)
    (k : Type v) [CommRing k] (g : FixedCoefficientGeometryAt Q k)
    (endpoint_eq : packagePoint Q = input.square.southwest) :
    geomFiberLift input.square.top
        (semanticDerivedLeftPulledGeometryAt input Q k g endpoint_eq) ≫
      (semanticDerivedUnitTopPushIsoAt input Q k g endpoint_eq).hom.1 =
    ((semanticGeometryPullFunctor input.square.left).map
      ((semanticGeometryTransportPullUnit input.square.bottom).app
        (semanticDerivedSouthwestGeometryFiber input Q k g endpoint_eq))).1 ≫
      geomFiberLift input.square.top
        (semanticDerivedBGeometryAt input Q k g endpoint_eq) := by
  change geomFiberLift input.square.top _ ≫
      (geomFiberTransportMap input.square.top _).1 =
    _ ≫ geomFiberLift input.square.top _
  exact geomFiberTransportMap_fac input.square.top _

/-- Naturality of top transport at the literal mate. -/
private theorem semanticDerivedTopMate_push_fac
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U) (Q : AATCorePackage U)
    (k : Type v) [CommRing k] (g : FixedCoefficientGeometryAt Q k)
    (endpoint_eq : packagePoint Q = input.square.southwest) :
    geomFiberLift input.square.top
        (semanticDerivedBGeometryAt input Q k g endpoint_eq) ≫
      ((geomFiberTransportFunctor input.square.top).map
        (semanticDerivedLiteralMateNorthwestIsoAt
          input Q k g endpoint_eq).hom).1 =
    (semanticDerivedLiteralMateNorthwestIsoAt
        input Q k g endpoint_eq).hom.1 ≫
      geomFiberLift input.square.top
        (semanticDerivedTGeometryAt input Q k g endpoint_eq) := by
  change geomFiberLift input.square.top _ ≫
      (geomFiberTransportMap input.square.top _).1 =
    _ ≫ geomFiberLift input.square.top _
  exact geomFiberTransportMap_fac input.square.top _

/-- The top counit followed by right pullback is the literal pulled route. -/
private theorem semanticDerivedTopCounit_pulled_fac
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U) (Q : AATCorePackage U)
    (k : Type v) [CommRing k] (g : FixedCoefficientGeometryAt Q k)
    (endpoint_eq : packagePoint Q = input.square.southwest) :
    geomFiberLift input.square.top
        (semanticDerivedTGeometryAt input Q k g endpoint_eq) ≫
      (semanticDerivedTopCounitIsoAt input Q k g endpoint_eq).hom.1 ≫
      semanticGeometryPullLift input.square.right
        (semanticDerivedTargetGeometryAt input Q k g endpoint_eq) =
    semanticDerivedDirectPulledRouteLegAt input Q k g endpoint_eq := by
  have h := semanticGeometryTransportPullCounit_app_fac
    input.square.top
    (semanticDerivedViaBaseGeometryAt input Q k g endpoint_eq)
  have h' := congrArg (fun f => f ≫
    semanticGeometryPullLift input.square.right
      (semanticDerivedTargetGeometryAt input Q k g endpoint_eq)) h
  simpa only [semanticDerivedDirectPulledRouteLegAt,
    Category.assoc] using h'

/-- The bottom unit, after the left pullback, gives the direct base route leg. -/
private theorem semanticDerivedLeftUnit_baseRoute_fac
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U) (Q : AATCorePackage U)
    (k : Type v) [CommRing k] (g : FixedCoefficientGeometryAt Q k)
    (endpoint_eq : packagePoint Q = input.square.southwest) :
    ((semanticGeometryPullFunctor input.square.left).map
      ((semanticGeometryTransportPullUnit input.square.bottom).app
        (semanticDerivedSouthwestGeometryFiber input Q k g endpoint_eq))).1 ≫
      semanticDerivedDirectBaseRouteLegAt input Q k g endpoint_eq =
    semanticGeometryPullLift input.square.left
        (semanticDerivedSouthwestGeometryFiber input Q k g endpoint_eq) ≫
      geomFiberLift input.square.bottom
        (semanticDerivedSouthwestGeometryFiber input Q k g endpoint_eq) := by
  let S := semanticDerivedSouthwestGeometryFiber input Q k g endpoint_eq
  let target := semanticDerivedTargetGeometryAt input Q k g endpoint_eq
  let unit := (semanticGeometryTransportPullUnit input.square.bottom).app S
  have hleft : ((semanticGeometryPullFunctor input.square.left).map unit).1 ≫
      semanticGeometryPullLift input.square.left
        (semanticDerivedBottomPulledTargetGeometryAt input Q k g endpoint_eq) =
      semanticGeometryPullLift input.square.left S ≫ unit.1 := by
    change (semanticGeometryPullMap input.square.left unit).1 ≫
      semanticGeometryPullLift input.square.left
        ((semanticGeometryPullFunctor input.square.bottom).obj target) =
      semanticGeometryPullLift input.square.left S ≫ unit.1
    exact semanticGeometryPullMap_fac input.square.left unit
  have hbottom : unit.1 ≫
      semanticGeometryPullLift input.square.bottom target =
      geomFiberLift input.square.bottom S := by
    change ((semanticGeometryTransportPullUnit input.square.bottom).app S).1 ≫
      semanticGeometryPullLift input.square.bottom
        ((geomFiberTransportFunctor input.square.bottom).obj S) =
      geomFiberLift input.square.bottom S
    exact semanticGeometryTransportPullUnit_app_fac input.square.bottom S
  change ((semanticGeometryPullFunctor input.square.left).map unit).1 ≫
      (semanticGeometryPullLift input.square.left
        (semanticDerivedBottomPulledTargetGeometryAt input Q k g endpoint_eq) ≫
        semanticGeometryPullLift input.square.bottom target) = _
  rw [← Category.assoc, hleft, Category.assoc, hbottom]

/-- Expose the total arrow of the three-factor semantic comparison once,
outside the larger route triangle. -/
private theorem semanticDerivedBarAlpha_total_hom
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U) (Q : AATCorePackage U)
    (k : Type v) [CommRing k] (g : FixedCoefficientGeometryAt Q k)
    (endpoint_eq : packagePoint Q = input.square.southwest)
    (square_isPullback : IsPullback input.square.left input.square.top
      input.square.bottom input.square.right) :
    (semanticDerivedBarAlphaIsoAt
      input Q k g endpoint_eq square_isPullback).hom.1 =
      (semanticDerivedUnitTopPushIsoAt input Q k g endpoint_eq).hom.1 ≫
      ((geomFiberTransportFunctor input.square.top).map
        (semanticDerivedLiteralMateNorthwestIsoAt
          input Q k g endpoint_eq).hom).1 ≫
      (semanticDerivedTopCounitIsoAt input Q k g endpoint_eq).hom.1 := by
  rfl

/-- The generated complete semantic comparison satisfies the two-route
triangle over the original square. -/
theorem semanticDerivedBarAlphaIsoAt_triangle
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U) (Q : AATCorePackage U)
    (k : Type v) [CommRing k] (g : FixedCoefficientGeometryAt Q k)
    (endpoint_eq : packagePoint Q = input.square.southwest)
    (square_isPullback : IsPullback input.square.left input.square.top
      input.square.bottom input.square.right) :
    geomFiberLift input.square.top
        (semanticDerivedLeftPulledGeometryAt input Q k g endpoint_eq) ≫
      (semanticDerivedBarAlphaIsoAt
        input Q k g endpoint_eq square_isPullback).hom.1 ≫
      semanticGeometryPullLift input.square.right
        (semanticDerivedTargetGeometryAt input Q k g endpoint_eq) =
    semanticGeometryPullLift input.square.left
        (semanticDerivedSouthwestGeometryFiber input Q k g endpoint_eq) ≫
      geomFiberLift input.square.bottom
        (semanticDerivedSouthwestGeometryFiber input Q k g endpoint_eq) := by
  rw [semanticDerivedBarAlpha_total_hom]
  let S := semanticDerivedSouthwestGeometryFiber input Q k g endpoint_eq
  let target := semanticDerivedTargetGeometryAt input Q k g endpoint_eq
  let L := semanticDerivedLeftPulledGeometryAt input Q k g endpoint_eq
  let unitPull := (semanticGeometryPullFunctor input.square.left).map
    ((semanticGeometryTransportPullUnit input.square.bottom).app S)
  let mate := (semanticDerivedLiteralMateNorthwestIsoAt
    input Q k g endpoint_eq).hom
  slice_lhs 1 2 => rw [semanticDerivedTopPush_unit_fac]
  slice_lhs 2 3 => rw [semanticDerivedTopMate_push_fac]
  slice_lhs 3 5 => rw [semanticDerivedTopCounit_pulled_fac]
  change unitPull.1 ≫ mate.1 ≫
      semanticDerivedDirectPulledRouteLegAt input Q k g endpoint_eq = _
  rw [semanticDerivedLiteralMateNorthwestIsoAt_hom_fac]
  exact semanticDerivedLeftUnit_baseRoute_fac input Q k g endpoint_eq

end AAT.AG.FullGeometryNormalization

#assert_standard_axioms_only AAT.AG.FullGeometryNormalization
