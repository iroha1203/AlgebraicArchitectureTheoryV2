import ResearchLean.AG.FullGeometryNormalization.ExactGeometryPullProjection
import ResearchLean.AG.FullGeometryNormalization.ExactGeometryTransportAdjunction
import ResearchLean.AG.DoctrineFiberProduct.CoreTransportReindexAdjunction

/-!
# Core projection of the exact complete-geometry adjunction

The complete-geometry transport/pullback adjunction and the existing core
transport/reindexing adjunction are generated independently from their
respective cocartesian and cartesian cleavages.  This module proves that their
unit and counit agree after inserting the canonical tower comparison for
transport and the canonical exact-pull projection comparison.

Both equations are forced by the defining lift factorizations and the
corresponding universal-property uniqueness theorem.  No component equality,
comparison morphism, or compatibility certificate is accepted from the
caller.
-/

namespace AAT.AG.FullGeometryNormalization

universe u v

open CategoryTheory AtomFoundation GeometryTransport CrossStageCoherence
open DoctrineFiberProduct

set_option maxHeartbeats 3000000

/-- Projection of the complete-geometry unit is the core
transport/reindexing unit, after transporting its codomain through the exact
pull and tower comparison isomorphisms. -/
theorem exactGeometryTransportPullUnit_projection
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : RealizableHom U)
    (source : GeomFiber.{u, v} input.semantic.source) :
    (geometryFiberProjection input.semantic.source).map
          ((exactGeometryTransportPullUnit input).app source) ≫
        (exactGeometryPullProjectionIsoApp input
          ((geomFiberTransportFunctor input.semantic.hom).obj source)).hom ≫
        (selectedCoreFiberReindexFunctor input).map
          (towerTransportComparisonApp input.semantic.hom source).hom =
      (coreTransportReindexUnit input).app
        ((geometryFiberProjection input.semantic.source).obj source) := by
  apply CategoryTheory.Functor.Fiber.hom_ext
  let targetPackage :=
    (coreFiberTransportFunctor input.semantic.hom).obj
      ((geometryFiberProjection input.semantic.source).obj source)
  let selectedLift := selectedCoreFiberCartesianLift input targetPackage
  letI : (packageProjection U).IsStronglyCartesian
      input.semantic.hom selectedLift.hom := selectedLift.isStronglyCartesian
  apply CategoryTheory.Functor.IsStronglyCartesian.ext
    (packageProjection U) input.semantic.hom selectedLift.hom
    (𝟙 input.semantic.source)
  change
    (((exactGeometryTransportPullUnit input).app source).1.base ≫
        (exactGeometryPullProjectionIsoApp input
          ((geomFiberTransportFunctor input.semantic.hom).obj source)).hom.1 ≫
        ((selectedCoreFiberReindexFunctor input).map
          (towerTransportComparisonApp input.semantic.hom source).hom).1) ≫
        selectedLift.hom =
      ((coreTransportReindexUnit input).app
        ((geometryFiberProjection input.semantic.source).obj source)).1 ≫
        selectedLift.hom
  rw [coreTransportReindexUnit_app_fac]
  dsimp only [selectedLift, targetPackage]
  let projectedPush :=
    (geometryFiberProjection input.semantic.target).obj
      ((geomFiberTransportFunctor input.semantic.hom).obj source)
  let projectedPullLift := selectedCoreFiberCartesianLift input projectedPush
  have reindexFac :
      ((selectedCoreFiberReindexFunctor input).map
          (towerTransportComparisonApp input.semantic.hom source).hom).1 ≫
          (selectedCoreFiberCartesianLift input
            ((coreFiberTransportFunctor input.semantic.hom).obj
              ((geometryFiberProjection input.semantic.source).obj source))).hom =
        projectedPullLift.hom ≫
          (towerTransportComparisonApp input.semantic.hom source).hom.1 := by
    simpa only [projectedPullLift, projectedPush] using
      selectedCoreFiberReindexFunctor_map_fac input
        (towerTransportComparisonApp input.semantic.hom source).hom
  calc
    _ = ((exactGeometryTransportPullUnit input).app source).1.base ≫
        (exactGeometryPullProjectionIsoApp input
          ((geomFiberTransportFunctor input.semantic.hom).obj source)).hom.1 ≫
        (projectedPullLift.hom ≫
          (towerTransportComparisonApp input.semantic.hom source).hom.1) := by
      simpa only [Category.assoc] using congrArg
        (fun k => ((exactGeometryTransportPullUnit input).app source).1.base ≫
          (exactGeometryPullProjectionIsoApp input
            ((geomFiberTransportFunctor input.semantic.hom).obj source)).hom.1 ≫ k)
        reindexFac
    _ = ((exactGeometryTransportPullUnit input).app source).1.base ≫
        ((geometryProjection U).map
          (exactGeometryPullLift input
            ((geomFiberTransportFunctor input.semantic.hom).obj source)) ≫
          (towerTransportComparisonApp input.semantic.hom source).hom.1) := by
      rw [← exactGeometryPullProjectionIsoApp_hom_fac]
      rfl
    _ = (geometryProjection U).map
          (((exactGeometryTransportPullUnit input).app source).1 ≫
            exactGeometryPullLift input
              ((geomFiberTransportFunctor input.semantic.hom).obj source)) ≫
        (towerTransportComparisonApp input.semantic.hom source).hom.1 := by
      exact (Category.assoc _ _ _).symm
    _ = (geometryProjection U).map
          (geomFiberLift input.semantic.hom source) ≫
        (towerTransportComparisonApp input.semantic.hom source).hom.1 := by
      rw [exactGeometryTransportPullUnit_app_fac]
    _ = _ := towerTransportComparisonApp_hom_fac input.semantic.hom source

/-- Projection of the complete-geometry counit is the core
transport/reindexing counit, after transporting its domain through the tower
and exact-pull comparison isomorphisms. -/
theorem exactGeometryTransportPullCounit_projection
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : RealizableHom U)
    (target : GeomFiber.{u, v} input.semantic.target) :
    (geometryFiberProjection input.semantic.target).map
        ((exactGeometryTransportPullCounit input).app target) =
      (towerTransportComparisonApp input.semantic.hom
          ((exactGeometryPullFunctor input).obj target)).hom ≫
        (coreFiberTransportFunctor input.semantic.hom).map
          (exactGeometryPullProjectionIsoApp input target).hom ≫
        (coreTransportReindexCounit input).app
          ((geometryFiberProjection input.semantic.target).obj target) := by
  apply CategoryTheory.Functor.Fiber.hom_ext
  let pulled := (exactGeometryPullFunctor input).obj target
  let projectedPushLift := (geometryProjection U).map
    (geomFiberLift input.semantic.hom pulled)
  letI : (packageProjection U).IsStronglyCocartesian
      input.semantic.hom projectedPushLift :=
    projectedGeomFiberLift_isStronglyCocartesian input.semantic.hom pulled
  apply CategoryTheory.Functor.IsStronglyCocartesian.ext
    (packageProjection U) input.semantic.hom projectedPushLift
    (𝟙 input.semantic.target)
  change
    projectedPushLift ≫
        ((exactGeometryTransportPullCounit input).app target).1.base =
      projectedPushLift ≫
        ((towerTransportComparisonApp input.semantic.hom
          ((exactGeometryPullFunctor input).obj target)).hom.1 ≫
        ((coreFiberTransportFunctor input.semantic.hom).map
          (exactGeometryPullProjectionIsoApp input target).hom).1 ≫
        ((coreTransportReindexCounit input).app
          ((geometryFiberProjection input.semantic.target).obj target)).1)
  let projectedPull :=
    (geometryFiberProjection input.semantic.source).obj pulled
  let selectedLift := selectedCoreFiberCartesianLift input
    ((geometryFiberProjection input.semantic.target).obj target)
  calc
    _ = (geometryProjection U).map
        (geomFiberLift input.semantic.hom pulled ≫
          ((exactGeometryTransportPullCounit input).app target).1) := by
      dsimp only [projectedPushLift, pulled]
      exact ((geometryProjection U).map_comp _ _).symm
    _ = (geometryProjection U).map (exactGeometryPullLift input target) := by
      rw [exactGeometryTransportPullCounit_app_fac]
    _ = (exactGeometryPullProjectionIsoApp input target).hom.1 ≫
        selectedLift.hom := by
      exact (exactGeometryPullProjectionIsoApp_hom_fac input target).symm
    _ = (exactGeometryPullProjectionIsoApp input target).hom.1 ≫
        (coreFiberLift input.semantic.hom
            ((selectedCoreFiberReindexFunctor input).obj
              ((geometryFiberProjection input.semantic.target).obj target)) ≫
          ((coreTransportReindexCounit input).app
            ((geometryFiberProjection input.semantic.target).obj target)).1) := by
      rw [coreTransportReindexCounit_app_fac]
    _ = (coreFiberLift input.semantic.hom projectedPull ≫
          ((coreFiberTransportFunctor input.semantic.hom).map
            (exactGeometryPullProjectionIsoApp input target).hom).1) ≫
        ((coreTransportReindexCounit input).app
          ((geometryFiberProjection input.semantic.target).obj target)).1 := by
      have transportFac :
          coreFiberLift input.semantic.hom projectedPull ≫
              ((coreFiberTransportFunctor input.semantic.hom).map
                (exactGeometryPullProjectionIsoApp input target).hom).1 =
            (exactGeometryPullProjectionIsoApp input target).hom.1 ≫
              coreFiberLift input.semantic.hom
                ((selectedCoreFiberReindexFunctor input).obj
                  ((geometryFiberProjection input.semantic.target).obj target)) := by
        simpa only [projectedPull, pulled] using
          coreFiberTransportMap_fac input.semantic.hom
            (exactGeometryPullProjectionIsoApp input target).hom
      simpa only [Category.assoc] using congrArg
        (fun k => k ≫ ((coreTransportReindexCounit input).app
          ((geometryFiberProjection input.semantic.target).obj target)).1)
        transportFac.symm
    _ = (projectedPushLift ≫
          (towerTransportComparisonApp input.semantic.hom pulled).hom.1) ≫
        (((coreFiberTransportFunctor input.semantic.hom).map
            (exactGeometryPullProjectionIsoApp input target).hom).1 ≫
          ((coreTransportReindexCounit input).app
            ((geometryFiberProjection input.semantic.target).obj target)).1) := by
      have towerFac : projectedPushLift ≫
          (towerTransportComparisonApp input.semantic.hom pulled).hom.1 =
        coreFiberLift input.semantic.hom projectedPull := by
        simpa only [projectedPushLift, projectedPull] using
          towerTransportComparisonApp_hom_fac input.semantic.hom pulled
      simpa only [Category.assoc] using congrArg
        (fun k => k ≫
          ((coreFiberTransportFunctor input.semantic.hom).map
            (exactGeometryPullProjectionIsoApp input target).hom).1 ≫
          ((coreTransportReindexCounit input).app
            ((geometryFiberProjection input.semantic.target).obj target)).1)
        towerFac.symm
    _ = _ := by rfl

end AAT.AG.FullGeometryNormalization

#assert_standard_axioms_only AAT.AG.FullGeometryNormalization
