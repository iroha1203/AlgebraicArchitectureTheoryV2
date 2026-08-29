import ResearchLean.AG.DoctrineFiberProduct.UpperRefinementBCRoutes

/-!
# Geometry legs over the G-114 composite routes

This module indexes the G-114 composite package routes by an arbitrary target
package and types the two individual refinement-geometry legs over those actual
routes. Geometry transport is retained as direction data: it is not generated
from the core route.

The coefficient carrier is fixed definitionally across the three geometry
endpoints. This lets later finite upper problems state coefficient identity
without transports between merely equal types. No route-between component or
factorization equation is stored in the leg data.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u v

open CategoryTheory
open AtomFoundation
open GeometryTransport
open CrossStageCoherence

set_option maxHeartbeats 3000000

/-- Geometry and raw data over a fixed core package and coefficient ring. -/
structure FixedCoefficientGeometryAt
    {U : AtomCarrier.{u}} (Q : AATCorePackage U)
    (k : Type v) [CommRing k] where
  /-- Selected geometry on the fixed core package. -/
  geometry : Site.SelectedGeometryReading Q
  /-- Raw restriction data with the fixed coefficient ring. -/
  raw : LawAlgebra.RawAmbientRestrictionSystem geometry.toAATSite k

namespace FixedCoefficientGeometryAt

/-- Assemble the fixed-core, fixed-coefficient data as a geometry package. -/
def package {U : AtomCarrier.{u}} {Q : AATCorePackage U}
    {k : Type v} [CommRing k] (data : FixedCoefficientGeometryAt Q k) :
    GeometryPackage.{u, v} U where
  core := Q
  geometry := data.geometry
  Coefficient := k
  coefficientCommRing := inferInstance
  raw := data.raw

end FixedCoefficientGeometryAt

/-- Replace only the target package of an active context. -/
def ActiveRefinementBCContext.retarget
    {U : AtomCarrier.{u}} (ctx : ActiveRefinementBCContext U)
    (target : CoreFiber
      (ctx.configuration.targetPointAt ctx.source)) :
    ActiveRefinementBCContext U where
  configuration := ctx.configuration
  source := ctx.source
  targetPackage := target
  condition := ctx.condition

/-- The base-side composite route evaluated at an arbitrary target package. -/
noncomputable def ActiveRefinementBCContext.baseCompositeLegAt
    {U : AtomCarrier.{u}} (ctx : ActiveRefinementBCContext U)
    (target : CoreFiber
      (ctx.configuration.targetPointAt ctx.source)) :
    RefinementPackageHom
      ⟨(ctx.retarget target).baseMatePackage.1⟩ ⟨target.1⟩ :=
  (ctx.retarget target).baseCompositeLeg

/-- The pulled-side composite route evaluated at an arbitrary target package. -/
noncomputable def ActiveRefinementBCContext.pulledCompositeLegAt
    {U : AtomCarrier.{u}} (ctx : ActiveRefinementBCContext U)
    (target : CoreFiber
      (ctx.configuration.targetPointAt ctx.source)) :
    RefinementPackageHom
      ⟨(ctx.retarget target).pulledMatePackage.1⟩ ⟨target.1⟩ :=
  (ctx.retarget target).pulledCompositeLeg

/-- The original base composite is the target-package specialization. -/
@[simp] theorem ActiveRefinementBCContext.baseCompositeLegAt_target
    {U : AtomCarrier.{u}} (ctx : ActiveRefinementBCContext U) :
    ctx.baseCompositeLegAt ctx.targetPackage = ctx.baseCompositeLeg := rfl

/-- The original pulled composite is the target-package specialization. -/
@[simp] theorem ActiveRefinementBCContext.pulledCompositeLegAt_target
    {U : AtomCarrier.{u}} (ctx : ActiveRefinementBCContext U) :
    ctx.pulledCompositeLegAt ctx.targetPackage = ctx.pulledCompositeLeg := rfl

/-- The package-level mate triangle is available at every target package. -/
theorem ActiveRefinementBCContext.compositeLegAt_upper_triangle
    {U : AtomCarrier.{u}} (ctx : ActiveRefinementBCContext U)
    (target : CoreFiber
      (ctx.configuration.targetPointAt ctx.source)) :
    ((ctx.retarget target).refinementMateAtTarget.comp
      (ctx.pulledCompositeLegAt target)).upper =
        (ctx.baseCompositeLegAt target).upper := by
  exact (ctx.retarget target).refinementMate_upper_triangle

/--
Full geometry direction data for the two individual legs at one target package.

The package routes occur as indices of the geometry contracts, so the lower
refinement cannot be replaced by an unrelated exact arrow. Coefficient
identity is part of the fixed-coefficient route hypothesis; no route-between
component or triangle is included.
-/
structure ActiveRefinementBCGeometryLegData
    {U : AtomCarrier.{u}} (ctx : ActiveRefinementBCContext U)
    (target : CoreFiber
      (ctx.configuration.targetPointAt ctx.source))
    (k : Type v) [CommRing k] where
  /-- Geometry at the base-route source. -/
  baseSource : FixedCoefficientGeometryAt
    (ctx.retarget target).baseMatePackage.1 k
  /-- Geometry at the pulled-route source. -/
  pulledSource : FixedCoefficientGeometryAt
    (ctx.retarget target).pulledMatePackage.1 k
  /-- Common target geometry. -/
  commonTarget : FixedCoefficientGeometryAt target.1 k
  /-- Full geometry transport over the actual base composite route. -/
  baseGeometry : RefinementGeomReadHom
    baseSource.package commonTarget.package (ctx.baseCompositeLegAt target)
  /-- Full geometry transport over the actual pulled composite route. -/
  pulledGeometry : RefinementGeomReadHom
    pulledSource.package commonTarget.package (ctx.pulledCompositeLegAt target)
  /-- The base leg fixes the coefficient morphism to the identity. -/
  base_coefficient_id : baseGeometry.coefficientHom = RingHom.id k
  /-- The pulled leg fixes the coefficient morphism to the identity. -/
  pulled_coefficient_id : pulledGeometry.coefficientHom = RingHom.id k

namespace ActiveRefinementBCGeometryLegData

/-- The individual base-route refinement-geometry leg. -/
noncomputable def baseLeg
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {target : CoreFiber
      (ctx.configuration.targetPointAt ctx.source)}
    {k : Type v} [CommRing k]
    (data : ActiveRefinementBCGeometryLegData ctx target k) :
    RefinementGeometryHom data.baseSource.package data.commonTarget.package where
  base := ctx.baseCompositeLegAt target
  geometry := data.baseGeometry

/-- The individual pulled-route refinement-geometry leg. -/
noncomputable def pulledLeg
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {target : CoreFiber
      (ctx.configuration.targetPointAt ctx.source)}
    {k : Type v} [CommRing k]
    (data : ActiveRefinementBCGeometryLegData ctx target k) :
    RefinementGeometryHom data.pulledSource.package data.commonTarget.package where
  base := ctx.pulledCompositeLegAt target
  geometry := data.pulledGeometry

/-- Projection of the base geometry leg is the actual composite package route. -/
@[simp] theorem baseLeg_projection
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {target : CoreFiber
      (ctx.configuration.targetPointAt ctx.source)}
    {k : Type v} [CommRing k]
    (data : ActiveRefinementBCGeometryLegData ctx target k) :
    (refinementGeometryProjection U).map data.baseLeg =
      ctx.baseCompositeLegAt target := rfl

/-- Projection of the pulled geometry leg is the actual composite package route. -/
@[simp] theorem pulledLeg_projection
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {target : CoreFiber
      (ctx.configuration.targetPointAt ctx.source)}
    {k : Type v} [CommRing k]
    (data : ActiveRefinementBCGeometryLegData ctx target k) :
    (refinementGeometryProjection U).map data.pulledLeg =
      ctx.pulledCompositeLegAt target := rfl

/-- The constructed base leg retains coefficient identity. -/
@[simp] theorem baseLeg_coefficient_id
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {target : CoreFiber
      (ctx.configuration.targetPointAt ctx.source)}
    {k : Type v} [CommRing k]
    (data : ActiveRefinementBCGeometryLegData ctx target k) :
    data.baseLeg.geometry.coefficientHom = RingHom.id k :=
  data.base_coefficient_id

/-- The constructed pulled leg retains coefficient identity. -/
@[simp] theorem pulledLeg_coefficient_id
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {target : CoreFiber
      (ctx.configuration.targetPointAt ctx.source)}
    {k : Type v} [CommRing k]
    (data : ActiveRefinementBCGeometryLegData ctx target k) :
    data.pulledLeg.geometry.coefficientHom = RingHom.id k :=
  data.pulled_coefficient_id

/-- The base geometry leg retains the G-112-then-G-114 lower composite. -/
theorem baseLeg_lower_factor
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {target : CoreFiber
      (ctx.configuration.targetPointAt ctx.source)}
    {k : Type v} [CommRing k]
    (data : ActiveRefinementBCGeometryLegData ctx target k) :
    data.baseLeg.base.base =
      ((exactPackageToRefinement U).map
        (exact_bottom_semantic_global_selected_lift
          (ctx.configuration.pointedConfigurationAt ctx.source).pulledFst
          (((ctx.retarget target).legacyRegime).reverseBase.obj target)).hom).base.comp
        (refinementPackageHomOfOver
          (((ctx.retarget target).legacyRegime).baseCleavage.lift target).hom).base := by
  exact (ctx.retarget target).baseCompositeLeg_base

/-- The pulled geometry leg retains the G-114-then-G-112 lower composite. -/
theorem pulledLeg_lower_factor
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {target : CoreFiber
      (ctx.configuration.targetPointAt ctx.source)}
    {k : Type v} [CommRing k]
    (data : ActiveRefinementBCGeometryLegData ctx target k) :
    data.pulledLeg.base.base =
      (refinementPackageHomOfOver
        (((ctx.retarget target).legacyRegime).pulledCleavage.lift
          (ctx.retarget target).pullbackTargetPackage).hom).base.comp
        ((exactPackageToRefinement U).map
          (exact_bottom_semantic_global_selected_lift
            (ctx.configuration.pointedConfigurationAt ctx.source).pullbackFst
            target).hom).base := by
  exact (ctx.retarget target).pulledCompositeLeg_base

end ActiveRefinementBCGeometryLegData

namespace RefinementGeometryHom

/--
An exact geometry component factors two refinement-geometry legs once its four
computational geometry comparisons and its full package base do.

This lemma is the solution-side triangle constructor. It does not infer
geometry equality from the package upper equation and does not add a triangle
to raw leg data.
-/
theorem exact_comp_eq
    {U : AtomCarrier.{u}}
    {G H K : GeometryPackage.{u, v} U}
    (component : GeometryTotalHom G H)
    (pulledLeg : RefinementGeometryHom H K)
    (baseLeg : RefinementGeometryHom G K)
    (hbase :
      ((exactPackageToRefinement U).map component.base).comp pulledLeg.base =
        baseLeg.base)
    (hcoefficient :
      (RefinementGeomReadHom.comp
        (RefinementGeomReadHom.ofExact component)
        pulledLeg.geometry).coefficientHom =
          baseLeg.geometry.coefficientHom)
    (hsupport : HEq
      (RefinementGeomReadHom.comp
        (RefinementGeomReadHom.ofExact component)
        pulledLeg.geometry).supportComp
      baseLeg.geometry.supportComp)
    (haxis : HEq
      (RefinementGeomReadHom.comp
        (RefinementGeomReadHom.ofExact component)
        pulledLeg.geometry).axisComp
      baseLeg.geometry.axisComp)
    (hobservable : HEq
      (RefinementGeomReadHom.comp
        (RefinementGeomReadHom.ofExact component)
        pulledLeg.geometry).observableComp
      baseLeg.geometry.observableComp) :
    RefinementGeometryHom.comp
        ((exactGeometryToRefinementGeometry U).map component) pulledLeg =
      baseLeg := by
  rcases pulledLeg with ⟨pulledBase, pulledGeometry⟩
  rcases baseLeg with ⟨baseBase, baseGeometry⟩
  dsimp only at hbase hcoefficient hsupport haxis hobservable ⊢
  subst baseBase
  apply RefinementGeometryHom.ext
  · rfl
  · apply heq_of_eq
    apply RefinementGeomReadHom.ext
    · exact hcoefficient
    · exact hsupport
    · exact haxis
    · exact hobservable

end RefinementGeometryHom

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
