import ResearchLean.AG.DoctrineFiberProduct.UpperGeometryCleavageNaturality
import ResearchLean.AG.DoctrineFiberProduct.RefinementBaseChange.Supply

/-!
# Geometry-compatible reverse routes over the active G-114 context

This G-115-local module applies the generated exact and realized-refinement
geometry cleavages to the two actual reverse routes of an
`ActiveRefinementBCContext`. The target geometry is tied to the context's
actual target package, so the construction cannot drift to a parallel fixture.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u v

open CategoryTheory AtomFoundation CrossStageCoherence GeometryTransport

namespace UpperGeometryCleavage

/-- A geometry package whose core is the actual target package of `ctx`. -/
structure TargetGeometry (ctx : ActiveRefinementBCContext U) where
  /-- Geometry placed on the actual G-114 target package. -/
  geometry : GeometryPackage.{u, v} U
  /-- Literal identification with the package selected by the active context. -/
  core_eq : geometry.core = ctx.targetPackage.1

namespace TargetGeometry

/-- The target geometry lies over the selected target point. -/
theorem packagePoint_eq (target : TargetGeometry.{u, v} ctx) :
    packagePoint target.geometry.core =
      ctx.configuration.targetPointAt ctx.source := by
  rw [target.core_eq]
  exact ctx.targetPackage.2

end TargetGeometry

/-- Geometry after the base-refinement reverse step. -/
noncomputable def baseRefinementGeometry
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :
    GeometryPackage.{u, v} U :=
  refinementSourceGeometry target.geometry
    (ctx.configuration.baseRefinementAt ctx.source) ctx.condition
    target.packagePoint_eq

/-- The base-refinement geometry is over the actual refined source point. -/
theorem baseRefinementGeometry_packagePoint_eq
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :
    packagePoint (baseRefinementGeometry ctx target).core =
      ctx.configuration.sourcePointAt ctx.source := by
  unfold baseRefinementGeometry
  rw [refinementSourceGeometry_core]
  apply SelectedRefinementTransport.inverseCorePackage_point

/-- Actual exact arrow used after the base-refinement reverse step. -/
noncomputable def baseRouteExactArrow
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :
    ctx.configuration.pullbackSourceAt ctx.source ⟶
      packagePoint (baseRefinementGeometry ctx target).core :=
  (ctx.configuration.pointedConfigurationAt ctx.source).pulledFst ≫
    eqToHom (baseRefinementGeometry_packagePoint_eq ctx target).symm

/-- Geometry after base refinement followed by the exact pulled-first leg. -/
noncomputable def baseRouteGeometry
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :
    GeometryPackage.{u, v} U :=
  exactSourceGeometry (baseRefinementGeometry ctx target)
    (baseRouteExactArrow ctx target)

/-- The generated base-first route ends in the actual mixed pullback fiber. -/
theorem baseRouteGeometry_packagePoint_eq
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :
    packagePoint (baseRouteGeometry ctx target).core =
      ctx.configuration.pullbackSourceAt ctx.source := by
  unfold baseRouteGeometry
  rw [exactSourceGeometry_core]
  apply inverseCorePackage_point

/-- Actual pullback-first arrow, retyped to the target geometry core. -/
noncomputable def pullbackTargetExactArrow
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :
    ctx.configuration.pullbackTargetAt ctx.source ⟶
      packagePoint target.geometry.core :=
  (ctx.configuration.pointedConfigurationAt ctx.source).pullbackFst ≫
    eqToHom target.packagePoint_eq.symm

/-- Geometry after the exact pullback-first step. -/
noncomputable def pullbackTargetGeometry
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :
    GeometryPackage.{u, v} U :=
  exactSourceGeometry target.geometry
    (pullbackTargetExactArrow ctx target)

/-- The pullback-first geometry is over the actual pullback target. -/
theorem pullbackTargetGeometry_packagePoint_eq
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :
    packagePoint (pullbackTargetGeometry ctx target).core =
      ctx.configuration.pullbackTargetAt ctx.source := by
  unfold pullbackTargetGeometry
  rw [exactSourceGeometry_core]
  apply inverseCorePackage_point

/-- Geometry after exact pullback followed by the pulled-refinement reverse step. -/
noncomputable def pulledRouteGeometry
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :
    GeometryPackage.{u, v} U :=
  refinementSourceGeometry (pullbackTargetGeometry ctx target)
    (ctx.configuration.pulledRefinementAt ctx.source)
    (pulledRealizedReflection ctx.configuration ctx.source ctx.condition)
    (pullbackTargetGeometry_packagePoint_eq ctx target)

/-- The generated pulled-first route ends in the actual mixed pullback fiber. -/
theorem pulledRouteGeometry_packagePoint_eq
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :
    packagePoint (pulledRouteGeometry ctx target).core =
      ctx.configuration.pullbackSourceAt ctx.source := by
  unfold pulledRouteGeometry
  rw [refinementSourceGeometry_core]
  apply SelectedRefinementTransport.inverseCorePackage_point

/-- Core-fiber object underlying the generated base-first geometry route. -/
noncomputable def baseRouteCoreFiber
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :
    CoreFiber (ctx.configuration.pullbackSourceAt ctx.source) :=
  ⟨(baseRouteGeometry ctx target).core,
    baseRouteGeometry_packagePoint_eq ctx target⟩

/-- Core-fiber object underlying the generated pulled-first geometry route. -/
noncomputable def pulledRouteCoreFiber
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :
    CoreFiber (ctx.configuration.pullbackSourceAt ctx.source) :=
  ⟨(pulledRouteGeometry ctx target).core,
    pulledRouteGeometry_packagePoint_eq ctx target⟩

/-- Base-refinement geometry leg in the first reverse route. -/
noncomputable def baseRefinementGeometryHom
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :
    RefinementGeometryHom (baseRefinementGeometry ctx target) target.geometry :=
  generatedRefinementGeometryHom target.geometry
    (ctx.configuration.baseRefinementAt ctx.source) ctx.condition
    target.packagePoint_eq

/-- Exact geometry leg in the first reverse route. -/
noncomputable def baseRouteExactGeometryHom
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :
    GeometryTotalHom (baseRouteGeometry ctx target)
      (baseRefinementGeometry ctx target) :=
  generatedExactGeometryHom (baseRefinementGeometry ctx target)
    (baseRouteExactArrow ctx target)

/-- Exact geometry leg in the second reverse route. -/
noncomputable def pullbackTargetGeometryHom
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :
    GeometryTotalHom (pullbackTargetGeometry ctx target) target.geometry :=
  generatedExactGeometryHom target.geometry
    (pullbackTargetExactArrow ctx target)

/-- Pulled-refinement geometry leg in the second reverse route. -/
noncomputable def pulledRefinementGeometryHom
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :
    RefinementGeometryHom (pulledRouteGeometry ctx target)
      (pullbackTargetGeometry ctx target) :=
  generatedRefinementGeometryHom (pullbackTargetGeometry ctx target)
    (ctx.configuration.pulledRefinementAt ctx.source)
    (pulledRealizedReflection ctx.configuration ctx.source ctx.condition)
    (pullbackTargetGeometry_packagePoint_eq ctx target)

/-- Composite geometry-compatible base-first reverse route. -/
noncomputable def baseRouteGeometryHom
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :
    RefinementGeometryHom (baseRouteGeometry ctx target) target.geometry :=
  RefinementGeometryHom.comp
    ((exactGeometryToRefinementGeometry U).map
      (baseRouteExactGeometryHom ctx target))
    (baseRefinementGeometryHom ctx target)

/-- Composite geometry-compatible pulled-first reverse route. -/
noncomputable def pulledRouteGeometryHom
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :
    RefinementGeometryHom (pulledRouteGeometry ctx target) target.geometry :=
  RefinementGeometryHom.comp
    (pulledRefinementGeometryHom ctx target)
    ((exactGeometryToRefinementGeometry U).map
      (pullbackTargetGeometryHom ctx target))

end UpperGeometryCleavage

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct.UpperGeometryCleavage
