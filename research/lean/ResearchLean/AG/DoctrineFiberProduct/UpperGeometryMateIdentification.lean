import ResearchLean.AG.DoctrineFiberProduct.UpperGeometryRouteComparison

/-!
# Identification of the generated upper mate with the completed G-114 mate

The completed G-114 mate is conjugated by the two G-115 route comparison
isomorphisms. Its lower map is normalized to the generated endpoint transport,
while its upper triangle comes from the exported G-114 mate equation. Cartesian
uniqueness then identifies the conjugate with the generated refinement mate and
with the embedded generated core mate. No predecessor declaration is changed.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u v

open CategoryTheory AtomFoundation CrossStageCoherence GeometryTransport

namespace UpperGeometryCleavage

set_option maxHeartbeats 2000000

noncomputable def transportedG114RefinementMate
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :
    RefinementPackageHom ⟨(baseRouteGeometry ctx target).core⟩
      ⟨(pulledRouteGeometry ctx target).core⟩ :=
  ((baseRouteComparisonIso ctx target).hom.comp
    ((retargetedContext ctx target).refinementMateAtTarget.comp
      (pulledRouteComparisonIso ctx target).inv))

theorem transportedG114RefinementMate_upper_fac
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :
    ((transportedG114RefinementMate ctx target).comp
      (pulledRouteGeometryHom ctx target).base).upper =
        (baseRouteGeometryHom ctx target).base.upper := by
  change ((baseRouteComparisonHom ctx target).comp
      ((retargetedContext ctx target).refinementMateAtTarget.comp
        ((pulledRouteComparisonInv ctx target).comp
          (pulledRouteGeometryHom ctx target).base))).upper = _
  rw [pulledRouteComparisonInv_fac]
  have hmate :=
    (retargetedContext ctx target).refinementMate_upper_triangle
  have hbase := congrArg RefinementPackageHom.upper
    (baseRouteComparisonHom_fac ctx target)
  change (retargetedContext ctx target).refinementMateAtTarget.upper.comp
      (retargetedContext ctx target).pulledCompositeLeg.upper =
    (retargetedContext ctx target).baseCompositeLeg.upper at hmate
  change (baseRouteComparisonHom ctx target).upper.comp
      (retargetedContext ctx target).baseCompositeLeg.upper =
    (baseRouteGeometryHom ctx target).base.upper at hbase
  change (baseRouteComparisonHom ctx target).upper.comp
      (((retargetedContext ctx target).refinementMateAtTarget.upper.comp
        (retargetedContext ctx target).pulledCompositeLeg.upper)) = _
  rw [hmate]
  exact hbase

noncomputable def baseRouteCommonSource
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :
    PointedRefinementHom
      (packagePoint (baseRouteGeometry ctx target).core)
      (ctx.configuration.pullbackSourceAt ctx.source) :=
  (exactPointedToRefinement U).map
    (eqToHom (baseRouteGeometry_packagePoint_eq ctx target))

noncomputable def commonSourcePulledRoute
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :
    PointedRefinementHom
      (ctx.configuration.pullbackSourceAt ctx.source)
      (packagePoint (pulledRouteGeometry ctx target).core) :=
  (exactPointedToRefinement U).map
    (eqToHom (pulledRouteGeometry_packagePoint_eq ctx target).symm)

theorem baseRouteComparisonHom_isHomLift_common
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :
    (refinementPackageProjection U).IsHomLift
      (baseRouteCommonSource ctx target)
      (baseRouteComparisonHom ctx target) := by
  apply CategoryTheory.IsHomLift.of_fac'
    (refinementPackageProjection U) (baseRouteCommonSource ctx target)
    (baseRouteComparisonHom ctx target) rfl
    (congrArg (fun X => PointedRefinementObject.mk X)
      (retargetedContext ctx target).baseMatePackage.2)
  change (baseRouteComparisonHom ctx target).base = _
  rw [baseRouteComparisonHom_base]
  unfold baseRouteActualSource baseRouteCommonSource
  simp only [exactPointedToRefinement_map_eqToHom]
  simp

theorem pulledRouteComparisonInv_isHomLift_common
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :
    (refinementPackageProjection U).IsHomLift
      (commonSourcePulledRoute ctx target)
      (pulledRouteComparisonInv ctx target) := by
  apply CategoryTheory.IsHomLift.of_fac'
    (refinementPackageProjection U) (commonSourcePulledRoute ctx target)
    (pulledRouteComparisonInv ctx target)
    (congrArg (fun X => PointedRefinementObject.mk X)
      (retargetedContext ctx target).pulledMatePackage.2) rfl
  change (pulledRouteComparisonInv ctx target).base = _
  rw [pulledRouteComparisonInv_base]
  unfold pulledActualRouteSource commonSourcePulledRoute
  simp only [exactPointedToRefinement_map_eqToHom]
  simp

theorem baseRouteCommonSource_comp_commonSourcePulledRoute
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :
    (baseRouteCommonSource ctx target).comp
        (commonSourcePulledRoute ctx target) =
      routeSourceForward ctx target := by
  unfold baseRouteCommonSource commonSourcePulledRoute routeSourceForward
  change (exactPointedToRefinement U).map
      (eqToHom (baseRouteGeometry_packagePoint_eq ctx target)) ≫
    (exactPointedToRefinement U).map
      (eqToHom (pulledRouteGeometry_packagePoint_eq ctx target).symm) =
    (exactPointedToRefinement U).map
      (eqToHom ((baseRouteGeometry_packagePoint_eq ctx target).trans
        (pulledRouteGeometry_packagePoint_eq ctx target).symm))
  rw [← Functor.map_comp]
  simp

theorem transportedG114RefinementMate_isHomLift
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :
    (refinementPackageProjection U).IsHomLift
      (routeSourceForward ctx target)
      (transportedG114RefinementMate ctx target) := by
  letI hbase := baseRouteComparisonHom_isHomLift_common ctx target
  letI hmate : (refinementPackageProjection U).IsHomLift
      (PointedRefinementHom.id
        (ctx.configuration.pullbackSourceAt ctx.source))
      (retargetedContext ctx target).refinementMateAtTarget := by
    simpa [retargetedContext, ActiveRefinementBCContext.retarget] using
      (retargetedContext ctx target).refinementMate_isHomLift
  letI hpulled := pulledRouteComparisonInv_isHomLift_common ctx target
  have hmiddle := CategoryTheory.IsHomLift.comp
    (refinementPackageProjection U)
    (PointedRefinementHom.id
      (ctx.configuration.pullbackSourceAt ctx.source))
    (commonSourcePulledRoute ctx target)
    (retargetedContext ctx target).refinementMateAtTarget
    (pulledRouteComparisonInv ctx target)
  letI hmiddle' : (refinementPackageProjection U).IsHomLift
      ((PointedRefinementHom.id
        (ctx.configuration.pullbackSourceAt ctx.source)).comp
          (commonSourcePulledRoute ctx target))
      ((retargetedContext ctx target).refinementMateAtTarget.comp
        (pulledRouteComparisonInv ctx target)) := hmiddle
  have hall := CategoryTheory.IsHomLift.comp
    (refinementPackageProjection U)
    (baseRouteCommonSource ctx target)
    ((PointedRefinementHom.id
      (ctx.configuration.pullbackSourceAt ctx.source)).comp
        (commonSourcePulledRoute ctx target))
    (baseRouteComparisonHom ctx target)
    ((retargetedContext ctx target).refinementMateAtTarget.comp
      (pulledRouteComparisonInv ctx target))
  have hid : (PointedRefinementHom.id
      (ctx.configuration.pullbackSourceAt ctx.source)).comp
        (commonSourcePulledRoute ctx target) =
      commonSourcePulledRoute ctx target := by
    apply PointedRefinementHom.ext
    apply RefinementDoctrineHom.ext <;> rfl
  have hroute : (baseRouteCommonSource ctx target).comp
      ((PointedRefinementHom.id
        (ctx.configuration.pullbackSourceAt ctx.source)).comp
          (commonSourcePulledRoute ctx target)) =
      routeSourceForward ctx target := by
    rw [hid]
    exact baseRouteCommonSource_comp_commonSourcePulledRoute ctx target
  change (refinementPackageProjection U).IsHomLift
    ((baseRouteCommonSource ctx target).comp
      ((PointedRefinementHom.id
        (ctx.configuration.pullbackSourceAt ctx.source)).comp
          (commonSourcePulledRoute ctx target)))
    (transportedG114RefinementMate ctx target) at hall
  rw [hroute] at hall
  simpa [transportedG114RefinementMate] using hall

theorem transportedG114RefinementMate_base
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :
    (transportedG114RefinementMate ctx target).base =
      routeSourceForward ctx target := by
  letI := transportedG114RefinementMate_isHomLift ctx target
  exact (CategoryTheory.IsHomLift.eq_of_isHomLift
    (refinementPackageProjection U)
    (routeSourceForward ctx target)
    (transportedG114RefinementMate ctx target)).symm

theorem transportedG114RefinementMate_fac
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :
    (transportedG114RefinementMate ctx target).comp
        (pulledRouteGeometryHom ctx target).base =
      (baseRouteGeometryHom ctx target).base := by
  apply RefinementPackageHom.ext
  · change (transportedG114RefinementMate ctx target).base.comp
        (pulledRouteGeometryHom ctx target).base.base =
      (baseRouteGeometryHom ctx target).base.base
    rw [transportedG114RefinementMate_base]
    exact routeSourceForward_fac ctx target
  · exact transportedG114RefinementMate_upper_fac ctx target

theorem transportedG114RefinementMate_eq_generated
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :
    transportedG114RefinementMate ctx target =
      generatedRouteRefinementMate ctx target := by
  letI := transportedG114RefinementMate_isHomLift ctx target
  exact generatedRouteRefinementMate_unique ctx target
    (transportedG114RefinementMate ctx target)
    (transportedG114RefinementMate_fac ctx target)

theorem generatedRouteRefinementMate_comparison_square
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :
    (generatedRouteRefinementMate ctx target).comp
        (pulledRouteComparisonHom ctx target) =
      (baseRouteComparisonHom ctx target).comp
        (retargetedContext ctx target).refinementMateAtTarget := by
  rw [← transportedG114RefinementMate_eq_generated]
  unfold transportedG114RefinementMate
  change (baseRouteComparisonHom ctx target).comp
      (((retargetedContext ctx target).refinementMateAtTarget.comp
        (pulledRouteComparisonInv ctx target)).comp
          (pulledRouteComparisonHom ctx target)) = _
  have hinner :
      ((retargetedContext ctx target).refinementMateAtTarget.comp
        (pulledRouteComparisonInv ctx target)).comp
          (pulledRouteComparisonHom ctx target) =
      (retargetedContext ctx target).refinementMateAtTarget := by
    calc
      ((retargetedContext ctx target).refinementMateAtTarget ≫
          pulledRouteComparisonInv ctx target) ≫
          pulledRouteComparisonHom ctx target =
        (retargetedContext ctx target).refinementMateAtTarget ≫
          (pulledRouteComparisonInv ctx target ≫
            pulledRouteComparisonHom ctx target) := Category.assoc _ _ _
      _ = (retargetedContext ctx target).refinementMateAtTarget ≫
          𝟙 (⟨(retargetedContext ctx target).pulledMatePackage.1⟩ :
            RefinementPackageObject U) := by
        have hinv := (pulledRouteComparisonIso ctx target).inv_hom_id
        exact congrArg (fun leg =>
          (retargetedContext ctx target).refinementMateAtTarget.comp leg) hinv
      _ = (retargetedContext ctx target).refinementMateAtTarget := by
        apply Category.comp_id
  exact congrArg (fun leg =>
    (baseRouteComparisonHom ctx target).comp leg) hinner

theorem generatedRouteCoreMate_comparison_square
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :
    ((exactPackageToRefinement U).map
        (generatedRouteCoreMate ctx target).1).comp
        (pulledRouteComparisonHom ctx target) =
      (baseRouteComparisonHom ctx target).comp
        (retargetedContext ctx target).refinementMateAtTarget := by
  rw [generatedRouteCoreMate_toRefinement]
  exact generatedRouteRefinementMate_comparison_square ctx target

end UpperGeometryCleavage
end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct.UpperGeometryCleavage
