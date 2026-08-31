import ResearchLean.AG.DoctrineFiberProduct.UpperGeometryRealizationNormalization

/-!
# Composite route context cancellation

The direct canonical-authored route legs need the object-level cancellation of
the actual composite exact/refinement context transports.  These equalities are
generated from the two explicit route constructions; they are not compatible
input fields.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u v

open CategoryTheory AtomFoundation GeometryTransport CrossStageCoherence
open TransportCoherence

set_option maxHeartbeats 3000000

namespace UpperGeometryCleavage

private theorem contextObjectExt
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {C : Site.ContextPreorderCategory A}
    {W V : Site.ContextCategoryObject C} (h : W.ctx = V.ctx) : W = V := by
  cases W
  cases V
  cases h
  rfl

/-- The base-first composite context functor cancels its chosen inverse on
target contexts. -/
theorem baseRouteContextForward_backward_ctx
    {U : AtomCarrier.{u}} (ctx : ActiveRefinementBCContext U)
    (target : TargetGeometry.{u, v} ctx) (W : target.geometry.site.category) :
    (refinementGeometryContextForward (baseRouteGeometryHom ctx target).base
      (refinementGeometryContextBackward
        (baseRouteGeometryHom ctx target).base W)).ctx = W.ctx := by
  change
    (refinementGeometryContextForward
      (((exactPackageToRefinement U).map
          (exactBaseHom (baseRefinementGeometry ctx target)
            (baseRouteExactArrow ctx target))).comp
          (refinementBaseHom target.geometry
            (ctx.configuration.baseRefinementAt ctx.source) ctx.condition
            target.packagePoint_eq))
      (refinementGeometryContextBackward
        (((exactPackageToRefinement U).map
            (exactBaseHom (baseRefinementGeometry ctx target)
              (baseRouteExactArrow ctx target))).comp
            (refinementBaseHom target.geometry
              (ctx.configuration.baseRefinementAt ctx.source) ctx.condition
              target.packagePoint_eq)) W)).ctx = W.ctx
  change
    (refinementGeometryContextForward
      (refinementBaseHom target.geometry
        (ctx.configuration.baseRefinementAt ctx.source) ctx.condition
        target.packagePoint_eq)
      (refinementGeometryContextForward
        ((exactPackageToRefinement U).map
          (exactBaseHom (baseRefinementGeometry ctx target)
            (baseRouteExactArrow ctx target)))
        (refinementGeometryContextBackward
          ((exactPackageToRefinement U).map
            (exactBaseHom (baseRefinementGeometry ctx target)
              (baseRouteExactArrow ctx target)))
          (refinementGeometryContextBackward
            (refinementBaseHom target.geometry
              (ctx.configuration.baseRefinementAt ctx.source) ctx.condition
              target.packagePoint_eq) W)))).ctx = W.ctx
  have hexact := generatedExactContextForward_backward_ctx
    (baseRefinementGeometry ctx target) (baseRouteExactArrow ctx target)
    (refinementGeometryContextBackward
      (refinementBaseHom target.geometry
        (ctx.configuration.baseRefinementAt ctx.source) ctx.condition
        target.packagePoint_eq) W)
  have hExactObject :
      refinementGeometryContextForward
        ((exactPackageToRefinement U).map
          (exactBaseHom (baseRefinementGeometry ctx target)
            (baseRouteExactArrow ctx target)))
        (refinementGeometryContextBackward
          ((exactPackageToRefinement U).map
            (exactBaseHom (baseRefinementGeometry ctx target)
              (baseRouteExactArrow ctx target)))
          (refinementGeometryContextBackward
            (refinementBaseHom target.geometry
              (ctx.configuration.baseRefinementAt ctx.source) ctx.condition
              target.packagePoint_eq) W)) =
        refinementGeometryContextBackward
          (refinementBaseHom target.geometry
            (ctx.configuration.baseRefinementAt ctx.source) ctx.condition
            target.packagePoint_eq) W :=
    contextObjectExt (by simpa using hexact)
  rw [hExactObject]
  exact generatedRefinementContextForward_backward_ctx target.geometry
    (ctx.configuration.baseRefinementAt ctx.source) ctx.condition
    target.packagePoint_eq W

/-- The pulled-first composite context functor cancels its chosen inverse on
target contexts. -/
theorem pulledRouteContextForward_backward_ctx
    {U : AtomCarrier.{u}} (ctx : ActiveRefinementBCContext U)
    (target : TargetGeometry.{u, v} ctx) (W : target.geometry.site.category) :
    (refinementGeometryContextForward (pulledRouteGeometryHom ctx target).base
      (refinementGeometryContextBackward
        (pulledRouteGeometryHom ctx target).base W)).ctx = W.ctx := by
  change
    (refinementGeometryContextForward
      ((refinementBaseHom (pullbackTargetGeometry ctx target)
          (ctx.configuration.pulledRefinementAt ctx.source)
          (pulledRealizedReflection ctx.configuration ctx.source ctx.condition)
          (pullbackTargetGeometry_packagePoint_eq ctx target)).comp
        ((exactPackageToRefinement U).map
          (exactBaseHom target.geometry
            (pullbackTargetExactArrow ctx target))))
      (refinementGeometryContextBackward
        ((refinementBaseHom (pullbackTargetGeometry ctx target)
            (ctx.configuration.pulledRefinementAt ctx.source)
            (pulledRealizedReflection ctx.configuration ctx.source ctx.condition)
            (pullbackTargetGeometry_packagePoint_eq ctx target)).comp
          ((exactPackageToRefinement U).map
            (exactBaseHom target.geometry
              (pullbackTargetExactArrow ctx target)))) W)).ctx = W.ctx
  change
    (refinementGeometryContextForward
      ((exactPackageToRefinement U).map
        (exactBaseHom target.geometry (pullbackTargetExactArrow ctx target)))
      (refinementGeometryContextForward
        (refinementBaseHom (pullbackTargetGeometry ctx target)
          (ctx.configuration.pulledRefinementAt ctx.source)
          (pulledRealizedReflection ctx.configuration ctx.source ctx.condition)
          (pullbackTargetGeometry_packagePoint_eq ctx target))
        (refinementGeometryContextBackward
          (refinementBaseHom (pullbackTargetGeometry ctx target)
            (ctx.configuration.pulledRefinementAt ctx.source)
            (pulledRealizedReflection ctx.configuration ctx.source ctx.condition)
            (pullbackTargetGeometry_packagePoint_eq ctx target))
          (refinementGeometryContextBackward
            ((exactPackageToRefinement U).map
              (exactBaseHom target.geometry
                (pullbackTargetExactArrow ctx target))) W)))).ctx = W.ctx
  have hrefinement := generatedRefinementContextForward_backward_ctx
    (pullbackTargetGeometry ctx target)
    (ctx.configuration.pulledRefinementAt ctx.source)
    (pulledRealizedReflection ctx.configuration ctx.source ctx.condition)
    (pullbackTargetGeometry_packagePoint_eq ctx target)
    (refinementGeometryContextBackward
      ((exactPackageToRefinement U).map
        (exactBaseHom target.geometry (pullbackTargetExactArrow ctx target))) W)
  have hRefinementObject :
      refinementGeometryContextForward
        (refinementBaseHom (pullbackTargetGeometry ctx target)
          (ctx.configuration.pulledRefinementAt ctx.source)
          (pulledRealizedReflection ctx.configuration ctx.source ctx.condition)
          (pullbackTargetGeometry_packagePoint_eq ctx target))
        (refinementGeometryContextBackward
          (refinementBaseHom (pullbackTargetGeometry ctx target)
            (ctx.configuration.pulledRefinementAt ctx.source)
            (pulledRealizedReflection ctx.configuration ctx.source ctx.condition)
            (pullbackTargetGeometry_packagePoint_eq ctx target))
          (refinementGeometryContextBackward
            ((exactPackageToRefinement U).map
              (exactBaseHom target.geometry
                (pullbackTargetExactArrow ctx target))) W)) =
        refinementGeometryContextBackward
          ((exactPackageToRefinement U).map
            (exactBaseHom target.geometry
              (pullbackTargetExactArrow ctx target))) W :=
    contextObjectExt (by simpa using hrefinement)
  rw [hRefinementObject]
  simpa using generatedExactContextForward_backward_ctx target.geometry
    (pullbackTargetExactArrow ctx target) W

end UpperGeometryCleavage

namespace UpperGeometryCompatibleProblemInputData

/-- Finite-vertex base-route context cancellation for the literal generated
route base used by the direct canonical-authored leg. -/
theorem canonicalAuthoredBaseRouteContextForward_backwardAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex)
    (W : (input.sourceGeometry i).package.site.category) :
    (refinementGeometryContextForward (input.generatedBaseRouteLegAt i).base
      (refinementGeometryContextBackward
        (input.generatedBaseRouteLegAt i).base W)).ctx = W.ctx := by
  exact UpperGeometryCleavage.baseRouteContextForward_backward_ctx
    (ctx.retarget (input.sourceFiberDiagram.obj ⟨i⟩))
    (input.sourceTargetGeometryAt i) W

/-- Finite-vertex pulled-route context cancellation for the independently
ordered literal generated route base. -/
theorem canonicalAuthoredPulledRouteContextForward_backwardAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex)
    (W : (input.sourceGeometry i).package.site.category) :
    (refinementGeometryContextForward (input.generatedPulledRouteLegAt i).base
      (refinementGeometryContextBackward
        (input.generatedPulledRouteLegAt i).base W)).ctx = W.ctx := by
  exact UpperGeometryCleavage.pulledRouteContextForward_backward_ctx
    (ctx.retarget (input.sourceFiberDiagram.obj ⟨i⟩))
    (input.sourceTargetGeometryAt i) W

end UpperGeometryCompatibleProblemInputData

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
