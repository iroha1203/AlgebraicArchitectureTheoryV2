import ResearchLean.AG.DoctrineFiberProduct.RefinementGeometry
import ResearchLean.AG.DoctrineFiberProduct.RefinementBaseChange.Supply

/-!
# G-114 composite routes in the refinement-geometry base

This module fixes the two objectwise lower routes used by the G-115 upper
problem.  Both routes end at the same target package.  One first takes the
G-112 lift over `pulledFst` and then the authored G-114 base refinement; the
other first takes the pulled G-114 refinement and then the G-112 lift over
`pullbackFst`.

The canonical G-114 mate is exact and vertical between the two route sources.
After exact embedding into the lax refinement category, its defining universal
property gives the complete-upper factorization equation.  The two lower
composites and mate verticality are exposed separately, matching the G-115
requirement that lower factor laws not be inferred from upper data.  No
geometry transport data are selected here.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation
open CrossStageCoherence

set_option maxHeartbeats 3000000

/-- Read a relative hom over a pointed refinement as a refinement-package hom. -/
def refinementPackageHomOfOver
    {U : AtomCarrier.{u}} {X Y : ExtractionInstance U}
    {f : PointedRefinementHom X Y} {source : CoreFiber X} {target : CoreFiber Y}
    (hom : RefinementOverHom f source target) :
    RefinementPackageHom ⟨source.1⟩ ⟨target.1⟩ where
  base := (PointedRefinementHom.ofExact (eqToHom source.2)).comp
    (hom.lower.comp (PointedRefinementHom.ofExact (eqToHom target.2.symm)))
  upper := hom.upper
  atomEquiv_eq := by
    apply Equiv.ext
    intro atom
    change hom.upper.atomEquiv atom = _
    rw [hom.atomEquiv_eq]
    simp [PointedRefinementHom.comp, refinementHomComp,
      PointedRefinementHom.ofExact, exactToRefinement,
      ExtInstHom.eqToHom_atomEquiv]

/-- The base-side G-112/G-114 composite from the base mate package to the target. -/
noncomputable def ActiveRefinementBCContext.baseCompositeLeg
    {U : AtomCarrier.{u}} (ctx : ActiveRefinementBCContext U) :
    RefinementPackageHom ⟨ctx.baseMatePackage.1⟩ ⟨ctx.targetPackage.1⟩ :=
  (((exactPackageToRefinement U).map
      (exact_bottom_semantic_global_selected_lift
        (ctx.configuration.pointedConfigurationAt ctx.source).pulledFst
        ((ctx.legacyRegime).reverseBase.obj ctx.targetPackage)).hom).comp
    (refinementPackageHomOfOver
      ((ctx.legacyRegime).baseCleavage.lift ctx.targetPackage).hom))

/-- The pulled-side G-114/G-112 composite from the pulled mate package to the target. -/
noncomputable def ActiveRefinementBCContext.pulledCompositeLeg
    {U : AtomCarrier.{u}} (ctx : ActiveRefinementBCContext U) :
    RefinementPackageHom ⟨ctx.pulledMatePackage.1⟩ ⟨ctx.targetPackage.1⟩ :=
  ((refinementPackageHomOfOver
      ((ctx.legacyRegime).pulledCleavage.lift ctx.pullbackTargetPackage).hom).comp
    ((exactPackageToRefinement U).map
      (exact_bottom_semantic_global_selected_lift
        (ctx.configuration.pointedConfigurationAt ctx.source).pullbackFst
        ctx.targetPackage).hom))

/-- The vertical G-114 mate embedded into the lax refinement-package category. -/
noncomputable def ActiveRefinementBCContext.refinementMateAtTarget
    {U : AtomCarrier.{u}} (ctx : ActiveRefinementBCContext U) :
    RefinementPackageHom ⟨ctx.baseMatePackage.1⟩ ⟨ctx.pulledMatePackage.1⟩ :=
  (exactPackageToRefinement U).map ctx.mateAtTarget.1

/-- The base composite exposes the G-112 lift followed by the G-114 base lift. -/
@[simp] theorem ActiveRefinementBCContext.baseCompositeLeg_base
    {U : AtomCarrier.{u}} (ctx : ActiveRefinementBCContext U) :
    ctx.baseCompositeLeg.base =
      ((exactPackageToRefinement U).map
        (exact_bottom_semantic_global_selected_lift
          (ctx.configuration.pointedConfigurationAt ctx.source).pulledFst
          ((ctx.legacyRegime).reverseBase.obj ctx.targetPackage)).hom).base.comp
        (refinementPackageHomOfOver
          ((ctx.legacyRegime).baseCleavage.lift ctx.targetPackage).hom).base := rfl

/-- The pulled composite exposes the G-114 pulled lift followed by the G-112 lift. -/
@[simp] theorem ActiveRefinementBCContext.pulledCompositeLeg_base
    {U : AtomCarrier.{u}} (ctx : ActiveRefinementBCContext U) :
    ctx.pulledCompositeLeg.base =
      (refinementPackageHomOfOver
        ((ctx.legacyRegime).pulledCleavage.lift
          ctx.pullbackTargetPackage).hom).base.comp
        ((exactPackageToRefinement U).map
          (exact_bottom_semantic_global_selected_lift
            (ctx.configuration.pointedConfigurationAt ctx.source).pullbackFst
            ctx.targetPackage).hom).base := rfl

/-- The embedded mate retains the G-114 vertical lower projection. -/
theorem ActiveRefinementBCContext.refinementMate_isHomLift
    {U : AtomCarrier.{u}} (ctx : ActiveRefinementBCContext U) :
    (refinementPackageProjection U).IsHomLift
      (PointedRefinementHom.id
        (ctx.configuration.pullbackSourceAt ctx.source))
      ctx.refinementMateAtTarget := by
  exact exactVerticalComparison_isHomLift ctx.mateAtTarget

/-- The G-114 universal property factors the complete upper parts of the routes. -/
theorem ActiveRefinementBCContext.refinementMate_upper_triangle
    {U : AtomCarrier.{u}} (ctx : ActiveRefinementBCContext U) :
    (ctx.refinementMateAtTarget.comp ctx.pulledCompositeLeg).upper =
      ctx.baseCompositeLeg.upper := by
    have hpulled := congrArg RefinementOverHom.upper
      ((ctx.legacyRegime).pulledCleavage.homEquiv_fac
        ctx.baseMatePackage ctx.pullbackTargetPackage
        ((ctx.legacyRegime).mateRoute ctx.targetPackage))
    have hroute := (ctx.legacyRegime).mateRoute_fac ctx.targetPackage
    change (ctx.mateAtTarget.1.upper.comp
        ((ctx.legacyRegime).pulledCleavage.lift
          ctx.pullbackTargetPackage).hom.upper).comp
        (exact_bottom_semantic_global_selected_lift
          (ctx.configuration.pointedConfigurationAt ctx.source).pullbackFst
          ctx.targetPackage).hom.upper =
      (exact_bottom_semantic_global_selected_lift
          (ctx.configuration.pointedConfigurationAt ctx.source).pulledFst
          ((ctx.legacyRegime).reverseBase.obj ctx.targetPackage)).hom.upper.comp
        ((ctx.legacyRegime).baseCleavage.lift ctx.targetPackage).hom.upper
    change ctx.mateAtTarget.1.upper.comp
        (((ctx.legacyRegime).pulledCleavage.lift
          ctx.pullbackTargetPackage).hom.upper.comp
          (exact_bottom_semantic_global_selected_lift
            (ctx.configuration.pointedConfigurationAt ctx.source).pullbackFst
            ctx.targetPackage).hom.upper) = _
    change ctx.mateAtTarget.1.upper.comp
        ((ctx.legacyRegime).pulledCleavage.lift
          ctx.pullbackTargetPackage).hom.upper =
      ((ctx.legacyRegime).mateRoute ctx.targetPackage).upper at hpulled
    rw [← PackageTotalHom.upper_comp_assoc, hpulled]
    exact hroute

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
