import ResearchLean.AG.DoctrineFiberProduct.UpperGeometryMate
import ResearchLean.AG.DoctrineFiberProduct.UpperRefinementBCGeometry
import ResearchLean.AG.DoctrineFiberProduct.FiniteModelLiftComparison

/-!
# Universal route-domain comparisons for the upper geometry mate

The geometry-compatible routes use explicit inverse-package lifts, whereas the
completed G-114 route uses independently selected cleavages. Their domains are
therefore compared by universal isomorphisms, not by predecessor edits or by
pretending that the chosen objects are definitionally equal.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u v

open CategoryTheory AtomFoundation CrossStageCoherence GeometryTransport

namespace UpperGeometryCleavage

/-- The target geometry core as an object of the actual G-114 target fiber. -/
noncomputable def targetCoreFiber
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :
    CoreFiber (ctx.configuration.targetPointAt ctx.source) :=
  ⟨target.geometry.core, target.packagePoint_eq⟩

/-- The active context retargeted only to the chosen target geometry core. -/
noncomputable def retargetedContext
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :
    ActiveRefinementBCContext U :=
  ctx.retarget (targetCoreFiber ctx target)

/-- The explicit realized-refinement source package as a fiber object. -/
noncomputable def baseRefinementCoreFiber
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :
    CoreFiber (ctx.configuration.sourcePointAt ctx.source) :=
  ⟨(baseRefinementGeometry ctx target).core,
    baseRefinementGeometry_packagePoint_eq ctx target⟩

/-- The explicit refinement source and the public realized-refinement lift
select the same complete core package. -/
theorem refinementSourceGeometry_core_eq_refinementLiftDomain
    {X Y : ExtractionInstance U} (G : GeometryPackage.{u, v} U)
    (r : PointedRefinementHom X Y)
    (condition : RealizedLocusExtractionReflecting r)
    (hG : packagePoint G.core = Y) :
    (refinementSourceGeometry G r condition hG).core =
      (refinementLiftOfRealizedReflection r condition ⟨G.core, hG⟩).domain := by
  subst Y
  rfl

/-- The explicit base-refinement source agrees with the legacy G-114 reverse
object at the retargeted target package. -/
theorem baseRefinementCoreFiber_eq_legacy
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :
    baseRefinementCoreFiber ctx target =
      ((retargetedContext ctx target).legacyRegime).reverseBase.obj
        (targetCoreFiber ctx target) := by
  apply Subtype.ext
  change (baseRefinementGeometry ctx target).core =
    (legacyRefinementLiftOfRealizedReflection
      (ctx.configuration.baseRefinementAt ctx.source) ctx.condition
      (targetCoreFiber ctx target)).domain.1
  calc
    (baseRefinementGeometry ctx target).core =
        (refinementLiftOfRealizedReflection
          (ctx.configuration.baseRefinementAt ctx.source) ctx.condition
          (targetCoreFiber ctx target)).domain :=
      refinementSourceGeometry_core_eq_refinementLiftDomain target.geometry
        (ctx.configuration.baseRefinementAt ctx.source) ctx.condition
        target.packagePoint_eq
    _ = _ := (legacyRefinementLift_domain_coherence
      (ctx.configuration.baseRefinementAt ctx.source) ctx.condition
      (targetCoreFiber ctx target)).symm

/-- The G-112-selected exact lift used by the retargeted base-first route. -/
noncomputable def selectedBaseExactLift
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :=
  exact_bottom_semantic_global_selected_lift
    (ctx.configuration.pointedConfigurationAt ctx.source).pulledFst
    (baseRefinementCoreFiber ctx target)

/-- The explicit exact lift used to generate the base-first geometry route. -/
noncomputable def explicitBaseExactLift
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :=
  strongCartesianLiftOfTarget
    (cartSemanticInputOfHom
      (ctx.configuration.pointedConfigurationAt ctx.source).pulledFst)
    (baseRefinementCoreFiber ctx target)

/-- The generated geometry route core is the explicit exact lift domain. -/
theorem baseRouteCoreFiber_eq_explicit
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :
    baseRouteCoreFiber ctx target =
      (explicitBaseExactLift ctx target).domainObject := by
  apply Subtype.ext
  rfl

/-- The selected exact lift domain is the retargeted G-114 base mate package. -/
theorem selectedBaseExactLift_domain_eq_baseMate
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :
    (selectedBaseExactLift ctx target).domainObject =
      (retargetedContext ctx target).baseMatePackage := by
  apply Subtype.ext
  change (selectedBaseExactLift ctx target).domain =
    (exact_bottom_semantic_global_selected_lift
      (ctx.configuration.pointedConfigurationAt ctx.source).pulledFst
      (((retargetedContext ctx target).legacyRegime).reverseBase.obj
        (targetCoreFiber ctx target))).domain
  exact congrArg
    (fun package => (exact_bottom_semantic_global_selected_lift
      (ctx.configuration.pointedConfigurationAt ctx.source).pulledFst
      package).domain)
    (baseRefinementCoreFiber_eq_legacy ctx target)

/-- Cartesian uniqueness compares the explicit and selected exact lift domains
over the same normalized intermediate package. -/
noncomputable def baseRouteSelectedDomainIso
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :
    (explicitBaseExactLift ctx target).domainObject ≅
      (selectedBaseExactLift ctx target).domainObject where
  hom := ⟨(StrongCartesianLift.domainIso
    (selectedBaseExactLift ctx target)
    (explicitBaseExactLift ctx target)).hom,
    StrongCartesianLift.domainIso_hom_isHomLift
      (selectedBaseExactLift ctx target)
      (explicitBaseExactLift ctx target)⟩
  inv := ⟨(StrongCartesianLift.domainIso
    (selectedBaseExactLift ctx target)
    (explicitBaseExactLift ctx target)).inv,
    StrongCartesianLift.domainIso_inv_isHomLift
      (selectedBaseExactLift ctx target)
      (explicitBaseExactLift ctx target)⟩
  hom_inv_id := by
    apply CategoryTheory.Functor.Fiber.hom_ext
    exact (StrongCartesianLift.domainIso
      (selectedBaseExactLift ctx target)
      (explicitBaseExactLift ctx target)).hom_inv_id
  inv_hom_id := by
    apply CategoryTheory.Functor.Fiber.hom_ext
    exact (StrongCartesianLift.domainIso
      (selectedBaseExactLift ctx target)
      (explicitBaseExactLift ctx target)).inv_hom_id

/-- The forward comparison followed by the selected exact lift is the explicit
geometry-route lift. -/
theorem baseRouteSelectedDomainIso_hom_fac
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :
    (baseRouteSelectedDomainIso ctx target).hom.1 ≫
        (selectedBaseExactLift ctx target).hom =
      (explicitBaseExactLift ctx target).hom :=
  StrongCartesianLift.domainIso_hom_fac
    (selectedBaseExactLift ctx target) (explicitBaseExactLift ctx target)

/-- The inverse comparison followed by the explicit exact lift is the selected
G-112 route lift. -/
theorem baseRouteSelectedDomainIso_inv_fac
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :
    (baseRouteSelectedDomainIso ctx target).inv.1 ≫
        (explicitBaseExactLift ctx target).hom =
      (selectedBaseExactLift ctx target).hom :=
  StrongCartesianLift.domainIso_inv_fac
    (selectedBaseExactLift ctx target) (explicitBaseExactLift ctx target)

/-- The actual base-route endpoint comparison, assembled from the proven
endpoint normalizations and the universal domain isomorphism. -/
noncomputable def baseRouteBaseMateIso
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :
    baseRouteCoreFiber ctx target ≅
      (retargetedContext ctx target).baseMatePackage :=
  (eqToIso (baseRouteCoreFiber_eq_explicit ctx target)).trans
    ((baseRouteSelectedDomainIso ctx target).trans
      (eqToIso (selectedBaseExactLift_domain_eq_baseMate ctx target)))

end UpperGeometryCleavage

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct.UpperGeometryCleavage
