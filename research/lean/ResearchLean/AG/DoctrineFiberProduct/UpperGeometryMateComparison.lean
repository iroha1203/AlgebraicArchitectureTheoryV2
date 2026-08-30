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

/-! ## Pulled-route domain comparison -/

/-- The explicit pullback-target geometry core as a fiber object. -/
noncomputable def pullbackTargetCoreFiber
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :
    CoreFiber (ctx.configuration.pullbackTargetAt ctx.source) :=
  ⟨(pullbackTargetGeometry ctx target).core,
    pullbackTargetGeometry_packagePoint_eq ctx target⟩

/-- The G-112-selected exact lift used by the retargeted pulled-first route. -/
noncomputable def selectedPullbackExactLift
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :=
  exact_bottom_semantic_global_selected_lift
    (ctx.configuration.pointedConfigurationAt ctx.source).pullbackFst
    (targetCoreFiber ctx target)

/-- The explicit exact lift used to generate the pullback-target geometry. -/
noncomputable def explicitPullbackExactLift
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :=
  strongCartesianLiftOfTarget
    (cartSemanticInputOfHom
      (ctx.configuration.pointedConfigurationAt ctx.source).pullbackFst)
    (targetCoreFiber ctx target)

/-- The generated pullback-target core is the explicit exact lift domain. -/
theorem pullbackTargetCoreFiber_eq_explicit
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :
    pullbackTargetCoreFiber ctx target =
      (explicitPullbackExactLift ctx target).domainObject := by
  apply Subtype.ext
  rfl

/-- The selected exact lift domain is the retargeted pullback target package. -/
theorem selectedPullbackExactLift_domain_eq_target
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :
    (selectedPullbackExactLift ctx target).domainObject =
      (retargetedContext ctx target).pullbackTargetPackage := by
  rfl

/-- Cartesian uniqueness compares the explicit and selected pullback-target
exact lift domains. -/
noncomputable def pullbackTargetSelectedDomainIso
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :
    (explicitPullbackExactLift ctx target).domainObject ≅
      (selectedPullbackExactLift ctx target).domainObject where
  hom := ⟨(StrongCartesianLift.domainIso
    (selectedPullbackExactLift ctx target)
    (explicitPullbackExactLift ctx target)).hom,
    StrongCartesianLift.domainIso_hom_isHomLift
      (selectedPullbackExactLift ctx target)
      (explicitPullbackExactLift ctx target)⟩
  inv := ⟨(StrongCartesianLift.domainIso
    (selectedPullbackExactLift ctx target)
    (explicitPullbackExactLift ctx target)).inv,
    StrongCartesianLift.domainIso_inv_isHomLift
      (selectedPullbackExactLift ctx target)
      (explicitPullbackExactLift ctx target)⟩
  hom_inv_id := by
    apply CategoryTheory.Functor.Fiber.hom_ext
    exact (StrongCartesianLift.domainIso
      (selectedPullbackExactLift ctx target)
      (explicitPullbackExactLift ctx target)).hom_inv_id
  inv_hom_id := by
    apply CategoryTheory.Functor.Fiber.hom_ext
    exact (StrongCartesianLift.domainIso
      (selectedPullbackExactLift ctx target)
      (explicitPullbackExactLift ctx target)).inv_hom_id

/-- The forward pullback-target comparison followed by the selected exact lift
is the explicit exact lift. -/
theorem pullbackTargetSelectedDomainIso_hom_fac
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :
    (pullbackTargetSelectedDomainIso ctx target).hom.1 ≫
        (selectedPullbackExactLift ctx target).hom =
      (explicitPullbackExactLift ctx target).hom :=
  StrongCartesianLift.domainIso_hom_fac
    (selectedPullbackExactLift ctx target)
    (explicitPullbackExactLift ctx target)

/-- The inverse pullback-target comparison followed by the explicit exact lift
is the selected exact lift. -/
theorem pullbackTargetSelectedDomainIso_inv_fac
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :
    (pullbackTargetSelectedDomainIso ctx target).inv.1 ≫
        (explicitPullbackExactLift ctx target).hom =
      (selectedPullbackExactLift ctx target).hom :=
  StrongCartesianLift.domainIso_inv_fac
    (selectedPullbackExactLift ctx target)
    (explicitPullbackExactLift ctx target)

/-- The actual pullback-target comparison between the explicit geometry route
and the retargeted selected route. -/
noncomputable def pullbackTargetPackageIso
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :
    pullbackTargetCoreFiber ctx target ≅
      (retargetedContext ctx target).pullbackTargetPackage :=
  (eqToIso (pullbackTargetCoreFiber_eq_explicit ctx target)).trans
    ((pullbackTargetSelectedDomainIso ctx target).trans
      (eqToIso (selectedPullbackExactLift_domain_eq_target ctx target)))

/-- The explicit realized-refinement lift generating the pulled geometry route. -/
noncomputable def explicitPulledRefinementLift
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :=
  refinementLiftOfRealizedReflection
    (ctx.configuration.pulledRefinementAt ctx.source)
    (pulledRealizedReflection ctx.configuration ctx.source ctx.condition)
    (pullbackTargetCoreFiber ctx target)

/-- The generated pulled-route core is the explicit refinement lift domain. -/
theorem pulledRouteCoreFiber_eq_explicit
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :
    pulledRouteCoreFiber ctx target =
      ⟨(explicitPulledRefinementLift ctx target).domain,
        SelectedRefinementTransport.inverseCorePackage_point _ _⟩ := by
  apply Subtype.ext
  rfl

/-- The legacy relative lift at the explicit pullback-target package. -/
noncomputable def explicitPulledLegacyLift
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :=
  legacyRefinementLiftOfRealizedReflection
    (ctx.configuration.pulledRefinementAt ctx.source)
    (pulledRealizedReflection ctx.configuration ctx.source ctx.condition)
    (pullbackTargetCoreFiber ctx target)

/-- The public and relative realized-refinement lifts have the same domain. -/
theorem explicitPulledRefinementLift_domain_eq_legacy
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :
    (⟨(explicitPulledRefinementLift ctx target).domain,
        SelectedRefinementTransport.inverseCorePackage_point _ _⟩ :
      CoreFiber (ctx.configuration.pullbackSourceAt ctx.source)) =
      (explicitPulledLegacyLift ctx target).domain := by
  apply Subtype.ext
  exact (legacyRefinementLift_domain_coherence
    (ctx.configuration.pulledRefinementAt ctx.source)
    (pulledRealizedReflection ctx.configuration ctx.source ctx.condition)
    (pullbackTargetCoreFiber ctx target)).symm

/-- Universal comparison from the explicit pulled lift domain to the selected
retargeted pulled lift domain, transported along the pullback-target iso. -/
noncomputable def pulledLegacyDomainComparisonHom
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :
    (explicitPulledLegacyLift ctx target).domain ⟶
      (retargetedContext ctx target).pulledMatePackage :=
  (((retargetedContext ctx target).legacyRegime).pulledCleavage.lift
    (retargetedContext ctx target).pullbackTargetPackage).factor
      (RefinementOverHom.postcomp
        (explicitPulledLegacyLift ctx target).hom
        (pullbackTargetPackageIso ctx target).hom)

/-- Universal comparison in the reverse direction. -/
noncomputable def pulledLegacyDomainComparisonInv
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :
    (retargetedContext ctx target).pulledMatePackage ⟶
      (explicitPulledLegacyLift ctx target).domain :=
  (explicitPulledLegacyLift ctx target).factor
    (RefinementOverHom.postcomp
      (((retargetedContext ctx target).legacyRegime).pulledCleavage.lift
        (retargetedContext ctx target).pullbackTargetPackage).hom
      (pullbackTargetPackageIso ctx target).inv)

/-- The forward pulled-domain comparison has its transported factor triangle. -/
theorem pulledLegacyDomainComparisonHom_fac
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :
    RefinementOverHom.precomp (pulledLegacyDomainComparisonHom ctx target)
        (((retargetedContext ctx target).legacyRegime).pulledCleavage.lift
          (retargetedContext ctx target).pullbackTargetPackage).hom =
      RefinementOverHom.postcomp (explicitPulledLegacyLift ctx target).hom
        (pullbackTargetPackageIso ctx target).hom :=
  (((retargetedContext ctx target).legacyRegime).pulledCleavage.lift
    (retargetedContext ctx target).pullbackTargetPackage).factor_fac _

/-- The inverse pulled-domain comparison has its transported factor triangle. -/
theorem pulledLegacyDomainComparisonInv_fac
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :
    RefinementOverHom.precomp (pulledLegacyDomainComparisonInv ctx target)
        (explicitPulledLegacyLift ctx target).hom =
      RefinementOverHom.postcomp
        (((retargetedContext ctx target).legacyRegime).pulledCleavage.lift
          (retargetedContext ctx target).pullbackTargetPackage).hom
        (pullbackTargetPackageIso ctx target).inv :=
  (explicitPulledLegacyLift ctx target).factor_fac _

/-- The two universal comparisons are inverse. -/
noncomputable def pulledLegacyDomainIso
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :
    (explicitPulledLegacyLift ctx target).domain ≅
      (retargetedContext ctx target).pulledMatePackage where
  hom := pulledLegacyDomainComparisonHom ctx target
  inv := pulledLegacyDomainComparisonInv ctx target
  hom_inv_id := by
    have hid :
        (explicitPulledLegacyLift ctx target).factor
            (explicitPulledLegacyLift ctx target).hom =
          𝟙 (explicitPulledLegacyLift ctx target).domain := by
      symm
      apply (explicitPulledLegacyLift ctx target).factor_unique
      rfl
    rw [← hid]
    apply (explicitPulledLegacyLift ctx target).factor_unique
      (explicitPulledLegacyLift ctx target).hom
    rw [RefinementOverHom.precomp_comp,
      pulledLegacyDomainComparisonInv_fac,
      RefinementOverHom.precomp_postcomp,
      pulledLegacyDomainComparisonHom_fac,
      ← RefinementOverHom.postcomp_comp,
      (pullbackTargetPackageIso ctx target).hom_inv_id,
      RefinementOverHom.postcomp_id]
  inv_hom_id := by
    have hid :
        (((retargetedContext ctx target).legacyRegime).pulledCleavage.lift
            (retargetedContext ctx target).pullbackTargetPackage).factor
          (((retargetedContext ctx target).legacyRegime).pulledCleavage.lift
            (retargetedContext ctx target).pullbackTargetPackage).hom =
        𝟙 (retargetedContext ctx target).pulledMatePackage := by
      symm
      apply (((retargetedContext ctx target).legacyRegime).pulledCleavage.lift
        (retargetedContext ctx target).pullbackTargetPackage).factor_unique
      rfl
    rw [← hid]
    apply (((retargetedContext ctx target).legacyRegime).pulledCleavage.lift
      (retargetedContext ctx target).pullbackTargetPackage).factor_unique
        (((retargetedContext ctx target).legacyRegime).pulledCleavage.lift
          (retargetedContext ctx target).pullbackTargetPackage).hom
    rw [RefinementOverHom.precomp_comp,
      pulledLegacyDomainComparisonHom_fac,
      RefinementOverHom.precomp_postcomp,
      pulledLegacyDomainComparisonInv_fac,
      ← RefinementOverHom.postcomp_comp,
      (pullbackTargetPackageIso ctx target).inv_hom_id,
      RefinementOverHom.postcomp_id]

/-- The generated pulled-route core and the explicit relative lift choose the
same source package. -/
theorem pulledRouteCoreFiber_eq_legacy
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :
    pulledRouteCoreFiber ctx target =
      (explicitPulledLegacyLift ctx target).domain :=
  (pulledRouteCoreFiber_eq_explicit ctx target).trans
    (explicitPulledRefinementLift_domain_eq_legacy ctx target)

/-- The actual pulled-route endpoint comparison. -/
noncomputable def pulledRoutePulledMateIso
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :
    pulledRouteCoreFiber ctx target ≅
      (retargetedContext ctx target).pulledMatePackage :=
  (eqToIso (pulledRouteCoreFiber_eq_legacy ctx target)).trans
    (pulledLegacyDomainIso ctx target)

end UpperGeometryCleavage

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct.UpperGeometryCleavage
