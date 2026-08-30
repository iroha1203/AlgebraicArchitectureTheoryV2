import ResearchLean.AG.DoctrineFiberProduct.UpperGeometryMateComponents

/-!
# Exact geometry mate for the two upper base-change routes

This G-115-local module lifts the generated core mate to a full
`GeometryTotalHom` without changing any completed predecessor GOAL.  It also
proves the geometry-level factorization triangle through the pulled route.
-/

namespace AAT.AG.DoctrineFiberProduct
universe u v
open CategoryTheory AtomFoundation CrossStageCoherence GeometryTransport
namespace UpperGeometryCleavage

set_option maxHeartbeats 2000000

private theorem geometryContextObjectExt
    {A : ArchitectureObject U} {C : Site.ContextPreorderCategory A}
    {W V : Site.ContextCategoryObject C} (h : W.ctx = V.ctx) : W = V := by
  cases W
  cases V
  cases h
  rfl

/-- The generated route mate with its upper map exposed as forward then backward transport. -/
noncomputable def upperGeometryMateExplicitBase
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :
    PackageTotalHom (baseRouteGeometry ctx target).core
      (pulledRouteGeometry ctx target).core where
  base := (generatedRouteCoreMate ctx target).1.base
  upper := (baseRouteGeometryHom ctx target).base.upper.comp
    (pulledRouteBackwardUpper ctx target)
  atomEquiv_eq := by
    rw [← generatedRouteCoreMate_upper_eq_explicit]
    exact (generatedRouteCoreMate ctx target).1.atomEquiv_eq

/-- The explicit geometry-mate base is the universally generated core mate. -/
theorem upperGeometryMateExplicitBase_eq
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :
    upperGeometryMateExplicitBase ctx target = (generatedRouteCoreMate ctx target).1 := by
  apply PackageTotalHom.ext
  · rfl
  · exact generatedRouteCoreMate_upper_eq_explicit ctx target |>.symm

/-- Support transport for the exact geometry mate. -/
noncomputable def upperGeometryMateSupportComp
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx)
    (W : (baseRouteGeometry ctx target).site.category) :
    W.ctx.Support →
      (contextForward (upperGeometryMateExplicitBase ctx target) W).ctx.Support :=
  fun support =>
    pulledRouteBackwardSupportComp ctx target
      (refinementGeometryContextForward
        (baseRouteGeometryHom ctx target).base W)
      ((baseRouteGeometryHom ctx target).geometry.supportComp W support)

/-- Axis transport for the exact geometry mate. -/
noncomputable def upperGeometryMateAxisComp
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx)
    (W : (baseRouteGeometry ctx target).site.category) :
    W.ctx.Axis →
      (contextForward (upperGeometryMateExplicitBase ctx target) W).ctx.Axis :=
  fun axis =>
    pulledRouteBackwardAxisComp ctx target
      (refinementGeometryContextForward
        (baseRouteGeometryHom ctx target).base W)
      ((baseRouteGeometryHom ctx target).geometry.axisComp W axis)

/-- Observable transport for the exact geometry mate. -/
noncomputable def upperGeometryMateObservableComp
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx)
    (W : (baseRouteGeometry ctx target).site.category) :
    W.ctx.Observable →
      (contextForward (upperGeometryMateExplicitBase ctx target) W).ctx.Observable :=
  fun observable =>
    pulledRouteBackwardObservableComp ctx target
      (refinementGeometryContextForward
        (baseRouteGeometryHom ctx target).base W)
      ((baseRouteGeometryHom ctx target).geometry.observableComp W observable)

/-- The mate support map preserves support readings. -/
theorem upperGeometryMateSupportReads
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx)
    (W : (baseRouteGeometry ctx target).site.category) support atom
    (h : W.ctx.minimal.supportReads support atom) :
    (contextForward (upperGeometryMateExplicitBase ctx target) W).ctx.minimal.supportReads
      (upperGeometryMateSupportComp ctx target W support)
      ((upperGeometryMateExplicitBase ctx target).upper.atomEquiv atom) := by
  exact
    pulledRouteBackwardSupportComp_reads ctx target
      (refinementGeometryContextForward
        (baseRouteGeometryHom ctx target).base W)
      ((baseRouteGeometryHom ctx target).geometry.supportComp W support)
      ((baseRouteGeometryHom ctx target).base.upper.atomEquiv atom)
      ((baseRouteGeometryHom ctx target).geometry.supportReads W support atom h)

/-- The mate axis map preserves axis readings. -/
theorem upperGeometryMateAxisReads
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx)
    (W : (baseRouteGeometry ctx target).site.category) axis
    (h : W.ctx.minimal.axisReads axis) :
    (contextForward (upperGeometryMateExplicitBase ctx target) W).ctx.minimal.axisReads
      (upperGeometryMateAxisComp ctx target W axis) := by
  exact
    pulledRouteBackwardAxisComp_reads ctx target
      (refinementGeometryContextForward
        (baseRouteGeometryHom ctx target).base W)
      ((baseRouteGeometryHom ctx target).geometry.axisComp W axis)
      ((baseRouteGeometryHom ctx target).geometry.axisReads W axis h)

/-- The mate observable map preserves observable readings. -/
theorem upperGeometryMateObservableReads
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx)
    (W : (baseRouteGeometry ctx target).site.category) observable
    (h : W.ctx.minimal.observableReads observable) :
    (contextForward (upperGeometryMateExplicitBase ctx target) W).ctx.minimal.observableReads
      (upperGeometryMateObservableComp ctx target W observable) := by
  exact
    pulledRouteBackwardObservableComp_reads ctx target
      (refinementGeometryContextForward
        (baseRouteGeometryHom ctx target).base W)
      ((baseRouteGeometryHom ctx target).geometry.observableComp W observable)
      ((baseRouteGeometryHom ctx target).geometry.observableReads W observable h)

/-- The mate support map is natural under context restriction. -/
theorem upperGeometryMateSupport_naturality
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx)
    {W V : (baseRouteGeometry ctx target).site.category} (w : W ⟶ V) support :
    (targetContextMorphism (f := upperGeometryMateExplicitBase ctx target) w).supportMap
        (upperGeometryMateSupportComp ctx target W support) =
      upperGeometryMateSupportComp ctx target V
        ((sourceContextMorphism w).supportMap support) := by
  change
    ((pulledRouteGeometry ctx target).core.contextPreorder.morphism
      (leOfHom ((pulledRouteBackwardUpper ctx target).equationTransport.contextEquivalence.functor.map
        ((refinementGeometryContextFunctor
          (baseRouteGeometryHom ctx target).base).map w)))).supportMap
        (pulledRouteBackwardSupportComp ctx target _
          ((baseRouteGeometryHom ctx target).geometry.supportComp W support)) =
      pulledRouteBackwardSupportComp ctx target _
        ((baseRouteGeometryHom ctx target).geometry.supportComp V
          (((baseRouteGeometry ctx target).core.contextPreorder.morphism
            (leOfHom w)).supportMap support))
  rw [pulledRouteBackwardSupportComp_naturality ctx target
    ((refinementGeometryContextFunctor
      (baseRouteGeometryHom ctx target).base).map w)
    ((baseRouteGeometryHom ctx target).geometry.supportComp W support)]
  exact congrArg (pulledRouteBackwardSupportComp ctx target
      (refinementGeometryContextForward
        (baseRouteGeometryHom ctx target).base V))
    ((baseRouteGeometryHom ctx target).geometry.support_naturality w support)

/-- The mate axis map is natural under context restriction. -/
theorem upperGeometryMateAxis_naturality
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx)
    {W V : (baseRouteGeometry ctx target).site.category} (w : W ⟶ V) axis :
    (targetContextMorphism (f := upperGeometryMateExplicitBase ctx target) w).axisMap
        (upperGeometryMateAxisComp ctx target W axis) =
      upperGeometryMateAxisComp ctx target V
        ((sourceContextMorphism w).axisMap axis) := by
  change
    ((pulledRouteGeometry ctx target).core.contextPreorder.morphism
      (leOfHom ((pulledRouteBackwardUpper ctx target).equationTransport.contextEquivalence.functor.map
        ((refinementGeometryContextFunctor
          (baseRouteGeometryHom ctx target).base).map w)))).axisMap
        (pulledRouteBackwardAxisComp ctx target _
          ((baseRouteGeometryHom ctx target).geometry.axisComp W axis)) =
      pulledRouteBackwardAxisComp ctx target _
        ((baseRouteGeometryHom ctx target).geometry.axisComp V
          (((baseRouteGeometry ctx target).core.contextPreorder.morphism
            (leOfHom w)).axisMap axis))
  rw [pulledRouteBackwardAxisComp_naturality ctx target
    ((refinementGeometryContextFunctor
      (baseRouteGeometryHom ctx target).base).map w)
    ((baseRouteGeometryHom ctx target).geometry.axisComp W axis)]
  exact congrArg (pulledRouteBackwardAxisComp ctx target
      (refinementGeometryContextForward
        (baseRouteGeometryHom ctx target).base V))
    ((baseRouteGeometryHom ctx target).geometry.axis_naturality w axis)

/-- The mate observable map is contravariantly natural under context restriction. -/
theorem upperGeometryMateObservable_naturality
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx)
    {W V : (baseRouteGeometry ctx target).site.category} (w : W ⟶ V) observable :
    (targetContextMorphism (f := upperGeometryMateExplicitBase ctx target) w).observableRestrict
        (upperGeometryMateObservableComp ctx target V observable) =
      upperGeometryMateObservableComp ctx target W
        ((sourceContextMorphism w).observableRestrict observable) := by
  change
    ((pulledRouteGeometry ctx target).core.contextPreorder.morphism
      (leOfHom ((pulledRouteBackwardUpper ctx target).equationTransport.contextEquivalence.functor.map
        ((refinementGeometryContextFunctor
          (baseRouteGeometryHom ctx target).base).map w)))).observableRestrict
        (pulledRouteBackwardObservableComp ctx target _
          ((baseRouteGeometryHom ctx target).geometry.observableComp V observable)) =
      pulledRouteBackwardObservableComp ctx target _
        ((baseRouteGeometryHom ctx target).geometry.observableComp W
          (((baseRouteGeometry ctx target).core.contextPreorder.morphism
            (leOfHom w)).observableRestrict observable))
  rw [pulledRouteBackwardObservableComp_naturality ctx target
    ((refinementGeometryContextFunctor
      (baseRouteGeometryHom ctx target).base).map w)
    ((baseRouteGeometryHom ctx target).geometry.observableComp V observable)]
  exact congrArg (pulledRouteBackwardObservableComp ctx target
      (refinementGeometryContextForward
        (baseRouteGeometryHom ctx target).base W))
    ((baseRouteGeometryHom ctx target).geometry.observable_naturality w observable)

/-- Coverage transport for all nine geometry coverage obligations. -/
noncomputable def upperGeometryMateCoverage
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :
    CoverageTransport (baseRouteGeometry ctx target)
      (pulledRouteGeometry ctx target) (upperGeometryMateExplicitBase ctx target) where
  requiredSupport atom h := by
    have ht := (baseRouteGeometryHom ctx target).geometry.coverage.requiredSupport atom h
    change
      target.geometry.geometry.requirements.requiredSupport
        (((pulledRouteBackwardUpper ctx target).comp
          (pulledRouteGeometryHom ctx target).base.upper).atomEquiv
            ((baseRouteGeometryHom ctx target).base.upper.atomEquiv atom))
    rw [pulledRouteBackwardUpper_comp_forward]
    exact ht
  requiredEquationCoordinate coordinate h := by
    have ht := (baseRouteGeometryHom ctx target).geometry.coverage.requiredEquationCoordinate
      coordinate h
    let bc := refinementRequiredCoordinateMap
      (baseRouteGeometryHom ctx target).base coordinate
    change target.geometry.geometry.requirements.requiredEquationCoordinate
      (⟨(((pulledRouteBackwardUpper ctx target).comp
          (pulledRouteGeometryHom ctx target).base.upper).equationMap bc.1.1),
        ((((pulledRouteBackwardUpper ctx target).comp
          (pulledRouteGeometryHom ctx target).base.upper).required_iff bc.1.1).mp
            bc.1.2)⟩,
       ((pulledRouteBackwardUpper ctx target).comp
          (pulledRouteGeometryHom ctx target).base.upper).atomEquiv bc.2)
    rw [pulledRouteBackwardUpper_comp_forward]
    exact ht
  selectedViolationWitness coordinate h := by
    have ht := (baseRouteGeometryHom ctx target).geometry.coverage.selectedViolationWitness
      coordinate h
    let bc := refinementEquationCoordinateMap
      (baseRouteGeometryHom ctx target).base coordinate
    change target.geometry.geometry.requirements.selectedViolationWitness
      ((((pulledRouteBackwardUpper ctx target).comp
          (pulledRouteGeometryHom ctx target).base.upper).equationEquiv bc.1),
       ((pulledRouteBackwardUpper ctx target).comp
          (pulledRouteGeometryHom ctx target).base.upper).atomEquiv bc.2)
    rw [pulledRouteBackwardUpper_comp_forward]
    exact ht
  requiredAxis axis h := by
    have ht := (baseRouteGeometryHom ctx target).geometry.coverage.requiredAxis axis h
    change target.geometry.geometry.requirements.requiredAxis
      (((pulledRouteBackwardUpper ctx target).comp
        (pulledRouteGeometryHom ctx target).base.upper).axisMap
          ((baseRouteGeometryHom ctx target).base.upper.axisMap axis))
    rw [pulledRouteBackwardUpper_comp_forward]
    exact ht
  supportVisibleOn W atom h := by
    have ht := (baseRouteGeometryHom ctx target).geometry.coverage.supportVisibleOn W atom h
    let bW := refinementGeometryContextForward
      (baseRouteGeometryHom ctx target).base ⟨W⟩
    change target.geometry.geometry.requirements.supportVisibleOn
      ((((pulledRouteBackwardUpper ctx target).comp
        (pulledRouteGeometryHom ctx target).base.upper).equationTransport.contextForward
          bW).ctx)
      (((pulledRouteBackwardUpper ctx target).comp
        (pulledRouteGeometryHom ctx target).base.upper).atomEquiv
          ((baseRouteGeometryHom ctx target).base.upper.atomEquiv atom))
    rw [pulledRouteBackwardUpper_comp_forward]
    exact ht
  equationCoordinateVisibleOn W coordinate h := by
    have ht := (baseRouteGeometryHom ctx target).geometry.coverage.equationCoordinateVisibleOn
      W coordinate h
    let bW := refinementGeometryContextForward
      (baseRouteGeometryHom ctx target).base ⟨W⟩
    let bc := refinementRequiredCoordinateMap
      (baseRouteGeometryHom ctx target).base coordinate
    change target.geometry.geometry.requirements.equationCoordinateVisibleOn
      ((((pulledRouteBackwardUpper ctx target).comp
        (pulledRouteGeometryHom ctx target).base.upper).equationTransport.contextForward
          bW).ctx)
      (⟨(((pulledRouteBackwardUpper ctx target).comp
          (pulledRouteGeometryHom ctx target).base.upper).equationMap bc.1.1),
        ((((pulledRouteBackwardUpper ctx target).comp
          (pulledRouteGeometryHom ctx target).base.upper).required_iff bc.1.1).mp
            bc.1.2)⟩,
       ((pulledRouteBackwardUpper ctx target).comp
          (pulledRouteGeometryHom ctx target).base.upper).atomEquiv bc.2)
    rw [pulledRouteBackwardUpper_comp_forward]
    exact ht
  violationWitnessVisibleOn W coordinate h := by
    have ht := (baseRouteGeometryHom ctx target).geometry.coverage.violationWitnessVisibleOn
      W coordinate h
    let bW := refinementGeometryContextForward
      (baseRouteGeometryHom ctx target).base ⟨W⟩
    let bc := refinementEquationCoordinateMap
      (baseRouteGeometryHom ctx target).base coordinate
    change target.geometry.geometry.requirements.violationWitnessVisibleOn
      ((((pulledRouteBackwardUpper ctx target).comp
        (pulledRouteGeometryHom ctx target).base.upper).equationTransport.contextForward
          bW).ctx)
      ((((pulledRouteBackwardUpper ctx target).comp
          (pulledRouteGeometryHom ctx target).base.upper).equationEquiv bc.1),
       ((pulledRouteBackwardUpper ctx target).comp
          (pulledRouteGeometryHom ctx target).base.upper).atomEquiv bc.2)
    rw [pulledRouteBackwardUpper_comp_forward]
    exact ht
  axisReadableOn W axis h := by
    have ht := (baseRouteGeometryHom ctx target).geometry.coverage.axisReadableOn W axis h
    let bW := refinementGeometryContextForward
      (baseRouteGeometryHom ctx target).base ⟨W⟩
    change target.geometry.geometry.requirements.axisReadableOn
      ((((pulledRouteBackwardUpper ctx target).comp
        (pulledRouteGeometryHom ctx target).base.upper).equationTransport.contextForward
          bW).ctx)
      (((pulledRouteBackwardUpper ctx target).comp
        (pulledRouteGeometryHom ctx target).base.upper).axisMap
          ((baseRouteGeometryHom ctx target).base.upper.axisMap axis))
    rw [pulledRouteBackwardUpper_comp_forward]
    exact ht
  boundaryVisibleOn W V h := by
    have ht := (baseRouteGeometryHom ctx target).geometry.coverage.boundaryVisibleOn W V h
    let bW := refinementGeometryContextForward
      (baseRouteGeometryHom ctx target).base ⟨W⟩
    let bV := refinementGeometryContextForward
      (baseRouteGeometryHom ctx target).base ⟨V⟩
    change target.geometry.geometry.requirements.boundaryVisibleOn
      ((((pulledRouteBackwardUpper ctx target).comp
        (pulledRouteGeometryHom ctx target).base.upper).equationTransport.contextForward
          bW).ctx)
      ((((pulledRouteBackwardUpper ctx target).comp
        (pulledRouteGeometryHom ctx target).base.upper).equationTransport.contextForward
          bV).ctx)
    rw [pulledRouteBackwardUpper_comp_forward]
    exact ht

/-- Backward context transport along the pulled inverse recovers pulled forward context. -/
theorem pulledRouteBackward_contextBackward
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx)
    (W : (pulledRouteGeometry ctx target).site.category) :
    ((pulledRouteBackwardUpper ctx target).equationTransport.contextBackward W).ctx =
      ((pulledRouteGeometryHom ctx target).base.upper.equationTransport.contextForward W).ctx := by
  unfold pulledRouteBackwardUpper
  change
    ((inverseCorePackageBackwardUpper target.geometry.core
      (pullbackTargetExactArrow ctx target)).equationTransport.contextBackward
        ((SelectedRefinementTransport.inverseCorePackageBackwardUpper
          (pullbackTargetGeometry ctx target).core
          (pulledRouteTransportData ctx target)).equationTransport.contextBackward W)).ctx = _
  have hrefinement :
      (SelectedRefinementTransport.inverseCorePackageBackwardUpper
          (pullbackTargetGeometry ctx target).core
          (pulledRouteTransportData ctx target)).equationTransport.contextBackward W =
        (SelectedRefinementTransport.inverseCorePackageForwardUpper
          (pullbackTargetGeometry ctx target).core
          (pulledRouteTransportData ctx target)).equationTransport.contextForward W := by
    apply geometryContextObjectExt
    exact selectedInverseCorePackageBackward_contextBackward_eq_forward_contextForward
      (pullbackTargetGeometry ctx target).core
      (pulledRouteTransportData ctx target) W
  rw [hrefinement,
    inverseCorePackageBackward_contextBackward_eq_forward_contextForward]
  rfl

example {X : ExtractionInstance U} (Q : AATCorePackage U)
    (f : X ⟶ packagePoint Q) (W : Site.ContextCategoryObject Q.contextPreorder) :
    ((inverseCorePackageBackwardUpper Q f).equationTransport.contextForward W).ctx =
      ((inverseCorePackageForwardUpper Q f).equationTransport.contextBackward W).ctx := by
  exact inverseCorePackageBackward_contextForward_eq_forward_contextBackward Q f W

/-- Forward context transport along the pulled inverse recovers pulled backward context. -/
theorem pulledRouteBackward_contextForward
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx)
    (W : target.geometry.site.category) :
    ((pulledRouteBackwardUpper ctx target).equationTransport.contextForward W).ctx =
      ((pulledRouteGeometryHom ctx target).base.upper.equationTransport.contextBackward W).ctx := by
  unfold pulledRouteBackwardUpper
  change
    ((SelectedRefinementTransport.inverseCorePackageBackwardUpper
      (pullbackTargetGeometry ctx target).core
      (pulledRouteTransportData ctx target)).equationTransport.contextForward
        ((inverseCorePackageBackwardUpper target.geometry.core
          (pullbackTargetExactArrow ctx target)).equationTransport.contextForward W)).ctx = _
  rw [selectedInverseCorePackageBackward_contextForward_eq_forward_contextBackward]
  have hexact :
      (inverseCorePackageBackwardUpper target.geometry.core
          (pullbackTargetExactArrow ctx target)).equationTransport.contextForward W =
        (inverseCorePackageForwardUpper target.geometry.core
          (pullbackTargetExactArrow ctx target)).equationTransport.contextBackward W := by
    apply geometryContextObjectExt
    exact inverseCorePackageBackward_contextForward_eq_forward_contextBackward
      target.geometry.core (pullbackTargetExactArrow ctx target) W
  rw [hexact]
  rfl

/-- The explicit mate backward context is base backward after pulled forward context. -/
theorem upperGeometryMateExplicit_contextBackward
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx)
    (W : (pulledRouteGeometry ctx target).site.category) :
    contextBackward (upperGeometryMateExplicitBase ctx target) W =
      refinementGeometryContextBackward (baseRouteGeometryHom ctx target).base
        ((pulledRouteGeometryHom ctx target).base.upper.equationTransport.contextForward W) := by
  apply geometryContextObjectExt
  change
    ((baseRouteGeometryHom ctx target).base.upper.equationTransport.contextBackward
      ((pulledRouteBackwardUpper ctx target).equationTransport.contextBackward W)).ctx = _
  have hpulled :
      (pulledRouteBackwardUpper ctx target).equationTransport.contextBackward W =
        (pulledRouteGeometryHom ctx target).base.upper.equationTransport.contextForward W := by
    apply geometryContextObjectExt
    exact pulledRouteBackward_contextBackward ctx target W
  rw [hpulled]

/-- Selected-overlap transport for the exact geometry mate. -/
noncomputable def upperGeometryMateOverlap
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :
    OverlapTransport (baseRouteGeometry ctx target)
      (pulledRouteGeometry ctx target) (upperGeometryMateExplicitBase ctx target) where
  overlapIso base left right := by
    have hbase := upperGeometryMateExplicit_contextBackward ctx target
      (⟨base⟩ : (pulledRouteGeometry ctx target).site.category)
    have hleft := upperGeometryMateExplicit_contextBackward ctx target
      (⟨left⟩ : (pulledRouteGeometry ctx target).site.category)
    have hright := upperGeometryMateExplicit_contextBackward ctx target
      (⟨right⟩ : (pulledRouteGeometry ctx target).site.category)
    simp only [contextBackwardMap]
    rw [hbase, hleft, hright]
    exact
      ((pulledRouteBackwardUpper ctx target).equationTransport.contextEquivalence.functor.mapIso
        ((baseRouteGeometryHom ctx target).geometry.overlap.overlapIso
          ((pulledRouteGeometryHom ctx target).base.upper.equationTransport.contextForward
            ⟨base⟩).ctx
          ((pulledRouteGeometryHom ctx target).base.upper.equationTransport.contextForward
            ⟨left⟩).ctx
          ((pulledRouteGeometryHom ctx target).base.upper.equationTransport.contextForward
            ⟨right⟩).ctx)).trans
        (eqToIso (by
          apply geometryContextObjectExt
          exact pulledRouteBackward_contextForward ctx target
            ⟨target.geometry.geometry.overlap.overlap
              ((pulledRouteGeometryHom ctx target).base.upper.equationTransport.contextForward
                ⟨base⟩).ctx
              ((pulledRouteGeometryHom ctx target).base.upper.equationTransport.contextForward
                ⟨left⟩).ctx
              ((pulledRouteGeometryHom ctx target).base.upper.equationTransport.contextForward
                ⟨right⟩).ctx⟩))

/-- Canonical coefficient map for the exact geometry mate. -/
noncomputable def upperGeometryMateCoefficientHom
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :
    (baseRouteGeometry ctx target).Coefficient →+*
      (pulledRouteGeometry ctx target).Coefficient :=
  (refinementSourceCoefficientBackwardHom (pullbackTargetGeometry ctx target)
      (ctx.configuration.pulledRefinementAt ctx.source)
      (pulledRealizedReflection ctx.configuration ctx.source ctx.condition)
      (pullbackTargetGeometry_packagePoint_eq ctx target)).comp
    ((exactSourceCoefficientBackwardHom target.geometry
      (pullbackTargetExactArrow ctx target)).comp
        (baseRouteGeometryHom ctx target).geometry.coefficientHom)

/-- The pulled-route raw system is the mate reindexing and coefficient base change. -/
theorem upperGeometryMate_raw_eq
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :
    (pulledRouteGeometry ctx target).raw =
      rawTransport (upperGeometryMateExplicitBase ctx target)
        (upperGeometryMateCoefficientHom ctx target) := by
  change (refinementSourceGeometry (pullbackTargetGeometry ctx target)
        (ctx.configuration.pulledRefinementAt ctx.source)
        (pulledRealizedReflection ctx.configuration ctx.source ctx.condition)
        (pullbackTargetGeometry_packagePoint_eq ctx target)).raw = _
  rw [refinementSourceGeometry_raw_backward]
  rw [show (pullbackTargetGeometry ctx target).raw =
      (exactSourceGeometry target.geometry
        (pullbackTargetExactArrow ctx target)).raw from rfl]
  rw [exactSourceGeometry_raw_backward]
  rw [rawReindexUpper_baseChange]
  unfold rawTransport
  change
    rawReindexUpper (pullbackTargetGeometry ctx target).geometry
      (pulledRouteGeometry ctx target).geometry
      (refinementSourceBackwardUpper (pullbackTargetGeometry ctx target)
        (ctx.configuration.pulledRefinementAt ctx.source)
        (pulledRealizedReflection ctx.configuration ctx.source ctx.condition)
        (pullbackTargetGeometry_packagePoint_eq ctx target))
      (rawReindexUpper target.geometry.geometry
        (pullbackTargetGeometry ctx target).geometry
        (inverseCorePackageBackwardUpper target.geometry.core
          (pullbackTargetExactArrow ctx target))
        ((target.geometry.raw.baseChange
          (exactSourceCoefficientBackwardHom target.geometry
            (pullbackTargetExactArrow ctx target))).baseChange
          (refinementSourceCoefficientBackwardHom (pullbackTargetGeometry ctx target)
            (ctx.configuration.pulledRefinementAt ctx.source)
            (pulledRealizedReflection ctx.configuration ctx.source ctx.condition)
            (pullbackTargetGeometry_packagePoint_eq ctx target)))) = _
  rw [← rawReindexUpper_comp target.geometry.geometry
    (pullbackTargetGeometry ctx target).geometry
    (pulledRouteGeometry ctx target).geometry
    (inverseCorePackageBackwardUpper target.geometry.core
      (pullbackTargetExactArrow ctx target))
    (refinementSourceBackwardUpper (pullbackTargetGeometry ctx target)
      (ctx.configuration.pulledRefinementAt ctx.source)
      (pulledRealizedReflection ctx.configuration ctx.source ctx.condition)
      (pullbackTargetGeometry_packagePoint_eq ctx target))]
  rw [← LawAlgebra.RawAmbientRestrictionSystem.baseChange_comp]
  change
    rawReindexUpper target.geometry.geometry (pulledRouteGeometry ctx target).geometry
      (pulledRouteBackwardUpper ctx target)
      (target.geometry.raw.baseChange
        ((refinementSourceCoefficientBackwardHom (pullbackTargetGeometry ctx target)
          (ctx.configuration.pulledRefinementAt ctx.source)
          (pulledRealizedReflection ctx.configuration ctx.source ctx.condition)
          (pullbackTargetGeometry_packagePoint_eq ctx target)).comp
        (exactSourceCoefficientBackwardHom target.geometry
          (pullbackTargetExactArrow ctx target)))) =
    rawReindexUpper (baseRouteGeometry ctx target).geometry
      (pulledRouteGeometry ctx target).geometry
      ((baseRouteGeometryHom ctx target).base.upper.comp
        (pulledRouteBackwardUpper ctx target))
      ((baseRouteGeometry ctx target).raw.baseChange
        (upperGeometryMateCoefficientHom ctx target))
  rw [rawReindexUpper_comp (baseRouteGeometry ctx target).geometry
    target.geometry.geometry (pulledRouteGeometry ctx target).geometry
    (baseRouteGeometryHom ctx target).base.upper
    (pulledRouteBackwardUpper ctx target)]
  unfold upperGeometryMateCoefficientHom
  conv_rhs =>
    rw [LawAlgebra.RawAmbientRestrictionSystem.baseChange_comp]
    rw [LawAlgebra.RawAmbientRestrictionSystem.baseChange_comp]
    rw [← rawReindexUpper_baseChange]
  have hraw := (baseRouteGeometryHom ctx target).geometry.raw_eq
  change target.geometry.raw =
    rawReindexUpper (baseRouteGeometry ctx target).geometry
      target.geometry.geometry (baseRouteGeometryHom ctx target).base.upper
      ((baseRouteGeometry ctx target).raw.baseChange
        (baseRouteGeometryHom ctx target).geometry.coefficientHom) at hraw
  have hrawExact := congrArg
    (fun raw => raw.baseChange
      (exactSourceCoefficientBackwardHom target.geometry
        (pullbackTargetExactArrow ctx target))) hraw
  change
    target.geometry.raw.baseChange
        (exactSourceCoefficientBackwardHom target.geometry
          (pullbackTargetExactArrow ctx target)) =
      (rawReindexUpper (baseRouteGeometry ctx target).geometry
        target.geometry.geometry (baseRouteGeometryHom ctx target).base.upper
        ((baseRouteGeometry ctx target).raw.baseChange
          (baseRouteGeometryHom ctx target).geometry.coefficientHom)).baseChange
        (exactSourceCoefficientBackwardHom target.geometry
          (pullbackTargetExactArrow ctx target)) at hrawExact
  rw [rawReindexUpper_baseChange] at hrawExact
  rw [← hrawExact]
  rw [← LawAlgebra.RawAmbientRestrictionSystem.baseChange_comp]

/-- Complete geometry data over the explicit mate base. -/
noncomputable def upperGeometryMateGeomReadHomExplicit
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :
    GeomReadHom (baseRouteGeometry ctx target) (pulledRouteGeometry ctx target)
      (upperGeometryMateExplicitBase ctx target) where
  coverage := upperGeometryMateCoverage ctx target
  overlap := upperGeometryMateOverlap ctx target
  coefficientHom := upperGeometryMateCoefficientHom ctx target
  raw_eq := upperGeometryMate_raw_eq ctx target
  supportComp := upperGeometryMateSupportComp ctx target
  axisComp := upperGeometryMateAxisComp ctx target
  observableComp := upperGeometryMateObservableComp ctx target
  supportReads := upperGeometryMateSupportReads ctx target
  axisReads := upperGeometryMateAxisReads ctx target
  observableReads := upperGeometryMateObservableReads ctx target
  support_naturality := upperGeometryMateSupport_naturality ctx target
  axis_naturality := upperGeometryMateAxis_naturality ctx target
  observable_naturality := upperGeometryMateObservable_naturality ctx target

/-- The complete exact geometry mate over the universally generated core mate. -/
noncomputable def upperGeometryMate
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :
    GeometryTotalHom (baseRouteGeometry ctx target) (pulledRouteGeometry ctx target) where
  base := (generatedRouteCoreMate ctx target).1
  geometry := by
    rw [← upperGeometryMateExplicitBase_eq ctx target]
    exact upperGeometryMateGeomReadHomExplicit ctx target

/-- The complete exact geometry mate with its base upper map exposed. -/
noncomputable def upperGeometryMateExplicit
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :
    GeometryTotalHom (baseRouteGeometry ctx target) (pulledRouteGeometry ctx target) where
  base := upperGeometryMateExplicitBase ctx target
  geometry := upperGeometryMateGeomReadHomExplicit ctx target

/-- The generated-base and explicit-base presentations of the mate agree. -/
theorem upperGeometryMate_eq_explicit
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :
    upperGeometryMate ctx target = upperGeometryMateExplicit ctx target := by
  apply GeometryTotalHom.ext
  · exact (upperGeometryMateExplicitBase_eq ctx target).symm
  · simp only [upperGeometryMate, upperGeometryMateExplicit]
    exact cast_heq _ _

/-- The mate coefficient map factors the two route coefficient maps. -/
theorem upperGeometryMateCoefficient_fac
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :
    (pulledRouteGeometryHom ctx target).geometry.coefficientHom.comp
        (upperGeometryMateCoefficientHom ctx target) =
      (baseRouteGeometryHom ctx target).geometry.coefficientHom := by
  rfl

/-- The pulled-route forward support map preserves the underlying support value. -/
theorem pulledRouteForwardSupportComp_heq
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx)
    (W : (pulledRouteGeometry ctx target).site.category) (support : W.ctx.Support) :
    HEq ((pulledRouteGeometryHom ctx target).geometry.supportComp W support)
      support := by
  change HEq
    (generatedExactSupportComp target.geometry (pullbackTargetExactArrow ctx target)
      (refinementGeometryContextForward
        (refinementBaseHom (pullbackTargetGeometry ctx target)
          (ctx.configuration.pulledRefinementAt ctx.source)
          (pulledRealizedReflection ctx.configuration ctx.source ctx.condition)
          (pullbackTargetGeometry_packagePoint_eq ctx target)) W)
      (generatedRefinementSupportComp (pullbackTargetGeometry ctx target)
        (ctx.configuration.pulledRefinementAt ctx.source)
        (pulledRealizedReflection ctx.configuration ctx.source ctx.condition)
        (pullbackTargetGeometry_packagePoint_eq ctx target) W support)) support
  apply HEq.trans (generatedExactSupportComp_heq _ _ _ _)
  exact generatedRefinementSupportComp_heq _ _ _ _ _ _

/-- The pulled-route backward and forward support maps cancel pointwise. -/
theorem pulledRouteSupportComp_cancel
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx)
    (W : target.geometry.site.category) (support : W.ctx.Support) :
    HEq
      ((pulledRouteGeometryHom ctx target).geometry.supportComp
        ((pulledRouteBackwardUpper ctx target).equationTransport.contextForward W)
      (pulledRouteBackwardSupportComp ctx target W support))
      support := by
  apply HEq.trans (pulledRouteForwardSupportComp_heq ctx target _ _)
  exact pulledRouteBackwardSupportComp_heq ctx target W support

/-- The pulled-route forward axis map preserves the underlying axis value. -/
theorem pulledRouteForwardAxisComp_heq
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx)
    (W : (pulledRouteGeometry ctx target).site.category) (axis : W.ctx.Axis) :
    HEq ((pulledRouteGeometryHom ctx target).geometry.axisComp W axis) axis := by
  change HEq
    (generatedExactAxisComp target.geometry (pullbackTargetExactArrow ctx target)
      (refinementGeometryContextForward
        (refinementBaseHom (pullbackTargetGeometry ctx target)
          (ctx.configuration.pulledRefinementAt ctx.source)
          (pulledRealizedReflection ctx.configuration ctx.source ctx.condition)
          (pullbackTargetGeometry_packagePoint_eq ctx target)) W)
      (generatedRefinementAxisComp (pullbackTargetGeometry ctx target)
        (ctx.configuration.pulledRefinementAt ctx.source)
        (pulledRealizedReflection ctx.configuration ctx.source ctx.condition)
        (pullbackTargetGeometry_packagePoint_eq ctx target) W axis)) axis
  apply HEq.trans (generatedExactAxisComp_heq _ _ _ _)
  exact generatedRefinementAxisComp_heq _ _ _ _ _ _

/-- The pulled-route backward and forward axis maps cancel pointwise. -/
theorem pulledRouteAxisComp_cancel
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx)
    (W : target.geometry.site.category) (axis : W.ctx.Axis) :
    HEq
      ((pulledRouteGeometryHom ctx target).geometry.axisComp
        ((pulledRouteBackwardUpper ctx target).equationTransport.contextForward W)
      (pulledRouteBackwardAxisComp ctx target W axis))
      axis := by
  apply HEq.trans (pulledRouteForwardAxisComp_heq ctx target _ _)
  exact pulledRouteBackwardAxisComp_heq ctx target W axis

/-- The pulled-route forward observable map preserves the underlying observable value. -/
theorem pulledRouteForwardObservableComp_heq
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx)
    (W : (pulledRouteGeometry ctx target).site.category)
    (observable : W.ctx.Observable) :
    HEq ((pulledRouteGeometryHom ctx target).geometry.observableComp W observable)
      observable := by
  change HEq
    (generatedExactObservableComp target.geometry (pullbackTargetExactArrow ctx target)
      (refinementGeometryContextForward
        (refinementBaseHom (pullbackTargetGeometry ctx target)
          (ctx.configuration.pulledRefinementAt ctx.source)
          (pulledRealizedReflection ctx.configuration ctx.source ctx.condition)
          (pullbackTargetGeometry_packagePoint_eq ctx target)) W)
      (generatedRefinementObservableComp (pullbackTargetGeometry ctx target)
        (ctx.configuration.pulledRefinementAt ctx.source)
        (pulledRealizedReflection ctx.configuration ctx.source ctx.condition)
        (pullbackTargetGeometry_packagePoint_eq ctx target) W observable)) observable
  apply HEq.trans (generatedExactObservableComp_heq _ _ _ _)
  exact generatedRefinementObservableComp_heq _ _ _ _ _ _

/-- The pulled-route backward and forward observable maps cancel pointwise. -/
theorem pulledRouteObservableComp_cancel
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx)
    (W : target.geometry.site.category) (observable : W.ctx.Observable) :
    HEq
      ((pulledRouteGeometryHom ctx target).geometry.observableComp
        ((pulledRouteBackwardUpper ctx target).equationTransport.contextForward W)
      (pulledRouteBackwardObservableComp ctx target W observable))
      observable := by
  apply HEq.trans (pulledRouteForwardObservableComp_heq ctx target _ _)
  exact pulledRouteBackwardObservableComp_heq ctx target W observable

/-- The explicit mate base factors the generated refinement route triangle. -/
theorem upperGeometryMateExplicitBase_fac
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :
    ((exactPackageToRefinement U).map (upperGeometryMateExplicitBase ctx target)).comp
        (pulledRouteGeometryHom ctx target).base =
      (baseRouteGeometryHom ctx target).base := by
  rw [upperGeometryMateExplicitBase_eq ctx target, generatedRouteCoreMate_toRefinement]
  exact generatedRouteRefinementMate_fac ctx target

/-- Pointwise base, coefficient, and carrier equalities determine an exact geometry triangle. -/
theorem exactGeometryComp_eq_of_pointwise
    {G H K : GeometryPackage.{u, v} U}
    (component : GeometryTotalHom G H)
    (pulledLeg : RefinementGeometryHom H K)
    (baseLeg : RefinementGeometryHom G K)
    (hbase : ((exactPackageToRefinement U).map component.base).comp
      pulledLeg.base = baseLeg.base)
    (hcoefficient : pulledLeg.geometry.coefficientHom.comp
      component.geometry.coefficientHom = baseLeg.geometry.coefficientHom)
    (hsupport : ∀ W support, HEq
      (pulledLeg.geometry.supportComp (contextForward component.base W)
        (component.geometry.supportComp W support))
      (baseLeg.geometry.supportComp W support))
    (haxis : ∀ W axis, HEq
      (pulledLeg.geometry.axisComp (contextForward component.base W)
        (component.geometry.axisComp W axis))
      (baseLeg.geometry.axisComp W axis))
    (hobservable : ∀ W observable, HEq
      (pulledLeg.geometry.observableComp (contextForward component.base W)
        (component.geometry.observableComp W observable))
      (baseLeg.geometry.observableComp W observable)) :
    RefinementGeometryHom.comp
        ((exactGeometryToRefinementGeometry U).map component) pulledLeg = baseLeg := by
  rcases pulledLeg with ⟨pulledBase, pulledGeometry⟩
  rcases baseLeg with ⟨baseBase, baseGeometry⟩
  dsimp only at hbase hcoefficient hsupport haxis hobservable ⊢
  subst baseBase
  apply RefinementGeometryHom.ext
  · rfl
  · apply heq_of_eq
    apply RefinementGeomReadHom.ext
    · exact hcoefficient
    · apply heq_of_eq
      funext W support
      exact eq_of_heq (hsupport W support)
    · apply heq_of_eq
      funext W axis
      exact eq_of_heq (haxis W axis)
    · apply heq_of_eq
      funext W observable
      exact eq_of_heq (hobservable W observable)

/-- The explicit upper geometry mate satisfies the full geometry route triangle. -/
theorem upperGeometryMateExplicit_fac
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :
    RefinementGeometryHom.comp
        ((exactGeometryToRefinementGeometry U).map (upperGeometryMateExplicit ctx target))
        (pulledRouteGeometryHom ctx target) =
      baseRouteGeometryHom ctx target := by
  apply exactGeometryComp_eq_of_pointwise
  · exact upperGeometryMateExplicitBase_fac ctx target
  · exact upperGeometryMateCoefficient_fac ctx target
  · intro W support
    exact pulledRouteSupportComp_cancel ctx target
      (refinementGeometryContextForward (baseRouteGeometryHom ctx target).base W)
      ((baseRouteGeometryHom ctx target).geometry.supportComp W support)
  · intro W axis
    exact pulledRouteAxisComp_cancel ctx target
      (refinementGeometryContextForward (baseRouteGeometryHom ctx target).base W)
      ((baseRouteGeometryHom ctx target).geometry.axisComp W axis)
  · intro W observable
    exact pulledRouteObservableComp_cancel ctx target
      (refinementGeometryContextForward (baseRouteGeometryHom ctx target).base W)
      ((baseRouteGeometryHom ctx target).geometry.observableComp W observable)

/-- The generated upper geometry mate satisfies the full geometry route triangle. -/
theorem upperGeometryMate_fac
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :
    RefinementGeometryHom.comp
        ((exactGeometryToRefinementGeometry U).map (upperGeometryMate ctx target))
        (pulledRouteGeometryHom ctx target) =
      baseRouteGeometryHom ctx target := by
  rw [upperGeometryMate_eq_explicit]
  exact upperGeometryMateExplicit_fac ctx target

end UpperGeometryCleavage
end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct.UpperGeometryCleavage
