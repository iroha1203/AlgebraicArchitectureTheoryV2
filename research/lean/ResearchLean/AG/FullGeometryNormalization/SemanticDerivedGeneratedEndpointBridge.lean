import ResearchLean.AG.FullGeometryNormalization.SemanticDerivedEndpointBridge
import ResearchLean.AG.FullGeometryNormalization.SemanticDerivedLiteralMateFactor
import ResearchLean.AG.FullGeometryNormalization.SemanticDerivedRouteExactImage
import ResearchLean.AG.DoctrineFiberProduct.UpperGeometryCompatibleEndpointExactIsos
import ResearchLean.AG.FullGeometryNormalization.ExactRefinementIso

/-!
# Comparison with the generated G-118 route endpoints

This file compares the literal exact two-edge semantic pullbacks with the
canonical and generated route geometries of the one-vertex G-118 problem.
-/

namespace AAT.AG.FullGeometryNormalization

universe u v

open CategoryTheory AtomFoundation GeometryTransport CrossStageCoherence
open DoctrineFiberProduct

set_option maxHeartbeats 3000000

noncomputable local instance semanticGeneratedEndpointAtomDecidableEq
    (U : AtomCarrier.{u}) : DecidableEq U.Atom := Classical.decEq _

/-- The G-118 canonical base-route geometry in the generated mixed fiber. -/
noncomputable def semanticDerivedCanonicalBaseRouteFiberAt
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U) (Q : AATCorePackage U)
    (k : Type v) [CommRing k] (g : FixedCoefficientGeometryAt Q k)
    (endpoint_eq : packagePoint Q = input.square.southwest) :
    GeomFiber
      ((semanticDerivedRefinementBCConfiguration input).pullbackSourceAt
        (semanticDerivedRefinementBCCompatibleSource input)) := by
  let problem := semanticDerivedCompatibleProblemData input Q k g endpoint_eq
  let ctx := semanticDerivedRefinementBCContext input
    (semanticDerivedSouthwestGeometryFiber input Q k g endpoint_eq)
  refine ⟨problem.canonicalAuthoredBaseRouteGeometryAt PUnit.unit, ?_⟩
  change packagePoint
    (problem.canonicalAuthoredBaseRouteGeometryAt PUnit.unit).core = _
  rw [problem.canonicalAuthoredBaseRouteGeometryAt_core]
  exact UpperGeometryCleavage.baseRouteGeometry_packagePoint_eq
    (ctx.retarget (problem.sourceFiberDiagram.obj ⟨PUnit.unit⟩))
    (problem.sourceTargetGeometryAt PUnit.unit)

/-- The G-118 canonical pulled-route geometry in the generated mixed fiber. -/
noncomputable def semanticDerivedCanonicalPulledRouteFiberAt
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U) (Q : AATCorePackage U)
    (k : Type v) [CommRing k] (g : FixedCoefficientGeometryAt Q k)
    (endpoint_eq : packagePoint Q = input.square.southwest) :
    GeomFiber
      ((semanticDerivedRefinementBCConfiguration input).pullbackSourceAt
        (semanticDerivedRefinementBCCompatibleSource input)) := by
  let problem := semanticDerivedCompatibleProblemData input Q k g endpoint_eq
  let ctx := semanticDerivedRefinementBCContext input
    (semanticDerivedSouthwestGeometryFiber input Q k g endpoint_eq)
  refine ⟨problem.canonicalAuthoredPulledRouteGeometryAt PUnit.unit, ?_⟩
  change packagePoint
    (problem.canonicalAuthoredPulledRouteGeometryAt PUnit.unit).core = _
  rw [problem.canonicalAuthoredPulledRouteGeometryAt_core]
  exact UpperGeometryCleavage.pulledRouteGeometry_packagePoint_eq
    (ctx.retarget (problem.sourceFiberDiagram.obj ⟨PUnit.unit⟩))
    (problem.sourceTargetGeometryAt PUnit.unit)

private noncomputable def semanticFiberIsoOfTotalIso
    {U : AtomCarrier.{u}} {X : ExtractionInstance U}
    (source target : GeomFiber.{u, v} X)
    (comparison : source.1 ≅ target.1)
    (hbase : (crossStageProjection U).map comparison.hom ≫
      eqToHom target.2 = eqToHom source.2) : source ≅ target := by
  let forward : source ⟶ target :=
    ⟨comparison.hom, by
      apply CategoryTheory.IsHomLift.of_fac'
        (crossStageProjection U) (𝟙 X) comparison.hom source.2 target.2
      have h := congrArg (fun f => f ≫ eqToHom target.2.symm) hbase
      simpa only [Category.assoc, eqToHom_trans, eqToHom_refl,
        Category.comp_id, Category.id_comp] using h⟩
  letI : IsIso forward := semanticGeomFiberHom_isIso_of_total_isIso forward
  exact asIso forward

/-- Exact canonical-to-generated comparison in the mixed base-route fiber. -/
noncomputable def semanticDerivedCanonicalBaseToGeneratedFiberIsoAt
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U) (Q : AATCorePackage U)
    (k : Type v) [CommRing k] (g : FixedCoefficientGeometryAt Q k)
    (endpoint_eq : packagePoint Q = input.square.southwest) :
    semanticDerivedCanonicalBaseRouteFiberAt input Q k g endpoint_eq ≅
      semanticDerivedGeneratedBaseRouteFiberAt input Q k g endpoint_eq := by
  let problem := semanticDerivedCompatibleProblemData input Q k g endpoint_eq
  apply semanticFiberIsoOfTotalIso
    (semanticDerivedCanonicalBaseRouteFiberAt input Q k g endpoint_eq)
    (semanticDerivedGeneratedBaseRouteFiberAt input Q k g endpoint_eq)
    (problem.canonicalAuthoredBaseToGeneratedRouteExactGeometryIsoAt PUnit.unit)
  simp [semanticDerivedCanonicalBaseRouteFiberAt,
    semanticDerivedGeneratedBaseRouteFiberAt, problem,
    UpperGeometryCompatibleProblemInputData.canonicalAuthoredBaseToGeneratedRouteExactGeometryHomAt,
    UpperGeometryCompatibleProblemInputData.canonicalAuthoredBaseToGeneratedRouteExactCoreHomAt]
  rfl

/-- Exact canonical-to-generated comparison in the mixed pulled-route fiber. -/
noncomputable def semanticDerivedCanonicalPulledToGeneratedFiberIsoAt
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U) (Q : AATCorePackage U)
    (k : Type v) [CommRing k] (g : FixedCoefficientGeometryAt Q k)
    (endpoint_eq : packagePoint Q = input.square.southwest) :
    semanticDerivedCanonicalPulledRouteFiberAt input Q k g endpoint_eq ≅
      semanticDerivedGeneratedPulledRouteFiberAt input Q k g endpoint_eq := by
  let problem := semanticDerivedCompatibleProblemData input Q k g endpoint_eq
  apply semanticFiberIsoOfTotalIso
    (semanticDerivedCanonicalPulledRouteFiberAt input Q k g endpoint_eq)
    (semanticDerivedGeneratedPulledRouteFiberAt input Q k g endpoint_eq)
    (problem.canonicalAuthoredPulledToGeneratedRouteExactGeometryIsoAt PUnit.unit)
  simp [semanticDerivedCanonicalPulledRouteFiberAt,
    semanticDerivedGeneratedPulledRouteFiberAt, problem,
    UpperGeometryCompatibleProblemInputData.canonicalAuthoredPulledToGeneratedRouteExactGeometryHomAt,
    UpperGeometryCompatibleProblemInputData.canonicalAuthoredPulledToGeneratedRouteExactCoreHomAt]
  rfl

/-! ## Literal-to-canonical source points and lower route equations -/

noncomputable def semanticDerivedBToCanonicalBaseSourcePointIsoAt
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U) (Q : AATCorePackage U)
    (k : Type v) [CommRing k] (g : FixedCoefficientGeometryAt Q k)
    (endpoint_eq : packagePoint Q = input.square.southwest)
    (square_isPullback : IsPullback input.square.left input.square.top
      input.square.bottom input.square.right) :
    packagePoint (semanticDerivedBGeometryAt input Q k g endpoint_eq).1.core ≅
      packagePoint (semanticDerivedCanonicalBaseRouteFiberAt
        input Q k g endpoint_eq).1.core :=
  eqToIso (semanticDerivedBGeometryAt input Q k g endpoint_eq).2 ≪≫
    (semanticDerivedPullbackSourceIso input square_isPullback).symm ≪≫
    eqToIso (semanticDerivedCanonicalBaseRouteFiberAt input Q k g endpoint_eq).2.symm

noncomputable def semanticDerivedTToCanonicalPulledSourcePointIsoAt
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U) (Q : AATCorePackage U)
    (k : Type v) [CommRing k] (g : FixedCoefficientGeometryAt Q k)
    (endpoint_eq : packagePoint Q = input.square.southwest)
    (square_isPullback : IsPullback input.square.left input.square.top
      input.square.bottom input.square.right) :
    packagePoint (semanticDerivedTGeometryAt input Q k g endpoint_eq).1.core ≅
      packagePoint (semanticDerivedCanonicalPulledRouteFiberAt
        input Q k g endpoint_eq).1.core :=
  eqToIso (semanticDerivedTGeometryAt input Q k g endpoint_eq).2 ≪≫
    (semanticDerivedPullbackSourceIso input square_isPullback).symm ≪≫
    eqToIso (semanticDerivedCanonicalPulledRouteFiberAt input Q k g endpoint_eq).2.symm

private theorem semanticDerivedBToCanonicalBase_lower_fac
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U) (Q : AATCorePackage U)
    (k : Type v) [CommRing k] (g : FixedCoefficientGeometryAt Q k)
    (endpoint_eq : packagePoint Q = input.square.southwest)
    (square_isPullback : IsPullback input.square.left input.square.top
      input.square.bottom input.square.right) :
    (semanticDerivedBToCanonicalBaseSourcePointIsoAt
        input Q k g endpoint_eq square_isPullback).hom ≫
      eqToHom (semanticDerivedCanonicalBaseRouteFiberAt input Q k g endpoint_eq).2 ≫
      semanticDerivedMixedFst input ≫ input.square.bottom =
    eqToHom (semanticDerivedBGeometryAt input Q k g endpoint_eq).2 ≫
      input.square.left ≫ input.square.bottom := by
  have hleft := semanticDerivedMixedFst_sourceIso_inv
    input square_isPullback
  simp [semanticDerivedBToCanonicalBaseSourcePointIsoAt, eqToIso]
  simpa only [Category.assoc] using congrArg
    (fun hom => hom ≫ input.square.bottom) hleft

private theorem semanticDerivedTToCanonicalPulled_lower_fac
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U) (Q : AATCorePackage U)
    (k : Type v) [CommRing k] (g : FixedCoefficientGeometryAt Q k)
    (endpoint_eq : packagePoint Q = input.square.southwest)
    (square_isPullback : IsPullback input.square.left input.square.top
      input.square.bottom input.square.right) :
    (semanticDerivedTToCanonicalPulledSourcePointIsoAt
        input Q k g endpoint_eq square_isPullback).hom ≫
      eqToHom (semanticDerivedCanonicalPulledRouteFiberAt input Q k g endpoint_eq).2 ≫
      semanticDerivedPulledComparison input ≫
      (semanticDerivedPullbackTargetIso input).hom ≫ input.square.right =
    eqToHom (semanticDerivedTGeometryAt input Q k g endpoint_eq).2 ≫
      input.square.top ≫ input.square.right := by
  have htop := semanticDerivedPulledComparison_sourceIso_inv
    input square_isPullback
  simp [semanticDerivedTToCanonicalPulledSourcePointIsoAt, eqToIso]
  simpa only [Category.assoc] using congrArg
    (fun hom => hom ≫ input.square.right) htop

@[simp] private theorem semanticEqToHom_doctrineHom_sameDoctrine
    {U : AtomCarrier.{u}} (D : ExtractionDoctrine U)
    (x y : D.Source)
    (h : (ExtractionInstance.mk D x : ExtractionInstance U) =
      ExtractionInstance.mk D y) :
    (eqToHom h : ExtInstHom (ExtractionInstance.mk D x)
      (ExtractionInstance.mk D y)).doctrineHom = ExactDoctrineHom.id D := by
  cases h
  rfl

private theorem semanticOfExact_eq_exactPointedToRefinement_map
    {U : AtomCarrier.{u}} {X Y : ExtractionInstance U} (f : X ⟶ Y) :
    PointedRefinementHom.ofExact f = (exactPointedToRefinement U).map f := by
  rfl

private theorem semanticDerivedBaseRefinementExactArrow_eq_endpointCasts
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U) :
    semanticDerivedBaseRefinementExactArrow input =
      eqToHom (semanticDerivedRefinementBCSourcePoint_eq input) ≫
        input.square.bottom ≫
        eqToHom (semanticDerivedRefinementBCTargetPoint_eq input).symm := by
  have hsource :
      (eqToHom (semanticDerivedRefinementBCSourcePoint_eq input)).doctrineHom =
        ExactDoctrineHom.id input.square.southwest.doctrine := by
    simpa [semanticDerivedRefinementBCConfiguration,
      semanticDerivedRefinementBCCompatibleSource,
      RefinementBCConfiguration.sourcePointAt] using
      semanticEqToHom_doctrineHom_sameDoctrine
        input.square.southwest.doctrine
        input.square.southwest.source
        input.square.southwest.source
        (semanticDerivedRefinementBCSourcePoint_eq input)
  have htarget :
      (eqToHom (semanticDerivedRefinementBCTargetPoint_eq input).symm).doctrineHom =
        ExactDoctrineHom.id input.square.southeast.doctrine := by
    simpa [semanticDerivedRefinementBCConfiguration,
      semanticDerivedRefinementBCCompatibleSource,
      RefinementBCConfiguration.targetPointAt,
      RefinementBCConfiguration.sourceOneAt] using
      semanticEqToHom_doctrineHom_sameDoctrine
        input.square.southeast.doctrine
        input.square.southeast.source
        (input.square.bottom.doctrineHom.sourceMap input.square.southwest.source)
        (semanticDerivedRefinementBCTargetPoint_eq input).symm
  apply ExtInstHom.ext
  change input.square.bottom.doctrineHom =
    (eqToHom (semanticDerivedRefinementBCSourcePoint_eq input)).doctrineHom.comp
      (input.square.bottom.doctrineHom.comp
        (eqToHom (semanticDerivedRefinementBCTargetPoint_eq input).symm).doctrineHom)
  rw [hsource, htarget]
  apply ExactDoctrineHom.ext
  · funext source
    rfl
  · apply Equiv.ext
    intro atom
    rfl

/-- The generated canonical base-route lower map is the refinement image of
the literal exact two-edge base route after the pullback-source cast. -/
theorem semanticDerivedCanonicalBaseRoute_refinementExactImage
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U) (Q : AATCorePackage U)
    (k : Type v) [CommRing k] (g : FixedCoefficientGeometryAt Q k)
    (endpoint_eq : packagePoint Q = input.square.southwest)
    (square_isPullback : IsPullback input.square.left input.square.top
      input.square.bottom input.square.right) :
    (exactPointedToRefinement U).map
        (semanticDerivedBToCanonicalBaseSourcePointIsoAt
          input Q k g endpoint_eq square_isPullback).hom ≫
      ((semanticDerivedCompatibleProblemData input Q k g endpoint_eq).canonicalAuthoredBaseRouteGeometryHomAt
        PUnit.unit).base.base =
    (exactPointedToRefinement U).map
      ((crossStageProjection U).map
        (semanticDerivedDirectBaseRouteLegAt input Q k g endpoint_eq)) := by
  rw [UpperGeometryCompatibleProblemInputData.canonicalAuthoredBaseRouteGeometryHomAt_base]
  unfold UpperGeometryCompatibleProblemInputData.generatedBaseRouteLegAt
  unfold UpperGeometryCleavage.baseRouteGeometryHom
  change PointedRefinementHom.comp _
    (PointedRefinementHom.comp
      ((exactGeometryToRefinementGeometry U).map _).base.base
      (UpperGeometryCleavage.refinementBaseHom _ _ _ _).base) = _
  rw [UpperGeometryCleavage.refinementBaseHom_base_eq_casts]
  simp only [ActiveRefinementBCContext.retarget,
    semanticDerivedRefinementBCContext,
    activeRefinementBCContextOfCondition,
    semanticDerivedCompatibleProblemData,
    semanticDerivedSourceFiberDiagram]
  conv_lhs =>
    rhs
    rhs
    rhs
    lhs
    rw [semanticDerivedBaseRefinement_exactImage]
  rw [semanticDerivedBaseRefinementExactArrow_eq_endpointCasts]
  simp only [Functor.map_comp, exactPointedToRefinement_map_eqToHom,
    Category.assoc, eqToHom_refl]
  have hright :
      (exactPointedToRefinement U).map
        ((crossStageProjection U).map
          (semanticDerivedDirectBaseRouteLegAt input Q k g endpoint_eq)) =
      (exactPointedToRefinement U).map
        (eqToHom (semanticDerivedBGeometryAt input Q k g endpoint_eq).2 ≫
          input.square.left ≫ input.square.bottom ≫
          eqToHom (semanticDerivedTargetGeometryAt input Q k g endpoint_eq).2.symm) := by
    unfold semanticDerivedDirectBaseRouteLegAt
    rw [Functor.map_comp,
      semanticGeometryPullLift_crossStageProjection,
      semanticGeometryPullLift_crossStageProjection]
    simp [semanticGeometryPullBaseHom]
  rw [hright]
  have hlower := semanticDerivedBToCanonicalBase_lower_fac
    input Q k g endpoint_eq square_isPullback
  have hlower' := congrArg
    (fun hom => hom ≫ eqToHom
      (semanticDerivedTargetGeometryAt input Q k g endpoint_eq).2.symm)
    hlower
  simp only [Category.assoc, eqToHom_refl, Category.id_comp] at hlower'
  have h := congrArg (fun hom => (exactPointedToRefinement U).map hom) hlower'
  change (exactPointedToRefinement U).map
    (semanticDerivedBToCanonicalBaseSourcePointIsoAt
      input Q k g endpoint_eq square_isPullback).hom ≫ (_ ≫ _) = _
  simp only [Functor.map_comp,
    exactPointedToRefinement_map_eqToHom,
    eqToHom_refl,
    semanticDerivedMixedFst,
    UpperGeometryCleavage.baseRouteExactGeometryHom,
    UpperGeometryCleavage.generatedExactGeometryHom,
    UpperGeometryCleavage.baseRouteExactArrow,
    UpperGeometryCleavage.exactBaseHom,
    exactGeometryToRefinementGeometry,
    exactPackageToRefinement,
    inverseCorePackageHom] at h ⊢
  simpa using h

private theorem semanticDerivedTargetFst_eq_snd_right
    {U : AtomCarrier.{u}} (input : BCSemanticInput U) :
    semanticDerivedTargetFst input =
      semanticDerivedTargetSnd input ≫ input.square.right := by
  let C := semanticDerivedRefinementBCConfiguration input
  let p := semanticDerivedRefinementBCCompatibleSource input
  have hcommutes := pointedPullback_commutes (C.fstAt p) (C.sndAt p)
  have hdoctrine := congrArg (fun hom => hom.doctrineHom) hcommutes
  have hsecond :
      (eqToHom (semanticDerivedRefinementBCSecondPoint_eq input)).doctrineHom =
        ExactDoctrineHom.id input.square.northeast.doctrine := by
    simpa [C, p, semanticDerivedRefinementBCConfiguration,
      semanticDerivedRefinementBCCompatibleSource,
      RefinementBCConfiguration.secondPointAt] using
      semanticEqToHom_doctrineHom_sameDoctrine
        input.square.northeast.doctrine
        (semanticDerivedRefinementBCCompatibleSource input).sourceTwo
        input.square.northeast.source
        (semanticDerivedRefinementBCSecondPoint_eq input)
  have htarget :
      (eqToHom (semanticDerivedRefinementBCTargetPoint_eq input)).doctrineHom =
        ExactDoctrineHom.id input.square.southeast.doctrine := by
    simpa [C, p, semanticDerivedRefinementBCConfiguration,
      semanticDerivedRefinementBCCompatibleSource,
      RefinementBCConfiguration.targetPointAt,
      RefinementBCConfiguration.sourceOneAt] using
      semanticEqToHom_doctrineHom_sameDoctrine
        input.square.southeast.doctrine
        (input.square.bottom.doctrineHom.sourceMap input.square.southwest.source)
        input.square.southeast.source
        (semanticDerivedRefinementBCTargetPoint_eq input)
  apply ExtInstHom.ext
  change
    (semanticDerivedPointedRefinementBCConfiguration input).pullbackFst.doctrineHom.comp
      (eqToHom (semanticDerivedRefinementBCTargetPoint_eq input)).doctrineHom =
    (pointedPullbackSnd
      (semanticDerivedPointedRefinementBCConfiguration input).sigmaOne
      (semanticDerivedPointedRefinementBCConfiguration input).sigmaTwo).doctrineHom.comp
      ((eqToHom (semanticDerivedRefinementBCSecondPoint_eq input)).doctrineHom.comp
        input.square.right.doctrineHom)
  rw [hsecond, htarget]
  simpa [C, p, semanticDerivedPointedRefinementBCConfiguration,
    semanticDerivedRefinementBCConfiguration,
    semanticDerivedRefinementBCCompatibleSource,
    RefinementBCConfiguration.pointedConfigurationAt,
    RefinementBCConfiguration.fstAt,
    RefinementBCConfiguration.sndAt] using hdoctrine

/-- The generated canonical pulled-route lower map is the refinement image
of the literal exact two-edge pulled route. -/
theorem semanticDerivedCanonicalPulledRoute_refinementExactImage
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U) (Q : AATCorePackage U)
    (k : Type v) [CommRing k] (g : FixedCoefficientGeometryAt Q k)
    (endpoint_eq : packagePoint Q = input.square.southwest)
    (square_isPullback : IsPullback input.square.left input.square.top
      input.square.bottom input.square.right) :
    (exactPointedToRefinement U).map
        (semanticDerivedTToCanonicalPulledSourcePointIsoAt
          input Q k g endpoint_eq square_isPullback).hom ≫
      ((semanticDerivedCompatibleProblemData input Q k g endpoint_eq).canonicalAuthoredPulledRouteGeometryHomAt
        PUnit.unit).base.base =
    (exactPointedToRefinement U).map
      ((crossStageProjection U).map
        (semanticDerivedDirectPulledRouteLegAt input Q k g endpoint_eq)) := by
  rw [UpperGeometryCompatibleProblemInputData.canonicalAuthoredPulledRouteGeometryHomAt_base]
  unfold UpperGeometryCompatibleProblemInputData.generatedPulledRouteLegAt
  unfold UpperGeometryCleavage.pulledRouteGeometryHom
  change PointedRefinementHom.comp _
    (PointedRefinementHom.comp
      (UpperGeometryCleavage.refinementBaseHom _ _ _ _).base
      ((exactGeometryToRefinementGeometry U).map _).base.base) = _
  rw [UpperGeometryCleavage.refinementBaseHom_base_eq_casts]
  have hright :
      (exactPointedToRefinement U).map
        ((crossStageProjection U).map
          (semanticDerivedDirectPulledRouteLegAt input Q k g endpoint_eq)) =
      (exactPointedToRefinement U).map
        (eqToHom (semanticDerivedTGeometryAt input Q k g endpoint_eq).2 ≫
          input.square.top ≫ input.square.right ≫
          eqToHom (semanticDerivedTargetGeometryAt input Q k g endpoint_eq).2.symm) := by
    unfold semanticDerivedDirectPulledRouteLegAt
    rw [Functor.map_comp,
      semanticGeometryPullLift_crossStageProjection,
      semanticGeometryPullLift_crossStageProjection]
    simp [semanticGeometryPullBaseHom]
  rw [hright]
  simp only [ActiveRefinementBCContext.retarget,
    semanticDerivedRefinementBCContext,
    activeRefinementBCContextOfCondition,
    semanticDerivedCompatibleProblemData,
    semanticDerivedSourceFiberDiagram]
  simp only [semanticDerivedPulledRefinement_exactImage input]
  have hlower := semanticDerivedTToCanonicalPulled_lower_fac
    input Q k g endpoint_eq square_isPullback
  rw [semanticDerivedPullbackTargetIso_hom] at hlower
  have htail := semanticDerivedTargetFst_eq_snd_right input
  simp only [Category.assoc] at htail hlower
  rw [← htail] at hlower
  have hlower' := congrArg
    (fun hom => hom ≫ eqToHom
      (semanticDerivedTargetGeometryAt input Q k g endpoint_eq).2.symm)
    hlower
  simp only [Category.assoc, eqToHom_refl, Category.id_comp] at hlower'
  have h := congrArg (fun hom => (exactPointedToRefinement U).map hom) hlower'
  change (exactPointedToRefinement U).map
    (semanticDerivedTToCanonicalPulledSourcePointIsoAt
      input Q k g endpoint_eq square_isPullback).hom ≫ (_ ≫ _) = _
  simp only [Functor.map_comp,
    exactPointedToRefinement_map_eqToHom,
    eqToHom_refl,
    semanticDerivedPulledComparison,
    semanticDerivedTargetFst,
    UpperGeometryCleavage.pullbackTargetGeometryHom,
    UpperGeometryCleavage.generatedExactGeometryHom,
    UpperGeometryCleavage.pullbackTargetExactArrow,
    UpperGeometryCleavage.exactBaseHom,
    exactGeometryToRefinementGeometry,
    exactPackageToRefinement,
    inverseCorePackageHom,
    semanticDerivedTargetPackage,
    RefinementBCConfiguration.targetPointAt,
    semanticOfExact_eq_exactPointedToRefinement_map] at h ⊢
  simpa using h

/-! ## Two-stage Cartesian comparison in the exact geometry category -/

private noncomputable def semanticExactRouteToCanonicalGeometryIso
    {U : AtomCarrier.{u}}
    {G C H : GeometryPackage.{u, v} U}
    (direct : (show GeomReadCategory U from G) ⟶
      (show GeomReadCategory U from H))
    (canonical : (show RefinementGeometryCategory U from ⟨C⟩) ⟶
      (show RefinementGeometryCategory U from ⟨H⟩))
    (pointIso : packagePoint G.core ≅ packagePoint C.core)
    (hbase : ((exactGeometryToRefinementGeometry U).map direct).base.base =
      (exactPointedToRefinement U).map pointIso.hom ≫ canonical.base.base)
    (hcanonPackage : (refinementPackageProjection U).IsStronglyCartesian
      canonical.base.base canonical.base)
    (hdirectPackage : (refinementPackageProjection U).IsStronglyCartesian
      (((exactGeometryToRefinementGeometry U).map direct).base.base)
      ((exactGeometryToRefinementGeometry U).map direct).base)
    (hcanonGeometry : (refinementGeometryProjection U).IsStronglyCartesian
      canonical.base canonical)
    (hdirectGeometry : (refinementGeometryProjection U).IsStronglyCartesian
      ((exactGeometryToRefinementGeometry U).map direct).base
      ((exactGeometryToRefinementGeometry U).map direct)) :
    (show GeomReadCategory U from G) ≅
      (show GeomReadCategory U from C) := by
  let directR := (exactGeometryToRefinementGeometry U).map direct
  let pointRefinementIso := (exactPointedToRefinement U).mapIso pointIso
  letI : (refinementPackageProjection U).IsStronglyCartesian
      canonical.base.base canonical.base := hcanonPackage
  letI : (refinementPackageProjection U).IsStronglyCartesian
      directR.base.base directR.base := hdirectPackage
  have packageBaseFac : directR.base.base =
      pointRefinementIso.hom ≫ canonical.base.base := hbase
  let packageRefinementIso :=
    CategoryTheory.Functor.IsStronglyCartesian.domainIsoOfBaseIso
      (p := refinementPackageProjection U) (g := pointRefinementIso)
      (f := canonical.base.base) (f' := directR.base.base)
      packageBaseFac canonical.base directR.base
  let packageMap := CategoryTheory.Functor.IsStronglyCartesian.map
    (refinementPackageProjection U) canonical.base.base canonical.base
    packageBaseFac directR.base
  letI hpackageMap : (refinementPackageProjection U).IsHomLift
      pointRefinementIso.hom packageMap :=
    CategoryTheory.Functor.IsStronglyCartesian.map_isHomLift
      (p := refinementPackageProjection U)
      (f := canonical.base.base) (φ := canonical.base)
      (g := pointRefinementIso.hom) (f' := directR.base.base)
      packageBaseFac directR.base
  have packageHomBase : packageRefinementIso.hom.base =
      pointRefinementIso.hom := by
    change packageMap.base = pointRefinementIso.hom
    exact (CategoryTheory.IsHomLift.eq_of_isHomLift
      (p := refinementPackageProjection U)
      (a := (⟨G.core⟩ : RefinementPackageTotalCategory U))
      (b := (⟨C.core⟩ : RefinementPackageTotalCategory U))
      (f := pointRefinementIso.hom) (φ := packageMap)).symm
  let packageIso := UpperGeometryCleavage.exactPackageIsoOfRefinementIso
    pointIso packageRefinementIso packageHomBase
  letI : (refinementGeometryProjection U).IsStronglyCartesian
      canonical.base canonical := hcanonGeometry
  letI : (refinementGeometryProjection U).IsStronglyCartesian
      directR.base directR := hdirectGeometry
  have packageFac : packageRefinementIso.hom ≫ canonical.base = directR.base :=
    CategoryTheory.Functor.IsStronglyCartesian.fac
      (refinementPackageProjection U) canonical.base.base canonical.base
      packageBaseFac directR.base
  have geometryBaseFac : directR.base =
      packageRefinementIso.hom ≫ canonical.base := packageFac.symm
  let geometryRefinementIso :=
    CategoryTheory.Functor.IsStronglyCartesian.domainIsoOfBaseIso
      (p := refinementGeometryProjection U) (g := packageRefinementIso)
      (f := canonical.base) (f' := directR.base)
      geometryBaseFac canonical directR
  let geometryMap := CategoryTheory.Functor.IsStronglyCartesian.map
    (refinementGeometryProjection U) canonical.base canonical
    geometryBaseFac directR
  letI hgeometryMap : (refinementGeometryProjection U).IsHomLift
      packageRefinementIso.hom geometryMap :=
    CategoryTheory.Functor.IsStronglyCartesian.map_isHomLift
      (p := refinementGeometryProjection U)
      (f := canonical.base) (φ := canonical)
      (g := packageRefinementIso.hom) (f' := directR.base)
      geometryBaseFac directR
  have geometryHomBase : geometryRefinementIso.hom.base =
      packageRefinementIso.hom := by
    change geometryMap.base = packageRefinementIso.hom
    exact (CategoryTheory.IsHomLift.eq_of_isHomLift
      (p := refinementGeometryProjection U)
      (a := (⟨G⟩ : RefinementGeometryCategory U))
      (b := (⟨C⟩ : RefinementGeometryCategory U))
      (f := packageRefinementIso.hom) (φ := geometryMap)).symm
  have packageToRefinement : (exactPackageToRefinement U).map packageIso.hom =
      packageRefinementIso.hom := by
    dsimp [packageIso]
    apply UpperGeometryCleavage.exactPackageHomOfRefinement_toRefinement
    exact packageHomBase
  exact UpperGeometryCleavage.exactGeometryIsoOfRefinementIso
    packageIso geometryRefinementIso
    (geometryHomBase.trans packageToRefinement.symm)

private theorem semanticExactGeometryIsoOfRefinementIso_hom_toRefinement
    {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
    (baseIso : (show PackageTotalCategory U from G.core) ≅
      (show PackageTotalCategory U from H.core))
    (refinementIso : RefinementGeometryObject.mk G ≅
      RefinementGeometryObject.mk H)
    (hbase : refinementIso.hom.base =
      (exactPackageToRefinement U).map baseIso.hom) :
    (exactGeometryToRefinementGeometry U).map
      (UpperGeometryCleavage.exactGeometryIsoOfRefinementIso
        baseIso refinementIso hbase).hom = refinementIso.hom := by
  exact UpperGeometryCleavage.exactGeometryHomOfRefinement_toRefinement _ _ _

private theorem semanticExactRouteToCanonicalGeometryIso_hom_fac
    {U : AtomCarrier.{u}} {G C H : GeometryPackage.{u, v} U}
    (direct : (show GeomReadCategory U from G) ⟶
      (show GeomReadCategory U from H))
    (canonical : (show RefinementGeometryCategory U from ⟨C⟩) ⟶
      (show RefinementGeometryCategory U from ⟨H⟩))
    (pointIso : packagePoint G.core ≅ packagePoint C.core)
    (hbase : ((exactGeometryToRefinementGeometry U).map direct).base.base =
      (exactPointedToRefinement U).map pointIso.hom ≫ canonical.base.base)
    (hcanonPackage : (refinementPackageProjection U).IsStronglyCartesian
      canonical.base.base canonical.base)
    (hdirectPackage : (refinementPackageProjection U).IsStronglyCartesian
      (((exactGeometryToRefinementGeometry U).map direct).base.base)
      ((exactGeometryToRefinementGeometry U).map direct).base)
    (hcanonGeometry : (refinementGeometryProjection U).IsStronglyCartesian
      canonical.base canonical)
    (hdirectGeometry : (refinementGeometryProjection U).IsStronglyCartesian
      ((exactGeometryToRefinementGeometry U).map direct).base
      ((exactGeometryToRefinementGeometry U).map direct)) :
    (exactGeometryToRefinementGeometry U).map
        (semanticExactRouteToCanonicalGeometryIso direct canonical pointIso
          hbase hcanonPackage hdirectPackage hcanonGeometry hdirectGeometry).hom ≫
      canonical = (exactGeometryToRefinementGeometry U).map direct := by
  letI : (refinementGeometryProjection U).IsStronglyCartesian
      canonical.base canonical := hcanonGeometry
  letI : (refinementPackageProjection U).IsStronglyCartesian
      canonical.base.base canonical.base := hcanonPackage
  letI : (refinementPackageProjection U).IsHomLift
      ((exactGeometryToRefinementGeometry U).map direct).base.base
      ((exactGeometryToRefinementGeometry U).map direct).base :=
    UpperGeometryCleavage.refinementPackageHom_isHomLift_of_base_eq _ _ rfl
  letI := UpperGeometryCleavage.refinementGeometryHom_isHomLift
    ((exactGeometryToRefinementGeometry U).map direct)
  unfold semanticExactRouteToCanonicalGeometryIso
  dsimp only
  rw [semanticExactGeometryIsoOfRefinementIso_hom_toRefinement]
  apply CategoryTheory.Functor.IsStronglyCartesian.fac
    (p := refinementGeometryProjection U)
    (f := canonical.base) (φ := canonical)
    (f' := ((exactGeometryToRefinementGeometry U).map direct).base)
  symm
  apply CategoryTheory.Functor.IsStronglyCartesian.fac
    (p := refinementPackageProjection U)
    (f := canonical.base.base) (φ := canonical.base)
    (f' := ((exactGeometryToRefinementGeometry U).map direct).base.base)
  exact hbase

private theorem semanticPullLiftPackage_isStronglyCartesian
    {U : AtomCarrier.{u}}
    {X Y : ExtractionInstance U} (f : ExtInstHom X Y)
    (target : GeomFiber.{u, v} Y) :
    (refinementPackageProjection U).IsStronglyCartesian
      (((exactGeometryToRefinementGeometry U).map
        (semanticGeometryPullLift f target)).base.base)
      (((exactGeometryToRefinementGeometry U).map
        (semanticGeometryPullLift f target)).base) := by
  change (refinementPackageProjection U).IsStronglyCartesian
    (((exactPackageToRefinement U).map
      (UpperGeometryCleavage.exactBaseHom target.1
        (semanticGeometryPullBaseHom f target))).base)
    ((exactPackageToRefinement U).map
      (UpperGeometryCleavage.exactBaseHom target.1
        (semanticGeometryPullBaseHom f target)))
  exact UpperGeometryCleavage.exactGeometryBase_isStronglyCartesian _ _

private theorem semanticDerivedDirectBaseRoute_packageStronglyCartesian
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U) (Q : AATCorePackage U)
    (k : Type v) [CommRing k] (g : FixedCoefficientGeometryAt Q k)
    (endpoint_eq : packagePoint Q = input.square.southwest) :
    (refinementPackageProjection U).IsStronglyCartesian
      (((exactGeometryToRefinementGeometry U).map
        (semanticDerivedDirectBaseRouteLegAt input Q k g endpoint_eq)).base.base)
      (((exactGeometryToRefinementGeometry U).map
        (semanticDerivedDirectBaseRouteLegAt input Q k g endpoint_eq)).base) := by
  let first := semanticGeometryPullLift input.square.left
    (semanticDerivedBottomPulledTargetGeometryAt input Q k g endpoint_eq)
  let second := semanticGeometryPullLift input.square.bottom
    (semanticDerivedTargetGeometryAt input Q k g endpoint_eq)
  letI hfirst : (refinementPackageProjection U).IsStronglyCartesian
      (((exactGeometryToRefinementGeometry U).map first).base.base)
      (((exactGeometryToRefinementGeometry U).map first).base) := by
    simpa [first] using semanticPullLiftPackage_isStronglyCartesian
      input.square.left
      (semanticDerivedBottomPulledTargetGeometryAt input Q k g endpoint_eq)
  letI hsecond : (refinementPackageProjection U).IsStronglyCartesian
      (((exactGeometryToRefinementGeometry U).map second).base.base)
      (((exactGeometryToRefinementGeometry U).map second).base) := by
    simpa [second] using semanticPullLiftPackage_isStronglyCartesian
      input.square.bottom
      (semanticDerivedTargetGeometryAt input Q k g endpoint_eq)
  simpa [semanticDerivedDirectBaseRouteLegAt, first, second, Functor.map_comp]
    using CategoryTheory.Functor.IsStronglyCartesian.comp
      (refinementPackageProjection U)

private theorem semanticDerivedDirectPulledRoute_packageStronglyCartesian
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U) (Q : AATCorePackage U)
    (k : Type v) [CommRing k] (g : FixedCoefficientGeometryAt Q k)
    (endpoint_eq : packagePoint Q = input.square.southwest) :
    (refinementPackageProjection U).IsStronglyCartesian
      (((exactGeometryToRefinementGeometry U).map
        (semanticDerivedDirectPulledRouteLegAt input Q k g endpoint_eq)).base.base)
      (((exactGeometryToRefinementGeometry U).map
        (semanticDerivedDirectPulledRouteLegAt input Q k g endpoint_eq)).base) := by
  let first := semanticGeometryPullLift input.square.top
    (semanticDerivedViaBaseGeometryAt input Q k g endpoint_eq)
  let second := semanticGeometryPullLift input.square.right
    (semanticDerivedTargetGeometryAt input Q k g endpoint_eq)
  letI hfirst : (refinementPackageProjection U).IsStronglyCartesian
      (((exactGeometryToRefinementGeometry U).map first).base.base)
      (((exactGeometryToRefinementGeometry U).map first).base) := by
    simpa [first] using semanticPullLiftPackage_isStronglyCartesian
      input.square.top
      (semanticDerivedViaBaseGeometryAt input Q k g endpoint_eq)
  letI hsecond : (refinementPackageProjection U).IsStronglyCartesian
      (((exactGeometryToRefinementGeometry U).map second).base.base)
      (((exactGeometryToRefinementGeometry U).map second).base) := by
    simpa [second] using semanticPullLiftPackage_isStronglyCartesian
      input.square.right
      (semanticDerivedTargetGeometryAt input Q k g endpoint_eq)
  simpa [semanticDerivedDirectPulledRouteLegAt, first, second, Functor.map_comp]
    using CategoryTheory.Functor.IsStronglyCartesian.comp
      (refinementPackageProjection U)

private theorem semanticDerivedDirectBaseRoute_geometryStronglyCartesian
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U) (Q : AATCorePackage U)
    (k : Type v) [CommRing k] (g : FixedCoefficientGeometryAt Q k)
    (endpoint_eq : packagePoint Q = input.square.southwest) :
    (refinementGeometryProjection U).IsStronglyCartesian
      (((exactGeometryToRefinementGeometry U).map
        (semanticDerivedDirectBaseRouteLegAt input Q k g endpoint_eq)).base)
      ((exactGeometryToRefinementGeometry U).map
        (semanticDerivedDirectBaseRouteLegAt input Q k g endpoint_eq)) := by
  let first := semanticGeometryPullLift input.square.left
    (semanticDerivedBottomPulledTargetGeometryAt input Q k g endpoint_eq)
  let second := semanticGeometryPullLift input.square.bottom
    (semanticDerivedTargetGeometryAt input Q k g endpoint_eq)
  letI hfirst : (refinementGeometryProjection U).IsStronglyCartesian
      (((exactGeometryToRefinementGeometry U).map first).base)
      ((exactGeometryToRefinementGeometry U).map first) := by
    simpa [first] using semanticGeometryPullLift_refinementStronglyCartesian
      input.square.left
      (semanticDerivedBottomPulledTargetGeometryAt input Q k g endpoint_eq)
  letI hsecond : (refinementGeometryProjection U).IsStronglyCartesian
      (((exactGeometryToRefinementGeometry U).map second).base)
      ((exactGeometryToRefinementGeometry U).map second) := by
    simpa [second] using semanticGeometryPullLift_refinementStronglyCartesian
      input.square.bottom
      (semanticDerivedTargetGeometryAt input Q k g endpoint_eq)
  simpa [semanticDerivedDirectBaseRouteLegAt, first, second, Functor.map_comp]
    using CategoryTheory.Functor.IsStronglyCartesian.comp
      (refinementGeometryProjection U)

private theorem semanticDerivedDirectPulledRoute_geometryStronglyCartesian
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U) (Q : AATCorePackage U)
    (k : Type v) [CommRing k] (g : FixedCoefficientGeometryAt Q k)
    (endpoint_eq : packagePoint Q = input.square.southwest) :
    (refinementGeometryProjection U).IsStronglyCartesian
      (((exactGeometryToRefinementGeometry U).map
        (semanticDerivedDirectPulledRouteLegAt input Q k g endpoint_eq)).base)
      ((exactGeometryToRefinementGeometry U).map
        (semanticDerivedDirectPulledRouteLegAt input Q k g endpoint_eq)) := by
  let first := semanticGeometryPullLift input.square.top
    (semanticDerivedViaBaseGeometryAt input Q k g endpoint_eq)
  let second := semanticGeometryPullLift input.square.right
    (semanticDerivedTargetGeometryAt input Q k g endpoint_eq)
  letI hfirst : (refinementGeometryProjection U).IsStronglyCartesian
      (((exactGeometryToRefinementGeometry U).map first).base)
      ((exactGeometryToRefinementGeometry U).map first) := by
    simpa [first] using semanticGeometryPullLift_refinementStronglyCartesian
      input.square.top
      (semanticDerivedViaBaseGeometryAt input Q k g endpoint_eq)
  letI hsecond : (refinementGeometryProjection U).IsStronglyCartesian
      (((exactGeometryToRefinementGeometry U).map second).base)
      ((exactGeometryToRefinementGeometry U).map second) := by
    simpa [second] using semanticGeometryPullLift_refinementStronglyCartesian
      input.square.right
      (semanticDerivedTargetGeometryAt input Q k g endpoint_eq)
  simpa [semanticDerivedDirectPulledRouteLegAt, first, second, Functor.map_comp]
    using CategoryTheory.Functor.IsStronglyCartesian.comp
      (refinementGeometryProjection U)

/-- The literal base-first exact endpoint is exactly isomorphic to the
canonical G-118 base normalization. -/
noncomputable def semanticDerivedBToCanonicalBaseGeometryIsoAt
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U) (Q : AATCorePackage U)
    (k : Type v) [CommRing k] (g : FixedCoefficientGeometryAt Q k)
    (endpoint_eq : packagePoint Q = input.square.southwest)
    (square_isPullback : IsPullback input.square.left input.square.top
      input.square.bottom input.square.right) :
    (show GeomReadCategory U from
      (semanticDerivedBGeometryAt input Q k g endpoint_eq).1) ≅
    (show GeomReadCategory U from
      (semanticDerivedCanonicalBaseRouteFiberAt input Q k g endpoint_eq).1) := by
  let problem := semanticDerivedCompatibleProblemData input Q k g endpoint_eq
  let canonical := problem.canonicalAuthoredBaseRouteGeometryHomAt PUnit.unit
  let direct := semanticDerivedDirectBaseRouteLegAt input Q k g endpoint_eq
  let pointIso := semanticDerivedBToCanonicalBaseSourcePointIsoAt
    input Q k g endpoint_eq square_isPullback
  apply semanticExactRouteToCanonicalGeometryIso direct canonical pointIso
  · simpa [direct, canonical, pointIso, problem] using
      (semanticDerivedCanonicalBaseRoute_refinementExactImage
        input Q k g endpoint_eq square_isPullback).symm
  · simpa [canonical, problem] using
      UpperGeometryCleavage.baseRouteGeometryBase_isStronglyCartesian
        (semanticDerivedRefinementBCContext input
          (semanticDerivedSouthwestGeometryFiber input Q k g endpoint_eq))
        (problem.sourceTargetGeometryAt PUnit.unit)
  · simpa [direct] using
      semanticDerivedDirectBaseRoute_packageStronglyCartesian
        input Q k g endpoint_eq
  · simpa [canonical, problem] using
      problem.canonicalAuthoredBaseRouteGeometryHomAt_isStronglyCartesian
        PUnit.unit
  · simpa [direct] using
      semanticDerivedDirectBaseRoute_geometryStronglyCartesian
        input Q k g endpoint_eq

/-- The literal pulled-first exact endpoint is exactly isomorphic to the
canonical G-118 pulled normalization. -/
noncomputable def semanticDerivedTToCanonicalPulledGeometryIsoAt
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U) (Q : AATCorePackage U)
    (k : Type v) [CommRing k] (g : FixedCoefficientGeometryAt Q k)
    (endpoint_eq : packagePoint Q = input.square.southwest)
    (square_isPullback : IsPullback input.square.left input.square.top
      input.square.bottom input.square.right) :
    (show GeomReadCategory U from
      (semanticDerivedTGeometryAt input Q k g endpoint_eq).1) ≅
    (show GeomReadCategory U from
      (semanticDerivedCanonicalPulledRouteFiberAt input Q k g endpoint_eq).1) := by
  let problem := semanticDerivedCompatibleProblemData input Q k g endpoint_eq
  let canonical := problem.canonicalAuthoredPulledRouteGeometryHomAt PUnit.unit
  let direct := semanticDerivedDirectPulledRouteLegAt input Q k g endpoint_eq
  let pointIso := semanticDerivedTToCanonicalPulledSourcePointIsoAt
    input Q k g endpoint_eq square_isPullback
  apply semanticExactRouteToCanonicalGeometryIso direct canonical pointIso
  · simpa [direct, canonical, pointIso, problem] using
      (semanticDerivedCanonicalPulledRoute_refinementExactImage
        input Q k g endpoint_eq square_isPullback).symm
  · simpa [canonical, problem] using
      UpperGeometryCleavage.pulledRouteGeometryBase_isStronglyCartesian
        (semanticDerivedRefinementBCContext input
          (semanticDerivedSouthwestGeometryFiber input Q k g endpoint_eq))
        (problem.sourceTargetGeometryAt PUnit.unit)
  · simpa [direct] using
      semanticDerivedDirectPulledRoute_packageStronglyCartesian
        input Q k g endpoint_eq
  · simpa [canonical, problem] using
      problem.canonicalAuthoredPulledRouteGeometryHomAt_isStronglyCartesian
        PUnit.unit
  · simpa [direct] using
      semanticDerivedDirectPulledRoute_geometryStronglyCartesian
        input Q k g endpoint_eq

theorem semanticDerivedBToCanonicalBaseGeometryIsoAt_hom_fac
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U) (Q : AATCorePackage U)
    (k : Type v) [CommRing k] (g : FixedCoefficientGeometryAt Q k)
    (endpoint_eq : packagePoint Q = input.square.southwest)
    (square_isPullback : IsPullback input.square.left input.square.top
      input.square.bottom input.square.right) :
    (exactGeometryToRefinementGeometry U).map
        (semanticDerivedBToCanonicalBaseGeometryIsoAt
          input Q k g endpoint_eq square_isPullback).hom ≫
      (semanticDerivedCompatibleProblemData input Q k g endpoint_eq).canonicalAuthoredBaseRouteGeometryHomAt PUnit.unit =
    (exactGeometryToRefinementGeometry U).map
      (semanticDerivedDirectBaseRouteLegAt input Q k g endpoint_eq) := by
  let problem := semanticDerivedCompatibleProblemData input Q k g endpoint_eq
  unfold semanticDerivedBToCanonicalBaseGeometryIsoAt
  exact semanticExactRouteToCanonicalGeometryIso_hom_fac
    (semanticDerivedDirectBaseRouteLegAt input Q k g endpoint_eq)
    (problem.canonicalAuthoredBaseRouteGeometryHomAt PUnit.unit)
    (semanticDerivedBToCanonicalBaseSourcePointIsoAt
      input Q k g endpoint_eq square_isPullback)
    (by simpa using
      (semanticDerivedCanonicalBaseRoute_refinementExactImage
        input Q k g endpoint_eq square_isPullback).symm)
    (by simpa [problem] using (UpperGeometryCleavage.baseRouteGeometryBase_isStronglyCartesian
      (semanticDerivedRefinementBCContext input
        (semanticDerivedSouthwestGeometryFiber input Q k g endpoint_eq))
      (problem.sourceTargetGeometryAt PUnit.unit)))
    (semanticDerivedDirectBaseRoute_packageStronglyCartesian input Q k g endpoint_eq)
    (by simpa [problem] using
      problem.canonicalAuthoredBaseRouteGeometryHomAt_isStronglyCartesian PUnit.unit)
    (semanticDerivedDirectBaseRoute_geometryStronglyCartesian input Q k g endpoint_eq)

theorem semanticDerivedTToCanonicalPulledGeometryIsoAt_hom_fac
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U) (Q : AATCorePackage U)
    (k : Type v) [CommRing k] (g : FixedCoefficientGeometryAt Q k)
    (endpoint_eq : packagePoint Q = input.square.southwest)
    (square_isPullback : IsPullback input.square.left input.square.top
      input.square.bottom input.square.right) :
    (exactGeometryToRefinementGeometry U).map
        (semanticDerivedTToCanonicalPulledGeometryIsoAt
          input Q k g endpoint_eq square_isPullback).hom ≫
      (semanticDerivedCompatibleProblemData input Q k g endpoint_eq).canonicalAuthoredPulledRouteGeometryHomAt PUnit.unit =
    (exactGeometryToRefinementGeometry U).map
      (semanticDerivedDirectPulledRouteLegAt input Q k g endpoint_eq) := by
  let problem := semanticDerivedCompatibleProblemData input Q k g endpoint_eq
  unfold semanticDerivedTToCanonicalPulledGeometryIsoAt
  exact semanticExactRouteToCanonicalGeometryIso_hom_fac
    (semanticDerivedDirectPulledRouteLegAt input Q k g endpoint_eq)
    (problem.canonicalAuthoredPulledRouteGeometryHomAt PUnit.unit)
    (semanticDerivedTToCanonicalPulledSourcePointIsoAt
      input Q k g endpoint_eq square_isPullback)
    (by simpa using
      (semanticDerivedCanonicalPulledRoute_refinementExactImage
        input Q k g endpoint_eq square_isPullback).symm)
    (by simpa [problem] using (UpperGeometryCleavage.pulledRouteGeometryBase_isStronglyCartesian
      (semanticDerivedRefinementBCContext input
        (semanticDerivedSouthwestGeometryFiber input Q k g endpoint_eq))
      (problem.sourceTargetGeometryAt PUnit.unit)))
    (semanticDerivedDirectPulledRoute_packageStronglyCartesian input Q k g endpoint_eq)
    (by simpa [problem] using
      problem.canonicalAuthoredPulledRouteGeometryHomAt_isStronglyCartesian PUnit.unit)
    (semanticDerivedDirectPulledRoute_geometryStronglyCartesian input Q k g endpoint_eq)

theorem semanticDerivedBToCanonicalBaseGeometryIsoAt_hom_projection
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U) (Q : AATCorePackage U)
    (k : Type v) [CommRing k] (g : FixedCoefficientGeometryAt Q k)
    (endpoint_eq : packagePoint Q = input.square.southwest)
    (square_isPullback : IsPullback input.square.left input.square.top
      input.square.bottom input.square.right) :
    (crossStageProjection U).map
      (semanticDerivedBToCanonicalBaseGeometryIsoAt
        input Q k g endpoint_eq square_isPullback).hom =
    (semanticDerivedBToCanonicalBaseSourcePointIsoAt
      input Q k g endpoint_eq square_isPullback).hom := by
  change (semanticDerivedBToCanonicalBaseGeometryIsoAt
    input Q k g endpoint_eq square_isPullback).hom.base.base = _
  unfold semanticDerivedBToCanonicalBaseGeometryIsoAt
  rfl

theorem semanticDerivedTToCanonicalPulledGeometryIsoAt_hom_projection
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U) (Q : AATCorePackage U)
    (k : Type v) [CommRing k] (g : FixedCoefficientGeometryAt Q k)
    (endpoint_eq : packagePoint Q = input.square.southwest)
    (square_isPullback : IsPullback input.square.left input.square.top
      input.square.bottom input.square.right) :
    (crossStageProjection U).map
      (semanticDerivedTToCanonicalPulledGeometryIsoAt
        input Q k g endpoint_eq square_isPullback).hom =
    (semanticDerivedTToCanonicalPulledSourcePointIsoAt
      input Q k g endpoint_eq square_isPullback).hom := by
  change (semanticDerivedTToCanonicalPulledGeometryIsoAt
    input Q k g endpoint_eq square_isPullback).hom.base.base = _
  unfold semanticDerivedTToCanonicalPulledGeometryIsoAt
  rfl

private noncomputable def semanticFiberIsoToTransportAlongIso
    {U : AtomCarrier.{u}} {X Y : ExtractionInstance U}
    (sigma : X ≅ Y) (source : GeomFiber.{u, v} Y)
    (target : GeomFiber.{u, v} X) (comparison : source.1 ≅ target.1)
    (hbase : (crossStageProjection U).map comparison.hom ≫
      eqToHom target.2 = eqToHom source.2 ≫ sigma.inv) :
    source ≅ (geomFiberTransportFunctor sigma.hom).obj target := by
  let lift := geomFiberLift sigma.hom target
  let transported := (geomFiberTransportFunctor sigma.hom).obj target
  let forwardTotal := comparison.hom ≫ lift
  have forward_projection :
      (crossStageProjection U).map forwardTotal ≫ eqToHom transported.2 =
        eqToHom source.2 ≫ 𝟙 Y := by
    change (crossStageProjection U).map (comparison.hom ≫ lift) ≫
      eqToHom transported.2 = eqToHom source.2 ≫ 𝟙 Y
    rw [Functor.map_comp, Category.assoc]
    change (crossStageProjection U).map comparison.hom ≫
      ((crossStageProjection U).map (geomFiberLift sigma.hom target) ≫
        eqToHom transported.2) = _
    rw [geomFiberLift_projection]
    rw [← Category.assoc, hbase]
    simp
  let forward : source ⟶ transported :=
    ⟨forwardTotal, CategoryTheory.IsHomLift.of_commsq
      (crossStageProjection U) (𝟙 Y) forwardTotal source.2 transported.2
      forward_projection⟩
  letI hlift : (crossStageProjection U).IsStronglyCocartesian
      sigma.hom lift := by
    simpa [lift] using geomFiberLift_isStronglyCocartesian sigma.hom target
  letI : IsIso lift :=
    CategoryTheory.Functor.IsStronglyCocartesian.isIso_of_base_isIso
      (crossStageProjection U) sigma.hom lift
  letI : IsIso forwardTotal := by
    dsimp [forwardTotal]
    infer_instance
  letI : IsIso forward := semanticGeomFiberHom_isIso_of_total_isIso forward
  exact asIso forward

/-- The canonical base-route geometry transported to the original northwest
semantic fiber. -/
noncomputable def semanticDerivedCanonicalBaseRouteNorthwestAt
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U) (Q : AATCorePackage U)
    (k : Type v) [CommRing k] (g : FixedCoefficientGeometryAt Q k)
    (endpoint_eq : packagePoint Q = input.square.southwest)
    (square_isPullback : IsPullback input.square.left input.square.top
      input.square.bottom input.square.right) :
    GeomFiber input.square.northwest :=
  (geomFiberTransportFunctor
    (semanticDerivedPullbackSourceIso input square_isPullback).hom).obj
      (semanticDerivedCanonicalBaseRouteFiberAt input Q k g endpoint_eq)

noncomputable def semanticDerivedCanonicalPulledRouteNorthwestAt
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U) (Q : AATCorePackage U)
    (k : Type v) [CommRing k] (g : FixedCoefficientGeometryAt Q k)
    (endpoint_eq : packagePoint Q = input.square.southwest)
    (square_isPullback : IsPullback input.square.left input.square.top
      input.square.bottom input.square.right) :
    GeomFiber input.square.northwest :=
  (geomFiberTransportFunctor
    (semanticDerivedPullbackSourceIso input square_isPullback).hom).obj
      (semanticDerivedCanonicalPulledRouteFiberAt input Q k g endpoint_eq)

/-- Literal `B` compared to the canonical G-118 base route in the northwest
fiber. -/
noncomputable def semanticDerivedBToCanonicalBaseNorthwestIsoAt
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U) (Q : AATCorePackage U)
    (k : Type v) [CommRing k] (g : FixedCoefficientGeometryAt Q k)
    (endpoint_eq : packagePoint Q = input.square.southwest)
    (square_isPullback : IsPullback input.square.left input.square.top
      input.square.bottom input.square.right) :
    semanticDerivedBGeometryAt input Q k g endpoint_eq ≅
      semanticDerivedCanonicalBaseRouteNorthwestAt
        input Q k g endpoint_eq square_isPullback := by
  apply semanticFiberIsoToTransportAlongIso
    (semanticDerivedPullbackSourceIso input square_isPullback)
    (semanticDerivedBGeometryAt input Q k g endpoint_eq)
    (semanticDerivedCanonicalBaseRouteFiberAt input Q k g endpoint_eq)
    (semanticDerivedBToCanonicalBaseGeometryIsoAt
      input Q k g endpoint_eq square_isPullback)
  rw [semanticDerivedBToCanonicalBaseGeometryIsoAt_hom_projection]
  simp [semanticDerivedBToCanonicalBaseSourcePointIsoAt, eqToIso]

noncomputable def semanticDerivedTToCanonicalPulledNorthwestIsoAt
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U) (Q : AATCorePackage U)
    (k : Type v) [CommRing k] (g : FixedCoefficientGeometryAt Q k)
    (endpoint_eq : packagePoint Q = input.square.southwest)
    (square_isPullback : IsPullback input.square.left input.square.top
      input.square.bottom input.square.right) :
    semanticDerivedTGeometryAt input Q k g endpoint_eq ≅
      semanticDerivedCanonicalPulledRouteNorthwestAt
        input Q k g endpoint_eq square_isPullback := by
  apply semanticFiberIsoToTransportAlongIso
    (semanticDerivedPullbackSourceIso input square_isPullback)
    (semanticDerivedTGeometryAt input Q k g endpoint_eq)
    (semanticDerivedCanonicalPulledRouteFiberAt input Q k g endpoint_eq)
    (semanticDerivedTToCanonicalPulledGeometryIsoAt
      input Q k g endpoint_eq square_isPullback)
  rw [semanticDerivedTToCanonicalPulledGeometryIsoAt_hom_projection]
  simp [semanticDerivedTToCanonicalPulledSourcePointIsoAt, eqToIso]

/-- Literal `B` compared to the actual generated G-118 base-route endpoint. -/
noncomputable def semanticDerivedBToGeneratedBaseNorthwestIsoAt
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U) (Q : AATCorePackage U)
    (k : Type v) [CommRing k] (g : FixedCoefficientGeometryAt Q k)
    (endpoint_eq : packagePoint Q = input.square.southwest)
    (square_isPullback : IsPullback input.square.left input.square.top
      input.square.bottom input.square.right) :
    semanticDerivedBGeometryAt input Q k g endpoint_eq ≅
      semanticDerivedGeneratedBaseRouteNorthwestAt
        input Q k g endpoint_eq square_isPullback :=
  semanticDerivedBToCanonicalBaseNorthwestIsoAt
      input Q k g endpoint_eq square_isPullback ≪≫
    (geomFiberTransportFunctor
      (semanticDerivedPullbackSourceIso input square_isPullback).hom).mapIso
        (semanticDerivedCanonicalBaseToGeneratedFiberIsoAt
          input Q k g endpoint_eq)

/-- The actual generated G-118 pulled-route endpoint compared to literal `T`. -/
noncomputable def semanticDerivedGeneratedPulledToTNorthwestIsoAt
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U) (Q : AATCorePackage U)
    (k : Type v) [CommRing k] (g : FixedCoefficientGeometryAt Q k)
    (endpoint_eq : packagePoint Q = input.square.southwest)
    (square_isPullback : IsPullback input.square.left input.square.top
      input.square.bottom input.square.right) :
    semanticDerivedGeneratedPulledRouteNorthwestAt
        input Q k g endpoint_eq square_isPullback ≅
      semanticDerivedTGeometryAt input Q k g endpoint_eq :=
  ((geomFiberTransportFunctor
      (semanticDerivedPullbackSourceIso input square_isPullback).hom).mapIso
        (semanticDerivedCanonicalPulledToGeneratedFiberIsoAt
          input Q k g endpoint_eq)).symm ≪≫
    (semanticDerivedTToCanonicalPulledNorthwestIsoAt
      input Q k g endpoint_eq square_isPullback).symm

/-- The actual generated G-118 mate, transported to the two literal exact
pullback endpoints through the proved endpoint comparisons. -/
noncomputable def semanticDerivedGeneratedMateOnLiteralEndpointsIsoAt
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U) (Q : AATCorePackage U)
    (k : Type v) [CommRing k] (g : FixedCoefficientGeometryAt Q k)
    (endpoint_eq : packagePoint Q = input.square.southwest)
    (square_isPullback : IsPullback input.square.left input.square.top
      input.square.bottom input.square.right) :
    semanticDerivedBGeometryAt input Q k g endpoint_eq ≅
      semanticDerivedTGeometryAt input Q k g endpoint_eq := by
  let mate := semanticDerivedGeneratedMateNorthwestAt
    input Q k g endpoint_eq square_isPullback
  letI : IsIso mate := semanticDerivedGeneratedMateNorthwestAt_isIso
    input Q k g endpoint_eq square_isPullback
  exact semanticDerivedBToGeneratedBaseNorthwestIsoAt
      input Q k g endpoint_eq square_isPullback ≪≫
    asIso mate ≪≫
    semanticDerivedGeneratedPulledToTNorthwestIsoAt
      input Q k g endpoint_eq square_isPullback

private noncomputable def semanticDerivedCanonicalMateInMixedFiberAt
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U) (Q : AATCorePackage U)
    (k : Type v) [CommRing k] (g : FixedCoefficientGeometryAt Q k)
    (endpoint_eq : packagePoint Q = input.square.southwest) :
    semanticDerivedCanonicalBaseRouteFiberAt input Q k g endpoint_eq ⟶
      semanticDerivedCanonicalPulledRouteFiberAt input Q k g endpoint_eq :=
  (semanticDerivedCanonicalBaseToGeneratedFiberIsoAt input Q k g endpoint_eq).hom ≫
    semanticDerivedGeneratedMateInMixedFiberAt input Q k g endpoint_eq ≫
    (semanticDerivedCanonicalPulledToGeneratedFiberIsoAt input Q k g endpoint_eq).inv

private theorem semanticDerivedCanonicalMateInMixedFiberAt_toRefinement
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U) (Q : AATCorePackage U)
    (k : Type v) [CommRing k] (g : FixedCoefficientGeometryAt Q k)
    (endpoint_eq : packagePoint Q = input.square.southwest) :
    (exactGeometryToRefinementGeometry U).map
        (semanticDerivedCanonicalMateInMixedFiberAt input Q k g endpoint_eq).1 =
      (semanticDerivedCompatibleProblemData input Q k g endpoint_eq).canonicalAuthoredUpperGeometryMateRefinementAt PUnit.unit := by
  let problem := semanticDerivedCompatibleProblemData input Q k g endpoint_eq
  change (exactGeometryToRefinementGeometry U).map
    ((semanticDerivedCanonicalBaseToGeneratedFiberIsoAt input Q k g endpoint_eq).hom.1 ≫
      (semanticDerivedGeneratedMateInMixedFiberAt input Q k g endpoint_eq).1 ≫
      (semanticDerivedCanonicalPulledToGeneratedFiberIsoAt input Q k g endpoint_eq).inv.1) = _
  simp only [Functor.map_comp]
  rw [show (exactGeometryToRefinementGeometry U).map
      (semanticDerivedCanonicalBaseToGeneratedFiberIsoAt input Q k g endpoint_eq).hom.1 =
        (problem.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt PUnit.unit).hom from
    problem.canonicalAuthoredBaseToGeneratedRouteExactGeometryHomAt_toRefinement PUnit.unit]
  rw [show (exactGeometryToRefinementGeometry U).map
      (semanticDerivedGeneratedMateInMixedFiberAt input Q k g endpoint_eq).1 =
        (exactGeometryToRefinementGeometry U).map
          (problem.generatedCompatibleUpperGeometryMateAt PUnit.unit) from rfl]
  have pulledHom :
      (semanticDerivedCanonicalPulledToGeneratedFiberIsoAt
        input Q k g endpoint_eq).hom.1 =
      (problem.canonicalAuthoredPulledToGeneratedRouteExactGeometryIsoAt PUnit.unit).hom := by
    rfl
  have pulledInv :
      (semanticDerivedCanonicalPulledToGeneratedFiberIsoAt
        input Q k g endpoint_eq).inv.1 =
      problem.canonicalAuthoredPulledToGeneratedRouteExactGeometryInvAt PUnit.unit := by
    let exactIso := problem.canonicalAuthoredPulledToGeneratedRouteExactGeometryIsoAt PUnit.unit
    apply (cancel_mono exactIso.hom).1
    calc
      (semanticDerivedCanonicalPulledToGeneratedFiberIsoAt
          input Q k g endpoint_eq).inv.1 ≫ exactIso.hom =
        (semanticDerivedCanonicalPulledToGeneratedFiberIsoAt
          input Q k g endpoint_eq).inv.1 ≫
        (semanticDerivedCanonicalPulledToGeneratedFiberIsoAt
          input Q k g endpoint_eq).hom.1 := by rw [pulledHom]
      _ = 𝟙 _ := by
        change ((semanticDerivedCanonicalPulledToGeneratedFiberIsoAt
          input Q k g endpoint_eq).inv ≫
          (semanticDerivedCanonicalPulledToGeneratedFiberIsoAt
            input Q k g endpoint_eq).hom).1 = _
        simpa only [Iso.inv_hom_id] using (show
          ((𝟙 (semanticDerivedGeneratedPulledRouteFiberAt input Q k g endpoint_eq)) :
            (semanticDerivedGeneratedPulledRouteFiberAt input Q k g endpoint_eq) ⟶
              (semanticDerivedGeneratedPulledRouteFiberAt input Q k g endpoint_eq)).1 =
            𝟙 (semanticDerivedGeneratedPulledRouteFiberAt input Q k g endpoint_eq).1 from rfl)
      _ = problem.canonicalAuthoredPulledToGeneratedRouteExactGeometryInvAt
          PUnit.unit ≫ exactIso.hom := by
        change 𝟙 _ = exactIso.inv ≫ exactIso.hom
        simp
  rw [show (exactGeometryToRefinementGeometry U).map
      (semanticDerivedCanonicalPulledToGeneratedFiberIsoAt input Q k g endpoint_eq).inv.1 =
        (problem.canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt PUnit.unit).inv from
    pulledInv ▸ problem.canonicalAuthoredPulledToGeneratedRouteExactGeometryInvAt_toRefinement PUnit.unit]
  rfl

private theorem semanticDerivedBToCanonicalBaseNorthwestIsoAt_hom
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U) (Q : AATCorePackage U)
    (k : Type v) [CommRing k] (g : FixedCoefficientGeometryAt Q k)
    (endpoint_eq : packagePoint Q = input.square.southwest)
    (square_isPullback : IsPullback input.square.left input.square.top
      input.square.bottom input.square.right) :
    (semanticDerivedBToCanonicalBaseNorthwestIsoAt
      input Q k g endpoint_eq square_isPullback).hom.1 =
    (semanticDerivedBToCanonicalBaseGeometryIsoAt
      input Q k g endpoint_eq square_isPullback).hom ≫
    geomFiberLift (semanticDerivedPullbackSourceIso input square_isPullback).hom
      (semanticDerivedCanonicalBaseRouteFiberAt input Q k g endpoint_eq) := by
  rfl

private theorem semanticDerivedTToCanonicalPulledNorthwestIsoAt_hom
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U) (Q : AATCorePackage U)
    (k : Type v) [CommRing k] (g : FixedCoefficientGeometryAt Q k)
    (endpoint_eq : packagePoint Q = input.square.southwest)
    (square_isPullback : IsPullback input.square.left input.square.top
      input.square.bottom input.square.right) :
    (semanticDerivedTToCanonicalPulledNorthwestIsoAt
      input Q k g endpoint_eq square_isPullback).hom.1 =
    (semanticDerivedTToCanonicalPulledGeometryIsoAt
      input Q k g endpoint_eq square_isPullback).hom ≫
    geomFiberLift (semanticDerivedPullbackSourceIso input square_isPullback).hom
      (semanticDerivedCanonicalPulledRouteFiberAt input Q k g endpoint_eq) := by
  rfl

private theorem semanticDerivedGeneratedMateOnLiteralEndpoints_decomposition
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U) (Q : AATCorePackage U)
    (k : Type v) [CommRing k] (g : FixedCoefficientGeometryAt Q k)
    (endpoint_eq : packagePoint Q = input.square.southwest)
    (square_isPullback : IsPullback input.square.left input.square.top
      input.square.bottom input.square.right) :
    (semanticDerivedGeneratedMateOnLiteralEndpointsIsoAt
      input Q k g endpoint_eq square_isPullback).hom =
      (semanticDerivedBToCanonicalBaseNorthwestIsoAt
        input Q k g endpoint_eq square_isPullback).hom ≫
      (geomFiberTransportFunctor
        (semanticDerivedPullbackSourceIso input square_isPullback).hom).map
          (semanticDerivedCanonicalMateInMixedFiberAt input Q k g endpoint_eq) ≫
      (semanticDerivedTToCanonicalPulledNorthwestIsoAt
        input Q k g endpoint_eq square_isPullback).inv := by
  simp [semanticDerivedGeneratedMateOnLiteralEndpointsIsoAt,
    semanticDerivedBToGeneratedBaseNorthwestIsoAt,
    semanticDerivedGeneratedPulledToTNorthwestIsoAt,
    semanticDerivedGeneratedMateNorthwestAt,
    semanticDerivedCanonicalMateInMixedFiberAt, Functor.map_comp]

/-- The actual generated G-118 comparison satisfies the literal two-route
triangle after transporting both endpoints to the semantic square. -/
theorem semanticDerivedGeneratedMateOnLiteralEndpoints_triangle
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U) (Q : AATCorePackage U)
    (k : Type v) [CommRing k] (g : FixedCoefficientGeometryAt Q k)
    (endpoint_eq : packagePoint Q = input.square.southwest)
    (square_isPullback : IsPullback input.square.left input.square.top
      input.square.bottom input.square.right) :
    (semanticDerivedGeneratedMateOnLiteralEndpointsIsoAt
      input Q k g endpoint_eq square_isPullback).hom.1 ≫
        semanticDerivedDirectPulledRouteLegAt input Q k g endpoint_eq =
      semanticDerivedDirectBaseRouteLegAt input Q k g endpoint_eq := by
  let problem := semanticDerivedCompatibleProblemData input Q k g endpoint_eq
  let sigma := (semanticDerivedPullbackSourceIso input square_isPullback).hom
  let pulledFiber := semanticDerivedCanonicalPulledRouteFiberAt input Q k g endpoint_eq
  let pulledLift := geomFiberLift sigma pulledFiber
  letI hpulledLiftStrong : (crossStageProjection U).IsStronglyCocartesian
      sigma pulledLift := by
    simpa [sigma, pulledLift, pulledFiber] using
      geomFiberLift_isStronglyCocartesian sigma pulledFiber
  letI hpulledLiftIso : IsIso pulledLift :=
    CategoryTheory.Functor.IsStronglyCocartesian.isIso_of_base_isIso
      (crossStageProjection U) sigma pulledLift
  have htargetInv :
      (semanticDerivedTToCanonicalPulledNorthwestIsoAt
          input Q k g endpoint_eq square_isPullback).inv.1 ≫
        (semanticDerivedTToCanonicalPulledGeometryIsoAt
          input Q k g endpoint_eq square_isPullback).hom =
      inv pulledLift := by
    apply (cancel_mono pulledLift).1
    rw [Category.assoc,
      ← semanticDerivedTToCanonicalPulledNorthwestIsoAt_hom]
    change ((semanticDerivedTToCanonicalPulledNorthwestIsoAt
      input Q k g endpoint_eq square_isPullback).inv ≫
        (semanticDerivedTToCanonicalPulledNorthwestIsoAt
          input Q k g endpoint_eq square_isPullback).hom).1 = _
    simp
    rfl
  have htarget :
      (exactGeometryToRefinementGeometry U).map
          (semanticDerivedTToCanonicalPulledNorthwestIsoAt
            input Q k g endpoint_eq square_isPullback).inv.1 ≫
        (exactGeometryToRefinementGeometry U).map
          (semanticDerivedDirectPulledRouteLegAt input Q k g endpoint_eq) =
      (exactGeometryToRefinementGeometry U).map (inv pulledLift) ≫
        problem.canonicalAuthoredPulledRouteGeometryHomAt PUnit.unit := by
    rw [← semanticDerivedTToCanonicalPulledGeometryIsoAt_hom_fac
      input Q k g endpoint_eq square_isPullback]
    rw [← Category.assoc, ← Functor.map_comp, htargetInv]
  have htransport :
      (semanticDerivedBToCanonicalBaseNorthwestIsoAt
          input Q k g endpoint_eq square_isPullback).hom.1 ≫
        (geomFiberTransportMap sigma
          (semanticDerivedCanonicalMateInMixedFiberAt input Q k g endpoint_eq)).1 ≫
        inv pulledLift =
      (semanticDerivedBToCanonicalBaseGeometryIsoAt
        input Q k g endpoint_eq square_isPullback).hom ≫
        (semanticDerivedCanonicalMateInMixedFiberAt input Q k g endpoint_eq).1 := by
    rw [semanticDerivedBToCanonicalBaseNorthwestIsoAt_hom]
    have hfac := geomFiberTransportMap_fac sigma
      (semanticDerivedCanonicalMateInMixedFiberAt input Q k g endpoint_eq)
    calc
      ((semanticDerivedBToCanonicalBaseGeometryIsoAt
          input Q k g endpoint_eq square_isPullback).hom ≫
          geomFiberLift sigma
            (semanticDerivedCanonicalBaseRouteFiberAt input Q k g endpoint_eq)) ≫
          (geomFiberTransportMap sigma
            (semanticDerivedCanonicalMateInMixedFiberAt input Q k g endpoint_eq)).1 ≫
          inv pulledLift =
        (semanticDerivedBToCanonicalBaseGeometryIsoAt
          input Q k g endpoint_eq square_isPullback).hom ≫
          ((geomFiberLift sigma
              (semanticDerivedCanonicalBaseRouteFiberAt input Q k g endpoint_eq) ≫
            (geomFiberTransportMap sigma
              (semanticDerivedCanonicalMateInMixedFiberAt input Q k g endpoint_eq)).1) ≫
            inv pulledLift) := by simp only [Category.assoc]
      _ = (semanticDerivedBToCanonicalBaseGeometryIsoAt
          input Q k g endpoint_eq square_isPullback).hom ≫
          (((semanticDerivedCanonicalMateInMixedFiberAt input Q k g endpoint_eq).1 ≫
            geomFiberLift sigma pulledFiber) ≫ inv pulledLift) := by
          rw [hfac]
      _ = (semanticDerivedBToCanonicalBaseGeometryIsoAt
          input Q k g endpoint_eq square_isPullback).hom ≫
          (semanticDerivedCanonicalMateInMixedFiberAt input Q k g endpoint_eq).1 := by
          dsimp only [pulledLift]
          simp only [Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  rw [semanticDerivedGeneratedMateOnLiteralEndpoints_decomposition]
  apply (exactGeometryToRefinementGeometry U).map_injective
  simp only [Functor.map_comp]
  change (exactGeometryToRefinementGeometry U).map
      ((semanticDerivedBToCanonicalBaseNorthwestIsoAt
          input Q k g endpoint_eq square_isPullback).hom.1 ≫
        (geomFiberTransportMap sigma
          (semanticDerivedCanonicalMateInMixedFiberAt input Q k g endpoint_eq)).1 ≫
        (semanticDerivedTToCanonicalPulledNorthwestIsoAt
          input Q k g endpoint_eq square_isPullback).inv.1) ≫
      (exactGeometryToRefinementGeometry U).map
        (semanticDerivedDirectPulledRouteLegAt input Q k g endpoint_eq) = _
  simp only [Functor.map_comp, Category.assoc]
  rw [htarget]
  have htransportMapped := congrArg
    (fun f => (exactGeometryToRefinementGeometry U).map f) htransport
  simp only [Functor.map_comp] at htransportMapped
  calc
    _ = ((exactGeometryToRefinementGeometry U).map
          (semanticDerivedBToCanonicalBaseGeometryIsoAt
            input Q k g endpoint_eq square_isPullback).hom ≫
        (exactGeometryToRefinementGeometry U).map
          (semanticDerivedCanonicalMateInMixedFiberAt input Q k g endpoint_eq).1) ≫
        problem.canonicalAuthoredPulledRouteGeometryHomAt PUnit.unit := by
      rw [← htransportMapped]
      simp only [Category.assoc]
    _ = _ := by
      rw [semanticDerivedCanonicalMateInMixedFiberAt_toRefinement]
      rw [← problem.canonicalAuthoredUpperGeometryMateAt_toRefinement]
      simp only [Category.assoc]
      have htriangle := problem.canonicalAuthoredUpperGeometryMateAt_triangle
        PUnit.unit
      change (exactGeometryToRefinementGeometry U).map
          (problem.canonicalAuthoredUpperGeometryMateAt PUnit.unit) ≫
        problem.canonicalAuthoredPulledRouteGeometryHomAt PUnit.unit =
          problem.canonicalAuthoredBaseRouteGeometryHomAt PUnit.unit at htriangle
      rw [htriangle]
      exact semanticDerivedBToCanonicalBaseGeometryIsoAt_hom_fac
        input Q k g endpoint_eq square_isPullback

/-- Cartesian uniqueness identifies the literal semantic mate with the
transported actual G-118 generated mate. -/
theorem semanticDerivedGeneratedMateOnLiteralEndpoints_eq_literal
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U) (Q : AATCorePackage U)
    (k : Type v) [CommRing k] (g : FixedCoefficientGeometryAt Q k)
    (endpoint_eq : packagePoint Q = input.square.southwest)
    (square_isPullback : IsPullback input.square.left input.square.top
      input.square.bottom input.square.right) :
    semanticDerivedGeneratedMateOnLiteralEndpointsIsoAt
      input Q k g endpoint_eq square_isPullback =
    semanticDerivedLiteralMateNorthwestIsoAt input Q k g endpoint_eq := by
  apply Iso.ext
  apply CategoryTheory.Functor.Fiber.hom_ext
  let pulledLeg := semanticDerivedDirectPulledRouteLegAt input Q k g endpoint_eq
  letI hpulled : (crossStageProjection U).IsStronglyCartesian
      ((crossStageProjection U).map pulledLeg) pulledLeg := by
    let first := semanticGeometryPullLift input.square.top
      (semanticDerivedViaBaseGeometryAt input Q k g endpoint_eq)
    let second := semanticGeometryPullLift input.square.right
      (semanticDerivedTargetGeometryAt input Q k g endpoint_eq)
    letI hfirst : (crossStageProjection U).IsStronglyCartesian
        first.base.base first := by
      simpa [first] using semanticGeometryPullLift_crossStageStronglyCartesian_map
        input.square.top
        (semanticDerivedViaBaseGeometryAt input Q k g endpoint_eq)
    letI hsecond : (crossStageProjection U).IsStronglyCartesian
        second.base.base second := by
      simpa [second] using semanticGeometryPullLift_crossStageStronglyCartesian_map
        input.square.right
        (semanticDerivedTargetGeometryAt input Q k g endpoint_eq)
    simpa [pulledLeg, semanticDerivedDirectPulledRouteLegAt,
      first, second, Functor.map_comp] using
      CategoryTheory.Functor.IsStronglyCartesian.comp
        (crossStageProjection U)
  apply CategoryTheory.Functor.IsStronglyCartesian.ext
    (crossStageProjection U) ((crossStageProjection U).map pulledLeg) pulledLeg
    (𝟙 input.square.northwest)
  change (semanticDerivedGeneratedMateOnLiteralEndpointsIsoAt
      input Q k g endpoint_eq square_isPullback).hom.1 ≫ pulledLeg =
    (semanticDerivedLiteralMateNorthwestIsoAt input Q k g endpoint_eq).hom.1 ≫
      pulledLeg
  rw [semanticDerivedGeneratedMateOnLiteralEndpoints_triangle
    input Q k g endpoint_eq square_isPullback]
  exact (semanticDerivedLiteralMateNorthwestIsoAt_hom_fac
    input Q k g endpoint_eq).symm

/-- The semantic complete-geometry comparison is the unit, source endpoint
comparison, actual G-118 generated mate, target endpoint comparison, counit
composite. -/
theorem semanticDerivedBarAlphaIsoAt_generatedFiveFactor_hom
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U) (Q : AATCorePackage U)
    (k : Type v) [CommRing k] (g : FixedCoefficientGeometryAt Q k)
    (endpoint_eq : packagePoint Q = input.square.southwest)
    (square_isPullback : IsPullback input.square.left input.square.top
      input.square.bottom input.square.right) :
    (semanticDerivedBarAlphaIsoAt input Q k g endpoint_eq square_isPullback).hom =
      (semanticDerivedUnitTopPushIsoAt input Q k g endpoint_eq).hom ≫
      (geomFiberTransportFunctor input.square.top).map
        (semanticDerivedBToGeneratedBaseNorthwestIsoAt
          input Q k g endpoint_eq square_isPullback).hom ≫
      semanticDerivedGeneratedMateTopPushAt
        input Q k g endpoint_eq square_isPullback ≫
      (geomFiberTransportFunctor input.square.top).map
        (semanticDerivedGeneratedPulledToTNorthwestIsoAt
          input Q k g endpoint_eq square_isPullback).hom ≫
      (semanticDerivedTopCounitIsoAt input Q k g endpoint_eq).hom := by
  rw [semanticDerivedBarAlphaIsoAt_hom,
    ← semanticDerivedGeneratedMateOnLiteralEndpoints_eq_literal
      input Q k g endpoint_eq square_isPullback]
  simp only [semanticDerivedGeneratedMateOnLiteralEndpointsIsoAt,
    semanticDerivedGeneratedMateTopPushAt, Iso.trans_hom, Functor.map_comp,
    Category.assoc]
  rfl

end AAT.AG.FullGeometryNormalization

#assert_standard_axioms_only AAT.AG.FullGeometryNormalization
