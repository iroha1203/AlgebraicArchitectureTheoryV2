import ResearchLean.AG.FullGeometryNormalization.ExactDerivedRouteLowerCoherence

/-!
# Exact-image coherence for the exact-derived pulled route

The canonical-authored pulled route is built in the refinement geometry
category, whereas the literal G-122 pulled-first route is an exact complete
geometry morphism.  On the exact-derived configuration, the pulled
refinement is itself the image of the realization-derived exact comparison.
The theorem below keeps both endpoint casts explicit and identifies the full
pointed refinement maps, not only their source or atom functions separately.

## Implementation notes

The proof separates the pullback commutative square from endpoint casts and
then maps the resulting exact equality into refinements.  A single global
unfolding was rejected because typeclass normalization of the dependent route
is unstable and obscures the provenance of the pullback comparison.
-/

namespace AAT.AG.FullGeometryNormalization

universe u v

open CategoryTheory AtomFoundation GeometryTransport CrossStageCoherence
open DoctrineFiberProduct

set_option maxHeartbeats 3000000

/-- An endpoint equality within one doctrine induces the identity doctrine
homomorphism, while retaining the required pointed source cast. -/
private theorem eqToHom_doctrineHom_sameDoctrine
    {U : AtomCarrier.{u}} (D : ExtractionDoctrine U)
    (x y : D.Source)
    (h : (ExtractionInstance.mk D x : ExtractionInstance U) =
      ExtractionInstance.mk D y) :
    (eqToHom h : ExtInstHom (ExtractionInstance.mk D x)
      (ExtractionInstance.mk D y)).doctrineHom = ExactDoctrineHom.id D := by
  cases h
  rfl

/-- The constructor presentation of an exact refinement arrow agrees with the
canonical exact-to-refinement functor on morphisms. -/
private theorem ofExact_eq_exactPointedToRefinement_map
    {U : AtomCarrier.{u}} {X Y : ExtractionInstance U} (f : X ⟶ Y) :
    PointedRefinementHom.ofExact f = (exactPointedToRefinement U).map f := by
  rfl

/-- The pointed pullback square commutes after inserting the authored target
and northeast endpoint identifications. -/
private theorem authoredExactPullbackTarget_fst_eq_snd_right
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) :
    (authoredExactPointedRefinementBCConfiguration A).pullbackFst ≫
        eqToHom (authoredExactRefinementBCTargetPoint_eq A) =
      pointedPullbackSnd
          (authoredExactPointedRefinementBCConfiguration A).sigmaOne
          (authoredExactPointedRefinementBCConfiguration A).sigmaTwo ≫
        eqToHom (authoredExactRefinementBCSecondPoint_eq A) ≫
        A.context.square.semantic.square.right := by
  let C := authoredExactRefinementBCConfiguration A
  let p := authoredExactRefinementBCCompatibleSource A
  have hcommutes := pointedPullback_commutes (C.fstAt p) (C.sndAt p)
  have hdoctrine := congrArg (fun hom => hom.doctrineHom) hcommutes
  have hsecond :
      (eqToHom (authoredExactRefinementBCSecondPoint_eq A)).doctrineHom =
        ExactDoctrineHom.id A.context.square.semantic.square.northeast.doctrine := by
    simpa [C, p, authoredExactRefinementBCConfiguration,
      authoredExactRefinementBCCompatibleSource,
      RefinementBCConfiguration.secondPointAt] using
      eqToHom_doctrineHom_sameDoctrine
        A.context.square.semantic.square.northeast.doctrine
        (authoredExactRefinementBCCompatibleSource A).sourceTwo
        A.context.square.semantic.square.northeast.source
        (authoredExactRefinementBCSecondPoint_eq A)
  have htarget :
      (eqToHom (authoredExactRefinementBCTargetPoint_eq A)).doctrineHom =
        ExactDoctrineHom.id A.context.square.semantic.square.southeast.doctrine := by
    simpa [C, p, authoredExactRefinementBCConfiguration,
      authoredExactRefinementBCCompatibleSource,
      RefinementBCConfiguration.targetPointAt,
      RefinementBCConfiguration.sourceOneAt] using
      eqToHom_doctrineHom_sameDoctrine
        A.context.square.semantic.square.southeast.doctrine
        (A.context.square.semantic.square.bottom.doctrineHom.sourceMap
          A.context.square.semantic.compatiblePoints.southwest)
        A.context.square.semantic.square.southeast.source
        (authoredExactRefinementBCTargetPoint_eq A)
  apply ExtInstHom.ext
  change
    (authoredExactPointedRefinementBCConfiguration A).pullbackFst.doctrineHom.comp
        (eqToHom (authoredExactRefinementBCTargetPoint_eq A)).doctrineHom =
      (pointedPullbackSnd
          (authoredExactPointedRefinementBCConfiguration A).sigmaOne
          (authoredExactPointedRefinementBCConfiguration A).sigmaTwo).doctrineHom.comp
        ((eqToHom (authoredExactRefinementBCSecondPoint_eq A)).doctrineHom.comp
          A.context.square.semantic.square.right.doctrineHom)
  rw [hsecond, htarget]
  simpa [C, p, authoredExactPointedRefinementBCConfiguration,
    authoredExactRefinementBCConfiguration,
    authoredExactRefinementBCCompatibleSource,
    RefinementBCConfiguration.pointedConfigurationAt,
    RefinementBCConfiguration.fstAt,
    RefinementBCConfiguration.sndAt] using hdoctrine

/-- After the realization-derived source identification, the lower map of the
canonical-authored pulled route is exactly the refinement image of the literal
two-edge exact pulled route.  The equality uses the exact-image theorem for
`pulledRefinementAt` and the realized comparison square; no endpoint or
factorization certificate is supplied by the caller. -/
theorem authoredExactCanonicalPulledRoute_base_eq_direct
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    (exactPointedToRefinement U).map
          (authoredExactDirectToCanonicalPulledSourcePointIsoAt A z k g).hom ≫
        ((authoredExactCompatibleProblemDataAt A z k g).canonicalAuthoredPulledRouteGeometryHomAt
          PUnit.unit).base.base =
      (exactPointedToRefinement U).map
        ((crossStageProjection.{u, v} U).map
          (authoredExactDirectPulledRouteLegAt A z k g)) := by
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
            (authoredExactDirectPulledRouteLegAt A z k g)) =
        (exactPointedToRefinement U).map
          (eqToHom (authoredExactGeneratedMateTargetGeometryAt A z k g).2 ≫
            A.context.square.semantic.square.top ≫
            A.context.square.semantic.square.right ≫
            eqToHom (authoredExactTargetGeometryAt A z k g).2.symm) := by
    unfold authoredExactDirectPulledRouteLegAt
    rw [Functor.map_comp,
      exactGeometryPullLift_crossStageProjection,
      exactGeometryPullLift_crossStageProjection]
    simp [exactGeometryPullBaseHom, authoredExactTopInput,
      authoredExactRightInput]
  rw [hright]
  simp only [ActiveRefinementBCContext.retarget,
    authoredExactRefinementBCContextAt,
    activeRefinementBCContextOfCondition,
    authoredExactCompatibleProblemDataAt,
    authoredExactSourceFiberDiagramAt]
  simp only [← pulledRefinementAt_mem_exactComparisonImage
    (authoredExactRefinementBCConfiguration A)
    (authoredExactRefinementBCCompatibleSource A)
    (authoredExactRefinementBC_exactImage A)]
  have hlower := authoredExactDirectPulledRoute_lower_fac A z k g
  rw [authoredExactPullbackTargetIso_hom] at hlower
  unfold authoredExactTargetSnd at hlower
  have htail := authoredExactPullbackTarget_fst_eq_snd_right A
  simp only [Category.assoc] at htail hlower
  rw [← htail] at hlower
  have hlower' := congrArg
    (fun hom => hom ≫ eqToHom (authoredExactTargetGeometryAt A z k g).2.symm)
    hlower
  simp only [Category.assoc, eqToHom_refl, Category.id_comp] at hlower'
  have h := congrArg (fun hom => (exactPointedToRefinement U).map hom) hlower'
  change (exactPointedToRefinement U).map
      (authoredExactDirectToCanonicalPulledSourcePointIsoAt A z k g).hom ≫
        (_ ≫ _) = _
  simp only [Functor.map_comp,
    exactPointedToRefinement_map_eqToHom,
    eqToHom_refl,
    authoredExactPulledComparison,
    UpperGeometryCleavage.pullbackTargetGeometryHom,
    UpperGeometryCleavage.generatedExactGeometryHom,
    UpperGeometryCleavage.pullbackTargetExactArrow,
    UpperGeometryCleavage.exactBaseHom,
    exactGeometryToRefinementGeometry,
    exactPackageToRefinement,
    inverseCorePackageHom,
    authoredExactTargetPackageAt,
    RefinementBCConfiguration.targetPointAt,
    ofExact_eq_exactPointedToRefinement_map] at h ⊢
  simpa using h

end AAT.AG.FullGeometryNormalization

#assert_standard_axioms_only AAT.AG.FullGeometryNormalization
