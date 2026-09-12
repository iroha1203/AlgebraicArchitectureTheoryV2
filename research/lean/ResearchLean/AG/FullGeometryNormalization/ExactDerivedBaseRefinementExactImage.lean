import ResearchLean.AG.FullGeometryNormalization.ExactDerivedRouteLowerCoherence

/-!
# Exact image of the exact-derived base refinement route

This layer identifies the complete lower refinement carried by the G-118
canonical-authored base route with the refinement image of the original exact
two-edge base route.  The source endpoint cast is the comparison generated
from pullback realization and fiber incidence; no route equality certificate
is accepted from the caller.

## Implementation notes

The base refinement is first represented by the original exact bottom arrow
with explicit endpoint casts.  Rewriting inside the dependent refinement
configuration was rejected because it changes the type of the pullback leg;
the proof instead normalizes the standalone exact arrow before mapping it.
-/

namespace AAT.AG.FullGeometryNormalization

universe u v

open CategoryTheory AtomFoundation GeometryTransport CrossStageCoherence
open DoctrineFiberProduct

set_option maxHeartbeats 3000000

/-- An equality cast between two sources of one doctrine has identity doctrine
component; this isolates proof-dependent endpoint casts from route algebra. -/
@[simp] private theorem eqToHom_doctrineHom_sameDoctrine
    {U : AtomCarrier.{u}} (D : ExtractionDoctrine U)
    (x y : D.Source)
    (h : (ExtractionInstance.mk D x : ExtractionInstance U) =
      ExtractionInstance.mk D y) :
    (eqToHom h : ExtInstHom (ExtractionInstance.mk D x)
      (ExtractionInstance.mk D y)).doctrineHom = ExactDoctrineHom.id D := by
  cases h
  rfl

/-- The original exact bottom doctrine morphism, canonically repointed at the
source and target selected by the exact-derived refinement configuration. -/
def authoredExactBaseRefinementExactArrow
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) :
    (authoredExactRefinementBCConfiguration A).sourcePointAt
        (authoredExactRefinementBCCompatibleSource A) ⟶
      (authoredExactRefinementBCConfiguration A).targetPointAt
        (authoredExactRefinementBCCompatibleSource A) where
  doctrineHom := A.context.square.semantic.square.bottom.doctrineHom
  source_eq := rfl

/-- The exact-derived base refinement is literally the refinement image of
the canonically repointed original exact bottom edge. -/
theorem authoredExactBaseRefinement_exactImage
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) :
    (authoredExactRefinementBCConfiguration A).baseRefinementAt
        (authoredExactRefinementBCCompatibleSource A) =
      (exactPointedToRefinement U).map
        (authoredExactBaseRefinementExactArrow A) := by
  apply PointedRefinementHom.ext
  apply RefinementDoctrineHom.ext
  · funext source
    rfl
  · funext atom
    rfl

/-- Repointing the original bottom edge agrees with inserting the two derived
endpoint identifications around that edge. -/
theorem authoredExactBaseRefinementExactArrow_eq_endpointCasts
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) :
    authoredExactBaseRefinementExactArrow A =
      eqToHom (authoredExactRefinementBCSourcePoint_eq A) ≫
        A.context.square.semantic.square.bottom ≫
        eqToHom (authoredExactRefinementBCTargetPoint_eq A).symm := by
  have hsource :
      (eqToHom (authoredExactRefinementBCSourcePoint_eq A)).doctrineHom =
        ExactDoctrineHom.id A.context.square.semantic.square.southwest.doctrine := by
    simpa [authoredExactRefinementBCConfiguration,
      authoredExactRefinementBCCompatibleSource,
      RefinementBCConfiguration.sourcePointAt] using
      eqToHom_doctrineHom_sameDoctrine
        A.context.square.semantic.square.southwest.doctrine
        A.context.square.semantic.compatiblePoints.southwest
        A.context.square.semantic.square.southwest.source
        (authoredExactRefinementBCSourcePoint_eq A)
  have htarget :
      (eqToHom (authoredExactRefinementBCTargetPoint_eq A).symm).doctrineHom =
        ExactDoctrineHom.id A.context.square.semantic.square.southeast.doctrine := by
    simpa [authoredExactRefinementBCConfiguration,
      authoredExactRefinementBCCompatibleSource,
      RefinementBCConfiguration.targetPointAt,
      RefinementBCConfiguration.sourceOneAt] using
      eqToHom_doctrineHom_sameDoctrine
        A.context.square.semantic.square.southeast.doctrine
        A.context.square.semantic.square.southeast.source
        (A.context.square.semantic.square.bottom.doctrineHom.sourceMap
          A.context.square.semantic.compatiblePoints.southwest)
        (authoredExactRefinementBCTargetPoint_eq A).symm
  apply ExtInstHom.ext
  change A.context.square.semantic.square.bottom.doctrineHom =
    (eqToHom (authoredExactRefinementBCSourcePoint_eq A)).doctrineHom.comp
      (A.context.square.semantic.square.bottom.doctrineHom.comp
        (eqToHom (authoredExactRefinementBCTargetPoint_eq A).symm).doctrineHom)
  rw [hsource, htarget]
  apply ExactDoctrineHom.ext
  · funext source
    rfl
  · apply Equiv.ext
    intro atom
    rfl

/-- After inserting the realization-generated source-point comparison, the
lower hom of the canonical-authored base route is exactly the refinement image
of the literal two-edge exact base route. -/
theorem authoredExactCanonicalBaseRoute_refinementExactImage
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    (exactPointedToRefinement U).map
          (authoredExactDirectToCanonicalBaseSourcePointIsoAt A z k g).hom ≫
        (((authoredExactCompatibleProblemDataAt A z k g).canonicalAuthoredBaseRouteGeometryHomAt
            PUnit.unit).base.base) =
      (exactPointedToRefinement U).map
        ((crossStageProjection U).map
          (authoredExactDirectBaseRouteLegAt A z k g)) := by
  rw [UpperGeometryCompatibleProblemInputData.canonicalAuthoredBaseRouteGeometryHomAt_base]
  unfold UpperGeometryCompatibleProblemInputData.generatedBaseRouteLegAt
  unfold UpperGeometryCleavage.baseRouteGeometryHom
  change PointedRefinementHom.comp _
      (PointedRefinementHom.comp
        ((exactGeometryToRefinementGeometry U).map _).base.base
        (UpperGeometryCleavage.refinementBaseHom _ _ _ _).base) = _
  rw [UpperGeometryCleavage.refinementBaseHom_base_eq_casts]
  simp only [ActiveRefinementBCContext.retarget,
    authoredExactRefinementBCContextAt,
    activeRefinementBCContextOfCondition,
    authoredExactCompatibleProblemDataAt,
    authoredExactSourceFiberDiagramAt]
  conv_lhs =>
    rhs
    rhs
    rhs
    lhs
    rw [authoredExactBaseRefinement_exactImage]
  rw [authoredExactBaseRefinementExactArrow_eq_endpointCasts]
  simp only [Functor.map_comp, exactPointedToRefinement_map_eqToHom,
    Category.assoc, eqToHom_refl]
  have hright :
      (exactPointedToRefinement U).map
          ((crossStageProjection U).map
            (authoredExactDirectBaseRouteLegAt A z k g)) =
        (exactPointedToRefinement U).map
          (eqToHom (authoredExactGeneratedMateSourceGeometryAt A z k g).2 ≫
            A.context.square.semantic.square.left ≫
            A.context.square.semantic.square.bottom ≫
            eqToHom (authoredExactTargetGeometryAt A z k g).2.symm) := by
    unfold authoredExactDirectBaseRouteLegAt
    rw [Functor.map_comp,
      exactGeometryPullLift_crossStageProjection,
      exactGeometryPullLift_crossStageProjection]
    simp [exactGeometryPullBaseHom, authoredExactLeftInput,
      authoredExactBottomInput]
  rw [hright]
  have hlower := authoredExactDirectBaseRoute_lower_fac A z k g
  have hlower' := congrArg
    (fun hom => hom ≫ eqToHom (authoredExactTargetGeometryAt A z k g).2.symm)
    hlower
  simp only [Category.assoc, eqToHom_refl, Category.id_comp] at hlower'
  have h := congrArg (fun hom => (exactPointedToRefinement U).map hom) hlower'
  change (exactPointedToRefinement U).map
      (authoredExactDirectToCanonicalBaseSourcePointIsoAt A z k g).hom ≫
        (_ ≫ _) = _
  simp only [Functor.map_comp,
    exactPointedToRefinement_map_eqToHom,
    eqToHom_refl,
    authoredExactMixedFst,
    UpperGeometryCleavage.baseRouteExactGeometryHom,
    UpperGeometryCleavage.generatedExactGeometryHom,
    UpperGeometryCleavage.baseRouteExactArrow,
    UpperGeometryCleavage.exactBaseHom,
    exactGeometryToRefinementGeometry,
    exactPackageToRefinement,
    inverseCorePackageHom] at h ⊢
  simpa using h

end AAT.AG.FullGeometryNormalization

#assert_standard_axioms_only AAT.AG.FullGeometryNormalization
