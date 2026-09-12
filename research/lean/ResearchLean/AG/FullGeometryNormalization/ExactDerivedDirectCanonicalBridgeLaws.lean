import ResearchLean.AG.FullGeometryNormalization.ExactDerivedDirectCanonicalBridge

/-!
# Factor and coefficient laws for the exact-derived endpoint bridges

The direct-to-canonical endpoint isomorphisms were constructed by two stages
of Cartesian uniqueness.  This module exposes the factor equation which that
construction already satisfies and derives coefficient identity from it.
The final northwest-fiber bridge inherits the same identity after composing
with the canonical cocartesian transport lift.

## Implementation notes

The proof replays only the universal-property `fac` equations at the geometry
and package projections.  It does not reconstruct a comparison morphism or
accept a coefficient equation from the caller.  The last base equation is the
exact-image theorem proved for the literal authored route.
-/

namespace AAT.AG.FullGeometryNormalization

universe u v

open CategoryTheory AtomFoundation GeometryTransport CrossStageCoherence
open DoctrineFiberProduct

set_option maxHeartbeats 3000000

/-- Exactifying an isomorphism and re-embedding its forward map recovers the
original refinement-geometry isomorphism. -/
theorem exactGeometryIsoOfRefinementIso_hom_toRefinement
    {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
    (baseIso :
      (show PackageTotalCategory U from G.core) ≅
        (show PackageTotalCategory U from H.core))
    (refinementIso : RefinementGeometryObject.mk G ≅
      RefinementGeometryObject.mk H)
    (hbase : refinementIso.hom.base =
      (exactPackageToRefinement U).map baseIso.hom) :
    (exactGeometryToRefinementGeometry U).map
        (UpperGeometryCleavage.exactGeometryIsoOfRefinementIso
          baseIso refinementIso hbase).hom = refinementIso.hom := by
  exact UpperGeometryCleavage.exactGeometryHomOfRefinement_toRefinement _ _ _

/-- The embedded literal base-first route remains strongly Cartesian at the
complete refinement-geometry projection. -/
private theorem directBaseRouteGeometry_isStronglyCartesian
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    (refinementGeometryProjection U).IsStronglyCartesian
      (((exactGeometryToRefinementGeometry U).map
        (authoredExactDirectBaseRouteLegAt A z k g)).base)
      ((exactGeometryToRefinementGeometry U).map
        (authoredExactDirectBaseRouteLegAt A z k g)) := by
  let first := exactGeometryPullLift (authoredExactLeftInput A)
    (authoredExactBottomPulledTargetGeometryAt A z k g)
  let second := exactGeometryPullLift (authoredExactBottomInput A)
    (authoredExactTargetGeometryAt A z k g)
  letI hfirst : (refinementGeometryProjection U).IsStronglyCartesian
      (((exactGeometryToRefinementGeometry U).map first).base)
      ((exactGeometryToRefinementGeometry U).map first) := by
    simpa [first] using exactGeometryPullLift_refinementStronglyCartesian
      (authoredExactLeftInput A)
      (authoredExactBottomPulledTargetGeometryAt A z k g)
  letI hsecond : (refinementGeometryProjection U).IsStronglyCartesian
      (((exactGeometryToRefinementGeometry U).map second).base)
      ((exactGeometryToRefinementGeometry U).map second) := by
    simpa [second] using exactGeometryPullLift_refinementStronglyCartesian
      (authoredExactBottomInput A) (authoredExactTargetGeometryAt A z k g)
  simpa [authoredExactDirectBaseRouteLegAt, first, second, Functor.map_comp]
    using CategoryTheory.Functor.IsStronglyCartesian.comp
      (refinementGeometryProjection U)

/-- The forward exact base comparison factors the canonical-authored route
leg to the literal two-pull route leg. -/
theorem authoredExactDirectToCanonicalBaseGeometryIsoAt_hom_fac
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    (exactGeometryToRefinementGeometry U).map
        (authoredExactDirectToCanonicalBaseGeometryIsoAt A z k g).hom ≫
      (authoredExactCompatibleProblemDataAt A z k g).canonicalAuthoredBaseRouteGeometryHomAt
        PUnit.unit =
      (exactGeometryToRefinementGeometry U).map
        (authoredExactDirectBaseRouteLegAt A z k g) := by
  unfold authoredExactDirectToCanonicalBaseGeometryIsoAt
  letI := directBaseRouteGeometry_isStronglyCartesian A z k g
  letI : (refinementGeometryProjection U).IsStronglyCartesian
      ((authoredExactCompatibleProblemDataAt A z k g).canonicalAuthoredBaseRouteGeometryHomAt
        PUnit.unit).base
      ((authoredExactCompatibleProblemDataAt A z k g).canonicalAuthoredBaseRouteGeometryHomAt
        PUnit.unit) := by
    apply UpperGeometryCompatibleProblemInputData.canonicalAuthoredBaseRouteGeometryHomAt_isStronglyCartesian
  letI : (refinementPackageProjection U).IsStronglyCartesian
      ((authoredExactCompatibleProblemDataAt A z k g).canonicalAuthoredBaseRouteGeometryHomAt
        PUnit.unit).base.base
      ((authoredExactCompatibleProblemDataAt A z k g).canonicalAuthoredBaseRouteGeometryHomAt
        PUnit.unit).base := by
    simpa using UpperGeometryCleavage.baseRouteGeometryBase_isStronglyCartesian
      (authoredExactRefinementBCContextAt A z k g)
      ((authoredExactCompatibleProblemDataAt A z k g).sourceTargetGeometryAt PUnit.unit)
  letI : (refinementPackageProjection U).IsHomLift
      ((exactGeometryToRefinementGeometry U).map
        (authoredExactDirectBaseRouteLegAt A z k g)).base.base
      ((exactGeometryToRefinementGeometry U).map
        (authoredExactDirectBaseRouteLegAt A z k g)).base :=
    UpperGeometryCleavage.refinementPackageHom_isHomLift_of_base_eq _ _ rfl
  letI := UpperGeometryCleavage.refinementGeometryHom_isHomLift
    ((exactGeometryToRefinementGeometry U).map
      (authoredExactDirectBaseRouteLegAt A z k g))
  dsimp only
  rw [exactGeometryIsoOfRefinementIso_hom_toRefinement]
  apply CategoryTheory.Functor.IsStronglyCartesian.fac
    (p := refinementGeometryProjection U)
    (f := ((authoredExactCompatibleProblemDataAt A z k g).canonicalAuthoredBaseRouteGeometryHomAt
      PUnit.unit).base)
    (φ := (authoredExactCompatibleProblemDataAt A z k g).canonicalAuthoredBaseRouteGeometryHomAt
      PUnit.unit)
    (f' := ((exactGeometryToRefinementGeometry U).map
      (authoredExactDirectBaseRouteLegAt A z k g)).base)
  symm
  apply CategoryTheory.Functor.IsStronglyCartesian.fac
    (p := refinementPackageProjection U)
    (f := ((authoredExactCompatibleProblemDataAt A z k g).canonicalAuthoredBaseRouteGeometryHomAt
      PUnit.unit).base.base)
    (φ := ((authoredExactCompatibleProblemDataAt A z k g).canonicalAuthoredBaseRouteGeometryHomAt
      PUnit.unit).base)
    (f' := ((exactGeometryToRefinementGeometry U).map
      (authoredExactDirectBaseRouteLegAt A z k g)).base.base)
  simpa [UpperGeometryCompatibleProblemInputData.canonicalAuthoredBaseRouteGeometryHomAt_base]
    using (authoredExactCanonicalBaseRoute_refinementExactImage A z k g).symm

/-- The forward exact base comparison fixes the authored coefficient ring. -/
theorem authoredExactDirectToCanonicalBaseGeometryIsoAt_hom_coefficient_id
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    (authoredExactDirectToCanonicalBaseGeometryIsoAt A z k g).hom.geometry.coefficientHom =
      RingHom.id k := by
  have h := congrArg (fun hom => hom.geometry.coefficientHom)
    (authoredExactDirectToCanonicalBaseGeometryIsoAt_hom_fac A z k g)
  change
    ((authoredExactCompatibleProblemDataAt A z k g).canonicalAuthoredBaseRouteGeometryHomAt
        PUnit.unit).geometry.coefficientHom.comp
      (authoredExactDirectToCanonicalBaseGeometryIsoAt A z k g).hom.geometry.coefficientHom =
    (authoredExactDirectBaseRouteLegAt A z k g).geometry.coefficientHom at h
  rw [UpperGeometryCompatibleProblemInputData.canonicalAuthoredBaseRouteGeometryHomAt_coefficientHom] at h
  simpa [authoredExactDirectBaseRouteLegAt, GeometryTotalHom.comp,
    GeomReadHom.comp] using h

/-- The embedded literal pulled-first route remains strongly Cartesian at the
complete refinement-geometry projection. -/
private theorem directPulledRouteGeometry_isStronglyCartesian
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    (refinementGeometryProjection U).IsStronglyCartesian
      (((exactGeometryToRefinementGeometry U).map
        (authoredExactDirectPulledRouteLegAt A z k g)).base)
      ((exactGeometryToRefinementGeometry U).map
        (authoredExactDirectPulledRouteLegAt A z k g)) := by
  let first := exactGeometryPullLift (authoredExactTopInput A)
    (authoredExactViaBaseGeometryAt A z k g)
  let second := exactGeometryPullLift (authoredExactRightInput A)
    (authoredExactTargetGeometryAt A z k g)
  letI hfirst : (refinementGeometryProjection U).IsStronglyCartesian
      (((exactGeometryToRefinementGeometry U).map first).base)
      ((exactGeometryToRefinementGeometry U).map first) := by
    simpa [first] using exactGeometryPullLift_refinementStronglyCartesian
      (authoredExactTopInput A) (authoredExactViaBaseGeometryAt A z k g)
  letI hsecond : (refinementGeometryProjection U).IsStronglyCartesian
      (((exactGeometryToRefinementGeometry U).map second).base)
      ((exactGeometryToRefinementGeometry U).map second) := by
    simpa [second] using exactGeometryPullLift_refinementStronglyCartesian
      (authoredExactRightInput A) (authoredExactTargetGeometryAt A z k g)
  simpa [authoredExactDirectPulledRouteLegAt, first, second, Functor.map_comp]
    using CategoryTheory.Functor.IsStronglyCartesian.comp
      (refinementGeometryProjection U)

/-- The forward exact pulled comparison factors the canonical-authored route
leg to the literal two-pull route leg. -/
theorem authoredExactDirectToCanonicalPulledGeometryIsoAt_hom_fac
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    (exactGeometryToRefinementGeometry U).map
        (authoredExactDirectToCanonicalPulledGeometryIsoAt A z k g).hom ≫
      (authoredExactCompatibleProblemDataAt A z k g).canonicalAuthoredPulledRouteGeometryHomAt
        PUnit.unit =
      (exactGeometryToRefinementGeometry U).map
        (authoredExactDirectPulledRouteLegAt A z k g) := by
  unfold authoredExactDirectToCanonicalPulledGeometryIsoAt
  letI := directPulledRouteGeometry_isStronglyCartesian A z k g
  letI : (refinementGeometryProjection U).IsStronglyCartesian
      ((authoredExactCompatibleProblemDataAt A z k g).canonicalAuthoredPulledRouteGeometryHomAt
        PUnit.unit).base
      ((authoredExactCompatibleProblemDataAt A z k g).canonicalAuthoredPulledRouteGeometryHomAt
        PUnit.unit) := by
    let input := authoredExactCompatibleProblemDataAt A z k g
    simpa [input] using
      input.canonicalAuthoredPulledRouteGeometryHomAt_isStronglyCartesian PUnit.unit
  letI : (refinementPackageProjection U).IsStronglyCartesian
      ((authoredExactCompatibleProblemDataAt A z k g).canonicalAuthoredPulledRouteGeometryHomAt
        PUnit.unit).base.base
      ((authoredExactCompatibleProblemDataAt A z k g).canonicalAuthoredPulledRouteGeometryHomAt
        PUnit.unit).base := by
    simpa using UpperGeometryCleavage.pulledRouteGeometryBase_isStronglyCartesian
      (authoredExactRefinementBCContextAt A z k g)
      ((authoredExactCompatibleProblemDataAt A z k g).sourceTargetGeometryAt PUnit.unit)
  letI : (refinementPackageProjection U).IsHomLift
      ((exactGeometryToRefinementGeometry U).map
        (authoredExactDirectPulledRouteLegAt A z k g)).base.base
      ((exactGeometryToRefinementGeometry U).map
        (authoredExactDirectPulledRouteLegAt A z k g)).base :=
    UpperGeometryCleavage.refinementPackageHom_isHomLift_of_base_eq _ _ rfl
  letI := UpperGeometryCleavage.refinementGeometryHom_isHomLift
    ((exactGeometryToRefinementGeometry U).map
      (authoredExactDirectPulledRouteLegAt A z k g))
  dsimp only
  rw [exactGeometryIsoOfRefinementIso_hom_toRefinement]
  apply CategoryTheory.Functor.IsStronglyCartesian.fac
    (p := refinementGeometryProjection U)
    (f := ((authoredExactCompatibleProblemDataAt A z k g).canonicalAuthoredPulledRouteGeometryHomAt
      PUnit.unit).base)
    (φ := (authoredExactCompatibleProblemDataAt A z k g).canonicalAuthoredPulledRouteGeometryHomAt
      PUnit.unit)
    (f' := ((exactGeometryToRefinementGeometry U).map
      (authoredExactDirectPulledRouteLegAt A z k g)).base)
  symm
  apply CategoryTheory.Functor.IsStronglyCartesian.fac
    (p := refinementPackageProjection U)
    (f := ((authoredExactCompatibleProblemDataAt A z k g).canonicalAuthoredPulledRouteGeometryHomAt
      PUnit.unit).base.base)
    (φ := ((authoredExactCompatibleProblemDataAt A z k g).canonicalAuthoredPulledRouteGeometryHomAt
      PUnit.unit).base)
    (f' := ((exactGeometryToRefinementGeometry U).map
      (authoredExactDirectPulledRouteLegAt A z k g)).base.base)
  simpa [UpperGeometryCompatibleProblemInputData.canonicalAuthoredPulledRouteGeometryHomAt_base]
    using (authoredExactCanonicalPulledRoute_base_eq_direct A z k g).symm

/-- The forward exact pulled comparison fixes the authored coefficient ring. -/
theorem authoredExactDirectToCanonicalPulledGeometryIsoAt_hom_coefficient_id
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    (authoredExactDirectToCanonicalPulledGeometryIsoAt A z k g).hom.geometry.coefficientHom =
      RingHom.id k := by
  have h := congrArg (fun hom => hom.geometry.coefficientHom)
    (authoredExactDirectToCanonicalPulledGeometryIsoAt_hom_fac A z k g)
  change
    ((authoredExactCompatibleProblemDataAt A z k g).canonicalAuthoredPulledRouteGeometryHomAt
        PUnit.unit).geometry.coefficientHom.comp
      (authoredExactDirectToCanonicalPulledGeometryIsoAt A z k g).hom.geometry.coefficientHom =
    (authoredExactDirectPulledRouteLegAt A z k g).geometry.coefficientHom at h
  rw [UpperGeometryCompatibleProblemInputData.canonicalAuthoredPulledRouteGeometryHomAt_coefficientHom]
    at h
  simpa [authoredExactDirectPulledRouteLegAt, GeometryTotalHom.comp,
    GeomReadHom.comp] using h

end AAT.AG.FullGeometryNormalization

#assert_standard_axioms_only AAT.AG.FullGeometryNormalization
