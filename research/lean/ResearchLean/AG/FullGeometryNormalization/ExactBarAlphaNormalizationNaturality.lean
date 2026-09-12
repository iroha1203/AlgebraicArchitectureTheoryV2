import ResearchLean.AG.FullGeometryNormalization.ExactNormalizationNaturality
import ResearchLean.AG.FullGeometryNormalization.ExactDerivedBarAlphaTriangle

/-!
# Canonical normalization and the exact-derived bar-alpha comparison

This module completes G-122(B3).  Starting from one admissibility proof at the
authored southwest package, it transports canonical normalization through the
actual left pull, top push, bottom push, and right pull.  The Cycle 9
`barAlpha` triangle then identifies the two composites, and strong Cartesian
and cocartesian uniqueness cancels the two outer lifts.  No endpoint
admissibility or comparison-coherence equation is accepted from the caller.
-/

namespace AAT.AG.FullGeometryNormalization

universe u v

open CategoryTheory AtomFoundation GeometryTransport CrossStageCoherence
open DoctrineFiberProduct

set_option maxHeartbeats 24000000

/-- The actual complete-geometry cocartesian lift commutes with canonical
normalization generated from its source admissibility. -/
theorem geomFiberLift_normalization_natural
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : RealizableHom U)
    (source : GeomFiber.{u, v} input.semantic.source)
    (admissible : CanonicalObjectNormalizationAdmissible source.1.core) :
    (canonicalGeometryFiberNormalization source admissible).1 ≫
        geomFiberLift input.semantic.hom source =
      geomFiberLift input.semantic.hom source ≫
        (canonicalGeometryFiberNormalization
          ((geomFiberTransportFunctor input.semantic.hom).obj source)
          (canonicalGeometryNormalizationAdmissible_exactTransport
            input source admissible)).1 := by
  change canonicalGeometryNormalization source.1 admissible ≫
      geomTransportAlongHom source.1
        (geomFiberBaseHom input.semantic.hom source).doctrineHom =
    geomTransportAlongHom source.1
        (geomFiberBaseHom input.semantic.hom source).doctrineHom ≫
      canonicalGeometryNormalization
        (geomTransportAlong source.1
          (geomFiberBaseHom input.semantic.hom source).doctrineHom)
        (canonicalGeometryNormalizationAdmissible_exactTransport
          input source admissible)
  exact geomTransportAlongHom_normalization_natural source.1 admissible
    (geomFiberBaseHom input.semantic.hom source).doctrineHom

/-- The selected exact complete-geometry Cartesian lift commutes with canonical
normalization generated from its target admissibility. -/
theorem exactGeometryPullLift_fiber_normalization_natural
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : RealizableHom U)
    (target : GeomFiber.{u, v} input.semantic.target)
    (admissible : CanonicalObjectNormalizationAdmissible target.1.core) :
    (canonicalGeometryFiberNormalization
          ((exactGeometryPullFunctor input).obj target)
          (canonicalGeometryNormalizationAdmissible_exactPull
            input target admissible)).1 ≫
        exactGeometryPullLift input target =
      exactGeometryPullLift input target ≫
        (canonicalGeometryFiberNormalization target admissible).1 := by
  change canonicalGeometryNormalization (exactGeometryPull input target).1
        (canonicalGeometryNormalizationAdmissible_exactPull
          input target admissible) ≫
      exactGeometryPullLift input target =
    exactGeometryPullLift input target ≫
      canonicalGeometryNormalization target.1 admissible
  exact exactGeometryPullLift_normalization_natural input target admissible

/-- Specialize push-normalization naturality to the authored top edge and the
left-pulled geometry generated from `g`. -/
theorem authoredExactTopLift_normalization_natural
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k)
    (admissible : CanonicalObjectNormalizationAdmissible
      (A.context.supportPackage z.as)) :
    geomFiberLift A.context.square.semantic.square.top
          (authoredExactLeftPulledGeometryAt A z k g) ≫
        (canonicalGeometryFiberNormalization
          (authoredExactDirectGeometryAt A z k g)
          (authoredExactDirectGeometryAt_admissible A z k g admissible)).1 =
      (canonicalGeometryFiberNormalization
        (authoredExactLeftPulledGeometryAt A z k g)
        (canonicalGeometryNormalizationAdmissible_exactPull
          (authoredExactLeftInput A) (authoredSouthwestGeometryFiberAt A z k g)
          admissible)).1 ≫
        geomFiberLift A.context.square.semantic.square.top
          (authoredExactLeftPulledGeometryAt A z k g) := by
  simpa only [authoredExactDirectGeometryAt,
    authoredExactDirectGeometryAt_admissible] using
      (geomFiberLift_normalization_natural
        (authoredExactTopInput A) (authoredExactLeftPulledGeometryAt A z k g)
        (canonicalGeometryNormalizationAdmissible_exactPull
          (authoredExactLeftInput A) (authoredSouthwestGeometryFiberAt A z k g)
          admissible)).symm

/-- Specialize pull-normalization naturality to the authored left edge; its
northwest admissibility is generated from the southwest input. -/
theorem authoredExactLeftPull_normalization_natural
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k)
    (admissible : CanonicalObjectNormalizationAdmissible
      (A.context.supportPackage z.as)) :
    (canonicalGeometryFiberNormalization
        (authoredExactLeftPulledGeometryAt A z k g)
        (canonicalGeometryNormalizationAdmissible_exactPull
          (authoredExactLeftInput A) (authoredSouthwestGeometryFiberAt A z k g)
          admissible)).1 ≫
      exactGeometryPullLift (authoredExactLeftInput A)
        (authoredSouthwestGeometryFiberAt A z k g) =
    exactGeometryPullLift (authoredExactLeftInput A)
        (authoredSouthwestGeometryFiberAt A z k g) ≫
      (canonicalGeometryFiberNormalization
        (authoredSouthwestGeometryFiberAt A z k g) admissible).1 := by
  simpa only [authoredExactLeftPulledGeometryAt] using
    exactGeometryPullLift_fiber_normalization_natural
      (authoredExactLeftInput A) (authoredSouthwestGeometryFiberAt A z k g)
      admissible

/-- Specialize push-normalization naturality to the authored bottom edge; its
southeast admissibility is generated from the southwest input. -/
theorem authoredExactBottomLift_normalization_natural
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k)
    (admissible : CanonicalObjectNormalizationAdmissible
      (A.context.supportPackage z.as)) :
    (canonicalGeometryFiberNormalization
        (authoredSouthwestGeometryFiberAt A z k g) admissible).1 ≫
      geomFiberLift A.context.square.semantic.square.bottom
        (authoredSouthwestGeometryFiberAt A z k g) =
    geomFiberLift A.context.square.semantic.square.bottom
        (authoredSouthwestGeometryFiberAt A z k g) ≫
      (canonicalGeometryFiberNormalization
        (authoredExactTargetGeometryAt A z k g)
        (canonicalGeometryNormalizationAdmissible_exactTransport
          (authoredExactBottomInput A) (authoredSouthwestGeometryFiberAt A z k g)
          admissible)).1 := by
  simpa only [authoredExactTargetGeometryAt] using
    geomFiberLift_normalization_natural
      (authoredExactBottomInput A) (authoredSouthwestGeometryFiberAt A z k g)
      admissible

/-- Specialize pull-normalization naturality to the authored right edge; both
the target and northeast admissibility proofs are internally transported. -/
theorem authoredExactRightPull_normalization_natural
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k)
    (admissible : CanonicalObjectNormalizationAdmissible
      (A.context.supportPackage z.as)) :
    (canonicalGeometryFiberNormalization
        (authoredExactViaBaseGeometryAt A z k g)
        (authoredExactViaBaseGeometryAt_admissible A z k g admissible)).1 ≫
      exactGeometryPullLift (authoredExactRightInput A)
        (authoredExactTargetGeometryAt A z k g) =
    exactGeometryPullLift (authoredExactRightInput A)
        (authoredExactTargetGeometryAt A z k g) ≫
      (canonicalGeometryFiberNormalization
        (authoredExactTargetGeometryAt A z k g)
        (canonicalGeometryNormalizationAdmissible_exactTransport
          (authoredExactBottomInput A) (authoredSouthwestGeometryFiberAt A z k g)
          admissible)).1 := by
  simpa only [authoredExactViaBaseGeometryAt,
    authoredExactViaBaseGeometryAt_admissible] using
    exactGeometryPullLift_fiber_normalization_natural
      (authoredExactRightInput A) (authoredExactTargetGeometryAt A z k g)
      (canonicalGeometryNormalizationAdmissible_exactTransport
        (authoredExactBottomInput A) (authoredSouthwestGeometryFiberAt A z k g)
        admissible)

/-- Precompose the exact `barAlpha` triangle by the normalization of the
left-pulled endpoint. -/
theorem authoredExactBarAlphaIsoAt_triangle_pre_normalization
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k)
    (admissible : CanonicalObjectNormalizationAdmissible
      (A.context.supportPackage z.as)) :
    (canonicalGeometryFiberNormalization
        (authoredExactLeftPulledGeometryAt A z k g)
        (canonicalGeometryNormalizationAdmissible_exactPull
          (authoredExactLeftInput A) (authoredSouthwestGeometryFiberAt A z k g)
          admissible)).1 ≫
      geomFiberLift A.context.square.semantic.square.top
        (authoredExactLeftPulledGeometryAt A z k g) ≫
      (authoredExactBarAlphaIsoAt A z k g).hom.1 ≫
      exactGeometryPullLift (authoredExactRightInput A)
        (authoredExactTargetGeometryAt A z k g) =
    (canonicalGeometryFiberNormalization
        (authoredExactLeftPulledGeometryAt A z k g)
        (canonicalGeometryNormalizationAdmissible_exactPull
          (authoredExactLeftInput A) (authoredSouthwestGeometryFiberAt A z k g)
          admissible)).1 ≫
      exactGeometryPullLift (authoredExactLeftInput A)
        (authoredSouthwestGeometryFiberAt A z k g) ≫
      geomFiberLift A.context.square.semantic.square.bottom
        (authoredSouthwestGeometryFiberAt A z k g) := by
  simpa only [Category.assoc] using congrArg
    (fun h => (canonicalGeometryFiberNormalization
      (authoredExactLeftPulledGeometryAt A z k g)
      (canonicalGeometryNormalizationAdmissible_exactPull
        (authoredExactLeftInput A) (authoredSouthwestGeometryFiberAt A z k g)
        admissible)).1 ≫ h)
    (authoredExactBarAlphaIsoAt_triangle A z k g)

/-- Postcompose the reversed exact `barAlpha` triangle by the normalization of
the bottom-transport endpoint. -/
theorem authoredExactBarAlphaIsoAt_triangle_post_normalization
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k)
    (admissible : CanonicalObjectNormalizationAdmissible
      (A.context.supportPackage z.as)) :
    exactGeometryPullLift (authoredExactLeftInput A)
        (authoredSouthwestGeometryFiberAt A z k g) ≫
      geomFiberLift A.context.square.semantic.square.bottom
        (authoredSouthwestGeometryFiberAt A z k g) ≫
      (canonicalGeometryFiberNormalization
        (authoredExactTargetGeometryAt A z k g)
        (canonicalGeometryNormalizationAdmissible_exactTransport
          (authoredExactBottomInput A) (authoredSouthwestGeometryFiberAt A z k g)
          admissible)).1 =
    geomFiberLift A.context.square.semantic.square.top
        (authoredExactLeftPulledGeometryAt A z k g) ≫
      (authoredExactBarAlphaIsoAt A z k g).hom.1 ≫
      exactGeometryPullLift (authoredExactRightInput A)
        (authoredExactTargetGeometryAt A z k g) ≫
      (canonicalGeometryFiberNormalization
        (authoredExactTargetGeometryAt A z k g)
        (canonicalGeometryNormalizationAdmissible_exactTransport
          (authoredExactBottomInput A) (authoredSouthwestGeometryFiberAt A z k g)
          admissible)).1 := by
  simpa only [Category.assoc] using congrArg
    (fun h => h ≫ (canonicalGeometryFiberNormalization
      (authoredExactTargetGeometryAt A z k g)
      (canonicalGeometryNormalizationAdmissible_exactTransport
        (authoredExactBottomInput A) (authoredSouthwestGeometryFiberAt A z k g)
        admissible)).1)
    (authoredExactBarAlphaIsoAt_triangle A z k g).symm

/-- Move normalization around the full semantic square: left pull, bottom
push, the Cycle 9 `barAlpha` triangle, top push, and right pull. -/
theorem authoredExactBarAlphaIsoAt_normalization_whiskered
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k)
    (admissible : CanonicalObjectNormalizationAdmissible
      (A.context.supportPackage z.as)) :
    geomFiberLift A.context.square.semantic.square.top
          (authoredExactLeftPulledGeometryAt A z k g) ≫
        (canonicalGeometryFiberNormalization
          (authoredExactDirectGeometryAt A z k g)
          (authoredExactDirectGeometryAt_admissible A z k g admissible)).1 ≫
        (authoredExactBarAlphaIsoAt A z k g).hom.1 ≫
        exactGeometryPullLift (authoredExactRightInput A)
          (authoredExactTargetGeometryAt A z k g) =
      geomFiberLift A.context.square.semantic.square.top
          (authoredExactLeftPulledGeometryAt A z k g) ≫
        (authoredExactBarAlphaIsoAt A z k g).hom.1 ≫
        (canonicalGeometryFiberNormalization
          (authoredExactViaBaseGeometryAt A z k g)
          (authoredExactViaBaseGeometryAt_admissible A z k g admissible)).1 ≫
        exactGeometryPullLift (authoredExactRightInput A)
          (authoredExactTargetGeometryAt A z k g) := by
  calc
    geomFiberLift A.context.square.semantic.square.top
          (authoredExactLeftPulledGeometryAt A z k g) ≫
          (canonicalGeometryFiberNormalization
            (authoredExactDirectGeometryAt A z k g)
            (authoredExactDirectGeometryAt_admissible A z k g admissible)).1 ≫
          (authoredExactBarAlphaIsoAt A z k g).hom.1 ≫
          exactGeometryPullLift (authoredExactRightInput A)
            (authoredExactTargetGeometryAt A z k g) =
        (canonicalGeometryFiberNormalization
          (authoredExactLeftPulledGeometryAt A z k g)
          (canonicalGeometryNormalizationAdmissible_exactPull
            (authoredExactLeftInput A) (authoredSouthwestGeometryFiberAt A z k g)
            admissible)).1 ≫
          geomFiberLift A.context.square.semantic.square.top
            (authoredExactLeftPulledGeometryAt A z k g) ≫
          (authoredExactBarAlphaIsoAt A z k g).hom.1 ≫
          exactGeometryPullLift (authoredExactRightInput A)
            (authoredExactTargetGeometryAt A z k g) := by
      simpa only [Category.assoc] using congrArg
        (fun h => h ≫ (authoredExactBarAlphaIsoAt A z k g).hom.1 ≫
          exactGeometryPullLift (authoredExactRightInput A)
            (authoredExactTargetGeometryAt A z k g))
        (authoredExactTopLift_normalization_natural A z k g admissible)
    _ = (canonicalGeometryFiberNormalization
          (authoredExactLeftPulledGeometryAt A z k g)
          (canonicalGeometryNormalizationAdmissible_exactPull
            (authoredExactLeftInput A) (authoredSouthwestGeometryFiberAt A z k g)
            admissible)).1 ≫
          exactGeometryPullLift (authoredExactLeftInput A)
            (authoredSouthwestGeometryFiberAt A z k g) ≫
          geomFiberLift A.context.square.semantic.square.bottom
            (authoredSouthwestGeometryFiberAt A z k g) :=
      authoredExactBarAlphaIsoAt_triangle_pre_normalization A z k g admissible
    _ = exactGeometryPullLift (authoredExactLeftInput A)
            (authoredSouthwestGeometryFiberAt A z k g) ≫
          (canonicalGeometryFiberNormalization
            (authoredSouthwestGeometryFiberAt A z k g) admissible).1 ≫
          geomFiberLift A.context.square.semantic.square.bottom
            (authoredSouthwestGeometryFiberAt A z k g) := by
      simpa only [Category.assoc] using congrArg
        (fun h => h ≫ geomFiberLift A.context.square.semantic.square.bottom
          (authoredSouthwestGeometryFiberAt A z k g))
        (authoredExactLeftPull_normalization_natural A z k g admissible)
    _ = exactGeometryPullLift (authoredExactLeftInput A)
            (authoredSouthwestGeometryFiberAt A z k g) ≫
          geomFiberLift A.context.square.semantic.square.bottom
            (authoredSouthwestGeometryFiberAt A z k g) ≫
          (canonicalGeometryFiberNormalization
            (authoredExactTargetGeometryAt A z k g)
            (canonicalGeometryNormalizationAdmissible_exactTransport
              (authoredExactBottomInput A) (authoredSouthwestGeometryFiberAt A z k g)
              admissible)).1 := by
      simpa only [Category.assoc] using congrArg
        (fun h => exactGeometryPullLift (authoredExactLeftInput A)
          (authoredSouthwestGeometryFiberAt A z k g) ≫ h)
        (authoredExactBottomLift_normalization_natural A z k g admissible)
    _ = geomFiberLift A.context.square.semantic.square.top
          (authoredExactLeftPulledGeometryAt A z k g) ≫
          (authoredExactBarAlphaIsoAt A z k g).hom.1 ≫
          exactGeometryPullLift (authoredExactRightInput A)
            (authoredExactTargetGeometryAt A z k g) ≫
          (canonicalGeometryFiberNormalization
            (authoredExactTargetGeometryAt A z k g)
            (canonicalGeometryNormalizationAdmissible_exactTransport
              (authoredExactBottomInput A) (authoredSouthwestGeometryFiberAt A z k g)
              admissible)).1 :=
      authoredExactBarAlphaIsoAt_triangle_post_normalization A z k g admissible
    _ = geomFiberLift A.context.square.semantic.square.top
          (authoredExactLeftPulledGeometryAt A z k g) ≫
          (authoredExactBarAlphaIsoAt A z k g).hom.1 ≫
          (canonicalGeometryFiberNormalization
            (authoredExactViaBaseGeometryAt A z k g)
            (authoredExactViaBaseGeometryAt_admissible A z k g admissible)).1 ≫
          exactGeometryPullLift (authoredExactRightInput A)
            (authoredExactTargetGeometryAt A z k g) := by
      simpa only [Category.assoc] using congrArg
        (fun h => geomFiberLift A.context.square.semantic.square.top
          (authoredExactLeftPulledGeometryAt A z k g) ≫
          (authoredExactBarAlphaIsoAt A z k g).hom.1 ≫ h)
        (authoredExactRightPull_normalization_natural A z k g admissible).symm

/-- Cancel the selected right Cartesian lift from the two-sided whiskered
normalization equality. -/
theorem authoredExactBarAlphaIsoAt_normalization_top_whiskered
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k)
    (admissible : CanonicalObjectNormalizationAdmissible
      (A.context.supportPackage z.as)) :
    geomFiberLift A.context.square.semantic.square.top
          (authoredExactLeftPulledGeometryAt A z k g) ≫
        (canonicalGeometryFiberNormalization
          (authoredExactDirectGeometryAt A z k g)
          (authoredExactDirectGeometryAt_admissible A z k g admissible)).1 ≫
        (authoredExactBarAlphaIsoAt A z k g).hom.1 =
      geomFiberLift A.context.square.semantic.square.top
          (authoredExactLeftPulledGeometryAt A z k g) ≫
        (authoredExactBarAlphaIsoAt A z k g).hom.1 ≫
        (canonicalGeometryFiberNormalization
          (authoredExactViaBaseGeometryAt A z k g)
          (authoredExactViaBaseGeometryAt_admissible A z k g admissible)).1 := by
  letI : (crossStageProjection.{u, v} U).IsStronglyCartesian
      (authoredExactRightInput A).semantic.hom
      (exactGeometryPullLift (authoredExactRightInput A)
        (authoredExactTargetGeometryAt A z k g)) :=
    exactGeometryPullLift_crossStageStronglyCartesian
      (authoredExactRightInput A) (authoredExactTargetGeometryAt A z k g)
  letI : (crossStageProjection.{u, v} U).IsHomLift
      A.context.square.semantic.square.top
      (geomFiberLift A.context.square.semantic.square.top
        (authoredExactLeftPulledGeometryAt A z k g)) :=
    geomFiberLift_isHomLift A.context.square.semantic.square.top
      (authoredExactLeftPulledGeometryAt A z k g)
  letI : (crossStageProjection.{u, v} U).IsHomLift
      (𝟙 A.context.square.semantic.square.northeast)
      (canonicalGeometryFiberNormalization
        (authoredExactDirectGeometryAt A z k g)
        (authoredExactDirectGeometryAt_admissible A z k g admissible)).1 :=
    (canonicalGeometryFiberNormalization
      (authoredExactDirectGeometryAt A z k g)
      (authoredExactDirectGeometryAt_admissible A z k g admissible)).2
  letI : (crossStageProjection.{u, v} U).IsHomLift
      (𝟙 A.context.square.semantic.square.northeast)
      (authoredExactBarAlphaIsoAt A z k g).hom.1 :=
    (authoredExactBarAlphaIsoAt A z k g).hom.2
  letI : (crossStageProjection.{u, v} U).IsHomLift
      (𝟙 A.context.square.semantic.square.northeast)
      (canonicalGeometryFiberNormalization
        (authoredExactViaBaseGeometryAt A z k g)
        (authoredExactViaBaseGeometryAt_admissible A z k g admissible)).1 :=
    (canonicalGeometryFiberNormalization
      (authoredExactViaBaseGeometryAt A z k g)
      (authoredExactViaBaseGeometryAt_admissible A z k g admissible)).2
  letI : (crossStageProjection.{u, v} U).IsHomLift
      A.context.square.semantic.square.top
      (geomFiberLift A.context.square.semantic.square.top
          (authoredExactLeftPulledGeometryAt A z k g) ≫
        (canonicalGeometryFiberNormalization
          (authoredExactDirectGeometryAt A z k g)
          (authoredExactDirectGeometryAt_admissible A z k g admissible)).1) := by
    simpa using CategoryTheory.IsHomLift.comp
      (crossStageProjection.{u, v} U)
      A.context.square.semantic.square.top
      (𝟙 A.context.square.semantic.square.northeast)
      (geomFiberLift A.context.square.semantic.square.top
        (authoredExactLeftPulledGeometryAt A z k g))
      (canonicalGeometryFiberNormalization
        (authoredExactDirectGeometryAt A z k g)
        (authoredExactDirectGeometryAt_admissible A z k g admissible)).1
  letI : (crossStageProjection.{u, v} U).IsHomLift
      A.context.square.semantic.square.top
      (geomFiberLift A.context.square.semantic.square.top
          (authoredExactLeftPulledGeometryAt A z k g) ≫
        (canonicalGeometryFiberNormalization
          (authoredExactDirectGeometryAt A z k g)
          (authoredExactDirectGeometryAt_admissible A z k g admissible)).1 ≫
        (authoredExactBarAlphaIsoAt A z k g).hom.1) := by
    simpa using CategoryTheory.IsHomLift.comp
      (crossStageProjection.{u, v} U)
      A.context.square.semantic.square.top
      (𝟙 A.context.square.semantic.square.northeast)
      (geomFiberLift A.context.square.semantic.square.top
          (authoredExactLeftPulledGeometryAt A z k g) ≫
        (canonicalGeometryFiberNormalization
          (authoredExactDirectGeometryAt A z k g)
          (authoredExactDirectGeometryAt_admissible A z k g admissible)).1)
      (authoredExactBarAlphaIsoAt A z k g).hom.1
  letI : (crossStageProjection.{u, v} U).IsHomLift
      A.context.square.semantic.square.top
      (geomFiberLift A.context.square.semantic.square.top
          (authoredExactLeftPulledGeometryAt A z k g) ≫
        (authoredExactBarAlphaIsoAt A z k g).hom.1) := by
    simpa using CategoryTheory.IsHomLift.comp
      (crossStageProjection.{u, v} U)
      A.context.square.semantic.square.top
      (𝟙 A.context.square.semantic.square.northeast)
      (geomFiberLift A.context.square.semantic.square.top
        (authoredExactLeftPulledGeometryAt A z k g))
      (authoredExactBarAlphaIsoAt A z k g).hom.1
  letI : (crossStageProjection.{u, v} U).IsHomLift
      A.context.square.semantic.square.top
      (geomFiberLift A.context.square.semantic.square.top
          (authoredExactLeftPulledGeometryAt A z k g) ≫
        (authoredExactBarAlphaIsoAt A z k g).hom.1 ≫
        (canonicalGeometryFiberNormalization
          (authoredExactViaBaseGeometryAt A z k g)
          (authoredExactViaBaseGeometryAt_admissible A z k g admissible)).1) := by
    simpa using CategoryTheory.IsHomLift.comp
      (crossStageProjection.{u, v} U)
      A.context.square.semantic.square.top
      (𝟙 A.context.square.semantic.square.northeast)
      (geomFiberLift A.context.square.semantic.square.top
          (authoredExactLeftPulledGeometryAt A z k g) ≫
        (authoredExactBarAlphaIsoAt A z k g).hom.1)
      (canonicalGeometryFiberNormalization
        (authoredExactViaBaseGeometryAt A z k g)
        (authoredExactViaBaseGeometryAt_admissible A z k g admissible)).1
  apply CategoryTheory.Functor.IsStronglyCartesian.ext
    (crossStageProjection.{u, v} U)
    (authoredExactRightInput A).semantic.hom
    (exactGeometryPullLift (authoredExactRightInput A)
      (authoredExactTargetGeometryAt A z k g))
    A.context.square.semantic.square.top
  simpa only [Category.assoc] using
    authoredExactBarAlphaIsoAt_normalization_whiskered
      A z k g admissible

/-- Cancel the top cocartesian lift and obtain the underlying complete-geometry
morphism equality between normalization and `barAlpha`. -/
theorem authoredExactBarAlphaIsoAt_normalization_core
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k)
    (admissible : CanonicalObjectNormalizationAdmissible
      (A.context.supportPackage z.as)) :
    (canonicalGeometryFiberNormalization
          (authoredExactDirectGeometryAt A z k g)
          (authoredExactDirectGeometryAt_admissible A z k g admissible)).1 ≫
        (authoredExactBarAlphaIsoAt A z k g).hom.1 =
      (authoredExactBarAlphaIsoAt A z k g).hom.1 ≫
        (canonicalGeometryFiberNormalization
          (authoredExactViaBaseGeometryAt A z k g)
          (authoredExactViaBaseGeometryAt_admissible A z k g admissible)).1 := by
  letI : (crossStageProjection.{u, v} U).IsStronglyCocartesian
      A.context.square.semantic.square.top
      (geomFiberLift A.context.square.semantic.square.top
        (authoredExactLeftPulledGeometryAt A z k g)) :=
    geomFiberLift_isStronglyCocartesian
      A.context.square.semantic.square.top
      (authoredExactLeftPulledGeometryAt A z k g)
  letI : (crossStageProjection.{u, v} U).IsHomLift
      A.context.square.semantic.square.top
      (geomFiberLift A.context.square.semantic.square.top
        (authoredExactLeftPulledGeometryAt A z k g)) :=
    geomFiberLift_isHomLift A.context.square.semantic.square.top
      (authoredExactLeftPulledGeometryAt A z k g)
  letI : (crossStageProjection.{u, v} U).IsHomLift
      (𝟙 A.context.square.semantic.square.northeast)
      (canonicalGeometryFiberNormalization
        (authoredExactDirectGeometryAt A z k g)
        (authoredExactDirectGeometryAt_admissible A z k g admissible)).1 :=
    (canonicalGeometryFiberNormalization
      (authoredExactDirectGeometryAt A z k g)
      (authoredExactDirectGeometryAt_admissible A z k g admissible)).2
  letI : (crossStageProjection.{u, v} U).IsHomLift
      (𝟙 A.context.square.semantic.square.northeast)
      (authoredExactBarAlphaIsoAt A z k g).hom.1 :=
    (authoredExactBarAlphaIsoAt A z k g).hom.2
  letI : (crossStageProjection.{u, v} U).IsHomLift
      (𝟙 A.context.square.semantic.square.northeast)
      (canonicalGeometryFiberNormalization
        (authoredExactViaBaseGeometryAt A z k g)
        (authoredExactViaBaseGeometryAt_admissible A z k g admissible)).1 :=
    (canonicalGeometryFiberNormalization
      (authoredExactViaBaseGeometryAt A z k g)
      (authoredExactViaBaseGeometryAt_admissible A z k g admissible)).2
  letI : (crossStageProjection.{u, v} U).IsHomLift
      (𝟙 A.context.square.semantic.square.northeast)
      ((canonicalGeometryFiberNormalization
          (authoredExactDirectGeometryAt A z k g)
          (authoredExactDirectGeometryAt_admissible A z k g admissible)).1 ≫
        (authoredExactBarAlphaIsoAt A z k g).hom.1) := by
    simpa using CategoryTheory.IsHomLift.comp
      (crossStageProjection.{u, v} U)
      (𝟙 A.context.square.semantic.square.northeast)
      (𝟙 A.context.square.semantic.square.northeast)
      (canonicalGeometryFiberNormalization
        (authoredExactDirectGeometryAt A z k g)
        (authoredExactDirectGeometryAt_admissible A z k g admissible)).1
      (authoredExactBarAlphaIsoAt A z k g).hom.1
  letI : (crossStageProjection.{u, v} U).IsHomLift
      (𝟙 A.context.square.semantic.square.northeast)
      ((authoredExactBarAlphaIsoAt A z k g).hom.1 ≫
        (canonicalGeometryFiberNormalization
          (authoredExactViaBaseGeometryAt A z k g)
          (authoredExactViaBaseGeometryAt_admissible A z k g admissible)).1) := by
    simpa using CategoryTheory.IsHomLift.comp
      (crossStageProjection.{u, v} U)
      (𝟙 A.context.square.semantic.square.northeast)
      (𝟙 A.context.square.semantic.square.northeast)
      (authoredExactBarAlphaIsoAt A z k g).hom.1
      (canonicalGeometryFiberNormalization
        (authoredExactViaBaseGeometryAt A z k g)
        (authoredExactViaBaseGeometryAt_admissible A z k g admissible)).1
  apply CategoryTheory.Functor.IsStronglyCocartesian.ext
    (crossStageProjection.{u, v} U)
    A.context.square.semantic.square.top
    (geomFiberLift A.context.square.semantic.square.top
      (authoredExactLeftPulledGeometryAt A z k g))
    (𝟙 A.context.square.semantic.square.northeast)
  simpa only [Category.assoc] using
    authoredExactBarAlphaIsoAt_normalization_top_whiskered
      A z k g admissible

/-- G-122(B3): canonical normalization commutes with the actual five-factor
exact-derived `barAlpha`, from one southwest admissibility proof only. -/
theorem authoredExactBarAlphaIsoAt_normalization_natural
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k)
    (admissible : CanonicalObjectNormalizationAdmissible
      (A.context.supportPackage z.as)) :
    canonicalGeometryFiberNormalization
          (authoredExactDirectGeometryAt A z k g)
          (authoredExactDirectGeometryAt_admissible A z k g admissible) ≫
        (authoredExactBarAlphaIsoAt A z k g).hom =
      (authoredExactBarAlphaIsoAt A z k g).hom ≫
        canonicalGeometryFiberNormalization
          (authoredExactViaBaseGeometryAt A z k g)
          (authoredExactViaBaseGeometryAt_admissible A z k g admissible) := by
  apply CategoryTheory.Functor.Fiber.hom_ext
  exact authoredExactBarAlphaIsoAt_normalization_core
    A z k g admissible

end AAT.AG.FullGeometryNormalization

#assert_standard_axioms_only AAT.AG.FullGeometryNormalization
