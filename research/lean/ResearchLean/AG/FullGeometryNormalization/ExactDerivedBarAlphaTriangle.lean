import ResearchLean.AG.FullGeometryNormalization.ExactDerivedMateComposite
import ResearchLean.AG.FullGeometryNormalization.ExactDerivedMateProjectionTriangle
import ResearchLean.AG.FullGeometryNormalization.ExactDerivedSupportCoreEndpoints
import ResearchLean.AG.FullGeometryNormalization.ExactGeometryAdjunctionProjection
import ResearchLean.AG.DoctrineFiberProduct.CoreBeckChevalleyMateCleavageIndependence

/-!
# Exact-derived bar-alpha triangle

This module proves the two factorization laws needed to compare the exact
complete-geometry mate with the canonical core Beck--Chevalley mate.  The
first exposes the selected Cartesian lift in the canonical core mate.  The
second proves that the full exact-derived `barAlpha` is the unique lift of the
commuting semantic square, using the generated G-118 mate and the endpoint
triangle rather than accepting a comparison equation from the caller.
-/

namespace AAT.AG.FullGeometryNormalization

universe u v

open CategoryTheory AtomFoundation GeometryTransport CrossStageCoherence
open DoctrineFiberProduct

set_option maxHeartbeats 12000000

/-- The independently generated G-116 core Beck--Chevalley mate factors through
the selected right Cartesian lift.  Its source is the presentation and source
package; no mate factorization is accepted as an input. -/
theorem coreBeckChevalleyMate_app_selectedLift_fac
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (presentation : BCPresentation U)
    (sourcePackage : CoreFiber presentation.1.cospan.firstSource.toSemantic) :
    ((coreBeckChevalleyMate presentation).app sourcePackage).1 ≫
        (selectedCoreFiberCartesianLift (bcRightInput presentation)
          ((coreFiberTransportFunctor
            (typedPresentationToSemantic
              (bcBottomPresentation presentation))).obj sourcePackage)).hom =
      (coreFiberLift (bcRightInput presentation).semantic.hom
          ((coreFiberTransportFunctor
            (typedPresentationToSemantic
              (bcTopPresentation presentation))).obj
            ((selectedCoreFiberReindexFunctor
              (bcLeftInput presentation)).obj sourcePackage))) ≫
        (((bcCoreTransportSquareIso presentation).hom.app
            ((selectedCoreFiberReindexFunctor
              (bcLeftInput presentation)).obj sourcePackage)) ≫
          (coreFiberTransportFunctor
            (typedPresentationToSemantic
              (bcBottomPresentation presentation))).map
            ((bcLeftAdjunction presentation).counit.app sourcePackage)).1 := by
  rw [coreBeckChevalleyMate_homEquiv,
    bcRightAdjunction_homEquiv_apply]
  exact coreTransportToReindexHom_fac
    (bcRightInput presentation)
    ((coreFiberTransportFunctor
      (typedPresentationToSemantic
        (bcTopPresentation presentation))).obj
      ((selectedCoreFiberReindexFunctor
        (bcLeftInput presentation)).obj sourcePackage))
    ((coreFiberTransportFunctor
      (typedPresentationToSemantic
        (bcBottomPresentation presentation))).obj sourcePackage)
    ((bcCoreTransportSquareIso presentation).hom.app
        ((selectedCoreFiberReindexFunctor
          (bcLeftInput presentation)).obj sourcePackage) ≫
      (coreFiberTransportFunctor
        (typedPresentationToSemantic
          (bcBottomPresentation presentation))).map
    ((bcLeftAdjunction presentation).counit.app sourcePackage))

/-- The five-factor exact `barAlpha` is the complete-geometry lift of the
commuting semantic square.  The proof consumes the actual G-118 endpoint
triangle together with exact unit and counit factor laws. -/
theorem authoredExactBarAlphaIsoAt_triangle
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    geomFiberLift A.context.square.semantic.square.top
          (authoredExactLeftPulledGeometryAt A z k g) ≫
        (authoredExactBarAlphaIsoAt A z k g).hom.1 ≫
        exactGeometryPullLift (authoredExactRightInput A)
          (authoredExactTargetGeometryAt A z k g) =
      exactGeometryPullLift (authoredExactLeftInput A)
          (authoredSouthwestGeometryFiberAt A z k g) ≫
        geomFiberLift A.context.square.semantic.square.bottom
          (authoredSouthwestGeometryFiberAt A z k g) := by
  let middle :=
    (authoredExactBToGeneratedBaseNorthwestIsoAt A z k g).hom ≫
      authoredExactGeneratedMateNorthwestAt A z k g ≫
      (authoredExactGeneratedPulledToTargetNorthwestIsoAt A z k g).hom
  have hmiddle : middle.1 ≫ authoredExactDirectPulledRouteLegAt A z k g =
      authoredExactDirectBaseRouteLegAt A z k g := by
    exact authoredExactDirectEndpointMate_triangle A z k g
  let unitPull := exactGeometryPullMap (authoredExactLeftInput A)
    ((exactGeometryTransportPullUnit
      (authoredExactBottomInput A)).app
        (authoredSouthwestGeometryFiberAt A z k g))
  have htopUnit' :
      geomFiberLift A.context.square.semantic.square.top
          (authoredExactLeftPulledGeometryAt A z k g) ≫
        (geomFiberTransportMap A.context.square.semantic.square.top unitPull).1 =
      unitPull.1 ≫ geomFiberLift A.context.square.semantic.square.top
        (authoredExactGeneratedMateSourceGeometryAt A z k g) := by
    simpa [unitPull, authoredExactLeftPulledGeometryAt,
      authoredExactGeneratedMateSourceGeometryAt,
      authoredExactBottomPulledTargetGeometryAt] using
        geomFiberTransportMap_fac A.context.square.semantic.square.top unitPull
  have hunitFac :
      geomFiberLift A.context.square.semantic.square.top
          (authoredExactLeftPulledGeometryAt A z k g) ≫
        (authoredExactUnitTopPushIsoAt A z k g).hom.1 =
      unitPull.1 ≫ geomFiberLift A.context.square.semantic.square.top
        (authoredExactGeneratedMateSourceGeometryAt A z k g) := by
    simpa [authoredExactUnitTopPushIsoAt, unitPull] using htopUnit'
  have hmiddleFac :
      geomFiberLift A.context.square.semantic.square.top
          (authoredExactGeneratedMateSourceGeometryAt A z k g) ≫
        ((geomFiberTransportFunctor
          A.context.square.semantic.square.top).map middle).1 =
      middle.1 ≫ geomFiberLift A.context.square.semantic.square.top
        (authoredExactGeneratedMateTargetGeometryAt A z k g) := by
    simpa only [geomFiberTransportFunctor] using
      geomFiberTransportMap_fac A.context.square.semantic.square.top middle
  have htargetFac :
      (geomFiberLift A.context.square.semantic.square.top
          (authoredExactGeneratedMateTargetGeometryAt A z k g) ≫
        (authoredExactTopCounitIsoAt A z k g).hom.1) ≫
        exactGeometryPullLift (authoredExactRightInput A)
          (authoredExactTargetGeometryAt A z k g) =
      authoredExactDirectPulledRouteLegAt A z k g := by
    change (geomFiberLift (authoredExactTopInput A).semantic.hom
          ((exactGeometryPullFunctor (authoredExactTopInput A)).obj
            (authoredExactViaBaseGeometryAt A z k g)) ≫
        ((exactGeometryTransportPullCounit
          (authoredExactTopInput A)).app
            (authoredExactViaBaseGeometryAt A z k g)).1) ≫
        exactGeometryPullLift (authoredExactRightInput A)
          (authoredExactTargetGeometryAt A z k g) = _
    rw [exactGeometryTransportPullCounit_app_fac]
    rfl
  have hleftUnit :
      (exactGeometryPullMap (authoredExactLeftInput A)
        ((exactGeometryTransportPullUnit
          (authoredExactBottomInput A)).app
            (authoredSouthwestGeometryFiberAt A z k g))).1 ≫
        exactGeometryPullLift (authoredExactLeftInput A)
          (authoredExactBottomPulledTargetGeometryAt A z k g) =
      exactGeometryPullLift (authoredExactLeftInput A)
          (authoredSouthwestGeometryFiberAt A z k g) ≫
        ((exactGeometryTransportPullUnit
          (authoredExactBottomInput A)).app
            (authoredSouthwestGeometryFiberAt A z k g)).1 := by
    simpa [authoredExactBottomPulledTargetGeometryAt] using
      exactGeometryPullMap_fac (authoredExactLeftInput A)
        ((exactGeometryTransportPullUnit
          (authoredExactBottomInput A)).app
            (authoredSouthwestGeometryFiberAt A z k g))
  have hbottomUnit :
      ((exactGeometryTransportPullUnit
        (authoredExactBottomInput A)).app
          (authoredSouthwestGeometryFiberAt A z k g)).1 ≫
        exactGeometryPullLift (authoredExactBottomInput A)
          (authoredExactTargetGeometryAt A z k g) =
      geomFiberLift A.context.square.semantic.square.bottom
        (authoredSouthwestGeometryFiberAt A z k g) := by
    simpa [authoredExactTargetGeometryAt] using
      exactGeometryTransportPullUnit_app_fac
        (authoredExactBottomInput A)
        (authoredSouthwestGeometryFiberAt A z k g)
  have hbar : (authoredExactBarAlphaIsoAt A z k g).hom =
      (authoredExactUnitTopPushIsoAt A z k g).hom ≫
        (geomFiberTransportFunctor
          A.context.square.semantic.square.top).map middle ≫
        (authoredExactTopCounitIsoAt A z k g).hom := by
    rw [authoredExactBarAlphaIsoAt_hom]
    unfold authoredExactGeneratedMateTopPushIsoAt
      authoredExactGeneratedMateTopPushAt
    dsimp only
    dsimp only [middle]
    simp only [asIso_hom, Functor.map_comp, Category.assoc]
  rw [hbar]
  change
    geomFiberLift A.context.square.semantic.square.top
          (authoredExactLeftPulledGeometryAt A z k g) ≫
        (authoredExactUnitTopPushIsoAt A z k g).hom.1 ≫
        ((geomFiberTransportFunctor
          A.context.square.semantic.square.top).map middle).1 ≫
        (authoredExactTopCounitIsoAt A z k g).hom.1 ≫
        exactGeometryPullLift (authoredExactRightInput A)
          (authoredExactTargetGeometryAt A z k g) = _
  slice_lhs 1 2 => rw [hunitFac]
  slice_lhs 2 3 => rw [hmiddleFac]
  slice_lhs 3 5 => rw [← Category.assoc, htargetFac]
  change unitPull.1 ≫ middle.1 ≫
      authoredExactDirectPulledRouteLegAt A z k g = _
  rw [hmiddle]
  unfold authoredExactDirectBaseRouteLegAt
  dsimp only [unitPull]
  rw [← Category.assoc, hleftUnit]
  rw [Category.assoc]
  rw [hbottomUnit]

end AAT.AG.FullGeometryNormalization

#assert_standard_axioms_only AAT.AG.FullGeometryNormalization
