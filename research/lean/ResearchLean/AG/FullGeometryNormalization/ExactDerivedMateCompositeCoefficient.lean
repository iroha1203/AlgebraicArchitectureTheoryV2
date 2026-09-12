import ResearchLean.AG.FullGeometryNormalization.ExactDerivedMateComposite
import ResearchLean.AG.FullGeometryNormalization.ExactDerivedDirectCanonicalBridgeLaws

/-!
# Coefficient laws for the exact-derived mate composite

This module proves that the endpoint changes used by the literal five-factor
mate fix the authored coefficient ring, and then combines those equations
with the exact unit, generated mate, and exact counit equations.

## Implementation notes

The canonical-to-generated equations are inherited from the exact endpoint
comparisons and preserved by transport to the northwest fiber.  The composite
equation is obtained by unfolding only the public five-factor hom equation;
no coefficient equation or invertibility witness is accepted from a caller.
-/

namespace AAT.AG.FullGeometryNormalization

universe u v

open CategoryTheory AtomFoundation GeometryTransport CrossStageCoherence
open DoctrineFiberProduct

set_option maxHeartbeats 3000000

/-! ## Direct-to-canonical endpoint comparisons -/

/-- The source endpoint bridge fixes the authored coefficient ring.  Its
forward map is the exact direct-to-canonical comparison followed by the
canonical cocartesian transport lift, both of which have identity coefficient
map. -/
theorem authoredExactGeneratedMateSourceToCanonicalBaseNorthwestIsoAt_hom_coefficient_id
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    (authoredExactGeneratedMateSourceToCanonicalBaseNorthwestIsoAt
      A z k g).hom.1.geometry.coefficientHom = RingHom.id k := by
  change ((authoredExactDirectToCanonicalBaseGeometryIsoAt A z k g).hom ≫
      geomFiberLift (authoredExactPullbackSourceIso A).hom
        (authoredExactCanonicalBaseRouteFiberAt A z k g)).geometry.coefficientHom =
    RingHom.id k
  rw [show ((authoredExactDirectToCanonicalBaseGeometryIsoAt A z k g).hom ≫
      geomFiberLift (authoredExactPullbackSourceIso A).hom
        (authoredExactCanonicalBaseRouteFiberAt A z k g)).geometry.coefficientHom =
      (geomFiberLift (authoredExactPullbackSourceIso A).hom
          (authoredExactCanonicalBaseRouteFiberAt A z k g)).geometry.coefficientHom.comp
        (authoredExactDirectToCanonicalBaseGeometryIsoAt A z k g).hom.geometry.coefficientHom
      by rfl]
  rw [authoredExactDirectToCanonicalBaseGeometryIsoAt_hom_coefficient_id]
  simp [geomFiberLift, geomTransportAlongHom,
    geomTransportAlongGeometryHom]

/-- The forward target endpoint bridge fixes the authored coefficient ring by
the pulled-route factor equation and the canonical transport lift. -/
theorem authoredExactGeneratedMateTargetToCanonicalPulledNorthwestIsoAt_hom_coefficient_id
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    (authoredExactGeneratedMateTargetToCanonicalPulledNorthwestIsoAt
      A z k g).hom.1.geometry.coefficientHom = RingHom.id k := by
  change ((authoredExactDirectToCanonicalPulledGeometryIsoAt A z k g).hom ≫
      geomFiberLift (authoredExactPullbackSourceIso A).hom
        (authoredExactCanonicalPulledRouteFiberAt A z k g)).geometry.coefficientHom =
    RingHom.id k
  rw [show ((authoredExactDirectToCanonicalPulledGeometryIsoAt A z k g).hom ≫
      geomFiberLift (authoredExactPullbackSourceIso A).hom
        (authoredExactCanonicalPulledRouteFiberAt A z k g)).geometry.coefficientHom =
      (geomFiberLift (authoredExactPullbackSourceIso A).hom
          (authoredExactCanonicalPulledRouteFiberAt A z k g)).geometry.coefficientHom.comp
        (authoredExactDirectToCanonicalPulledGeometryIsoAt A z k g).hom.geometry.coefficientHom
      by rfl]
  rw [authoredExactDirectToCanonicalPulledGeometryIsoAt_hom_coefficient_id]
  simp [geomFiberLift, geomTransportAlongHom,
    geomTransportAlongGeometryHom]

/-- The inverse target endpoint bridge fixes the authored coefficient ring,
as follows from the forward identity and the inverse law of the constructed
isomorphism. -/
theorem authoredExactGeneratedMateTargetToCanonicalPulledNorthwestIsoAt_inv_coefficient_id
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    (authoredExactGeneratedMateTargetToCanonicalPulledNorthwestIsoAt
      A z k g).inv.1.geometry.coefficientHom = RingHom.id k := by
  have h := congrArg (fun hom => hom.1.geometry.coefficientHom)
    (authoredExactGeneratedMateTargetToCanonicalPulledNorthwestIsoAt
      A z k g).hom_inv_id
  change
    (authoredExactGeneratedMateTargetToCanonicalPulledNorthwestIsoAt
      A z k g).inv.1.geometry.coefficientHom.comp
      (authoredExactGeneratedMateTargetToCanonicalPulledNorthwestIsoAt
        A z k g).hom.1.geometry.coefficientHom = RingHom.id k at h
  rw [authoredExactGeneratedMateTargetToCanonicalPulledNorthwestIsoAt_hom_coefficient_id]
    at h
  simpa using h

/-! ## Canonical-to-generated endpoint comparisons -/

/-- The canonical-to-generated base endpoint comparison fixes the authored
coefficient ring before transport to the northwest fiber. -/
theorem authoredExactCanonicalBaseToGeneratedFiberIsoAt_hom_coefficient_id
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    (authoredExactCanonicalBaseToGeneratedFiberIsoAt A z k g).hom.1.geometry.coefficientHom =
      RingHom.id k := by
  let input := authoredExactCompatibleProblemDataAt A z k g
  simpa [authoredExactCanonicalBaseToGeneratedFiberIsoAt, input] using
    input.canonicalAuthoredBaseToGeneratedRouteExactGeometryHomAt_coefficient_id
      PUnit.unit

/-- The inverse canonical-to-generated base endpoint comparison also fixes
the authored coefficient ring. -/
theorem authoredExactCanonicalBaseToGeneratedFiberIsoAt_inv_coefficient_id
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    (authoredExactCanonicalBaseToGeneratedFiberIsoAt A z k g).inv.1.geometry.coefficientHom =
      RingHom.id k := by
  let input := authoredExactCompatibleProblemDataAt A z k g
  simpa [authoredExactCanonicalBaseToGeneratedFiberIsoAt, input] using
    input.canonicalAuthoredBaseToGeneratedRouteExactGeometryInvAt_coefficient_id
      PUnit.unit

/-- The inverse canonical-to-generated pulled endpoint comparison fixes the
authored coefficient ring before northwest transport. -/
theorem authoredExactCanonicalPulledToGeneratedFiberIsoAt_inv_coefficient_id
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    (authoredExactCanonicalPulledToGeneratedFiberIsoAt A z k g).inv.1.geometry.coefficientHom =
      RingHom.id k := by
  let input := authoredExactCompatibleProblemDataAt A z k g
  simpa [authoredExactCanonicalPulledToGeneratedFiberIsoAt, input] using
    input.canonicalAuthoredPulledToGeneratedRouteExactGeometryInvAt_coefficient_id
      PUnit.unit

/-- Northwest transport preserves the coefficient identity of the forward
canonical-to-generated base comparison. -/
theorem authoredExactCanonicalBaseToGeneratedNorthwestIsoAt_hom_coefficient_id
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    (authoredExactCanonicalBaseToGeneratedNorthwestIsoAt A z k g).hom.1.geometry.coefficientHom =
      RingHom.id k := by
  rw [show (authoredExactCanonicalBaseToGeneratedNorthwestIsoAt A z k g).hom =
      (geomFiberTransportFunctor (authoredExactPullbackSourceIso A).hom).map
        (authoredExactCanonicalBaseToGeneratedFiberIsoAt A z k g).hom by rfl]
  change (geomFiberTransportMap (authoredExactPullbackSourceIso A).hom
      (authoredExactCanonicalBaseToGeneratedFiberIsoAt A z k g).hom).1.geometry.coefficientHom =
        RingHom.id k
  rw [geomFiberTransportMap_coefficientHom,
    authoredExactCanonicalBaseToGeneratedFiberIsoAt_hom_coefficient_id]

/-- Northwest transport preserves the coefficient identity of the inverse
canonical-to-generated pulled comparison. -/
theorem authoredExactCanonicalPulledToGeneratedNorthwestIsoAt_inv_coefficient_id
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    (authoredExactCanonicalPulledToGeneratedNorthwestIsoAt A z k g).inv.1.geometry.coefficientHom =
      RingHom.id k := by
  rw [show (authoredExactCanonicalPulledToGeneratedNorthwestIsoAt A z k g).inv =
      (geomFiberTransportFunctor (authoredExactPullbackSourceIso A).hom).map
        (authoredExactCanonicalPulledToGeneratedFiberIsoAt A z k g).inv by rfl]
  change (geomFiberTransportMap (authoredExactPullbackSourceIso A).hom
      (authoredExactCanonicalPulledToGeneratedFiberIsoAt A z k g).inv).1.geometry.coefficientHom =
        RingHom.id k
  rw [geomFiberTransportMap_coefficientHom]
  exact authoredExactCanonicalPulledToGeneratedFiberIsoAt_inv_coefficient_id
    A z k g

/-! ## Endpoint alignments in the five-factor mate -/

/-- The composite from the literal mate source to the generated base-route
endpoint fixes the authored coefficient ring. -/
theorem authoredExactBToGeneratedBaseNorthwestIsoAt_hom_coefficient_id
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    (authoredExactBToGeneratedBaseNorthwestIsoAt A z k g).hom.1.geometry.coefficientHom =
      RingHom.id k := by
  change
    (authoredExactCanonicalBaseToGeneratedNorthwestIsoAt
      A z k g).hom.1.geometry.coefficientHom.comp
      (authoredExactGeneratedMateSourceToCanonicalBaseNorthwestIsoAt
        A z k g).hom.1.geometry.coefficientHom = RingHom.id k
  rw [authoredExactCanonicalBaseToGeneratedNorthwestIsoAt_hom_coefficient_id,
    authoredExactGeneratedMateSourceToCanonicalBaseNorthwestIsoAt_hom_coefficient_id]
  rfl

/-- The composite from the generated pulled-route endpoint to the literal
mate target fixes the authored coefficient ring. -/
theorem authoredExactGeneratedPulledToTargetNorthwestIsoAt_hom_coefficient_id
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    (authoredExactGeneratedPulledToTargetNorthwestIsoAt A z k g).hom.1.geometry.coefficientHom =
      RingHom.id k := by
  change
    (authoredExactGeneratedMateTargetToCanonicalPulledNorthwestIsoAt
      A z k g).inv.1.geometry.coefficientHom.comp
      (authoredExactCanonicalPulledToGeneratedNorthwestIsoAt
        A z k g).inv.1.geometry.coefficientHom = RingHom.id k
  rw [authoredExactGeneratedMateTargetToCanonicalPulledNorthwestIsoAt_inv_coefficient_id,
    authoredExactCanonicalPulledToGeneratedNorthwestIsoAt_inv_coefficient_id]
  rfl

/-- Pushing the source endpoint alignment along the top edge preserves its
coefficient identity. -/
theorem authoredExactBToGeneratedBaseNorthwestIsoAt_topPush_hom_coefficient_id
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    ((geomFiberTransportFunctor A.context.square.semantic.square.top).mapIso
      (authoredExactBToGeneratedBaseNorthwestIsoAt A z k g)).hom.1.geometry.coefficientHom =
      RingHom.id k := by
  change (geomFiberTransportMap A.context.square.semantic.square.top
      (authoredExactBToGeneratedBaseNorthwestIsoAt A z k g).hom).1.geometry.coefficientHom =
    RingHom.id k
  rw [geomFiberTransportMap_coefficientHom,
    authoredExactBToGeneratedBaseNorthwestIsoAt_hom_coefficient_id]

/-- Pushing the target endpoint alignment along the top edge preserves its
coefficient identity. -/
theorem authoredExactGeneratedPulledToTargetNorthwestIsoAt_topPush_hom_coefficient_id
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    ((geomFiberTransportFunctor A.context.square.semantic.square.top).mapIso
      (authoredExactGeneratedPulledToTargetNorthwestIsoAt A z k g)).hom.1.geometry.coefficientHom =
      RingHom.id k := by
  change (geomFiberTransportMap A.context.square.semantic.square.top
      (authoredExactGeneratedPulledToTargetNorthwestIsoAt A z k g).hom).1.geometry.coefficientHom =
    RingHom.id k
  rw [geomFiberTransportMap_coefficientHom,
    authoredExactGeneratedPulledToTargetNorthwestIsoAt_hom_coefficient_id]

/-! ## The complete mate coefficient -/

/-- The hom of the exact-derived five-factor Beck--Chevalley comparison fixes
the authored coefficient ring.  Each of its five factors is constructed from
the exact adjunction, the endpoint comparisons, or the generated mate. -/
theorem authoredExactBarAlphaIsoAt_hom_coefficient_id
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    (authoredExactBarAlphaIsoAt A z k g).hom.1.geometry.coefficientHom =
      RingHom.id k := by
  rw [authoredExactBarAlphaIsoAt_hom]
  change
    (authoredExactTopCounitIsoAt A z k g).hom.1.geometry.coefficientHom.comp
      (((geomFiberTransportFunctor A.context.square.semantic.square.top).mapIso
        (authoredExactGeneratedPulledToTargetNorthwestIsoAt A z k g)).hom.1.geometry.coefficientHom.comp
        ((authoredExactGeneratedMateTopPushIsoAt A z k g).hom.1.geometry.coefficientHom.comp
          (((geomFiberTransportFunctor A.context.square.semantic.square.top).mapIso
            (authoredExactBToGeneratedBaseNorthwestIsoAt A z k g)).hom.1.geometry.coefficientHom.comp
            (authoredExactUnitTopPushIsoAt A z k g).hom.1.geometry.coefficientHom))) =
      RingHom.id k
  rw [authoredExactTopCounitIsoAt_hom_coefficient_id,
    authoredExactGeneratedPulledToTargetNorthwestIsoAt_topPush_hom_coefficient_id,
    authoredExactGeneratedMateTopPushIsoAt_hom_coefficient_id,
    authoredExactBToGeneratedBaseNorthwestIsoAt_topPush_hom_coefficient_id,
    authoredExactUnitTopPushIsoAt_hom_coefficient_id]
  rfl

end AAT.AG.FullGeometryNormalization

#assert_standard_axioms_only AAT.AG.FullGeometryNormalization
