import ResearchLean.AG.FullGeometryNormalization.ExactDerivedDirectCanonicalBridge
import ResearchLean.AG.FullGeometryNormalization.ExactGeometryTransportUnitIso
import ResearchLean.AG.FullGeometryNormalization.ExactGeometryTransportCounitIso

/-!
# Exact-derived complete-geometry mate composite

This module inserts the realization-generated endpoint comparisons around the
actual G-118 mate and composes them with the exact transport unit and counit.
It constructs the literal unit endpoint isomorphism `a_z`, the literal counit
endpoint isomorphism `b_z`, and the resulting complete-geometry comparison
`barAlpha_z` required by G-122(B2).

## Implementation notes

The unit and counit isomorphisms are kept separate from the endpoint-change
isomorphisms, matching the five factors in the mathematical mate formula.
Collapsing these factors into one opaque arrow was rejected because it would
hide which terms come from the exact adjunction and which come from the
realization-proven cleavage comparisons.  Every factor is constructed from
`A`, `z`, `k`, and `g`; no endpoint, comparison morphism, inverse, or
invertibility certificate is accepted from a caller.
-/

namespace AAT.AG.FullGeometryNormalization

universe u v

open CategoryTheory AtomFoundation GeometryTransport CrossStageCoherence
open DoctrineFiberProduct

set_option maxHeartbeats 3000000

/-! ## Endpoint comparisons -/

/-- The literal generated-mate source `B_z`, compared through the canonical
authored base endpoint with the actual generated base-route endpoint. -/
noncomputable def authoredExactBToGeneratedBaseNorthwestIsoAt
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    authoredExactGeneratedMateSourceGeometryAt A z k g ≅
      authoredExactGeneratedBaseRouteNorthwestAt A z k g :=
  authoredExactGeneratedMateSourceToCanonicalBaseNorthwestIsoAt A z k g ≪≫
    authoredExactCanonicalBaseToGeneratedNorthwestIsoAt A z k g

/-- The actual generated pulled-route endpoint, compared through the canonical
authored pulled endpoint with the literal generated-mate target `T_z`. -/
noncomputable def authoredExactGeneratedPulledToTargetNorthwestIsoAt
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    authoredExactGeneratedPulledRouteNorthwestAt A z k g ≅
      authoredExactGeneratedMateTargetGeometryAt A z k g :=
  (authoredExactCanonicalPulledToGeneratedNorthwestIsoAt A z k g).symm ≪≫
    (authoredExactGeneratedMateTargetToCanonicalPulledNorthwestIsoAt
      A z k g).symm

/-! ## Literal unit and counit endpoint isomorphisms -/

/-- `a_z`: push along the top edge of the left pullback of the exact bottom
transport unit.  Its codomain is literally `(pi_2)_! B_z`; endpoint alignment
with the generated route is kept as a separate factor. -/
noncomputable def authoredExactUnitTopPushIsoAt
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    authoredExactDirectGeometryAt A z k g ≅
      (geomFiberTransportFunctor
        A.context.square.semantic.square.top).obj
          (authoredExactGeneratedMateSourceGeometryAt A z k g) := by
  let unit := (exactGeometryTransportPullUnit
    (authoredExactBottomInput A)).app
      (authoredSouthwestGeometryFiberAt A z k g)
  letI : IsIso unit := exactGeometryTransportPullUnit_app_isIso
    (authoredExactBottomInput A)
    (authoredSouthwestGeometryFiberAt A z k g)
  exact (geomFiberTransportFunctor
    A.context.square.semantic.square.top).mapIso
      ((exactGeometryPullFunctor (authoredExactLeftInput A)).mapIso
        (asIso unit))

/-- The literal unit endpoint isomorphism fixes the authored coefficient
ring.  This is inherited successively through exact pull and top push. -/
theorem authoredExactUnitTopPushIsoAt_hom_coefficient_id
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    (authoredExactUnitTopPushIsoAt A z k g).hom.1.geometry.coefficientHom =
      RingHom.id k := by
  dsimp [authoredExactUnitTopPushIsoAt]
  change
    (geomFiberTransportMap A.context.square.semantic.square.top
      (exactGeometryPullMap (authoredExactLeftInput A)
        ((exactGeometryTransportPullUnit (authoredExactBottomInput A)).app
          (authoredSouthwestGeometryFiberAt A z k g)))).1.geometry.coefficientHom =
      RingHom.id k
  rw [geomFiberTransportMap_coefficientHom,
    exactGeometryPullMap_coefficientHom,
    exactGeometryTransportPullUnit_app_coefficientHom]
  rfl

/-- `b_z`: the exact top transport counit at the via-base endpoint.  Its
domain is literally `(pi_2)_! T_z`; endpoint alignment with the generated
route is kept as a separate factor. -/
noncomputable def authoredExactTopCounitIsoAt
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    (geomFiberTransportFunctor
        A.context.square.semantic.square.top).obj
          (authoredExactGeneratedMateTargetGeometryAt A z k g) ≅
      authoredExactViaBaseGeometryAt A z k g := by
  let counit := (exactGeometryTransportPullCounit
    (authoredExactTopInput A)).app
      (authoredExactViaBaseGeometryAt A z k g)
  letI : IsIso counit := exactGeometryTransportPullCounit_app_isIso
    (authoredExactTopInput A) (authoredExactViaBaseGeometryAt A z k g)
  exact asIso counit

/-- The literal counit endpoint isomorphism fixes the authored coefficient
ring, as forced by the exact top transport triangle. -/
theorem authoredExactTopCounitIsoAt_hom_coefficient_id
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    (authoredExactTopCounitIsoAt A z k g).hom.1.geometry.coefficientHom =
      RingHom.id k := by
  simpa [authoredExactTopCounitIsoAt] using
    exactGeometryTransportPullCounit_app_coefficientHom
      (authoredExactTopInput A) (authoredExactViaBaseGeometryAt A z k g)

/-! ## The five-factor complete mate -/

/-- The generated G-118 mate itself, transported to the authored northwest
fiber and pushed along the original top edge, as an isomorphism. -/
noncomputable def authoredExactGeneratedMateTopPushIsoAt
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    (geomFiberTransportFunctor
        A.context.square.semantic.square.top).obj
          (authoredExactGeneratedBaseRouteNorthwestAt A z k g) ≅
      (geomFiberTransportFunctor
        A.context.square.semantic.square.top).obj
          (authoredExactGeneratedPulledRouteNorthwestAt A z k g) := by
  let mate := authoredExactGeneratedMateTopPushAt A z k g
  letI : IsIso mate := authoredExactGeneratedMateTopPushAt_isIso A z k g
  exact asIso mate

/-- The isomorphism wrapper of the pushed G-118 mate retains its established
coefficient identity. -/
theorem authoredExactGeneratedMateTopPushIsoAt_hom_coefficient_id
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    (authoredExactGeneratedMateTopPushIsoAt A z k g).hom.1.geometry.coefficientHom =
      RingHom.id k := by
  simpa [authoredExactGeneratedMateTopPushIsoAt] using
    authoredExactGeneratedMateTopPushAt_coefficient_id A z k g

/-- `barAlpha_z`: the exact complete-geometry Beck--Chevalley comparison.
The five displayed factors are `a_z`, source endpoint alignment, the pushed
G-118 mate, target endpoint alignment, and `b_z`, in that order. -/
noncomputable def authoredExactBarAlphaIsoAt
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    authoredExactDirectGeometryAt A z k g ≅
      authoredExactViaBaseGeometryAt A z k g :=
  authoredExactUnitTopPushIsoAt A z k g ≪≫
    (geomFiberTransportFunctor
      A.context.square.semantic.square.top).mapIso
        (authoredExactBToGeneratedBaseNorthwestIsoAt A z k g) ≪≫
    authoredExactGeneratedMateTopPushIsoAt A z k g ≪≫
    (geomFiberTransportFunctor
      A.context.square.semantic.square.top).mapIso
        (authoredExactGeneratedPulledToTargetNorthwestIsoAt A z k g) ≪≫
    authoredExactTopCounitIsoAt A z k g

/-- The hom of `barAlpha_z` is definitionally the required five-factor
mate composite.  This API keeps downstream projection and coefficient proofs
independent of the implementation body of the isomorphism. -/
theorem authoredExactBarAlphaIsoAt_hom
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    (authoredExactBarAlphaIsoAt A z k g).hom =
      (authoredExactUnitTopPushIsoAt A z k g).hom ≫
        (geomFiberTransportFunctor
          A.context.square.semantic.square.top).map
            (authoredExactBToGeneratedBaseNorthwestIsoAt A z k g).hom ≫
        (authoredExactGeneratedMateTopPushIsoAt A z k g).hom ≫
        (geomFiberTransportFunctor
          A.context.square.semantic.square.top).map
            (authoredExactGeneratedPulledToTargetNorthwestIsoAt A z k g).hom ≫
        (authoredExactTopCounitIsoAt A z k g).hom := by
  rfl

end AAT.AG.FullGeometryNormalization

#assert_standard_axioms_only AAT.AG.FullGeometryNormalization
