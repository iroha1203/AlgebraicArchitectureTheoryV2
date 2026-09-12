import ResearchLean.AG.FullGeometryNormalization.ExactDerivedPullbackComparison
import ResearchLean.AG.FullGeometryNormalization.ExactGeometryPullProjection
import ResearchLean.AG.FullGeometryNormalization.ExactGeometryTransportCounitIso

/-!
# Complete-geometry endpoints for the exact-derived comparison

This module realizes the four complete geometries occurring in G-122(B) from
one authored Beck--Chevalley square and one fixed-coefficient geometry at an
authored southwest cell.  The four realized edge inputs are recovered from the
finite presentation carried by the square.  Thus every pullback uses the exact
Cartesian cleavage from G-122(B1), while every pushforward uses the canonical
complete-geometry cocartesian transport.

## Implementation notes

The objects remain in the corresponding `GeomFiber`s instead of being cast to
bare `GeometryPackage`s.  This makes the endpoint incidence part of their type
and lets the later unit, counit, and generated-mate construction use the B1
functors directly.  Accepting four `RealizableHom`s or four prebuilt geometries
was rejected because that would detach the endpoints from the realization
provenance of the authored square.
-/

namespace AAT.AG.FullGeometryNormalization

universe u v

open CategoryTheory AtomFoundation GeometryTransport CrossStageCoherence
open DoctrineFiberProduct

set_option maxHeartbeats 3000000

/-! ## Edge realization provenance -/

/-- The realized northwest-to-southwest edge `pi_1`. -/
def authoredExactLeftInput
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) : RealizableHom U where
  semantic :=
    { source := A.context.square.semantic.square.northwest
      target := A.context.square.semantic.square.southwest
      hom := A.context.square.semantic.square.left }
  presentation :=
    (bcLeftPresentation A.context.square.presentation).toPresentation
  realization_eq := by
    rcases A with ⟨⟨⟨semantic, presentation, realization_eq⟩,
      lift, endpoint_eq⟩, twoCellBase, authored⟩
    cases realization_eq
    rfl

/-- The realized northwest-to-northeast edge `pi_2`. -/
def authoredExactTopInput
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) : RealizableHom U where
  semantic :=
    { source := A.context.square.semantic.square.northwest
      target := A.context.square.semantic.square.northeast
      hom := A.context.square.semantic.square.top }
  presentation :=
    (bcTopPresentation A.context.square.presentation).toPresentation
  realization_eq := by
    rcases A with ⟨⟨⟨semantic, presentation, realization_eq⟩,
      lift, endpoint_eq⟩, twoCellBase, authored⟩
    cases realization_eq
    rfl

/-- The realized southwest-to-southeast edge `sigma_1`. -/
def authoredExactBottomInput
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) : RealizableHom U where
  semantic :=
    { source := A.context.square.semantic.square.southwest
      target := A.context.square.semantic.square.southeast
      hom := A.context.square.semantic.square.bottom }
  presentation :=
    (bcBottomPresentation A.context.square.presentation).toPresentation
  realization_eq := by
    rcases A with ⟨⟨⟨semantic, presentation, realization_eq⟩,
      lift, endpoint_eq⟩, twoCellBase, authored⟩
    cases realization_eq
    rfl

/-- The realized northeast-to-southeast edge `sigma_2`. -/
def authoredExactRightInput
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) : RealizableHom U where
  semantic :=
    { source := A.context.square.semantic.square.northeast
      target := A.context.square.semantic.square.southeast
      hom := A.context.square.semantic.square.right }
  presentation :=
    (bcRightPresentation A.context.square.presentation).toPresentation
  realization_eq := by
    rcases A with ⟨⟨⟨semantic, presentation, realization_eq⟩,
      lift, endpoint_eq⟩, twoCellBase, authored⟩
    cases realization_eq
    rfl

/-! ## The four generated complete geometries -/

/-- The first pullback `(pi_1)^* g_z` in the northwest fiber. -/
noncomputable def authoredExactLeftPulledGeometryAt
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    GeomFiber A.context.square.semantic.square.northwest :=
  (exactGeometryPullFunctor (authoredExactLeftInput A)).obj
    (authoredSouthwestGeometryFiberAt A z k g)

/-- The direct-route endpoint
`G_z = (pi_2)_! (pi_1)^* g_z` in the northeast fiber. -/
noncomputable def authoredExactDirectGeometryAt
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    GeomFiber A.context.square.semantic.square.northeast :=
  (geomFiberTransportFunctor A.context.square.semantic.square.top).obj
    (authoredExactLeftPulledGeometryAt A z k g)

/-- The via-base endpoint
`H_z = (sigma_2)^* (sigma_1)_! g_z` in the northeast fiber. -/
noncomputable def authoredExactViaBaseGeometryAt
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    GeomFiber A.context.square.semantic.square.northeast :=
  (exactGeometryPullFunctor (authoredExactRightInput A)).obj
    (authoredExactTargetGeometryAt A z k g)

/-- The bottom-unit pullback `(sigma_1)^* q_z` in the southwest fiber. -/
noncomputable def authoredExactBottomPulledTargetGeometryAt
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    GeomFiber A.context.square.semantic.square.southwest :=
  (exactGeometryPullFunctor (authoredExactBottomInput A)).obj
    (authoredExactTargetGeometryAt A z k g)

/-- The generated-mate source
`B_z = (pi_1)^* (sigma_1)^* q_z` in the northwest fiber. -/
noncomputable def authoredExactGeneratedMateSourceGeometryAt
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    GeomFiber A.context.square.semantic.square.northwest :=
  (exactGeometryPullFunctor (authoredExactLeftInput A)).obj
    (authoredExactBottomPulledTargetGeometryAt A z k g)

/-- The generated-mate target
`T_z = (pi_2)^* (sigma_2)^* q_z` in the northwest fiber. -/
noncomputable def authoredExactGeneratedMateTargetGeometryAt
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    GeomFiber A.context.square.semantic.square.northwest :=
  (exactGeometryPullFunctor (authoredExactTopInput A)).obj
    (authoredExactViaBaseGeometryAt A z k g)

/-! ## Coefficient and core-projection APIs -/

/-- The direct-route endpoint retains the coefficient ring `k`.  As a simp
rule this normalizes the endpoint coefficient type to the fixed type `k`. -/
@[simp] theorem authoredExactDirectGeometryAt_coefficient
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    (authoredExactDirectGeometryAt A z k g).1.Coefficient = k := by
  change (authoredExactLeftPulledGeometryAt A z k g).1.Coefficient = k
  exact (exactGeometryPull_coefficient
    (authoredExactLeftInput A) (authoredSouthwestGeometryFiberAt A z k g)).trans
      rfl

/-- The via-base endpoint retains the coefficient ring `k`.  As a simp rule
this normalizes the endpoint coefficient type to the fixed type `k`. -/
@[simp] theorem authoredExactViaBaseGeometryAt_coefficient
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    (authoredExactViaBaseGeometryAt A z k g).1.Coefficient = k := by
  exact (exactGeometryPull_coefficient
    (authoredExactRightInput A) (authoredExactTargetGeometryAt A z k g)).trans
      rfl

/-- The generated-mate source retains the coefficient ring `k`.  As a simp
rule this normalizes the endpoint coefficient type to the fixed type `k`. -/
@[simp] theorem authoredExactGeneratedMateSourceGeometryAt_coefficient
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    (authoredExactGeneratedMateSourceGeometryAt A z k g).1.Coefficient = k := by
  change (exactGeometryPull (authoredExactLeftInput A)
      (authoredExactBottomPulledTargetGeometryAt A z k g)).1.Coefficient = k
  rw [exactGeometryPull_coefficient]
  change (exactGeometryPull (authoredExactBottomInput A)
      (authoredExactTargetGeometryAt A z k g)).1.Coefficient = k
  rw [exactGeometryPull_coefficient]
  rfl

/-- The generated-mate target retains the coefficient ring `k`.  As a simp
rule this normalizes the endpoint coefficient type to the fixed type `k`. -/
@[simp] theorem authoredExactGeneratedMateTargetGeometryAt_coefficient
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    (authoredExactGeneratedMateTargetGeometryAt A z k g).1.Coefficient = k := by
  change (exactGeometryPull (authoredExactTopInput A)
      (authoredExactViaBaseGeometryAt A z k g)).1.Coefficient = k
  rw [exactGeometryPull_coefficient]
  change (exactGeometryPull (authoredExactRightInput A)
      (authoredExactTargetGeometryAt A z k g)).1.Coefficient = k
  rw [exactGeometryPull_coefficient]
  rfl

/-- Core projection of the direct endpoint is the canonical top transport of
the selected core pullback along `pi_1`. -/
noncomputable def authoredExactDirectGeometryCoreIsoAt
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    (geometryFiberProjection A.context.square.semantic.square.northeast).obj
        (authoredExactDirectGeometryAt A z k g) ≅
      (coreFiberTransportFunctor A.context.square.semantic.square.top).obj
        ((selectedCoreFiberReindexFunctor (authoredExactLeftInput A)).obj
          ((geometryFiberProjection
            A.context.square.semantic.square.southwest).obj
              (authoredSouthwestGeometryFiberAt A z k g))) :=
  towerTransportComparisonApp A.context.square.semantic.square.top
      (authoredExactLeftPulledGeometryAt A z k g) ≪≫
    (coreFiberTransportFunctor A.context.square.semantic.square.top).mapIso
      (exactGeometryPullProjectionIsoApp (authoredExactLeftInput A)
        (authoredSouthwestGeometryFiberAt A z k g))

/-- Core projection of the via-base endpoint is the selected core pullback of
the canonical bottom transport of the original core. -/
noncomputable def authoredExactViaBaseGeometryCoreIsoAt
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    (geometryFiberProjection A.context.square.semantic.square.northeast).obj
        (authoredExactViaBaseGeometryAt A z k g) ≅
      (selectedCoreFiberReindexFunctor (authoredExactRightInput A)).obj
        ((coreFiberTransportFunctor A.context.square.semantic.square.bottom).obj
          ((geometryFiberProjection
            A.context.square.semantic.square.southwest).obj
              (authoredSouthwestGeometryFiberAt A z k g))) :=
  exactGeometryPullProjectionIsoApp (authoredExactRightInput A)
      (authoredExactTargetGeometryAt A z k g) ≪≫
    (selectedCoreFiberReindexFunctor (authoredExactRightInput A)).mapIso
      (towerTransportComparisonApp A.context.square.semantic.square.bottom
        (authoredSouthwestGeometryFiberAt A z k g))

end AAT.AG.FullGeometryNormalization

#assert_standard_axioms_only AAT.AG.FullGeometryNormalization
