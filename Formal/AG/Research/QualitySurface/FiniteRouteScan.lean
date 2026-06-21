import Formal.AG.Research.QualitySurface.FailingSlotCertificate

/-!
Cycle 55 evidence for `G-aat-quality-surface-01`.

This file turns the route-family exact locus into a finite scan when a supplied
slot list covers the route-slot type.  The scan is relative to the supplied list:
it does not enumerate an arbitrary type on its own, choose a canonical failing
slot, synthesize repairs, validate ArchMap observations, or judge whole-codebase
quality.
-/

namespace Formal.AG.Research
namespace QualitySurface
namespace FiniteRouteScan

open SourceRefExactVisualizationCriterion
open ParametrizedSelectedCorrectionSystem
open MultiRouteCorrectionSystem
open FiniteRouteFamilyExactLocus
open FailingSlotCertificate
open RepairStage
open RouteSlot

universe u

/-! ## Finite scan for supplied route-slot lists -/

/-- A supplied finite slot list covers every route slot. -/
def SlotListCovers {Slot : Type u} (slots : List Slot) : Prop :=
  ∀ slot, slot ∈ slots

/-- All listed slots are at the all-branches stage. -/
def ListedSlotsAllBranches {Slot : Type u}
    (assignment : StageAssignment Slot) (slots : List Slot) : Prop :=
  ∀ slot, slot ∈ slots -> assignment slot = allBranches

/-- Boolean scan for whether every listed slot is at the all-branches stage. -/
def listedAllBranchesScan {Slot : Type u}
    (assignment : StageAssignment Slot) : List Slot -> Bool
  | [] => true
  | slot :: rest =>
      decide (assignment slot = allBranches) &&
        listedAllBranchesScan assignment rest

/-- The boolean scan is true exactly when every listed slot is all-branches. -/
theorem listedAllBranchesScan_eq_true_iff {Slot : Type u}
    (assignment : StageAssignment Slot) :
    ∀ slots,
      listedAllBranchesScan assignment slots = true ↔
        ListedSlotsAllBranches assignment slots
  | [] => by
      constructor
      · intro _ slot hmem
        cases hmem
      · intro _
        rfl
  | slot :: rest => by
      constructor
      · intro hscan listedSlot hmem
        have hscanPair :
            decide (assignment slot = allBranches) = true ∧
              listedAllBranchesScan assignment rest = true := by
          simpa [listedAllBranchesScan] using hscan
        have hhead : assignment slot = allBranches := by
          exact of_decide_eq_true hscanPair.left
        have htail :
            ListedSlotsAllBranches assignment rest :=
          (listedAllBranchesScan_eq_true_iff assignment rest).mp
            hscanPair.right
        cases hmem with
        | head =>
            exact hhead
        | tail _ hlisted =>
            exact htail listedSlot hlisted
      · intro hall
        have hhead : assignment slot = allBranches :=
          hall slot (by simp)
        have htail :
            ListedSlotsAllBranches assignment rest := by
          intro listedSlot hmem
          exact hall listedSlot (by simp [hmem])
        have htailScan :
            listedAllBranchesScan assignment rest = true :=
          (listedAllBranchesScan_eq_true_iff assignment rest).mpr htail
        simp [listedAllBranchesScan, hhead, htailScan]

/-- A supplied covering list turns family exactness into the finite scan. -/
theorem assignmentFamilySourceRefExact_iff_listedScan {Slot : Type u}
    (assignment : StageAssignment Slot)
    (slots : List Slot)
    (hcover : SlotListCovers slots) :
    AssignmentFamilySourceRefExact assignment ↔
      listedAllBranchesScan assignment slots = true := by
  constructor
  · intro hexact
    apply (listedAllBranchesScan_eq_true_iff assignment slots).mpr
    intro slot _hmem
    exact (assignmentFamilySourceRefExact_iff_allBranches
      assignment).mp hexact slot
  · intro hscan
    apply (assignmentFamilySourceRefExact_iff_allBranches assignment).mpr
    intro slot
    exact ((listedAllBranchesScan_eq_true_iff assignment slots).mp
      hscan) slot (hcover slot)

/--
If a listed slot fails the scan, it produces the same failing-slot certificate
used by the exactness obstruction interface.
-/
def listedFailingSlotCertificate {Slot : Type u}
    {assignment : StageAssignment Slot}
    {slots : List Slot}
    {slot : Slot}
    (_hmem : slot ∈ slots)
    (hfail : assignment slot ≠ allBranches) :
    FailingSlotWitness assignment where
  slot := slot
  fails := hfail

/-! ## Concrete mixed route-slot scan -/

/-- A supplied finite list of the two concrete route slots. -/
def routeSlotScanOrder : List RouteSlot :=
  [primary, secondary]

/-- The supplied route-slot scan order covers the concrete route-slot type. -/
theorem routeSlotScanOrder_covers :
    SlotListCovers routeSlotScanOrder := by
  intro slot
  cases slot <;> simp [routeSlotScanOrder]

/-- The mixed two-slot assignment fails the finite all-branches scan. -/
theorem mixedRouteSlot_listedAllBranchesScan_false :
    listedAllBranchesScan mixedRouteSlotAssignment routeSlotScanOrder = false := by
  simp [listedAllBranchesScan, routeSlotScanOrder, mixedRouteSlotAssignment]

/-- For the mixed two-slot assignment, family exactness is exactly the scan result. -/
theorem mixedRouteSlot_familyExact_iff_listedScan :
    AssignmentFamilySourceRefExact mixedRouteSlotAssignment ↔
      listedAllBranchesScan mixedRouteSlotAssignment routeSlotScanOrder = true :=
  assignmentFamilySourceRefExact_iff_listedScan
    mixedRouteSlotAssignment routeSlotScanOrder routeSlotScanOrder_covers

/-- The concrete scan exposes the secondary-slot failing certificate. -/
def mixedRouteSlot_scanFailingCertificate :
    FailingSlotWitness mixedRouteSlotAssignment :=
  listedFailingSlotCertificate
    (assignment := mixedRouteSlotAssignment)
    (slots := routeSlotScanOrder)
    (slot := secondary)
    (by simp [routeSlotScanOrder])
    mixedRouteSlotAssignment_secondary_fails

/-- The scan-exposed certificate obstructs mixed route-family exactness. -/
theorem mixedRouteSlot_scanCertificate_obstructs :
    ¬ AssignmentFamilySourceRefExact mixedRouteSlotAssignment :=
  failingSlotCertificate_obstructs_familyExact
    mixedRouteSlot_scanFailingCertificate

/-! ## Theorem package -/

/--
Cycle-55 theorem package: a supplied covering finite slot list computes the
route-family exactness gate, and the mixed two-slot scan exposes the concrete
secondary-slot failure certificate.
-/
theorem finiteRouteScan_package :
    (∀ {Slot : Type u} (assignment : StageAssignment Slot)
      (slots : List Slot), SlotListCovers slots ->
        (AssignmentFamilySourceRefExact assignment ↔
          listedAllBranchesScan assignment slots = true)) ∧
    (listedAllBranchesScan mixedRouteSlotAssignment routeSlotScanOrder = false) ∧
    (AssignmentFamilySourceRefExact mixedRouteSlotAssignment ↔
      listedAllBranchesScan mixedRouteSlotAssignment routeSlotScanOrder = true) ∧
    ¬ AssignmentFamilySourceRefExact mixedRouteSlotAssignment := by
  exact ⟨assignmentFamilySourceRefExact_iff_listedScan,
    mixedRouteSlot_listedAllBranchesScan_false,
    mixedRouteSlot_familyExact_iff_listedScan,
    mixedRouteSlot_scanCertificate_obstructs⟩

end FiniteRouteScan
end QualitySurface
end Formal.AG.Research
