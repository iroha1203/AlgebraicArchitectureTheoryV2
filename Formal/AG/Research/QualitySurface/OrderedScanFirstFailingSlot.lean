import Formal.AG.Research.QualitySurface.FiniteRouteScan

/-!
Cycle 56 evidence for `G-aat-quality-surface-01`.

This file refines the finite route scan into an ordered certificate selector.
The first failing slot is canonical only relative to the supplied ordered slot
list.  It does not enumerate an arbitrary type, prove global minimality,
synthesize repairs, validate ArchMap observations, or judge whole-codebase
quality.
-/

namespace Formal.AG.Research
namespace QualitySurface
namespace OrderedScanFirstFailingSlot

open SourceRefExactVisualizationCriterion
open ParametrizedSelectedCorrectionSystem
open MultiRouteCorrectionSystem
open FiniteRouteFamilyExactLocus
open FailingSlotCertificate
open FiniteRouteScan
open RepairStage
open RouteSlot

universe u

/-! ## Ordered first-failing-slot scan -/

/-- The first listed slot that is not at the all-branches stage. -/
def firstFailingSlot? {Slot : Type u}
    (assignment : StageAssignment Slot) : List Slot -> Option Slot
  | [] => none
  | slot :: rest =>
      if assignment slot = allBranches then
        firstFailingSlot? assignment rest
      else
        some slot

/-- A first failing slot returned by the ordered scan is a member of the supplied list. -/
theorem firstFailingSlot?_some_mem {Slot : Type u}
    (assignment : StageAssignment Slot) :
    ∀ {slots : List Slot} {slot : Slot},
      firstFailingSlot? assignment slots = some slot ->
        slot ∈ slots
  | [], _slot, hsome => by
      cases hsome
  | head :: rest, slot, hsome => by
      by_cases hhead : assignment head = allBranches
      · have htail :
            firstFailingSlot? assignment rest = some slot := by
          simpa [firstFailingSlot?, hhead] using hsome
        exact List.mem_cons_of_mem head
          (firstFailingSlot?_some_mem assignment htail)
      · have hslot : slot = head := by
          simpa [firstFailingSlot?, hhead] using hsome.symm
        subst hslot
        simp

/-- A first failing slot returned by the ordered scan really fails all-branches. -/
theorem firstFailingSlot?_some_fails {Slot : Type u}
    (assignment : StageAssignment Slot) :
    ∀ {slots : List Slot} {slot : Slot},
      firstFailingSlot? assignment slots = some slot ->
        assignment slot ≠ allBranches
  | [], _slot, hsome => by
      cases hsome
  | head :: rest, slot, hsome => by
      by_cases hhead : assignment head = allBranches
      · have htail :
            firstFailingSlot? assignment rest = some slot := by
          simpa [firstFailingSlot?, hhead] using hsome
        exact firstFailingSlot?_some_fails assignment htail
      · have hslot : slot = head := by
          simpa [firstFailingSlot?, hhead] using hsome.symm
        subst hslot
        exact hhead

/-- The ordered scan returns none exactly when every listed slot is all-branches. -/
theorem firstFailingSlot?_none_iff_listedAllBranches {Slot : Type u}
    (assignment : StageAssignment Slot) :
    ∀ slots,
      firstFailingSlot? assignment slots = none ↔
        ListedSlotsAllBranches assignment slots
  | [] => by
      constructor
      · intro _ slot hmem
        cases hmem
      · intro _
        rfl
  | head :: rest => by
      constructor
      · intro hnone listedSlot hmem
        by_cases hhead : assignment head = allBranches
        · have htail :
              firstFailingSlot? assignment rest = none := by
            simpa [firstFailingSlot?, hhead] using hnone
          cases hmem with
          | head =>
              exact hhead
          | tail _ hlisted =>
              exact ((firstFailingSlot?_none_iff_listedAllBranches
                assignment rest).mp htail) listedSlot hlisted
        · have hsome :
              firstFailingSlot? assignment (head :: rest) = some head := by
            simp [firstFailingSlot?, hhead]
          rw [hsome] at hnone
          cases hnone
      · intro hall
        have hhead : assignment head = allBranches := hall head (by simp)
        have htail :
            ListedSlotsAllBranches assignment rest := by
          intro listedSlot hmem
          exact hall listedSlot (by simp [hmem])
        have htailNone :
            firstFailingSlot? assignment rest = none :=
          (firstFailingSlot?_none_iff_listedAllBranches assignment rest).mpr
            htail
        simp [firstFailingSlot?, hhead, htailNone]

/-- A returned first failing slot gives a reportable failing-slot certificate. -/
def firstFailingSlot?_failingCertificate {Slot : Type u}
    {assignment : StageAssignment Slot}
    {slots : List Slot}
    {slot : Slot}
    (hfirst : firstFailingSlot? assignment slots = some slot) :
    FailingSlotWitness assignment where
  slot := slot
  fails := firstFailingSlot?_some_fails assignment hfirst

/-! ## Prefix exactness relative to the supplied order -/

/--
Every listed slot before the returned target slot is all-branches.  This is an
order-relative statement, not a global minimality claim.
-/
def PrefixBeforeFirstAllBranches {Slot : Type u} [DecidableEq Slot]
    (assignment : StageAssignment Slot) (target : Slot) : List Slot -> Prop
  | [] => True
  | slot :: rest =>
      if slot = target then
        True
      else
        assignment slot = allBranches ∧
          PrefixBeforeFirstAllBranches assignment target rest

/-- The first-failing-slot scan carries prefix exactness for the supplied order. -/
theorem firstFailingSlot?_some_prefixAllBranches {Slot : Type u}
    [DecidableEq Slot]
    (assignment : StageAssignment Slot) :
    ∀ {slots : List Slot} {slot : Slot},
      firstFailingSlot? assignment slots = some slot ->
        PrefixBeforeFirstAllBranches assignment slot slots
  | [], _slot, hsome => by
      cases hsome
  | head :: rest, slot, hsome => by
      by_cases hhead : assignment head = allBranches
      · have htail :
            firstFailingSlot? assignment rest = some slot := by
          simpa [firstFailingSlot?, hhead] using hsome
        by_cases hslot : head = slot
        · simp [PrefixBeforeFirstAllBranches, hslot]
        · simp [PrefixBeforeFirstAllBranches, hslot, hhead,
            firstFailingSlot?_some_prefixAllBranches assignment htail]
      · have hslot : slot = head := by
          simpa [firstFailingSlot?, hhead] using hsome.symm
        subst hslot
        simp [PrefixBeforeFirstAllBranches]

/-- A returned first failing slot obstructs family source-ref exactness. -/
theorem firstFailingSlot?_some_obstructs_familyExact {Slot : Type u}
    {assignment : StageAssignment Slot}
    {slots : List Slot}
    {slot : Slot}
    (hfirst : firstFailingSlot? assignment slots = some slot) :
    ¬ AssignmentFamilySourceRefExact assignment :=
  failingSlotCertificate_obstructs_familyExact
    (firstFailingSlot?_failingCertificate hfirst)

/-- On a covering slot list, family exactness is equivalent to no first failing slot. -/
theorem assignmentFamilySourceRefExact_iff_firstFailingSlot?_none {Slot : Type u}
    (assignment : StageAssignment Slot)
    (slots : List Slot)
    (hcover : SlotListCovers slots) :
    AssignmentFamilySourceRefExact assignment ↔
      firstFailingSlot? assignment slots = none := by
  constructor
  · intro hexact
    apply (firstFailingSlot?_none_iff_listedAllBranches
      assignment slots).mpr
    intro slot _hmem
    exact (assignmentFamilySourceRefExact_iff_allBranches
      assignment).mp hexact slot
  · intro hnone
    apply (assignmentFamilySourceRefExact_iff_allBranches assignment).mpr
    intro slot
    exact ((firstFailingSlot?_none_iff_listedAllBranches
      assignment slots).mp hnone) slot (hcover slot)

/-! ## Concrete mixed route-slot order -/

/-- The ordered scan selects the secondary slot for the mixed two-slot assignment. -/
theorem mixedRouteSlot_firstFailingSlot?_secondary :
    firstFailingSlot? mixedRouteSlotAssignment routeSlotScanOrder =
      some secondary := by
  simp [firstFailingSlot?, routeSlotScanOrder, mixedRouteSlotAssignment]

/-- The selected secondary slot is the first-failing certificate for the mixed assignment. -/
def mixedRouteSlot_firstFailingCertificate :
    FailingSlotWitness mixedRouteSlotAssignment :=
  firstFailingSlot?_failingCertificate
    mixedRouteSlot_firstFailingSlot?_secondary

/-- The ordered first-failing certificate obstructs mixed route-family exactness. -/
theorem mixedRouteSlot_firstFailingCertificate_obstructs :
    ¬ AssignmentFamilySourceRefExact mixedRouteSlotAssignment :=
  failingSlotCertificate_obstructs_familyExact
    mixedRouteSlot_firstFailingCertificate

/-- In the concrete route order, the primary prefix is exact before the secondary failure. -/
theorem mixedRouteSlot_firstFailing_prefixAllBranches :
    PrefixBeforeFirstAllBranches
      mixedRouteSlotAssignment secondary routeSlotScanOrder := by
  exact firstFailingSlot?_some_prefixAllBranches
    mixedRouteSlotAssignment mixedRouteSlot_firstFailingSlot?_secondary

/-! ## Theorem package -/

/--
Cycle-56 theorem package: an ordered covering slot list turns family exactness
into absence of a first failing slot, and a returned slot gives the reportable
failing-slot certificate.
-/
theorem orderedScanFirstFailingSlot_package :
    (∀ {Slot : Type u} (assignment : StageAssignment Slot)
      (slots : List Slot), SlotListCovers slots ->
        (AssignmentFamilySourceRefExact assignment ↔
          firstFailingSlot? assignment slots = none)) ∧
    (∀ {Slot : Type u} [DecidableEq Slot] {assignment : StageAssignment Slot}
      {slots : List Slot} {slot : Slot},
        firstFailingSlot? assignment slots = some slot ->
          slot ∈ slots ∧
            assignment slot ≠ allBranches ∧
            PrefixBeforeFirstAllBranches assignment slot slots ∧
            ¬ AssignmentFamilySourceRefExact assignment) ∧
    (firstFailingSlot? mixedRouteSlotAssignment routeSlotScanOrder =
      some secondary) ∧
    ¬ AssignmentFamilySourceRefExact mixedRouteSlotAssignment := by
  exact ⟨assignmentFamilySourceRefExact_iff_firstFailingSlot?_none,
    fun hfirst =>
      ⟨firstFailingSlot?_some_mem _ hfirst,
        firstFailingSlot?_some_fails _ hfirst,
        firstFailingSlot?_some_prefixAllBranches _ hfirst,
        firstFailingSlot?_some_obstructs_familyExact hfirst⟩,
    mixedRouteSlot_firstFailingSlot?_secondary,
    mixedRouteSlot_firstFailingCertificate_obstructs⟩

end OrderedScanFirstFailingSlot
end QualitySurface
end Formal.AG.Research
