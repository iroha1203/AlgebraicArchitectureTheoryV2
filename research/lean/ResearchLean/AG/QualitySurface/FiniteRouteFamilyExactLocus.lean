import ResearchLean.AG.QualitySurface.MultiRouteCorrectionSystem

/-!
Cycle 53 evidence for `G-aat-quality-surface-01`.

This file generalizes the two-route staged correction family to an arbitrary
route-slot family.  A staged assignment is family source-ref exact exactly when
every route slot is at the all-branches stage.  Exactness is upward closed
under pointwise stage order, and any failing slot obstructs family exactness.

The claim is relative to supplied route slots, staged selected correction
semantics, and the explicit source-ref packet bridge.  It does not assert an
arbitrary repair planner, runtime patch synthesis, source extraction
completeness, ArchMap correctness, or whole-codebase quality.
-/

namespace ResearchLean.AG
namespace QualitySurface
namespace FiniteRouteFamilyExactLocus

open CodebaseTracePacket
open SourceRefExactVisualizationCriterion
open RouteDefectSupportTheory
open SelectedRouteDefectSupportHitting
open SelectedRouteFamilyExactness
open ParametrizedSelectedCorrectionSystem
open ParametrizedLossAwareAtlas
open MultiRouteCorrectionSystem
open RepairStage
open RouteSlot

universe u

/-! ## Arbitrary route-slot staged assignments -/

/-- A staged selected correction assignment over a route-slot family. -/
abbrev StageAssignment (Slot : Type u) :=
  Slot -> RepairStage

/-- Left packets for a staged route-slot family. -/
def assignmentFamilyLeft {Slot : Type u}
    (assignment : StageAssignment Slot) : Slot -> SourceRefPacket :=
  fun slot => correctedVisibleRouteLeft (stagedCorrection (assignment slot))

/-- Right packets for a staged route-slot family. -/
def assignmentFamilyRight {Slot : Type u} : Slot -> SourceRefPacket :=
  fun _slot => visibleRouteRight

/-- Source-ref exactness of a staged route-slot family. -/
def AssignmentFamilySourceRefExact {Slot : Type u}
    (assignment : StageAssignment Slot) : Prop :=
  FamilySourceRefExact
    (assignmentFamilyLeft assignment) assignmentFamilyRight

/-- Every route slot is at the all-branches stage. -/
def AssignmentAllBranches {Slot : Type u}
    (assignment : StageAssignment Slot) : Prop :=
  ∀ slot, assignment slot = allBranches

/-- A staged route-slot family is exact exactly when every slot is all-branches. -/
theorem assignmentFamilySourceRefExact_iff_allBranches {Slot : Type u}
    (assignment : StageAssignment Slot) :
    AssignmentFamilySourceRefExact assignment ↔
      AssignmentAllBranches assignment := by
  constructor
  · intro hexact slot
    exact (stagedCorrection_exact_iff_allBranches
      (assignment slot)).mp (by
        simpa [AssignmentFamilySourceRefExact, assignmentFamilyLeft,
          assignmentFamilyRight, CorrectionSourceRefExact] using hexact slot)
  · intro hall slot
    simpa [AssignmentFamilySourceRefExact, assignmentFamilyLeft,
      assignmentFamilyRight, CorrectionSourceRefExact, hall slot]
      using stagedCorrection_allBranches_exact

/-! ## Pointwise stage order -/

/-- Pointwise stage order on staged route-slot assignments. -/
def AssignmentLe {Slot : Type u}
    (left right : StageAssignment Slot) : Prop :=
  ∀ slot, StageLe (left slot) (right slot)

/-- Family exactness is upward closed under pointwise stage order. -/
theorem assignmentFamilySourceRefExact_upwardClosed {Slot : Type u}
    {left right : StageAssignment Slot}
    (hle : AssignmentLe left right)
    (hexact : AssignmentFamilySourceRefExact left) :
    AssignmentFamilySourceRefExact right := by
  have hallLeft :=
    (assignmentFamilySourceRefExact_iff_allBranches left).mp hexact
  apply (assignmentFamilySourceRefExact_iff_allBranches right).mpr
  intro slot
  exact stageLe_allBranches_right (by
    simpa [hallLeft slot] using hle slot)

/-- A failing slot obstructs exactness of the whole route-slot family. -/
theorem failingSlot_obstructs_assignmentFamilyExact {Slot : Type u}
    (assignment : StageAssignment Slot)
    (slot : Slot)
    (hslot : assignment slot ≠ allBranches) :
    ¬ AssignmentFamilySourceRefExact assignment := by
  intro hexact
  have hall :=
    (assignmentFamilySourceRefExact_iff_allBranches assignment).mp hexact
  exact hslot (hall slot)

/-! ## Concrete mixed finite assignment as an instance -/

/-- The mixed two-slot assignment from Cycle 52 as an arbitrary-family instance. -/
def mixedRouteSlotAssignment : StageAssignment RouteSlot
  | primary => allBranches
  | secondary => obligationOnly

/-- The mixed assignment has an exact primary slot. -/
theorem mixedRouteSlotAssignment_primary_sourceRefExact :
    SourceRefExactVisualization
      SourceRefTupleBridge.endpointGridCertificate
      SourceRefTupleBridge.endpointGridCertificate
      (assignmentFamilyLeft mixedRouteSlotAssignment primary)
      (assignmentFamilyRight primary) := by
  simpa [assignmentFamilyLeft, assignmentFamilyRight,
    mixedRouteSlotAssignment, CorrectionSourceRefExact]
    using stagedCorrection_allBranches_exact

/-- The secondary slot is a failing slot in the mixed assignment. -/
theorem mixedRouteSlotAssignment_secondary_fails :
    mixedRouteSlotAssignment secondary ≠ allBranches := by
  intro hstage
  cases hstage

/-- The mixed assignment is not family exact. -/
theorem mixedRouteSlotAssignment_not_familyExact :
    ¬ AssignmentFamilySourceRefExact mixedRouteSlotAssignment :=
  failingSlot_obstructs_assignmentFamilyExact
    mixedRouteSlotAssignment secondary
    mixedRouteSlotAssignment_secondary_fails

/-! ## Theorem package -/

/--
Cycle-53 theorem package: arbitrary staged route-slot families are exact
exactly when every slot is all-branches; exactness is upward closed under
pointwise stage order; any failing slot obstructs family exactness.
-/
theorem finiteRouteFamilyExactLocus_package :
    (∀ {Slot : Type u} (assignment : StageAssignment Slot),
      AssignmentFamilySourceRefExact assignment ↔
        AssignmentAllBranches assignment) ∧
    (∀ {Slot : Type u} {left right : StageAssignment Slot},
      AssignmentLe left right ->
        AssignmentFamilySourceRefExact left ->
          AssignmentFamilySourceRefExact right) ∧
    (∀ {Slot : Type u} (assignment : StageAssignment Slot) (slot : Slot),
      assignment slot ≠ allBranches ->
        ¬ AssignmentFamilySourceRefExact assignment) ∧
    SourceRefExactVisualization
      SourceRefTupleBridge.endpointGridCertificate
      SourceRefTupleBridge.endpointGridCertificate
      (assignmentFamilyLeft mixedRouteSlotAssignment primary)
      (assignmentFamilyRight primary) ∧
    mixedRouteSlotAssignment secondary ≠ allBranches ∧
    ¬ AssignmentFamilySourceRefExact mixedRouteSlotAssignment := by
  exact ⟨assignmentFamilySourceRefExact_iff_allBranches,
    fun hle hexact =>
      assignmentFamilySourceRefExact_upwardClosed hle hexact,
    fun assignment slot hslot =>
      failingSlot_obstructs_assignmentFamilyExact assignment slot hslot,
    mixedRouteSlotAssignment_primary_sourceRefExact,
    mixedRouteSlotAssignment_secondary_fails,
    mixedRouteSlotAssignment_not_familyExact⟩

end FiniteRouteFamilyExactLocus
end QualitySurface
end ResearchLean.AG
