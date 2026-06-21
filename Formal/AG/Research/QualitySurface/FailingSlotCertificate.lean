import Formal.AG.Research.QualitySurface.FiniteRouteFamilyExactLocus

/-!
Cycle 54 evidence for `G-aat-quality-surface-01`.

This file turns failing route slots into explicit certificates.  For any
staged route-slot family, failure of family source-ref exactness is equivalent
to the existence of a failing-slot certificate.  Conversely, absence of such a
certificate is equivalent to family exactness.

The claim is relative to supplied route slots, staged selected correction
semantics, and the explicit source-ref packet bridge.  It does not assert a
computable scan, arbitrary repair planning, runtime patch synthesis, source
extraction completeness, ArchMap correctness, or whole-codebase quality.
-/

namespace Formal.AG.Research
namespace QualitySurface
namespace FailingSlotCertificate

open SourceRefExactVisualizationCriterion
open ParametrizedSelectedCorrectionSystem
open MultiRouteCorrectionSystem
open FiniteRouteFamilyExactLocus
open RepairStage
open RouteSlot

universe u

/-! ## Failing-slot certificates -/

/-- A certificate that a staged route-slot family has a failing slot. -/
structure FailingSlotWitness {Slot : Type u}
    (assignment : StageAssignment Slot) where
  slot : Slot
  fails : assignment slot ≠ allBranches

/-- A failing-slot certificate obstructs family source-ref exactness. -/
theorem failingSlotCertificate_obstructs_familyExact {Slot : Type u}
    {assignment : StageAssignment Slot}
    (certificate : FailingSlotWitness assignment) :
    ¬ AssignmentFamilySourceRefExact assignment :=
  failingSlot_obstructs_assignmentFamilyExact
    assignment certificate.slot certificate.fails

/-- Family exactness failure is equivalent to the existence of a failing-slot certificate. -/
theorem not_familyExact_iff_exists_failingSlotCertificate {Slot : Type u}
    (assignment : StageAssignment Slot) :
    ¬ AssignmentFamilySourceRefExact assignment ↔
      ∃ _certificate : FailingSlotWitness assignment, True := by
  classical
  constructor
  · intro hnotExact
    by_contra hnoCertificate
    have hall : AssignmentAllBranches assignment := by
      intro slot
      by_contra hslot
      exact hnoCertificate ⟨⟨slot, hslot⟩, trivial⟩
    exact hnotExact
      ((assignmentFamilySourceRefExact_iff_allBranches assignment).mpr hall)
  · intro hcertificate
    rcases hcertificate with ⟨certificate, _htrivial⟩
    exact failingSlotCertificate_obstructs_familyExact certificate

/-- Family exactness is equivalent to absence of failing-slot certificates. -/
theorem familyExact_iff_no_failingSlotCertificate {Slot : Type u}
    (assignment : StageAssignment Slot) :
    AssignmentFamilySourceRefExact assignment ↔
      ¬ ∃ _certificate : FailingSlotWitness assignment, True := by
  classical
  constructor
  · intro hexact hcertificate
    exact ((not_familyExact_iff_exists_failingSlotCertificate
      assignment).mpr hcertificate) hexact
  · intro hnoCertificate
    by_contra hnotExact
    exact hnoCertificate
      ((not_familyExact_iff_exists_failingSlotCertificate
        assignment).mp hnotExact)

/-! ## Mixed assignment certificate -/

/-- The secondary route is the failing-slot certificate for the mixed assignment. -/
def mixedRouteSlotFailingCertificate :
    FailingSlotWitness mixedRouteSlotAssignment where
  slot := secondary
  fails := mixedRouteSlotAssignment_secondary_fails

/-- The mixed assignment failure is explained by its failing-slot certificate. -/
theorem mixedRouteSlotFailingCertificate_obstructs :
    ¬ AssignmentFamilySourceRefExact mixedRouteSlotAssignment :=
  failingSlotCertificate_obstructs_familyExact
    mixedRouteSlotFailingCertificate

/-- The mixed assignment has a failing-slot certificate exactly as expected. -/
theorem mixedRouteSlot_exists_failingSlotCertificate :
    ∃ _certificate : FailingSlotWitness mixedRouteSlotAssignment, True :=
  ⟨mixedRouteSlotFailingCertificate, trivial⟩

/-! ## Theorem package -/

/--
Cycle-54 theorem package: family exactness failure is equivalent to an explicit
failing-slot certificate, and the mixed route-slot assignment carries such a
certificate at its secondary slot.
-/
theorem failingSlotCertificate_package :
    (∀ {Slot : Type u} (assignment : StageAssignment Slot),
      ¬ AssignmentFamilySourceRefExact assignment ↔
        ∃ _certificate : FailingSlotWitness assignment, True) ∧
    (∀ {Slot : Type u} (assignment : StageAssignment Slot),
      AssignmentFamilySourceRefExact assignment ↔
        ¬ ∃ _certificate : FailingSlotWitness assignment, True) ∧
    (∀ {Slot : Type u} {assignment : StageAssignment Slot}
      (_certificate : FailingSlotWitness assignment),
      ¬ AssignmentFamilySourceRefExact assignment) ∧
    ¬ AssignmentFamilySourceRefExact mixedRouteSlotAssignment ∧
    (∃ _certificate : FailingSlotWitness mixedRouteSlotAssignment, True) := by
  exact ⟨not_familyExact_iff_exists_failingSlotCertificate,
    familyExact_iff_no_failingSlotCertificate,
    fun certificate =>
      failingSlotCertificate_obstructs_familyExact certificate,
    mixedRouteSlotFailingCertificate_obstructs,
    mixedRouteSlot_exists_failingSlotCertificate⟩

end FailingSlotCertificate
end QualitySurface
end Formal.AG.Research
