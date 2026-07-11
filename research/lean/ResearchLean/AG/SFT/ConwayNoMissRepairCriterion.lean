import ResearchLean.AG.SFT.ConwayMissRepairCriterion

/-!
Cycle 35 evidence for `G-sft-conway-01`.

Cycle 34 related first selected misses to absence of selected repair-transition
records.  This file records the positive side: no selected first miss is
equivalent to existence of a selected repair-transition record.  It also links
that positive criterion back to selected no-miss predicates for the bounded
reorg/refactor edit shapes.

This remains selected finite Conway vocabulary.  It is not an arbitrary repair
calculus or runtime diagnostic procedure.
-/

namespace Formal.AG.Research
namespace SFT
namespace ConwayTwoTopology

/-! ## Positive repair criterion from no first miss -/

/-- Reorg no-first-miss is equivalent to selected repair-transition existence. -/
theorem reorgNoFirstSelectedMiss_iff_repairTransition
    (edit : ReorgCoverEdit) :
    Not
        (exists conflict : ReorgSelectedConflict,
          ReorgCoverEditFirstSelectedMiss edit conflict) ↔
      Nonempty (ReorgCoverEditRepairTransition edit) := by
  rw [reorgFirstSelectedMiss_exists_iff_noRepairTransition]
  exact not_not

/-- Refactor no-first-miss is equivalent to selected repair-transition existence. -/
theorem refactorNoFirstSelectedMiss_iff_repairTransition
    (edit : RefactorOwnershipEdit) :
    Not
        (exists conflict : RefactorSelectedConflict,
          RefactorOwnershipEditFirstSelectedMiss edit conflict) ↔
      Nonempty (RefactorOwnershipEditRepairTransition edit) := by
  rw [refactorFirstSelectedMiss_exists_iff_noRepairTransition]
  exact not_not

/-- Reorg no selected miss is equivalent to selected repair-transition existence. -/
theorem reorgNoSelectedMiss_iff_repairTransition
    (edit : ReorgCoverEdit) :
    (forall conflict : ReorgSelectedConflict,
      Not (ReorgCoverEditMissesSelectedConflict edit conflict)) ↔
      Nonempty (ReorgCoverEditRepairTransition edit) := by
  rw [← reorgHitsSelectedConflictSet_iff_noSelectedMiss,
    ← reorgRepairTransition_nonempty_iff_hitsSelectedConflictSet]

/-- Refactor no selected miss is equivalent to selected repair-transition existence. -/
theorem refactorNoSelectedMiss_iff_repairTransition
    (edit : RefactorOwnershipEdit) :
    (forall conflict : RefactorSelectedConflict,
      Not (RefactorOwnershipEditMissesSelectedConflict edit conflict)) ↔
      Nonempty (RefactorOwnershipEditRepairTransition edit) := by
  rw [← refactorHitsSelectedConflictSet_iff_noSelectedMiss,
    ← refactorRepairTransition_nonempty_iff_hitsSelectedConflictSet]

/--
The selected Cycle 35 package: absence of selected first misses, absence of any
selected miss, and selected repair-transition existence coincide for both
bounded edit shapes.
-/
theorem selectedNoMissRepairCriterionPackage :
    (forall edit : ReorgCoverEdit,
      Not
          (exists conflict : ReorgSelectedConflict,
            ReorgCoverEditFirstSelectedMiss edit conflict) ↔
        Nonempty (ReorgCoverEditRepairTransition edit)) /\
      (forall edit : ReorgCoverEdit,
        (forall conflict : ReorgSelectedConflict,
          Not (ReorgCoverEditMissesSelectedConflict edit conflict)) ↔
          Nonempty (ReorgCoverEditRepairTransition edit)) /\
      (forall edit : RefactorOwnershipEdit,
        Not
            (exists conflict : RefactorSelectedConflict,
              RefactorOwnershipEditFirstSelectedMiss edit conflict) ↔
          Nonempty (RefactorOwnershipEditRepairTransition edit)) /\
      (forall edit : RefactorOwnershipEdit,
        (forall conflict : RefactorSelectedConflict,
          Not (RefactorOwnershipEditMissesSelectedConflict edit conflict)) ↔
          Nonempty (RefactorOwnershipEditRepairTransition edit)) := by
  exact
    ⟨reorgNoFirstSelectedMiss_iff_repairTransition,
      reorgNoSelectedMiss_iff_repairTransition,
      refactorNoFirstSelectedMiss_iff_repairTransition,
      refactorNoSelectedMiss_iff_repairTransition⟩

end ConwayTwoTopology
end SFT
end Formal.AG.Research
