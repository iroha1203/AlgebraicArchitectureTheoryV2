import ResearchLean.AG.SFT.ConwaySelectedMissScanner

/-!
Cycle 34 evidence for `G-sft-conway-01`.

Cycle 33 provided a bounded first-miss scanner over selected conflict sets.
This file connects the scanner to the repair-transition criterion: for selected
reorg/refactor edit shapes, a first selected miss exists exactly when no
selected repair-transition record exists.  Thus the selected first miss is not
only a diagnostic selector; it is a complete obstruction to the selected
repair-transition existence criterion.

This remains selected finite Conway vocabulary.  It is not an arbitrary repair
calculus, runtime extraction algorithm, or general conflict enumeration result.
-/

namespace Formal.AG.Research
namespace SFT
namespace ConwayTwoTopology

/-! ## Reorg miss scanner versus repair transition -/

/-- Reorg selected misses exist exactly when the edit has no repair transition. -/
theorem reorgSelectedMiss_exists_iff_noRepairTransition
    (edit : ReorgCoverEdit) :
    (exists conflict : ReorgSelectedConflict,
      ReorgCoverEditMissesSelectedConflict edit conflict) ↔
      Not (Nonempty (ReorgCoverEditRepairTransition edit)) := by
  rw [← reorgFirstSelectedMiss_exists_iff_hasSelectedMiss,
    reorgRepairTransition_nonempty_iff_hitsSelectedConflictSet,
    reorgHitsSelectedConflictSet_iff_noSelectedMiss]
  constructor
  · intro hfirst hnoMiss
    rcases hfirst with ⟨conflict, hfirstConflict⟩
    exact hnoMiss conflict
      (reorgFirstSelectedMiss_sound edit conflict hfirstConflict)
  · intro hnotNoMiss
    by_contra hnoFirst
    apply hnotNoMiss
    intro conflict hmiss
    apply hnoFirst
    exact
      (reorgFirstSelectedMiss_exists_iff_hasSelectedMiss edit).2
        ⟨conflict, hmiss⟩

/-- Reorg first-miss existence is the same obstruction to repair transition. -/
theorem reorgFirstSelectedMiss_exists_iff_noRepairTransition
    (edit : ReorgCoverEdit) :
    (exists conflict : ReorgSelectedConflict,
      ReorgCoverEditFirstSelectedMiss edit conflict) ↔
      Not (Nonempty (ReorgCoverEditRepairTransition edit)) := by
  rw [reorgFirstSelectedMiss_exists_iff_hasSelectedMiss,
    reorgSelectedMiss_exists_iff_noRepairTransition]

/-- The canonical reorg edit has a repair transition because it has no first miss. -/
theorem canonicalReorgCoverEdit_repairTransition_iff_noFirstMiss :
    Nonempty (ReorgCoverEditRepairTransition canonicalReorgCoverEdit) ↔
      Not
        (exists conflict : ReorgSelectedConflict,
          ReorgCoverEditFirstSelectedMiss
            canonicalReorgCoverEdit conflict) := by
  rw [reorgFirstSelectedMiss_exists_iff_noRepairTransition]
  exact not_not.symm

/--
The partial reorg edit has a first selected miss exactly where it has no repair
transition.
-/
theorem partialReorgMissesDbConflict_firstMiss_iff_noRepairTransition :
    (exists conflict : ReorgSelectedConflict,
      ReorgCoverEditFirstSelectedMiss
        partialReorgMissesDbConflict conflict) ↔
      Not
        (Nonempty
          (ReorgCoverEditRepairTransition
            partialReorgMissesDbConflict)) :=
  reorgFirstSelectedMiss_exists_iff_noRepairTransition
    partialReorgMissesDbConflict

/-! ## Refactor miss scanner versus repair transition -/

/-- Refactor selected misses exist exactly when the edit has no repair transition. -/
theorem refactorSelectedMiss_exists_iff_noRepairTransition
    (edit : RefactorOwnershipEdit) :
    (exists conflict : RefactorSelectedConflict,
      RefactorOwnershipEditMissesSelectedConflict edit conflict) ↔
      Not (Nonempty (RefactorOwnershipEditRepairTransition edit)) := by
  rw [← refactorFirstSelectedMiss_exists_iff_hasSelectedMiss,
    refactorRepairTransition_nonempty_iff_hitsSelectedConflictSet,
    refactorHitsSelectedConflictSet_iff_noSelectedMiss]
  constructor
  · intro hfirst hnoMiss
    rcases hfirst with ⟨conflict, hfirstConflict⟩
    exact hnoMiss conflict
      (refactorFirstSelectedMiss_sound edit conflict hfirstConflict)
  · intro hnotNoMiss
    by_contra hnoFirst
    apply hnotNoMiss
    intro conflict hmiss
    apply hnoFirst
    exact
      (refactorFirstSelectedMiss_exists_iff_hasSelectedMiss edit).2
        ⟨conflict, hmiss⟩

/-- Refactor first-miss existence is the same obstruction to repair transition. -/
theorem refactorFirstSelectedMiss_exists_iff_noRepairTransition
    (edit : RefactorOwnershipEdit) :
    (exists conflict : RefactorSelectedConflict,
      RefactorOwnershipEditFirstSelectedMiss edit conflict) ↔
      Not (Nonempty (RefactorOwnershipEditRepairTransition edit)) := by
  rw [refactorFirstSelectedMiss_exists_iff_hasSelectedMiss,
    refactorSelectedMiss_exists_iff_noRepairTransition]

/-- The canonical refactor edit has a repair transition because it has no first miss. -/
theorem canonicalRefactorOwnershipEdit_repairTransition_iff_noFirstMiss :
    Nonempty
        (RefactorOwnershipEditRepairTransition
          canonicalRefactorOwnershipEdit) ↔
      Not
        (exists conflict : RefactorSelectedConflict,
          RefactorOwnershipEditFirstSelectedMiss
            canonicalRefactorOwnershipEdit conflict) := by
  rw [refactorFirstSelectedMiss_exists_iff_noRepairTransition]
  exact not_not.symm

/--
The API-only partial refactor edit has a first selected miss exactly where it
has no repair transition.
-/
theorem partialRefactorSupportsOnlyApi_firstMiss_iff_noRepairTransition :
    (exists conflict : RefactorSelectedConflict,
      RefactorOwnershipEditFirstSelectedMiss
        partialRefactorSupportsOnlyApi conflict) ↔
      Not
        (Nonempty
          (RefactorOwnershipEditRepairTransition
            partialRefactorSupportsOnlyApi)) :=
  refactorFirstSelectedMiss_exists_iff_noRepairTransition
    partialRefactorSupportsOnlyApi

/--
The selected Cycle 34 package: selected first-miss existence is equivalent to
absence of selected repair-transition records for both selected edit shapes,
with canonical and partial examples connected to that criterion.
-/
theorem selectedMissRepairCriterionPackage :
    (forall edit : ReorgCoverEdit,
      (exists conflict : ReorgSelectedConflict,
        ReorgCoverEditFirstSelectedMiss edit conflict) ↔
        Not (Nonempty (ReorgCoverEditRepairTransition edit))) /\
      (Nonempty (ReorgCoverEditRepairTransition canonicalReorgCoverEdit) ↔
        Not
          (exists conflict : ReorgSelectedConflict,
            ReorgCoverEditFirstSelectedMiss
              canonicalReorgCoverEdit conflict)) /\
      ((exists conflict : ReorgSelectedConflict,
        ReorgCoverEditFirstSelectedMiss
          partialReorgMissesDbConflict conflict) ↔
        Not
          (Nonempty
            (ReorgCoverEditRepairTransition
              partialReorgMissesDbConflict))) /\
      (forall edit : RefactorOwnershipEdit,
        (exists conflict : RefactorSelectedConflict,
          RefactorOwnershipEditFirstSelectedMiss edit conflict) ↔
          Not (Nonempty (RefactorOwnershipEditRepairTransition edit))) /\
      (Nonempty
          (RefactorOwnershipEditRepairTransition
            canonicalRefactorOwnershipEdit) ↔
        Not
          (exists conflict : RefactorSelectedConflict,
            RefactorOwnershipEditFirstSelectedMiss
              canonicalRefactorOwnershipEdit conflict)) /\
      ((exists conflict : RefactorSelectedConflict,
        RefactorOwnershipEditFirstSelectedMiss
          partialRefactorSupportsOnlyApi conflict) ↔
        Not
          (Nonempty
            (RefactorOwnershipEditRepairTransition
              partialRefactorSupportsOnlyApi))) := by
  exact
    ⟨reorgFirstSelectedMiss_exists_iff_noRepairTransition,
      canonicalReorgCoverEdit_repairTransition_iff_noFirstMiss,
      partialReorgMissesDbConflict_firstMiss_iff_noRepairTransition,
      refactorFirstSelectedMiss_exists_iff_noRepairTransition,
      canonicalRefactorOwnershipEdit_repairTransition_iff_noFirstMiss,
      partialRefactorSupportsOnlyApi_firstMiss_iff_noRepairTransition⟩

end ConwayTwoTopology
end SFT
end Formal.AG.Research
