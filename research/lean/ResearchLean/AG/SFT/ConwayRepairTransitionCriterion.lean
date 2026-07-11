import ResearchLean.AG.SFT.ConwayRepairTransition

/-!
Cycle 28 evidence for `G-sft-conway-01`.

Cycle 27 introduced selected repair/failure transition records.  This file
moves from record packaging to a criterion: for the selected reorg/refactor edit
shapes, finite conflict-table satisfaction is equivalent to existence of a
repair transition from `mismatchedAtlas` to the post-edit atlas.

This is still selected finite Conway vocabulary.  It does not claim arbitrary
repair composition, optimality, or a general conflict-set calculus.
-/

namespace ResearchLean.AG
namespace SFT
namespace ConwayTwoTopology

/-! ## Edit-indexed repair transition criteria -/

/-- A reorg edit realizes a selected repair transition to its post-edit atlas. -/
structure ReorgCoverEditRepairTransition (edit : ReorgCoverEdit) where
  transition : ConwayRepairTransition
  before_eq : transition.before = mismatchedAtlas
  after_eq : transition.after = edit.postAtlas

/-- A refactor edit realizes a selected repair transition to its post-edit atlas. -/
structure RefactorOwnershipEditRepairTransition
    (edit : RefactorOwnershipEdit) where
  transition : ConwayRepairTransition
  before_eq : transition.before = mismatchedAtlas
  after_eq : transition.after = edit.postAtlas

namespace ReorgCoverEdit

/--
For selected reorg edits, finite table satisfaction is exactly existence of a
repair transition from `mismatchedAtlas` to the edit's post-edit atlas.
-/
theorem repairTransition_nonempty_iff_finiteConflictTable
    (edit : ReorgCoverEdit) :
    Nonempty (ReorgCoverEditRepairTransition edit) ↔
      ReorgCoverEditFiniteConflictTable edit := by
  constructor
  · intro htransition
    rcases htransition with ⟨transition⟩
    have hsupport :
        Nonempty (CommunicationSupportAssignment edit.postAtlas) := by
      simpa [transition.after_eq] using
        transition.transition.afterSupportAssignment
    exact
      (edit.supportAssignment_nonempty_iff_finiteConflictTable).1
        hsupport
  · intro htable
    have hsupport :
        Nonempty (CommunicationSupportAssignment edit.postAtlas) :=
      (edit.supportAssignment_nonempty_iff_finiteConflictTable).2 htable
    rcases hsupport with ⟨assignment⟩
    exact
      ⟨{
        transition := {
          before := mismatchedAtlas
          after := edit.postAtlas
          beforeObstruction := mismatchedAtlas_nonzeroConwayObstruction
          afterSupportAssignment := ⟨assignment⟩
          afterNoObstruction :=
            compatible_no_conwayObstruction
              edit.postAtlas
              assignment.toCompatibility
        }
        before_eq := rfl
        after_eq := rfl
      }⟩

/-- Canonical reorg realizes a selected repair transition by the finite table. -/
theorem canonicalRepairTransition_nonempty :
    Nonempty (ReorgCoverEditRepairTransition canonicalReorgCoverEdit) :=
  (canonicalReorgCoverEdit.repairTransition_nonempty_iff_finiteConflictTable).2
    canonicalReorgCoverEdit_finiteConflictTable

/-- The missed-conflict reorg edit realizes no selected repair transition. -/
theorem partialMissesDbConflict_noRepairTransition :
    Not
      (Nonempty
        (ReorgCoverEditRepairTransition
          partialReorgMissesDbConflict)) := by
  intro htransition
  exact partialReorgMissesDbConflict_not_finiteConflictTable
    ((partialReorgMissesDbConflict
      |>.repairTransition_nonempty_iff_finiteConflictTable).1 htransition)

end ReorgCoverEdit

namespace RefactorOwnershipEdit

/--
For selected refactor edits, finite table satisfaction is exactly existence of
a repair transition from `mismatchedAtlas` to the edit's post-edit atlas.
-/
theorem repairTransition_nonempty_iff_finiteConflictTable
    (edit : RefactorOwnershipEdit) :
    Nonempty (RefactorOwnershipEditRepairTransition edit) ↔
      RefactorOwnershipEditFiniteConflictTable edit := by
  constructor
  · intro htransition
    rcases htransition with ⟨transition⟩
    have hsupport :
        Nonempty (CommunicationSupportAssignment edit.postAtlas) := by
      simpa [transition.after_eq] using
        transition.transition.afterSupportAssignment
    exact
      (edit.supportAssignment_nonempty_iff_finiteConflictTable).1
        hsupport
  · intro htable
    have hsupport :
        Nonempty (CommunicationSupportAssignment edit.postAtlas) :=
      (edit.supportAssignment_nonempty_iff_finiteConflictTable).2 htable
    rcases hsupport with ⟨assignment⟩
    exact
      ⟨{
        transition := {
          before := mismatchedAtlas
          after := edit.postAtlas
          beforeObstruction := mismatchedAtlas_nonzeroConwayObstruction
          afterSupportAssignment := ⟨assignment⟩
          afterNoObstruction :=
            compatible_no_conwayObstruction
              edit.postAtlas
              assignment.toCompatibility
        }
        before_eq := rfl
        after_eq := rfl
      }⟩

/-- Canonical refactor realizes a selected repair transition by the finite table. -/
theorem canonicalRepairTransition_nonempty :
    Nonempty
      (RefactorOwnershipEditRepairTransition
        canonicalRefactorOwnershipEdit) :=
  (canonicalRefactorOwnershipEdit
    |>.repairTransition_nonempty_iff_finiteConflictTable).2
      canonicalRefactorOwnershipEdit_finiteConflictTable

/-- The API-only refactor edit realizes no selected repair transition. -/
theorem partialSupportsOnlyApi_noRepairTransition :
    Not
      (Nonempty
        (RefactorOwnershipEditRepairTransition
          partialRefactorSupportsOnlyApi)) := by
  intro htransition
  exact partialRefactorSupportsOnlyApi_not_finiteConflictTable
    ((partialRefactorSupportsOnlyApi
      |>.repairTransition_nonempty_iff_finiteConflictTable).1 htransition)

end RefactorOwnershipEdit

/--
The selected Cycle 28 package: for both selected edit shapes, finite table
satisfaction is equivalent to existence of a repair transition from
`mismatchedAtlas` to the post-edit atlas; canonical repairs satisfy the
criterion, and selected missed-conflict edits do not.
-/
theorem selectedRepairTransitionCriterionPackage :
    (forall edit : ReorgCoverEdit,
      Nonempty (ReorgCoverEditRepairTransition edit) ↔
        ReorgCoverEditFiniteConflictTable edit) /\
      Nonempty (ReorgCoverEditRepairTransition canonicalReorgCoverEdit) /\
      Not
        (Nonempty
          (ReorgCoverEditRepairTransition
            partialReorgMissesDbConflict)) /\
      (forall edit : RefactorOwnershipEdit,
        Nonempty (RefactorOwnershipEditRepairTransition edit) ↔
          RefactorOwnershipEditFiniteConflictTable edit) /\
      Nonempty
        (RefactorOwnershipEditRepairTransition
          canonicalRefactorOwnershipEdit) /\
      Not
        (Nonempty
          (RefactorOwnershipEditRepairTransition
            partialRefactorSupportsOnlyApi)) := by
  exact
    ⟨ReorgCoverEdit.repairTransition_nonempty_iff_finiteConflictTable,
      ReorgCoverEdit.canonicalRepairTransition_nonempty,
      ReorgCoverEdit.partialMissesDbConflict_noRepairTransition,
      RefactorOwnershipEdit.repairTransition_nonempty_iff_finiteConflictTable,
      RefactorOwnershipEdit.canonicalRepairTransition_nonempty,
      RefactorOwnershipEdit.partialSupportsOnlyApi_noRepairTransition⟩

end ConwayTwoTopology
end SFT
end ResearchLean.AG
