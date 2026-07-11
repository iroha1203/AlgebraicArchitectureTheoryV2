import ResearchLean.AG.SFT.ConwaySelectedConflictSet

/-!
Cycle 30 evidence for `G-sft-conway-01`.

Cycle 29 introduced selected conflict-set indices and hitting predicates.
This file relates those selected indices back to the older operation-shaped
hitting criteria, support-assignment existence, and repair-transition
existence.  The result is a small selector-preserving bridge: the selected
conflict-set interface has the same truth condition as the existing reorg and
refactor repair-existence criteria, and it implies post-edit no-obstruction.

This remains selected finite Conway vocabulary.  It is not a general
conflict-set morphism category, arbitrary conflict enumeration algorithm, or
repair composition theorem.
-/

namespace ResearchLean.AG
namespace SFT
namespace ConwayTwoTopology

/-! ## Selected conflict-set bridge to operation-shaped hitting -/

/--
For reorg edits, selected conflict-set hitting is the same condition as the
older operation-shaped hitting predicate.
-/
theorem reorgHitsSelectedConflictSet_iff_hitsEveryConflict
    (edit : ReorgCoverEdit) :
    ReorgCoverEditHitsSelectedConflictSet edit ↔
      ReorgCoverEditHitsEveryConflict edit := by
  rw [reorgHitsSelectedConflictSet_iff_finiteConflictTable,
    ← reorgCoverEditHitsEveryConflict_iff_finiteConflictTable]

/--
For refactor edits, selected conflict-set hitting is the same condition as the
older operation-shaped hitting predicate.
-/
theorem refactorHitsSelectedConflictSet_iff_hitsEveryConflict
    (edit : RefactorOwnershipEdit) :
    RefactorOwnershipEditHitsSelectedConflictSet edit ↔
      RefactorOwnershipEditHitsEveryConflict edit := by
  rw [refactorHitsSelectedConflictSet_iff_finiteConflictTable,
    ← refactorOwnershipEditHitsEveryConflict_iff_finiteConflictTable]

/--
For reorg edits, selected conflict-set hitting is the same condition as
post-edit support-assignment existence.
-/
theorem reorgHitsSelectedConflictSet_iff_supportAssignment
    (edit : ReorgCoverEdit) :
    ReorgCoverEditHitsSelectedConflictSet edit ↔
      Nonempty (CommunicationSupportAssignment edit.postAtlas) := by
  rw [reorgHitsSelectedConflictSet_iff_finiteConflictTable,
    ← edit.supportAssignment_nonempty_iff_finiteConflictTable]

/--
For refactor edits, selected conflict-set hitting is the same condition as
post-edit support-assignment existence.
-/
theorem refactorHitsSelectedConflictSet_iff_supportAssignment
    (edit : RefactorOwnershipEdit) :
    RefactorOwnershipEditHitsSelectedConflictSet edit ↔
      Nonempty (CommunicationSupportAssignment edit.postAtlas) := by
  rw [refactorHitsSelectedConflictSet_iff_finiteConflictTable,
    ← edit.supportAssignment_nonempty_iff_finiteConflictTable]

/--
For reorg edits, selected conflict-set hitting rules out a selected Conway
obstruction in the post-edit atlas.
-/
theorem reorgNoConwayObstruction_of_hitsSelectedConflictSet
    (edit : ReorgCoverEdit)
    (hhit : ReorgCoverEditHitsSelectedConflictSet edit) :
    Not (ConwayObstructionWitness edit.postAtlas) := by
  exact
    edit.killsConwayObstruction_of_hitsEveryConflict
      ((reorgHitsSelectedConflictSet_iff_hitsEveryConflict edit).1 hhit)

/--
For refactor edits, selected conflict-set hitting rules out a selected Conway
obstruction in the post-edit atlas.
-/
theorem refactorNoConwayObstruction_of_hitsSelectedConflictSet
    (edit : RefactorOwnershipEdit)
    (hhit : RefactorOwnershipEditHitsSelectedConflictSet edit) :
    Not (ConwayObstructionWitness edit.postAtlas) := by
  exact
    edit.killsConwayObstruction_of_hitsEveryConflict
      ((refactorHitsSelectedConflictSet_iff_hitsEveryConflict edit).1 hhit)

/--
The selected Cycle 30 bridge: selected conflict-set hitting, operation-shaped
hitting, support-assignment existence, and repair-transition existence are the
same bounded repair-existence criterion for the selected reorg/refactor edit
shapes.  Post-edit no-obstruction is recorded as a consequence of selected
hitting.
-/
theorem selectedConflictBridgePackage :
    (forall edit : ReorgCoverEdit,
      ReorgCoverEditHitsSelectedConflictSet edit ↔
        ReorgCoverEditHitsEveryConflict edit) /\
      (forall edit : ReorgCoverEdit,
        ReorgCoverEditHitsSelectedConflictSet edit ↔
          Nonempty (CommunicationSupportAssignment edit.postAtlas)) /\
      (forall edit : ReorgCoverEdit,
        Nonempty (ReorgCoverEditRepairTransition edit) ↔
          ReorgCoverEditHitsSelectedConflictSet edit) /\
      (forall edit : ReorgCoverEdit,
        ReorgCoverEditHitsSelectedConflictSet edit ->
          Not (ConwayObstructionWitness edit.postAtlas)) /\
      (forall edit : RefactorOwnershipEdit,
        RefactorOwnershipEditHitsSelectedConflictSet edit ↔
          RefactorOwnershipEditHitsEveryConflict edit) /\
      (forall edit : RefactorOwnershipEdit,
        RefactorOwnershipEditHitsSelectedConflictSet edit ↔
          Nonempty (CommunicationSupportAssignment edit.postAtlas)) /\
      (forall edit : RefactorOwnershipEdit,
        Nonempty (RefactorOwnershipEditRepairTransition edit) ↔
          RefactorOwnershipEditHitsSelectedConflictSet edit) /\
      (forall edit : RefactorOwnershipEdit,
        RefactorOwnershipEditHitsSelectedConflictSet edit ->
          Not (ConwayObstructionWitness edit.postAtlas)) := by
  exact
    ⟨reorgHitsSelectedConflictSet_iff_hitsEveryConflict,
      reorgHitsSelectedConflictSet_iff_supportAssignment,
      reorgRepairTransition_nonempty_iff_hitsSelectedConflictSet,
      reorgNoConwayObstruction_of_hitsSelectedConflictSet,
      refactorHitsSelectedConflictSet_iff_hitsEveryConflict,
      refactorHitsSelectedConflictSet_iff_supportAssignment,
      refactorRepairTransition_nonempty_iff_hitsSelectedConflictSet,
      refactorNoConwayObstruction_of_hitsSelectedConflictSet⟩

end ConwayTwoTopology
end SFT
end ResearchLean.AG
