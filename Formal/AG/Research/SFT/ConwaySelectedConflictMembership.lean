import Formal.AG.Research.SFT.ConwayRefactorTwoOwnerObstruction
import Formal.AG.Research.SFT.ConwaySelectedConflictMorphism

/-!
Cycle 32 evidence for `G-sft-conway-01`.

Cycle 29 introduced selected conflict-set indices, and Cycle 30 related their
hitting predicates to the existing repair criteria.  This file adds pointwise
membership and missed-conflict selectors for the selected finite edit shapes.
Canonical edits miss no selected conflict.  The two existing partial edits miss
exactly one selected conflict each.

This is still selected finite Conway vocabulary.  It is not an arbitrary
conflict enumeration algorithm.
-/

namespace Formal.AG.Research
namespace SFT
namespace ConwayTwoTopology

/-! ## Reorg selected conflict membership -/

/-- A selected reorg conflict is active for an edit when its communication entry holds. -/
def ReorgCoverEditActivatesSelectedConflict
    (edit : ReorgCoverEdit)
    (conflict : ReorgSelectedConflict) : Prop :=
  edit.communication
    (ReorgSelectedConflict.comm conflict)
    (ReorgSelectedConflict.context conflict)

/-- A selected reorg conflict is missed when it is active and lacks required support. -/
def ReorgCoverEditMissesSelectedConflict
    (edit : ReorgCoverEdit)
    (conflict : ReorgSelectedConflict) : Prop :=
  ReorgCoverEditActivatesSelectedConflict edit conflict /\
    Not
      (splitOwnership
        (ReorgSelectedConflict.owner conflict)
        (ReorgSelectedConflict.context conflict))

/-- Hitting every selected reorg conflict is equivalent to missing none. -/
theorem reorgHitsSelectedConflictSet_iff_noSelectedMiss
    (edit : ReorgCoverEdit) :
    ReorgCoverEditHitsSelectedConflictSet edit ↔
      forall conflict : ReorgSelectedConflict,
        Not (ReorgCoverEditMissesSelectedConflict edit conflict) := by
  constructor
  · intro hhit conflict hmiss
    exact hmiss.2 (hhit conflict hmiss.1)
  · intro hnoMiss conflict hactive
    by_contra hnot
    exact hnoMiss conflict ⟨hactive, hnot⟩

/-- The canonical reorg edit misses no selected conflict. -/
theorem canonicalReorgCoverEdit_noSelectedMiss
    (conflict : ReorgSelectedConflict) :
    Not
      (ReorgCoverEditMissesSelectedConflict
        canonicalReorgCoverEdit conflict) := by
  exact
    (reorgHitsSelectedConflictSet_iff_noSelectedMiss
      canonicalReorgCoverEdit).1
        canonicalReorgCoverEdit_hitsSelectedConflictSet conflict

/--
The missed-conflict reorg edit misses exactly the selected platform-DB
conflict.
-/
theorem partialReorgMissesDbConflict_missesSelectedConflict_iff
    (conflict : ReorgSelectedConflict) :
    ReorgCoverEditMissesSelectedConflict
      partialReorgMissesDbConflict conflict ↔
      conflict = ReorgSelectedConflict.platformDb := by
  constructor
  · intro hmiss
    cases conflict with
    | platformApi =>
        simp [ReorgCoverEditMissesSelectedConflict,
          ReorgCoverEditActivatesSelectedConflict,
          ReorgSelectedConflict.comm, ReorgSelectedConflict.context,
          ReorgSelectedConflict.owner, partialReorgMissesDbConflict,
          splitOwnership] at hmiss
    | platformDb =>
        rfl
    | dataApi =>
        simp [ReorgCoverEditMissesSelectedConflict,
          ReorgCoverEditActivatesSelectedConflict,
          ReorgSelectedConflict.comm, ReorgSelectedConflict.context,
          ReorgSelectedConflict.owner, partialReorgMissesDbConflict] at hmiss
    | dataDb =>
        simp [ReorgCoverEditMissesSelectedConflict,
          ReorgCoverEditActivatesSelectedConflict,
          ReorgSelectedConflict.comm, ReorgSelectedConflict.context,
          ReorgSelectedConflict.owner, partialReorgMissesDbConflict,
          splitOwnership] at hmiss
  · intro hconflict
    subst hconflict
    constructor
    · simp [ReorgCoverEditActivatesSelectedConflict,
        ReorgSelectedConflict.comm, ReorgSelectedConflict.context,
        partialReorgMissesDbConflict]
    · simp [ReorgSelectedConflict.owner, ReorgSelectedConflict.context,
        splitOwnership]

/-- The missed-conflict reorg edit has a selected miss. -/
theorem partialReorgMissesDbConflict_hasSelectedMiss :
    exists conflict : ReorgSelectedConflict,
      ReorgCoverEditMissesSelectedConflict
        partialReorgMissesDbConflict conflict := by
  exact
    ⟨ReorgSelectedConflict.platformDb,
      (partialReorgMissesDbConflict_missesSelectedConflict_iff
        ReorgSelectedConflict.platformDb).2 rfl⟩

/-! ## Refactor selected conflict membership -/

/-- A selected refactor conflict is missed when the edited owner lacks support. -/
def RefactorOwnershipEditMissesSelectedConflict
    (edit : RefactorOwnershipEdit)
    (conflict : RefactorSelectedConflict) : Prop :=
  Not (edit.ownership () (RefactorSelectedConflict.context conflict))

/-- Hitting every selected refactor conflict is equivalent to missing none. -/
theorem refactorHitsSelectedConflictSet_iff_noSelectedMiss
    (edit : RefactorOwnershipEdit) :
    RefactorOwnershipEditHitsSelectedConflictSet edit ↔
      forall conflict : RefactorSelectedConflict,
        Not (RefactorOwnershipEditMissesSelectedConflict edit conflict) := by
  constructor
  · intro hhit conflict hmiss
    exact hmiss (hhit conflict)
  · intro hnoMiss conflict
    by_contra hnot
    exact hnoMiss conflict hnot

/-- The canonical refactor edit misses no selected conflict. -/
theorem canonicalRefactorOwnershipEdit_noSelectedMiss
    (conflict : RefactorSelectedConflict) :
    Not
      (RefactorOwnershipEditMissesSelectedConflict
        canonicalRefactorOwnershipEdit conflict) := by
  exact
    (refactorHitsSelectedConflictSet_iff_noSelectedMiss
      canonicalRefactorOwnershipEdit).1
        canonicalRefactorOwnershipEdit_hitsSelectedConflictSet conflict

/-- The API-only refactor edit misses exactly the selected DB conflict. -/
theorem partialRefactorSupportsOnlyApi_missesSelectedConflict_iff
    (conflict : RefactorSelectedConflict) :
    RefactorOwnershipEditMissesSelectedConflict
      partialRefactorSupportsOnlyApi conflict ↔
      conflict = RefactorSelectedConflict.db := by
  constructor
  · intro hmiss
    cases conflict with
    | api =>
        simp [RefactorOwnershipEditMissesSelectedConflict,
          RefactorSelectedConflict.context, partialRefactorSupportsOnlyApi]
          at hmiss
    | db =>
        rfl
  · intro hconflict
    subst hconflict
    simp [RefactorOwnershipEditMissesSelectedConflict,
      RefactorSelectedConflict.context, partialRefactorSupportsOnlyApi]

/-- The API-only refactor edit has a selected miss. -/
theorem partialRefactorSupportsOnlyApi_hasSelectedMiss :
    exists conflict : RefactorSelectedConflict,
      RefactorOwnershipEditMissesSelectedConflict
        partialRefactorSupportsOnlyApi conflict := by
  exact
    ⟨RefactorSelectedConflict.db,
      (partialRefactorSupportsOnlyApi_missesSelectedConflict_iff
        RefactorSelectedConflict.db).2 rfl⟩

/--
The selected Cycle 32 package: selected hitting is exactly no pointwise miss;
canonical repairs miss none; and the selected partial edits have exact one-entry
miss selectors.
-/
theorem selectedConflictMembershipPackage :
    (forall edit : ReorgCoverEdit,
      ReorgCoverEditHitsSelectedConflictSet edit ↔
        forall conflict : ReorgSelectedConflict,
          Not (ReorgCoverEditMissesSelectedConflict edit conflict)) /\
      (forall conflict : ReorgSelectedConflict,
        Not
          (ReorgCoverEditMissesSelectedConflict
            canonicalReorgCoverEdit conflict)) /\
      (forall conflict : ReorgSelectedConflict,
        ReorgCoverEditMissesSelectedConflict
          partialReorgMissesDbConflict conflict ↔
          conflict = ReorgSelectedConflict.platformDb) /\
      (exists conflict : ReorgSelectedConflict,
        ReorgCoverEditMissesSelectedConflict
          partialReorgMissesDbConflict conflict) /\
      (forall edit : RefactorOwnershipEdit,
        RefactorOwnershipEditHitsSelectedConflictSet edit ↔
          forall conflict : RefactorSelectedConflict,
            Not (RefactorOwnershipEditMissesSelectedConflict edit conflict)) /\
      (forall conflict : RefactorSelectedConflict,
        Not
          (RefactorOwnershipEditMissesSelectedConflict
            canonicalRefactorOwnershipEdit conflict)) /\
      (forall conflict : RefactorSelectedConflict,
        RefactorOwnershipEditMissesSelectedConflict
          partialRefactorSupportsOnlyApi conflict ↔
          conflict = RefactorSelectedConflict.db) /\
      (exists conflict : RefactorSelectedConflict,
        RefactorOwnershipEditMissesSelectedConflict
          partialRefactorSupportsOnlyApi conflict) := by
  exact
    ⟨reorgHitsSelectedConflictSet_iff_noSelectedMiss,
      canonicalReorgCoverEdit_noSelectedMiss,
      partialReorgMissesDbConflict_missesSelectedConflict_iff,
      partialReorgMissesDbConflict_hasSelectedMiss,
      refactorHitsSelectedConflictSet_iff_noSelectedMiss,
      canonicalRefactorOwnershipEdit_noSelectedMiss,
      partialRefactorSupportsOnlyApi_missesSelectedConflict_iff,
      partialRefactorSupportsOnlyApi_hasSelectedMiss⟩

end ConwayTwoTopology
end SFT
end Formal.AG.Research
