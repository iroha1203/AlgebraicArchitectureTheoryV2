import ResearchLean.AG.SFT.ConwayRepairTransitionCriterion

/-!
Cycle 29 evidence for `G-sft-conway-01`.

Cycle 26 used hard-coded finite tables.  Cycle 28 connected those tables to
repair-transition record existence.  This file factors the hard-coded tables
through explicit selected conflict-set indices with a hitting predicate.  For
the selected reorg/refactor edit shapes, hitting the selected conflict set is
equivalent to finite-table satisfaction and to repair-transition existence.

This is still selected finite Conway vocabulary.  It is not an arbitrary
conflict enumeration algorithm or a general repair calculus.
-/

namespace ResearchLean.AG
namespace SFT
namespace ConwayTwoTopology

/-! ## Selected reorg conflict set -/

/-- The selected finite reorg conflicts for the two-team/two-module vocabulary. -/
inductive ReorgSelectedConflict where
  | platformApi
  | platformDb
  | dataApi
  | dataDb
  deriving DecidableEq

namespace ReorgSelectedConflict

/-- Communication block of a selected reorg conflict. -/
def comm : ReorgSelectedConflict -> Team
  | platformApi => Team.platform
  | platformDb => Team.platform
  | dataApi => Team.data
  | dataDb => Team.data

/-- Context of a selected reorg conflict. -/
def context : ReorgSelectedConflict -> Module
  | platformApi => Module.api
  | platformDb => Module.db
  | dataApi => Module.api
  | dataDb => Module.db

/-- Required owner for a selected reorg conflict. -/
def owner : ReorgSelectedConflict -> Owner
  | platformApi => Owner.apiOwner
  | platformDb => Owner.apiOwner
  | dataApi => Owner.dbOwner
  | dataDb => Owner.dbOwner

end ReorgSelectedConflict

/-- A selected reorg conflict is hit when the required owner supports it. -/
def ReorgCoverEditHitsSelectedConflict
    (edit : ReorgCoverEdit)
    (conflict : ReorgSelectedConflict) : Prop :=
  edit.communication
      (ReorgSelectedConflict.comm conflict)
      (ReorgSelectedConflict.context conflict) ->
    splitOwnership
      (ReorgSelectedConflict.owner conflict)
      (ReorgSelectedConflict.context conflict)

/-- A reorg edit hits every selected conflict. -/
def ReorgCoverEditHitsSelectedConflictSet
    (edit : ReorgCoverEdit) : Prop :=
  forall conflict : ReorgSelectedConflict,
    ReorgCoverEditHitsSelectedConflict edit conflict

/--
For selected reorg edits, hitting the conflict set is exactly satisfying the
finite conflict table.
-/
theorem reorgHitsSelectedConflictSet_iff_finiteConflictTable
    (edit : ReorgCoverEdit) :
    ReorgCoverEditHitsSelectedConflictSet edit ↔
      ReorgCoverEditFiniteConflictTable edit := by
  constructor
  · intro hhit
    exact
      ⟨hhit ReorgSelectedConflict.platformApi,
        hhit ReorgSelectedConflict.platformDb,
        hhit ReorgSelectedConflict.dataApi,
        hhit ReorgSelectedConflict.dataDb⟩
  · intro htable conflict
    rcases htable with ⟨hplatformApi, hplatformDb, hdataApi, hdataDb⟩
    cases conflict with
    | platformApi =>
        exact hplatformApi
    | platformDb =>
        exact hplatformDb
    | dataApi =>
        exact hdataApi
    | dataDb =>
        exact hdataDb

/--
For selected reorg edits, hitting the selected conflict set is exactly
existence of a selected repair-transition record.
-/
theorem reorgRepairTransition_nonempty_iff_hitsSelectedConflictSet
    (edit : ReorgCoverEdit) :
    Nonempty (ReorgCoverEditRepairTransition edit) ↔
      ReorgCoverEditHitsSelectedConflictSet edit := by
  rw [edit.repairTransition_nonempty_iff_finiteConflictTable,
    ← reorgHitsSelectedConflictSet_iff_finiteConflictTable]

/-- Canonical reorg hits the selected conflict set. -/
theorem canonicalReorgCoverEdit_hitsSelectedConflictSet :
    ReorgCoverEditHitsSelectedConflictSet canonicalReorgCoverEdit :=
  (reorgHitsSelectedConflictSet_iff_finiteConflictTable
    canonicalReorgCoverEdit).2
      canonicalReorgCoverEdit_finiteConflictTable

/-- The missed-conflict reorg edit misses the selected conflict set. -/
theorem partialReorgMissesDbConflict_not_hitsSelectedConflictSet :
    Not
      (ReorgCoverEditHitsSelectedConflictSet
        partialReorgMissesDbConflict) := by
  intro hhit
  exact partialReorgMissesDbConflict_not_finiteConflictTable
    ((reorgHitsSelectedConflictSet_iff_finiteConflictTable
      partialReorgMissesDbConflict).1 hhit)

/-! ## Selected refactor conflict set -/

/-- The selected finite refactor conflicts for the two-module vocabulary. -/
inductive RefactorSelectedConflict where
  | api
  | db
  deriving DecidableEq

namespace RefactorSelectedConflict

/-- Context of a selected refactor conflict. -/
def context : RefactorSelectedConflict -> Module
  | api => Module.api
  | db => Module.db

end RefactorSelectedConflict

/-- A selected refactor conflict is hit when the single owner supports it. -/
def RefactorOwnershipEditHitsSelectedConflict
    (edit : RefactorOwnershipEdit)
    (conflict : RefactorSelectedConflict) : Prop :=
  edit.ownership () (RefactorSelectedConflict.context conflict)

/-- A refactor edit hits every selected conflict. -/
def RefactorOwnershipEditHitsSelectedConflictSet
    (edit : RefactorOwnershipEdit) : Prop :=
  forall conflict : RefactorSelectedConflict,
    RefactorOwnershipEditHitsSelectedConflict edit conflict

/--
For selected refactor edits, hitting the conflict set is exactly satisfying the
finite conflict table.
-/
theorem refactorHitsSelectedConflictSet_iff_finiteConflictTable
    (edit : RefactorOwnershipEdit) :
    RefactorOwnershipEditHitsSelectedConflictSet edit ↔
      RefactorOwnershipEditFiniteConflictTable edit := by
  constructor
  · intro hhit
    exact
      ⟨hhit RefactorSelectedConflict.api,
        hhit RefactorSelectedConflict.db⟩
  · intro htable conflict
    rcases htable with ⟨hapi, hdb⟩
    cases conflict with
    | api =>
        exact hapi
    | db =>
        exact hdb

/--
For selected refactor edits, hitting the selected conflict set is exactly
existence of a selected repair-transition record.
-/
theorem refactorRepairTransition_nonempty_iff_hitsSelectedConflictSet
    (edit : RefactorOwnershipEdit) :
    Nonempty (RefactorOwnershipEditRepairTransition edit) ↔
      RefactorOwnershipEditHitsSelectedConflictSet edit := by
  rw [edit.repairTransition_nonempty_iff_finiteConflictTable,
    ← refactorHitsSelectedConflictSet_iff_finiteConflictTable]

/-- Canonical refactor hits the selected conflict set. -/
theorem canonicalRefactorOwnershipEdit_hitsSelectedConflictSet :
    RefactorOwnershipEditHitsSelectedConflictSet
      canonicalRefactorOwnershipEdit :=
  (refactorHitsSelectedConflictSet_iff_finiteConflictTable
    canonicalRefactorOwnershipEdit).2
      canonicalRefactorOwnershipEdit_finiteConflictTable

/-- The API-only refactor edit misses the selected conflict set. -/
theorem partialRefactorSupportsOnlyApi_not_hitsSelectedConflictSet :
    Not
      (RefactorOwnershipEditHitsSelectedConflictSet
        partialRefactorSupportsOnlyApi) := by
  intro hhit
  exact partialRefactorSupportsOnlyApi_not_finiteConflictTable
    ((refactorHitsSelectedConflictSet_iff_finiteConflictTable
      partialRefactorSupportsOnlyApi).1 hhit)

/--
The selected Cycle 29 package: selected conflict-set hitting is equivalent to
finite-table satisfaction and to selected repair-transition existence; canonical
repairs hit the selected sets, while missed-conflict edits do not.
-/
theorem selectedConflictSetPackage :
    (forall edit : ReorgCoverEdit,
      ReorgCoverEditHitsSelectedConflictSet edit ↔
        ReorgCoverEditFiniteConflictTable edit) /\
      (forall edit : ReorgCoverEdit,
        Nonempty (ReorgCoverEditRepairTransition edit) ↔
          ReorgCoverEditHitsSelectedConflictSet edit) /\
      ReorgCoverEditHitsSelectedConflictSet canonicalReorgCoverEdit /\
      Not
        (ReorgCoverEditHitsSelectedConflictSet
          partialReorgMissesDbConflict) /\
      (forall edit : RefactorOwnershipEdit,
        RefactorOwnershipEditHitsSelectedConflictSet edit ↔
          RefactorOwnershipEditFiniteConflictTable edit) /\
      (forall edit : RefactorOwnershipEdit,
        Nonempty (RefactorOwnershipEditRepairTransition edit) ↔
          RefactorOwnershipEditHitsSelectedConflictSet edit) /\
      RefactorOwnershipEditHitsSelectedConflictSet
        canonicalRefactorOwnershipEdit /\
      Not
        (RefactorOwnershipEditHitsSelectedConflictSet
          partialRefactorSupportsOnlyApi) := by
  exact
    ⟨reorgHitsSelectedConflictSet_iff_finiteConflictTable,
      reorgRepairTransition_nonempty_iff_hitsSelectedConflictSet,
      canonicalReorgCoverEdit_hitsSelectedConflictSet,
      partialReorgMissesDbConflict_not_hitsSelectedConflictSet,
      refactorHitsSelectedConflictSet_iff_finiteConflictTable,
      refactorRepairTransition_nonempty_iff_hitsSelectedConflictSet,
      canonicalRefactorOwnershipEdit_hitsSelectedConflictSet,
      partialRefactorSupportsOnlyApi_not_hitsSelectedConflictSet⟩

end ConwayTwoTopology
end SFT
end ResearchLean.AG
