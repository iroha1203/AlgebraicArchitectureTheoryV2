import Formal.AG.Research.SFT.ConwayCommunicationSupportAssignment

/-!
Cycle 26 evidence for `G-sft-conway-01`.

Cycle 25 introduced explicit communication-support assignments.  This file
adds a finite conflict table for the selected two-module Conway vocabulary:
the operation-shaped hitting predicates of Cycle 23 are equivalent to checking
the finite table entries, and the finite table is exactly what is needed to
produce support-assignment data for the post-edit atlas.

This is still selected finite Conway vocabulary.  It does not claim a general
conflict-set calculus for arbitrary covers, canonical repairs, or empirical
organizational causality.
-/

namespace Formal.AG.Research
namespace SFT
namespace ConwayTwoTopology

/-! ## Reorg-side finite conflict table -/

/--
The finite reorg conflict table.  Each possible `(team, module)` entry must be
owned by the owner assigned to that team after a reorg-side communication edit.
-/
def ReorgCoverEditFiniteConflictTable (edit : ReorgCoverEdit) : Prop :=
  (edit.communication Team.platform Module.api ->
    splitOwnership Owner.apiOwner Module.api) /\
    (edit.communication Team.platform Module.db ->
      splitOwnership Owner.apiOwner Module.db) /\
    (edit.communication Team.data Module.api ->
      splitOwnership Owner.dbOwner Module.api) /\
    (edit.communication Team.data Module.db ->
      splitOwnership Owner.dbOwner Module.db)

/--
For the finite two-module vocabulary, the reorg hitting predicate is exactly
the finite conflict table.
-/
theorem reorgCoverEditHitsEveryConflict_iff_finiteConflictTable
    (edit : ReorgCoverEdit) :
    ReorgCoverEditHitsEveryConflict edit ↔
      ReorgCoverEditFiniteConflictTable edit := by
  constructor
  · intro hhit
    rcases hhit with ⟨hplatform, hdata⟩
    exact
      ⟨hplatform Module.api,
        hplatform Module.db,
        hdata Module.api,
        hdata Module.db⟩
  · intro htable
    rcases htable with ⟨hplatformApi, hplatformDb, hdataApi, hdataDb⟩
    constructor
    · intro context hcomm
      cases context with
      | api =>
          exact hplatformApi hcomm
      | db =>
          exact hplatformDb hcomm
    · intro context hcomm
      cases context with
      | api =>
          exact hdataApi hcomm
      | db =>
          exact hdataDb hcomm

namespace ReorgCoverEdit

/--
For reorg edits, finite conflict-table satisfaction is equivalent to existence
of a support assignment for the post-edit atlas.
-/
theorem supportAssignment_nonempty_iff_finiteConflictTable
    (edit : ReorgCoverEdit) :
    Nonempty (CommunicationSupportAssignment edit.postAtlas) ↔
      ReorgCoverEditFiniteConflictTable edit := by
  rw [← communicationCoverCompatible_iff_supportAssignment edit.postAtlas,
    edit.postCompatible_iff_hitsEveryConflict,
    reorgCoverEditHitsEveryConflict_iff_finiteConflictTable]

end ReorgCoverEdit

/-- The canonical reorg edit satisfies the finite conflict table. -/
theorem canonicalReorgCoverEdit_finiteConflictTable :
    ReorgCoverEditFiniteConflictTable canonicalReorgCoverEdit := by
  exact
    (reorgCoverEditHitsEveryConflict_iff_finiteConflictTable
      canonicalReorgCoverEdit).1
        canonicalReorgCoverEdit_hitsEveryConflict

/-- The missed-conflict reorg edit fails the finite conflict table. -/
theorem partialReorgMissesDbConflict_not_finiteConflictTable :
    Not
      (ReorgCoverEditFiniteConflictTable
        partialReorgMissesDbConflict) := by
  intro htable
  exact partialReorgMissesDbConflict_not_hitsEveryConflict
    ((reorgCoverEditHitsEveryConflict_iff_finiteConflictTable
      partialReorgMissesDbConflict).2 htable)

/-! ## Refactor-side finite conflict table -/

/--
The finite refactor conflict table.  The single post-refactor owner block must
support both selected modules in the all-communication block.
-/
def RefactorOwnershipEditFiniteConflictTable
    (edit : RefactorOwnershipEdit) : Prop :=
  edit.ownership () Module.api /\
    edit.ownership () Module.db

/--
For the finite two-module vocabulary, the refactor hitting predicate is exactly
the finite conflict table.
-/
theorem refactorOwnershipEditHitsEveryConflict_iff_finiteConflictTable
    (edit : RefactorOwnershipEdit) :
    RefactorOwnershipEditHitsEveryConflict edit ↔
      RefactorOwnershipEditFiniteConflictTable edit := by
  constructor
  · intro hhit
    exact ⟨hhit Module.api, hhit Module.db⟩
  · intro htable
    rcases htable with ⟨hapi, hdb⟩
    intro context
    cases context with
    | api =>
        exact hapi
    | db =>
        exact hdb

namespace RefactorOwnershipEdit

/--
For refactor edits, finite conflict-table satisfaction is equivalent to
existence of a support assignment for the post-edit atlas.
-/
theorem supportAssignment_nonempty_iff_finiteConflictTable
    (edit : RefactorOwnershipEdit) :
    Nonempty (CommunicationSupportAssignment edit.postAtlas) ↔
      RefactorOwnershipEditFiniteConflictTable edit := by
  rw [← communicationCoverCompatible_iff_supportAssignment edit.postAtlas,
    edit.postCompatible_iff_hitsEveryConflict,
    refactorOwnershipEditHitsEveryConflict_iff_finiteConflictTable]

end RefactorOwnershipEdit

/-- The canonical refactor edit satisfies the finite conflict table. -/
theorem canonicalRefactorOwnershipEdit_finiteConflictTable :
    RefactorOwnershipEditFiniteConflictTable
      canonicalRefactorOwnershipEdit := by
  exact
    (refactorOwnershipEditHitsEveryConflict_iff_finiteConflictTable
      canonicalRefactorOwnershipEdit).1
        canonicalRefactorOwnershipEdit_hitsEveryConflict

/-- The API-only refactor edit fails the finite conflict table. -/
theorem partialRefactorSupportsOnlyApi_not_finiteConflictTable :
    Not
      (RefactorOwnershipEditFiniteConflictTable
        partialRefactorSupportsOnlyApi) := by
  intro htable
  exact partialRefactorSupportsOnlyApi_not_hitsEveryConflict
    ((refactorOwnershipEditHitsEveryConflict_iff_finiteConflictTable
      partialRefactorSupportsOnlyApi).2 htable)

/--
The selected Cycle 26 package: finite conflict tables are equivalent to the
operation-shaped hitting predicates, equivalent to post-edit support-assignment
existence, satisfied by canonical repairs, and refuted by the selected
missed-conflict edits.
-/
theorem selectedFiniteConflictTablePackage :
    (forall edit : ReorgCoverEdit,
      ReorgCoverEditHitsEveryConflict edit ↔
        ReorgCoverEditFiniteConflictTable edit) /\
      (forall edit : ReorgCoverEdit,
        Nonempty (CommunicationSupportAssignment edit.postAtlas) ↔
          ReorgCoverEditFiniteConflictTable edit) /\
      ReorgCoverEditFiniteConflictTable canonicalReorgCoverEdit /\
      Not
        (ReorgCoverEditFiniteConflictTable
          partialReorgMissesDbConflict) /\
      (forall edit : RefactorOwnershipEdit,
        RefactorOwnershipEditHitsEveryConflict edit ↔
          RefactorOwnershipEditFiniteConflictTable edit) /\
      (forall edit : RefactorOwnershipEdit,
        Nonempty (CommunicationSupportAssignment edit.postAtlas) ↔
          RefactorOwnershipEditFiniteConflictTable edit) /\
      RefactorOwnershipEditFiniteConflictTable
        canonicalRefactorOwnershipEdit /\
      Not
        (RefactorOwnershipEditFiniteConflictTable
          partialRefactorSupportsOnlyApi) := by
  exact
    ⟨reorgCoverEditHitsEveryConflict_iff_finiteConflictTable,
      ReorgCoverEdit.supportAssignment_nonempty_iff_finiteConflictTable,
      canonicalReorgCoverEdit_finiteConflictTable,
      partialReorgMissesDbConflict_not_finiteConflictTable,
      refactorOwnershipEditHitsEveryConflict_iff_finiteConflictTable,
      RefactorOwnershipEdit.supportAssignment_nonempty_iff_finiteConflictTable,
      canonicalRefactorOwnershipEdit_finiteConflictTable,
      partialRefactorSupportsOnlyApi_not_finiteConflictTable⟩

end ConwayTwoTopology
end SFT
end Formal.AG.Research
