import ResearchLean.AG.SFT.ConwaySelectedConflictMembership

/-!
Cycle 33 evidence for `G-sft-conway-01`.

Cycle 32 added pointwise selected misses and exact miss identities for the
selected partial edits.  This file adds a bounded finite first-miss scanner:
for each selected edit shape, a first selected miss exists exactly when some
selected miss exists, it is sound, and the existing partial edits have the
expected exact first miss.

This is a selected finite scanner over the Conway two-module vocabulary.  It is
not a runtime extraction algorithm or arbitrary conflict enumeration procedure.
-/

namespace ResearchLean.AG
namespace SFT
namespace ConwayTwoTopology

/-! ## Reorg first-miss scanner -/

/--
The selected reorg first-miss predicate, ordered as platform-API, platform-DB,
data-API, data-DB.
-/
def ReorgCoverEditFirstSelectedMiss
    (edit : ReorgCoverEdit)
    (conflict : ReorgSelectedConflict) : Prop :=
  match conflict with
  | ReorgSelectedConflict.platformApi =>
      ReorgCoverEditMissesSelectedConflict
        edit ReorgSelectedConflict.platformApi
  | ReorgSelectedConflict.platformDb =>
      Not
          (ReorgCoverEditMissesSelectedConflict
            edit ReorgSelectedConflict.platformApi) /\
        ReorgCoverEditMissesSelectedConflict
          edit ReorgSelectedConflict.platformDb
  | ReorgSelectedConflict.dataApi =>
      Not
          (ReorgCoverEditMissesSelectedConflict
            edit ReorgSelectedConflict.platformApi) /\
        Not
          (ReorgCoverEditMissesSelectedConflict
            edit ReorgSelectedConflict.platformDb) /\
        ReorgCoverEditMissesSelectedConflict
          edit ReorgSelectedConflict.dataApi
  | ReorgSelectedConflict.dataDb =>
      Not
          (ReorgCoverEditMissesSelectedConflict
            edit ReorgSelectedConflict.platformApi) /\
        Not
          (ReorgCoverEditMissesSelectedConflict
            edit ReorgSelectedConflict.platformDb) /\
        Not
          (ReorgCoverEditMissesSelectedConflict
            edit ReorgSelectedConflict.dataApi) /\
        ReorgCoverEditMissesSelectedConflict
          edit ReorgSelectedConflict.dataDb

/-- A selected reorg first miss is a selected miss. -/
theorem reorgFirstSelectedMiss_sound
    (edit : ReorgCoverEdit)
    (conflict : ReorgSelectedConflict)
    (hfirst : ReorgCoverEditFirstSelectedMiss edit conflict) :
    ReorgCoverEditMissesSelectedConflict edit conflict := by
  cases conflict with
  | platformApi =>
      exact hfirst
  | platformDb =>
      exact hfirst.2
  | dataApi =>
      exact hfirst.2.2
  | dataDb =>
      exact hfirst.2.2.2

/-- A selected reorg first miss exists exactly when some selected miss exists. -/
theorem reorgFirstSelectedMiss_exists_iff_hasSelectedMiss
    (edit : ReorgCoverEdit) :
    (exists conflict : ReorgSelectedConflict,
      ReorgCoverEditFirstSelectedMiss edit conflict) ↔
      exists conflict : ReorgSelectedConflict,
        ReorgCoverEditMissesSelectedConflict edit conflict := by
  constructor
  · intro hfirst
    rcases hfirst with ⟨conflict, hconflict⟩
    exact ⟨conflict, reorgFirstSelectedMiss_sound edit conflict hconflict⟩
  · intro hmiss
    classical
    by_cases hplatformApi :
        ReorgCoverEditMissesSelectedConflict
          edit ReorgSelectedConflict.platformApi
    · exact ⟨ReorgSelectedConflict.platformApi, hplatformApi⟩
    by_cases hplatformDb :
        ReorgCoverEditMissesSelectedConflict
          edit ReorgSelectedConflict.platformDb
    · exact
        ⟨ReorgSelectedConflict.platformDb,
          ⟨hplatformApi, hplatformDb⟩⟩
    by_cases hdataApi :
        ReorgCoverEditMissesSelectedConflict
          edit ReorgSelectedConflict.dataApi
    · exact
        ⟨ReorgSelectedConflict.dataApi,
          ⟨hplatformApi, hplatformDb, hdataApi⟩⟩
    by_cases hdataDb :
        ReorgCoverEditMissesSelectedConflict
          edit ReorgSelectedConflict.dataDb
    · exact
        ⟨ReorgSelectedConflict.dataDb,
          ⟨hplatformApi, hplatformDb, hdataApi, hdataDb⟩⟩
    rcases hmiss with ⟨conflict, hconflict⟩
    cases conflict with
    | platformApi =>
        exact False.elim (hplatformApi hconflict)
    | platformDb =>
        exact False.elim (hplatformDb hconflict)
    | dataApi =>
        exact False.elim (hdataApi hconflict)
    | dataDb =>
        exact False.elim (hdataDb hconflict)

/-- The canonical reorg edit has no selected first miss. -/
theorem canonicalReorgCoverEdit_noFirstSelectedMiss :
    Not
      (exists conflict : ReorgSelectedConflict,
        ReorgCoverEditFirstSelectedMiss
          canonicalReorgCoverEdit conflict) := by
  intro hfirst
  rcases (reorgFirstSelectedMiss_exists_iff_hasSelectedMiss
    canonicalReorgCoverEdit).1 hfirst with ⟨conflict, hmiss⟩
  exact canonicalReorgCoverEdit_noSelectedMiss conflict hmiss

/-- The partial reorg edit has exactly platform-DB as its first selected miss. -/
theorem partialReorgMissesDbConflict_firstSelectedMiss_iff
    (conflict : ReorgSelectedConflict) :
    ReorgCoverEditFirstSelectedMiss
      partialReorgMissesDbConflict conflict ↔
      conflict = ReorgSelectedConflict.platformDb := by
  constructor
  · intro hfirst
    have hmiss :=
      reorgFirstSelectedMiss_sound
        partialReorgMissesDbConflict conflict hfirst
    exact
      (partialReorgMissesDbConflict_missesSelectedConflict_iff
        conflict).1 hmiss
  · intro hconflict
    subst hconflict
    constructor
    · intro hmiss
      have hbad :=
        (partialReorgMissesDbConflict_missesSelectedConflict_iff
          ReorgSelectedConflict.platformApi).1 hmiss
      cases hbad
    · exact
        (partialReorgMissesDbConflict_missesSelectedConflict_iff
          ReorgSelectedConflict.platformDb).2 rfl

/-! ## Refactor first-miss scanner -/

/-- The selected refactor first-miss predicate, ordered as API then DB. -/
def RefactorOwnershipEditFirstSelectedMiss
    (edit : RefactorOwnershipEdit)
    (conflict : RefactorSelectedConflict) : Prop :=
  match conflict with
  | RefactorSelectedConflict.api =>
      RefactorOwnershipEditMissesSelectedConflict
        edit RefactorSelectedConflict.api
  | RefactorSelectedConflict.db =>
      Not
          (RefactorOwnershipEditMissesSelectedConflict
            edit RefactorSelectedConflict.api) /\
        RefactorOwnershipEditMissesSelectedConflict
          edit RefactorSelectedConflict.db

/-- A selected refactor first miss is a selected miss. -/
theorem refactorFirstSelectedMiss_sound
    (edit : RefactorOwnershipEdit)
    (conflict : RefactorSelectedConflict)
    (hfirst : RefactorOwnershipEditFirstSelectedMiss edit conflict) :
    RefactorOwnershipEditMissesSelectedConflict edit conflict := by
  cases conflict with
  | api =>
      exact hfirst
  | db =>
      exact hfirst.2

/-- A selected refactor first miss exists exactly when some selected miss exists. -/
theorem refactorFirstSelectedMiss_exists_iff_hasSelectedMiss
    (edit : RefactorOwnershipEdit) :
    (exists conflict : RefactorSelectedConflict,
      RefactorOwnershipEditFirstSelectedMiss edit conflict) ↔
      exists conflict : RefactorSelectedConflict,
        RefactorOwnershipEditMissesSelectedConflict edit conflict := by
  constructor
  · intro hfirst
    rcases hfirst with ⟨conflict, hconflict⟩
    exact ⟨conflict, refactorFirstSelectedMiss_sound edit conflict hconflict⟩
  · intro hmiss
    classical
    by_cases hapi :
        RefactorOwnershipEditMissesSelectedConflict
          edit RefactorSelectedConflict.api
    · exact ⟨RefactorSelectedConflict.api, hapi⟩
    by_cases hdb :
        RefactorOwnershipEditMissesSelectedConflict
          edit RefactorSelectedConflict.db
    · exact ⟨RefactorSelectedConflict.db, ⟨hapi, hdb⟩⟩
    rcases hmiss with ⟨conflict, hconflict⟩
    cases conflict with
    | api =>
        exact False.elim (hapi hconflict)
    | db =>
        exact False.elim (hdb hconflict)

/-- The canonical refactor edit has no selected first miss. -/
theorem canonicalRefactorOwnershipEdit_noFirstSelectedMiss :
    Not
      (exists conflict : RefactorSelectedConflict,
        RefactorOwnershipEditFirstSelectedMiss
          canonicalRefactorOwnershipEdit conflict) := by
  intro hfirst
  rcases (refactorFirstSelectedMiss_exists_iff_hasSelectedMiss
    canonicalRefactorOwnershipEdit).1 hfirst with ⟨conflict, hmiss⟩
  exact canonicalRefactorOwnershipEdit_noSelectedMiss conflict hmiss

/-- The API-only refactor edit has exactly DB as its first selected miss. -/
theorem partialRefactorSupportsOnlyApi_firstSelectedMiss_iff
    (conflict : RefactorSelectedConflict) :
    RefactorOwnershipEditFirstSelectedMiss
      partialRefactorSupportsOnlyApi conflict ↔
      conflict = RefactorSelectedConflict.db := by
  constructor
  · intro hfirst
    have hmiss :=
      refactorFirstSelectedMiss_sound
        partialRefactorSupportsOnlyApi conflict hfirst
    exact
      (partialRefactorSupportsOnlyApi_missesSelectedConflict_iff
        conflict).1 hmiss
  · intro hconflict
    subst hconflict
    constructor
    · intro hmiss
      have hbad :=
        (partialRefactorSupportsOnlyApi_missesSelectedConflict_iff
          RefactorSelectedConflict.api).1 hmiss
      cases hbad
    · exact
        (partialRefactorSupportsOnlyApi_missesSelectedConflict_iff
          RefactorSelectedConflict.db).2 rfl

/--
The selected Cycle 33 package: first-miss scanners are sound and complete for
the selected miss predicates, canonical repairs have no first miss, and partial
edits have exact first-miss selectors.
-/
theorem selectedMissScannerPackage :
    (forall edit : ReorgCoverEdit,
      (exists conflict : ReorgSelectedConflict,
        ReorgCoverEditFirstSelectedMiss edit conflict) ↔
        exists conflict : ReorgSelectedConflict,
          ReorgCoverEditMissesSelectedConflict edit conflict) /\
      (forall edit : ReorgCoverEdit,
        forall conflict : ReorgSelectedConflict,
          ReorgCoverEditFirstSelectedMiss edit conflict ->
            ReorgCoverEditMissesSelectedConflict edit conflict) /\
      Not
        (exists conflict : ReorgSelectedConflict,
          ReorgCoverEditFirstSelectedMiss
            canonicalReorgCoverEdit conflict) /\
      (forall conflict : ReorgSelectedConflict,
        ReorgCoverEditFirstSelectedMiss
          partialReorgMissesDbConflict conflict ↔
          conflict = ReorgSelectedConflict.platformDb) /\
      (forall edit : RefactorOwnershipEdit,
        (exists conflict : RefactorSelectedConflict,
          RefactorOwnershipEditFirstSelectedMiss edit conflict) ↔
          exists conflict : RefactorSelectedConflict,
            RefactorOwnershipEditMissesSelectedConflict edit conflict) /\
      (forall edit : RefactorOwnershipEdit,
        forall conflict : RefactorSelectedConflict,
          RefactorOwnershipEditFirstSelectedMiss edit conflict ->
            RefactorOwnershipEditMissesSelectedConflict edit conflict) /\
      Not
        (exists conflict : RefactorSelectedConflict,
          RefactorOwnershipEditFirstSelectedMiss
            canonicalRefactorOwnershipEdit conflict) /\
      (forall conflict : RefactorSelectedConflict,
        RefactorOwnershipEditFirstSelectedMiss
          partialRefactorSupportsOnlyApi conflict ↔
          conflict = RefactorSelectedConflict.db) := by
  exact
    ⟨reorgFirstSelectedMiss_exists_iff_hasSelectedMiss,
      reorgFirstSelectedMiss_sound,
      canonicalReorgCoverEdit_noFirstSelectedMiss,
      partialReorgMissesDbConflict_firstSelectedMiss_iff,
      refactorFirstSelectedMiss_exists_iff_hasSelectedMiss,
      refactorFirstSelectedMiss_sound,
      canonicalRefactorOwnershipEdit_noFirstSelectedMiss,
      partialRefactorSupportsOnlyApi_firstSelectedMiss_iff⟩

end ConwayTwoTopology
end SFT
end ResearchLean.AG
