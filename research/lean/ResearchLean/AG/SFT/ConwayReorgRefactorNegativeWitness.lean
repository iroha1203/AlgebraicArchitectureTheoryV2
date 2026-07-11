import ResearchLean.AG.SFT.ConwayReorgRefactorKilling

/-!
Cycle 24 evidence for `G-sft-conway-01`.

Cycle 23 introduced canonical reorg/refactor operation-shaped compatibility
criteria.  This file adds finite negative witnesses: a reorg edit that misses
the DB-side conflict leaves an actual Conway obstruction, and a refactor edit
that only supports the API context fails the refactor hitting/compatibility
criterion.  The refactor negative witness is deliberately limited to
compatibility failure because the Cycle 23 refactor shape has a single owner
index, so it cannot witness two distinct owners.

This remains finite selected Conway vocabulary.  It does not claim an arbitrary
operation calculus, optimal repair, real organizational causality, or sheaf
cohomology.
-/

namespace Formal.AG.Research
namespace SFT
namespace ConwayTwoTopology

/-! ## Reorg-side missed-conflict witness -/

/--
A partial reorg edit that still lets the platform communication block see both
API and DB.  It covers the required API/DB witnesses, but it misses the
platform-DB conflict.
-/
def partialReorgMissesDbConflict : ReorgCoverEdit where
  communication
    | Team.platform, _ => True
    | Team.data, Module.db => True
    | Team.data, Module.api => False
  coversApi := by
    simp
  coversDb := by
    simp

/-- The partial reorg edit misses the hitting criterion. -/
theorem partialReorgMissesDbConflict_not_hitsEveryConflict :
    Not
      (ReorgCoverEditHitsEveryConflict
        partialReorgMissesDbConflict) := by
  intro hhit
  have hplatform :=
    hhit.1 Module.db
      (by
        simp [partialReorgMissesDbConflict])
  simp [splitOwnership] at hplatform

/-- The partial reorg edit is not post-edit compatible. -/
theorem partialReorgMissesDbConflict_not_compatible :
    Not
      (CommunicationCoverCompatible
        partialReorgMissesDbConflict.postAtlas) := by
  intro hcompatible
  exact partialReorgMissesDbConflict_not_hitsEveryConflict
    ((partialReorgMissesDbConflict.postCompatible_iff_hitsEveryConflict).1
      hcompatible)

/-- The partial reorg edit leaves an actual selected Conway obstruction. -/
theorem partialReorgMissesDbConflict_nonzeroConwayObstruction :
    ConwayObstructionWitness partialReorgMissesDbConflict.postAtlas := by
  refine
    ⟨Team.platform, Module.api, Module.db, Owner.apiOwner, Owner.dbOwner,
      ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [ReorgCoverEdit.postAtlas, partialReorgMissesDbConflict]
  · simp [ReorgCoverEdit.postAtlas, partialReorgMissesDbConflict]
  · simp [ReorgCoverEdit.postAtlas, splitOwnership]
  · simp [ReorgCoverEdit.postAtlas, splitOwnership]
  · intro howners
    cases howners
  · intro hsupported
    rcases hsupported with ⟨owner, howner⟩
    have hapi : splitOwnership owner Module.api :=
      howner Module.api
        (by simp [ReorgCoverEdit.postAtlas, partialReorgMissesDbConflict])
    have hdb : splitOwnership owner Module.db :=
      howner Module.db
        (by simp [ReorgCoverEdit.postAtlas, partialReorgMissesDbConflict])
    cases owner <;> simp [splitOwnership] at hapi hdb

/-! ## Refactor-side missed-conflict witness -/

/--
A partial refactor edit that supports API but not DB.  It has the Cycle 23
single-owner refactor shape, so the precise negative statement is hitting and
compatibility failure, not a two-owner obstruction witness.
-/
def partialRefactorSupportsOnlyApi : RefactorOwnershipEdit where
  ownership
    | (), Module.api => True
    | (), Module.db => False

/-- The partial refactor edit misses the hitting criterion. -/
theorem partialRefactorSupportsOnlyApi_not_hitsEveryConflict :
    Not
      (RefactorOwnershipEditHitsEveryConflict
        partialRefactorSupportsOnlyApi) := by
  intro hhit
  have hdb := hhit Module.db
  simp [partialRefactorSupportsOnlyApi] at hdb

/-- The partial refactor edit is not post-edit compatible. -/
theorem partialRefactorSupportsOnlyApi_not_compatible :
    Not
      (CommunicationCoverCompatible
        partialRefactorSupportsOnlyApi.postAtlas) := by
  intro hcompatible
  exact partialRefactorSupportsOnlyApi_not_hitsEveryConflict
    ((partialRefactorSupportsOnlyApi.postCompatible_iff_hitsEveryConflict).1
      hcompatible)

/--
The selected Cycle 24 package: missing a canonical reorg conflict leaves an
actual obstruction, while missing the refactor support condition fails the
refactor hitting/compatibility criterion.
-/
theorem selectedReorgRefactorNegativeWitnessPackage :
    Not
      (ReorgCoverEditHitsEveryConflict
        partialReorgMissesDbConflict) /\
      Not
        (CommunicationCoverCompatible
          partialReorgMissesDbConflict.postAtlas) /\
      ConwayObstructionWitness
        partialReorgMissesDbConflict.postAtlas /\
      Not
        (RefactorOwnershipEditHitsEveryConflict
          partialRefactorSupportsOnlyApi) /\
      Not
        (CommunicationCoverCompatible
          partialRefactorSupportsOnlyApi.postAtlas) := by
  exact
    ⟨partialReorgMissesDbConflict_not_hitsEveryConflict,
      partialReorgMissesDbConflict_not_compatible,
      partialReorgMissesDbConflict_nonzeroConwayObstruction,
      partialRefactorSupportsOnlyApi_not_hitsEveryConflict,
      partialRefactorSupportsOnlyApi_not_compatible⟩

end ConwayTwoTopology
end SFT
end Formal.AG.Research
