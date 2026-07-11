import ResearchLean.AG.SFT.ConwayReorgRefactorNegativeWitness

/-!
Cycle 25 evidence for `G-sft-conway-01`.

Cycle 23/24 gave operation-shaped hitting criteria and finite negative
witnesses.  This file factors the compatible side through a general
communication-support assignment: a choice of one ownership block supporting
each communication block.  The selected mismatch and missed-conflict edits have
no such assignment, while both canonical one-sided repairs do.

This remains selected finite Conway vocabulary.  It does not claim an
arbitrary repair calculus, a canonical assignment, optimality, or empirical
organizational causality.
-/

namespace ResearchLean.AG
namespace SFT
namespace ConwayTwoTopology

/-! ## Communication-support assignments -/

/--
A communication-support assignment chooses one ownership block for every
communication block and proves that it supports the whole communication block.
-/
structure CommunicationSupportAssignment (atlas : TwoCoverAtlas) where
  ownerOf : atlas.CommIdx -> atlas.OwnerIdx
  supports :
    forall comm context,
      atlas.communication comm context ->
        atlas.ownership (ownerOf comm) context

namespace CommunicationSupportAssignment

/-- A communication-support assignment is exactly compatibility data. -/
theorem toCompatibility {atlas : TwoCoverAtlas}
    (assignment : CommunicationSupportAssignment atlas) :
    CommunicationCoverCompatible atlas := by
  intro comm
  exact ⟨assignment.ownerOf comm, assignment.supports comm⟩

/-- Compatibility can be recorded as a communication-support assignment. -/
noncomputable def ofCompatibility {atlas : TwoCoverAtlas}
    (compatible : CommunicationCoverCompatible atlas) :
    CommunicationSupportAssignment atlas where
  ownerOf comm := Classical.choose (compatible comm)
  supports comm := Classical.choose_spec (compatible comm)

end CommunicationSupportAssignment

/--
Communication-cover compatibility is equivalent to existence of explicit
communication-support assignment data.
-/
theorem communicationCoverCompatible_iff_supportAssignment
    (atlas : TwoCoverAtlas) :
    CommunicationCoverCompatible atlas ↔
      Nonempty (CommunicationSupportAssignment atlas) := by
  constructor
  · intro compatible
    exact ⟨CommunicationSupportAssignment.ofCompatibility compatible⟩
  · intro hassignment
    rcases hassignment with ⟨assignment⟩
    exact assignment.toCompatibility

/-! ## Selected canonical and missed-conflict assignments -/

/-- The canonical reorg repair has an explicit communication-support assignment. -/
def canonicalReorgCoverEdit_supportAssignment :
    CommunicationSupportAssignment canonicalReorgCoverEdit.postAtlas where
  ownerOf
    | Team.platform => Owner.apiOwner
    | Team.data => Owner.dbOwner
  supports := by
    intro comm context hcomm
    cases comm <;> cases context <;>
      simp [canonicalReorgCoverEdit, ReorgCoverEdit.postAtlas,
        splitCommunication, splitOwnership] at hcomm ⊢

/-- The canonical refactor repair has an explicit communication-support assignment. -/
def canonicalRefactorOwnershipEdit_supportAssignment :
    CommunicationSupportAssignment canonicalRefactorOwnershipEdit.postAtlas where
  ownerOf _ := ()
  supports := by
    intro comm context _hcomm
    cases comm
    cases context <;>
      simp [canonicalRefactorOwnershipEdit, RefactorOwnershipEdit.postAtlas,
        mergedOwnership]

namespace CanonicalRepairOperation

/-- Every canonical one-sided repair has explicit support-assignment data. -/
def supportAssignment (operation : CanonicalRepairOperation) :
    CommunicationSupportAssignment
      (CanonicalRepairOperation.postAtlas operation) := by
  cases operation with
  | reorg =>
      exact canonicalReorgCoverEdit_supportAssignment
  | refactor =>
      exact canonicalRefactorOwnershipEdit_supportAssignment

/-- Every canonical one-sided repair is compatible because it has an assignment. -/
theorem compatible_of_supportAssignment
    (operation : CanonicalRepairOperation) :
    CommunicationCoverCompatible
      (CanonicalRepairOperation.postAtlas operation) :=
  (supportAssignment operation).toCompatibility

end CanonicalRepairOperation

/-- The canonical mismatch has no communication-support assignment. -/
theorem mismatchedAtlas_noCommunicationSupportAssignment :
    Not (Nonempty (CommunicationSupportAssignment mismatchedAtlas)) := by
  intro hassignment
  rcases hassignment with ⟨assignment⟩
  exact mismatchedAtlas_notCommunicationCompatible assignment.toCompatibility

/-- The missed-conflict reorg edit has no communication-support assignment. -/
theorem partialReorgMissesDbConflict_noCommunicationSupportAssignment :
    Not
      (Nonempty
        (CommunicationSupportAssignment
          partialReorgMissesDbConflict.postAtlas)) := by
  intro hassignment
  rcases hassignment with ⟨assignment⟩
  exact partialReorgMissesDbConflict_not_compatible
    assignment.toCompatibility

/-- The API-only refactor edit has no communication-support assignment. -/
theorem partialRefactorSupportsOnlyApi_noCommunicationSupportAssignment :
    Not
      (Nonempty
        (CommunicationSupportAssignment
          partialRefactorSupportsOnlyApi.postAtlas)) := by
  intro hassignment
  rcases hassignment with ⟨assignment⟩
  exact partialRefactorSupportsOnlyApi_not_compatible
    assignment.toCompatibility

/--
The selected Cycle 25 package: compatibility is equivalent to explicit
support-assignment data; the canonical mismatch and missed-conflict edits have
no assignment; and both canonical one-sided repairs have assignments,
compatibility, and no selected Conway obstruction.
-/
theorem selectedCommunicationSupportAssignmentPackage :
    (forall atlas : TwoCoverAtlas,
      CommunicationCoverCompatible atlas ↔
        Nonempty (CommunicationSupportAssignment atlas)) /\
      ConwayObstructionWitness mismatchedAtlas /\
      Not (Nonempty (CommunicationSupportAssignment mismatchedAtlas)) /\
      (forall operation : CanonicalRepairOperation,
        Nonempty
          (CommunicationSupportAssignment
            (CanonicalRepairOperation.postAtlas operation)) /\
          CommunicationCoverCompatible
            (CanonicalRepairOperation.postAtlas operation) /\
          Not
            (ConwayObstructionWitness
              (CanonicalRepairOperation.postAtlas operation))) /\
      Not
        (Nonempty
          (CommunicationSupportAssignment
            partialReorgMissesDbConflict.postAtlas)) /\
      Not
        (Nonempty
          (CommunicationSupportAssignment
            partialRefactorSupportsOnlyApi.postAtlas)) := by
  exact
    ⟨communicationCoverCompatible_iff_supportAssignment,
      mismatchedAtlas_nonzeroConwayObstruction,
      mismatchedAtlas_noCommunicationSupportAssignment,
      (by
        intro operation
        exact
          ⟨⟨CanonicalRepairOperation.supportAssignment operation⟩,
            CanonicalRepairOperation.compatible_of_supportAssignment operation,
            canonicalRepairOperation_killsConwayObstruction operation⟩),
      partialReorgMissesDbConflict_noCommunicationSupportAssignment,
      partialRefactorSupportsOnlyApi_noCommunicationSupportAssignment⟩

end ConwayTwoTopology
end SFT
end ResearchLean.AG
