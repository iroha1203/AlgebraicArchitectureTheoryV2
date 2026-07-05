import Formal.AG.Research.SFT.ConwayFiniteConflictTable

/-!
Cycle 27 evidence for `G-sft-conway-01`.

Cycle 25/26 supplied support-assignment and finite-table interfaces.  This file
uses them to record actual before/after transition objects for the selected
canonical Conway mismatch: canonical repairs start from `mismatchedAtlas` and
land in post-edit atlases with support assignments and no selected Conway
obstruction.  The selected missed-conflict edits are recorded as transition
failures because their post-edit atlases have no support assignment, and the
reorg missed-conflict transition still has an obstruction witness.

This remains selected finite Conway vocabulary.  It is not an arbitrary repair
calculus, optimality theorem, or empirical organizational-causality claim.
-/

namespace Formal.AG.Research
namespace SFT
namespace ConwayTwoTopology

/-! ## Selected repair and failure transition objects -/

/--
A selected Conway repair transition records a before-atlas with an obstruction
and an after-atlas with support-assignment existence and no selected Conway
obstruction.
-/
structure ConwayRepairTransition where
  before : TwoCoverAtlas
  after : TwoCoverAtlas
  beforeObstruction : ConwayObstructionWitness before
  afterSupportAssignment : Nonempty (CommunicationSupportAssignment after)
  afterNoObstruction : Not (ConwayObstructionWitness after)

/--
A selected transition failure records that the before-atlas has an obstruction
and the after-atlas still has no support-assignment data.
-/
structure ConwayAssignmentFailedTransition where
  before : TwoCoverAtlas
  after : TwoCoverAtlas
  beforeObstruction : ConwayObstructionWitness before
  afterNoSupportAssignment : Not (Nonempty (CommunicationSupportAssignment after))

/--
A selected obstruction-preserving transition failure records that the before
and after atlases both exhibit selected Conway obstruction witnesses.
-/
structure ConwayObstructionPreservingTransition where
  before : TwoCoverAtlas
  after : TwoCoverAtlas
  beforeObstruction : ConwayObstructionWitness before
  afterObstruction : ConwayObstructionWitness after
  afterNoSupportAssignment : Not (Nonempty (CommunicationSupportAssignment after))

namespace CanonicalRepairOperation

/--
Every canonical one-sided repair is a selected before/after transition from
the canonical mismatch to a support-assigned obstruction-free post-edit atlas.
-/
def repairTransition (operation : CanonicalRepairOperation) :
    ConwayRepairTransition where
  before := mismatchedAtlas
  after := CanonicalRepairOperation.postAtlas operation
  beforeObstruction := mismatchedAtlas_nonzeroConwayObstruction
  afterSupportAssignment :=
    ⟨CanonicalRepairOperation.supportAssignment operation⟩
  afterNoObstruction :=
    canonicalRepairOperation_killsConwayObstruction operation

/-- The transition target is the operation's post-edit atlas. -/
theorem repairTransition_after
    (operation : CanonicalRepairOperation) :
    (CanonicalRepairOperation.repairTransition operation).after =
      CanonicalRepairOperation.postAtlas operation :=
  rfl

/-- The transition source is the canonical mismatched atlas. -/
theorem repairTransition_before
    (operation : CanonicalRepairOperation) :
    (CanonicalRepairOperation.repairTransition operation).before =
      mismatchedAtlas :=
  rfl

end CanonicalRepairOperation

/-! ## Selected missed-conflict transition failures -/

/--
The missed-conflict reorg edit is not a repair transition: it starts from the
canonical mismatch, but the post-edit atlas still lacks a support assignment.
-/
def partialReorgMissesDbConflict_assignmentFailedTransition :
    ConwayAssignmentFailedTransition where
  before := mismatchedAtlas
  after := partialReorgMissesDbConflict.postAtlas
  beforeObstruction := mismatchedAtlas_nonzeroConwayObstruction
  afterNoSupportAssignment :=
    partialReorgMissesDbConflict_noCommunicationSupportAssignment

/--
The missed-conflict reorg edit is stronger than an assignment failure: it
preserves an actual selected Conway obstruction after the edit.
-/
def partialReorgMissesDbConflict_obstructionPreservingTransition :
    ConwayObstructionPreservingTransition where
  before := mismatchedAtlas
  after := partialReorgMissesDbConflict.postAtlas
  beforeObstruction := mismatchedAtlas_nonzeroConwayObstruction
  afterObstruction :=
    partialReorgMissesDbConflict_nonzeroConwayObstruction
  afterNoSupportAssignment :=
    partialReorgMissesDbConflict_noCommunicationSupportAssignment

/--
The API-only refactor edit is also not a repair transition in the support
assignment sense.  This statement deliberately does not claim a post-edit
two-owner obstruction witness for the single-owner refactor shape.
-/
def partialRefactorSupportsOnlyApi_assignmentFailedTransition :
    ConwayAssignmentFailedTransition where
  before := mismatchedAtlas
  after := partialRefactorSupportsOnlyApi.postAtlas
  beforeObstruction := mismatchedAtlas_nonzeroConwayObstruction
  afterNoSupportAssignment :=
    partialRefactorSupportsOnlyApi_noCommunicationSupportAssignment

/--
The selected Cycle 27 package: canonical repairs are before/after transitions
from `mismatchedAtlas` to support-assigned obstruction-free atlases, while the
selected missed-conflict edits are before/after failures; the reorg miss even
preserves a selected obstruction after the edit.
-/
theorem selectedRepairTransitionPackage :
    (forall operation : CanonicalRepairOperation,
      (CanonicalRepairOperation.repairTransition operation).before =
        mismatchedAtlas /\
        (CanonicalRepairOperation.repairTransition operation).after =
          CanonicalRepairOperation.postAtlas operation /\
        ConwayObstructionWitness
          (CanonicalRepairOperation.repairTransition operation).before /\
        Nonempty
          (CommunicationSupportAssignment
            (CanonicalRepairOperation.repairTransition operation).after) /\
        Not
          (ConwayObstructionWitness
            (CanonicalRepairOperation.repairTransition operation).after)) /\
      partialReorgMissesDbConflict_assignmentFailedTransition.before =
        mismatchedAtlas /\
      partialReorgMissesDbConflict_assignmentFailedTransition.after =
        partialReorgMissesDbConflict.postAtlas /\
      Not
        (Nonempty
          (CommunicationSupportAssignment
            partialReorgMissesDbConflict_assignmentFailedTransition.after)) /\
      partialReorgMissesDbConflict_obstructionPreservingTransition.before =
        mismatchedAtlas /\
      partialReorgMissesDbConflict_obstructionPreservingTransition.after =
        partialReorgMissesDbConflict.postAtlas /\
      ConwayObstructionWitness
        partialReorgMissesDbConflict_obstructionPreservingTransition.after /\
      partialRefactorSupportsOnlyApi_assignmentFailedTransition.before =
        mismatchedAtlas /\
      partialRefactorSupportsOnlyApi_assignmentFailedTransition.after =
        partialRefactorSupportsOnlyApi.postAtlas /\
      Not
        (Nonempty
          (CommunicationSupportAssignment
            partialRefactorSupportsOnlyApi_assignmentFailedTransition.after)) := by
  exact
    ⟨(by
        intro operation
        exact
          ⟨CanonicalRepairOperation.repairTransition_before operation,
            CanonicalRepairOperation.repairTransition_after operation,
            (CanonicalRepairOperation.repairTransition
              operation).beforeObstruction,
            (CanonicalRepairOperation.repairTransition
              operation).afterSupportAssignment,
            (CanonicalRepairOperation.repairTransition
              operation).afterNoObstruction⟩),
      rfl,
      rfl,
      partialReorgMissesDbConflict_assignmentFailedTransition
        |>.afterNoSupportAssignment,
      rfl,
      rfl,
      partialReorgMissesDbConflict_obstructionPreservingTransition
        |>.afterObstruction,
      rfl,
      rfl,
      partialRefactorSupportsOnlyApi_assignmentFailedTransition
        |>.afterNoSupportAssignment⟩

end ConwayTwoTopology
end SFT
end Formal.AG.Research
