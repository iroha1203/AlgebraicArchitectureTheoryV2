import Formal.AG.Research.SFT.ConwayRepairTransition

/-!
Cycle 31 evidence for `G-sft-conway-01`.

Cycle 24 deliberately limited the refactor-side negative witness to
compatibility failure because `RefactorOwnershipEdit` collapses ownership to a
single owner index.  This file closes the bounded two-owner gap by adding a
selected refactor-failure shape whose communication cover is still the
all-communication block but whose ownership cover keeps the split two-owner
shape.  That post-edit atlas is definitionally the canonical mismatched atlas,
so it preserves an actual selected Conway obstruction.

This is a selected finite witness.  It is not an arbitrary refactor calculus or
an empirical claim about real organization changes.
-/

namespace Formal.AG.Research
namespace SFT
namespace ConwayTwoTopology

/-! ## Two-owner refactor failure shape -/

/--
A refactor-side failure shape that keeps the all-communication block but allows
the ownership cover to remain two-owner indexed.
-/
structure RefactorTwoOwnerFailureEdit where
  ownership : Owner -> Module -> Prop

/-- The post-edit atlas for a two-owner refactor failure. -/
def RefactorTwoOwnerFailureEdit.postAtlas
    (edit : RefactorTwoOwnerFailureEdit) : TwoCoverAtlas where
  CommIdx := Unit
  OwnerIdx := Owner
  Context := Module
  communication := allCommunication
  ownership := edit.ownership

/--
The selected failed refactor that keeps split ownership while communication
remains all-to-all.
-/
def refactorKeepsSplitOwnership : RefactorTwoOwnerFailureEdit where
  ownership := splitOwnership

/--
The failed two-owner refactor post-atlas is the canonical mismatched atlas.
-/
theorem refactorKeepsSplitOwnership_postAtlas_eq_mismatchedAtlas :
    refactorKeepsSplitOwnership.postAtlas = mismatchedAtlas :=
  rfl

/--
The failed two-owner refactor is not compatible.
-/
theorem refactorKeepsSplitOwnership_not_compatible :
    Not
      (CommunicationCoverCompatible
        refactorKeepsSplitOwnership.postAtlas) := by
  simpa [refactorKeepsSplitOwnership_postAtlas_eq_mismatchedAtlas] using
    mismatchedAtlas_notCommunicationCompatible

/--
The failed two-owner refactor preserves an actual selected Conway obstruction.
-/
theorem refactorKeepsSplitOwnership_nonzeroConwayObstruction :
    ConwayObstructionWitness refactorKeepsSplitOwnership.postAtlas := by
  simpa [refactorKeepsSplitOwnership_postAtlas_eq_mismatchedAtlas] using
    mismatchedAtlas_nonzeroConwayObstruction

/--
The failed two-owner refactor has no post-edit support assignment.
-/
theorem refactorKeepsSplitOwnership_noCommunicationSupportAssignment :
    Not
      (Nonempty
        (CommunicationSupportAssignment
          refactorKeepsSplitOwnership.postAtlas)) := by
  intro hassignment
  rcases hassignment with ⟨assignment⟩
  exact refactorKeepsSplitOwnership_not_compatible
    assignment.toCompatibility

/--
The failed two-owner refactor is an obstruction-preserving transition from the
canonical mismatch back to a post-edit atlas with the same selected obstruction.
-/
def refactorKeepsSplitOwnership_obstructionPreservingTransition :
    ConwayObstructionPreservingTransition where
  before := mismatchedAtlas
  after := refactorKeepsSplitOwnership.postAtlas
  beforeObstruction := mismatchedAtlas_nonzeroConwayObstruction
  afterObstruction :=
    refactorKeepsSplitOwnership_nonzeroConwayObstruction
  afterNoSupportAssignment :=
    refactorKeepsSplitOwnership_noCommunicationSupportAssignment

/--
The selected Cycle 31 package: a two-owner refactor failure shape can preserve
the selected Conway obstruction after the edit, closing the single-owner
limitation of the Cycle 24 refactor negative witness.
-/
theorem selectedRefactorTwoOwnerObstructionPackage :
    refactorKeepsSplitOwnership.postAtlas = mismatchedAtlas /\
      Not
        (CommunicationCoverCompatible
          refactorKeepsSplitOwnership.postAtlas) /\
      ConwayObstructionWitness
        refactorKeepsSplitOwnership.postAtlas /\
      Not
        (Nonempty
          (CommunicationSupportAssignment
            refactorKeepsSplitOwnership.postAtlas)) /\
      refactorKeepsSplitOwnership_obstructionPreservingTransition.before =
        mismatchedAtlas /\
      refactorKeepsSplitOwnership_obstructionPreservingTransition.after =
        refactorKeepsSplitOwnership.postAtlas /\
      ConwayObstructionWitness
        refactorKeepsSplitOwnership_obstructionPreservingTransition.after := by
  exact
    ⟨refactorKeepsSplitOwnership_postAtlas_eq_mismatchedAtlas,
      refactorKeepsSplitOwnership_not_compatible,
      refactorKeepsSplitOwnership_nonzeroConwayObstruction,
      refactorKeepsSplitOwnership_noCommunicationSupportAssignment,
      rfl,
      rfl,
      refactorKeepsSplitOwnership_obstructionPreservingTransition
        |>.afterObstruction⟩

end ConwayTwoTopology
end SFT
end Formal.AG.Research
