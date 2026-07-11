import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Group.Subgroup.Lattice
import ResearchLean.AG.SFT.ConwaySupportReceiver

/-!
Cycle 3 evidence for `G-sft-conway-01`.

Cycle 2 located the selected Conway obstruction in a support-nerve fork
receiver.  This file adds the first boundary-quotient reading of that receiver:
support forks are treated as the selected `C^1` data, single-owner supported
forks as the selected boundary part `B^1`, and a nonzero class is a fork outside
that boundary part.

This is intentionally a finite `C^1/B^1`-style receiver, not a full sheaf
cohomology construction.
-/

namespace Formal.AG.Research
namespace SFT
namespace ConwayTwoTopology

/-! ## Boundary quotient vocabulary -/

/-- The selected finite coefficient group for the Cycle 3 boundary receiver. -/
abbrev ConwayZ2 :=
  ZMod 2

/-- The selected one-cochains are support-nerve forks. -/
abbrev SupportForkOneCochain (atlas : TwoCoverAtlas) :=
  SupportNerveFork atlas

/-- The selected degree-one defect carried by a support fork. -/
def SupportForkDefect {atlas : TwoCoverAtlas}
    (_fork : SupportForkOneCochain atlas) : ConwayZ2 :=
  1

/-- The selected defect is the nonzero coefficient in `ZMod 2`. -/
theorem supportForkDefect_nonzero {atlas : TwoCoverAtlas}
    (fork : SupportForkOneCochain atlas) :
    SupportForkDefect fork ≠ 0 := by
  change (1 : ConwayZ2) ≠ 0
  decide

/--
The selected boundary subgroup for one fork.  If a fork has a single-owner
support, all selected defects are absorbed (`⊤`); otherwise only zero is
absorbed (`⊥`).
-/
noncomputable def SupportForkBoundarySubgroup {atlas : TwoCoverAtlas}
    (fork : SupportForkOneCochain atlas) : AddSubgroup ConwayZ2 := by
  classical
  exact if ForkHasSingleOwnerSupport fork then ⊤ else ⊥

/-- The selected defect vanishes modulo the chosen boundary subgroup. -/
def SupportForkDefectVanishesModuloBoundary {atlas : TwoCoverAtlas}
    (fork : SupportForkOneCochain atlas) : Prop :=
  SupportForkDefect fork ∈ SupportForkBoundarySubgroup fork

/-- A selected fork has nonzero boundary-quotient class when it is not a boundary. -/
def SupportForkNonzeroClass {atlas : TwoCoverAtlas}
    (fork : SupportForkOneCochain atlas) : Prop :=
  Not (SupportForkDefectVanishesModuloBoundary fork)

/-- Boundary vanishing is equivalent to single-owner support for the selected fork. -/
theorem supportForkDefect_vanishes_iff_singleOwnerSupport
    {atlas : TwoCoverAtlas} (fork : SupportForkOneCochain atlas) :
    SupportForkDefectVanishesModuloBoundary fork ↔
      ForkHasSingleOwnerSupport fork := by
  classical
  by_cases hsupport : ForkHasSingleOwnerSupport fork
  · simp [SupportForkDefectVanishesModuloBoundary, SupportForkBoundarySubgroup,
      hsupport]
  · constructor
    · intro hvanish
      simp [SupportForkDefectVanishesModuloBoundary, SupportForkBoundarySubgroup,
        hsupport, SupportForkDefect] at hvanish
    · intro hsupport'
      exact False.elim (hsupport hsupport')

/-- Nonvanishing modulo boundary is equivalent to the Cycle 2 no-support condition. -/
theorem supportForkNonzeroClass_iff_noSingleOwnerSupport
    {atlas : TwoCoverAtlas} (fork : SupportForkOneCochain atlas) :
    SupportForkNonzeroClass fork ↔ Not (ForkHasSingleOwnerSupport fork) := by
  exact not_congr (supportForkDefect_vanishes_iff_singleOwnerSupport fork)

/-- The finite `C^1/B^1`-style receiver: some support fork survives modulo boundary. -/
def BoundaryQuotientReceiver (atlas : TwoCoverAtlas) : Prop :=
  exists fork : SupportForkOneCochain atlas, SupportForkNonzeroClass fork

/-- The boundary-quotient receiver is the Cycle 2 support receiver in quotient vocabulary. -/
theorem boundaryQuotientReceiver_iff_supportReceiver (atlas : TwoCoverAtlas) :
    BoundaryQuotientReceiver atlas ↔ SupportNerveObstructionReceiver atlas :=
  by
    unfold BoundaryQuotientReceiver SupportNerveObstructionReceiver
    constructor
    · intro h
      rcases h with ⟨fork, hnonzero⟩
      exact ⟨fork, (supportForkNonzeroClass_iff_noSingleOwnerSupport fork).mp hnonzero⟩
    · intro h
      rcases h with ⟨fork, hnoSupport⟩
      exact ⟨fork, (supportForkNonzeroClass_iff_noSingleOwnerSupport fork).mpr hnoSupport⟩

/-! ## Functional ownership as a non-boundary certificate -/

/--
Ownership is functional when each selected context has at most one selected
owner support.  Under this condition, a same-communication fork with distinct
owners cannot be a single-owner boundary.
-/
def OwnershipFunctional (atlas : TwoCoverAtlas) : Prop :=
  forall ownerLeft ownerRight context,
    atlas.ownership ownerLeft context ->
      atlas.ownership ownerRight context ->
        ownerLeft = ownerRight

/--
If ownership is functional, every support-nerve fork already has nonzero
boundary-quotient class.  This is the first Cycle 3 theorem that does not use
`ForkHasSingleOwnerSupport` negatively as an input; the no-boundary conclusion is
derived from functionality plus distinct owner endpoints.
-/
theorem functionalFork_nonzeroClass {atlas : TwoCoverAtlas}
    (functional : OwnershipFunctional atlas)
    (fork : SupportForkOneCochain atlas) :
    SupportForkNonzeroClass fork := by
  rw [supportForkNonzeroClass_iff_noSingleOwnerSupport]
  intro boundary
  rcases boundary with ⟨owner, supports⟩
  have hLeftOwner : owner = fork.left.owner :=
    functional owner fork.left.owner fork.left.context
      (supports fork.left.context fork.left.communication_holds)
      fork.left.ownership_holds
  have hRightCommunication :
      atlas.communication fork.left.comm fork.right.context := by
    simpa [fork.sameCommunication] using fork.right.communication_holds
  have hRightOwner : owner = fork.right.owner :=
    functional owner fork.right.owner fork.right.context
      (supports fork.right.context hRightCommunication)
      fork.right.ownership_holds
  exact fork.ownersDistinct (hLeftOwner.symm.trans hRightOwner)

/-- A functional ownership fork induces a boundary-quotient receiver. -/
theorem functionalFork_boundaryQuotientReceiver {atlas : TwoCoverAtlas}
    (functional : OwnershipFunctional atlas)
    (fork : SupportForkOneCochain atlas) :
    BoundaryQuotientReceiver atlas :=
  ⟨fork, functionalFork_nonzeroClass functional fork⟩

/-! ## Cycle 1 examples in boundary-quotient vocabulary -/

/-- The split ownership relation is functional on the mismatched atlas. -/
theorem mismatchedAtlas_ownershipFunctional :
    OwnershipFunctional mismatchedAtlas := by
  intro ownerLeft ownerRight context hLeft hRight
  cases ownerLeft <;> cases ownerRight <;> cases context <;>
    simp [mismatchedAtlas, splitOwnership] at hLeft hRight ⊢

/-- The canonical mismatched support fork over the all-communication block. -/
def mismatchedSupportFork : SupportForkOneCochain mismatchedAtlas where
  left := {
    comm := ()
    owner := Owner.apiOwner
    context := Module.api
    communication_holds := by simp [mismatchedAtlas, allCommunication]
    ownership_holds := by simp [mismatchedAtlas, splitOwnership]
  }
  right := {
    comm := ()
    owner := Owner.dbOwner
    context := Module.db
    communication_holds := by simp [mismatchedAtlas, allCommunication]
    ownership_holds := by simp [mismatchedAtlas, splitOwnership]
  }
  sameCommunication := rfl
  ownersDistinct := by
    intro howners
    cases howners

/--
The canonical mismatched fork has nonzero boundary-quotient class by functional
ownership, rather than by directly invoking the Cycle 1 no-support theorem.
-/
theorem mismatchedSupportFork_nonzeroClass :
    SupportForkNonzeroClass mismatchedSupportFork :=
  functionalFork_nonzeroClass
    mismatchedAtlas_ownershipFunctional
    mismatchedSupportFork

/-- The mismatched atlas has a boundary-quotient receiver. -/
theorem mismatchedAtlas_boundaryQuotientReceiver :
    BoundaryQuotientReceiver mismatchedAtlas :=
  ⟨mismatchedSupportFork, mismatchedSupportFork_nonzeroClass⟩

/-- Compatibility rules out boundary-quotient receiver classes. -/
theorem compatible_no_boundaryQuotientReceiver (atlas : TwoCoverAtlas)
    (compatible : CommunicationCoverCompatible atlas) :
    Not (BoundaryQuotientReceiver atlas) := by
  rw [boundaryQuotientReceiver_iff_supportReceiver]
  exact compatible_no_supportReceiver atlas compatible

/-- The compatible Cycle 1 atlas has zero boundary-quotient receiver. -/
theorem compatibleAtlas_zeroBoundaryQuotientReceiver :
    Not (BoundaryQuotientReceiver compatibleAtlas) := by
  rw [boundaryQuotientReceiver_iff_supportReceiver]
  exact compatibleAtlas_noSupportReceiver

/-- The reorg-side repaired atlas has zero boundary-quotient receiver. -/
theorem reorgedAtlas_zeroBoundaryQuotientReceiver :
    Not (BoundaryQuotientReceiver reorgedAtlas) := by
  rw [boundaryQuotientReceiver_iff_supportReceiver]
  exact reorgedAtlas_noSupportReceiver

/-- The refactor-side repaired atlas has zero boundary-quotient receiver. -/
theorem refactoredAtlas_zeroBoundaryQuotientReceiver :
    Not (BoundaryQuotientReceiver refactoredAtlas) := by
  rw [boundaryQuotientReceiver_iff_supportReceiver]
  exact refactoredAtlas_noSupportReceiver

/--
The selected Cycle 3 package: the mismatched fork is nonzero modulo selected
single-owner boundaries by a functional-ownership certificate, while the
compatible and repaired examples have zero boundary-quotient receiver.
-/
theorem selectedBoundaryQuotientReceiverPackage :
    Not (BoundaryQuotientReceiver compatibleAtlas) /\
      BoundaryQuotientReceiver mismatchedAtlas /\
      SupportForkNonzeroClass mismatchedSupportFork /\
      OwnershipFunctional mismatchedAtlas /\
      Not (BoundaryQuotientReceiver reorgedAtlas) /\
      Not (BoundaryQuotientReceiver refactoredAtlas) := by
  exact
    ⟨compatibleAtlas_zeroBoundaryQuotientReceiver,
      mismatchedAtlas_boundaryQuotientReceiver,
      mismatchedSupportFork_nonzeroClass,
      mismatchedAtlas_ownershipFunctional,
      reorgedAtlas_zeroBoundaryQuotientReceiver,
      refactoredAtlas_zeroBoundaryQuotientReceiver⟩

end ConwayTwoTopology
end SFT
end Formal.AG.Research
