import Formal.AG.Research.SFT.ConwayCommonRefinementBoundary

/-!
Cycle 10 evidence for `G-sft-conway-01`.

Cycle 9 moved the support constraint into common-refinement provenance.  This
file compares that provenance with the Cycle 5 global zero-cochain boundary:
one global zero-cochain supplies common-refinement support for every selected
fork, and the combined global/common-refinement vanishing predicate is exactly
communication-cover compatibility.

This is still selected finite Conway vocabulary.  It does not claim a new
obstruction beyond the global-boundary receiver; it records a comparison layer
between global boundary exactness and common-refinement support provenance.
-/

namespace Formal.AG.Research
namespace SFT
namespace ConwayTwoTopology

/-! ## Global zero-cochains induce common-refinement support -/

namespace CommunicationZeroCochain

/--
A global zero-cochain gives common-refinement support for every selected fork:
the refinement block is the fork communication block itself, mapped to the
globally selected owner for that communication block.
-/
def toCommonRefinementSupport {atlas : TwoCoverAtlas}
    (zero : CommunicationZeroCochain atlas)
    (fork : SupportForkOneCochain atlas) :
    CommonRefinementSupportsFork fork where
  span := {
    RefIdx := Unit
    refinesCommunication _ := fork.left.comm
    refinesOwnership _ := zero.ownerOf fork.left.comm
    refinement _ context := atlas.communication fork.left.comm context
    refinement_to_communication := by
      intro ref context hcomm
      cases ref
      exact hcomm
    refinement_to_ownership := by
      intro ref context hcomm
      cases ref
      exact zero.supports fork.left.comm context hcomm
  }
  ref := ()
  refines_comm := rfl
  covers_comm := by
    intro context hcomm
    exact hcomm

end CommunicationZeroCochain

/-- A global zero-cochain gives common-refinement support for every fork. -/
theorem communicationZeroCochain_commonRefinementSupport
    {atlas : TwoCoverAtlas}
    (zero : CommunicationZeroCochain atlas)
    (fork : SupportForkOneCochain atlas) :
    Nonempty (CommonRefinementSupportsFork fork) :=
  ⟨zero.toCommonRefinementSupport fork⟩

/-! ## Combined global/common-refinement vanishing -/

/--
The combined comparison predicate: the selected fork defect is absorbed by the
global zero-cochain boundary and the same fork has common-refinement support
provenance.
-/
def SupportForkDefectVanishesModuloGlobalCommonRefinement
    {atlas : TwoCoverAtlas}
    (fork : SupportForkOneCochain atlas) : Prop :=
  SupportForkDefectVanishesModuloGlobalBoundary fork /\
    Nonempty (CommonRefinementSupportsFork fork)

/--
The global/common-refinement comparison is exact at the selected finite level:
combined vanishing for one selected fork is equivalent to communication-cover
compatibility, because the global zero-cochain already supports every fork.
-/
theorem globalCommonRefinement_vanishes_iff_compatible
    {atlas : TwoCoverAtlas}
    (fork : SupportForkOneCochain atlas) :
    SupportForkDefectVanishesModuloGlobalCommonRefinement fork ↔
      CommunicationCoverCompatible atlas := by
  constructor
  · intro hvanish
    exact (globalBoundary_vanishes_iff_compatible fork).mp hvanish.1
  · intro compatible
    let zero := CommunicationZeroCochain.ofCompatibility compatible
    exact
      ⟨globalBoundary_absorbs_defect zero fork,
        communicationZeroCochain_commonRefinementSupport zero fork⟩

/--
The combined comparison factors through the Cycle 9 common-refinement
owner-potential predicate when owner equality is decidable.
-/
theorem globalCommonRefinement_implies_commonRefinementOwnerPotential
    {atlas : TwoCoverAtlas}
    [DecidableEq atlas.OwnerIdx]
    {fork : SupportForkOneCochain atlas}
    (hvanish : SupportForkDefectVanishesModuloGlobalCommonRefinement fork) :
    SupportForkDefectVanishesModuloCommonRefinementOwnerPotential fork := by
  exact
    (commonRefinementOwnerPotential_vanishes_iff_singleOwnerSupport fork).mpr
      ((commonRefinementSupportsFork_iff_singleOwnerSupport fork).mp
        hvanish.2)

/-! ## Receiver comparison and finite examples -/

/-- A receiver for failures of the combined global/common-refinement comparison. -/
def GlobalCommonRefinementReceiver (atlas : TwoCoverAtlas) : Prop :=
  exists fork : SupportForkOneCochain atlas,
    Not (SupportForkDefectVanishesModuloGlobalCommonRefinement fork)

/--
The combined receiver is exactly the Cycle 5 global-boundary receiver.  The
common-refinement support side adds provenance but no new obstruction condition.
-/
theorem globalCommonRefinementReceiver_iff_globalBoundaryReceiver
    (atlas : TwoCoverAtlas) :
    GlobalCommonRefinementReceiver atlas ↔ GlobalBoundaryReceiver atlas := by
  constructor
  · intro hreceiver
    rcases hreceiver with ⟨fork, hnotCombined⟩
    have hnotCompatible : Not (CommunicationCoverCompatible atlas) := by
      intro compatible
      exact hnotCombined
        ((globalCommonRefinement_vanishes_iff_compatible fork).mpr
          compatible)
    exact
      ⟨fork,
        fun hglobal =>
          hnotCompatible
            ((globalBoundary_vanishes_iff_compatible fork).mp hglobal)⟩
  · intro hreceiver
    rcases hreceiver with ⟨fork, hnotGlobal⟩
    exact ⟨fork, fun hcombined => hnotGlobal hcombined.1⟩

/-- Compatibility rules out combined global/common-refinement receiver classes. -/
theorem compatible_no_globalCommonRefinementReceiver
    (atlas : TwoCoverAtlas)
    (compatible : CommunicationCoverCompatible atlas) :
    Not (GlobalCommonRefinementReceiver atlas) := by
  rw [globalCommonRefinementReceiver_iff_globalBoundaryReceiver]
  exact compatible_no_globalBoundaryReceiver atlas compatible

/-- The compatible Cycle 1 atlas has zero combined receiver. -/
theorem compatibleAtlas_zeroGlobalCommonRefinementReceiver :
    Not (GlobalCommonRefinementReceiver compatibleAtlas) :=
  compatible_no_globalCommonRefinementReceiver
    compatibleAtlas
    compatibleAtlas_communicationCompatible

/-- The canonical mismatched fork is not absorbed by the combined comparison. -/
theorem mismatchedSupportFork_notGlobalCommonRefinementVanishes :
    Not
      (SupportForkDefectVanishesModuloGlobalCommonRefinement
        mismatchedSupportFork) := by
  intro hvanish
  exact mismatchedSupportFork_notGlobalBoundaryVanishes hvanish.1

/-- The mismatched atlas has a combined global/common-refinement receiver. -/
theorem mismatchedAtlas_globalCommonRefinementReceiver :
    GlobalCommonRefinementReceiver mismatchedAtlas :=
  ⟨mismatchedSupportFork,
    mismatchedSupportFork_notGlobalCommonRefinementVanishes⟩

/-- The reorg-side repaired atlas has zero combined receiver. -/
theorem reorgedAtlas_zeroGlobalCommonRefinementReceiver :
    Not (GlobalCommonRefinementReceiver reorgedAtlas) :=
  compatibleAtlas_zeroGlobalCommonRefinementReceiver

/-- The refactor-side repaired atlas has zero combined receiver. -/
theorem refactoredAtlas_zeroGlobalCommonRefinementReceiver :
    Not (GlobalCommonRefinementReceiver refactoredAtlas) :=
  compatible_no_globalCommonRefinementReceiver
    refactoredAtlas
    refactoredAtlas_communicationCompatible

/--
The selected Cycle 10 package: global zero-cochain boundary absorption already
supplies common-refinement provenance for every fork, so the combined receiver
recovers the Cycle 5 global-boundary receiver.
-/
theorem selectedGlobalCommonRefinementComparisonPackage :
    Not (GlobalCommonRefinementReceiver compatibleAtlas) /\
      GlobalCommonRefinementReceiver mismatchedAtlas /\
      Not
        (SupportForkDefectVanishesModuloGlobalCommonRefinement
          mismatchedSupportFork) /\
      (GlobalCommonRefinementReceiver mismatchedAtlas ↔
        GlobalBoundaryReceiver mismatchedAtlas) /\
      Not (GlobalCommonRefinementReceiver reorgedAtlas) /\
      Not (GlobalCommonRefinementReceiver refactoredAtlas) := by
  exact
    ⟨compatibleAtlas_zeroGlobalCommonRefinementReceiver,
      mismatchedAtlas_globalCommonRefinementReceiver,
      mismatchedSupportFork_notGlobalCommonRefinementVanishes,
      globalCommonRefinementReceiver_iff_globalBoundaryReceiver mismatchedAtlas,
      reorgedAtlas_zeroGlobalCommonRefinementReceiver,
      refactoredAtlas_zeroGlobalCommonRefinementReceiver⟩

end ConwayTwoTopology
end SFT
end Formal.AG.Research
