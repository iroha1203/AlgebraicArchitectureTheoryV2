import ResearchLean.AG.SFT.ConwayConstrainedOwnerPotentialBoundary

/-!
Cycle 9 evidence for `G-sft-conway-01`.

Cycle 8 repaired the local owner-potential boundary by adding the support
constraint back.  This file records the same constraint as selected
common-refinement data: a refinement block over the fork's communication block
must cover that communication block and refine one ownership block.

This is still a selected finite receiver layer.  It does not claim a new
obstruction condition beyond the support receiver; its role is to move the
support constraint into common-refinement vocabulary for later comparison
theorems.
-/

namespace ResearchLean.AG
namespace SFT
namespace ConwayTwoTopology

/-! ## Common-refinement support for a fork -/

/--
A common-refinement support for a selected fork: one common-refinement block
lies over the fork's communication block and covers that whole communication
block.
-/
structure CommonRefinementSupportsFork {atlas : TwoCoverAtlas}
    (fork : SupportForkOneCochain atlas) where
  span : CommonRefinementSpan atlas
  ref : span.RefIdx
  refines_comm : span.refinesCommunication ref = fork.left.comm
  covers_comm :
    forall context,
      atlas.communication fork.left.comm context ->
        span.refinement ref context

/-- A common-refinement support gives the Cycle 2 single-owner support condition. -/
theorem CommonRefinementSupportsFork.toSingleOwnerSupport
    {atlas : TwoCoverAtlas}
    {fork : SupportForkOneCochain atlas}
    (support : CommonRefinementSupportsFork fork) :
    ForkHasSingleOwnerSupport fork := by
  refine ⟨support.span.refinesOwnership support.ref, ?_⟩
  intro context hcomm
  exact
    support.span.refinement_to_ownership
      support.ref
      context
      (support.covers_comm context hcomm)

/-- A single-owner support witness can be represented as common-refinement data. -/
noncomputable def CommonRefinementSupportsFork.ofSingleOwnerSupport
    {atlas : TwoCoverAtlas}
    {fork : SupportForkOneCochain atlas}
    (support : ForkHasSingleOwnerSupport fork) :
    CommonRefinementSupportsFork fork where
  span := {
    RefIdx := Unit
    refinesCommunication _ := fork.left.comm
    refinesOwnership _ := support.choose
    refinement _ context := atlas.communication fork.left.comm context
    refinement_to_communication := by
      intro ref context hcomm
      cases ref
      exact hcomm
    refinement_to_ownership := by
      intro ref context hcomm
      cases ref
      exact support.choose_spec context hcomm
  }
  ref := ()
  refines_comm := rfl
  covers_comm := by
    intro context hcomm
    exact hcomm

/-- Common-refinement support is equivalent to single-owner support. -/
theorem commonRefinementSupportsFork_iff_singleOwnerSupport
    {atlas : TwoCoverAtlas}
    (fork : SupportForkOneCochain atlas) :
    Nonempty (CommonRefinementSupportsFork fork) ↔
      ForkHasSingleOwnerSupport fork := by
  constructor
  · intro hsupport
    rcases hsupport with ⟨support⟩
    exact support.toSingleOwnerSupport
  · intro hsupport
    exact ⟨CommonRefinementSupportsFork.ofSingleOwnerSupport hsupport⟩

/-! ## Common-refinement constrained potential boundary -/

/--
The common-refinement constrained owner-potential vanishing predicate: the fork
has selected common-refinement support and local owner-potential absorption.
-/
def SupportForkDefectVanishesModuloCommonRefinementOwnerPotential
    {atlas : TwoCoverAtlas}
    (fork : SupportForkOneCochain atlas) : Prop :=
  Nonempty (CommonRefinementSupportsFork fork) /\
    SupportForkDefectVanishesModuloOwnerPotentialBoundary fork

/--
With decidable owner equality, common-refinement constrained owner-potential
vanishing is exactly single-owner support.
-/
theorem commonRefinementOwnerPotential_vanishes_iff_singleOwnerSupport
    {atlas : TwoCoverAtlas}
    [DecidableEq atlas.OwnerIdx]
    (fork : SupportForkOneCochain atlas) :
    SupportForkDefectVanishesModuloCommonRefinementOwnerPotential fork ↔
      ForkHasSingleOwnerSupport fork := by
  constructor
  · intro hvanish
    exact (commonRefinementSupportsFork_iff_singleOwnerSupport fork).mp hvanish.1
  · intro hsupport
    exact
      ⟨(commonRefinementSupportsFork_iff_singleOwnerSupport fork).mpr hsupport,
        ownerPotentialBoundary_vanishes_of_decidableOwners fork⟩

/-- A receiver for common-refinement constrained owner-potential boundary failures. -/
def CommonRefinementOwnerPotentialReceiver (atlas : TwoCoverAtlas) : Prop :=
  exists fork : SupportForkOneCochain atlas,
    Not
      (SupportForkDefectVanishesModuloCommonRefinementOwnerPotential
        fork)

/--
With decidable owner equality, the common-refinement constrained receiver is
exactly the support receiver.
-/
theorem commonRefinementOwnerPotentialReceiver_iff_supportReceiver
    (atlas : TwoCoverAtlas)
    [DecidableEq atlas.OwnerIdx] :
    CommonRefinementOwnerPotentialReceiver atlas ↔
      SupportNerveObstructionReceiver atlas := by
  unfold CommonRefinementOwnerPotentialReceiver
    SupportNerveObstructionReceiver
  constructor
  · intro hreceiver
    rcases hreceiver with ⟨fork, hnonzero⟩
    exact
      ⟨fork,
        fun hsupport =>
          hnonzero
            ((commonRefinementOwnerPotential_vanishes_iff_singleOwnerSupport
              fork).mpr hsupport)⟩
  · intro hreceiver
    rcases hreceiver with ⟨fork, hnoSupport⟩
    exact
      ⟨fork,
        fun hvanish =>
          hnoSupport
            ((commonRefinementOwnerPotential_vanishes_iff_singleOwnerSupport
              fork).mp hvanish)⟩

/-! ## Finite examples -/

/-- The canonical mismatched fork has no common-refinement constrained vanishing. -/
theorem mismatchedSupportFork_notCommonRefinementOwnerPotentialVanishes :
    Not
      (SupportForkDefectVanishesModuloCommonRefinementOwnerPotential
        mismatchedSupportFork) := by
  intro hvanish
  exact
    mismatchedAtlas_allCommunication_notSupported
      ((commonRefinementSupportsFork_iff_singleOwnerSupport
        mismatchedSupportFork).mp hvanish.1)

/-- The mismatched atlas has a common-refinement constrained receiver. -/
theorem mismatchedAtlas_commonRefinementOwnerPotentialReceiver :
    CommonRefinementOwnerPotentialReceiver mismatchedAtlas :=
  ⟨mismatchedSupportFork,
    mismatchedSupportFork_notCommonRefinementOwnerPotentialVanishes⟩

/-- Compatibility rules out common-refinement constrained receiver classes. -/
theorem compatible_no_commonRefinementOwnerPotentialReceiver
    (atlas : TwoCoverAtlas)
    [DecidableEq atlas.OwnerIdx]
    (compatible : CommunicationCoverCompatible atlas) :
    Not (CommonRefinementOwnerPotentialReceiver atlas) := by
  rw [commonRefinementOwnerPotentialReceiver_iff_supportReceiver]
  exact compatible_no_supportReceiver atlas compatible

/-- The compatible Cycle 1 atlas has zero common-refinement constrained receiver. -/
theorem compatibleAtlas_zeroCommonRefinementOwnerPotentialReceiver :
    Not (CommonRefinementOwnerPotentialReceiver compatibleAtlas) := by
  haveI : DecidableEq compatibleAtlas.OwnerIdx := by
    change DecidableEq Owner
    infer_instance
  exact
    compatible_no_commonRefinementOwnerPotentialReceiver
      compatibleAtlas
      compatibleAtlas_communicationCompatible

/-- The reorg-side repaired atlas has zero common-refinement constrained receiver. -/
theorem reorgedAtlas_zeroCommonRefinementOwnerPotentialReceiver :
    Not (CommonRefinementOwnerPotentialReceiver reorgedAtlas) :=
  compatibleAtlas_zeroCommonRefinementOwnerPotentialReceiver

/-- The refactor-side repaired atlas has zero common-refinement constrained receiver. -/
theorem refactoredAtlas_zeroCommonRefinementOwnerPotentialReceiver :
    Not (CommonRefinementOwnerPotentialReceiver refactoredAtlas) := by
  haveI : DecidableEq refactoredAtlas.OwnerIdx := by
    change DecidableEq Unit
    infer_instance
  exact
    compatible_no_commonRefinementOwnerPotentialReceiver
      refactoredAtlas
      refactoredAtlas_communicationCompatible

/--
The selected Cycle 9 package: common-refinement support recovers the same finite
zero/nonzero receiver behavior while moving the support constraint into
common-refinement vocabulary.
-/
theorem selectedCommonRefinementOwnerPotentialPackage :
    Not (CommonRefinementOwnerPotentialReceiver compatibleAtlas) /\
      CommonRefinementOwnerPotentialReceiver mismatchedAtlas /\
      Not
        (SupportForkDefectVanishesModuloCommonRefinementOwnerPotential
          mismatchedSupportFork) /\
      Not (CommonRefinementOwnerPotentialReceiver reorgedAtlas) /\
      Not (CommonRefinementOwnerPotentialReceiver refactoredAtlas) := by
  exact
    ⟨compatibleAtlas_zeroCommonRefinementOwnerPotentialReceiver,
      mismatchedAtlas_commonRefinementOwnerPotentialReceiver,
      mismatchedSupportFork_notCommonRefinementOwnerPotentialVanishes,
      reorgedAtlas_zeroCommonRefinementOwnerPotentialReceiver,
      refactoredAtlas_zeroCommonRefinementOwnerPotentialReceiver⟩

end ConwayTwoTopology
end SFT
end ResearchLean.AG
