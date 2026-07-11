import ResearchLean.AG.SFT.ConwayOwnerPotentialBoundary

/-!
Cycle 8 evidence for `G-sft-conway-01`.

Cycle 7 showed that an unconstrained local owner-potential boundary is too weak:
it absorbs the canonical mismatch.  This file adds the support constraint back
to that local additive boundary.  Under decidable owner equality, endpoint
potentials can absorb any supportable fork; with the support constraint present,
the constrained additive receiver is exactly the Cycle 2 support receiver.

This is still selected finite Conway vocabulary.  It is not a full functorial
cochain complex or sheaf cohomology theory.
-/

namespace Formal.AG.Research
namespace SFT
namespace ConwayTwoTopology

/-! ## Support-constrained owner-potential boundaries -/

/--
The support-constrained owner-potential vanishing predicate: the fork must have
single-owner support and its selected defect must be absorbed by a local
owner-potential boundary.
-/
def SupportForkDefectVanishesModuloSupportConstrainedOwnerPotential
    {atlas : TwoCoverAtlas}
    (fork : SupportForkOneCochain atlas) : Prop :=
  ForkHasSingleOwnerSupport fork /\
    SupportForkDefectVanishesModuloOwnerPotentialBoundary fork

/-- Endpoint-separating potential for a selected support fork. -/
def endpointSeparatingOwnerPotential {atlas : TwoCoverAtlas}
    [DecidableEq atlas.OwnerIdx]
    (fork : SupportForkOneCochain atlas) :
    OwnerPotential atlas where
  value owner := if owner = fork.right.owner then 1 else 0

/-- The endpoint-separating potential absorbs the selected fork defect. -/
theorem endpointSeparatingOwnerPotential_boundary_eq_defect
    {atlas : TwoCoverAtlas}
    [DecidableEq atlas.OwnerIdx]
    (fork : SupportForkOneCochain atlas) :
    SupportForkOwnerPotentialBoundary
      (endpointSeparatingOwnerPotential fork)
      fork =
        SupportForkDefect fork := by
  simp [SupportForkOwnerPotentialBoundary, endpointSeparatingOwnerPotential,
    SupportForkDefect, fork.ownersDistinct]

/-- Every selected fork has local owner-potential absorption under decidable owners. -/
theorem ownerPotentialBoundary_vanishes_of_decidableOwners
    {atlas : TwoCoverAtlas}
    [DecidableEq atlas.OwnerIdx]
    (fork : SupportForkOneCochain atlas) :
    SupportForkDefectVanishesModuloOwnerPotentialBoundary fork :=
  ownerPotentialBoundary_absorbs_of_endpointDifference
    (endpointSeparatingOwnerPotential fork)
    fork
    (endpointSeparatingOwnerPotential_boundary_eq_defect fork)

/--
Support-constrained owner-potential absorption is exactly single-owner support
for selected forks with decidable owner equality.
-/
theorem supportConstrainedOwnerPotential_vanishes_iff_singleOwnerSupport
    {atlas : TwoCoverAtlas}
    [DecidableEq atlas.OwnerIdx]
    (fork : SupportForkOneCochain atlas) :
    SupportForkDefectVanishesModuloSupportConstrainedOwnerPotential fork ↔
      ForkHasSingleOwnerSupport fork := by
  constructor
  · intro hvanish
    exact hvanish.1
  · intro hsupport
    exact
      ⟨hsupport,
        ownerPotentialBoundary_vanishes_of_decidableOwners fork⟩

/-- A receiver for support-constrained owner-potential boundary failures. -/
def SupportConstrainedOwnerPotentialReceiver (atlas : TwoCoverAtlas) : Prop :=
  exists fork : SupportForkOneCochain atlas,
    Not
      (SupportForkDefectVanishesModuloSupportConstrainedOwnerPotential
        fork)

/--
With decidable owner equality, the support-constrained owner-potential receiver
is exactly the support receiver.
-/
theorem supportConstrainedOwnerPotentialReceiver_iff_supportReceiver
    (atlas : TwoCoverAtlas)
    [DecidableEq atlas.OwnerIdx] :
    SupportConstrainedOwnerPotentialReceiver atlas ↔
      SupportNerveObstructionReceiver atlas := by
  unfold SupportConstrainedOwnerPotentialReceiver
    SupportNerveObstructionReceiver
  constructor
  · intro hreceiver
    rcases hreceiver with ⟨fork, hnonzero⟩
    exact
      ⟨fork,
        fun hsupport =>
          hnonzero
            ((supportConstrainedOwnerPotential_vanishes_iff_singleOwnerSupport
              fork).mpr hsupport)⟩
  · intro hreceiver
    rcases hreceiver with ⟨fork, hnoSupport⟩
    exact
      ⟨fork,
        fun hvanish =>
          hnoSupport
            ((supportConstrainedOwnerPotential_vanishes_iff_singleOwnerSupport
              fork).mp hvanish)⟩

/-! ## Finite examples -/

/-- The canonical mismatched fork is not support-constrained owner-potential exact. -/
theorem mismatchedSupportFork_notSupportConstrainedOwnerPotentialVanishes :
    Not
      (SupportForkDefectVanishesModuloSupportConstrainedOwnerPotential
        mismatchedSupportFork) := by
  intro hvanish
  exact
    mismatchedAtlas_allCommunication_notSupported hvanish.1

/-- The mismatched atlas has a support-constrained owner-potential receiver. -/
theorem mismatchedAtlas_supportConstrainedOwnerPotentialReceiver :
    SupportConstrainedOwnerPotentialReceiver mismatchedAtlas :=
  ⟨mismatchedSupportFork,
    mismatchedSupportFork_notSupportConstrainedOwnerPotentialVanishes⟩

/-- Compatibility rules out support-constrained owner-potential receivers. -/
theorem compatible_no_supportConstrainedOwnerPotentialReceiver
    (atlas : TwoCoverAtlas)
    [DecidableEq atlas.OwnerIdx]
    (compatible : CommunicationCoverCompatible atlas) :
    Not (SupportConstrainedOwnerPotentialReceiver atlas) := by
  rw [supportConstrainedOwnerPotentialReceiver_iff_supportReceiver]
  exact compatible_no_supportReceiver atlas compatible

/-- The compatible Cycle 1 atlas has zero support-constrained owner-potential receiver. -/
theorem compatibleAtlas_zeroSupportConstrainedOwnerPotentialReceiver :
    Not (SupportConstrainedOwnerPotentialReceiver compatibleAtlas) :=
  by
    haveI : DecidableEq compatibleAtlas.OwnerIdx := by
      change DecidableEq Owner
      infer_instance
    exact
      compatible_no_supportConstrainedOwnerPotentialReceiver
        compatibleAtlas
        compatibleAtlas_communicationCompatible

/-- The reorg-side repaired atlas has zero support-constrained owner-potential receiver. -/
theorem reorgedAtlas_zeroSupportConstrainedOwnerPotentialReceiver :
    Not (SupportConstrainedOwnerPotentialReceiver reorgedAtlas) :=
  compatibleAtlas_zeroSupportConstrainedOwnerPotentialReceiver

/-- The refactor-side repaired atlas has zero support-constrained owner-potential receiver. -/
theorem refactoredAtlas_zeroSupportConstrainedOwnerPotentialReceiver :
    Not (SupportConstrainedOwnerPotentialReceiver refactoredAtlas) :=
  by
    haveI : DecidableEq refactoredAtlas.OwnerIdx := by
      change DecidableEq Unit
      infer_instance
    exact
      compatible_no_supportConstrainedOwnerPotentialReceiver
        refactoredAtlas
        refactoredAtlas_communicationCompatible

/--
The selected Cycle 8 package: adding support constraints repairs the Cycle 7
local additive weakness for the finite Conway examples and recovers the support
receiver.
-/
theorem selectedSupportConstrainedOwnerPotentialPackage :
    Not (SupportConstrainedOwnerPotentialReceiver compatibleAtlas) /\
      SupportConstrainedOwnerPotentialReceiver mismatchedAtlas /\
      Not
        (SupportForkDefectVanishesModuloSupportConstrainedOwnerPotential
          mismatchedSupportFork) /\
      Not (SupportConstrainedOwnerPotentialReceiver reorgedAtlas) /\
      Not (SupportConstrainedOwnerPotentialReceiver refactoredAtlas) := by
  exact
    ⟨compatibleAtlas_zeroSupportConstrainedOwnerPotentialReceiver,
      mismatchedAtlas_supportConstrainedOwnerPotentialReceiver,
      mismatchedSupportFork_notSupportConstrainedOwnerPotentialVanishes,
      reorgedAtlas_zeroSupportConstrainedOwnerPotentialReceiver,
      refactoredAtlas_zeroSupportConstrainedOwnerPotentialReceiver⟩

end ConwayTwoTopology
end SFT
end Formal.AG.Research
