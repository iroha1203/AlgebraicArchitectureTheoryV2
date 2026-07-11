import ResearchLean.AG.SFT.ConwayBoundaryMap

/-!
Cycle 6 evidence for `G-sft-conway-01`.

Cycle 5 introduced a global zero-cochain boundary map, but that selected map did
not inspect the zero-cochain value.  This file adds a smaller owner-choice
boundary evaluation that does inspect the chosen owner for the fork's
communication block.

The result is still a finite selected receiver, not an additive cochain complex
or a sheaf-cohomology construction.  Its purpose is to separate "the boundary
map uses degree-zero data" from the stronger, still open, problem of building a
nontrivial functorial `C0 -> C1` complex.
-/

namespace Formal.AG.Research
namespace SFT
namespace ConwayTwoTopology

/-! ## Owner-choice boundary evaluation -/

/--
A selected degree-zero owner choice: every communication block is assigned an
owner, without requiring that owner to support the block.
-/
structure CommunicationOwnerChoice (atlas : TwoCoverAtlas) where
  ownerOf : atlas.CommIdx -> atlas.OwnerIdx

namespace CommunicationOwnerChoice

/-- A global zero-cochain has an underlying owner choice. -/
def ofZeroCochain {atlas : TwoCoverAtlas}
    (zero : CommunicationZeroCochain atlas) :
    CommunicationOwnerChoice atlas where
  ownerOf := zero.ownerOf

end CommunicationOwnerChoice

/-- The owner selected by a degree-zero choice supports the fork's communication block. -/
def OwnerChoiceSupportsFork {atlas : TwoCoverAtlas}
    (choice : CommunicationOwnerChoice atlas)
    (fork : SupportForkOneCochain atlas) : Prop :=
  forall context,
    atlas.communication fork.left.comm context ->
      atlas.ownership (choice.ownerOf fork.left.comm) context

/--
The selected owner-choice boundary evaluation.  Unlike Cycle 5's global
boundary map, this value depends on whether the chosen owner supports the
communication block carried by the fork.
-/
noncomputable def SupportForkOwnerChoiceBoundary {atlas : TwoCoverAtlas}
    (choice : CommunicationOwnerChoice atlas)
    (fork : SupportForkOneCochain atlas) : ConwayZ2 := by
  classical
  exact
    if OwnerChoiceSupportsFork choice fork then
      SupportForkDefect fork
    else
      0

/-- The selected defect is absorbed by some owner-choice boundary evaluation. -/
def SupportForkDefectVanishesModuloOwnerChoiceBoundary {atlas : TwoCoverAtlas}
    (fork : SupportForkOneCochain atlas) : Prop :=
  exists choice : CommunicationOwnerChoice atlas,
    SupportForkOwnerChoiceBoundary choice fork = SupportForkDefect fork

/--
For a fixed owner choice, selected boundary absorption is exactly support by
that chosen owner.
-/
theorem ownerChoiceBoundary_absorbs_iff_supportsFork
    {atlas : TwoCoverAtlas}
    (choice : CommunicationOwnerChoice atlas)
    (fork : SupportForkOneCochain atlas) :
    SupportForkOwnerChoiceBoundary choice fork = SupportForkDefect fork ↔
      OwnerChoiceSupportsFork choice fork := by
  classical
  by_cases hsupports : OwnerChoiceSupportsFork choice fork
  · constructor
    · intro _hboundary
      exact hsupports
    · intro _hsupports
      simp [SupportForkOwnerChoiceBoundary, hsupports]
  · constructor
    · intro hboundary
      exact False.elim
        (supportForkDefect_nonzero fork
          ((by
            simpa [SupportForkOwnerChoiceBoundary, hsupports] using
              hboundary) : (0 : ConwayZ2) = SupportForkDefect fork).symm)
    · intro hsupport
      exact False.elim (hsupports hsupport)

/--
Owner-choice boundary absorption is equivalent to the Cycle 2 single-owner
support condition for the selected fork.
-/
theorem ownerChoiceBoundary_vanishes_iff_singleOwnerSupport
    {atlas : TwoCoverAtlas} (fork : SupportForkOneCochain atlas) :
    SupportForkDefectVanishesModuloOwnerChoiceBoundary fork ↔
      ForkHasSingleOwnerSupport fork := by
  constructor
  · intro hvanish
    rcases hvanish with ⟨choice, hboundary⟩
    exact
      ⟨choice.ownerOf fork.left.comm,
        (ownerChoiceBoundary_absorbs_iff_supportsFork choice fork).mp
          hboundary⟩
  · intro hsupport
    rcases hsupport with ⟨owner, supports⟩
    let choice : CommunicationOwnerChoice atlas := {
      ownerOf := fun _comm => owner
    }
    exact
      ⟨choice,
        (ownerChoiceBoundary_absorbs_iff_supportsFork choice fork).mpr
          supports⟩

/-- A global zero-cochain gives owner-choice boundary absorption for every fork. -/
theorem zeroCochain_ownerChoiceBoundary_absorbs
    {atlas : TwoCoverAtlas}
    (zero : CommunicationZeroCochain atlas)
    (fork : SupportForkOneCochain atlas) :
    SupportForkDefectVanishesModuloOwnerChoiceBoundary fork := by
  exact
    ⟨CommunicationOwnerChoice.ofZeroCochain zero,
      (ownerChoiceBoundary_absorbs_iff_supportsFork
        (CommunicationOwnerChoice.ofZeroCochain zero)
        fork).mpr
        (by
          intro context hcomm
          exact zero.supports fork.left.comm context hcomm)⟩

/-! ## Receiver and finite examples -/

/-- A receiver whose selected defect survives every owner-choice boundary evaluation. -/
def OwnerChoiceBoundaryReceiver (atlas : TwoCoverAtlas) : Prop :=
  exists fork : SupportForkOneCochain atlas,
    Not (SupportForkDefectVanishesModuloOwnerChoiceBoundary fork)

/-- The owner-choice boundary receiver is exactly the support receiver. -/
theorem ownerChoiceBoundaryReceiver_iff_supportReceiver
    (atlas : TwoCoverAtlas) :
    OwnerChoiceBoundaryReceiver atlas ↔
      SupportNerveObstructionReceiver atlas := by
  unfold OwnerChoiceBoundaryReceiver SupportNerveObstructionReceiver
  constructor
  · intro hreceiver
    rcases hreceiver with ⟨fork, hnonzero⟩
    exact
      ⟨fork,
        fun hsupport =>
          hnonzero
            ((ownerChoiceBoundary_vanishes_iff_singleOwnerSupport fork).mpr
              hsupport)⟩
  · intro hreceiver
    rcases hreceiver with ⟨fork, hnoSupport⟩
    exact
      ⟨fork,
        fun hvanish =>
          hnoSupport
            ((ownerChoiceBoundary_vanishes_iff_singleOwnerSupport fork).mp
              hvanish)⟩

/-- Compatibility rules out owner-choice boundary receiver classes. -/
theorem compatible_no_ownerChoiceBoundaryReceiver
    (atlas : TwoCoverAtlas)
    (compatible : CommunicationCoverCompatible atlas) :
    Not (OwnerChoiceBoundaryReceiver atlas) := by
  rw [ownerChoiceBoundaryReceiver_iff_supportReceiver]
  exact compatible_no_supportReceiver atlas compatible

/-- The canonical mismatched fork is not absorbed by any owner-choice boundary. -/
theorem mismatchedSupportFork_notOwnerChoiceBoundaryVanishes :
    Not
      (SupportForkDefectVanishesModuloOwnerChoiceBoundary
        mismatchedSupportFork) := by
  intro hvanish
  exact
    mismatchedAtlas_allCommunication_notSupported
      ((ownerChoiceBoundary_vanishes_iff_singleOwnerSupport
        mismatchedSupportFork).mp hvanish)

/-- The mismatched atlas has an owner-choice boundary receiver. -/
theorem mismatchedAtlas_ownerChoiceBoundaryReceiver :
    OwnerChoiceBoundaryReceiver mismatchedAtlas :=
  ⟨mismatchedSupportFork, mismatchedSupportFork_notOwnerChoiceBoundaryVanishes⟩

/-- The compatible Cycle 1 atlas has zero owner-choice boundary receiver. -/
theorem compatibleAtlas_zeroOwnerChoiceBoundaryReceiver :
    Not (OwnerChoiceBoundaryReceiver compatibleAtlas) :=
  compatible_no_ownerChoiceBoundaryReceiver
    compatibleAtlas
    compatibleAtlas_communicationCompatible

/-- The reorg-side repaired atlas has zero owner-choice boundary receiver. -/
theorem reorgedAtlas_zeroOwnerChoiceBoundaryReceiver :
    Not (OwnerChoiceBoundaryReceiver reorgedAtlas) :=
  compatibleAtlas_zeroOwnerChoiceBoundaryReceiver

/-- The refactor-side repaired atlas has zero owner-choice boundary receiver. -/
theorem refactoredAtlas_zeroOwnerChoiceBoundaryReceiver :
    Not (OwnerChoiceBoundaryReceiver refactoredAtlas) :=
  compatible_no_ownerChoiceBoundaryReceiver
    refactoredAtlas
    refactoredAtlas_communicationCompatible

/--
The selected Cycle 6 package: the owner-choice boundary evaluation uses the
chosen owner value, is equivalent to single-owner support on support forks, and
keeps the same zero/nonzero finite Conway examples.
-/
theorem selectedOwnerChoiceBoundaryPackage :
    Not (OwnerChoiceBoundaryReceiver compatibleAtlas) /\
      OwnerChoiceBoundaryReceiver mismatchedAtlas /\
      Not
        (SupportForkDefectVanishesModuloOwnerChoiceBoundary
          mismatchedSupportFork) /\
      Not (OwnerChoiceBoundaryReceiver reorgedAtlas) /\
      Not (OwnerChoiceBoundaryReceiver refactoredAtlas) := by
  exact
    ⟨compatibleAtlas_zeroOwnerChoiceBoundaryReceiver,
      mismatchedAtlas_ownerChoiceBoundaryReceiver,
      mismatchedSupportFork_notOwnerChoiceBoundaryVanishes,
      reorgedAtlas_zeroOwnerChoiceBoundaryReceiver,
      refactoredAtlas_zeroOwnerChoiceBoundaryReceiver⟩

end ConwayTwoTopology
end SFT
end Formal.AG.Research
