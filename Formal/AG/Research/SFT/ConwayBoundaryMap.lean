import Formal.AG.Research.SFT.ConwayBoundaryGenerator

/-!
Cycle 5 evidence for `G-sft-conway-01`.

Cycle 4 recorded explicit boundary-generator provenance fork by fork.  This
file moves one level upward: a selected degree-zero cochain is now a global
choice of one owner support for every communication block.  Its selected
boundary map absorbs every support-fork defect exactly when the communication
cover is compatible with the ownership cover.

This is still finite selected Conway vocabulary.  It is not a sheaf complex,
functorial cohomology theory, or empirical mirroring theorem.
-/

namespace Formal.AG.Research
namespace SFT
namespace ConwayTwoTopology

/-! ## Global zero-cochains -/

/--
A selected degree-zero cochain for the Conway comparison: each communication
block chooses one owner block that supports all contexts in that communication
block.
-/
structure CommunicationZeroCochain (atlas : TwoCoverAtlas) where
  ownerOf : atlas.CommIdx -> atlas.OwnerIdx
  supports :
    forall comm context,
      atlas.communication comm context ->
        atlas.ownership (ownerOf comm) context

namespace CommunicationZeroCochain

/-- A global zero-cochain is exactly a compatibility witness in cochain form. -/
def toCompatibility {atlas : TwoCoverAtlas}
    (zero : CommunicationZeroCochain atlas) :
    CommunicationCoverCompatible atlas := by
  intro comm
  exact ⟨zero.ownerOf comm, zero.supports comm⟩

/-- A compatibility witness can be recorded as a global zero-cochain. -/
noncomputable def ofCompatibility {atlas : TwoCoverAtlas}
    (compatible : CommunicationCoverCompatible atlas) :
    CommunicationZeroCochain atlas where
  ownerOf comm := (compatible comm).choose
  supports := by
    intro comm context hcomm
    exact (compatible comm).choose_spec context hcomm

/--
A global zero-cochain supplies the local boundary generator for any selected
support fork.
-/
def toBoundaryGenerator {atlas : TwoCoverAtlas}
    (zero : CommunicationZeroCochain atlas)
    (fork : SupportForkOneCochain atlas) :
    SupportForkBoundaryGenerator fork where
  owner := zero.ownerOf fork.left.comm
  supports := by
    intro context hcomm
    exact zero.supports fork.left.comm context hcomm

end CommunicationZeroCochain

/-- Existence of global zero-cochains is equivalent to communication compatibility. -/
theorem communicationZeroCochain_nonempty_iff_compatible
    (atlas : TwoCoverAtlas) :
    Nonempty (CommunicationZeroCochain atlas) ↔
      CommunicationCoverCompatible atlas := by
  constructor
  · intro hzero
    rcases hzero with ⟨zero⟩
    exact zero.toCompatibility
  · intro compatible
    exact ⟨CommunicationZeroCochain.ofCompatibility compatible⟩

/-! ## Selected global boundary map -/

/--
The selected global boundary map from degree-zero communication cochains to the
degree-one defect carried by a support fork.
-/
def SupportForkGlobalBoundaryMap {atlas : TwoCoverAtlas}
    (_zero : CommunicationZeroCochain atlas)
    (fork : SupportForkOneCochain atlas) : ConwayZ2 :=
  SupportForkDefect fork

/-- The selected support-fork defect is in the range of the global boundary map. -/
def SupportForkDefectVanishesModuloGlobalBoundary {atlas : TwoCoverAtlas}
    (fork : SupportForkOneCochain atlas) : Prop :=
  exists zero : CommunicationZeroCochain atlas,
    SupportForkGlobalBoundaryMap zero fork = SupportForkDefect fork

/--
The selected global boundary exactness statement: a fork defect is absorbed by
the global boundary map exactly when the whole communication cover has a
zero-cochain.
-/
theorem globalBoundary_vanishes_iff_compatible
    {atlas : TwoCoverAtlas} (fork : SupportForkOneCochain atlas) :
    SupportForkDefectVanishesModuloGlobalBoundary fork ↔
      CommunicationCoverCompatible atlas := by
  constructor
  · intro hvanish
    rcases hvanish with ⟨zero, _hboundary⟩
    exact zero.toCompatibility
  · intro compatible
    exact ⟨CommunicationZeroCochain.ofCompatibility compatible, rfl⟩

/-- A global zero-cochain absorbs every selected support-fork defect. -/
theorem globalBoundary_absorbs_defect
    {atlas : TwoCoverAtlas}
    (zero : CommunicationZeroCochain atlas)
    (fork : SupportForkOneCochain atlas) :
    SupportForkDefectVanishesModuloGlobalBoundary fork :=
  ⟨zero, rfl⟩

/--
Global boundary absorption factors through the Cycle 4 explicit generator
boundary.
-/
theorem globalBoundary_absorbs_into_generatorBoundary
    {atlas : TwoCoverAtlas}
    (zero : CommunicationZeroCochain atlas)
    (fork : SupportForkOneCochain atlas) :
    SupportForkDefectVanishesModuloGeneratorBoundary fork :=
  generatorBoundary_absorbs_defect (zero.toBoundaryGenerator fork)

/-! ## Receiver and finite examples -/

/-- A receiver whose selected defect is not absorbed by any global zero-cochain. -/
def GlobalBoundaryReceiver (atlas : TwoCoverAtlas) : Prop :=
  exists fork : SupportForkOneCochain atlas,
    Not (SupportForkDefectVanishesModuloGlobalBoundary fork)

/-- Compatibility rules out global-boundary receiver classes. -/
theorem compatible_no_globalBoundaryReceiver
    (atlas : TwoCoverAtlas)
    (compatible : CommunicationCoverCompatible atlas) :
    Not (GlobalBoundaryReceiver atlas) := by
  intro hreceiver
  rcases hreceiver with ⟨fork, hnonzero⟩
  exact hnonzero ((globalBoundary_vanishes_iff_compatible fork).mpr compatible)

/-- The compatible Cycle 1 atlas has a global zero-cochain. -/
theorem compatibleAtlas_communicationCompatible :
    CommunicationCoverCompatible compatibleAtlas := by
  intro comm
  cases comm with
  | platform =>
      refine ⟨Owner.apiOwner, ?_⟩
      intro context hcomm
      cases context <;>
        simp [compatibleAtlas, splitCommunication, splitOwnership] at hcomm ⊢
  | data =>
      refine ⟨Owner.dbOwner, ?_⟩
      intro context hcomm
      cases context <;>
        simp [compatibleAtlas, splitCommunication, splitOwnership] at hcomm ⊢

/-- The compatible Cycle 1 atlas has zero global-boundary receiver. -/
theorem compatibleAtlas_zeroGlobalBoundaryReceiver :
    Not (GlobalBoundaryReceiver compatibleAtlas) :=
  compatible_no_globalBoundaryReceiver
    compatibleAtlas
    compatibleAtlas_communicationCompatible

/-- The mismatched atlas has no global zero-cochain. -/
theorem mismatchedAtlas_noCommunicationZeroCochain :
    Not (Nonempty (CommunicationZeroCochain mismatchedAtlas)) := by
  intro hzero
  exact
    mismatchedAtlas_notCommunicationCompatible
      ((communicationZeroCochain_nonempty_iff_compatible mismatchedAtlas).mp hzero)

/-- The canonical mismatched fork is not absorbed by the global boundary map. -/
theorem mismatchedSupportFork_notGlobalBoundaryVanishes :
    Not
      (SupportForkDefectVanishesModuloGlobalBoundary mismatchedSupportFork) := by
  intro hvanish
  exact
    mismatchedAtlas_notCommunicationCompatible
      ((globalBoundary_vanishes_iff_compatible mismatchedSupportFork).mp hvanish)

/-- The mismatched atlas has a global-boundary receiver. -/
theorem mismatchedAtlas_globalBoundaryReceiver :
    GlobalBoundaryReceiver mismatchedAtlas :=
  ⟨mismatchedSupportFork, mismatchedSupportFork_notGlobalBoundaryVanishes⟩

/-- The reorg-side repaired atlas has zero global-boundary receiver. -/
theorem reorgedAtlas_zeroGlobalBoundaryReceiver :
    Not (GlobalBoundaryReceiver reorgedAtlas) :=
  compatibleAtlas_zeroGlobalBoundaryReceiver

/-- The refactor-side repaired atlas is communication-compatible. -/
theorem refactoredAtlas_communicationCompatible :
    CommunicationCoverCompatible refactoredAtlas := by
  intro comm
  cases comm
  refine ⟨(), ?_⟩
  intro context _hcomm
  cases context <;> simp [refactoredAtlas, mergedOwnership]

/-- The refactor-side repaired atlas has zero global-boundary receiver. -/
theorem refactoredAtlas_zeroGlobalBoundaryReceiver :
    Not (GlobalBoundaryReceiver refactoredAtlas) :=
  compatible_no_globalBoundaryReceiver
    refactoredAtlas
    refactoredAtlas_communicationCompatible

/--
The selected Cycle 5 package: global zero-cochains are an exactness condition
for the selected boundary map, the mismatched atlas has no such global
zero-cochain, and both repaired examples have zero global-boundary receiver.
-/
theorem selectedGlobalBoundaryMapPackage :
    Nonempty (CommunicationZeroCochain compatibleAtlas) /\
      Not (GlobalBoundaryReceiver compatibleAtlas) /\
      GlobalBoundaryReceiver mismatchedAtlas /\
      Not (Nonempty (CommunicationZeroCochain mismatchedAtlas)) /\
      Not
        (SupportForkDefectVanishesModuloGlobalBoundary
          mismatchedSupportFork) /\
      Not (GlobalBoundaryReceiver reorgedAtlas) /\
      Not (GlobalBoundaryReceiver refactoredAtlas) := by
  exact
    ⟨(communicationZeroCochain_nonempty_iff_compatible compatibleAtlas).mpr
        compatibleAtlas_communicationCompatible,
      compatibleAtlas_zeroGlobalBoundaryReceiver,
      mismatchedAtlas_globalBoundaryReceiver,
      mismatchedAtlas_noCommunicationZeroCochain,
      mismatchedSupportFork_notGlobalBoundaryVanishes,
      reorgedAtlas_zeroGlobalBoundaryReceiver,
      refactoredAtlas_zeroGlobalBoundaryReceiver⟩

end ConwayTwoTopology
end SFT
end Formal.AG.Research
