import Formal.AG.Research.Basic

/-!
Cycle 1 evidence for `G-sft-conway-01`.

This file starts the Conway part of SFT as a finite two-cover comparison,
not as an empirical mirroring claim.  The communication cover and the
ownership cover are independent selected data.  The finite witnesses below
show a zero case, a nonzero mismatch case, and two one-sided repairs of the
selected mismatch by changing either the communication side or the ownership
side.
-/

namespace ResearchLean.AG
namespace SFT
namespace ConwayTwoTopology

/-! ## Abstract two-cover comparison -/

/--
A finite Conway comparison atlas with two independently supplied covers over
the same selected context family.
-/
structure TwoCoverAtlas where
  CommIdx : Type
  OwnerIdx : Type
  Context : Type
  communication : CommIdx -> Context -> Prop
  ownership : OwnerIdx -> Context -> Prop

/-- One communication block is supported by a single ownership block. -/
def CommunicationSupportedByOwnership (atlas : TwoCoverAtlas)
    (comm : atlas.CommIdx) : Prop :=
  exists owner, forall context,
    atlas.communication comm context -> atlas.ownership owner context

/--
The selected communication cover is compatible with the ownership cover when
each communication block has a single ownership support.
-/
def CommunicationCoverCompatible (atlas : TwoCoverAtlas) : Prop :=
  forall comm, CommunicationSupportedByOwnership atlas comm

/--
A selected Conway obstruction witness: one communication block contains two
contexts assigned to distinct ownership blocks, while no single ownership block
supports that communication block.
-/
def ConwayObstructionWitness (atlas : TwoCoverAtlas) : Prop :=
  exists comm contextLeft contextRight ownerLeft ownerRight,
    atlas.communication comm contextLeft /\
      atlas.communication comm contextRight /\
      atlas.ownership ownerLeft contextLeft /\
      atlas.ownership ownerRight contextRight /\
      Ne ownerLeft ownerRight /\
      Not (CommunicationSupportedByOwnership atlas comm)

/-- Compatibility rules out the selected obstruction witness. -/
theorem compatible_no_conwayObstruction (atlas : TwoCoverAtlas)
    (compatible : CommunicationCoverCompatible atlas) :
    Not (ConwayObstructionWitness atlas) := by
  intro witness
  rcases witness with
    ⟨comm, _contextLeft, _contextRight, _ownerLeft, _ownerRight,
      _hCommLeft, _hCommRight, _hOwnLeft, _hOwnRight, _hOwnersDistinct,
      noSupport⟩
  exact noSupport (compatible comm)

/-! ## A canonical two-module family -/

inductive Module where
  | api
  | db
  deriving DecidableEq

inductive Team where
  | platform
  | data
  deriving DecidableEq

inductive Owner where
  | apiOwner
  | dbOwner
  | productOwner
  deriving DecidableEq

/-- A communication cover that separates the two selected modules. -/
def splitCommunication : Team -> Module -> Prop
  | Team.platform, Module.api => True
  | Team.data, Module.db => True
  | _, _ => False

/-- An ownership cover matching the split communication cover. -/
def splitOwnership : Owner -> Module -> Prop
  | Owner.apiOwner, Module.api => True
  | Owner.dbOwner, Module.db => True
  | _, _ => False

/-- A communication cover with one organization-side block seeing both modules. -/
def allCommunication : Unit -> Module -> Prop
  | (), _ => True

/-- A merged ownership cover with one architecture-side owner seeing both modules. -/
def mergedOwnership : Unit -> Module -> Prop
  | (), _ => True

/-- Compatible selected data: communication and ownership split the same way. -/
def compatibleAtlas : TwoCoverAtlas where
  CommIdx := Team
  OwnerIdx := Owner
  Context := Module
  communication := splitCommunication
  ownership := splitOwnership

/--
Mismatched selected data: one communication block sees both modules, but
ownership is split.  This is the finite nonzero Conway witness used below.
-/
def mismatchedAtlas : TwoCoverAtlas where
  CommIdx := Unit
  OwnerIdx := Owner
  Context := Module
  communication := allCommunication
  ownership := splitOwnership

/-- Reorg-side repair: change the communication cover to match ownership. -/
def reorgedAtlas : TwoCoverAtlas :=
  compatibleAtlas

/-- Refactor-side repair: change the ownership cover to match communication. -/
def refactoredAtlas : TwoCoverAtlas where
  CommIdx := Unit
  OwnerIdx := Unit
  Context := Module
  communication := allCommunication
  ownership := mergedOwnership

/-- The compatible finite atlas has zero selected Conway obstruction. -/
theorem compatibleAtlas_zeroConwayObstruction :
    Not (ConwayObstructionWitness compatibleAtlas) := by
  apply compatible_no_conwayObstruction
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

/-- The all-communication block is not supported by any split owner. -/
theorem mismatchedAtlas_allCommunication_notSupported :
    Not (CommunicationSupportedByOwnership mismatchedAtlas ()) := by
  intro supported
  rcases supported with ⟨owner, howner⟩
  cases owner with
  | apiOwner =>
      have hdb : splitOwnership Owner.apiOwner Module.db := by
        exact howner Module.db (by simp [mismatchedAtlas, allCommunication])
      simp [splitOwnership] at hdb
  | dbOwner =>
      have hapi : splitOwnership Owner.dbOwner Module.api := by
        exact howner Module.api (by simp [mismatchedAtlas, allCommunication])
      simp [splitOwnership] at hapi
  | productOwner =>
      have hapi : splitOwnership Owner.productOwner Module.api := by
        exact howner Module.api (by simp [mismatchedAtlas, allCommunication])
      simp [splitOwnership] at hapi

/-- The mismatched finite atlas has a nonzero selected Conway obstruction. -/
theorem mismatchedAtlas_nonzeroConwayObstruction :
    ConwayObstructionWitness mismatchedAtlas := by
  refine
    ⟨(), Module.api, Module.db, Owner.apiOwner, Owner.dbOwner,
      ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [mismatchedAtlas, allCommunication]
  · simp [mismatchedAtlas, allCommunication]
  · simp [mismatchedAtlas, splitOwnership]
  · simp [mismatchedAtlas, splitOwnership]
  · intro howners
    cases howners
  · exact mismatchedAtlas_allCommunication_notSupported

/-- The mismatched finite atlas is not communication-compatible. -/
theorem mismatchedAtlas_notCommunicationCompatible :
    Not (CommunicationCoverCompatible mismatchedAtlas) := by
  intro compatible
  exact mismatchedAtlas_allCommunication_notSupported (compatible ())

/-- The reorg-side repaired atlas has zero selected Conway obstruction. -/
theorem reorgedAtlas_zeroConwayObstruction :
    Not (ConwayObstructionWitness reorgedAtlas) := by
  exact compatibleAtlas_zeroConwayObstruction

/-- The refactor-side repaired atlas has zero selected Conway obstruction. -/
theorem refactoredAtlas_zeroConwayObstruction :
    Not (ConwayObstructionWitness refactoredAtlas) := by
  apply compatible_no_conwayObstruction
  intro comm
  cases comm
  refine ⟨(), ?_⟩
  intro context _hcomm
  cases context <;> simp [refactoredAtlas, mergedOwnership]

/-! ## Circular ownership-indexing degeneracy -/

/--
The forbidden degenerate construction: derive ownership indices directly from
communication indices.  This makes compatibility true by construction.
-/
def ownershipIndexedFromCommunication {CommIdx Context : Type}
    (communication : CommIdx -> Context -> Prop) : TwoCoverAtlas where
  CommIdx := CommIdx
  OwnerIdx := CommIdx
  Context := Context
  communication := communication
  ownership := communication

/--
If ownership is indexed from communication, the selected Conway obstruction
is trivially zero.  This is the finite version of the GOAL's
definition-circularity warning.
-/
theorem ownershipIndexedFromCommunication_zeroConwayObstruction
    {CommIdx Context : Type} (communication : CommIdx -> Context -> Prop) :
    Not
      (ConwayObstructionWitness
        (ownershipIndexedFromCommunication communication)) := by
  exact
    compatible_no_conwayObstruction
      (ownershipIndexedFromCommunication communication)
      (by
        intro comm
        refine ⟨comm, ?_⟩
        intro context hcomm
        exact hcomm)

/--
The selected witness package: compatible data has zero obstruction, independent
mismatched data has a nonzero obstruction, and both one-sided repairs return to
zero obstruction.
-/
theorem selectedConwayTwoCoverWitnessPackage :
    Not (ConwayObstructionWitness compatibleAtlas) /\
      ConwayObstructionWitness mismatchedAtlas /\
      Not (CommunicationCoverCompatible mismatchedAtlas) /\
      Not (ConwayObstructionWitness reorgedAtlas) /\
      Not (ConwayObstructionWitness refactoredAtlas) := by
  exact
    ⟨compatibleAtlas_zeroConwayObstruction,
      mismatchedAtlas_nonzeroConwayObstruction,
      mismatchedAtlas_notCommunicationCompatible,
      reorgedAtlas_zeroConwayObstruction,
      refactoredAtlas_zeroConwayObstruction⟩

end ConwayTwoTopology
end SFT
end ResearchLean.AG
