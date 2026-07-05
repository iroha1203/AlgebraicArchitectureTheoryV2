import Formal.AG.Research.SFT.ConwayTwoTopology

/-!
Cycle 23 evidence for `G-sft-conway-01`.

Cycle 1 gave two repaired examples for the canonical Conway mismatch.  This
file promotes those examples to finite operation criteria: a reorg-side edit
changes the communication cover while keeping split ownership, and a
refactor-side edit changes the ownership cover while keeping the all-
communication block.  In each case, a concrete hitting predicate is equivalent
to post-edit communication compatibility, which kills the selected Conway
obstruction.

This is a finite selected operation theorem for the canonical witness.  It does
not claim real organizational causality, optimal repair, arbitrary-cover
naturality, or a sheaf cohomology statement.
-/

namespace Formal.AG.Research
namespace SFT
namespace ConwayTwoTopology

/-! ## Reorg-side communication edits -/

/--
A finite reorg-side edit of the canonical mismatch: only the communication
cover is changed; the ownership cover stays `splitOwnership`.
-/
structure ReorgCoverEdit where
  communication : Team -> Module -> Prop
  coversApi : communication Team.platform Module.api
  coversDb : communication Team.data Module.db

/-- The post-edit atlas produced by a reorg-side communication edit. -/
def ReorgCoverEdit.postAtlas (edit : ReorgCoverEdit) : TwoCoverAtlas where
  CommIdx := Team
  OwnerIdx := Owner
  Context := Module
  communication := edit.communication
  ownership := splitOwnership

/--
The reorg-side edit hits every canonical conflict when the platform block is
supported by the API owner and the data block is supported by the DB owner.
-/
def ReorgCoverEditHitsEveryConflict (edit : ReorgCoverEdit) : Prop :=
  (forall context,
    edit.communication Team.platform context ->
      splitOwnership Owner.apiOwner context) /\
    (forall context,
      edit.communication Team.data context ->
        splitOwnership Owner.dbOwner context)

namespace ReorgCoverEdit

/--
For canonical reorg edits, the concrete hitting criterion is exactly
communication compatibility of the post-edit atlas.
-/
theorem postCompatible_iff_hitsEveryConflict
    (edit : ReorgCoverEdit) :
    CommunicationCoverCompatible edit.postAtlas ↔
      ReorgCoverEditHitsEveryConflict edit := by
  constructor
  · intro compatible
    constructor
    · rcases compatible Team.platform with ⟨owner, howner⟩
      have hapi : splitOwnership owner Module.api :=
        howner Module.api edit.coversApi
      cases owner with
      | apiOwner =>
          exact howner
      | dbOwner =>
          simp [splitOwnership] at hapi
      | productOwner =>
          simp [splitOwnership] at hapi
    · rcases compatible Team.data with ⟨owner, howner⟩
      have hdb : splitOwnership owner Module.db :=
        howner Module.db edit.coversDb
      cases owner with
      | apiOwner =>
          simp [splitOwnership] at hdb
      | dbOwner =>
          exact howner
      | productOwner =>
          simp [splitOwnership] at hdb
  · intro hhit
    rcases hhit with ⟨hplatform, hdata⟩
    intro comm
    cases comm with
    | platform =>
        exact ⟨Owner.apiOwner, hplatform⟩
    | data =>
        exact ⟨Owner.dbOwner, hdata⟩

/--
A reorg edit satisfying the hitting criterion kills the selected Conway
obstruction in its post-edit atlas.
-/
theorem killsConwayObstruction_of_hitsEveryConflict
    (edit : ReorgCoverEdit)
    (hhit : ReorgCoverEditHitsEveryConflict edit) :
    Not (ConwayObstructionWitness edit.postAtlas) :=
  compatible_no_conwayObstruction
    edit.postAtlas
    ((edit.postCompatible_iff_hitsEveryConflict).2 hhit)

end ReorgCoverEdit

/-- The canonical reorg edit: split communication to match split ownership. -/
def canonicalReorgCoverEdit : ReorgCoverEdit where
  communication := splitCommunication
  coversApi := by
    simp [splitCommunication]
  coversDb := by
    simp [splitCommunication]

/-- The canonical reorg edit hits every conflict. -/
theorem canonicalReorgCoverEdit_hitsEveryConflict :
    ReorgCoverEditHitsEveryConflict canonicalReorgCoverEdit := by
  constructor
  · intro context hcomm
    cases context <;>
      simp [canonicalReorgCoverEdit, splitCommunication, splitOwnership]
        at hcomm ⊢
  · intro context hcomm
    cases context <;>
      simp [canonicalReorgCoverEdit, splitCommunication, splitOwnership]
        at hcomm ⊢

/-- The canonical reorg edit kills the selected Conway obstruction. -/
theorem canonicalReorgCoverEdit_killsConwayObstruction :
    Not
      (ConwayObstructionWitness
        canonicalReorgCoverEdit.postAtlas) :=
  canonicalReorgCoverEdit.killsConwayObstruction_of_hitsEveryConflict
    canonicalReorgCoverEdit_hitsEveryConflict

/-! ## Refactor-side ownership edits -/

/--
A finite refactor-side edit of the canonical mismatch: the communication cover
stays the all-communication block, and the ownership cover is edited.
-/
structure RefactorOwnershipEdit where
  ownership : Unit -> Module -> Prop

/-- The post-edit atlas produced by a refactor-side ownership edit. -/
def RefactorOwnershipEdit.postAtlas
    (edit : RefactorOwnershipEdit) : TwoCoverAtlas where
  CommIdx := Unit
  OwnerIdx := Unit
  Context := Module
  communication := allCommunication
  ownership := edit.ownership

/--
The refactor-side edit hits the canonical conflict when the edited owner block
supports every context in the all-communication block.
-/
def RefactorOwnershipEditHitsEveryConflict
    (edit : RefactorOwnershipEdit) : Prop :=
  forall context, edit.ownership () context

namespace RefactorOwnershipEdit

/--
For canonical refactor edits, the concrete hitting criterion is exactly
communication compatibility of the post-edit atlas.
-/
theorem postCompatible_iff_hitsEveryConflict
    (edit : RefactorOwnershipEdit) :
    CommunicationCoverCompatible edit.postAtlas ↔
      RefactorOwnershipEditHitsEveryConflict edit := by
  constructor
  · intro compatible context
    rcases compatible () with ⟨owner, howner⟩
    cases owner
    exact howner context trivial
  · intro hhit comm
    cases comm
    exact
      ⟨(), by
        intro context _hcomm
        exact hhit context⟩

/--
A refactor edit satisfying the hitting criterion kills the selected Conway
obstruction in its post-edit atlas.
-/
theorem killsConwayObstruction_of_hitsEveryConflict
    (edit : RefactorOwnershipEdit)
    (hhit : RefactorOwnershipEditHitsEveryConflict edit) :
    Not (ConwayObstructionWitness edit.postAtlas) :=
  compatible_no_conwayObstruction
    edit.postAtlas
    ((edit.postCompatible_iff_hitsEveryConflict).2 hhit)

end RefactorOwnershipEdit

/-- The canonical refactor edit: merge ownership to match all communication. -/
def canonicalRefactorOwnershipEdit : RefactorOwnershipEdit where
  ownership := mergedOwnership

/-- The canonical refactor edit hits every conflict. -/
theorem canonicalRefactorOwnershipEdit_hitsEveryConflict :
    RefactorOwnershipEditHitsEveryConflict
      canonicalRefactorOwnershipEdit := by
  intro context
  cases context <;> simp [canonicalRefactorOwnershipEdit, mergedOwnership]

/-- The canonical refactor edit kills the selected Conway obstruction. -/
theorem canonicalRefactorOwnershipEdit_killsConwayObstruction :
    Not
      (ConwayObstructionWitness
        canonicalRefactorOwnershipEdit.postAtlas) :=
  canonicalRefactorOwnershipEdit.killsConwayObstruction_of_hitsEveryConflict
    canonicalRefactorOwnershipEdit_hitsEveryConflict

/-! ## Combined operation package -/

inductive CanonicalRepairOperation where
  | reorg
  | refactor
  deriving DecidableEq

/-- The post-edit atlas for the two canonical one-sided repairs. -/
def CanonicalRepairOperation.postAtlas :
    CanonicalRepairOperation -> TwoCoverAtlas
  | CanonicalRepairOperation.reorg => canonicalReorgCoverEdit.postAtlas
  | CanonicalRepairOperation.refactor => canonicalRefactorOwnershipEdit.postAtlas

/-- Both canonical one-sided repair operations kill the selected obstruction. -/
theorem canonicalRepairOperation_killsConwayObstruction
    (operation : CanonicalRepairOperation) :
    Not
      (ConwayObstructionWitness
        (CanonicalRepairOperation.postAtlas operation)) := by
  cases operation with
  | reorg =>
      exact canonicalReorgCoverEdit_killsConwayObstruction
  | refactor =>
      exact canonicalRefactorOwnershipEdit_killsConwayObstruction

/--
The selected Cycle 23 package: reorg-side communication edits and refactor-side
ownership edits each have a concrete hitting criterion equivalent to post-edit
compatibility, and the canonical one-sided edits satisfy those criteria and
kill the selected Conway obstruction.
-/
theorem selectedReorgRefactorKillingPackage :
    (forall edit : ReorgCoverEdit,
      CommunicationCoverCompatible edit.postAtlas ↔
        ReorgCoverEditHitsEveryConflict edit) /\
      ReorgCoverEditHitsEveryConflict canonicalReorgCoverEdit /\
      Not
        (ConwayObstructionWitness
          canonicalReorgCoverEdit.postAtlas) /\
      (forall edit : RefactorOwnershipEdit,
        CommunicationCoverCompatible edit.postAtlas ↔
          RefactorOwnershipEditHitsEveryConflict edit) /\
      RefactorOwnershipEditHitsEveryConflict
        canonicalRefactorOwnershipEdit /\
      Not
        (ConwayObstructionWitness
          canonicalRefactorOwnershipEdit.postAtlas) /\
      (forall operation : CanonicalRepairOperation,
        Not
          (ConwayObstructionWitness
            (CanonicalRepairOperation.postAtlas operation))) := by
  exact
    ⟨(by
        intro edit
        exact edit.postCompatible_iff_hitsEveryConflict),
      canonicalReorgCoverEdit_hitsEveryConflict,
      canonicalReorgCoverEdit_killsConwayObstruction,
      (by
        intro edit
        exact edit.postCompatible_iff_hitsEveryConflict),
      canonicalRefactorOwnershipEdit_hitsEveryConflict,
      canonicalRefactorOwnershipEdit_killsConwayObstruction,
      canonicalRepairOperation_killsConwayObstruction⟩

end ConwayTwoTopology
end SFT
end Formal.AG.Research
