import Formal.AG.Research.SFT.ConwayTwoTopology

/-!
Cycle 2 evidence for `G-sft-conway-01`.

Cycle 1 fixed the selected zero/nonzero two-cover witness.  This file adds the
first refinement / nerve receiver layer over that witness: a cover refinement
predicate, one-edge common-refinement blocks, support-nerve edges, and a fork
receiver for the selected Conway obstruction.

The receiver is deliberately finite-combinatorial.  It does not claim a full
`H^1` theory yet; it supplies the first precise place where the obstruction
lives before a later `C^1/B^1` quotient or comparison-functor receiver is chosen.
-/

namespace Formal.AG.Research
namespace SFT
namespace ConwayTwoTopology

universe u

/-! ## Refinement vocabulary -/

/-- A selected cover refines another when every source block has one target support. -/
def CoverRefines {SourceIdx TargetIdx Context : Type}
    (source : SourceIdx -> Context -> Prop)
    (target : TargetIdx -> Context -> Prop) : Prop :=
  forall sourceIdx, exists targetIdx, forall context,
    source sourceIdx context -> target targetIdx context

/--
Communication-to-ownership refinement is exactly the Cycle 1 compatibility
predicate, now expressed as cover refinement.
-/
abbrev CommunicationOwnershipRefinement (atlas : TwoCoverAtlas) : Prop :=
  CoverRefines atlas.communication atlas.ownership

/-- Cycle 1 compatibility is the communication-to-ownership refinement relation. -/
theorem communicationCompatible_iff_coverRefines (atlas : TwoCoverAtlas) :
    CommunicationCoverCompatible atlas ↔ CommunicationOwnershipRefinement atlas :=
  Iff.rfl

/--
If ownership is indexed from communication, communication refines ownership by
construction.  This records the same degeneracy as a refinement statement.
-/
theorem ownershipIndexedFromCommunication_refines
    {CommIdx Context : Type} (communication : CommIdx -> Context -> Prop) :
    CommunicationOwnershipRefinement
      (ownershipIndexedFromCommunication communication) := by
  intro comm
  refine ⟨comm, ?_⟩
  intro context hcomm
  exact hcomm

/-! ## Common-refinement blocks and support nerve edges -/

/--
A common-refinement span is selected data refining both the communication and
ownership covers.
-/
structure CommonRefinementSpan (atlas : TwoCoverAtlas) where
  RefIdx : Type
  refinesCommunication : RefIdx -> atlas.CommIdx
  refinesOwnership : RefIdx -> atlas.OwnerIdx
  refinement : RefIdx -> atlas.Context -> Prop
  refinement_to_communication :
    forall ref context,
      refinement ref context ->
        atlas.communication (refinesCommunication ref) context
  refinement_to_ownership :
    forall ref context,
      refinement ref context ->
        atlas.ownership (refinesOwnership ref) context

/--
A support-nerve edge is a selected nonempty intersection of one communication
block and one ownership block, witnessed by a context.
-/
structure SupportNerveEdge (atlas : TwoCoverAtlas) where
  comm : atlas.CommIdx
  owner : atlas.OwnerIdx
  context : atlas.Context
  communication_holds : atlas.communication comm context
  ownership_holds : atlas.ownership owner context

namespace SupportNerveEdge

/-- A support-nerve edge gives a singleton common-refinement span. -/
def singletonCommonRefinement {atlas : TwoCoverAtlas}
    (edge : SupportNerveEdge atlas) : CommonRefinementSpan atlas where
  RefIdx := Unit
  refinesCommunication _ := edge.comm
  refinesOwnership _ := edge.owner
  refinement _ context := context = edge.context
  refinement_to_communication := by
    intro ref context hcontext
    cases ref
    subst context
    exact edge.communication_holds
  refinement_to_ownership := by
    intro ref context hcontext
    cases ref
    subst context
    exact edge.ownership_holds

end SupportNerveEdge

/-! ## Fork receiver for the selected Conway obstruction -/

/--
A support-nerve fork is two support edges over the same communication block but
with distinct ownership vertices.
-/
structure SupportNerveFork (atlas : TwoCoverAtlas) where
  left : SupportNerveEdge atlas
  right : SupportNerveEdge atlas
  sameCommunication : left.comm = right.comm
  ownersDistinct : Ne left.owner right.owner

/-- A support fork is globally supported when its communication block has one owner support. -/
def ForkHasSingleOwnerSupport {atlas : TwoCoverAtlas}
    (fork : SupportNerveFork atlas) : Prop :=
  CommunicationSupportedByOwnership atlas fork.left.comm

/--
The first Conway obstruction receiver: a support-nerve fork whose communication
block has no single owner support.
-/
def SupportNerveObstructionReceiver (atlas : TwoCoverAtlas) : Prop :=
  exists fork : SupportNerveFork atlas, Not (ForkHasSingleOwnerSupport fork)

/-- The Cycle 1 obstruction witness induces a support-nerve receiver witness. -/
theorem supportReceiver_of_conwayObstruction {atlas : TwoCoverAtlas}
    (h : ConwayObstructionWitness atlas) :
    SupportNerveObstructionReceiver atlas := by
  rcases h with
    ⟨comm, contextLeft, contextRight, ownerLeft, ownerRight,
      hCommLeft, hCommRight, hOwnLeft, hOwnRight, hOwnersDistinct, noSupport⟩
  refine
    ⟨{
      left := {
        comm := comm
        owner := ownerLeft
        context := contextLeft
        communication_holds := hCommLeft
        ownership_holds := hOwnLeft
      }
      right := {
        comm := comm
        owner := ownerRight
        context := contextRight
        communication_holds := hCommRight
        ownership_holds := hOwnRight
      }
      sameCommunication := rfl
      ownersDistinct := hOwnersDistinct
    }, ?_⟩
  exact noSupport

/-- A support-nerve receiver witness recovers the Cycle 1 obstruction witness. -/
theorem conwayObstruction_of_supportReceiver {atlas : TwoCoverAtlas}
    (h : SupportNerveObstructionReceiver atlas) :
    ConwayObstructionWitness atlas := by
  rcases h with ⟨fork, noSupport⟩
  refine
    ⟨fork.left.comm, fork.left.context, fork.right.context,
      fork.left.owner, fork.right.owner,
      fork.left.communication_holds, ?_, fork.left.ownership_holds,
      fork.right.ownership_holds, fork.ownersDistinct, noSupport⟩
  simpa [fork.sameCommunication] using fork.right.communication_holds

/--
The selected Conway obstruction is exactly the obstruction carried by the
support-nerve fork receiver.
-/
theorem supportReceiver_iff_conwayObstruction (atlas : TwoCoverAtlas) :
    SupportNerveObstructionReceiver atlas ↔ ConwayObstructionWitness atlas := by
  constructor
  · exact conwayObstruction_of_supportReceiver
  · exact supportReceiver_of_conwayObstruction

/-- Compatibility rules out the support-nerve obstruction receiver. -/
theorem compatible_no_supportReceiver (atlas : TwoCoverAtlas)
    (compatible : CommunicationCoverCompatible atlas) :
    Not (SupportNerveObstructionReceiver atlas) := by
  intro hreceiver
  exact
    compatible_no_conwayObstruction atlas compatible
      (conwayObstruction_of_supportReceiver hreceiver)

/-! ## Cycle 1 finite examples in the receiver vocabulary -/

/-- The compatible Cycle 1 atlas has no support-nerve obstruction receiver. -/
theorem compatibleAtlas_noSupportReceiver :
    Not (SupportNerveObstructionReceiver compatibleAtlas) := by
  intro hreceiver
  exact compatibleAtlas_zeroConwayObstruction
    (conwayObstruction_of_supportReceiver hreceiver)

/-- The mismatched Cycle 1 atlas has a support-nerve obstruction receiver. -/
theorem mismatchedAtlas_supportReceiver :
    SupportNerveObstructionReceiver mismatchedAtlas :=
  supportReceiver_of_conwayObstruction
    mismatchedAtlas_nonzeroConwayObstruction

/-- The reorg-side repaired atlas has no support-nerve obstruction receiver. -/
theorem reorgedAtlas_noSupportReceiver :
    Not (SupportNerveObstructionReceiver reorgedAtlas) := by
  intro hreceiver
  exact reorgedAtlas_zeroConwayObstruction
    (conwayObstruction_of_supportReceiver hreceiver)

/-- The refactor-side repaired atlas has no support-nerve obstruction receiver. -/
theorem refactoredAtlas_noSupportReceiver :
    Not (SupportNerveObstructionReceiver refactoredAtlas) := by
  intro hreceiver
  exact refactoredAtlas_zeroConwayObstruction
    (conwayObstruction_of_supportReceiver hreceiver)

/--
The selected Cycle 2 receiver package: the Cycle 1 zero/nonzero witness is now
located in the support-nerve fork receiver, with one-edge common-refinement
blocks available for every selected support edge.
-/
theorem selectedSupportReceiverPackage :
    CommunicationOwnershipRefinement compatibleAtlas /\
      Not (SupportNerveObstructionReceiver compatibleAtlas) /\
      SupportNerveObstructionReceiver mismatchedAtlas /\
      Not (CommunicationOwnershipRefinement mismatchedAtlas) /\
      Not (SupportNerveObstructionReceiver reorgedAtlas) /\
      Not (SupportNerveObstructionReceiver refactoredAtlas) := by
  exact
    ⟨(communicationCompatible_iff_coverRefines compatibleAtlas).mp
        (by
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
                simp [compatibleAtlas, splitCommunication, splitOwnership] at hcomm ⊢),
      compatibleAtlas_noSupportReceiver,
      mismatchedAtlas_supportReceiver,
      mismatchedAtlas_notCommunicationCompatible,
      reorgedAtlas_noSupportReceiver,
      refactoredAtlas_noSupportReceiver⟩

end ConwayTwoTopology
end SFT
end Formal.AG.Research
