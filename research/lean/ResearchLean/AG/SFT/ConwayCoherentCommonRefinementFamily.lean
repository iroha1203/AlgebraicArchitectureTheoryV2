import ResearchLean.AG.SFT.ConwayLocalVsGlobalCommonRefinement

/-!
Cycle 12 evidence for `G-sft-conway-01`.

Cycle 10 showed that a global zero-cochain supplies common-refinement support
for every selected fork.  Cycle 11 was a conservative separation package.  This
file moves beyond fork-by-fork singleton support by defining coherent
common-refinement support for a whole family of selected forks: one common
refinement span is shared, and each fork chooses a block from that shared span.

This is still finite selected Conway vocabulary.  It does not claim arbitrary
cover naturality or sheaf cohomology; it records the first family-level
coherence interface for common-refinement support.
-/

namespace ResearchLean.AG
namespace SFT
namespace ConwayTwoTopology

/-! ## Fork families and coherent support -/

/-- A selected family of support forks over one atlas. -/
structure SupportForkFamily (atlas : TwoCoverAtlas) where
  ForkIdx : Type
  fork : ForkIdx -> SupportForkOneCochain atlas

/--
Coherent common-refinement support for a fork family: one shared refinement span
contains one block over each selected fork's communication block, and that block
covers the whole communication block.
-/
structure CoherentCommonRefinementSupport {atlas : TwoCoverAtlas}
    (family : SupportForkFamily atlas) where
  span : CommonRefinementSpan atlas
  ref : family.ForkIdx -> span.RefIdx
  refines_comm :
    forall idx, span.refinesCommunication (ref idx) = (family.fork idx).left.comm
  covers_comm :
    forall idx context,
      atlas.communication (family.fork idx).left.comm context ->
        span.refinement (ref idx) context

namespace CoherentCommonRefinementSupport

/-- Coherent family support restricts to Cycle 9 support for each fork. -/
def toForkSupport {atlas : TwoCoverAtlas}
    {family : SupportForkFamily atlas}
    (support : CoherentCommonRefinementSupport family)
    (idx : family.ForkIdx) :
    CommonRefinementSupportsFork (family.fork idx) where
  span := support.span
  ref := support.ref idx
  refines_comm := support.refines_comm idx
  covers_comm := by
    intro context hcomm
    exact support.covers_comm idx context hcomm

end CoherentCommonRefinementSupport

/-- A predicate naming existence of coherent common-refinement support. -/
def ForkFamilyHasCoherentCommonRefinementSupport
    {atlas : TwoCoverAtlas}
    (family : SupportForkFamily atlas) : Prop :=
  Nonempty (CoherentCommonRefinementSupport family)

/-- Coherent family support gives single-fork support for every selected fork. -/
theorem coherentCommonRefinementSupport_implies_eachForkSupport
    {atlas : TwoCoverAtlas}
    {family : SupportForkFamily atlas}
    (support : CoherentCommonRefinementSupport family)
    (idx : family.ForkIdx) :
    Nonempty (CommonRefinementSupportsFork (family.fork idx)) :=
  ⟨support.toForkSupport idx⟩

/-! ## Global zero-cochains provide coherent family support -/

namespace CommunicationZeroCochain

/--
A global zero-cochain gives one shared common-refinement span indexed by
communication blocks, hence coherent support for any selected fork family.
-/
def toCoherentCommonRefinementSupport {atlas : TwoCoverAtlas}
    (zero : CommunicationZeroCochain atlas)
    (family : SupportForkFamily atlas) :
    CoherentCommonRefinementSupport family where
  span := {
    RefIdx := atlas.CommIdx
    refinesCommunication comm := comm
    refinesOwnership comm := zero.ownerOf comm
    refinement comm context := atlas.communication comm context
    refinement_to_communication := by
      intro comm context hcomm
      exact hcomm
    refinement_to_ownership := by
      intro comm context hcomm
      exact zero.supports comm context hcomm
  }
  ref idx := (family.fork idx).left.comm
  refines_comm := by
    intro idx
    rfl
  covers_comm := by
    intro idx context hcomm
    exact hcomm

end CommunicationZeroCochain

/-- A global zero-cochain gives coherent common-refinement support for any family. -/
theorem communicationZeroCochain_coherentCommonRefinementSupport
    {atlas : TwoCoverAtlas}
    (zero : CommunicationZeroCochain atlas)
    (family : SupportForkFamily atlas) :
    ForkFamilyHasCoherentCommonRefinementSupport family :=
  ⟨zero.toCoherentCommonRefinementSupport family⟩

/-! ## Family-level global/common-refinement vanishing -/

/--
Family-level vanishing: there is a global zero-cochain, and the same global
choice is represented as coherent common-refinement support for the selected
fork family.
-/
def SupportForkFamilyVanishesModuloCoherentGlobalCommonRefinement
    {atlas : TwoCoverAtlas}
    (family : SupportForkFamily atlas) : Prop :=
  Nonempty (CommunicationZeroCochain atlas) /\
    ForkFamilyHasCoherentCommonRefinementSupport family

/--
For every selected family, coherent global/common-refinement vanishing is
equivalent to communication-cover compatibility.  The coherent support side is
supplied by the same global zero-cochain.
-/
theorem familyCoherentGlobalCommonRefinement_vanishes_iff_compatible
    {atlas : TwoCoverAtlas}
    (family : SupportForkFamily atlas) :
    SupportForkFamilyVanishesModuloCoherentGlobalCommonRefinement family ↔
      CommunicationCoverCompatible atlas := by
  constructor
  · intro hvanish
    rcases hvanish.1 with ⟨zero⟩
    exact zero.toCompatibility
  · intro compatible
    let zero := CommunicationZeroCochain.ofCompatibility compatible
    exact
      ⟨⟨zero⟩,
        communicationZeroCochain_coherentCommonRefinementSupport zero family⟩

/-! ## Selected finite family examples -/

/-- The selected one-fork family containing the canonical mismatched fork. -/
def mismatchedSingletonForkFamily : SupportForkFamily mismatchedAtlas where
  ForkIdx := Unit
  fork _ := mismatchedSupportFork

/-- The selected empty family over the compatible atlas. -/
def compatibleEmptyForkFamily : SupportForkFamily compatibleAtlas where
  ForkIdx := Empty
  fork idx := by
    cases idx

/-- The mismatched singleton family has no coherent global/common-refinement vanishing. -/
theorem mismatchedSingletonForkFamily_notCoherentGlobalCommonRefinementVanishes :
    Not
      (SupportForkFamilyVanishesModuloCoherentGlobalCommonRefinement
        mismatchedSingletonForkFamily) := by
  intro hvanish
  exact
    mismatchedAtlas_notCommunicationCompatible
      ((familyCoherentGlobalCommonRefinement_vanishes_iff_compatible
        mismatchedSingletonForkFamily).mp hvanish)

/-- The compatible empty family has coherent global/common-refinement support. -/
theorem compatibleEmptyForkFamily_coherentGlobalCommonRefinementVanishes :
    SupportForkFamilyVanishesModuloCoherentGlobalCommonRefinement
      compatibleEmptyForkFamily :=
  (familyCoherentGlobalCommonRefinement_vanishes_iff_compatible
    compatibleEmptyForkFamily).mpr
      compatibleAtlas_communicationCompatible

/--
The selected Cycle 12 package: a global zero-cochain gives a shared
communication-indexed refinement span for any fork family, and the canonical
mismatch still blocks family-level coherent global/common-refinement vanishing.
-/
theorem selectedCoherentCommonRefinementFamilyPackage :
    (forall {atlas : TwoCoverAtlas}
      (_zero : CommunicationZeroCochain atlas)
      (family : SupportForkFamily atlas),
        ForkFamilyHasCoherentCommonRefinementSupport family) /\
      Not
        (SupportForkFamilyVanishesModuloCoherentGlobalCommonRefinement
          mismatchedSingletonForkFamily) /\
      SupportForkFamilyVanishesModuloCoherentGlobalCommonRefinement
        compatibleEmptyForkFamily := by
  exact
    ⟨(by
        intro atlas zero family
        exact communicationZeroCochain_coherentCommonRefinementSupport zero family),
      mismatchedSingletonForkFamily_notCoherentGlobalCommonRefinementVanishes,
      compatibleEmptyForkFamily_coherentGlobalCommonRefinementVanishes⟩

end ConwayTwoTopology
end SFT
end ResearchLean.AG
