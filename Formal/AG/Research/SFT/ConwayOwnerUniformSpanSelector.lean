import Formal.AG.Research.SFT.ConwayOwnerUniformSubfamilyDescent

/-!
Cycle 18 evidence for `G-sft-conway-01`.

Cycle 14 showed that unconstrained forkwise common-refinement supports assemble
by Sigma-indexing.  Cycle 15/16 showed that the assembly can still fail after
adding an owner-uniform restriction.  This file packages that boundary as a
selected span-selector obstruction: forkwise local common-refinement spans can
be selected, but those selected spans need not glue to one shared ownership
vertex.

This is finite selected selector vocabulary.  It does not claim a canonical
algorithmic selector, arbitrary-cover naturality, a true quotient object, or a
sheaf `H^1` theorem.
-/

namespace Formal.AG.Research
namespace SFT
namespace ConwayTwoTopology

/-! ## Forkwise and owner-uniform span selectors -/

/--
A forkwise common-refinement span selector chooses explicit local
common-refinement support for every selected fork in a family.
-/
structure ForkwiseCommonRefinementSpanSelector {atlas : TwoCoverAtlas}
    (family : SupportForkFamily atlas) where
  support : forall idx, CommonRefinementSupportsFork (family.fork idx)

/-- Existence predicate for forkwise common-refinement span selectors. -/
def ForkwiseCommonRefinementSpanSelectable {atlas : TwoCoverAtlas}
    (family : SupportForkFamily atlas) : Prop :=
  Nonempty (ForkwiseCommonRefinementSpanSelector family)

namespace ForkwiseCommonRefinementSpanSelector

/-- A forkwise span selector forgets to the Cycle 14 local support predicate. -/
theorem toLocalSupport {atlas : TwoCoverAtlas}
    {family : SupportForkFamily atlas}
    (selector : ForkwiseCommonRefinementSpanSelector family) :
    ForkFamilyHasLocalCommonRefinementSupport family := by
  intro idx
  exact ⟨selector.support idx⟩

/-- Local common-refinement support can be recorded as a forkwise selector. -/
noncomputable def ofLocalSupport {atlas : TwoCoverAtlas}
    {family : SupportForkFamily atlas}
    (support : ForkFamilyHasLocalCommonRefinementSupport family) :
    ForkwiseCommonRefinementSpanSelector family where
  support idx := Classical.choice (support idx)

end ForkwiseCommonRefinementSpanSelector

/-- Forkwise span selectors exist exactly when every fork has local support. -/
theorem forkwiseSpanSelector_nonempty_iff_localSupport
    {atlas : TwoCoverAtlas}
    (family : SupportForkFamily atlas) :
    ForkwiseCommonRefinementSpanSelectable family ↔
      ForkFamilyHasLocalCommonRefinementSupport family := by
  constructor
  · intro hselector
    rcases hselector with ⟨selector⟩
    exact selector.toLocalSupport
  · intro hlocal
    exact ⟨ForkwiseCommonRefinementSpanSelector.ofLocalSupport hlocal⟩

/--
An owner-uniform span selector: forkwise selected local spans are present, and
their selected refinement blocks all refine one shared ownership vertex.
-/
structure OwnerUniformSpanSelector {atlas : TwoCoverAtlas}
    (family : SupportForkFamily atlas) where
  forkwise : ForkwiseCommonRefinementSpanSelector family
  sharedOwner : atlas.OwnerIdx
  refines_shared :
    forall idx,
      (forkwise.support idx).span.refinesOwnership
        ((forkwise.support idx).ref) = sharedOwner

namespace OwnerUniformSpanSelector

/-- An owner-uniform selector forgets to its forkwise local selector. -/
theorem toForkwiseSelectable {atlas : TwoCoverAtlas}
    {family : SupportForkFamily atlas}
    (selector : OwnerUniformSpanSelector family) :
    ForkwiseCommonRefinementSpanSelectable family :=
  ⟨selector.forkwise⟩

/--
An owner-uniform selector assembles into owner-uniform coherent support by
Sigma-indexing the selected local spans.
-/
noncomputable def toOwnerUniformSupport {atlas : TwoCoverAtlas}
    {family : SupportForkFamily atlas}
    (selector : OwnerUniformSpanSelector family) :
    OwnerUniformCoherentCommonRefinementSupport family where
  span := {
    RefIdx :=
      Sigma fun idx => (selector.forkwise.support idx).span.RefIdx
    refinesCommunication ref :=
      (selector.forkwise.support ref.1).span.refinesCommunication ref.2
    refinesOwnership ref :=
      (selector.forkwise.support ref.1).span.refinesOwnership ref.2
    refinement ref context :=
      (selector.forkwise.support ref.1).span.refinement ref.2 context
    refinement_to_communication := by
      intro ref context hrefinement
      exact
        (selector.forkwise.support ref.1).span.refinement_to_communication
          ref.2
          context
          hrefinement
    refinement_to_ownership := by
      intro ref context hrefinement
      exact
        (selector.forkwise.support ref.1).span.refinement_to_ownership
          ref.2
          context
          hrefinement
  }
  ref idx := ⟨idx, (selector.forkwise.support idx).ref⟩
  sharedOwner := selector.sharedOwner
  refines_comm := by
    intro idx
    exact (selector.forkwise.support idx).refines_comm
  refines_owner := by
    intro idx
    exact selector.refines_shared idx
  covers_comm := by
    intro idx context hcomm
    exact (selector.forkwise.support idx).covers_comm context hcomm

/-- Owner-uniform coherent support can be recorded as an owner-uniform selector. -/
def ofOwnerUniformSupport {atlas : TwoCoverAtlas}
    {family : SupportForkFamily atlas}
    (support : OwnerUniformCoherentCommonRefinementSupport family) :
    OwnerUniformSpanSelector family where
  forkwise := {
    support idx := {
      span := support.span
      ref := support.ref idx
      refines_comm := support.refines_comm idx
      covers_comm := by
        intro context hcomm
        exact support.covers_comm idx context hcomm
    }
  }
  sharedOwner := support.sharedOwner
  refines_shared := by
    intro idx
    exact support.refines_owner idx

end OwnerUniformSpanSelector

/-- Owner-uniform span selectors exist exactly when owner-uniform support exists. -/
theorem ownerUniformSpanSelector_nonempty_iff_support
    {atlas : TwoCoverAtlas}
    (family : SupportForkFamily atlas) :
    Nonempty (OwnerUniformSpanSelector family) ↔
      ForkFamilyHasOwnerUniformCoherentSupport family := by
  constructor
  · intro hselector
    rcases hselector with ⟨selector⟩
    exact ⟨selector.toOwnerUniformSupport⟩
  · intro hsupport
    rcases hsupport with ⟨support⟩
    exact ⟨OwnerUniformSpanSelector.ofOwnerUniformSupport support⟩

/-! ## Selected restricted selector obstruction -/

/--
A selected span-selector obstruction: forkwise local span selections exist, but
they cannot be made owner-uniform.
-/
def OwnerUniformSpanSelectorObstruction {atlas : TwoCoverAtlas}
    (family : SupportForkFamily atlas) : Prop :=
  ForkwiseCommonRefinementSpanSelectable family /\
    Not (Nonempty (OwnerUniformSpanSelector family))

/-- A concrete common-refinement support for the restricted API fork. -/
def restrictedApiFork_commonRefinementSupport :
    CommonRefinementSupportsFork restrictedApiFork where
  span := {
    RefIdx := Unit
    refinesCommunication _ := RestrictedComm.apiComm
    refinesOwnership _ := RestrictedOwner.apiPrimary
    refinement _ context := restrictedCommunication RestrictedComm.apiComm context
    refinement_to_communication := by
      intro ref context hrefinement
      exact hrefinement
    refinement_to_ownership := by
      intro ref context hrefinement
      cases context <;>
        simp [restrictedCoherentAtlas, restrictedCommunication,
          restrictedOwnership] at hrefinement ⊢
  }
  ref := ()
  refines_comm := by
    simp [restrictedApiFork]
  covers_comm := by
    intro context hcomm
    exact hcomm

/-- A concrete common-refinement support for the restricted DB fork. -/
def restrictedDbFork_commonRefinementSupport :
    CommonRefinementSupportsFork restrictedDbFork where
  span := {
    RefIdx := Unit
    refinesCommunication _ := RestrictedComm.dbComm
    refinesOwnership _ := RestrictedOwner.dbPrimary
    refinement _ context := restrictedCommunication RestrictedComm.dbComm context
    refinement_to_communication := by
      intro ref context hrefinement
      exact hrefinement
    refinement_to_ownership := by
      intro ref context hrefinement
      cases context <;>
        simp [restrictedCoherentAtlas, restrictedCommunication,
          restrictedOwnership] at hrefinement ⊢
  }
  ref := ()
  refines_comm := by
    simp [restrictedDbFork]
  covers_comm := by
    intro context hcomm
    exact hcomm

/-- The restricted two-fork family has a concrete forkwise local span selector. -/
def restrictedTwoForkFamily_forkwiseSpanSelector :
    ForkwiseCommonRefinementSpanSelector restrictedTwoForkFamily where
  support idx := by
    cases idx with
    | apiFork =>
        exact restrictedApiFork_commonRefinementSupport
    | dbFork =>
        exact restrictedDbFork_commonRefinementSupport

/-- Existence form of the restricted two-fork forkwise selector. -/
theorem restrictedTwoForkFamily_forkwiseSpanSelectable :
    ForkwiseCommonRefinementSpanSelectable restrictedTwoForkFamily :=
  ⟨restrictedTwoForkFamily_forkwiseSpanSelector⟩

/-- The restricted two-fork family has no owner-uniform span selector. -/
theorem restrictedTwoForkFamily_noOwnerUniformSpanSelector :
    Not (Nonempty (OwnerUniformSpanSelector restrictedTwoForkFamily)) := by
  intro hselector
  exact restrictedTwoForkFamily_notOwnerUniformCoherent
    ((ownerUniformSpanSelector_nonempty_iff_support
      restrictedTwoForkFamily).mp hselector)

/-- The restricted two-fork family realizes the selected span-selector obstruction. -/
theorem restrictedTwoForkFamily_ownerUniformSpanSelectorObstruction :
    OwnerUniformSpanSelectorObstruction restrictedTwoForkFamily :=
  ⟨restrictedTwoForkFamily_forkwiseSpanSelectable,
    restrictedTwoForkFamily_noOwnerUniformSpanSelector⟩

/-- The API singleton subfamily has an owner-uniform span selector. -/
theorem restrictedApiSingletonFamily_ownerUniformSpanSelector :
    Nonempty (OwnerUniformSpanSelector restrictedApiSingletonFamily) :=
  (ownerUniformSpanSelector_nonempty_iff_support
    restrictedApiSingletonFamily).mpr
      restrictedApiSingletonFamily_ownerUniformSupport

/-- The DB singleton subfamily has an owner-uniform span selector. -/
theorem restrictedDbSingletonFamily_ownerUniformSpanSelector :
    Nonempty (OwnerUniformSpanSelector restrictedDbSingletonFamily) :=
  (ownerUniformSpanSelector_nonempty_iff_support
    restrictedDbSingletonFamily).mpr
      restrictedDbSingletonFamily_ownerUniformSupport

/-- Every selected singleton subfamily has an owner-uniform span selector. -/
theorem restrictedSingletonSubfamilies_ownerUniformSpanSelector
    (sub : RestrictedSingletonSubfamilyIdx) :
    Nonempty (OwnerUniformSpanSelector
      (restrictedSingletonSubfamily sub)) := by
  cases sub with
  | apiOnly =>
      exact restrictedApiSingletonFamily_ownerUniformSpanSelector
  | dbOnly =>
      exact restrictedDbSingletonFamily_ownerUniformSpanSelector

/--
The selected Cycle 18 package: local span choices exist forkwise and on each
singleton subfamily, but no owner-uniform selector glues them over the full
restricted two-fork family.
-/
theorem selectedOwnerUniformSpanSelectorObstructionPackage :
    ForkwiseCommonRefinementSpanSelectable restrictedTwoForkFamily /\
      Not (Nonempty (OwnerUniformSpanSelector restrictedTwoForkFamily)) /\
      OwnerUniformSpanSelectorObstruction restrictedTwoForkFamily /\
      (forall sub : RestrictedSingletonSubfamilyIdx,
        Nonempty (OwnerUniformSpanSelector
          (restrictedSingletonSubfamily sub))) /\
      SupportForkFamilySubcover
        restrictedTwoForkFamily
        RestrictedSingletonSubfamilyIdx
        restrictedSingletonSubfamily := by
  exact
    ⟨restrictedTwoForkFamily_forkwiseSpanSelectable,
      restrictedTwoForkFamily_noOwnerUniformSpanSelector,
      restrictedTwoForkFamily_ownerUniformSpanSelectorObstruction,
      restrictedSingletonSubfamilies_ownerUniformSpanSelector,
      restrictedSingletonSubfamilies_cover⟩

end ConwayTwoTopology
end SFT
end Formal.AG.Research
