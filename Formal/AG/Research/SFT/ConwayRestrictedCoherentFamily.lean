import Formal.AG.Research.SFT.ConwayCoherentFamilyExactness

/-!
Cycle 15 evidence for `G-sft-conway-01`.

Cycle 14 showed that the current `CommonRefinementSpan` vocabulary is too
flexible: forkwise local supports always assemble into a Sigma-indexed coherent
family support.  This file introduces a deliberately restricted coherent-family
interface: the family may still choose different refinement blocks, but those
blocks must refine one shared ownership vertex.

That owner-uniform restriction is strong enough to separate local fork support
from coherent family support in a finite selected atlas.  This is not arbitrary
cover naturality or a sheaf theorem; it is the first restricted-span obstruction
showing why Cycle 14's unconstrained Sigma assembly is too permissive.
-/

namespace Formal.AG.Research
namespace SFT
namespace ConwayTwoTopology

/-! ## Owner-uniform coherent family support -/

/--
Owner-uniform coherent common-refinement support: every selected fork is covered
by a block over its communication index, and all selected blocks refine the same
ownership vertex.
-/
structure OwnerUniformCoherentCommonRefinementSupport {atlas : TwoCoverAtlas}
    (family : SupportForkFamily atlas) where
  span : CommonRefinementSpan atlas
  ref : family.ForkIdx -> span.RefIdx
  sharedOwner : atlas.OwnerIdx
  refines_comm :
    forall idx, span.refinesCommunication (ref idx) = (family.fork idx).left.comm
  refines_owner :
    forall idx, span.refinesOwnership (ref idx) = sharedOwner
  covers_comm :
    forall idx context,
      atlas.communication (family.fork idx).left.comm context ->
        span.refinement (ref idx) context

namespace OwnerUniformCoherentCommonRefinementSupport

/-- Owner-uniform support forgets to ordinary coherent support. -/
def toCoherentSupport {atlas : TwoCoverAtlas}
    {family : SupportForkFamily atlas}
    (support : OwnerUniformCoherentCommonRefinementSupport family) :
    CoherentCommonRefinementSupport family where
  span := support.span
  ref := support.ref
  refines_comm := support.refines_comm
  covers_comm := support.covers_comm

/-- The shared owner supports every selected communication block in the family. -/
theorem sharedOwner_supports
    {atlas : TwoCoverAtlas}
    {family : SupportForkFamily atlas}
    (support : OwnerUniformCoherentCommonRefinementSupport family)
    (idx : family.ForkIdx)
    (context : atlas.Context)
    (hcomm : atlas.communication (family.fork idx).left.comm context) :
    atlas.ownership support.sharedOwner context := by
  have hrefinement : support.span.refinement (support.ref idx) context :=
    support.covers_comm idx context hcomm
  have hownership :
      atlas.ownership (support.span.refinesOwnership (support.ref idx))
        context :=
    support.span.refinement_to_ownership
      (support.ref idx)
      context
      hrefinement
  simpa [support.refines_owner idx] using hownership

end OwnerUniformCoherentCommonRefinementSupport

/-- Existence predicate for owner-uniform coherent support. -/
def ForkFamilyHasOwnerUniformCoherentSupport
    {atlas : TwoCoverAtlas}
    (family : SupportForkFamily atlas) : Prop :=
  Nonempty (OwnerUniformCoherentCommonRefinementSupport family)

/-- Owner-uniform support implies ordinary coherent family support. -/
theorem ownerUniformSupport_implies_coherentSupport
    {atlas : TwoCoverAtlas}
    {family : SupportForkFamily atlas}
    (support : OwnerUniformCoherentCommonRefinementSupport family) :
    ForkFamilyHasCoherentCommonRefinementSupport family :=
  ⟨support.toCoherentSupport⟩

/-! ## A finite local-but-not-owner-uniform atlas -/

/-- Two selected communication blocks for the restricted-span separation. -/
inductive RestrictedComm where
  | apiComm
  | dbComm
  deriving DecidableEq

/-- Two local owners per selected context; no owner supports both contexts. -/
inductive RestrictedOwner where
  | apiPrimary
  | apiSecondary
  | dbPrimary
  | dbSecondary
  deriving DecidableEq

/-- The restricted communication cover separates the API and DB contexts. -/
def restrictedCommunication : RestrictedComm -> Module -> Prop
  | RestrictedComm.apiComm, Module.api => True
  | RestrictedComm.dbComm, Module.db => True
  | _, _ => False

/-- Each context has two local owners, but no owner spans both contexts. -/
def restrictedOwnership : RestrictedOwner -> Module -> Prop
  | RestrictedOwner.apiPrimary, Module.api => True
  | RestrictedOwner.apiSecondary, Module.api => True
  | RestrictedOwner.dbPrimary, Module.db => True
  | RestrictedOwner.dbSecondary, Module.db => True
  | _, _ => False

/--
Finite atlas where every selected fork is locally supported, but the two fork
family has no owner-uniform coherent support.
-/
def restrictedCoherentAtlas : TwoCoverAtlas where
  CommIdx := RestrictedComm
  OwnerIdx := RestrictedOwner
  Context := Module
  communication := restrictedCommunication
  ownership := restrictedOwnership

/-- API fork with two local owners over the API communication block. -/
def restrictedApiFork : SupportForkOneCochain restrictedCoherentAtlas where
  left := {
    comm := RestrictedComm.apiComm
    owner := RestrictedOwner.apiPrimary
    context := Module.api
    communication_holds := by
      simp [restrictedCoherentAtlas, restrictedCommunication]
    ownership_holds := by
      simp [restrictedCoherentAtlas, restrictedOwnership]
  }
  right := {
    comm := RestrictedComm.apiComm
    owner := RestrictedOwner.apiSecondary
    context := Module.api
    communication_holds := by
      simp [restrictedCoherentAtlas, restrictedCommunication]
    ownership_holds := by
      simp [restrictedCoherentAtlas, restrictedOwnership]
  }
  sameCommunication := rfl
  ownersDistinct := by
    intro howners
    cases howners

/-- DB fork with two local owners over the DB communication block. -/
def restrictedDbFork : SupportForkOneCochain restrictedCoherentAtlas where
  left := {
    comm := RestrictedComm.dbComm
    owner := RestrictedOwner.dbPrimary
    context := Module.db
    communication_holds := by
      simp [restrictedCoherentAtlas, restrictedCommunication]
    ownership_holds := by
      simp [restrictedCoherentAtlas, restrictedOwnership]
  }
  right := {
    comm := RestrictedComm.dbComm
    owner := RestrictedOwner.dbSecondary
    context := Module.db
    communication_holds := by
      simp [restrictedCoherentAtlas, restrictedCommunication]
    ownership_holds := by
      simp [restrictedCoherentAtlas, restrictedOwnership]
  }
  sameCommunication := rfl
  ownersDistinct := by
    intro howners
    cases howners

/-- The two selected forks used for the owner-uniform separation. -/
inductive RestrictedForkIdx where
  | apiFork
  | dbFork
  deriving DecidableEq

/-- Family containing the API and DB local forks. -/
def restrictedTwoForkFamily : SupportForkFamily restrictedCoherentAtlas where
  ForkIdx := RestrictedForkIdx
  fork
    | RestrictedForkIdx.apiFork => restrictedApiFork
    | RestrictedForkIdx.dbFork => restrictedDbFork

/-- The API fork has local single-owner support. -/
theorem restrictedApiFork_singleOwnerSupport :
    ForkHasSingleOwnerSupport restrictedApiFork := by
  refine ⟨RestrictedOwner.apiPrimary, ?_⟩
  intro context hcomm
  cases context <;>
    simp [restrictedApiFork, restrictedCoherentAtlas, restrictedCommunication,
      restrictedOwnership] at hcomm ⊢

/-- The DB fork has local single-owner support. -/
theorem restrictedDbFork_singleOwnerSupport :
    ForkHasSingleOwnerSupport restrictedDbFork := by
  refine ⟨RestrictedOwner.dbPrimary, ?_⟩
  intro context hcomm
  cases context <;>
    simp [restrictedDbFork, restrictedCoherentAtlas, restrictedCommunication,
      restrictedOwnership] at hcomm ⊢

/-- Every fork in the restricted two-fork family has local common-refinement support. -/
theorem restrictedTwoForkFamily_localSupport :
    ForkFamilyHasLocalCommonRefinementSupport restrictedTwoForkFamily := by
  intro idx
  cases idx with
  | apiFork =>
      exact
        (commonRefinementSupportsFork_iff_singleOwnerSupport
          restrictedApiFork).mpr
          restrictedApiFork_singleOwnerSupport
  | dbFork =>
      exact
        (commonRefinementSupportsFork_iff_singleOwnerSupport
          restrictedDbFork).mpr
          restrictedDbFork_singleOwnerSupport

/-- No restricted owner supports both selected contexts. -/
theorem restricted_noOwnerSupportsBothApiAndDb :
    Not
      (exists owner : RestrictedOwner,
        restrictedOwnership owner Module.api /\
          restrictedOwnership owner Module.db) := by
  intro howner
  rcases howner with ⟨owner, hapi, hdb⟩
  cases owner <;> simp [restrictedOwnership] at hapi hdb

/--
The restricted two-fork family has no owner-uniform coherent support: the shared
owner would have to support both API and DB contexts.
-/
theorem restrictedTwoForkFamily_notOwnerUniformCoherent :
    Not
      (ForkFamilyHasOwnerUniformCoherentSupport
        restrictedTwoForkFamily) := by
  intro hsupport
  rcases hsupport with ⟨support⟩
  have hapi :
      restrictedOwnership support.sharedOwner Module.api :=
    support.sharedOwner_supports
      RestrictedForkIdx.apiFork
      Module.api
      (by simp [restrictedTwoForkFamily, restrictedApiFork,
        restrictedCoherentAtlas, restrictedCommunication])
  have hdb :
      restrictedOwnership support.sharedOwner Module.db :=
    support.sharedOwner_supports
      RestrictedForkIdx.dbFork
      Module.db
      (by simp [restrictedTwoForkFamily, restrictedDbFork,
        restrictedCoherentAtlas, restrictedCommunication])
  exact restricted_noOwnerSupportsBothApiAndDb
    ⟨support.sharedOwner, hapi, hdb⟩

/-! ## Restricted local/shared receiver -/

/--
The restricted local/shared receiver: forkwise local support exists, but no
owner-uniform coherent family support exists.
-/
def OwnerUniformLocalButNotCoherentReceiver
    {atlas : TwoCoverAtlas}
    (family : SupportForkFamily atlas) : Prop :=
  ForkFamilyHasLocalCommonRefinementSupport family /\
    Not (ForkFamilyHasOwnerUniformCoherentSupport family)

/-- The finite restricted two-fork family realizes the local/shared receiver. -/
theorem restrictedTwoForkFamily_ownerUniformReceiver :
    OwnerUniformLocalButNotCoherentReceiver restrictedTwoForkFamily :=
  ⟨restrictedTwoForkFamily_localSupport,
    restrictedTwoForkFamily_notOwnerUniformCoherent⟩

/--
The selected Cycle 15 package: owner-uniform coherent support is stronger than
ordinary coherent support, and the restricted finite atlas separates forkwise
local support from owner-uniform coherent support.
-/
theorem selectedRestrictedCoherentFamilyPackage :
    (forall {atlas : TwoCoverAtlas}
      {family : SupportForkFamily atlas},
        OwnerUniformCoherentCommonRefinementSupport family ->
          ForkFamilyHasCoherentCommonRefinementSupport family) /\
      ForkFamilyHasLocalCommonRefinementSupport
        restrictedTwoForkFamily /\
      Not
        (ForkFamilyHasOwnerUniformCoherentSupport
          restrictedTwoForkFamily) /\
      OwnerUniformLocalButNotCoherentReceiver
        restrictedTwoForkFamily := by
  exact
    ⟨(by
        intro atlas family support
        exact ownerUniformSupport_implies_coherentSupport support),
      restrictedTwoForkFamily_localSupport,
      restrictedTwoForkFamily_notOwnerUniformCoherent,
      restrictedTwoForkFamily_ownerUniformReceiver⟩

end ConwayTwoTopology
end SFT
end Formal.AG.Research
