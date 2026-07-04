import Formal.AG.Research.SFT.ConwayRestrictedCoherentFamily

/-!
Cycle 16 evidence for `G-sft-conway-01`.

Cycle 15 proved that the restricted two-fork family has forkwise local support
but no owner-uniform coherent family support.  This file sharpens that
separation into a selected subfamily descent failure: the API singleton
subfamily and the DB singleton subfamily each have owner-uniform support, and
they cover the selected fork family, but their supports do not glue to one
owner-uniform support of the whole family.

This remains finite selected Conway vocabulary.  It is not a quotient object,
not arbitrary-cover naturality, and not a sheaf `H^1` theorem.
-/

namespace Formal.AG.Research
namespace SFT
namespace ConwayTwoTopology

/-! ## Selected subfamily covers -/

/--
A selected family cover: every fork of `whole` appears in one of the local
selected families.  This is an index-level cover for the current finite
research interface, not a general cover category.
-/
def SupportForkFamilySubcover {atlas : TwoCoverAtlas}
    (whole : SupportForkFamily atlas)
    (SubIdx : Type)
    (subfamily : SubIdx -> SupportForkFamily atlas) : Prop :=
  forall idx : whole.ForkIdx,
    exists sub : SubIdx,
      exists localIdx : (subfamily sub).ForkIdx,
        (subfamily sub).fork localIdx = whole.fork idx

/--
Owner-uniform subfamily descent failure: a selected family is covered by local
subfamilies, every local subfamily has owner-uniform coherent support, but the
whole selected family does not.
-/
def OwnerUniformSubfamilyDescentFailure {atlas : TwoCoverAtlas}
    (whole : SupportForkFamily atlas)
    (SubIdx : Type)
    (subfamily : SubIdx -> SupportForkFamily atlas) : Prop :=
  SupportForkFamilySubcover whole SubIdx subfamily /\
    (forall sub : SubIdx,
      ForkFamilyHasOwnerUniformCoherentSupport (subfamily sub)) /\
    Not (ForkFamilyHasOwnerUniformCoherentSupport whole)

/-! ## Restricted singleton subfamilies -/

/-- The API singleton subfamily of the restricted two-fork family. -/
def restrictedApiSingletonFamily : SupportForkFamily restrictedCoherentAtlas where
  ForkIdx := Unit
  fork _ := restrictedApiFork

/-- The DB singleton subfamily of the restricted two-fork family. -/
def restrictedDbSingletonFamily : SupportForkFamily restrictedCoherentAtlas where
  ForkIdx := Unit
  fork _ := restrictedDbFork

/-- The two singleton subfamilies covering the restricted two-fork family. -/
inductive RestrictedSingletonSubfamilyIdx where
  | apiOnly
  | dbOnly
  deriving DecidableEq

/-- The selected singleton subfamily indexed by `RestrictedSingletonSubfamilyIdx`. -/
def restrictedSingletonSubfamily :
    RestrictedSingletonSubfamilyIdx -> SupportForkFamily restrictedCoherentAtlas
  | RestrictedSingletonSubfamilyIdx.apiOnly => restrictedApiSingletonFamily
  | RestrictedSingletonSubfamilyIdx.dbOnly => restrictedDbSingletonFamily

/-! ## Local owner-uniform supports -/

/-- The API singleton subfamily has owner-uniform coherent support. -/
def restrictedApiSingletonOwnerUniformSupport :
    OwnerUniformCoherentCommonRefinementSupport
      restrictedApiSingletonFamily where
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
  ref _ := ()
  sharedOwner := RestrictedOwner.apiPrimary
  refines_comm := by
    intro idx
    cases idx
    simp [restrictedApiSingletonFamily, restrictedApiFork]
  refines_owner := by
    intro idx
    cases idx
    rfl
  covers_comm := by
    intro idx context hcomm
    cases idx
    exact hcomm

/-- The DB singleton subfamily has owner-uniform coherent support. -/
def restrictedDbSingletonOwnerUniformSupport :
    OwnerUniformCoherentCommonRefinementSupport
      restrictedDbSingletonFamily where
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
  ref _ := ()
  sharedOwner := RestrictedOwner.dbPrimary
  refines_comm := by
    intro idx
    cases idx
    simp [restrictedDbSingletonFamily, restrictedDbFork]
  refines_owner := by
    intro idx
    cases idx
    rfl
  covers_comm := by
    intro idx context hcomm
    cases idx
    exact hcomm

/-- Existence form of API singleton owner-uniform support. -/
theorem restrictedApiSingletonFamily_ownerUniformSupport :
    ForkFamilyHasOwnerUniformCoherentSupport
      restrictedApiSingletonFamily :=
  ⟨restrictedApiSingletonOwnerUniformSupport⟩

/-- Existence form of DB singleton owner-uniform support. -/
theorem restrictedDbSingletonFamily_ownerUniformSupport :
    ForkFamilyHasOwnerUniformCoherentSupport
      restrictedDbSingletonFamily :=
  ⟨restrictedDbSingletonOwnerUniformSupport⟩

/-- The two singleton subfamilies cover the restricted two-fork family. -/
theorem restrictedSingletonSubfamilies_cover :
    SupportForkFamilySubcover
      restrictedTwoForkFamily
      RestrictedSingletonSubfamilyIdx
      restrictedSingletonSubfamily := by
  intro idx
  cases idx with
  | apiFork =>
      exact
        ⟨RestrictedSingletonSubfamilyIdx.apiOnly, (),
          by
            simp [restrictedSingletonSubfamily, restrictedApiSingletonFamily,
              restrictedTwoForkFamily]⟩
  | dbFork =>
      exact
        ⟨RestrictedSingletonSubfamilyIdx.dbOnly, (),
          by
            simp [restrictedSingletonSubfamily, restrictedDbSingletonFamily,
              restrictedTwoForkFamily]⟩

/-- Every selected singleton subfamily has owner-uniform coherent support. -/
theorem restrictedSingletonSubfamilies_ownerUniformSupport
    (sub : RestrictedSingletonSubfamilyIdx) :
    ForkFamilyHasOwnerUniformCoherentSupport
      (restrictedSingletonSubfamily sub) := by
  cases sub with
  | apiOnly =>
      exact restrictedApiSingletonFamily_ownerUniformSupport
  | dbOnly =>
      exact restrictedDbSingletonFamily_ownerUniformSupport

/-! ## Descent failure package -/

/--
The restricted two-fork family has owner-uniform local subfamily support but no
owner-uniform support after gluing the selected subfamilies.
-/
theorem restrictedTwoForkFamily_ownerUniformSubfamilyDescentFailure :
    OwnerUniformSubfamilyDescentFailure
      restrictedTwoForkFamily
      RestrictedSingletonSubfamilyIdx
      restrictedSingletonSubfamily :=
  ⟨restrictedSingletonSubfamilies_cover,
    restrictedSingletonSubfamilies_ownerUniformSupport,
    restrictedTwoForkFamily_notOwnerUniformCoherent⟩

/--
The selected Cycle 16 package: owner-uniform support exists locally on the
singleton subfamily cover of the restricted two-fork family, but does not glue
to an owner-uniform support of the whole family.
-/
theorem selectedOwnerUniformSubfamilyDescentPackage :
    SupportForkFamilySubcover
      restrictedTwoForkFamily
      RestrictedSingletonSubfamilyIdx
      restrictedSingletonSubfamily /\
      (forall sub : RestrictedSingletonSubfamilyIdx,
        ForkFamilyHasOwnerUniformCoherentSupport
          (restrictedSingletonSubfamily sub)) /\
      Not
        (ForkFamilyHasOwnerUniformCoherentSupport
          restrictedTwoForkFamily) /\
      OwnerUniformSubfamilyDescentFailure
        restrictedTwoForkFamily
        RestrictedSingletonSubfamilyIdx
        restrictedSingletonSubfamily := by
  exact
    ⟨restrictedSingletonSubfamilies_cover,
      restrictedSingletonSubfamilies_ownerUniformSupport,
      restrictedTwoForkFamily_notOwnerUniformCoherent,
      restrictedTwoForkFamily_ownerUniformSubfamilyDescentFailure⟩

end ConwayTwoTopology
end SFT
end Formal.AG.Research
