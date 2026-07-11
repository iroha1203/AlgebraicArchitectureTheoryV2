import ResearchLean.AG.SFT.ConwayOwnerUniformTrueQuotient

/-!
Cycle 22 evidence for `G-sft-conway-01`.

Cycle 21 recorded a finite Cech-style boundary shadow, but adversarial review
correctly noted that its `C0` term was still a wrapper around existing boundary
generator provenance.  This file adds an independent finite incidence receiver:
vertices are owners, edges are selected forks, and incidence means that one
owner supports the communication block of that fork.

The receiver is finite selected Conway vocabulary.  It does not claim true
sheaf cohomology, arbitrary-cover naturality, a canonical selector, or real
organizational causality.
-/

namespace Formal.AG.Research
namespace SFT
namespace ConwayTwoTopology

/-! ## Owner/fork incidence receiver -/

/-- The owner vertices of the selected incidence receiver for a fork family. -/
abbrev OwnerUniformIncidenceVertex {atlas : TwoCoverAtlas}
    (_family : SupportForkFamily atlas) :=
  atlas.OwnerIdx

/-- The fork edges of the selected incidence receiver for a fork family. -/
abbrev OwnerUniformIncidenceEdge {atlas : TwoCoverAtlas}
    (family : SupportForkFamily atlas) :=
  family.ForkIdx

/--
An owner vertex is incident to a fork edge when that owner supports the
communication block selected by the fork.
-/
def OwnerUniformIncidenceIncident {atlas : TwoCoverAtlas}
    (family : SupportForkFamily atlas)
    (owner : OwnerUniformIncidenceVertex family)
    (edge : OwnerUniformIncidenceEdge family) : Prop :=
  forall context,
    atlas.communication (family.fork edge).left.comm context ->
      atlas.ownership owner context

/--
A global section of the owner/fork incidence receiver: one owner vertex
incident to every selected fork edge.
-/
structure OwnerUniformIncidenceGlobalSection {atlas : TwoCoverAtlas}
    (family : SupportForkFamily atlas) where
  owner : OwnerUniformIncidenceVertex family
  incident : forall edge : OwnerUniformIncidenceEdge family,
    OwnerUniformIncidenceIncident family owner edge

/--
The incidence receiver has a local section on every edge when each selected
fork has some incident owner.
-/
def OwnerUniformIncidenceLocallySupported {atlas : TwoCoverAtlas}
    (family : SupportForkFamily atlas) : Prop :=
  forall edge : OwnerUniformIncidenceEdge family,
    exists owner : OwnerUniformIncidenceVertex family,
      OwnerUniformIncidenceIncident family owner edge

/--
The incidence receiver has a local/global gap when every edge has a local owner
vertex but no one owner vertex is incident to all edges.
-/
def OwnerUniformIncidenceLocalGlobalGap {atlas : TwoCoverAtlas}
    (family : SupportForkFamily atlas) : Prop :=
  OwnerUniformIncidenceLocallySupported family /\
    Not (Nonempty (OwnerUniformIncidenceGlobalSection family))

namespace OwnerUniformIncidenceGlobalSection

/--
A global incidence section builds owner-uniform coherent support: use one
refinement block per fork edge, each refining the same owner vertex.
-/
def toOwnerUniformSupport {atlas : TwoCoverAtlas}
    {family : SupportForkFamily atlas}
    (global : OwnerUniformIncidenceGlobalSection family) :
    OwnerUniformCoherentCommonRefinementSupport family where
  span := {
    RefIdx := OwnerUniformIncidenceEdge family
    refinesCommunication edge := (family.fork edge).left.comm
    refinesOwnership _ := global.owner
    refinement edge context :=
      atlas.communication (family.fork edge).left.comm context
    refinement_to_communication := by
      intro edge context hcomm
      exact hcomm
    refinement_to_ownership := by
      intro edge context hcomm
      exact global.incident edge context hcomm
  }
  ref edge := edge
  sharedOwner := global.owner
  refines_comm := by
    intro edge
    rfl
  refines_owner := by
    intro edge
    rfl
  covers_comm := by
    intro edge context hcomm
    exact hcomm

/--
Owner-uniform coherent support gives a global incidence section by taking its
shared owner.
-/
def ofOwnerUniformSupport {atlas : TwoCoverAtlas}
    {family : SupportForkFamily atlas}
    (support : OwnerUniformCoherentCommonRefinementSupport family) :
    OwnerUniformIncidenceGlobalSection family where
  owner := support.sharedOwner
  incident := by
    intro edge context hcomm
    exact support.sharedOwner_supports edge context hcomm

end OwnerUniformIncidenceGlobalSection

/--
The independent incidence receiver has a global section exactly when the fork
family has owner-uniform coherent support.
-/
theorem ownerUniformIncidenceGlobalSection_nonempty_iff_support
    {atlas : TwoCoverAtlas}
    (family : SupportForkFamily atlas) :
    Nonempty (OwnerUniformIncidenceGlobalSection family) ↔
      ForkFamilyHasOwnerUniformCoherentSupport family := by
  constructor
  · intro hsection
    rcases hsection with ⟨global⟩
    exact ⟨global.toOwnerUniformSupport⟩
  · intro hsupport
    rcases hsupport with ⟨support⟩
    exact ⟨OwnerUniformIncidenceGlobalSection.ofOwnerUniformSupport support⟩

/--
The selected Conway class is zero exactly when the owner/fork incidence receiver
has a global section.
-/
theorem ownerUniformConwayClass_eq_zero_iff_incidenceGlobalSection
    {atlas : TwoCoverAtlas}
    (family : SupportForkFamily atlas) :
    OwnerUniformConwayClass family = 0 ↔
      Nonempty (OwnerUniformIncidenceGlobalSection family) := by
  rw [ownerUniformConwayClass_eq_zero_iff_familyClassVanishes,
    ownerUniformFamilyClass_vanishes_iff_support,
    ← ownerUniformIncidenceGlobalSection_nonempty_iff_support]

/-! ## Restricted finite witness -/

/-- The API singleton edge has an incident owner vertex. -/
theorem restrictedApiSingleton_incidenceLocallySupported :
    OwnerUniformIncidenceLocallySupported restrictedApiSingletonFamily := by
  intro edge
  refine ⟨RestrictedOwner.apiPrimary, ?_⟩
  intro context hcomm
  cases edge
  cases context <;>
    simp [restrictedApiSingletonFamily, restrictedApiFork,
      restrictedCoherentAtlas, restrictedCommunication, restrictedOwnership]
      at hcomm ⊢

/-- The DB singleton edge has an incident owner vertex. -/
theorem restrictedDbSingleton_incidenceLocallySupported :
    OwnerUniformIncidenceLocallySupported restrictedDbSingletonFamily := by
  intro edge
  refine ⟨RestrictedOwner.dbPrimary, ?_⟩
  intro context hcomm
  cases edge
  cases context <;>
    simp [restrictedDbSingletonFamily, restrictedDbFork,
      restrictedCoherentAtlas, restrictedCommunication, restrictedOwnership]
      at hcomm ⊢

/-- Every selected singleton subfamily has local incidence support. -/
theorem restrictedSingletonSubfamilies_incidenceLocallySupported
    (sub : RestrictedSingletonSubfamilyIdx) :
    OwnerUniformIncidenceLocallySupported
      (restrictedSingletonSubfamily sub) := by
  cases sub with
  | apiOnly =>
      exact restrictedApiSingleton_incidenceLocallySupported
  | dbOnly =>
      exact restrictedDbSingleton_incidenceLocallySupported

/-- Every selected singleton subfamily has a global incidence section. -/
theorem restrictedSingletonSubfamilies_incidenceGlobalSection
    (sub : RestrictedSingletonSubfamilyIdx) :
    Nonempty
      (OwnerUniformIncidenceGlobalSection
        (restrictedSingletonSubfamily sub)) := by
  rw [ownerUniformIncidenceGlobalSection_nonempty_iff_support]
  exact restrictedSingletonSubfamilies_ownerUniformSupport sub

/-- The full restricted two-fork family has local incidence support on every edge. -/
theorem restrictedTwoForkFamily_incidenceLocallySupported :
    OwnerUniformIncidenceLocallySupported restrictedTwoForkFamily := by
  intro edge
  cases edge with
  | apiFork =>
      refine ⟨RestrictedOwner.apiPrimary, ?_⟩
      intro context hcomm
      cases context <;>
        simp [restrictedTwoForkFamily, restrictedApiFork,
          restrictedCoherentAtlas, restrictedCommunication,
          restrictedOwnership] at hcomm ⊢
  | dbFork =>
      refine ⟨RestrictedOwner.dbPrimary, ?_⟩
      intro context hcomm
      cases context <;>
        simp [restrictedTwoForkFamily, restrictedDbFork,
          restrictedCoherentAtlas, restrictedCommunication,
          restrictedOwnership] at hcomm ⊢

/-- The full restricted two-fork family has no global incidence section. -/
theorem restrictedTwoForkFamily_no_incidenceGlobalSection :
    Not
      (Nonempty
        (OwnerUniformIncidenceGlobalSection restrictedTwoForkFamily)) := by
  rw [ownerUniformIncidenceGlobalSection_nonempty_iff_support]
  exact restrictedTwoForkFamily_notOwnerUniformCoherent

/-- The full restricted two-fork family realizes the incidence local/global gap. -/
theorem restrictedTwoForkFamily_incidenceLocalGlobalGap :
    OwnerUniformIncidenceLocalGlobalGap restrictedTwoForkFamily :=
  ⟨restrictedTwoForkFamily_incidenceLocallySupported,
    restrictedTwoForkFamily_no_incidenceGlobalSection⟩

/--
The full restricted two-fork family has nonzero Conway class exactly because
the incidence receiver has no global section.
-/
theorem restrictedTwoForkFamily_conwayClass_nonzero_iff_no_incidenceGlobalSection :
    OwnerUniformConwayClass restrictedTwoForkFamily ≠ 0 ↔
      Not
        (Nonempty
          (OwnerUniformIncidenceGlobalSection restrictedTwoForkFamily)) := by
  rw [← ownerUniformConwayClass_eq_zero_iff_incidenceGlobalSection]

/--
The selected Cycle 22 package: owner/fork incidence is an independent finite
receiver; global incidence sections are equivalent to owner-uniform coherent
support and to zero of the selected Conway class; selected singleton
subfamilies have global sections; and the full restricted two-fork family is
locally incident but has no global section.
-/
theorem selectedOwnerUniformIncidenceReceiverPackage :
    (forall {atlas : TwoCoverAtlas}
      (family : SupportForkFamily atlas),
        Nonempty (OwnerUniformIncidenceGlobalSection family) ↔
          ForkFamilyHasOwnerUniformCoherentSupport family) /\
      (forall {atlas : TwoCoverAtlas}
        (family : SupportForkFamily atlas),
          OwnerUniformConwayClass family = 0 ↔
            Nonempty (OwnerUniformIncidenceGlobalSection family)) /\
      (forall sub : RestrictedSingletonSubfamilyIdx,
        OwnerUniformIncidenceLocallySupported
          (restrictedSingletonSubfamily sub)) /\
      (forall sub : RestrictedSingletonSubfamilyIdx,
        Nonempty
          (OwnerUniformIncidenceGlobalSection
            (restrictedSingletonSubfamily sub))) /\
      OwnerUniformIncidenceLocallySupported restrictedTwoForkFamily /\
      Not
        (Nonempty
          (OwnerUniformIncidenceGlobalSection restrictedTwoForkFamily)) /\
      OwnerUniformIncidenceLocalGlobalGap restrictedTwoForkFamily /\
      (OwnerUniformConwayClass restrictedTwoForkFamily ≠ 0 ↔
        Not
          (Nonempty
            (OwnerUniformIncidenceGlobalSection restrictedTwoForkFamily))) := by
  exact
    ⟨(by
        intro atlas family
        exact ownerUniformIncidenceGlobalSection_nonempty_iff_support family),
      (by
        intro atlas family
        exact ownerUniformConwayClass_eq_zero_iff_incidenceGlobalSection
          family),
      restrictedSingletonSubfamilies_incidenceLocallySupported,
      restrictedSingletonSubfamilies_incidenceGlobalSection,
      restrictedTwoForkFamily_incidenceLocallySupported,
      restrictedTwoForkFamily_no_incidenceGlobalSection,
      restrictedTwoForkFamily_incidenceLocalGlobalGap,
      restrictedTwoForkFamily_conwayClass_nonzero_iff_no_incidenceGlobalSection⟩

end ConwayTwoTopology
end SFT
end Formal.AG.Research
