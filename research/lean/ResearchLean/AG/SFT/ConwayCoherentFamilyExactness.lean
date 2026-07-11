import ResearchLean.AG.SFT.ConwayCoherentFamilyMorphism

/-!
Cycle 14 evidence for `G-sft-conway-01`.

Cycle 12 introduced coherent common-refinement support for a fork family, and
Cycle 13 proved selected morphism pullback.  A natural next failure candidate is
that every fork might have local common-refinement support while no one shared
span supports the whole family.

At the current selected Conway interface that failure cannot occur: the local
support spans can be summed into one Sigma-indexed `CommonRefinementSpan`.  This
file records that exactness/blocker theorem.  It does not claim arbitrary cover
naturality or a true sheaf gluing theorem; it identifies that the present
`CommonRefinementSpan` vocabulary is too flexible to detect a local-vs-shared
family obstruction.
-/

namespace Formal.AG.Research
namespace SFT
namespace ConwayTwoTopology

/-! ## Local family support and coherent exactness -/

/-- Every selected fork in a family has local common-refinement support. -/
def ForkFamilyHasLocalCommonRefinementSupport
    {atlas : TwoCoverAtlas}
    (family : SupportForkFamily atlas) : Prop :=
  forall idx,
    Nonempty (CommonRefinementSupportsFork (family.fork idx))

namespace CoherentCommonRefinementSupport

/--
Local fork-by-fork common-refinement support can be assembled into one coherent
family support by taking the Sigma sum of the local support spans.
-/
noncomputable def ofEachForkSupport {atlas : TwoCoverAtlas}
    {family : SupportForkFamily atlas}
    (support : ForkFamilyHasLocalCommonRefinementSupport family) :
    CoherentCommonRefinementSupport family where
  span := {
    RefIdx :=
      Sigma fun idx =>
        (Classical.choice (support idx)).span.RefIdx
    refinesCommunication ref :=
      (Classical.choice (support ref.1)).span.refinesCommunication ref.2
    refinesOwnership ref :=
      (Classical.choice (support ref.1)).span.refinesOwnership ref.2
    refinement ref context :=
      (Classical.choice (support ref.1)).span.refinement ref.2 context
    refinement_to_communication := by
      intro ref context href
      exact
        (Classical.choice (support ref.1)).span.refinement_to_communication
          ref.2
          context
          href
    refinement_to_ownership := by
      intro ref context href
      exact
        (Classical.choice (support ref.1)).span.refinement_to_ownership
          ref.2
          context
          href
  }
  ref idx := ⟨idx, (Classical.choice (support idx)).ref⟩
  refines_comm := by
    intro idx
    exact (Classical.choice (support idx)).refines_comm
  covers_comm := by
    intro idx context hcomm
    exact (Classical.choice (support idx)).covers_comm context hcomm

end CoherentCommonRefinementSupport

/--
Coherent common-refinement support is exactly fork-by-fork local support at the
current selected interface.
-/
theorem coherentCommonRefinementSupport_iff_eachForkSupport
    {atlas : TwoCoverAtlas}
    (family : SupportForkFamily atlas) :
    ForkFamilyHasCoherentCommonRefinementSupport family ↔
      ForkFamilyHasLocalCommonRefinementSupport family := by
  constructor
  · intro hcoherent idx
    rcases hcoherent with ⟨support⟩
    exact coherentCommonRefinementSupport_implies_eachForkSupport support idx
  · intro hlocal
    exact ⟨CoherentCommonRefinementSupport.ofEachForkSupport hlocal⟩

/-! ## Local-but-incoherent blocker -/

/--
A candidate local/shared obstruction: every fork has local support, but the
family has no coherent shared support.
-/
def ForkFamilyLocalButNotCoherent
    {atlas : TwoCoverAtlas}
    (family : SupportForkFamily atlas) : Prop :=
  ForkFamilyHasLocalCommonRefinementSupport family /\
    Not (ForkFamilyHasCoherentCommonRefinementSupport family)

/--
At the current selected interface, a local-but-not-coherent fork family cannot
exist.
-/
theorem no_forkFamilyLocalButNotCoherent
    {atlas : TwoCoverAtlas}
    (family : SupportForkFamily atlas) :
    Not (ForkFamilyLocalButNotCoherent family) := by
  intro hfailure
  exact hfailure.2
    ((coherentCommonRefinementSupport_iff_eachForkSupport family).mpr
      hfailure.1)

/-! ## Interaction with coherent global/common-refinement vanishing -/

/--
If a family vanishes modulo coherent global/common-refinement, then every fork
has local common-refinement support.
-/
theorem coherentGlobalCommonRefinementVanishes_implies_localSupport
    {atlas : TwoCoverAtlas}
    {family : SupportForkFamily atlas}
    (hvanish :
      SupportForkFamilyVanishesModuloCoherentGlobalCommonRefinement family) :
    ForkFamilyHasLocalCommonRefinementSupport family := by
  exact
    (coherentCommonRefinementSupport_iff_eachForkSupport family).mp
      hvanish.2

/--
Conversely, local family support plus a global zero-cochain gives coherent
global/common-refinement vanishing, because local supports assemble coherently.
-/
theorem localSupport_and_globalZeroCochain_implies_coherentVanishes
    {atlas : TwoCoverAtlas}
    {family : SupportForkFamily atlas}
    (hlocal : ForkFamilyHasLocalCommonRefinementSupport family)
    (hzero : Nonempty (CommunicationZeroCochain atlas)) :
    SupportForkFamilyVanishesModuloCoherentGlobalCommonRefinement family := by
  exact
    ⟨hzero,
      (coherentCommonRefinementSupport_iff_eachForkSupport family).mpr
        hlocal⟩

/--
The selected Cycle 14 package: local fork-by-fork common-refinement support is
equivalent to coherent family support, so the intended local-but-not-shared
failure mode is blocked at this interface.
-/
theorem selectedCoherentFamilyExactnessPackage :
    (forall {atlas : TwoCoverAtlas}
      (family : SupportForkFamily atlas),
        ForkFamilyHasCoherentCommonRefinementSupport family ↔
          ForkFamilyHasLocalCommonRefinementSupport family) /\
      (forall {atlas : TwoCoverAtlas}
        (family : SupportForkFamily atlas),
          Not (ForkFamilyLocalButNotCoherent family)) /\
      (forall {atlas : TwoCoverAtlas}
        {family : SupportForkFamily atlas},
          SupportForkFamilyVanishesModuloCoherentGlobalCommonRefinement
            family ->
            ForkFamilyHasLocalCommonRefinementSupport family) := by
  exact
    ⟨(by
        intro atlas family
        exact coherentCommonRefinementSupport_iff_eachForkSupport family),
      (by
        intro atlas family
        exact no_forkFamilyLocalButNotCoherent family),
      (by
        intro atlas family hvanish
        exact coherentGlobalCommonRefinementVanishes_implies_localSupport
          hvanish)⟩

end ConwayTwoTopology
end SFT
end Formal.AG.Research
