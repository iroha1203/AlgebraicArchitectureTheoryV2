import ResearchLean.AG.SFT.ConwayOwnerUniformFamilyQuotient
import ResearchLean.AG.SFT.ConwayOwnerUniformSpanSelector

/-!
Cycle 19 evidence for `G-sft-conway-01`.

Cycle 17 recorded the owner-uniform local/global gap as a selected finite
quotient-style receiver.  Cycle 18 recorded the same gap as a selected
span-selector obstruction.  This file bridges the two presentations: in the
selected finite vocabulary, owner-uniform span selectors exist exactly when the
owner-uniform family class vanishes, and selector obstruction is forkwise
selectability together with nonzero quotient-style class.

This is a comparison between selected finite presentations.  It does not claim
a true quotient object, canonical selector, arbitrary-cover naturality, or a
sheaf `H^1` theorem.
-/

namespace Formal.AG.Research
namespace SFT
namespace ConwayTwoTopology

/-! ## Selector / quotient comparison -/

/--
Owner-uniform span selectors and the selected owner-uniform family class
detect the same owner-uniform support boundary.
-/
theorem ownerUniformSpanSelector_nonempty_iff_familyClassVanishes
    {atlas : TwoCoverAtlas}
    (family : SupportForkFamily atlas) :
    Nonempty (OwnerUniformSpanSelector family) ↔
      OwnerUniformFamilyClassVanishes family := by
  rw [ownerUniformSpanSelector_nonempty_iff_support,
    ownerUniformFamilyClass_vanishes_iff_support]

/-- A selected owner-uniform selector gives vanishing of the quotient-style class. -/
theorem ownerUniformFamilyClassVanishes_of_spanSelector
    {atlas : TwoCoverAtlas}
    {family : SupportForkFamily atlas}
    (selector : Nonempty (OwnerUniformSpanSelector family)) :
    OwnerUniformFamilyClassVanishes family :=
  (ownerUniformSpanSelector_nonempty_iff_familyClassVanishes family).1 selector

/-- Vanishing of the selected quotient-style class gives an owner-uniform selector. -/
theorem ownerUniformSpanSelector_of_familyClassVanishes
    {atlas : TwoCoverAtlas}
    {family : SupportForkFamily atlas}
    (hvanish : OwnerUniformFamilyClassVanishes family) :
    Nonempty (OwnerUniformSpanSelector family) :=
  (ownerUniformSpanSelector_nonempty_iff_familyClassVanishes family).2 hvanish

/--
The nonzero selected quotient-style class is exactly the failure of an
owner-uniform span selector.
-/
theorem ownerUniformFamilyNonzeroClass_iff_noSpanSelector
    {atlas : TwoCoverAtlas}
    (family : SupportForkFamily atlas) :
    OwnerUniformFamilyNonzeroClass family ↔
      Not (Nonempty (OwnerUniformSpanSelector family)) := by
  unfold OwnerUniformFamilyNonzeroClass
  rw [ownerUniformSpanSelector_nonempty_iff_familyClassVanishes]

/--
Selected owner-uniform selector obstruction is equivalently forkwise local
span selectability plus nonzero owner-uniform family class.
-/
theorem ownerUniformSpanSelectorObstruction_iff_forkwiseSelectable_and_nonzeroClass
    {atlas : TwoCoverAtlas}
    (family : SupportForkFamily atlas) :
    OwnerUniformSpanSelectorObstruction family ↔
      ForkwiseCommonRefinementSpanSelectable family /\
        OwnerUniformFamilyNonzeroClass family := by
  unfold OwnerUniformSpanSelectorObstruction
  rw [← ownerUniformFamilyNonzeroClass_iff_noSpanSelector]

/-- A selector obstruction carries the selected nonzero family class. -/
theorem ownerUniformFamilyNonzeroClass_of_spanSelectorObstruction
    {atlas : TwoCoverAtlas}
    {family : SupportForkFamily atlas}
    (hobstruction : OwnerUniformSpanSelectorObstruction family) :
    OwnerUniformFamilyNonzeroClass family :=
  ((ownerUniformSpanSelectorObstruction_iff_forkwiseSelectable_and_nonzeroClass
    family).1 hobstruction).2

/-- Forkwise selectability plus nonzero class builds the selector obstruction. -/
theorem ownerUniformSpanSelectorObstruction_of_forkwiseSelectable_nonzeroClass
    {atlas : TwoCoverAtlas}
    {family : SupportForkFamily atlas}
    (hforkwise : ForkwiseCommonRefinementSpanSelectable family)
    (hnonzero : OwnerUniformFamilyNonzeroClass family) :
    OwnerUniformSpanSelectorObstruction family :=
  (ownerUniformSpanSelectorObstruction_iff_forkwiseSelectable_and_nonzeroClass
    family).2 ⟨hforkwise, hnonzero⟩

/-! ## Restricted two-fork comparison package -/

/--
For the restricted two-fork family, the Cycle 18 selector obstruction and the
Cycle 17 nonzero quotient-style class are equivalent presentations.
-/
theorem restrictedTwoForkFamily_spanSelectorObstruction_iff_familyClassNonzero :
    OwnerUniformSpanSelectorObstruction restrictedTwoForkFamily ↔
      OwnerUniformFamilyNonzeroClass restrictedTwoForkFamily := by
  constructor
  · intro hobstruction
    exact ownerUniformFamilyNonzeroClass_of_spanSelectorObstruction hobstruction
  · intro hnonzero
    exact
      ownerUniformSpanSelectorObstruction_of_forkwiseSelectable_nonzeroClass
        restrictedTwoForkFamily_forkwiseSpanSelectable
        hnonzero

/-- The restricted two-fork selector obstruction implies the nonzero class. -/
theorem restrictedTwoForkFamily_spanSelectorObstruction_implies_familyClassNonzero :
    OwnerUniformFamilyNonzeroClass restrictedTwoForkFamily :=
  ownerUniformFamilyNonzeroClass_of_spanSelectorObstruction
    restrictedTwoForkFamily_ownerUniformSpanSelectorObstruction

/-- The restricted two-fork nonzero class rebuilds the selector obstruction. -/
theorem restrictedTwoForkFamily_familyClassNonzero_implies_spanSelectorObstruction :
    OwnerUniformSpanSelectorObstruction restrictedTwoForkFamily :=
  ownerUniformSpanSelectorObstruction_of_forkwiseSelectable_nonzeroClass
    restrictedTwoForkFamily_forkwiseSpanSelectable
    restrictedTwoForkFamily_ownerUniformFamilyClass_nonzero

/--
Each selected singleton subfamily has both presentations of the zero side:
owner-uniform selector and vanishing family class.
-/
theorem restrictedSingletonSubfamilies_spanSelector_and_familyClassVanishes
    (sub : RestrictedSingletonSubfamilyIdx) :
    Nonempty (OwnerUniformSpanSelector (restrictedSingletonSubfamily sub)) /\
      OwnerUniformFamilyClassVanishes (restrictedSingletonSubfamily sub) := by
  exact
    ⟨restrictedSingletonSubfamilies_ownerUniformSpanSelector sub,
      restrictedSingletonSubfamilies_ownerUniformFamilyClass_vanishes sub⟩

/--
The selected Cycle 19 bridge package: selector existence and quotient-style
class vanishing are the same finite boundary; selector obstruction is forkwise
selectability plus nonzero class; and the restricted two-fork witness realizes
the nonzero side while singleton subfamilies realize the zero side.
-/
theorem selectedOwnerUniformSelectorQuotientBridgePackage :
    (forall {atlas : TwoCoverAtlas}
      (family : SupportForkFamily atlas),
        Nonempty (OwnerUniformSpanSelector family) ↔
          OwnerUniformFamilyClassVanishes family) /\
      (forall {atlas : TwoCoverAtlas}
        (family : SupportForkFamily atlas),
          OwnerUniformSpanSelectorObstruction family ↔
            ForkwiseCommonRefinementSpanSelectable family /\
              OwnerUniformFamilyNonzeroClass family) /\
      (OwnerUniformSpanSelectorObstruction restrictedTwoForkFamily ↔
        OwnerUniformFamilyNonzeroClass restrictedTwoForkFamily) /\
      OwnerUniformSpanSelectorObstruction restrictedTwoForkFamily /\
      OwnerUniformFamilyNonzeroClass restrictedTwoForkFamily /\
      (forall sub : RestrictedSingletonSubfamilyIdx,
        Nonempty (OwnerUniformSpanSelector
          (restrictedSingletonSubfamily sub)) /\
          OwnerUniformFamilyClassVanishes
            (restrictedSingletonSubfamily sub)) := by
  exact
    ⟨(by
        intro atlas family
        exact ownerUniformSpanSelector_nonempty_iff_familyClassVanishes family),
      (by
        intro atlas family
        exact
          ownerUniformSpanSelectorObstruction_iff_forkwiseSelectable_and_nonzeroClass
            family),
      restrictedTwoForkFamily_spanSelectorObstruction_iff_familyClassNonzero,
      restrictedTwoForkFamily_ownerUniformSpanSelectorObstruction,
      restrictedTwoForkFamily_ownerUniformFamilyClass_nonzero,
      restrictedSingletonSubfamilies_spanSelector_and_familyClassVanishes⟩

end ConwayTwoTopology
end SFT
end Formal.AG.Research
