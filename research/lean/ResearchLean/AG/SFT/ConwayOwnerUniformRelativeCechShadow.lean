import ResearchLean.AG.SFT.ConwayOwnerUniformTrueQuotient

/-!
Cycle 21 evidence for `G-sft-conway-01`.

Cycle 20 gave the owner-uniform Conway obstruction an explicit selected finite
quotient carrier.  This file records what finite Cech-style shadow that carrier
comes from: an explicit `C0 -> C1` boundary image whose degree-zero terms are
owner-uniform boundary-generator provenance and whose degree-one coefficient is
the selected `ZMod 2` family defect.

This is only a selected finite relative Cech shadow.  It does not claim a true
sheaf `H^1`, arbitrary-site cohomology, arbitrary-cover naturality, or a
canonical selector.
-/

namespace Formal.AG.Research
namespace SFT
namespace ConwayTwoTopology

/-! ## Selected finite relative Cech shadow -/

/--
The selected degree-zero cochains for the finite relative Cech shadow:
explicit owner-uniform boundary-generator provenance for the chosen support
fork family.
-/
structure OwnerUniformRelativeCechCochain0 {atlas : TwoCoverAtlas}
    (family : SupportForkFamily atlas) where
  generator : OwnerUniformFamilyBoundaryGenerator family

/-- The selected degree-one coefficient group of the finite relative Cech shadow. -/
abbrev OwnerUniformRelativeCechCochain1 :=
  OwnerUniformFamilyZ2

/--
The selected boundary map.  A degree-zero owner-uniform generator contributes
the selected family defect to degree one.
-/
def OwnerUniformRelativeCechBoundary {atlas : TwoCoverAtlas}
    {family : SupportForkFamily atlas}
    (_cochain : OwnerUniformRelativeCechCochain0 family) :
    OwnerUniformRelativeCechCochain1 :=
  OwnerUniformFamilyDefect family

/-- The selected finite relative Cech boundary image. -/
noncomputable def OwnerUniformRelativeCechBoundaryImage
    {atlas : TwoCoverAtlas}
    (family : SupportForkFamily atlas) :
    AddSubgroup OwnerUniformRelativeCechCochain1 :=
  AddSubgroup.closure
    { value | exists cochain : OwnerUniformRelativeCechCochain0 family,
      value = OwnerUniformRelativeCechBoundary cochain }

/--
The relative Cech boundary image is exactly the Cycle 17 explicit
owner-uniform family boundary subgroup.
-/
theorem ownerUniformRelativeCechBoundaryImage_eq_familyBoundarySubgroup
    {atlas : TwoCoverAtlas}
    (family : SupportForkFamily atlas) :
    OwnerUniformRelativeCechBoundaryImage family =
      OwnerUniformFamilyBoundarySubgroup family := by
  apply le_antisymm
  · apply (AddSubgroup.closure_le
      (OwnerUniformFamilyBoundarySubgroup family)).2
    intro value hvalue
    rcases hvalue with ⟨cochain, rfl⟩
    exact AddSubgroup.subset_closure ⟨cochain.generator, rfl⟩
  · apply (AddSubgroup.closure_le
      (OwnerUniformRelativeCechBoundaryImage family)).2
    intro value hvalue
    rcases hvalue with ⟨generator, rfl⟩
    exact AddSubgroup.subset_closure ⟨⟨generator⟩, rfl⟩

/-- The selected finite relative Cech shadow quotient. -/
abbrev OwnerUniformRelativeCechShadow {atlas : TwoCoverAtlas}
    (family : SupportForkFamily atlas) :=
  OwnerUniformRelativeCechCochain1 ⧸
    OwnerUniformRelativeCechBoundaryImage family

/-- The selected owner-uniform relative Cech shadow class of a family. -/
def OwnerUniformRelativeCechClass {atlas : TwoCoverAtlas}
    (family : SupportForkFamily atlas) :
    OwnerUniformRelativeCechShadow family :=
  QuotientAddGroup.mk (OwnerUniformFamilyDefect family)

/-! ## Comparison with the selected quotient carrier -/

/--
The selected relative Cech shadow class is zero exactly when the Cycle 17
boundary-membership presentation vanishes.
-/
theorem ownerUniformRelativeCechClass_eq_zero_iff_familyClassVanishes
    {atlas : TwoCoverAtlas}
    (family : SupportForkFamily atlas) :
    OwnerUniformRelativeCechClass family = 0 ↔
      OwnerUniformFamilyClassVanishes family := by
  rw [OwnerUniformRelativeCechClass, QuotientAddGroup.eq_zero_iff,
    OwnerUniformFamilyClassVanishes,
    ownerUniformRelativeCechBoundaryImage_eq_familyBoundarySubgroup]

/--
The selected relative Cech shadow class is zero exactly when the Cycle 20
selected Conway class is zero.
-/
theorem ownerUniformRelativeCechClass_eq_zero_iff_conwayClass_zero
    {atlas : TwoCoverAtlas}
    (family : SupportForkFamily atlas) :
    OwnerUniformRelativeCechClass family = 0 ↔
      OwnerUniformConwayClass family = 0 := by
  rw [ownerUniformRelativeCechClass_eq_zero_iff_familyClassVanishes,
    ownerUniformConwayClass_eq_zero_iff_familyClassVanishes]

/--
The selected relative Cech shadow class is nonzero exactly when the Cycle 20
selected Conway class is nonzero.
-/
theorem ownerUniformRelativeCechClass_ne_zero_iff_conwayClass_nonzero
    {atlas : TwoCoverAtlas}
    (family : SupportForkFamily atlas) :
    OwnerUniformRelativeCechClass family ≠ 0 ↔
      OwnerUniformConwayClass family ≠ 0 := by
  constructor
  · intro hrelative hconway
    exact hrelative
      ((ownerUniformRelativeCechClass_eq_zero_iff_conwayClass_zero
        family).2 hconway)
  · intro hconway hrelative
    exact hconway
      ((ownerUniformRelativeCechClass_eq_zero_iff_conwayClass_zero
        family).1 hrelative)

/--
The selected relative Cech shadow class is zero exactly when an owner-uniform
span selector exists.
-/
theorem ownerUniformRelativeCechClass_eq_zero_iff_spanSelector
    {atlas : TwoCoverAtlas}
    (family : SupportForkFamily atlas) :
    OwnerUniformRelativeCechClass family = 0 ↔
      Nonempty (OwnerUniformSpanSelector family) := by
  rw [ownerUniformRelativeCechClass_eq_zero_iff_familyClassVanishes]
  exact (ownerUniformSpanSelector_nonempty_iff_familyClassVanishes family).symm

/-! ## Restricted local-zero/global-nonzero witness -/

/-- Every selected singleton subfamily has zero relative Cech shadow class. -/
theorem restrictedSingletonSubfamilies_relativeCechClass_zero
    (sub : RestrictedSingletonSubfamilyIdx) :
    OwnerUniformRelativeCechClass (restrictedSingletonSubfamily sub) = 0 := by
  exact
    (ownerUniformRelativeCechClass_eq_zero_iff_familyClassVanishes
      (restrictedSingletonSubfamily sub)).2
        (restrictedSingletonSubfamilies_ownerUniformFamilyClass_vanishes sub)

/--
The full restricted two-fork family has nonzero selected relative Cech shadow
class.
-/
theorem restrictedTwoForkFamily_relativeCechClass_nonzero :
    OwnerUniformRelativeCechClass restrictedTwoForkFamily ≠ 0 := by
  exact
    (ownerUniformRelativeCechClass_ne_zero_iff_conwayClass_nonzero
      restrictedTwoForkFamily).2
        restrictedTwoForkFamily_ownerUniformConwayClass_nonzero

/--
For the restricted two-fork witness, nonzero of the relative Cech shadow class
is equivalent to the owner-uniform span-selector obstruction.
-/
theorem restrictedTwoForkFamily_relativeCechClass_nonzero_iff_selectorObstruction :
    OwnerUniformRelativeCechClass restrictedTwoForkFamily ≠ 0 ↔
      OwnerUniformSpanSelectorObstruction restrictedTwoForkFamily := by
  rw [ownerUniformRelativeCechClass_ne_zero_iff_conwayClass_nonzero]
  exact restrictedTwoForkFamily_conwayClass_nonzero_iff_selectorObstruction

/--
The selected Cycle 21 package: the owner-uniform obstruction is represented by
a finite relative Cech `C0 -> C1` shadow; its boundary image is the explicit
owner-uniform generator subgroup; its class has the same zero/nonzero reading
as the Cycle 20 quotient carrier; singleton subfamilies are zero; and the full
restricted two-fork family is nonzero.
-/
theorem selectedOwnerUniformRelativeCechShadowPackage :
    (forall {atlas : TwoCoverAtlas}
      (family : SupportForkFamily atlas),
        OwnerUniformRelativeCechBoundaryImage family =
          OwnerUniformFamilyBoundarySubgroup family) /\
      (forall {atlas : TwoCoverAtlas}
        (family : SupportForkFamily atlas),
          OwnerUniformRelativeCechClass family = 0 ↔
            OwnerUniformConwayClass family = 0) /\
      (forall {atlas : TwoCoverAtlas}
        (family : SupportForkFamily atlas),
          OwnerUniformRelativeCechClass family = 0 ↔
            Nonempty (OwnerUniformSpanSelector family)) /\
      (forall sub : RestrictedSingletonSubfamilyIdx,
        OwnerUniformRelativeCechClass
          (restrictedSingletonSubfamily sub) = 0) /\
      OwnerUniformRelativeCechClass restrictedTwoForkFamily ≠ 0 /\
      (OwnerUniformRelativeCechClass restrictedTwoForkFamily ≠ 0 ↔
        OwnerUniformSpanSelectorObstruction restrictedTwoForkFamily) := by
  exact
    ⟨(by
        intro atlas family
        exact ownerUniformRelativeCechBoundaryImage_eq_familyBoundarySubgroup
          family),
      (by
        intro atlas family
        exact ownerUniformRelativeCechClass_eq_zero_iff_conwayClass_zero
          family),
      (by
        intro atlas family
        exact ownerUniformRelativeCechClass_eq_zero_iff_spanSelector family),
      restrictedSingletonSubfamilies_relativeCechClass_zero,
      restrictedTwoForkFamily_relativeCechClass_nonzero,
      restrictedTwoForkFamily_relativeCechClass_nonzero_iff_selectorObstruction⟩

end ConwayTwoTopology
end SFT
end Formal.AG.Research
