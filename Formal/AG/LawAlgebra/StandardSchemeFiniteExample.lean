import Formal.AG.LawAlgebra.StandardScheme
import Formal.AG.LawAlgebra.RingedSiteFiniteExample

/-!
# Finite reading-preservation counterexample

This module supplies the negative member of the instance pair required for the
new `AATReadingDecoration.Preserves` predicate.  It uses the existing finite
raw system whose left-to-base restriction sends the selected coordinate to its
negative.  Since the selected topology is bottom, every raw presheaf is already
a sheaf and the canonical sheafification components are isomorphisms.

The source interpretation is transported with the identity quotient map,
whereas the Scheme transition uses the actual sign-changing restriction.  The
selected coordinate distinguishes these maps, yielding a concrete failure of
preservation without accepting an inequality or compatibility failure as
input.  The richer two-chart and negative chart examples remain separate later
reference-model work.
-/

noncomputable section

namespace AAT.AG.LawAlgebra.FiniteExamples.StandardSchemeReading

open CategoryTheory Opposite
open AlgebraicGeometry
open scoped AlgebraicGeometry

open RingedSite.FiniteModel

/-- Bottom-topology sheafification has an invertible canonical component at every context. -/
theorem canonicalComponentIsIso (W : site.category) :
    IsIso (rawSystem.toRingedSite.canonical.app (op W)) := by
  have hsheaf : Presheaf.IsSheaf site.topology rawSystem.toPresheaf := by
    rw [site_topology_eq_bot]
    exact Presheaf.isSheaf_bot _
  haveI : IsIso (CategoryTheory.toSheafify site.topology rawSystem.toPresheaf) :=
    CategoryTheory.isIso_toSheafify (J := site.topology) hsheaf
  change IsIso ((CategoryTheory.toSheafify site.topology rawSystem.toPresheaf).app (op W))
  infer_instance

/-- The identity ring homomorphism between the definitionally equal finite raw quotients. -/
def rawIdentityToLeft :
    CommRingCat.of (rawSystem.rawAlgebra base) ⟶
      CommRingCat.of (rawSystem.rawAlgebra RawPresheaf.left) :=
  CommRingCat.ofHom (RingHom.id _)

/-- The identity quotient map transported between the base and left sheafified section rings. -/
noncomputable def identitySheafifiedMap :
    SheafifiedSectionRing rawSystem base ⟶
      SheafifiedSectionRing rawSystem RawPresheaf.left := by
  letI := canonicalComponentIsIso base
  exact (inv (rawSystem.toRingedSite.canonical.app (op base))).right ≫
    rawIdentityToLeft ≫
    (rawSystem.toRingedSite.canonical.app (op RawPresheaf.left)).right

/-- The selected coordinate in the sheafified section ring of the base context. -/
noncomputable def baseCoordinateSection :
    SheafifiedSectionRing rawSystem base :=
  (rawSystem.toRingedSite.canonical.app (op base)).right
    ((rawSystem.relationFamily base).quotientMap (MvPolynomial.X ()))

/-- The selected coordinate in the sheafified section ring of the left context. -/
noncomputable def leftCoordinateSection :
    SheafifiedSectionRing rawSystem RawPresheaf.left :=
  (rawSystem.toRingedSite.canonical.app (op RawPresheaf.left)).right
    ((rawSystem.relationFamily RawPresheaf.left).quotientMap (MvPolynomial.X ()))

/-- The transported identity quotient map fixes the selected coordinate. -/
theorem identitySheafifiedMap_coordinate :
    identitySheafifiedMap baseCoordinateSection = leftCoordinateSection := by
  letI := canonicalComponentIsIso base
  let x := (rawSystem.relationFamily base).quotientMap (MvPolynomial.X ())
  have hc := congrArg (fun q => q.right x)
    (IsIso.hom_inv_id (rawSystem.toRingedSite.canonical.app (op base)))
  change
    (rawSystem.toRingedSite.canonical.app (op RawPresheaf.left)).right
        (rawIdentityToLeft
          ((inv (rawSystem.toRingedSite.canonical.app (op base))).right
            ((rawSystem.toRingedSite.canonical.app (op base)).right x))) =
      (rawSystem.toRingedSite.canonical.app (op RawPresheaf.left)).right x
  rw [show
    (inv (rawSystem.toRingedSite.canonical.app (op base))).right
        ((rawSystem.toRingedSite.canonical.app (op base)).right x) = x by
      simpa only [Under.comp_right, Under.id_right, CommRingCat.comp_apply,
        CommRingCat.id_apply] using hc]
  rfl

/-- The canonical component on the left context is injective. -/
theorem canonicalLeftInjective :
    Function.Injective
      (rawSystem.toRingedSite.canonical.app (op RawPresheaf.left)).right := by
  letI := canonicalComponentIsIso RawPresheaf.left
  intro x y h
  have hx := congrArg (fun q => q.right x)
    (IsIso.hom_inv_id
      (rawSystem.toRingedSite.canonical.app (op RawPresheaf.left)))
  have hy := congrArg (fun q => q.right y)
    (IsIso.hom_inv_id
      (rawSystem.toRingedSite.canonical.app (op RawPresheaf.left)))
  calc
    x = (inv (rawSystem.toRingedSite.canonical.app (op RawPresheaf.left))).right
        ((rawSystem.toRingedSite.canonical.app (op RawPresheaf.left)).right x) := by
      simpa only [Under.comp_right, Under.id_right, CommRingCat.comp_apply,
        CommRingCat.id_apply] using hx.symm
    _ = (inv (rawSystem.toRingedSite.canonical.app (op RawPresheaf.left))).right
        ((rawSystem.toRingedSite.canonical.app (op RawPresheaf.left)).right y) := by rw [h]
    _ = y := by
      simpa only [Under.comp_right, Under.id_right, CommRingCat.comp_apply,
        CommRingCat.id_apply] using hy

/-- The actual sheafified left-to-base restriction changes the selected coordinate. -/
theorem sheafifiedLeftToBaseCoordinate_ne :
    sheafifiedRestriction rawSystem RawPresheaf.leftToBase baseCoordinateSection ≠
      leftCoordinateSection := by
  intro h
  apply raw_leftToBase_quotientDesc_X_ne_X
  apply canonicalLeftInjective
  have hn := rawSystem.toRingedSite.canonical.naturality RawPresheaf.leftToBase.op
  have ha := congrArg
    (fun q => q.right
      ((rawSystem.relationFamily base).quotientMap (MvPolynomial.X ()))) hn
  calc
    (rawSystem.toRingedSite.canonical.app (op RawPresheaf.left)).right
        ((rawSystem.restrictionStable RawPresheaf.leftToBase).quotientDesc
          ((rawSystem.relationFamily base).quotientMap (MvPolynomial.X ()))) =
      sheafifiedRestriction rawSystem RawPresheaf.leftToBase baseCoordinateSection := by
        simpa only [CommRingCat.comp_apply, RawAmbientRestrictionSystem.toRingedSite_raw,
          baseCoordinateSection, sheafifiedRestriction] using ha
    _ = leftCoordinateSection := h
    _ = (rawSystem.toRingedSite.canonical.app (op RawPresheaf.left)).right
        ((rawSystem.relationFamily RawPresheaf.left).quotientMap
          (MvPolynomial.X ())) := rfl

/-- A source decoration using the identity quotient map instead of the actual restriction. -/
noncomputable def negativeSourceDecoration :
    AATReadingDecoration rawSystem
      (architectureChartSpec rawSystem RawPresheaf.left) where
  context := base
  interpretation := identitySheafifiedMap ≫
    (AlgebraicGeometry.Scheme.ΓSpecIso
      (SheafifiedSectionRing rawSystem RawPresheaf.left)).inv

/-- The negative source decoration disagrees with the actual transition on the selected coordinate. -/
theorem negativeSourceDecoration_coordinate_ne :
    negativeSourceDecoration.interpretation baseCoordinateSection ≠
      ((AATReadingDecoration.ofContext rawSystem base).interpretation ≫
        (architectureChartRestriction rawSystem RawPresheaf.leftToBase).appTop)
        baseCoordinateSection := by
  rw [show negativeSourceDecoration.interpretation baseCoordinateSection =
      (AlgebraicGeometry.Scheme.ΓSpecIso
        (SheafifiedSectionRing rawSystem RawPresheaf.left)).inv
        leftCoordinateSection by
    change
      (AlgebraicGeometry.Scheme.ΓSpecIso
        (SheafifiedSectionRing rawSystem RawPresheaf.left)).inv
          (identitySheafifiedMap baseCoordinateSection) =
        (AlgebraicGeometry.Scheme.ΓSpecIso
          (SheafifiedSectionRing rawSystem RawPresheaf.left)).inv
            leftCoordinateSection
    rw [identitySheafifiedMap_coordinate]]
  intro h
  apply sheafifiedLeftToBaseCoordinate_ne
  have hn := AlgebraicGeometry.Scheme.ΓSpecIso_inv_naturality
    (sheafifiedRestriction rawSystem RawPresheaf.leftToBase)
  have ha := congrArg (fun q => q baseCoordinateSection) hn
  have h' :
      (AlgebraicGeometry.Scheme.ΓSpecIso
        (SheafifiedSectionRing rawSystem RawPresheaf.left)).inv
          leftCoordinateSection =
        (AlgebraicGeometry.Scheme.ΓSpecIso
          (SheafifiedSectionRing rawSystem RawPresheaf.left)).inv
          (sheafifiedRestriction rawSystem RawPresheaf.leftToBase
            baseCoordinateSection) := by
    exact h.trans (by simpa only [CommRingCat.comp_apply] using ha.symm)
  have hh := congrArg
    (AlgebraicGeometry.Scheme.ΓSpecIso
      (SheafifiedSectionRing rawSystem RawPresheaf.left)).hom h'
  simpa using hh.symm

/-- The concrete finite source decoration is not preserved by the actual Spec transition. -/
theorem preserves_negative_example :
    ¬ negativeSourceDecoration.Preserves rawSystem
      (architectureChartRestriction rawSystem RawPresheaf.leftToBase)
      (AATReadingDecoration.ofContext rawSystem base) := by
  rintro ⟨h, hh⟩
  have hctx : h = 𝟙 base := Subsingleton.elim _ _
  subst h
  apply negativeSourceDecoration_coordinate_ne
  have ha := congrArg (fun q => q baseCoordinateSection) hh
  have hid :
      sheafifiedRestriction rawSystem (𝟙 base) baseCoordinateSection =
        baseCoordinateSection := by
    rw [sheafifiedRestriction_id]
    rfl
  change
    negativeSourceDecoration.interpretation
        (sheafifiedRestriction rawSystem (𝟙 base) baseCoordinateSection) =
      ((AATReadingDecoration.ofContext rawSystem base).interpretation ≫
        (architectureChartRestriction rawSystem RawPresheaf.leftToBase).appTop)
          baseCoordinateSection at ha
  rwa [hid] at ha

/-!
### Finite invalid-chart witness

The selected chart context uses the actual sign-changing context restriction, while its Scheme
map is induced by the identity transport between the definitionally equal quotient rings.  The
selected coordinate therefore refutes the chart interpretation equation without accepting an
inequality or failed validity proof as input.
-/

/-- A chart whose selected context restriction disagrees with its actual Spec map. -/
noncomputable def interpretationBrokenChart :
    ArchitectureAffineChart rawSystem
      (architectureChartSpec rawSystem base)
      (AATReadingDecoration.ofContext rawSystem base) where
  context := RawPresheaf.left
  contextHom := RawPresheaf.leftToBase
  map := AlgebraicGeometry.Spec.map identitySheafifiedMap

/-- The broken chart's actual interpretation equation fails on the selected coordinate. -/
theorem interpretationBrokenChart_equation_ne :
    sheafifiedRestriction rawSystem interpretationBrokenChart.contextHom ≠
      (AATReadingDecoration.ofContext rawSystem base).interpretation ≫
        interpretationBrokenChart.map.appTop ≫
        (AlgebraicGeometry.Scheme.ΓSpecIso
          (SheafifiedSectionRing rawSystem
            interpretationBrokenChart.context)).hom := by
  intro h
  apply sheafifiedLeftToBaseCoordinate_ne
  have ha := congrArg (fun q => q baseCoordinateSection) h
  calc
    sheafifiedRestriction rawSystem RawPresheaf.leftToBase baseCoordinateSection =
        ((AATReadingDecoration.ofContext rawSystem base).interpretation ≫
          (AlgebraicGeometry.Spec.map identitySheafifiedMap).appTop ≫
          (AlgebraicGeometry.Scheme.ΓSpecIso
            (SheafifiedSectionRing rawSystem RawPresheaf.left)).hom)
            baseCoordinateSection := by simpa [interpretationBrokenChart] using ha
    _ = identitySheafifiedMap baseCoordinateSection := by
      have hm :
          (AATReadingDecoration.ofContext rawSystem base).interpretation ≫
              (AlgebraicGeometry.Spec.map identitySheafifiedMap).appTop ≫
              (AlgebraicGeometry.Scheme.ΓSpecIso
                (SheafifiedSectionRing rawSystem RawPresheaf.left)).hom =
            identitySheafifiedMap := by
        change
          (AlgebraicGeometry.Scheme.ΓSpecIso
                (SheafifiedSectionRing rawSystem base)).inv ≫
              (AlgebraicGeometry.Spec.map identitySheafifiedMap).appTop ≫
              (AlgebraicGeometry.Scheme.ΓSpecIso
                (SheafifiedSectionRing rawSystem RawPresheaf.left)).hom =
            identitySheafifiedMap
        rw [← Category.assoc,
          ← AlgebraicGeometry.Scheme.ΓSpecIso_inv_naturality]
        simp
      exact congrArg (fun q => q baseCoordinateSection) hm
    _ = leftCoordinateSection := identitySheafifiedMap_coordinate

/-- The finite broken chart does not satisfy actual affine-chart validity. -/
theorem interpretationBrokenChart_not_valid :
    ¬ IsArchitectureAffineChart rawSystem interpretationBrokenChart := by
  intro h
  exact interpretationBrokenChart_equation_ne h.interpretation_compatible

end AAT.AG.LawAlgebra.FiniteExamples.StandardSchemeReading
