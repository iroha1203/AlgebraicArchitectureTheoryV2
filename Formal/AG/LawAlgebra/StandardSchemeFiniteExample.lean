import Formal.AG.LawAlgebra.StandardScheme
import Formal.AG.LawAlgebra.RingedSiteFiniteExample
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction

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

end AAT.AG.LawAlgebra.FiniteExamples.StandardSchemeReading

namespace AAT.AG.LawAlgebra.FiniteExamples.StandardArchitectureScheme

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open scoped AlgebraicGeometry

open RingedSite.FiniteModel
open AAT.AG.LawAlgebra.FiniteExamples.StandardSchemeReading

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

/-!
### Finite valid and invalid atlas witnesses

The existing sign-separated quotient makes the base raw algebra nontrivial.  Invertibility of
the canonical sheafification component transfers this witness to the section ring, so the base
Spec has an actual point.  The identity atlas covers it, while an empty-index atlas cannot.
-/

/-- The finite raw algebra at the base context is nontrivial. -/
theorem rawBaseNontrivial : Nontrivial (rawSystem.rawAlgebra base) := by
  refine ⟨⟨
    (rawSystem.relationFamily base).quotientMap (MvPolynomial.X ()),
    (rawSystem.relationFamily base).quotientMap (-(MvPolynomial.X ())),
    ?_⟩⟩
  exact RawPresheaf.quotient_X_ne_neg_X

/-- The canonical component on the finite base context is injective. -/
theorem canonicalBaseInjective :
    Function.Injective
      (rawSystem.toRingedSite.canonical.app (op base)).right := by
  letI := canonicalComponentIsIso base
  intro x y h
  have hx := congrArg (fun q => q.right x)
    (IsIso.hom_inv_id (rawSystem.toRingedSite.canonical.app (op base)))
  have hy := congrArg (fun q => q.right y)
    (IsIso.hom_inv_id (rawSystem.toRingedSite.canonical.app (op base)))
  calc
    x = (inv (rawSystem.toRingedSite.canonical.app (op base))).right
        ((rawSystem.toRingedSite.canonical.app (op base)).right x) := by
      simpa only [Under.comp_right, Under.id_right, CommRingCat.comp_apply,
        CommRingCat.id_apply] using hx.symm
    _ = (inv (rawSystem.toRingedSite.canonical.app (op base))).right
        ((rawSystem.toRingedSite.canonical.app (op base)).right y) := by rw [h]
    _ = y := by
      simpa only [Under.comp_right, Under.id_right, CommRingCat.comp_apply,
        CommRingCat.id_apply] using hy

/-- The canonical finite base Spec has an actual point. -/
theorem baseSpec_nonempty :
    Nonempty (architectureChartSpec rawSystem base) := by
  letI := canonicalComponentIsIso base
  letI : Nontrivial (rawSystem.rawAlgebra base) := rawBaseNontrivial
  letI : Nontrivial ((rawSystem.toPresheaf.obj (op base)).right) :=
    Function.Injective.nontrivial (rawSystem.toPresheafObjectIso base).injective
  letI : Nontrivial ((rawSystem.toRingedSite.raw.obj (op base)).right) := by
    rw [RawAmbientRestrictionSystem.toRingedSite_raw]
    infer_instance
  letI : Nontrivial (SheafifiedSectionRing rawSystem base) :=
    Function.Injective.nontrivial canonicalBaseInjective
  change Nonempty (AlgebraicGeometry.Spec
    (SheafifiedSectionRing rawSystem base))
  infer_instance

/-- A one-chart finite atlas carried by the identity chart. -/
noncomputable def identityAtlas :
    ArchitectureAffineAtlas rawSystem
      (architectureChartSpec rawSystem base)
      (AATReadingDecoration.ofContext rawSystem base) where
  Index := PUnit
  chart _ := ArchitectureAffineChart.identity rawSystem base

/-- The one-chart finite identity atlas is valid. -/
theorem identityAtlas_valid :
    IsArchitectureAffineAtlas rawSystem identityAtlas := by
  constructor
  · intro i
    exact ArchitectureAffineChart.identity_isArchitectureAffineChart rawSystem base
  · intro x
    exact ⟨PUnit.unit, x, rfl⟩

/-!
### Finite positive and negative overlap-presentation witnesses

The identity atlas supplies the positive witness.  For the negative witness, a second chart
uses the existing identity-transport Scheme map on the left finite context.  Its selected
context restriction is the actual sign-changing map, so the mixed comparison's first
projection fails on the selected coordinate.
-/

local instance identitySheafifiedMap_isIso :
    IsIso identitySheafifiedMap := by
  letI := canonicalComponentIsIso base
  letI := canonicalComponentIsIso RawPresheaf.left
  haveI : IsIso
      (inv (rawSystem.toRingedSite.canonical.app (op base))).right := by
    infer_instance
  haveI : IsIso
      (rawSystem.toRingedSite.canonical.app (op RawPresheaf.left)).right := by
    infer_instance
  haveI : IsIso rawIdentityToLeft := by
    dsimp [rawIdentityToLeft]
    infer_instance
  haveI : IsIso
      (rawIdentityToLeft ≫
        (rawSystem.toRingedSite.canonical.app (op RawPresheaf.left)).right) := by
    infer_instance
  exact inferInstanceAs (IsIso
    ((inv (rawSystem.toRingedSite.canonical.app (op base))).right ≫
      (rawIdentityToLeft ≫
        (rawSystem.toRingedSite.canonical.app (op RawPresheaf.left)).right)))

/-- Comparison of the identity atlas with the pullback of the identity chart map. -/
noncomputable def identityAtlasPresentation :
    ArchitectureOverlapPresentation rawSystem identityAtlas where
  comparison i j := by
    cases i
    cases j
    exact architectureChartIso rawSystem
        (identityAtlas.selfPairContextIso rawSystem PUnit.unit) ≪≫
      (IsPullback.of_id_fst
        (f := 𝟙 (architectureChartSpec rawSystem base))).isoPullback

/-- The identity-atlas comparison satisfies both actual projection equations. -/
theorem identityAtlasPresentation_valid :
    IsArchitectureOverlapPresentation rawSystem identityAtlasPresentation := by
  constructor
  · intro i j
    cases i
    cases j
    change
      (architectureChartIso rawSystem
          (identityAtlas.selfPairContextIso rawSystem PUnit.unit)).hom ≫
        ((IsPullback.of_id_fst
          (f := 𝟙 (architectureChartSpec rawSystem base))).isoPullback).hom ≫
        pullback.fst (𝟙 (architectureChartSpec rawSystem base))
          (𝟙 (architectureChartSpec rawSystem base)) = _
    rw [IsPullback.isoPullback_hom_fst]
    change architectureChartRestriction rawSystem
      (identityAtlas.pairToLeft rawSystem PUnit.unit PUnit.unit) ≫ 𝟙 _ = _
    rw [Category.comp_id]
  · intro i j
    cases i
    cases j
    change
      (architectureChartIso rawSystem
          (identityAtlas.selfPairContextIso rawSystem PUnit.unit)).hom ≫
        ((IsPullback.of_id_fst
          (f := 𝟙 (architectureChartSpec rawSystem base))).isoPullback).hom ≫
        pullback.snd (𝟙 (architectureChartSpec rawSystem base))
          (𝟙 (architectureChartSpec rawSystem base)) = _
    rw [IsPullback.isoPullback_hom_snd]
    change architectureChartRestriction rawSystem
      (identityAtlas.pairToLeft rawSystem PUnit.unit PUnit.unit) ≫ 𝟙 _ = _
    rw [Category.comp_id]
    exact congrArg (architectureChartRestriction rawSystem) (Subsingleton.elim _ _)

/-- Two charts with the identity base chart and the finite interpretation-broken left chart. -/
noncomputable def mixedAtlas :
    ArchitectureAffineAtlas rawSystem
      (architectureChartSpec rawSystem base)
      (AATReadingDecoration.ofContext rawSystem base) where
  Index := Bool
  chart
    | false => ArchitectureAffineChart.identity rawSystem base
    | true => interpretationBrokenChart

/-- The selected `false,true` pair context is isomorphic to the left chart context. -/
noncomputable def mixedAtlasFalseTruePairIso :
    mixedAtlas.pairContext rawSystem false true ≅ RawPresheaf.left where
  hom := mixedAtlas.pairToRight rawSystem false true
  inv := homOfLE (site.overlap.lift
    (leOfHom (mixedAtlas.chart false).contextHom)
    (leOfHom (mixedAtlas.chart true).contextHom)
    (leOfHom RawPresheaf.leftToBase)
    (site.contextPreorder.refl _))
  hom_inv_id := Subsingleton.elim _ _
  inv_hom_id := Subsingleton.elim _ _

/-- The selected `true,false` pair context is isomorphic to the left chart context. -/
noncomputable def mixedAtlasTrueFalsePairIso :
    mixedAtlas.pairContext rawSystem true false ≅ RawPresheaf.left where
  hom := mixedAtlas.pairToLeft rawSystem true false
  inv := homOfLE (site.overlap.lift
    (leOfHom (mixedAtlas.chart true).contextHom)
    (leOfHom (mixedAtlas.chart false).contextHom)
    (site.contextPreorder.refl _)
    (leOfHom RawPresheaf.leftToBase))
  hom_inv_id := Subsingleton.elim _ _
  inv_hom_id := Subsingleton.elim _ _

/-- The square of two copies of the broken chart map is a pullback square. -/
theorem brokenMapSelf_isPullback :
    IsPullback
      (𝟙 (architectureChartSpec rawSystem RawPresheaf.left))
      (𝟙 (architectureChartSpec rawSystem RawPresheaf.left))
      (AlgebraicGeometry.Spec.map identitySheafifiedMap)
      (AlgebraicGeometry.Spec.map identitySheafifiedMap) := by
  apply IsPullback.of_horiz_isIso
  exact ⟨by simp⟩

/-- The identity map and broken map form the standard pullback square. -/
theorem mixedFalseTrue_isPullback :
    IsPullback
      (AlgebraicGeometry.Spec.map identitySheafifiedMap)
      (𝟙 (architectureChartSpec rawSystem RawPresheaf.left))
      (𝟙 (architectureChartSpec rawSystem base))
      (AlgebraicGeometry.Spec.map identitySheafifiedMap) :=
  IsPullback.of_id_snd

/-- Pullback comparison data for all four pairs of the mixed atlas. -/
noncomputable def mixedAtlasPresentation :
    ArchitectureOverlapPresentation rawSystem mixedAtlas where
  comparison i j := by
    cases i <;> cases j
    · exact architectureChartIso rawSystem
          (mixedAtlas.selfPairContextIso rawSystem false) ≪≫
        (IsPullback.of_id_fst
          (f := 𝟙 (architectureChartSpec rawSystem base))).isoPullback
    · exact architectureChartIso rawSystem mixedAtlasFalseTruePairIso ≪≫
        mixedFalseTrue_isPullback.isoPullback
    · exact architectureChartIso rawSystem mixedAtlasTrueFalsePairIso ≪≫
        (IsPullback.of_id_fst
          (f := AlgebraicGeometry.Spec.map identitySheafifiedMap)).isoPullback
    · exact architectureChartIso rawSystem
          (mixedAtlas.selfPairContextIso rawSystem true) ≪≫
        brokenMapSelf_isPullback.isoPullback

/-- The mixed comparison fails the selected left-projection equation. -/
theorem mixedAtlasPresentation_not_valid :
    ¬ IsArchitectureOverlapPresentation rawSystem mixedAtlasPresentation := by
  intro h
  have hf := h.comparison_fst false true
  change
    (architectureChartIso rawSystem mixedAtlasFalseTruePairIso).hom ≫
        mixedFalseTrue_isPullback.isoPullback.hom ≫
        pullback.fst (𝟙 (architectureChartSpec rawSystem base))
          (AlgebraicGeometry.Spec.map identitySheafifiedMap) =
      architectureChartRestriction rawSystem
        (mixedAtlas.pairToLeft rawSystem false true) at hf
  rw [IsPullback.isoPullback_hom_fst mixedFalseTrue_isPullback] at hf
  rw [architectureChartIso_hom] at hf
  have hctx :
      mixedAtlas.pairToLeft rawSystem false true =
        mixedAtlas.pairToRight rawSystem false true ≫
          RawPresheaf.leftToBase :=
    Subsingleton.elim _ _
  rw [hctx, architectureChartRestriction_comp] at hf
  have hscheme :
      AlgebraicGeometry.Spec.map identitySheafifiedMap =
        architectureChartRestriction rawSystem RawPresheaf.leftToBase := by
    rw [← cancel_epi
      (architectureChartIso rawSystem mixedAtlasFalseTruePairIso).hom]
    simpa only [architectureChartIso_hom] using hf
  have hring :
      identitySheafifiedMap =
        sheafifiedRestriction rawSystem RawPresheaf.leftToBase := by
    apply AlgebraicGeometry.Spec.map_injective
    simpa only [architectureChartRestriction_eq_SpecMap] using hscheme
  apply sheafifiedLeftToBaseCoordinate_ne
  calc
    sheafifiedRestriction rawSystem RawPresheaf.leftToBase baseCoordinateSection =
        identitySheafifiedMap baseCoordinateSection := by
      exact congrArg (fun q => q baseCoordinateSection) hring.symm
    _ = leftCoordinateSection := identitySheafifiedMap_coordinate

/-- The empty-index finite atlas. -/
noncomputable def uncoveredAtlas :
    ArchitectureAffineAtlas rawSystem
      (architectureChartSpec rawSystem base)
      (AATReadingDecoration.ofContext rawSystem base) where
  Index := Empty
  chart := Empty.elim

/-- The empty-index finite atlas does not cover the nonempty base Spec. -/
theorem uncoveredAtlas_not_valid :
    ¬ IsArchitectureAffineAtlas rawSystem uncoveredAtlas := by
  intro h
  let x := Classical.choice baseSpec_nonempty
  obtain ⟨i, _, _⟩ := h.covers x
  exact i.elim

end AAT.AG.LawAlgebra.FiniteExamples.StandardArchitectureScheme
