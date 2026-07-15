import Formal.AG.LawAlgebra.StandardScheme
import Formal.AG.LawAlgebra.AffineChart
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
### Finite canonical sheafification and coordinate transport

The right context completes the selected two-patch context pair.  The finite bottom topology
makes every canonical sheafification component invertible, so the base presentation and its
representability equivalence are constructed from the canonical unit alone.  Naturality of that
same unit transports the selected coordinate through the actual left-to-base restriction.
-/

/-- The selected right patch as an object of the finite ringed site. -/
def rightContext : site.category :=
  Site.ContextCategoryObject.of site.contextPreorder
    (AAT.AG.FiniteModel.twoPatchContext
      AAT.AG.FiniteModel.TwoPatchContextIndex.right)

/-- The selected right patch includes into the base context. -/
def rightToBase : rightContext ⟶ base :=
  CategoryTheory.homOfLE
    (AAT.AG.FiniteModel.twoPatchContextLe_sound
      (i := AAT.AG.FiniteModel.TwoPatchContextIndex.right)
      (j := AAT.AG.FiniteModel.TwoPatchContextIndex.base)
      (by simp [AAT.AG.FiniteModel.twoPatchContextIndexLe]))

/-- The selected left and right patches are distinct context objects. -/
theorem leftContext_ne_rightContext :
    RawPresheaf.left ≠ rightContext := by
  intro h
  have hctx := congrArg Site.ContextCategoryObject.ctx h
  have heq := congrArg
    (fun W : Site.ArchitectureContext AAT.AG.FiniteModel.corePackage.object =>
      (⟨W.Extension, W.extension⟩ : Sigma fun T : Type => T)) hctx
  injection heq with _ hindex
  exact AAT.AG.FiniteModel.TwoPatchContextIndex.noConfusion hindex

/-- Bottom-topology sheafification is objectwise invertible in the finite model. -/
theorem canonical_component_isIso (W : site.category) :
    IsIso (rawSystem.toRingedSite.canonical.app (op W)) :=
  canonicalComponentIsIso W

/-- The finite base presentation whose only material condition is the canonical unit. -/
noncomputable def baseSheafifiedPresentation :
    AffineChart.AffineAATChart.SheafifiedChartPresentation
      rawSystem base where
  canonical_isIso := canonical_component_isIso base

/-- The inverse comparison of the finite base presentation is the canonical unit itself. -/
@[simp] theorem basePresentation_comparison_symm_toAlgHom :
    baseSheafifiedPresentation.comparison.symm.toAlgHom =
      sheafificationUnitAlgHom rawSystem base :=
  AffineChart.AffineAATChart.SheafifiedChartPresentation.comparison_symm_toAlgHom
    baseSheafifiedPresentation

/-- Configurations on the finite base are represented by its sheafified section ring. -/
noncomputable def baseSheafifiedRepresentability
    (R : Type w) [CommRing R] [Algebra Int R] :
    rawSystem.LocalConfiguration base R ≃
      (SheafifiedSectionRing rawSystem base →ₐ[Int] R) :=
  AffineChart.AffineAATChart.sheafifiedChartRepresentability
    baseSheafifiedPresentation R

/-- Forward evaluation of the finite base representability equivalence. -/
@[simp] theorem baseSheafifiedRepresentability_apply
    (R : Type w) [CommRing R] [Algebra Int R]
    (a : rawSystem.LocalConfiguration base R) :
    baseSheafifiedRepresentability R a =
      (rawSystem.localConfigurationRepresentability base R a).comp
        baseSheafifiedPresentation.comparison.toAlgHom :=
  AffineChart.AffineAATChart.sheafifiedChartRepresentability_apply
    baseSheafifiedPresentation R a

/-- The finite base representability equivalence is natural in the target algebra. -/
theorem baseSheafifiedRepresentability_natural
    {R : Type w} {T : Type x}
    [CommRing R] [Algebra Int R] [CommRing T] [Algebra Int T]
    (g : R →ₐ[Int] T) (a : rawSystem.LocalConfiguration base R) :
    baseSheafifiedRepresentability T (a.map g) =
      g.comp (baseSheafifiedRepresentability R a) :=
  AffineChart.AffineAATChart.sheafifiedChartRepresentability_natural
    baseSheafifiedPresentation g a

/-- The selected coefficient ring is nontrivial. -/
theorem coefficient_nontrivial : Nontrivial Int :=
  coefficientNontrivial

/-- The selected coordinate in the sheafified section ring of the base context. -/
noncomputable def baseCoordinateSection :
    SheafifiedSectionRing rawSystem base :=
  StandardSchemeReading.baseCoordinateSection

/-- The selected coordinate in the sheafified section ring of the left context. -/
noncomputable def leftCoordinateSection :
    SheafifiedSectionRing rawSystem RawPresheaf.left :=
  StandardSchemeReading.leftCoordinateSection

/-- The finite canonical unit on the left context is injective. -/
theorem canonical_left_injective :
    Function.Injective
      (rawSystem.toRingedSite.canonical.app (op RawPresheaf.left)).right :=
  canonicalLeftInjective

/-- The actual sheafified left-to-base restriction negates the selected coordinate. -/
theorem sheafified_leftToBase_coordinate :
    sheafifiedRestriction rawSystem RawPresheaf.leftToBase
        baseCoordinateSection =
      -leftCoordinateSection := by
  have hn := rawSystem.toRingedSite.canonical.naturality RawPresheaf.leftToBase.op
  have ha := congrArg
    (fun q => q.right
      ((rawSystem.relationFamily base).quotientMap (MvPolynomial.X ()))) hn
  calc
    sheafifiedRestriction rawSystem RawPresheaf.leftToBase baseCoordinateSection =
        (rawSystem.toRingedSite.canonical.app (op RawPresheaf.left)).right
          ((rawSystem.restrictionStable RawPresheaf.leftToBase).quotientDesc
            ((rawSystem.relationFamily base).quotientMap
              (MvPolynomial.X ()))) := by
          simpa only [CommRingCat.comp_apply,
            RawAmbientRestrictionSystem.toRingedSite_raw,
            baseCoordinateSection, StandardSchemeReading.baseCoordinateSection,
            sheafifiedRestriction] using ha.symm
    _ = (rawSystem.toRingedSite.canonical.app (op RawPresheaf.left)).right
          ((rawSystem.relationFamily RawPresheaf.left).quotientMap
            (-(MvPolynomial.X ()))) := by
          congr 1
          exact RawPresheaf.leftToBase_quotientDesc_X
    _ = -leftCoordinateSection := by
          simp only [map_neg, leftCoordinateSection,
            StandardSchemeReading.leftCoordinateSection]

/-- The actual sheafified left-to-base restriction changes the selected coordinate. -/
theorem sheafified_leftToBase_changes_coordinate :
    sheafifiedRestriction rawSystem RawPresheaf.leftToBase
        baseCoordinateSection ≠
      leftCoordinateSection := by
  simpa only [baseCoordinateSection, leftCoordinateSection] using
    sheafifiedLeftToBaseCoordinate_ne

/-- The actual Spec transition changes the selected coordinate on global sections. -/
theorem left_transition_changes_coordinate :
    ((AlgebraicGeometry.Scheme.ΓSpecIso
          (SheafifiedSectionRing rawSystem base)).inv ≫
        (architectureChartRestriction rawSystem
          RawPresheaf.leftToBase).appTop ≫
        (AlgebraicGeometry.Scheme.ΓSpecIso
          (SheafifiedSectionRing rawSystem RawPresheaf.left)).hom)
        baseCoordinateSection ≠
      leftCoordinateSection := by
  intro h
  apply sheafified_leftToBase_changes_coordinate
  have hm :
      (AlgebraicGeometry.Scheme.ΓSpecIso
          (SheafifiedSectionRing rawSystem base)).inv ≫
        (architectureChartRestriction rawSystem
          RawPresheaf.leftToBase).appTop ≫
        (AlgebraicGeometry.Scheme.ΓSpecIso
          (SheafifiedSectionRing rawSystem RawPresheaf.left)).hom =
      sheafifiedRestriction rawSystem RawPresheaf.leftToBase := by
    rw [architectureChartRestriction_appTop]
    exact (AlgebraicGeometry.Scheme.ΓSpecIso
      (SheafifiedSectionRing rawSystem base)).inv_hom_id_assoc _
  have heval := congrArg (fun q => q baseCoordinateSection) hm
  exact heval.symm.trans h

/-!
### Positive finite two-chart model

Every finite raw restriction is a sign automorphism: applying the same gauge product twice is
the identity.  The canonical-unit naturality square transports this raw isomorphism to the
sheafified restriction and then to its actual Spec transition.  These generated isomorphisms
produce both valid charts, pointwise coverage, and every pair pullback comparison.
-/

private theorem coordinateRestriction_comp_self
    {X Y : site.category} (f : X ⟶ Y) :
    (RawPresheaf.coordinateRestriction f).polynomialMap.comp
        (RawPresheaf.coordinateRestriction f).polynomialMap =
      RingHom.id _ := by
  have hsign :
      (RawPresheaf.gauge X * RawPresheaf.gauge Y) *
          (RawPresheaf.gauge X * RawPresheaf.gauge Y) = 1 := by
    calc
      (RawPresheaf.gauge X * RawPresheaf.gauge Y) *
          (RawPresheaf.gauge X * RawPresheaf.gauge Y) =
          (RawPresheaf.gauge X * RawPresheaf.gauge X) *
            (RawPresheaf.gauge Y * RawPresheaf.gauge Y) := by ring
      _ = 1 := by
        rw [RawPresheaf.gauge_sq, RawPresheaf.gauge_sq, one_mul]
  apply MvPolynomial.ringHom_ext
  · intro a
    simp [TypedCoordinateRestriction.polynomialMap]
  · intro i
    cases i
    change
      (RawPresheaf.coordinateRestriction f).polynomialMap
          ((RawPresheaf.coordinateRestriction f).polynomialMap
            (MvPolynomial.X ())) =
        MvPolynomial.X ()
    rw [RawPresheaf.coordinateRestriction_polynomialMap_X, map_mul]
    erw [TypedCoordinateRestriction.polynomialMap_C]
    rw [RawPresheaf.coordinateRestriction_polynomialMap_X]
    rw [← mul_assoc]
    erw [← MvPolynomial.C.map_mul]
    rw [hsign, map_one, one_mul]

private theorem rawRestriction_comp_self
    {X Y : site.category} (f : X ⟶ Y) :
    (rawSystem.restrictionStable f).quotientDesc.comp
        (rawSystem.restrictionStable f).quotientDesc =
      RingHom.id _ := by
  apply Ideal.Quotient.ringHom_ext
  apply RingHom.ext
  intro p
  simp only [RingHom.comp_apply]
  have h := congrArg (fun q => q p) (coordinateRestriction_comp_self f)
  simpa only [RawPresheaf.system_restriction, RingHom.comp_apply,
    RingHom.id_apply] using congrArg
      (rawSystem.relationFamily X).quotientMap h

private theorem rawRestriction_bijective
    {X Y : site.category} (f : X ⟶ Y) :
    Function.Bijective
      (rawSystem.restrictionStable f).quotientDesc := by
  apply Function.bijective_iff_has_inverse.mpr
  refine ⟨(rawSystem.restrictionStable f).quotientDesc, ?_, ?_⟩
  · intro q
    have h := congrArg (fun g => g q) (rawRestriction_comp_self f)
    simpa only [RingHom.comp_apply, RingHom.id_apply] using h
  · intro q
    have h := congrArg (fun g => g q) (rawRestriction_comp_self f)
    simpa only [RingHom.comp_apply, RingHom.id_apply] using h

private theorem rawRestrictionCommRing_isIso
    {X Y : site.category} (f : X ⟶ Y) :
    IsIso (CommRingCat.ofHom
      (rawSystem.restrictionStable f).quotientDesc) := by
  rw [CategoryTheory.ConcreteCategory.isIso_iff_bijective]
  exact rawRestriction_bijective f

private instance rawRestriction_isIso
    {X Y : site.category} (f : X ⟶ Y) :
    IsIso (rawSystem.toRingedSite.raw.map f.op) := by
  letI : IsIso ((Under.forget _).map
      (rawSystem.toRingedSite.raw.map f.op)) := by
    change IsIso (CommRingCat.ofHom
      (rawSystem.restrictionStable f).quotientDesc)
    exact rawRestrictionCommRing_isIso f
  exact isIso_of_reflects_iso _ (Under.forget _)

private instance sheafifiedRestrictionObject_isIso
    {X Y : site.category} (f : X ⟶ Y) :
    IsIso (rawSystem.toRingedSite.structureSheaf.val.map f.op) := by
  letI := canonical_component_isIso X
  letI := canonical_component_isIso Y
  haveI : IsIso
      (rawSystem.toRingedSite.raw.map f.op ≫
        rawSystem.toRingedSite.canonical.app (op X)) := inferInstance
  have hn := rawSystem.toRingedSite.canonical.naturality f.op
  haveI : IsIso
      (rawSystem.toRingedSite.canonical.app (op Y) ≫
        rawSystem.toRingedSite.structureSheaf.val.map f.op) := by
    rw [← hn]
    infer_instance
  exact CategoryTheory.IsIso.of_isIso_comp_left
    (rawSystem.toRingedSite.canonical.app (op Y))
    (rawSystem.toRingedSite.structureSheaf.val.map f.op)

private instance sheafifiedRestriction_isIso
    {X Y : site.category} (f : X ⟶ Y) :
    IsIso (sheafifiedRestriction rawSystem f) := by
  letI := sheafifiedRestrictionObject_isIso f
  change IsIso (rawSystem.toRingedSite.structureSheaf.val.map f.op).right
  infer_instance

private instance architectureChartRestriction_isIso
    {X Y : site.category} (f : X ⟶ Y) :
    IsIso (architectureChartRestriction rawSystem f) := by
  change IsIso (AlgebraicGeometry.Scheme.Spec.map
    (sheafifiedRestriction rawSystem f).op)
  infer_instance

private noncomputable def restrictionChart
    {W : site.category} (f : W ⟶ base) :
    ArchitectureAffineChart rawSystem
      (architectureChartSpec rawSystem base)
      (AATReadingDecoration.ofContext rawSystem base) where
  context := W
  contextHom := f
  map := architectureChartRestriction rawSystem f

private theorem restrictionChart_valid
    {W : site.category} (f : W ⟶ base) :
    IsArchitectureAffineChart rawSystem (restrictionChart f) := by
  constructor
  · letI := architectureChartRestriction_isIso f
    change AlgebraicGeometry.IsOpenImmersion
      (architectureChartRestriction rawSystem f)
    infer_instance
  · change sheafifiedRestriction rawSystem f =
      (AlgebraicGeometry.Scheme.ΓSpecIso
          (SheafifiedSectionRing rawSystem base)).inv ≫
        (architectureChartRestriction rawSystem f).appTop ≫
        (AlgebraicGeometry.Scheme.ΓSpecIso
          (SheafifiedSectionRing rawSystem W)).hom
    symm
    rw [architectureChartRestriction_appTop]
    exact (AlgebraicGeometry.Scheme.ΓSpecIso
      (SheafifiedSectionRing rawSystem base)).inv_hom_id_assoc _

private noncomputable def twoChartAtlas :
    ArchitectureAffineAtlas rawSystem
      (architectureChartSpec rawSystem base)
      (AATReadingDecoration.ofContext rawSystem base) where
  Index := Bool
  chart
    | false => restrictionChart RawPresheaf.leftToBase
    | true => restrictionChart rightToBase

private theorem twoChartAtlas_chart_map_eq (i : twoChartAtlas.Index) :
    (twoChartAtlas.chart i).map =
      architectureChartRestriction rawSystem
        (twoChartAtlas.chart i).contextHom := by
  cases i <;> rfl

private theorem twoChartAtlas_chart_isIso (i : twoChartAtlas.Index) :
    IsIso (twoChartAtlas.chart i).map := by
  rw [twoChartAtlas_chart_map_eq]
  infer_instance

private theorem twoChartAtlas_valid :
    IsArchitectureAffineAtlas rawSystem twoChartAtlas := by
  constructor
  · intro i
    cases i
    · exact restrictionChart_valid RawPresheaf.leftToBase
    · exact restrictionChart_valid rightToBase
  · intro x
    letI := architectureChartRestriction_isIso RawPresheaf.leftToBase
    refine ⟨false,
      (asIso (architectureChartRestriction rawSystem
        RawPresheaf.leftToBase)).inv x,
      ?_⟩
    exact AlgebraicGeometry.Scheme.inv_hom_apply
      (asIso (architectureChartRestriction rawSystem
        RawPresheaf.leftToBase)) x

private theorem twoChartPair_isPullback
    (i j : twoChartAtlas.Index) :
    IsPullback
      (architectureChartRestriction rawSystem
        (twoChartAtlas.pairToLeft rawSystem i j))
      (architectureChartRestriction rawSystem
        (twoChartAtlas.pairToRight rawSystem i j))
      (twoChartAtlas.chart i).map
      (twoChartAtlas.chart j).map := by
  letI := architectureChartRestriction_isIso
    (twoChartAtlas.pairToLeft rawSystem i j)
  letI := twoChartAtlas_chart_isIso j
  apply IsPullback.of_horiz_isIso
  constructor
  rw [twoChartAtlas_chart_map_eq, twoChartAtlas_chart_map_eq,
    ← architectureChartRestriction_comp,
    ← architectureChartRestriction_comp]
  exact congrArg (architectureChartRestriction rawSystem)
    (Subsingleton.elim _ _)

private noncomputable def twoChartOverlapPresentation :
    ArchitectureOverlapPresentation rawSystem twoChartAtlas where
  comparison i j := (twoChartPair_isPullback i j).isoPullback

private theorem twoChartOverlapPresentation_valid :
    IsArchitectureOverlapPresentation rawSystem
      twoChartOverlapPresentation := by
  constructor
  · intro i j
    exact IsPullback.isoPullback_hom_fst (twoChartPair_isPullback i j)
  · intro i j
    exact IsPullback.isoPullback_hom_snd (twoChartPair_isPullback i j)

/-- The finite model with exactly the selected left and right actual restriction charts. -/
noncomputable def twoChartReferenceModel :
    StandardArchitectureScheme rawSystem :=
  StandardArchitectureScheme.ofPresentation rawSystem
    (architectureChartSpec rawSystem base)
    (AATReadingDecoration.ofContext rawSystem base)
    twoChartAtlas twoChartAtlas_valid
    twoChartOverlapPresentation twoChartOverlapPresentation_valid

/-- The left chart index of the finite two-chart model. -/
def leftIndex : twoChartReferenceModel.atlas.Index :=
  false

/-- The right chart index of the finite two-chart model. -/
def rightIndex : twoChartReferenceModel.atlas.Index :=
  true

/-- The two selected chart indices are distinct. -/
theorem leftIndex_ne_rightIndex : leftIndex ≠ rightIndex := by
  change (false : Bool) ≠ true
  decide

/-- Every index of the generated finite atlas is one of its two selected indices. -/
theorem index_cases (i : twoChartReferenceModel.atlas.Index) :
    i = leftIndex ∨ i = rightIndex := by
  cases i <;> simp [leftIndex, rightIndex]

/-- The finite two-chart model is carried by the base section-ring Spec. -/
@[simp] theorem twoChart_underlying :
    twoChartReferenceModel.underlying =
      architectureChartSpec rawSystem base :=
  rfl

/-- The left chart retains the selected left context. -/
@[simp] theorem left_chart_context :
    (twoChartReferenceModel.atlas.chart leftIndex).context =
      RawPresheaf.left :=
  rfl

/-- The right chart retains the selected right context. -/
@[simp] theorem right_chart_context :
    (twoChartReferenceModel.atlas.chart rightIndex).context =
      rightContext :=
  rfl

/-- The left chart map is the actual canonical restriction transition. -/
@[simp] theorem left_chart_map :
    (twoChartReferenceModel.atlas.chart leftIndex).map =
      architectureChartRestriction rawSystem RawPresheaf.leftToBase :=
  rfl

/-- The right chart map is the actual canonical restriction transition. -/
@[simp] theorem right_chart_map :
    (twoChartReferenceModel.atlas.chart rightIndex).map =
      architectureChartRestriction rawSystem rightToBase :=
  rfl

/-- The two chart contexts of the generated model are distinct. -/
theorem chart_contexts_ne :
    (twoChartReferenceModel.atlas.chart leftIndex).context ≠
      (twoChartReferenceModel.atlas.chart rightIndex).context := by
  simpa using leftContext_ne_rightContext

/-- The actual affine chart images jointly cover the base Scheme. -/
theorem twoChart_jointlyCovers :
    ⨆ i, ((twoChartReferenceModel.affineOpenCover rawSystem).f i).opensRange = ⊤ :=
  twoChartReferenceModel.chart_jointlyCovers rawSystem

/-- The generated left chart is an actual open immersion. -/
theorem left_chart_isOpenImmersion :
    AlgebraicGeometry.IsOpenImmersion
      (twoChartReferenceModel.atlas.chart leftIndex).map :=
  twoChartReferenceModel.chart_isOpenImmersion rawSystem leftIndex

/-- The generated right chart is an actual open immersion. -/
theorem right_chart_isOpenImmersion :
    AlgebraicGeometry.IsOpenImmersion
      (twoChartReferenceModel.atlas.chart rightIndex).map :=
  twoChartReferenceModel.chart_isOpenImmersion rawSystem rightIndex

/-- The generated comparison has the selected actual left projection. -/
theorem overlap_comparison_fst :
    (twoChartReferenceModel.overlaps.comparison leftIndex rightIndex).hom ≫
        pullback.fst
          (twoChartReferenceModel.atlas.chart leftIndex).map
          (twoChartReferenceModel.atlas.chart rightIndex).map =
      architectureChartRestriction rawSystem
        (twoChartReferenceModel.atlas.pairToLeft rawSystem leftIndex rightIndex) :=
  twoChartReferenceModel.overlapsValid.comparison_fst _ _

/-- The generated comparison has the selected actual right projection. -/
theorem overlap_comparison_snd :
    (twoChartReferenceModel.overlaps.comparison leftIndex rightIndex).hom ≫
        pullback.snd
          (twoChartReferenceModel.atlas.chart leftIndex).map
          (twoChartReferenceModel.atlas.chart rightIndex).map =
      architectureChartRestriction rawSystem
        (twoChartReferenceModel.atlas.pairToRight rawSystem leftIndex rightIndex) :=
  twoChartReferenceModel.overlapsValid.comparison_snd _ _

/-- The selected decoration restrictions agree on the actual two-chart overlap context. -/
theorem decoration_overlap_fires :
    sheafifiedRestriction rawSystem
        (twoChartReferenceModel.atlas.pairToLeft rawSystem leftIndex rightIndex ≫
          (twoChartReferenceModel.atlas.chart leftIndex).contextHom) =
      sheafifiedRestriction rawSystem
        (twoChartReferenceModel.atlas.pairToRight rawSystem leftIndex rightIndex ≫
          (twoChartReferenceModel.atlas.chart rightIndex).contextHom) :=
  twoChartReferenceModel.atlas.decoration_overlap rawSystem _ _

/-- Actual iterated pullbacks satisfy both triple-overlap equations for all chart indices. -/
theorem actual_triple_cocycle_fires :
    ∀ i j l : twoChartReferenceModel.atlas.Index,
      twoChartReferenceModel.atlas.actualTripleToLeft rawSystem i j l ≫
          (twoChartReferenceModel.atlas.chart i).map =
        twoChartReferenceModel.atlas.actualTripleToMiddle rawSystem i j l ≫
          (twoChartReferenceModel.atlas.chart j).map ∧
      twoChartReferenceModel.atlas.actualTripleToMiddle rawSystem i j l ≫
          (twoChartReferenceModel.atlas.chart j).map =
        twoChartReferenceModel.atlas.actualTripleToRight rawSystem i j l ≫
          (twoChartReferenceModel.atlas.chart l).map := by
  intro i j l
  exact twoChartReferenceModel.atlas.actualTriple_cocycle rawSystem i j l

/-- Selected triple-context restrictions satisfy both equations for all chart indices. -/
theorem context_triple_cocycle_fires :
    ∀ i j l : twoChartReferenceModel.atlas.Index,
      architectureChartRestriction rawSystem
            (twoChartReferenceModel.atlas.tripleToLeft rawSystem i j l) ≫
          (twoChartReferenceModel.atlas.chart i).map =
        architectureChartRestriction rawSystem
            (twoChartReferenceModel.atlas.tripleToMiddle rawSystem i j l) ≫
          (twoChartReferenceModel.atlas.chart j).map ∧
      architectureChartRestriction rawSystem
            (twoChartReferenceModel.atlas.tripleToMiddle rawSystem i j l) ≫
          (twoChartReferenceModel.atlas.chart j).map =
        architectureChartRestriction rawSystem
            (twoChartReferenceModel.atlas.tripleToRight rawSystem i j l) ≫
          (twoChartReferenceModel.atlas.chart l).map := by
  intro i j l
  exact twoChartReferenceModel.atlas.contextTriple_cocycle rawSystem
    twoChartReferenceModel.overlaps twoChartReferenceModel.overlapsValid i j l

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
### Finite non-preserving decoration witness

The source decoration transports the selected coordinate through the identity raw-quotient
comparison.  The actual sign-changing Spec transition gives a different global section, so
the preservation equation fails without accepting an inequality or failure proof as input.
-/

/-- A source decoration using identity transport instead of the actual sign transition. -/
noncomputable def nonPreservingSourceDecoration :
    AATReadingDecoration rawSystem
      (architectureChartSpec rawSystem RawPresheaf.left) where
  context := base
  interpretation := identitySheafifiedMap ≫
    (AlgebraicGeometry.Scheme.ΓSpecIso
      (SheafifiedSectionRing rawSystem RawPresheaf.left)).inv

/-- The selected source context is the finite base context. -/
@[simp] theorem nonPreservingSourceDecoration_context :
    nonPreservingSourceDecoration.context = base :=
  rfl

/-- Identity transport and the actual Spec transition disagree on the selected coordinate. -/
theorem nonPreservingSourceDecoration_coordinate_ne :
    nonPreservingSourceDecoration.interpretation baseCoordinateSection ≠
      ((AATReadingDecoration.ofContext rawSystem base).interpretation ≫
        (architectureChartRestriction rawSystem
          RawPresheaf.leftToBase).appTop) baseCoordinateSection := by
  intro h
  apply left_transition_changes_coordinate
  have hh := congrArg
    (AlgebraicGeometry.Scheme.ΓSpecIso
      (SheafifiedSectionRing rawSystem RawPresheaf.left)).hom h
  have hsource :
      (AlgebraicGeometry.Scheme.ΓSpecIso
          (SheafifiedSectionRing rawSystem RawPresheaf.left)).hom
          (nonPreservingSourceDecoration.interpretation baseCoordinateSection) =
        leftCoordinateSection := by
    change
      (AlgebraicGeometry.Scheme.ΓSpecIso
          (SheafifiedSectionRing rawSystem RawPresheaf.left)).hom
          ((AlgebraicGeometry.Scheme.ΓSpecIso
            (SheafifiedSectionRing rawSystem RawPresheaf.left)).inv
              (identitySheafifiedMap baseCoordinateSection)) =
        leftCoordinateSection
    rw [Iso.inv_hom_id_apply]
    simpa only [baseCoordinateSection, leftCoordinateSection] using
      identitySheafifiedMap_coordinate
  rw [hsource] at hh
  simpa only [CommRingCat.comp_apply] using hh.symm

/-- The concrete source decoration is not preserved by the actual sign transition. -/
theorem nonPreservingDecoration_example :
    ¬ nonPreservingSourceDecoration.Preserves rawSystem
      (architectureChartRestriction rawSystem RawPresheaf.leftToBase)
      (AATReadingDecoration.ofContext rawSystem base) := by
  rintro ⟨h, hh⟩
  have hctx : h = 𝟙 base := Subsingleton.elim _ _
  subst h
  apply nonPreservingSourceDecoration_coordinate_ne
  have ha := congrArg (fun q => q baseCoordinateSection) hh
  change
    nonPreservingSourceDecoration.interpretation
        (sheafifiedRestriction rawSystem (𝟙 base) baseCoordinateSection) =
      ((AATReadingDecoration.ofContext rawSystem base).interpretation ≫
        (architectureChartRestriction rawSystem
          RawPresheaf.leftToBase).appTop) baseCoordinateSection at ha
  simpa only [sheafifiedRestriction_id, CommRingCat.id_apply] using ha

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

/-- The actual pullback overlap of the two selected charts has a point. -/
theorem twoChart_overlap_nonempty :
    Nonempty
      (twoChartReferenceModel.atlas.actualOverlap
        rawSystem leftIndex rightIndex) := by
  let f := architectureChartRestriction rawSystem
    (twoChartReferenceModel.atlas.pairToBase
      rawSystem leftIndex rightIndex)
  letI : IsIso f := architectureChartRestriction_isIso _
  let x := Classical.choice baseSpec_nonempty
  exact ⟨
    (twoChartReferenceModel.overlaps.comparison
      leftIndex rightIndex).hom ((asIso f).inv x)⟩

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

private theorem identitySpecMap_ne_leftTransition :
    AlgebraicGeometry.Spec.map identitySheafifiedMap ≠
      architectureChartRestriction rawSystem RawPresheaf.leftToBase := by
  intro h
  have hring :
      identitySheafifiedMap =
        sheafifiedRestriction rawSystem RawPresheaf.leftToBase := by
    apply AlgebraicGeometry.Spec.map_injective
    simpa only [architectureChartRestriction_eq_SpecMap] using h
  apply sheafified_leftToBase_changes_coordinate
  calc
    sheafifiedRestriction rawSystem RawPresheaf.leftToBase
          baseCoordinateSection =
        identitySheafifiedMap baseCoordinateSection := by
      exact congrArg (fun q => q baseCoordinateSection) hring.symm
    _ = leftCoordinateSection := by
      simpa only [baseCoordinateSection, leftCoordinateSection] using
        identitySheafifiedMap_coordinate

private noncomputable def baseSignTwist :
    architectureChartSpec rawSystem base ≅
      architectureChartSpec rawSystem base := by
  letI : IsIso identitySheafifiedMap :=
    identitySheafifiedMap_isIso
  exact
    (asIso (architectureChartRestriction rawSystem
      RawPresheaf.leftToBase)).symm ≪≫
      asIso (AlgebraicGeometry.Spec.map identitySheafifiedMap)

private theorem baseSignTwist_hom_ne :
    baseSignTwist.hom ≠ 𝟙 _ := by
  intro h
  apply identitySpecMap_ne_leftTransition
  rw [← cancel_epi
    (inv (architectureChartRestriction rawSystem
      RawPresheaf.leftToBase))]
  simpa [baseSignTwist] using h

private noncomputable def pairSignTwist
    (i j : twoChartReferenceModel.atlas.Index) :
    architectureChartSpec rawSystem
        (twoChartReferenceModel.atlas.pairContext rawSystem i j) ≅
      architectureChartSpec rawSystem
        (twoChartReferenceModel.atlas.pairContext rawSystem i j) :=
  asIso (architectureChartRestriction rawSystem
      (twoChartReferenceModel.atlas.pairToBase rawSystem i j)) ≪≫
    baseSignTwist ≪≫
    (asIso (architectureChartRestriction rawSystem
      (twoChartReferenceModel.atlas.pairToBase rawSystem i j))).symm

private theorem pairSignTwist_hom_ne
    (i j : twoChartReferenceModel.atlas.Index) :
    (pairSignTwist i j).hom ≠ 𝟙 _ := by
  intro h
  apply baseSignTwist_hom_ne
  let p := architectureChartRestriction rawSystem
    (twoChartReferenceModel.atlas.pairToBase rawSystem i j)
  have h' := congrArg (fun q => inv p ≫ q ≫ p) h
  simpa [pairSignTwist, p, Category.assoc] using h'

private theorem pairSignTwist_symm_hom_ne
    (i j : twoChartReferenceModel.atlas.Index) :
    (pairSignTwist i j).symm.hom ≠ 𝟙 _ := by
  intro h
  apply pairSignTwist_hom_ne i j
  have h' := congrArg
    (fun q => (pairSignTwist i j).hom ≫ q) h
  simpa using h'.symm

/-- The actual overlap comparison twisted by the finite sign action. -/
noncomputable def fstBrokenOverlapPresentation :
    ArchitectureOverlapPresentation rawSystem
      twoChartReferenceModel.atlas where
  comparison i j :=
    pairSignTwist i j ≪≫
      twoChartReferenceModel.overlaps.comparison i j

/-- The twisted comparison fails its selected first-projection equation. -/
theorem fstBrokenOverlapPresentation_equation_ne :
    (fstBrokenOverlapPresentation.comparison
          leftIndex rightIndex).hom ≫
        pullback.fst
          (twoChartReferenceModel.atlas.chart leftIndex).map
          (twoChartReferenceModel.atlas.chart rightIndex).map ≠
      architectureChartRestriction rawSystem
        (twoChartReferenceModel.atlas.pairToLeft
          rawSystem leftIndex rightIndex) := by
  intro h
  apply pairSignTwist_hom_ne leftIndex rightIndex
  rw [← cancel_mono
    (architectureChartRestriction rawSystem
      (twoChartReferenceModel.atlas.pairToLeft
        rawSystem leftIndex rightIndex))]
  simpa only [fstBrokenOverlapPresentation, Iso.trans_hom,
    Category.assoc, overlap_comparison_fst,
    Category.id_comp] using h

/-- The first-projection-twisted comparison is not a valid overlap presentation. -/
theorem fstBrokenOverlapPresentation_not_valid :
    ¬ IsArchitectureOverlapPresentation rawSystem
      fstBrokenOverlapPresentation := by
  intro h
  exact fstBrokenOverlapPresentation_equation_ne
    (h.comparison_fst leftIndex rightIndex)

/-- The actual overlap comparison twisted by the inverse finite sign action. -/
noncomputable def sndBrokenOverlapPresentation :
    ArchitectureOverlapPresentation rawSystem
      twoChartReferenceModel.atlas where
  comparison i j :=
    (pairSignTwist i j).symm ≪≫
      twoChartReferenceModel.overlaps.comparison i j

/-- The inverse-twisted comparison fails its selected second-projection equation. -/
theorem sndBrokenOverlapPresentation_equation_ne :
    (sndBrokenOverlapPresentation.comparison
          leftIndex rightIndex).hom ≫
        pullback.snd
          (twoChartReferenceModel.atlas.chart leftIndex).map
          (twoChartReferenceModel.atlas.chart rightIndex).map ≠
      architectureChartRestriction rawSystem
        (twoChartReferenceModel.atlas.pairToRight
          rawSystem leftIndex rightIndex) := by
  intro h
  apply pairSignTwist_symm_hom_ne leftIndex rightIndex
  rw [← cancel_mono
    (architectureChartRestriction rawSystem
      (twoChartReferenceModel.atlas.pairToRight
        rawSystem leftIndex rightIndex))]
  simpa only [sndBrokenOverlapPresentation, Iso.trans_hom,
    Category.assoc, overlap_comparison_snd,
    Category.id_comp] using h

/-- The second-projection-twisted comparison is not a valid overlap presentation. -/
theorem sndBrokenOverlapPresentation_not_valid :
    ¬ IsArchitectureOverlapPresentation rawSystem
      sndBrokenOverlapPresentation := by
  intro h
  exact sndBrokenOverlapPresentation_equation_ne
    (h.comparison_snd leftIndex rightIndex)

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
