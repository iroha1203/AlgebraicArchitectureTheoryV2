import Formal.SHIGURE.Part2.AffineFoundations
import Mathlib.AlgebraicGeometry.Sites.SmallAffineZariski
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # Relative spectrum on a scheme

The local algebras on the affine opens of the base come with their restriction
maps. Localizing those algebras on principal opens gives the actual open
immersions used to glue their spectra.

## Implementation notes

The small affine Zariski site remembers principal open restrictions. The
structure sheaf and its algebra are compared there by mathlib's pushout
criterion for localization. Passing to spectra turns those squares into
pullbacks, so the relative gluing recovers each chart on its whole inverse image.
-/

namespace SHIGURE.SchemeDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

noncomputable section

universe u

/-- A quasi-coherent algebra presented by its sections on affine opens. -/
structure QuasiCoherentAlgebra (X : Scheme.{u}) where
  /-- Sections with their restriction to principal opens. -/
  sections : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat
  /-- The action of the base structure sheaf. -/
  algebra : (Scheme.AffineZariskiSite.toOpensFunctor X).op ⋙ X.presheaf ⟶ sections
  /-- Sections over a principal open are the corresponding localization. -/
  localization (U : X.AffineZariskiSite) (r : Γ(X, U.1)) :
    letI := (sections.map (homOfLE (U.basicOpen_le r)).op).hom.toAlgebra
    IsLocalization.Away (algebra.app (.op U) r) (sections.obj (.op (U.basicOpen r)))

namespace QuasiCoherentAlgebra

variable {X : Scheme.{u}} (C : QuasiCoherentAlgebra X)

/-- Each basic-open restriction of the algebra is a pushout of the base restriction. -/
theorem coequifibered : C.algebra.Coequifibered :=
  Scheme.AffineZariskiSite.coequifibered_iff_forall_isLocalizationAway.mpr C.localization

/-- Gluing data for the affine spectra of the algebra. -/
def gluingData : (Scheme.AffineZariskiSite.directedCover X).RelativeGluingData :=
  Scheme.AffineZariskiSite.relativeGluingData C.coequifibered

/-- The relative spectrum of the quasi-coherent algebra. -/
abbrev spec : Scheme.{u} := C.gluingData.glued

/-- The structural morphism of the relative spectrum. -/
def projection : C.spec ⟶ X := C.gluingData.toBase

/-- The canonical morphism from the spectrum of the algebra on an affine open. -/
def chart (U : X.AffineZariskiSite) : Spec (C.sections.obj (.op U)) ⟶ C.spec :=
  C.gluingData.cover.f U

instance chart_open (U : X.AffineZariskiSite) : IsOpenImmersion (C.chart U) :=
  inferInstanceAs (IsOpenImmersion (C.gluingData.cover.f U))

/-- The structural morphism on each chart is the spectrum of its algebra map. -/
@[reassoc (attr := simp)]
theorem chart_projection (U : X.AffineZariskiSite) :
    C.chart U ≫ C.projection = Spec.map (C.algebra.app (.op U)) ≫ U.2.fromSpec := by
  have h := C.gluingData.ι_toBase U
  exact h

/-- The inverse image of a base affine open is exactly the image of its chart. -/
theorem preimage_eq_chart (U : X.AffineZariskiSite) :
    C.projection ⁻¹ᵁ U.1 = (C.chart U).opensRange := by
  simpa [projection, chart] using C.gluingData.toBase_preimage_eq_opensRange_ι U

/-- Each affine open gives the pullback of the relative spectrum over that open. -/
theorem isPullback_chart (U : X.AffineZariskiSite) :
    IsPullback (Spec.map (C.algebra.app (.op U)) ≫ U.2.isoSpec.inv) (C.chart U) U.1.ι C.projection :=
  C.gluingData.isPullback_natTrans_ι_toBase U

/-- The relative spectrum is affine over its base scheme. -/
instance affine_projection : IsAffineHom C.projection where
  isAffine_preimage U hU := by
    rw [C.preimage_eq_chart ⟨U, hU⟩]
    exact isAffineOpen_opensRange (C.chart ⟨U, hU⟩)


/-- The chart maps agree with the transition morphisms of the algebra. -/
@[reassoc (attr := simp)]
theorem chart_naturality {U V : X.AffineZariskiSite} (f : U ⟶ V) :
    Spec.map (C.sections.map f.op) ≫ C.chart V = C.chart U :=
  C.gluingData.cover.trans_map f

/-- Restrict a test scheme over the base to the base's affine opens. -/
abbrev testCover {Y : Scheme.{u}} (g : Y ⟶ X) : Y.OpenCover :=
  (Scheme.AffineZariskiSite.directedCover X).pullback₁ g

/-- The map from a test chart to the corresponding base open. -/
abbrev testToBase {Y : Scheme.{u}} (g : Y ⟶ X) (U : X.AffineZariskiSite) :
    (testCover g).X U ⟶ U.1.toScheme :=
  pullback.snd g U.1.ι

/-- The relative chart over its base affine open. -/
abbrev chartToBase (U : X.AffineZariskiSite) : Spec (C.sections.obj (.op U)) ⟶ U.1.toScheme :=
  Spec.map (C.algebra.app (.op U)) ≫ U.2.isoSpec.inv

/-- The chart map to the base open and the chart inclusion commute. -/
@[reassoc]
theorem chartToBase_ι (U : X.AffineZariskiSite) :
    C.chartToBase U ≫ U.1.ι = C.chart U ≫ C.projection :=
  (C.isPullback_chart U).w

/-- A compatible family of maps from the inverse images of base opens to their relative spectra. -/
@[ext]
structure ChartMaps {Y : Scheme.{u}} (g : Y ⟶ X) where
  /-- A map on each actual inverse image open of the test scheme. -/
  app (U : X.AffineZariskiSite) : (testCover g).X U ⟶ Spec (C.sections.obj (.op U))
  /-- On every principal-open restriction the two maps agree. -/
  naturality {U V : X.AffineZariskiSite} (f : U ⟶ V) :
    (testCover g).trans f ≫ app V = app U ≫ Spec.map (C.sections.map f.op)
  /-- Each local map lies over the corresponding affine open of the base. -/
  over (U : X.AffineZariskiSite) : app U ≫ C.chartToBase U = testToBase g U

variable {Y : Scheme.{u}} {g : Y ⟶ X}

/-- Restrict a map over the base using the actual pullback that defines each chart. -/
def restrictMap (h : Over.mk g ⟶ Over.mk C.projection) (U : X.AffineZariskiSite) :
    (testCover g).X U ⟶ Spec (C.sections.obj (.op U)) :=
  (C.isPullback_chart U).lift (testToBase g U) ((testCover g).f U ≫ h.left) (by
    rw [Category.assoc, show h.left ≫ C.projection = g from Over.w h]
    exact (pullback.condition (f := g) (g := U.1.ι)).symm)

@[reassoc (attr := simp)]
theorem restrictMap_chartToBase (h : Over.mk g ⟶ Over.mk C.projection) (U : X.AffineZariskiSite) :
    C.restrictMap h U ≫ C.chartToBase U = testToBase g U :=
  IsPullback.lift_fst _ _ _ _

@[reassoc (attr := simp)]
theorem restrictMap_chart (h : Over.mk g ⟶ Over.mk C.projection) (U : X.AffineZariskiSite) :
    C.restrictMap h U ≫ C.chart U = (testCover g).f U ≫ h.left :=
  IsPullback.lift_snd _ _ _ _

/-- A global map over the base gives a compatible family on the affine opens of the base. -/
def restrictCharts (h : Over.mk g ⟶ Over.mk C.projection) : C.ChartMaps g where
  app := C.restrictMap h
  over := C.restrictMap_chartToBase h
  naturality {U V} f := by
    rw [← cancel_mono (C.chart V), Category.assoc, C.restrictMap_chart, Category.assoc,
      C.chart_naturality, C.restrictMap_chart, ← Category.assoc, Scheme.Cover.trans_map]

/-- Compatible maps glue to a map of schemes over the base. -/
def glueCharts (h : C.ChartMaps g) : Over.mk g ⟶ Over.mk C.projection :=
  (testCover g).glueMorphismsOverOfLocallyDirected
    (fun U => h.app U ≫ C.chart U)
    (fun f => by rw [← Category.assoc, h.naturality, Category.assoc, C.chart_naturality])
    (fun U => by
      change (h.app U ≫ C.chart U) ≫ C.projection = (testCover g).f U ≫ g
      rw [Category.assoc, ← C.chartToBase_ι, ← Category.assoc, h.over]
      exact (pullback.condition (f := g) (g := U.1.ι)).symm)

/-- The glued map has the prescribed local components. -/
@[reassoc (attr := simp)]
theorem glueCharts_chart (h : C.ChartMaps g) (U : X.AffineZariskiSite) :
    (testCover g).f U ≫ (C.glueCharts h).left = h.app U ≫ C.chart U :=
  by
    unfold glueCharts
    apply Scheme.OpenCover.map_glueMorphismsOverOfLocallyDirected_left
    intro U V f
    rw [← Category.assoc, h.naturality, Category.assoc, C.chart_naturality]

/-- The relative spectrum represents the compatible maps to its affine charts. -/
def homEquivCharts : (Over.mk g ⟶ Over.mk C.projection) ≃ C.ChartMaps g where
  toFun := C.restrictCharts
  invFun := C.glueCharts
  left_inv h := by
    apply Over.OverMorphism.ext
    apply (testCover g).hom_ext
    intro U
    rw [C.glueCharts_chart, restrictCharts, C.restrictMap_chart]
  right_inv h := by
    apply ChartMaps.ext
    funext U
    change C.restrictMap (C.glueCharts h) U = h.app U
    rw [← cancel_mono (C.chart U), C.restrictMap_chart, C.glueCharts_chart]


/-- The structure ring of each base open acts on sections of its inverse image. -/
def baseSectionMap (g : Y ⟶ X) (U : X.AffineZariskiSite) :
    Γ(X, U.1) ⟶ Γ((testCover g).X U, ⊤) :=
  specGlobalHom (testToBase g U ≫ U.2.isoSpec.hom)

/-- Compatible algebra maps into the direct image of the test scheme's structure sheaf. -/
@[ext]
structure ChartAlgebraMaps (g : Y ⟶ X) where
  /-- An algebra map into the sections of each actual inverse image open. -/
  app (U : X.AffineZariskiSite) : C.sections.obj (.op U) ⟶ Γ((testCover g).X U, ⊤)
  /-- The maps commute with principal-open restriction. -/
  naturality {U V : X.AffineZariskiSite} (f : U ⟶ V) :
    C.sections.map f.op ≫ app U = app V ≫ ((testCover g).trans f).appTop
  /-- The maps preserve the action of the base structure sheaf. -/
  over (U : X.AffineZariskiSite) : C.algebra.app (.op U) ≫ app U = baseSectionMap g U

private theorem chart_map_over_iff (U : X.AffineZariskiSite)
    (h : (testCover g).X U ⟶ Spec (C.sections.obj (.op U))) :
    h ≫ C.chartToBase U = testToBase g U ↔
      C.algebra.app (.op U) ≫ specGlobalHom h = baseSectionMap g U := by
  rw [← specGlobalHom_postcomp, baseSectionMap]
  constructor
  · intro over
    apply congrArg specGlobalHom
    have h' := congrArg (· ≫ U.2.isoSpec.hom) over
    simpa only [chartToBase, Category.assoc, Iso.inv_hom_id, Category.comp_id] using h'
  · intro over
    have h' := specGlobalHom.injective over
    rw [← cancel_mono U.2.isoSpec.hom]
    simpa only [chartToBase, Category.assoc, Iso.inv_hom_id, Category.comp_id] using h'

/-- The absolute adjunction identifies compatible chart maps with compatible algebra maps. -/
def chartMapsEquivAlgebraMaps : C.ChartMaps g ≃ C.ChartAlgebraMaps g where
  toFun h :=
    { app := fun U => specGlobalHom (h.app U)
      naturality := fun f => by
        change _ = _ ≫ Scheme.Γ.map ((testCover g).trans f).op
        rw [← specGlobalHom_postcomp, ← specGlobalHom_precomp, h.naturality]
      over := fun U => (C.chart_map_over_iff U (h.app U)).1 (h.over U) }
  invFun a :=
    { app := fun U => specGlobalHom.symm (a.app U)
      naturality := fun f => by
        apply specGlobalHom.injective
        rw [specGlobalHom_precomp, specGlobalHom_postcomp]
        simpa using (a.naturality f).symm
      over := fun U => (C.chart_map_over_iff U _).2 (by simpa using a.over U) }
  left_inv h := by
    apply ChartMaps.ext
    funext U
    exact Equiv.symm_apply_apply _ _
  right_inv a := by
    apply ChartAlgebraMaps.ext
    funext U
    exact Equiv.apply_symm_apply _ _

/-- The relative spectrum represents algebra maps to the test scheme's structure sheaf on the base site. -/
def homEquivAlgebraMaps : (Over.mk g ⟶ Over.mk C.projection) ≃ C.ChartAlgebraMaps g :=
  C.homEquivCharts.trans C.chartMapsEquivAlgebraMaps


variable {Y' : Scheme.{u}} {g' : Y' ⟶ X}

/-- A map over the base induces a map on the corresponding inverse image opens. -/
def testChartMap (f : Over.mk g' ⟶ Over.mk g) (U : X.AffineZariskiSite) :
    (testCover g').X U ⟶ (testCover g).X U :=
  pullback.map g' U.1.ι g U.1.ι f.left (𝟙 _) (𝟙 _)
    (by simpa using (show f.left ≫ g = g' from Over.w f).symm)
    (by simp)

@[reassoc (attr := simp)]
theorem testChartMap_f (f : Over.mk g' ⟶ Over.mk g) (U : X.AffineZariskiSite) :
    testChartMap f U ≫ (testCover g).f U = (testCover g').f U ≫ f.left :=
  by simp [testChartMap, testCover, pullback.map]

/-- Restriction of a composite is the composite of the restrictions. -/
theorem restrictMap_precomp (f : Over.mk g' ⟶ Over.mk g)
    (h : Over.mk g ⟶ Over.mk C.projection) (U : X.AffineZariskiSite) :
    C.restrictMap (f ≫ h) U = testChartMap f U ≫ C.restrictMap h U := by
  rw [← cancel_mono (C.chart U), restrictMap_chart, Category.assoc, restrictMap_chart,
    testChartMap_f_assoc]
  rfl

/-- The relative spectrum's algebra-map equivalence is natural in all test schemes over the base. -/
theorem homEquivAlgebraMaps_precomp (f : Over.mk g' ⟶ Over.mk g)
    (h : Over.mk g ⟶ Over.mk C.projection) (U : X.AffineZariskiSite) :
    (C.homEquivAlgebraMaps (f ≫ h)).app U =
      (C.homEquivAlgebraMaps h).app U ≫ (testChartMap f U).appTop := by
  change specGlobalHom (C.restrictMap (f ≫ h) U) =
    specGlobalHom (C.restrictMap h U) ≫ Scheme.Γ.map (testChartMap f U).op
  rw [C.restrictMap_precomp, specGlobalHom_precomp]

end QuasiCoherentAlgebra

end

end SHIGURE.SchemeDescent
