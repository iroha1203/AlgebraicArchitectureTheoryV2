import Formal.SHIGURE.Part2.Schemes.RelativeSpecSheaves

/-! # Arbitrary base change of relative spectra

The direct image algebra of an affine morphism recovers the morphism by
gluing its affine spectra. In the pullback, the new rings of sections are
the tensor products on affine charts. The algebra-sheaf equivalence also
identifies maps into the pullback with maps from the pulled-back algebra.
-/

namespace SHIGURE.SchemeDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

noncomputable section

universe u

namespace QuasiCoherentAlgebra

variable {X Y : Scheme.{u}} (C : QuasiCoherentAlgebra X)

/-- The direct image of the structure sheaf along an affine morphism is a quasi-coherent algebra. -/
def ofAffine (f : Y ⟶ X) [IsAffineHom f] : QuasiCoherentAlgebra X where
  sections := directImageSections f
  algebra := directImageAlgebra f
  localization U r := by
    let W := U.basicOpen r
    let map : (f ⁻¹ᵁ W.1) ⟶ (f ⁻¹ᵁ U.1) :=
      (Opens.map f.base).map ((Scheme.AffineZariskiSite.toOpensFunctor X).map (homOfLE (U.basicOpen_le r)))
    exact (U.2.preimage f).isLocalization_of_eq_basicOpen (f.app U.1 r) map (f.preimage_basicOpen r)

variable (f : Y ⟶ X) [IsAffineHom f]

/-- Recover an affine morphism by gluing the spectra of its direct image algebra. -/
def recoverAffine : (ofAffine f).spec ⟶ Y :=
  (ofAffine f).gluingData.cover.glueMorphismsOfLocallyDirected
    (fun U => (U.2.preimage f).fromSpec)
    (fun {U V} a => (V.2.preimage f).map_fromSpec (U.2.preimage f)
      ((Opens.map f.base).map ((Scheme.AffineZariskiSite.toOpensFunctor X).map a)).op)

@[reassoc (attr := simp)]
theorem chart_recoverAffine (U : X.AffineZariskiSite) :
    (ofAffine f).chart U ≫ recoverAffine f = (U.2.preimage f).fromSpec := by
  unfold recoverAffine chart
  apply Scheme.OpenCover.map_glueMorphismsOfLocallyDirected
  intro V W a
  exact (W.2.preimage f).map_fromSpec (V.2.preimage f)
    ((Opens.map f.base).map ((Scheme.AffineZariskiSite.toOpensFunctor X).map a)).op

/-- The recovered morphism is over the original base. -/
@[reassoc (attr := simp)]
theorem recoverAffine_projection : recoverAffine f ≫ f = (ofAffine f).projection := by
  apply (ofAffine f).gluingData.cover.hom_ext
  intro U
  change (ofAffine f).chart U ≫ recoverAffine f ≫ f = (ofAffine f).chart U ≫ (ofAffine f).projection
  rw [chart_recoverAffine_assoc, chart_projection]
  exact (U.2.SpecMap_appLE_fromSpec f (U.2.preimage f) (i := le_rfl)).symm.trans (by
    rw [Scheme.Hom.appLE_eq_app]; rfl)


/-- An affine inverse-image chart is the spectrum of its ring of sections. -/
def affineChartIso (U : X.AffineZariskiSite) :
    Spec ((ofAffine f).sections.obj (.op U)) ≅ (testCover f).X U :=
  IsOpenImmersion.isoOfRangeEq (U.2.preimage f).fromSpec ((testCover f).f U) <| by
    change Set.range (U.2.preimage f).fromSpec = Set.range (pullback.fst f U.1.ι)
    rw [(U.2.preimage f).range_fromSpec, Scheme.Pullback.range_fst, Scheme.Opens.range_ι]
    rfl

@[reassoc (attr := simp)]
theorem affineChartIso_hom_f (U : X.AffineZariskiSite) :
    (affineChartIso f U).hom ≫ (testCover f).f U = (U.2.preimage f).fromSpec :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

@[reassoc (attr := simp)]
theorem affineChartIso_inv_fromSpec (U : X.AffineZariskiSite) :
    (affineChartIso f U).inv ≫ (U.2.preimage f).fromSpec = (testCover f).f U :=
  IsOpenImmersion.isoOfRangeEq_inv_fac _ _ _

private def affineChartMaps : (ofAffine f).ChartMaps f where
  app U := (affineChartIso f U).inv
  naturality {U V} a := by
    rw [← cancel_mono (V.2.preimage f).fromSpec]
    have left : ((testCover f).trans a ≫ (affineChartIso f V).inv) ≫ (V.2.preimage f).fromSpec =
        (testCover f).f U := by
      rw [Category.assoc, affineChartIso_inv_fromSpec, Scheme.Cover.trans_map]
    have natural : Spec.map ((ofAffine f).sections.map a.op) ≫ (V.2.preimage f).fromSpec =
        (U.2.preimage f).fromSpec :=
      (V.2.preimage f).map_fromSpec (U.2.preimage f)
        ((Opens.map f.base).map ((Scheme.AffineZariskiSite.toOpensFunctor X).map a)).op
    rw [left, Category.assoc, natural, affineChartIso_inv_fromSpec]
  over U := by
    rw [← cancel_mono U.1.ι, Category.assoc, (ofAffine f).chartToBase_ι,
      ← recoverAffine_projection, chart_recoverAffine_assoc,
      affineChartIso_inv_fromSpec_assoc]
    exact (pullback.condition (f := f) (g := U.1.ι))

/-- The inverse map of the recovered affine scheme is obtained by gluing inverse chart maps. -/
def recoverAffineInv : Y ⟶ (ofAffine f).spec :=
  ((ofAffine f).glueCharts (affineChartMaps f)).left

@[reassoc (attr := simp)]
theorem f_recoverAffineInv (U : X.AffineZariskiSite) :
    (testCover f).f U ≫ recoverAffineInv f = (affineChartIso f U).inv ≫ (ofAffine f).chart U :=
  (ofAffine f).glueCharts_chart (affineChartMaps f) U

/-- Gluing the direct-image algebra recovers the affine morphism isomorphically. -/
def recoverAffineIso : (ofAffine f).spec ≅ Y where
  hom := recoverAffine f
  inv := recoverAffineInv f
  hom_inv_id := by
    apply (ofAffine f).gluingData.cover.hom_ext
    intro U
    change (ofAffine f).chart U ≫ recoverAffine f ≫ recoverAffineInv f = (ofAffine f).chart U ≫ 𝟙 _
    rw [chart_recoverAffine_assoc, ← affineChartIso_hom_f_assoc, f_recoverAffineInv, Iso.hom_inv_id_assoc,
      Category.comp_id]
  inv_hom_id := by
    apply (testCover f).hom_ext
    intro U
    rw [f_recoverAffineInv_assoc, chart_recoverAffine, affineChartIso_inv_fromSpec, Category.comp_id]

private instance pullback_affine (g : Y ⟶ X) : IsAffineHom (pullback.snd C.projection g) :=
  MorphismProperty.pullback_snd C.projection g inferInstance

/-- The algebra of the relative spectrum pulled back along an arbitrary map of schemes. -/
def baseChange (g : Y ⟶ X) : QuasiCoherentAlgebra Y :=
  ofAffine (pullback.snd C.projection g)

/-- The relative spectrum after base change is the actual scheme pullback. -/
def baseChangeIso (g : Y ⟶ X) :
    (C.baseChange g).spec ≅ pullback C.projection g :=
  recoverAffineIso (pullback.snd C.projection g)

/-- The base-change identification respects the new base scheme. -/
theorem baseChangeIso_hom (g : Y ⟶ X) :
    (C.baseChangeIso g).hom ≫ pullback.snd C.projection g = (C.baseChange g).projection :=
  recoverAffine_projection _

/-- The comparison with the scheme pullback also preserves the other leg. -/
theorem baseChange_isPullback (g : Y ⟶ X) :
    IsPullback ((C.baseChangeIso g).hom ≫ pullback.fst C.projection g)
      (C.baseChange g).projection C.projection g := by
  let e := C.baseChangeIso g
  refine (IsPullback.of_hasPullback C.projection g).of_iso e.symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
    ?_ ?_ ?_ ?_
  · simp [e]
  · rw [Iso.refl_hom, Category.comp_id, ← C.baseChangeIso_hom g]
    change pullback.snd C.projection g = e.inv ≫ e.hom ≫ pullback.snd C.projection g
    simp
  · simp
  · simp

/-- Map an affine open of the test scheme into an affine open of the base that contains its image. -/
def mapIntoOpen (g : Y ⟶ X) (U : X.AffineZariskiSite) (V : Y.AffineZariskiSite)
    (inside : V.1 ≤ g ⁻¹ᵁ U.1) : V.1.toScheme ⟶ U.1.toScheme :=
  Y.homOfLE inside ≫ g ∣_ U.1

@[reassoc (attr := simp)]
theorem mapIntoOpen_ι (g : Y ⟶ X) (U : X.AffineZariskiSite) (V : Y.AffineZariskiSite)
    (inside : V.1 ≤ g ⁻¹ᵁ U.1) : mapIntoOpen g U V inside ≫ U.1.ι = V.1.ι ≫ g := by
  simp [mapIntoOpen, morphismRestrict_ι]

/-- The map into a base chart corresponds to the actual restriction of its sections. -/
theorem mapIntoOpen_Spec (g : Y ⟶ X) (U : X.AffineZariskiSite) (V : Y.AffineZariskiSite)
    (inside : V.1 ≤ g ⁻¹ᵁ U.1) :
    mapIntoOpen g U V inside ≫ U.2.isoSpec.hom =
      V.2.isoSpec.hom ≫ Spec.map (g.appLE U.1 V.1 inside) := by
  have right : Spec.map (g.appLE U.1 V.1 inside) ≫ U.2.fromSpec = V.2.fromSpec ≫ g :=
    U.2.SpecMap_appLE_fromSpec g V.2 inside
  have chart (S : Scheme.{u}) (W : S.AffineZariskiSite) : W.2.isoSpec.hom ≫ W.2.fromSpec = W.1.ι := by
    change W.2.isoSpec.hom ≫ W.2.isoSpec.inv ≫ W.1.ι = W.1.ι
    exact W.2.isoSpec.hom_inv_id_assoc _
  rw [← cancel_mono U.2.fromSpec, Category.assoc, chart, mapIntoOpen_ι,
    Category.assoc, right, ← Category.assoc, chart]

/-- On affine opens the base-change chart is the pullback of the corresponding original chart. -/
def baseChangeChartIso (g : Y ⟶ X) (U : X.AffineZariskiSite) (V : Y.AffineZariskiSite)
    (inside : V.1 ≤ g ⁻¹ᵁ U.1) :
    Spec ((C.baseChange g).sections.obj (.op V)) ≅ pullback (C.chartToBase U) (mapIntoOpen g U V inside) := by
  let d := (C.baseChange g).isPullback_chart V |>.flip.paste_horiz (C.baseChange_isPullback g)
  let other := (IsPullback.of_hasPullback (C.chartToBase U) (mapIntoOpen g U V inside)).paste_horiz
    (C.isPullback_chart U).flip
  exact d.isoPullback ≪≫ (pullback.congrHom rfl (mapIntoOpen_ι g U V inside).symm) ≪≫ other.isoPullback.symm

/-- The affine algebra of a base-change chart is the tensor product of the two section algebras. -/
def baseChangeChartTensorIso (g : Y ⟶ X) (U : X.AffineZariskiSite) (V : Y.AffineZariskiSite)
    (inside : V.1 ≤ g ⁻¹ᵁ U.1) :
    letI : Algebra Γ(X, U.1) (C.sections.obj (.op U)) := (C.algebra.app (.op U)).hom.toAlgebra
    letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (g.appLE U.1 V.1 inside).hom.toAlgebra
    Spec ((C.baseChange g).sections.obj (.op V)) ≅
      Spec (CommRingCat.of (TensorProduct Γ(X, U.1) (C.sections.obj (.op U)) Γ(Y, V.1))) := by
  letI : Algebra Γ(X, U.1) (C.sections.obj (.op U)) := (C.algebra.app (.op U)).hom.toAlgebra
  letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (g.appLE U.1 V.1 inside).hom.toAlgebra
  let f := C.chartToBase U
  let h := mapIntoOpen g U V inside
  -- Use the same pullback cone but express both of its lower schemes as spectra.
  have cone : IsPullback (pullback.fst f h) (pullback.snd f h ≫ V.2.isoSpec.hom)
      (Spec.map (C.algebra.app (.op U))) (Spec.map (g.appLE U.1 V.1 inside)) :=
    (IsPullback.of_hasPullback f h).of_iso (Iso.refl _) (Iso.refl _) V.2.isoSpec U.2.isoSpec
      (by simp) (by simp) (by simp [f, chartToBase]) (mapIntoOpen_Spec g U V inside)
  exact C.baseChangeChartIso g U V inside ≪≫ cone.isoPullback ≪≫
    pullbackSpecIso Γ(X, U.1) (C.sections.obj (.op U)) Γ(Y, V.1)

/-- The coefficient ring on the pullback chart is the actual tensor product algebra. -/
def baseChangeChartRingIso (g : Y ⟶ X) (U : X.AffineZariskiSite) (V : Y.AffineZariskiSite)
    (inside : V.1 ≤ g ⁻¹ᵁ U.1) :
    letI : Algebra Γ(X, U.1) (C.sections.obj (.op U)) := (C.algebra.app (.op U)).hom.toAlgebra
    letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (g.appLE U.1 V.1 inside).hom.toAlgebra
    CommRingCat.of (TensorProduct Γ(X, U.1) (C.sections.obj (.op U)) Γ(Y, V.1)) ≅
      (C.baseChange g).sections.obj (.op V) where
  hom := Spec.preimage (C.baseChangeChartTensorIso g U V inside).hom
  inv := Spec.preimage (C.baseChangeChartTensorIso g U V inside).inv
  hom_inv_id := by rw [← Spec.preimage_comp, Iso.inv_hom_id, Spec.preimage_id]
  inv_hom_id := by rw [← Spec.preimage_comp, Iso.hom_inv_id, Spec.preimage_id]

/-- A map to the relative spectrum over the new base is the same map over the original base. -/
def homEquivBaseChange (f : Y ⟶ X) {Z : Scheme.{u}} (g : Z ⟶ Y) :
    (Over.mk g ⟶ Over.mk (C.baseChange f).projection) ≃ (Over.mk (g ≫ f) ⟶ Over.mk C.projection) where
  toFun h := Over.homMk (h.left ≫ (C.baseChangeIso f).hom ≫ pullback.fst C.projection f) (by
    change (h.left ≫ (C.baseChangeIso f).hom ≫ pullback.fst C.projection f) ≫ C.projection = g ≫ f
    calc
      _ = h.left ≫ ((C.baseChangeIso f).hom ≫ pullback.snd C.projection f) ≫ f := by
        simp only [Category.assoc, pullback.condition]
      _ = g ≫ f := by
        rw [C.baseChangeIso_hom, ← Category.assoc]
        exact congrArg (· ≫ f) (Over.w h))
  invFun h := Over.homMk ((C.baseChange_isPullback f).lift h.left g (Over.w h))
    (IsPullback.lift_snd _ _ _ _)
  left_inv h := by
    apply Over.OverMorphism.ext
    apply (C.baseChange_isPullback f).hom_ext
    · exact IsPullback.lift_fst _ _ _ _
    · exact (IsPullback.lift_snd _ _ _ _).trans (Over.w h).symm
  right_inv h := by
    apply Over.OverMorphism.ext
    exact IsPullback.lift_fst _ _ _ _


/-- Direct images along two structure maps compose over the original structure sheaf. -/
def directImageStructure_comp (f : Y ⟶ X) {Z : Scheme.{u}} (g : Z ⟶ Y) :
    (pushforwardAlgebra f).obj (directImageStructure g) ≅ directImageStructure (g ≫ f) := by
  refine Under.isoMk (Iso.refl _) ?_
  apply Sheaf.hom_ext
  ext1
  funext U
  rfl

/-- Under arbitrary base change the pullback represents the pulled-back algebra on every test scheme. -/
def homEquivBaseChangeAlgebraSheaf (f : Y ⟶ X) {Z : Scheme.{u}} (g : Z ⟶ Y) :
    (Over.mk g ⟶ Over.mk (C.baseChange f).projection) ≃
      ((pullbackAlgebra g).obj ((pullbackAlgebra f).obj C.algebraSheaf) ⟶ Under.mk (𝟙 Z.sheaf)) :=
  (C.homEquivBaseChange f g).trans
    ((C.homEquivDirectImage.trans C.directImageMapsEquivSheaves).trans
      (((directImageStructure_comp f g).homToEquiv.symm).trans
        (((pullbackAlgebraAdjunction f).homEquiv C.algebraSheaf (directImageStructure g)).symm.trans
          (pullbackAlgebraHomEquiv g _).symm)))

end QuasiCoherentAlgebra

end

end SHIGURE.SchemeDescent
