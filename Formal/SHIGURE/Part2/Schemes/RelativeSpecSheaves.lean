import Formal.SHIGURE.Part2.Schemes.RelativeSpec
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.CategoryTheory.Sites.Limits

/-! # Relative spectra and algebra sheaves

The localization data on the small affine Zariski site give a sheaf of
algebras. Comparison with the affine charts identifies maps of those
algebras with maps of sheaves on all opens. The sheaf adjunction then
gives the relative spectrum's representing equivalence over every test
scheme.
-/

namespace SHIGURE.SchemeDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

noncomputable section

universe u

namespace QuasiCoherentAlgebra

variable {X Y : Scheme.{u}} (C : QuasiCoherentAlgebra X) {g : Y ⟶ X}

/-- The structure ring on each inverse image affine open of the base. -/
def directImageSections (f : Y ⟶ X) : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat :=
  (Scheme.AffineZariskiSite.toOpensFunctor X).op ⋙ (Opens.map f.base).op ⋙ Y.presheaf

/-- The base structure sheaf maps to the direct image via pullback of functions. -/
def directImageAlgebra (f : Y ⟶ X) :
    (Scheme.AffineZariskiSite.toOpensFunctor X).op ⋙ X.presheaf ⟶ directImageSections f where
  app U := f.app U.unop.1
  naturality _ _ j := f.naturality ((Scheme.AffineZariskiSite.toOpensFunctor X).op.map j)

/-- The test chart is the open subscheme of the inverse image. -/
def testChartOpenIso (g : Y ⟶ X) (U : X.AffineZariskiSite) :
    (testCover g).X U ≅ (g ⁻¹ᵁ U.1).toScheme :=
  IsOpenImmersion.isoOfRangeEq ((testCover g).f U) (g ⁻¹ᵁ U.1).ι <| by
    change Set.range (pullback.fst g U.1.ι) = Set.range ((g ⁻¹ᵁ U.1).ι)
    rw [Scheme.Pullback.range_fst, Scheme.Opens.range_ι, Scheme.Opens.range_ι]
    rfl

@[reassoc (attr := simp)]
theorem testChartOpenIso_hom_ι (g : Y ⟶ X) (U : X.AffineZariskiSite) :
    (testChartOpenIso g U).hom ≫ (g ⁻¹ᵁ U.1).ι = (testCover g).f U :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

/-- Global sections of a test chart are the sections over the inverse image open. -/
def testChartSectionsIso (g : Y ⟶ X) (U : X.AffineZariskiSite) :
    Γ(Y, g ⁻¹ᵁ U.1) ≅ Γ((testCover g).X U, ⊤) :=
  (g ⁻¹ᵁ U.1).topIso.symm ≪≫ Scheme.Γ.mapIso (testChartOpenIso g U).op

/-- The canonical maps to the base open agree with scheme restriction. -/
theorem testChartOpenIso_morphismRestrict (g : Y ⟶ X) (U : X.AffineZariskiSite) :
    (testChartOpenIso g U).hom ≫ g ∣_ U.1 = testToBase g U := by
  rw [← cancel_mono U.1.ι, Category.assoc, morphismRestrict_ι, testChartOpenIso_hom_ι_assoc]
  exact pullback.condition

private theorem specGlobalHom_toSpecΓ (S : Scheme.{u}) :
    specGlobalHom S.toSpecΓ = 𝟙 Γ(S, ⊤) := by
  apply (specGlobalHom (X := S) (B := Γ(S, ⊤))).symm.injective
  rw [Equiv.symm_apply_apply]
  change S.toSpecΓ = (ΓSpec.adjunction.homEquiv S (op Γ(S, ⊤))) (𝟙 Γ(S, ⊤)).op
  rw [Adjunction.homEquiv_apply]
  change S.toSpecΓ = ΓSpec.adjunction.unit.app S ≫ Scheme.Spec.map (𝟙 (op Γ(S, ⊤)))
  rw [show Scheme.Spec.map (𝟙 (op Γ(S, ⊤))) = 𝟙 _ from Scheme.Spec.map_id _]
  exact (Category.comp_id (ΓSpec.adjunction.unit.app S)).symm

/-- The algebra action induced on each test chart is the pullback of the base functions there. -/
theorem testChartSectionsIso_baseSectionMap (g : Y ⟶ X) (U : X.AffineZariskiSite) :
    g.app U.1 ≫ (testChartSectionsIso g U).hom = baseSectionMap g U := by
  rw [baseSectionMap, ← testChartOpenIso_morphismRestrict, Category.assoc, specGlobalHom_precomp]
  have formula : specGlobalHom ((g ∣_ U.1) ≫ U.2.isoSpec.hom) =
      g.app U.1 ≫ (g ⁻¹ᵁ U.1).topIso.inv := by
    rw [IsAffineOpen.isoSpec_hom, Scheme.Opens.toSpecΓ, ← Category.assoc, specGlobalHom_postcomp,
      specGlobalHom_precomp, specGlobalHom_toSpecΓ, Category.id_comp]
    change U.1.topIso.inv ≫ (g ∣_ U.1).appTop = _
    rw [morphismRestrict_appTop]
    simp only [Scheme.Opens.topIso, Functor.mapIso_inv]
    let j : op U.1 ⟶ op (U.1.ι ''ᵁ ⊤) := (eqToIso U.1.ι_image_top.symm).op.inv
    have natural := g.naturality j
    rw [← Category.assoc, natural, Category.assoc, ← Functor.map_comp]
    congr 2
  rw [formula]
  rfl


private def preimageOpenMap (g : Y ⟶ X) {U V : X.AffineZariskiSite} (a : U ⟶ V) :
    (g ⁻¹ᵁ U.1) ⟶ (g ⁻¹ᵁ V.1) :=
  (Opens.map g.base).map ((Scheme.AffineZariskiSite.toOpensFunctor X).map a)

private theorem testChartOpenIso_trans (g : Y ⟶ X) {U V : X.AffineZariskiSite} (a : U ⟶ V) :
    (testCover g).trans a ≫ (testChartOpenIso g V).hom =
      (testChartOpenIso g U).hom ≫ Y.homOfLE (preimageOpenMap g a).le := by
  rw [← cancel_mono (g ⁻¹ᵁ V.1).ι]
  calc
    _ = (testCover g).f U := by
      rw [Category.assoc, testChartOpenIso_hom_ι, Scheme.Cover.trans_map]
    _ = _ := by
      rw [Category.assoc, Scheme.homOfLE_ι, testChartOpenIso_hom_ι]

/-- Sections of inverse image opens and global sections of the test charts restrict identically. -/
theorem testChartSectionsIso_naturality (g : Y ⟶ X) {U V : X.AffineZariskiSite} (a : U ⟶ V) :
    (directImageSections g).map a.op ≫ (testChartSectionsIso g U).hom =
      (testChartSectionsIso g V).hom ≫ ((testCover g).trans a).appTop := by
  change Y.presheaf.map (preimageOpenMap g a).op ≫ (g ⁻¹ᵁ U.1).topIso.inv ≫
      (testChartOpenIso g U).hom.appTop =
    ((g ⁻¹ᵁ V.1).topIso.inv ≫ (testChartOpenIso g V).hom.appTop) ≫ ((testCover g).trans a).appTop
  rw [← Category.assoc]
  have openMap := Y.restrictFunctorΓ.inv.naturality (preimageOpenMap g a).op
  change Y.presheaf.map (preimageOpenMap g a).op ≫ (g ⁻¹ᵁ U.1).topIso.inv =
    (g ⁻¹ᵁ V.1).topIso.inv ≫ (Y.homOfLE (preimageOpenMap g a).le).appTop at openMap
  rw [openMap, Category.assoc, Category.assoc, ← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop,
    testChartOpenIso_trans]

/-- Maps of the coefficient algebra into the direct image of the test structure sheaf. -/
abbrev DirectImageMaps (g : Y ⟶ X) :=
  {a : C.sections ⟶ directImageSections g // C.algebra ≫ a = directImageAlgebra g}

/-- Identify chart algebra maps with algebra maps on the entire affine site. -/
def chartAlgebraMapsEquivDirectImage : C.ChartAlgebraMaps g ≃ C.DirectImageMaps g where
  toFun a :=
    ⟨{
      app U := a.app U.unop ≫ (testChartSectionsIso g U.unop).inv
      naturality {U V} f := by
        rw [← cancel_mono (testChartSectionsIso g V.unop).hom]
        simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
        have natural : (directImageSections g).map f ≫ (testChartSectionsIso g V.unop).hom =
            (testChartSectionsIso g U.unop).hom ≫ ((testCover g).trans f.unop).appTop := by
          simpa only [Quiver.Hom.op_unop] using testChartSectionsIso_naturality g f.unop
        rw [natural, Iso.inv_hom_id_assoc]
        simpa only [Quiver.Hom.op_unop] using a.naturality f.unop
    }, by
      ext1
      funext U
      change C.algebra.app U ≫ a.app U.unop ≫ (testChartSectionsIso g U.unop).inv = g.app U.unop.1
      rw [← Category.assoc, a.over, ← testChartSectionsIso_baseSectionMap, Category.assoc, Iso.hom_inv_id,
        Category.comp_id]⟩
  invFun a :=
    { app U := a.val.app (.op U) ≫ (testChartSectionsIso g U).hom
      naturality {U V} f := by
        rw [← Category.assoc, a.val.naturality, Category.assoc, testChartSectionsIso_naturality,
          Category.assoc]
      over U := by
        rw [← Category.assoc]
        change (C.algebra ≫ a.val).app (.op U) ≫ _ = _
        rw [a.property]
        exact testChartSectionsIso_baseSectionMap g U }
  left_inv a := by
    apply ChartAlgebraMaps.ext
    funext U
    change (a.app U ≫ (testChartSectionsIso g U).inv) ≫ (testChartSectionsIso g U).hom = a.app U
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  right_inv a := by
    apply Subtype.ext
    ext1
    funext U
    change (a.val.app U ≫ (testChartSectionsIso g U.unop).hom) ≫ (testChartSectionsIso g U.unop).inv = _
    rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The relative spectrum represents maps of the coefficient algebra into direct-image functions. -/
def homEquivDirectImage : (Over.mk g ⟶ Over.mk C.projection) ≃ C.DirectImageMaps g :=
  C.homEquivAlgebraMaps.trans C.chartAlgebraMapsEquivDirectImage

/-- The original chart is the spectrum of the functions on its whole inverse image. -/
def chartSpectrumIso (U : X.AffineZariskiSite) :
    Spec (C.sections.obj (.op U)) ≅ Spec Γ(C.spec, C.projection ⁻¹ᵁ U.1) :=
  IsOpenImmersion.isoOfRangeEq (C.chart U) (U.2.preimage C.projection).fromSpec <| by
    rw [(U.2.preimage C.projection).range_fromSpec, C.preimage_eq_chart]
    rfl

@[reassoc (attr := simp)]
theorem chartSpectrumIso_fromSpec (U : X.AffineZariskiSite) :
    (C.chartSpectrumIso U).hom ≫ (U.2.preimage C.projection).fromSpec = C.chart U :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

/-- Compare the direct image of the structure sheaf with the original algebra on the affine site. -/
def sectionsIsoDirectImage : directImageSections C.projection ≅ C.sections :=
  NatIso.ofComponents (fun U =>
    { hom := Spec.preimage (C.chartSpectrumIso U.unop).hom
      inv := Spec.preimage (C.chartSpectrumIso U.unop).inv
      hom_inv_id := by rw [← Spec.preimage_comp, Iso.inv_hom_id, Spec.preimage_id]
      inv_hom_id := by rw [← Spec.preimage_comp, Iso.hom_inv_id, Spec.preimage_id] }) (by
    intro V U a
    apply Spec.map_injective
    simp only [Spec.map_comp, Spec.map_preimage]
    change (C.chartSpectrumIso U.unop).hom ≫ Spec.map ((directImageSections C.projection).map a) =
      Spec.map (C.sections.map a) ≫ (C.chartSpectrumIso V.unop).hom
    rw [← cancel_mono (V.unop.2.preimage C.projection).fromSpec]
    have natural : Spec.map ((directImageSections C.projection).map a) ≫
        (V.unop.2.preimage C.projection).fromSpec = (U.unop.2.preimage C.projection).fromSpec :=
      (V.unop.2.preimage C.projection).map_fromSpec (U.unop.2.preimage C.projection)
        ((Opens.map C.projection.base).map ((Scheme.AffineZariskiSite.toOpensFunctor X).map a.unop)).op
    rw [Category.assoc, natural, chartSpectrumIso_fromSpec, Category.assoc, chartSpectrumIso_fromSpec]
    exact (C.chart_naturality a.unop).symm)

/-- The recovered functions have the original action of the base structure sheaf. -/
theorem sectionsIsoDirectImage_algebra :
    directImageAlgebra C.projection ≫ C.sectionsIsoDirectImage.hom = C.algebra := by
  ext1
  funext U
  apply Spec.map_injective
  simp only [NatTrans.comp_app, Spec.map_comp, sectionsIsoDirectImage, NatIso.ofComponents_hom_app,
    Spec.map_preimage]
  change (C.chartSpectrumIso U.unop).hom ≫ Spec.map (C.projection.app U.unop.1) =
    Spec.map (C.algebra.app U)
  rw [← cancel_mono U.unop.2.fromSpec, Category.assoc]
  have compat : Spec.map (C.projection.app U.unop.1) ≫ U.unop.2.fromSpec =
      (U.unop.2.preimage C.projection).fromSpec ≫ C.projection := by
    simpa only [Scheme.Hom.appLE_eq_app] using
      U.unop.2.SpecMap_appLE_fromSpec C.projection (U.unop.2.preimage C.projection) (i := le_rfl)
  rw [compat, chartSpectrumIso_fromSpec_assoc, C.chart_projection]

end QuasiCoherentAlgebra

section AlgebraSheaves

variable {X Y : Scheme.{u}}

/-- The pushforward structure sheaf viewed as an algebra over the base structure sheaf. -/
def directImageStructure (g : Y ⟶ X) : Under X.sheaf :=
  Under.mk (Y := (TopCat.Sheaf.pushforward CommRingCat g.base).obj Y.sheaf) ⟨g.c⟩

/-- The algebra sheaf associated to the local rings of the quasi-coherent algebra. -/
def QuasiCoherentAlgebra.algebraSheaf (C : QuasiCoherentAlgebra X) : Under X.sheaf :=
  directImageStructure C.projection

/-- The pullback of the structure sheaf maps to the actual structure sheaf of the source. -/
def pullbackStructureHom (g : Y ⟶ X) :
    (TopCat.Sheaf.pullback CommRingCat g.base).obj X.sheaf ⟶ Y.sheaf :=
  ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat g.base).homEquiv X.sheaf Y.sheaf).symm
    (directImageStructure g).hom

/-- Pullback of algebras is inverse image of sheaves followed by extension of scalars. -/
def pullbackAlgebra (g : Y ⟶ X) : Under X.sheaf ⥤ Under Y.sheaf := by
  letI : HasPushoutsAlong (pullbackStructureHom g) := by
    intro W h
    change @HasPushout (Sheaf (Opens.grothendieckTopology (Y : TopCat)) CommRingCat) _ _ _ _ h
      (pullbackStructureHom g)
    infer_instance
  exact Under.post (TopCat.Sheaf.pullback CommRingCat g.base) ⋙ Under.pushout (pullbackStructureHom g)

/-- Direct image of algebra sheaves, with the base structure sheaf acting by pullback of functions. -/
def pushforwardAlgebra (g : Y ⟶ X) : Under Y.sheaf ⥤ Under X.sheaf :=
  Under.post (TopCat.Sheaf.pushforward CommRingCat g.base) ⋙ Under.map (directImageStructure g).hom

/-- The algebra pullback is left adjoint to the direct image with its base ring action. -/
def pullbackAlgebraAdjunction (g : Y ⟶ X) :
    pullbackAlgebra g ⊣ pushforwardAlgebra g := by
  letI : HasPushoutsAlong (pullbackStructureHom g) := by
    intro W h
    change @HasPushout (Sheaf (Opens.grothendieckTopology (Y : TopCat)) CommRingCat) _ _ _ _ h
      (pullbackStructureHom g)
    infer_instance
  let adj := TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat g.base
  refine ((Under.postAdjunctionLeft adj).comp (Under.mapPushoutAdj (pullbackStructureHom g))).ofNatIsoRight ?_
  refine NatIso.ofComponents (fun B => Under.isoMk (Iso.refl _) ?_) ?_
  · change (adj.unit.app X.sheaf ≫ (TopCat.Sheaf.pushforward CommRingCat g.base).map
      (pullbackStructureHom g ≫ B.hom)) ≫ 𝟙 _ = _
    simp only [Category.comp_id, Functor.map_comp, ← Category.assoc]
    change adj.homEquiv X.sheaf Y.sheaf (pullbackStructureHom g) ≫ _ = _
    simp [pullbackStructureHom, adj, pushforwardAlgebra]
  · intro B B' f
    ext
    simp [pushforwardAlgebra]

/-- Algebra maps into the test structure sheaf are adjoint to maps into its direct image. -/
def pullbackAlgebraHomEquiv (g : Y ⟶ X) (D : Under X.sheaf) :
    ((pullbackAlgebra g).obj D ⟶ Under.mk (𝟙 Y.sheaf)) ≃ (D ⟶ directImageStructure g) := by
  refine ((pullbackAlgebraAdjunction g).homEquiv D (Under.mk (𝟙 Y.sheaf))).trans ?_
  refine (Under.isoMk (Iso.refl _) ?_).homToEquiv
  change ((directImageStructure g).hom ≫ (TopCat.Sheaf.pushforward CommRingCat g.base).map
    (𝟙 Y.sheaf)) ≫ 𝟙 _ = (directImageStructure g).hom
  rw [Category.comp_id]
  rw [show (TopCat.Sheaf.pushforward CommRingCat g.base).map (𝟙 Y.sheaf) = 𝟙 _ from
    (TopCat.Sheaf.pushforward CommRingCat g.base).map_id _]
  exact Category.comp_id _

namespace QuasiCoherentAlgebra

private abbrev affineSiteSheafEquivalence (X : Scheme.{u}) :=
  Scheme.AffineZariskiSite.sheafEquiv (X := X) (A := CommRingCat.{u})

variable (C : QuasiCoherentAlgebra X) {g : Y ⟶ X}

/-- The local coefficient sections satisfy the sheaf condition on the affine site. -/
def affineSectionsSheaf : Sheaf (Scheme.AffineZariskiSite.grothendieckTopology X) CommRingCat where
  val := C.sections
  cond := (Presheaf.isSheaf_of_iso_iff C.sectionsIsoDirectImage).1
    ((affineSiteSheafEquivalence X).inverse.obj C.algebraSheaf.right).cond

/-- The local algebra as an algebra under the restriction of the base structure sheaf. -/
def affineAlgebraSheaf : Under ((affineSiteSheafEquivalence X).inverse.obj X.sheaf) :=
  Under.mk (Y := C.affineSectionsSheaf) ⟨C.algebra⟩

/-- Restricting the reconstructed algebra sheaf gives the prescribed local algebra. -/
def affineAlgebraSheafIso :
    (Under.post (affineSiteSheafEquivalence X).inverse).obj C.algebraSheaf ≅ C.affineAlgebraSheaf :=
  Under.isoMk
    { hom := ⟨C.sectionsIsoDirectImage.hom⟩
      inv := ⟨C.sectionsIsoDirectImage.inv⟩
      hom_inv_id := Sheaf.hom_ext _ _ C.sectionsIsoDirectImage.hom_inv_id
      inv_hom_id := Sheaf.hom_ext _ _ C.sectionsIsoDirectImage.inv_hom_id }
    (Sheaf.hom_ext _ _ C.sectionsIsoDirectImage_algebra)

/-- The compatible algebra maps on the small site are precisely the maps of its algebra sheaves. -/
def directImageMapsEquivAffineSheaf :
    C.DirectImageMaps g ≃
      (C.affineAlgebraSheaf ⟶ (Under.post (affineSiteSheafEquivalence X).inverse).obj (directImageStructure g)) where
  toFun a := Under.homMk ⟨a.val⟩ (Sheaf.hom_ext _ _ a.property)
  invFun a := ⟨a.right.val, congrArg Sheaf.Hom.val (Under.w a)⟩
  left_inv a := rfl
  right_inv a := by
    apply Under.UnderMorphism.ext
    exact Sheaf.hom_ext _ _ rfl

/-- The comparison of sheaves on the affine site and all opens preserves the algebra maps. -/
def directImageMapsEquivSheaves :
    C.DirectImageMaps g ≃ (C.algebraSheaf ⟶ directImageStructure g) :=
  C.directImageMapsEquivAffineSheaf.trans
    (C.affineAlgebraSheafIso.symm.homFromEquiv.trans
      ((Functor.FullyFaithful.under X.sheaf (affineSiteSheafEquivalence X).inverse
        (affineSiteSheafEquivalence X).fullyFaithfulInverse).homEquiv).symm)

/-- The relative spectrum represents maps from the pulled-back algebra to the test structure sheaf. -/
def homEquivAlgebraSheaf :
    (Over.mk g ⟶ Over.mk C.projection) ≃
      ((pullbackAlgebra g).obj C.algebraSheaf ⟶ Under.mk (𝟙 Y.sheaf)) :=
  (C.homEquivDirectImage.trans C.directImageMapsEquivSheaves).trans
    (pullbackAlgebraHomEquiv g C.algebraSheaf).symm

/-- Read a morphism from the pulled-back algebra on each affine chart of the test scheme. -/
def algebraSheafMapSections :=
  (pullbackAlgebraHomEquiv g C.algebraSheaf).trans
    (C.directImageMapsEquivSheaves.symm.trans C.chartAlgebraMapsEquivDirectImage.symm)

/-- In chart sections the sheaf-valued representing equivalence is ordinary pullback of functions. -/
theorem homEquivAlgebraSheaf_precomp {Y' : Scheme.{u}} {g' : Y' ⟶ X}
    (t : Over.mk g' ⟶ Over.mk g) (h : Over.mk g ⟶ Over.mk C.projection) (U : X.AffineZariskiSite) :
    (C.algebraSheafMapSections ((C.homEquivAlgebraSheaf (g := g')) (t ≫ h))).app U =
      (C.algebraSheafMapSections (C.homEquivAlgebraSheaf h)).app U ≫ (testChartMap t U).appTop := by
  have cancel (V : Scheme.{u}) (i : V ⟶ X) (a : Over.mk i ⟶ Over.mk C.projection) :
      C.algebraSheafMapSections (C.homEquivAlgebraSheaf a) = C.homEquivAlgebraMaps a := by
    simp [algebraSheafMapSections, homEquivAlgebraSheaf, homEquivDirectImage]
  rw [cancel, cancel]
  exact C.homEquivAlgebraMaps_precomp t h U
end QuasiCoherentAlgebra

end AlgebraSheaves

end

end SHIGURE.SchemeDescent
