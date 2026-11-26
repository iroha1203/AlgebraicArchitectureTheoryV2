import Formal.SHIGURE.Part2.Schemes.AffineFppfRefinement
import Formal.SHIGURE.Part2.Schemes.FiniteLocallyFreeAffineOpens
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # Reflection of finite local freeness on fppf covers -/

namespace SHIGURE.SchemeDescent

open AlgebraicGeometry CategoryTheory Scheme.Modules TopologicalSpace
open SHIGURE.CoefficientDescent

noncomputable section

universe u

variable {X Y : Scheme.{u}} {M : X.Modules}

/-- A pointwise lifting on the affine opens gives surjectivity for the
spectrum of the actual map of section rings. -/
private theorem specMap_appLE_surjective (f : Y ⟶ X) {U : X.Opens} {V : Y.Opens}
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (inside : V ≤ f ⁻¹ᵁ U)
    (onto : ∀ x ∈ U, ∃ y ∈ V, f y = x) :
    Surjective (Spec.map (f.appLE U V inside)) := by
  constructor
  intro x
  have hx : hU.fromSpec x ∈ U := hU.range_fromSpec.le ⟨x, rfl⟩
  obtain ⟨y, hyV, hy⟩ := onto (hU.fromSpec x) hx
  have hyRange : y ∈ Set.range hV.fromSpec := by rw [hV.range_fromSpec]; exact hyV
  obtain ⟨z, hz⟩ := hyRange
  refine ⟨z, hU.fromSpec.isOpenEmbedding.injective ?_⟩
  rw [← Scheme.Hom.comp_apply, IsAffineOpen.SpecMap_appLE_fromSpec f hU hV inside,
    Scheme.Hom.comp_apply, hz, hy]

/-- For an affine chart mapping onto a base open, flatness gives a faithfully
flat section map. B.5 reflects finite local freeness across that map. -/
private theorem HasFiniteLocallyFreeOn.of_faithfullyFlat_chart
    (f : Y ⟶ X) [Flat f] {U : X.Opens} {V : Y.Opens}
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (inside : V ≤ f ⁻¹ᵁ U)
    (onto : ∀ x ∈ U, ∃ y ∈ V, f y = x)
    (presentation : HasTildeOn M hU)
    (localized : HasFiniteLocallyFreeOn ((Scheme.Modules.pullback f).obj M) hV) :
    HasFiniteLocallyFreeOn M hU := by
  let a := f.appLE U V inside
  have flat : a.hom.Flat := f.flat_appLE hU hV inside
  have faithfullyFlat : a.hom.FaithfullyFlat := (flat_and_surjective_SpecMap_iff a).1
    ⟨(HasRingHomProperty.Spec_iff (P := @Flat)).2 flat, specMap_appLE_surjective f hU hV inside onto⟩
  letI : Algebra Γ(X, U) Γ(Y, V) := a.hom.toAlgebra
  have faithful : Module.FaithfullyFlat Γ(X, U) Γ(Y, V) :=
    RingHom.faithfullyFlat_algebraMap_iff.1 faithfullyFlat
  obtain ⟨N, ⟨e⟩⟩ := presentation
  obtain ⟨P, finite, ⟨k⟩⟩ := localized
  let e' := pullbackTildePresentationIso (hV := hV) inside e
  let coefficients := (tilde.fullyFaithfulFunctor (R := Γ(Y, V))).preimageIso (k ≪≫ e'.symm)
  have finiteAfter : FiniteLocallyFree Γ(Y, V) ((ModuleCat.extendScalars a.hom).obj N) :=
    finiteLocallyFree_of_moduleIso coefficients finite
  exact ⟨N, finiteLocallyFree_of_faithfullyFlat_extendScalars a N faithful finiteAfter, ⟨e⟩⟩

/-- The map of the two given affine charts is affine, so the inverse image
of a smaller affine base open is affine within the source chart. -/
private theorem affine_inter_preimage_of_maps_into_affine
    (f : Y ⟶ X) {U W : X.Opens} {V : Y.Opens} (hU : IsAffineOpen U) (hW : IsAffineOpen W)
    (hV : IsAffineOpen V) (inside : V ≤ f ⁻¹ᵁ U) (within : W ≤ U) :
    IsAffineOpen (V ⊓ f ⁻¹ᵁ W) := by
  have hW' : IsAffineOpen (hU.fromSpec ⁻¹ᵁ W) :=
    hW.preimage_of_isOpenImmersion hU.fromSpec (hU.opensRange_fromSpec.symm ▸ within)
  let a := f.appLE U V inside
  have affine : IsAffineOpen (hV.fromSpec ''ᵁ ((Spec.map a) ⁻¹ᵁ (hU.fromSpec ⁻¹ᵁ W))) :=
    (hW'.preimage (Spec.map a)).image_of_isOpenImmersion hV.fromSpec
  rw [← Scheme.Hom.comp_preimage, IsAffineOpen.SpecMap_appLE_fromSpec f hU hV inside,
    Scheme.Hom.comp_preimage, hV.fromSpec.image_preimage_eq_opensRange_inf, hV.opensRange_fromSpec] at affine
  exact affine

/-- For B.3, finite local freeness of a quasi-coherent module can be checked
on the components of any fppf cover. The open image of a source chart gives
a base chart on which the actual section map is faithfully flat. -/
theorem isFiniteLocallyFreeModule_of_fppfCover (cover : FppfCover X) (coherent : IsQuasiCoherentModule M)
    (localFree : ∀ i, IsFiniteLocallyFreeModule ((Scheme.Modules.pullback (cover.f i)).obj M)) :
    IsFiniteLocallyFreeModule M := by
  let I := {U : X.affineOpens // HasFiniteLocallyFreeOn M U.property}
  refine ⟨I, Subtype.val, ?_, fun i => i.property⟩
  apply top_le_iff.mp
  intro x _
  let i := cover.idx x
  let f := cover.f i
  letI : Flat f := (cover.map_prop i).1
  letI : LocallyOfFinitePresentation f := (cover.map_prop i).2
  obtain ⟨y, hy⟩ := cover.covers x
  obtain ⟨U, hxU⟩ := Opens.mem_iSup.mp ((iSup_affineOpens_eq_top X).ge (Set.mem_univ x))
  have hyU : y ∈ f ⁻¹ᵁ U.1 := by
    change f y ∈ U.1
    rw [hy]
    exact hxU
  obtain ⟨_, ⟨V, hV, rfl⟩, hyV, hVU⟩ :=
    (cover.X i).isBasis_affineOpens.exists_subset_of_mem_open hyU (f ⁻¹ᵁ U.1).isOpen
  let image : X.Opens := ⟨f '' (V : Set (cover.X i)), f.isOpenMap _ V.isOpen⟩
  have hxImage : x ∈ image := ⟨y, hyV, hy⟩
  have imageInside : image ≤ U.1 := by
    rintro _ ⟨y', hy'V, rfl⟩
    exact hVU hy'V
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWImage⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxImage image.isOpen
  let V' := V ⊓ f ⁻¹ᵁ W
  have hV' : IsAffineOpen V' := affine_inter_preimage_of_maps_into_affine f U.property hW hV hVU
    (hWImage.trans imageInside)
  have onto : ∀ t ∈ W, ∃ y' ∈ V', f y' = t := by
    intro t ht
    obtain ⟨y', hy'V, hy'⟩ := hWImage ht
    refine ⟨y', ⟨hy'V, ?_⟩, hy'⟩
    change f y' ∈ W
    rwa [hy']
  have onV' := (isFiniteLocallyFreeModule_iff_on_affineOpens.mp (localFree i)) ⟨V', hV'⟩
  have onW := HasFiniteLocallyFreeOn.of_faithfullyFlat_chart f hW hV' inf_le_right onto
    (coherent ⟨W, hW⟩) onV'
  exact Opens.mem_iSup.mpr ⟨⟨⟨W, hW⟩, onW⟩, hxW⟩

end

end SHIGURE.SchemeDescent
