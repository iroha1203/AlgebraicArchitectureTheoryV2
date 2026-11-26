import Formal.SHIGURE.Part2.Schemes.AlgebraSheafStalks
import Formal.SHIGURE.Part2.Schemes.AffinePushforwardStalk

/-! # Base change of the algebra sheaf of a relative spectrum

On affine opens the pullback square gives the tensor pushout of functions
with both structure maps. Localizing at a base point and using the stalk
formula for the inverse image identifies the corresponding sheaf pushout.
-/

namespace SHIGURE.SchemeDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

noncomputable section

universe u

section AffinePullback

variable {X Y Z W : Scheme.{u}} {f : Y ⟶ X} {h : Z ⟶ X} {left : W ⟶ Z} {down : W ⟶ Y}
  (square : IsPullback left down h f)

private def affinePullbackDirectImageMap :
    directImageStructure h ⟶ (pushforwardAlgebra f).obj (directImageStructure down) :=
  directImageStructureMap (Over.homMk left square.w : Over.mk (down ≫ f) ⟶ Over.mk h) ≫
    (QuasiCoherentAlgebra.directImageStructure_comp f down).inv

/-- The first leg of an affine pullback induces a map from the inverse image of its algebra sheaf. -/
def affinePullbackMate :
    (TopCat.Sheaf.pullback CommRingCat f.base).obj (directImageStructure h).right ⟶
      (directImageStructure down).right :=
  ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat f.base).homEquiv _ _).symm
    (affinePullbackDirectImageMap square).right

private theorem affinePullbackMate_comm :
    (TopCat.Sheaf.pullback CommRingCat f.base).map (directImageStructure h).hom ≫ affinePullbackMate square =
      pullbackStructureHom f ≫ (directImageStructure down).hom := by
  let adj := TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat f.base
  apply (adj.homEquiv X.sheaf (directImageStructure down).right).injective
  rw [adj.homEquiv_naturality_left, adj.homEquiv_naturality_right]
  unfold affinePullbackMate pullbackStructureHom
  change (directImageStructure h).hom ≫
    adj.homEquiv _ _ ((adj.homEquiv _ _).symm (affinePullbackDirectImageMap square).right) =
      adj.homEquiv _ _ ((adj.homEquiv _ _).symm (directImageStructure f).hom) ≫ _
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  exact Under.w (affinePullbackDirectImageMap square)

private theorem affinePullbackDirectImageMap_app (U : X.Opens) :
    (affinePullbackDirectImageMap square).right.val.app (.op U) =
      left.appLE (h ⁻¹ᵁ U) (down ⁻¹ᵁ (f ⁻¹ᵁ U)) (by
        rw [← Scheme.Hom.comp_preimage left h, square.w, Scheme.Hom.comp_preimage down f]) := by
  change _ ≫ 𝟙 _ = _
  exact Category.comp_id _

variable [IsAffineHom h]

private theorem affinePullbackStalk_isPushout (y : Y) :
    IsPushout
      ((ringSheafStalk (f y)).map (directImageStructure h).hom)
      (directImageStalkMap f.base (directImageStructure f).hom y)
      (directImageStalkMap f.base (affinePullbackDirectImageMap square).right y)
      ((ringSheafStalk y).map (directImageStructure down).hom) := by
  obtain ⟨U, affineU, yU, _⟩ := exists_isAffineOpen_mem_and_subset (show f y ∈ (⊤ : X.Opens) by trivial)
  obtain ⟨V, affineV, yV, inside⟩ := exists_isAffineOpen_mem_and_subset (show y ∈ f ⁻¹ᵁ U from yU)
  let U' : X.AffineZariskiSite := ⟨U, affineU⟩
  let V' : Y.AffineZariskiSite := ⟨V, affineV⟩
  haveI : IsAffineHom down := MorphismProperty.of_isPullback square inferInstance
  let SX : (X : TopCat).Presheaf CommRingCat := (directImageStructure h).right.val
  let SY : (Y : TopCat).Presheaf CommRingCat := (directImageStructure down).right.val
  let a := directImageStalkMap f.base (directImageStructure f).hom y
  let b := directImageStalkMap f.base (affinePullbackDirectImageMap square).right y
  let lowerLeft : down ⁻¹ᵁ V ≤ left ⁻¹ᵁ (h ⁻¹ᵁ U) := by
    rw [← Scheme.Hom.comp_preimage, square.w, Scheme.Hom.comp_preimage]
    exact down.preimage_mono inside
  have chartSquare :
      IsPushout (h.app U) (f.appLE U V inside)
        (left.appLE (h ⁻¹ᵁ U) (down ⁻¹ᵁ V) lowerLeft) (down.app V) :=
    affinePullbackSections_isPushout h square U' V' inside
  have source := affinePushforwardStalk_isPushout h U' ⟨f y, yU⟩
  have target := affinePushforwardStalk_isPushout down V' ⟨y, yV⟩
  have base :
      f.appLE U V inside ≫ Y.presheaf.germ V y yV =
        X.presheaf.germ U (f y) yU ≫ a := by
    have germ : X.presheaf.germ U (f y) yU ≫ a = f.app U ≫ Y.presheaf.germ (f ⁻¹ᵁ U) y yU :=
      germ_directImageStalkMap f.base (directImageStructure f).hom y U yU
    rw [germ]
    change (f.app U ≫ Y.presheaf.map (homOfLE inside).op) ≫ Y.presheaf.germ V y yV =
      f.app U ≫ Y.presheaf.germ (f ⁻¹ᵁ U) y yU
    rw [Category.assoc]
    exact congrArg (f.app U ≫ ·) (TopCat.Presheaf.germ_res Y.presheaf (homOfLE inside) y yV)
  have extension :
      left.appLE (h ⁻¹ᵁ U) (down ⁻¹ᵁ V) lowerLeft ≫ SY.germ V y yV =
        SX.germ U (f y) yU ≫ b := by
    rw [germ_directImageStalkMap, affinePullbackDirectImageMap_app]
    change _ ≫ SY.germ V y yV =
      left.appLE (h ⁻¹ᵁ U) (down ⁻¹ᵁ (f ⁻¹ᵁ U)) _ ≫ SY.germ (f ⁻¹ᵁ U) y yU
    rw [← SY.germ_res (homOfLE inside) y yV, ← Category.assoc]
    exact congrArg (· ≫ SY.germ V y yV) (Scheme.Hom.appLE_map left _ _).symm
  have squareOnStalk :
      (ringSheafStalk (f y)).map (directImageStructure h).hom ≫ b =
        a ≫ (ringSheafStalk y).map (directImageStructure down).hom := by
    dsimp only [a, b]
    rw [← inverseImageStalkHom_mate f.base (affinePullbackDirectImageMap square).right y,
      ← inverseImageStalkHom_mate f.base (directImageStructure f).hom y]
    change _ = (inverseImageStalkHom f.base X.sheaf y ≫
      (ringSheafStalk y).map (pullbackStructureHom f)) ≫ _
    simp only [← Category.assoc]
    have natural :
        (ringSheafStalk (f y)).map (directImageStructure h).hom ≫
          inverseImageStalkHom f.base (directImageStructure h).right y =
        inverseImageStalkHom f.base X.sheaf y ≫
          (ringSheafStalk y).map ((TopCat.Sheaf.pullback CommRingCat f.base).map (directImageStructure h).hom) :=
      inverseImageStalkHom_naturality f.base (directImageStructure h).hom y
    rw [natural]
    change (inverseImageStalkHom f.base X.sheaf y ≫
      (ringSheafStalk y).map ((TopCat.Sheaf.pullback CommRingCat f.base).map (directImageStructure h).hom)) ≫
      (ringSheafStalk y).map (affinePullbackMate square) = _
    rw [Category.assoc, Category.assoc, ← Functor.map_comp, affinePullbackMate_comm, Functor.map_comp]
  have outer := chartSquare.paste_vert target
  rw [base, extension] at outer
  exact outer.of_top squareOnStalk source

private theorem affinePullbackPushoutStalk (y : Y) :
    let stalk := ringSheafStalk y
    IsPushout
      (stalk.map ((TopCat.Sheaf.pullback CommRingCat f.base).map (directImageStructure h).hom))
      (stalk.map (pullbackStructureHom f))
      (stalk.map (affinePullbackMate square))
      (stalk.map (directImageStructure down).hom) := by
  let e₁ := inverseImageStalkHom f.base X.sheaf y
  let e₂ := inverseImageStalkHom f.base (directImageStructure h).right y
  haveI : IsIso e₁ := inverseImageStalkHom_isIso f.base X.sheaf y
  haveI : IsIso e₂ := inverseImageStalkHom_isIso f.base (directImageStructure h).right y
  exact (affinePullbackStalk_isPushout square y).of_iso (asIso e₁) (asIso e₂) (Iso.refl _) (Iso.refl _)
    (inverseImageStalkHom_naturality f.base (directImageStructure h).hom y)
    (by simpa using (inverseImageStalkHom_mate f.base (directImageStructure f).hom y).symm)
    (by simpa using (inverseImageStalkHom_mate f.base (affinePullbackDirectImageMap square).right y).symm)
    (by simp)

/-- The direct image algebra of an affine pullback is the pushout defining algebra pullback. -/
theorem affinePullbackAlgebra_isPushout :
    IsPushout ((TopCat.Sheaf.pullback CommRingCat f.base).map (directImageStructure h).hom)
      (pullbackStructureHom f) (affinePullbackMate square) (directImageStructure down).hom := by
  let a := (TopCat.Sheaf.pullback CommRingCat f.base).map (directImageStructure h).hom
  let b := pullbackStructureHom f
  let c := affinePullbackMate square
  let d := (directImageStructure down).hom
  letI : HasPushout a b := by
    change @HasPushout (Sheaf (Opens.grothendieckTopology (Y : TopCat)) CommRingCat) _ _ _ _ a b
    infer_instance
  let comparison := pushout.desc c d (affinePullbackMate_comm square)
  haveI (y : (Y : TopCat)) :
      IsIso ((TopCat.Presheaf.stalkFunctor CommRingCat y).map comparison.val) := by
    change IsIso ((ringSheafStalk y).map comparison)
    let S := ringSheafStalk y
    let P := (IsPushout.of_hasPushout a b).map S
    let Q := affinePullbackPushoutStalk square y
    let e := P.isoPushout ≪≫ Q.isoPushout.symm
    have eq : S.map comparison = e.hom := by
      apply P.hom_ext
      · change S.map (pushout.inl a b) ≫ S.map comparison = _ ≫ P.isoPushout.hom ≫ Q.isoPushout.inv
        rw [← S.map_comp, pushout.inl_desc, P.inl_isoPushout_hom_assoc, Q.inl_isoPushout_inv]
      · change S.map (pushout.inr a b) ≫ S.map comparison = _ ≫ P.isoPushout.hom ≫ Q.isoPushout.inv
        rw [← S.map_comp, pushout.inr_desc, P.inr_isoPushout_hom_assoc, Q.inr_isoPushout_inv]
    rw [eq]
    infer_instance
  haveI : IsIso comparison := TopCat.Presheaf.isIso_of_stalkFunctor_map_iso comparison
  exact IsPushout.of_iso_pushout ⟨affinePullbackMate_comm square⟩ (asIso comparison).symm
    (by rw [Iso.symm_hom, Iso.comp_inv_eq]; exact (pushout.inl_desc c d (affinePullbackMate_comm square)).symm)
    (by rw [Iso.symm_hom, Iso.comp_inv_eq]; exact (pushout.inr_desc c d (affinePullbackMate_comm square)).symm)

end AffinePullback

namespace QuasiCoherentAlgebra

variable {X Y : Scheme.{u}} (C : QuasiCoherentAlgebra X)

/-- The algebra comparison in Lemma B.7 identifies the sheaf pullback with the algebra of the scheme pullback. -/
def baseChangeAlgebraIso (f : Y ⟶ X) :
    (pullbackAlgebra f).obj C.algebraSheaf ≅ (C.baseChange f).algebraSheaf := by
  let p := affinePullbackAlgebra_isPushout (C.baseChange_isPullback f)
  letI := p.hasPushout
  refine Under.isoMk p.isoPushout.symm ?_
  change _ ≫ p.isoPushout.inv = _
  exact p.inr_isoPushout_inv

/-- The pulled-back spectrum represents the actual pulled-back algebra on every test scheme. -/
def homEquivBaseChangeAlgebraSheaf (f : Y ⟶ X) {Z : Scheme.{u}} (g : Z ⟶ Y) :
    (Over.mk g ⟶ Over.mk (C.baseChange f).projection) ≃
      ((pullbackAlgebra g).obj ((pullbackAlgebra f).obj C.algebraSheaf) ⟶ Under.mk (𝟙 Z.sheaf)) :=
  (C.baseChange f).homEquivAlgebraSheaf.trans
    ((pullbackAlgebra g).mapIso (C.baseChangeAlgebraIso f)).symm.homFromEquiv

end QuasiCoherentAlgebra

end

end SHIGURE.SchemeDescent
