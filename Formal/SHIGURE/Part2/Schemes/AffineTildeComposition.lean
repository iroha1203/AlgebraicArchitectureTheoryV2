import Formal.SHIGURE.Part2.Schemes.AffineBaseChangeCoherence

/-! # Composition of affine pullback and scalar extension

The two composition comparisons agree by conjugating the affine
pushforward and global-section comparison along its adjunctions.
-/

namespace SHIGURE.SchemeDescent

open AlgebraicGeometry CategoryTheory Scheme.Modules Opposite

noncomputable section

universe u

/-- Transport composition of natural isomorphisms through the tilde comparisons of Appendix B.3. -/
private theorem conjugateIsoEquiv_trans {C D : Type*} [Category C] [Category D]
    {L₁ L₂ L₃ : C ⥤ D} {R₁ R₂ R₃ : D ⥤ C}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (a₃ : L₃ ⊣ R₃) (e : L₃ ≅ L₂) (f : L₂ ≅ L₁) :
    (conjugateIsoEquiv a₁ a₃) (e ≪≫ f) =
      (conjugateIsoEquiv a₁ a₂) f ≪≫ (conjugateIsoEquiv a₂ a₃) e :=
  Iso.ext (conjugateEquiv_comp a₁ a₂ a₃ f.hom e.hom).symm

/-- Compare conjugation with a common left functor in the B.3 pullback calculation. -/
private theorem conjugateIsoEquiv_whiskerLeft {A B C : Type*} [Category A] [Category B] [Category C]
    {L₁ L₂ : B ⥤ C} {R₁ R₂ : C ⥤ B} {L : A ⥤ B} {R : B ⥤ A}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (a : L ⊣ R) (e : L₂ ≅ L₁) :
    (conjugateIsoEquiv (a.comp a₁) (a.comp a₂)) (Functor.isoWhiskerLeft L e) =
      Functor.isoWhiskerRight ((conjugateIsoEquiv a₁ a₂) e) R :=
  Iso.ext (conjugateEquiv_whiskerLeft a₁ a₂ a e.hom)

/-- Compare conjugation with a common right functor in the B.3 pullback calculation. -/
private theorem conjugateIsoEquiv_whiskerRight {A B C : Type*} [Category A] [Category B] [Category C]
    {L₁ L₂ : A ⥤ B} {R₁ R₂ : B ⥤ A} {L : B ⥤ C} {R : C ⥤ B}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (a : L ⊣ R) (e : L₂ ≅ L₁) :
    (conjugateIsoEquiv (a₁.comp a) (a₂.comp a)) (Functor.isoWhiskerRight e L) =
      Functor.isoWhiskerLeft R ((conjugateIsoEquiv a₁ a₂) e) :=
  Iso.ext (conjugateEquiv_whiskerRight a₁ a₂ a e.hom)

/-- Transport the functor associator for the B.3 comparison of composed pullbacks. -/
private theorem conjugateIsoEquiv_associator {A B C D : Type*}
    [Category A] [Category B] [Category C] [Category D]
    {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : B ⥤ C} {R₂ : C ⥤ B} {L₃ : C ⥤ D} {R₃ : D ⥤ C}
    (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂) (c : L₃ ⊣ R₃) :
    (conjugateIsoEquiv (a.comp (b.comp c)) ((a.comp b).comp c)) (Functor.associator L₁ L₂ L₃) =
      Functor.associator R₃ R₂ R₁ :=
  Iso.ext (conjugateEquiv_associator_hom a b c)

/-- Transport inversion of a comparison for the B.3 pullback calculation. -/
private theorem conjugateIsoEquiv_symm_iso {C D : Type*} [Category C] [Category D]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C} (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂) (e : L₂ ≅ L₁) :
    (conjugateIsoEquiv b a) e.symm = ((conjugateIsoEquiv a b) e).symm := rfl

/-- Transport the comparison for equal geometric arrows in the B.3 pullback calculation. -/
private theorem conjugateIsoEquiv_pullbackCongr {Z X : Scheme.{u}} {p q : Z ⟶ X}
    (equal : p = q) :
    (conjugateIsoEquiv (pullbackPushforwardAdjunction q) (pullbackPushforwardAdjunction p))
      (pullbackCongr equal) = pushforwardCongr equal.symm := by
  subst q
  apply Iso.ext
  change conjugateEquiv _ _ (𝟙 _) = _
  rw [conjugateEquiv_id]
  ext M W x
  simp only [NatTrans.id_app, pushforwardCongr_hom_app_app]
  have h : eqToHom (show p ⁻¹ᵁ W = p ⁻¹ᵁ W by rfl) = 𝟙 _ := Subsingleton.elim _ _
  rw [h, op_id, M.presheaf.map_id]
  rfl

/-- Transport the composition comparison for the actual geometric B.3 pullback. -/
private theorem conjugateIsoEquiv_pullbackComp {Z Y X : Scheme.{u}} (p : Z ⟶ Y) (q : Y ⟶ X) :
    (conjugateIsoEquiv ((pullbackPushforwardAdjunction q).comp (pullbackPushforwardAdjunction p))
      (pullbackPushforwardAdjunction (p ≫ q))) (pullbackComp p q).symm = pushforwardComp p q :=
  Iso.ext (conjugateEquiv_pullbackComp_inv p q)

/-- Recover the B.3 forward composition comparison from the equality of inverse composites. -/
private theorem iso_eq_of_symm_chains {C : Type*} [Category C]
    {X₀ X₁ X₂ X₃ X₄ X₅ X₆ Y : C}
    (x₁ : X₀ ≅ X₁) (x₂ : X₁ ≅ X₂) (x₃ : X₂ ≅ X₃) (x₄ : X₃ ≅ X₄)
    (x₅ : X₄ ≅ X₅) (x₆ : X₅ ≅ X₆) (y₁ : X₀ ≅ Y) (y₂ : Y ≅ X₆)
    (e : y₂.symm ≪≫ y₁.symm = x₆.symm ≪≫ x₅.symm ≪≫ x₄.symm ≪≫ x₃.symm ≪≫ x₂.symm ≪≫ x₁.symm) :
    y₁ ≪≫ y₂ = x₁ ≪≫ x₂ ≪≫ x₃ ≪≫ x₄ ≪≫ x₅ ≪≫ x₆ := by
  simpa only [Iso.trans_symm, Iso.trans_assoc] using congrArg Iso.symm e

/-- Use the equality of the two transported paths to identify the original B.3 isomorphism. -/
private theorem conjugateParallelPaths {C D : Type*} [Category C] [Category D]
    {L₀ L₁ L₂ L₃ L₄ L₅ L₆ L : C ⥤ D} {R₀ R₁ R₂ R₃ R₄ R₅ R₆ R : D ⥤ C}
    (a₀ : L₀ ⊣ R₀) (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (a₃ : L₃ ⊣ R₃)
    (a₄ : L₄ ⊣ R₄) (a₅ : L₅ ⊣ R₅) (a₆ : L₆ ⊣ R₆) (b : L ⊣ R)
    (x₁ : L₀ ≅ L₁) (x₂ : L₁ ≅ L₂) (x₃ : L₂ ≅ L₃) (x₄ : L₃ ≅ L₄) (x₅ : L₄ ≅ L₅) (x₆ : L₅ ≅ L₆)
    (y₁ : L₀ ≅ L) (y₂ : L ≅ L₆)
    (mateEq : (conjugateIsoEquiv a₀ b) y₁.symm ≪≫ (conjugateIsoEquiv b a₆) y₂.symm =
      (conjugateIsoEquiv a₀ a₁) x₁.symm ≪≫ (conjugateIsoEquiv a₁ a₂) x₂.symm ≪≫
      (conjugateIsoEquiv a₂ a₃) x₃.symm ≪≫ (conjugateIsoEquiv a₃ a₄) x₄.symm ≪≫
      (conjugateIsoEquiv a₄ a₅) x₅.symm ≪≫ (conjugateIsoEquiv a₅ a₆) x₆.symm) :
    y₁ ≪≫ y₂ = x₁ ≪≫ x₂ ≪≫ x₃ ≪≫ x₄ ≪≫ x₅ ≪≫ x₆ := by
  apply iso_eq_of_symm_chains x₁ x₂ x₃ x₄ x₅ x₆ y₁ y₂
  apply (conjugateIsoEquiv a₀ a₆).injective
  rw [conjugateIsoEquiv_trans a₀ b a₆, conjugateIsoEquiv_trans a₀ a₅ a₆,
    conjugateIsoEquiv_trans a₀ a₄ a₅, conjugateIsoEquiv_trans a₀ a₃ a₄, conjugateIsoEquiv_trans a₀ a₂ a₃,
    conjugateIsoEquiv_trans a₀ a₁ a₂]
  simpa only [Iso.trans_assoc] using mateEq

variable {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T)

/-- Identify the inverse tilde pullback comparison with the transported affine chart map in B.3. -/
private theorem conjugateIsoEquiv_tildePullbackIso_inv :
    (conjugateIsoEquiv ((tilde.adjunction (R := R)).comp (pullbackPushforwardAdjunction (Spec.map f)))
      ((ModuleCat.extendRestrictScalarsAdj f.hom).comp (tilde.adjunction (R := S)))) (tildePullbackIso f).symm =
      moduleSpecΓPushforwardIso f :=
  Iso.ext (conjugateEquiv_tildePullbackIso_inv f)

set_option maxRecDepth 1600 in
set_option maxHeartbeats 400000 in
/-- The affine inverse-image comparison sends composition to the canonical
composition of scalar extension and scheme-module pullbacks. -/
theorem tildePullbackIso_comp :
    tildePullbackIso (f ≫ g) ≪≫
      Functor.isoWhiskerRight (ModuleCat.extendScalarsComp f.hom g.hom) (tilde.functor T) =
    Functor.isoWhiskerLeft (tilde.functor R)
      (pullbackCongr (Spec.map_comp f g) ≪≫ (pullbackComp (Spec.map g) (Spec.map f)).symm) ≪≫
    (Functor.associator (tilde.functor R) (pullback (Spec.map f)) (pullback (Spec.map g))).symm ≪≫
    Functor.isoWhiskerRight (tildePullbackIso f) (pullback (Spec.map g)) ≪≫
    Functor.associator (ModuleCat.extendScalars f.hom) (tilde.functor S) (pullback (Spec.map g)) ≪≫
    Functor.isoWhiskerLeft (ModuleCat.extendScalars f.hom) (tildePullbackIso g) ≪≫
    (Functor.associator (ModuleCat.extendScalars f.hom) (ModuleCat.extendScalars g.hom) (tilde.functor T)).symm := by
  let tR := tilde.adjunction (R := R)
  let tS := tilde.adjunction (R := S)
  let tT := tilde.adjunction (R := T)
  let pf := pullbackPushforwardAdjunction (Spec.map f)
  let pg := pullbackPushforwardAdjunction (Spec.map g)
  let pfg := pullbackPushforwardAdjunction (Spec.map (f ≫ g))
  let ef := ModuleCat.extendRestrictScalarsAdj f.hom
  let eg := ModuleCat.extendRestrictScalarsAdj g.hom
  let efg := ModuleCat.extendRestrictScalarsAdj (f ≫ g).hom
  let bc := pullbackCongr (Spec.map_comp f g) ≪≫ (pullbackComp (Spec.map g) (Spec.map f)).symm
  let as₁ := Functor.associator (tilde.functor R) (pullback (Spec.map f)) (pullback (Spec.map g))
  let as₂ := Functor.associator (ModuleCat.extendScalars f.hom) (tilde.functor S) (pullback (Spec.map g))
  let as₃ := Functor.associator (ModuleCat.extendScalars f.hom) (ModuleCat.extendScalars g.hom) (tilde.functor T)
  let ex := ModuleCat.extendScalarsComp f.hom g.hom
  have extEq : (conjugateIsoEquiv efg (ef.comp eg)) ex.symm =
      ModuleCat.restrictScalarsComp f.hom g.hom := by
    rw [conjugateIsoEquiv_symm_iso]
    change ((conjugateIsoEquiv (ef.comp eg) efg)
      ((conjugateIsoEquiv (ef.comp eg) efg).symm (ModuleCat.restrictScalarsComp f.hom g.hom).symm)).symm = _
    rw [Equiv.apply_symm_apply]
    rfl
  have pbEq : (conjugateIsoEquiv pfg (pf.comp pg)) bc.symm =
      (pushforwardComp (Spec.map g) (Spec.map f) ≪≫ pushforwardCongr (Spec.map_comp f g).symm).symm := by
    rw [conjugateIsoEquiv_symm_iso]
    have eq := conjugateIsoEquiv_trans (pf.comp pg)
      (pullbackPushforwardAdjunction (Spec.map g ≫ Spec.map f)) pfg
      (pullbackCongr (Spec.map_comp f g)) (pullbackComp (Spec.map g) (Spec.map f)).symm
    rw [show (conjugateIsoEquiv (pf.comp pg) pfg) bc = _ from eq, conjugateIsoEquiv_pullbackComp,
      conjugateIsoEquiv_pullbackCongr]
  let A₀ := tR.comp pfg
  let A₁ := tR.comp (pf.comp pg)
  let A₂ := (tR.comp pf).comp pg
  let A₃ := (ef.comp tS).comp pg
  let A₄ := ef.comp (tS.comp pg)
  let A₅ := ef.comp (eg.comp tT)
  let A₆ := (ef.comp eg).comp tT
  let B := efg.comp tT
  let C := Functor.isoWhiskerRight
    (pushforwardComp (Spec.map g) (Spec.map f) ≪≫ pushforwardCongr (Spec.map_comp f g).symm)
    (moduleSpecΓFunctor (R := R))
  let E := Functor.isoWhiskerLeft (moduleSpecΓFunctor (R := T))
    (ModuleCat.restrictScalarsComp f.hom g.hom)
  let path := Functor.associator (pushforward (Spec.map g)) (pushforward (Spec.map f))
        (moduleSpecΓFunctor (R := R)) ≪≫
      Functor.isoWhiskerLeft (pushforward (Spec.map g)) (moduleSpecΓPushforwardIso f) ≪≫
      (Functor.associator (pushforward (Spec.map g)) (moduleSpecΓFunctor (R := S))
        (ModuleCat.restrictScalars f.hom)).symm ≪≫
      Functor.isoWhiskerRight (moduleSpecΓPushforwardIso g) (ModuleCat.restrictScalars f.hom) ≪≫
      Functor.associator (moduleSpecΓFunctor (R := T)) (ModuleCat.restrictScalars g.hom)
        (ModuleCat.restrictScalars f.hom)
  let x₁ := Functor.isoWhiskerLeft (tilde.functor R) bc
  let x₂ := as₁.symm
  let x₃ := Functor.isoWhiskerRight (tildePullbackIso f) (pullback (Spec.map g))
  let x₄ := as₂
  let x₅ := Functor.isoWhiskerLeft (ModuleCat.extendScalars f.hom) (tildePullbackIso g)
  let x₆ := as₃.symm
  let y := Functor.isoWhiskerRight ex (tilde.functor T)
  change tildePullbackIso (f ≫ g) ≪≫ y = x₁ ≪≫ x₂ ≪≫ x₃ ≪≫ x₄ ≪≫ x₅ ≪≫ x₆
  have a₁ : (conjugateIsoEquiv A₀ A₁) x₁.symm = C.symm := by
    change (conjugateIsoEquiv (tR.comp pfg) (tR.comp (pf.comp pg)))
      (Functor.isoWhiskerLeft (tilde.functor R) bc.symm) = _
    rw [conjugateIsoEquiv_whiskerLeft, pbEq]
    rfl
  have a₂ : (conjugateIsoEquiv A₁ A₂) x₂.symm =
      Functor.associator (pushforward (Spec.map g)) (pushforward (Spec.map f))
        (moduleSpecΓFunctor (R := R)) := conjugateIsoEquiv_associator tR pf pg
  have a₃ : (conjugateIsoEquiv A₂ A₃) x₃.symm =
      Functor.isoWhiskerLeft (pushforward (Spec.map g)) (moduleSpecΓPushforwardIso f) := by
    change (conjugateIsoEquiv ((tR.comp pf).comp pg) ((ef.comp tS).comp pg))
      (Functor.isoWhiskerRight (tildePullbackIso f).symm (pullback (Spec.map g))) = _
    rw [conjugateIsoEquiv_whiskerRight, conjugateIsoEquiv_tildePullbackIso_inv]
  have a₄ : (conjugateIsoEquiv A₃ A₄) x₄.symm =
      (Functor.associator (pushforward (Spec.map g)) (moduleSpecΓFunctor (R := S))
        (ModuleCat.restrictScalars f.hom)).symm :=
    congrArg Iso.symm (conjugateIsoEquiv_associator ef tS pg)
  have a₅ : (conjugateIsoEquiv A₄ A₅) x₅.symm =
      Functor.isoWhiskerRight (moduleSpecΓPushforwardIso g) (ModuleCat.restrictScalars f.hom) := by
    change (conjugateIsoEquiv (ef.comp (tS.comp pg)) (ef.comp (eg.comp tT)))
      (Functor.isoWhiskerLeft (ModuleCat.extendScalars f.hom) (tildePullbackIso g).symm) = _
    rw [conjugateIsoEquiv_whiskerLeft, conjugateIsoEquiv_tildePullbackIso_inv]
  have a₆ : (conjugateIsoEquiv A₅ A₆) x₆.symm =
      Functor.associator (moduleSpecΓFunctor (R := T)) (ModuleCat.restrictScalars g.hom)
        (ModuleCat.restrictScalars f.hom) := conjugateIsoEquiv_associator ef eg tT
  have b : (conjugateIsoEquiv B A₆) y.symm = E := by
    change (conjugateIsoEquiv (efg.comp tT) ((ef.comp eg).comp tT))
      (Functor.isoWhiskerRight ex.symm (tilde.functor T)) = _
    rw [conjugateIsoEquiv_whiskerRight, extEq]
  have matched : moduleSpecΓPushforwardIso (f ≫ g) ≪≫ E = C.symm ≪≫ path :=
    moduleSpecΓPushforwardIso_comp_cancel f g
  apply conjugateParallelPaths A₀ A₁ A₂ A₃ A₄ A₅ A₆ B x₁ x₂ x₃ x₄ x₅ x₆ (tildePullbackIso (f ≫ g)) y
  calc
    _ = moduleSpecΓPushforwardIso (f ≫ g) ≪≫ E :=
      congrArg₂ (· ≪≫ ·) (conjugateIsoEquiv_tildePullbackIso_inv (f ≫ g)) b
    _ = C.symm ≪≫ path := matched
    _ = _ := congrArg₂ (· ≪≫ ·) a₁.symm
      (congrArg₂ (· ≪≫ ·) a₂.symm (congrArg₂ (· ≪≫ ·) a₃.symm
        (congrArg₂ (· ≪≫ ·) a₄.symm (congrArg₂ (· ≪≫ ·) a₅.symm a₆.symm))))

end

end SHIGURE.SchemeDescent
