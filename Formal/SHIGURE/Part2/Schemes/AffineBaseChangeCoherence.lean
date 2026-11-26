import Formal.SHIGURE.Part2.Schemes.TildeBaseChange

/-! # Coherence of the affine base change comparison

The global-section comparison for affine pushforwards is compatible with
composition. Its left adjoint mate is the tilde pullback comparison used
to transport the coefficient descent datum to the geometric overlaps.
-/

namespace SHIGURE.SchemeDescent

open AlgebraicGeometry CategoryTheory Scheme.Modules Opposite

noncomputable section

universe u

variable {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T)

set_option maxHeartbeats 500000 in
/-- The right adjoint comparison is compatible with composing scalar restrictions. -/
theorem moduleSpecΓPushforwardIso_comp :
    Functor.isoWhiskerRight
        (pushforwardComp (Spec.map g) (Spec.map f) ≪≫
          pushforwardCongr (Spec.map_comp f g).symm) (moduleSpecΓFunctor (R := R)) ≪≫
      moduleSpecΓPushforwardIso (f ≫ g) =
    Functor.associator (pushforward (Spec.map g)) (pushforward (Spec.map f)) (moduleSpecΓFunctor (R := R)) ≪≫
      Functor.isoWhiskerLeft (pushforward (Spec.map g)) (moduleSpecΓPushforwardIso f) ≪≫
      (Functor.associator (pushforward (Spec.map g)) (moduleSpecΓFunctor (R := S))
        (ModuleCat.restrictScalars f.hom)).symm ≪≫
      Functor.isoWhiskerRight (moduleSpecΓPushforwardIso g) (ModuleCat.restrictScalars f.hom) ≪≫
      Functor.associator (moduleSpecΓFunctor (R := T)) (ModuleCat.restrictScalars g.hom)
        (ModuleCat.restrictScalars f.hom) ≪≫
      Functor.isoWhiskerLeft (moduleSpecΓFunctor (R := T))
        (ModuleCat.restrictScalarsComp f.hom g.hom).symm := by
  ext N x
  change N.presheaf.map (𝟙 (op (⊤ : (Spec T).Opens))) x = x
  exact congrArg (fun m => m x) (N.presheaf.map_id (op ⊤))

private theorem transportedAdjunction_leftUniq_inv {C D : Type*} [Category C] [Category D]
    {L L' : C ⥤ D} {A B : D ⥤ C} (adj : L ⊣ A) (adj' : L' ⊣ B) (e : A ≅ B) :
    ((adj.ofNatIsoRight e).leftAdjointUniq adj').inv =
      (conjugateEquiv adj adj').symm e.hom := by
  ext X
  simp [Adjunction.leftAdjointUniq, Adjunction.ofNatIsoRight, Adjunction.mkOfHomEquiv,
    Adjunction.homEquiv_unit]

/-- The inverse of the affine tilde comparison is the left adjoint mate of the
global-sections comparison. This is used to transfer the composition law. -/
theorem conjugateEquiv_tildePullbackIso_inv :
    conjugateEquiv ((tilde.adjunction (R := R)).comp (pullbackPushforwardAdjunction (Spec.map f)))
      ((ModuleCat.extendRestrictScalarsAdj f.hom).comp (tilde.adjunction (R := S)))
      (tildePullbackIso f).inv = (moduleSpecΓPushforwardIso f).hom := by
  rw [tildePullbackIso, transportedAdjunction_leftUniq_inv, Equiv.apply_symm_apply]

section Transitions

/-- When the two base-change squares commute, the pullback of a comparison
map agrees with the scalar extension of that comparison. -/
theorem comparison_through_baseChange {C E G H : Type*}
    [Category C] [Category E] [Category G] [Category H]
    (T : C ⥤ G) (T' : E ⥤ H) (E₀ : C ⥤ E) (P : G ⥤ H)
    (base : T ⋙ P ≅ E₀ ⋙ T')
    {V₀ V₁ : C} (m : V₀ ⟶ V₁)
    {U₀ U₁ : G} {W₀ W₁ : H} {X₀ X₁ : E}
    (τ₀ : U₀ ≅ T.obj V₀) (τ₁ : U₁ ≅ T.obj V₁)
    (r₀ : P.obj U₀ ≅ W₀) (r₁ : P.obj U₁ ≅ W₁)
    (s₀ : X₀ ≅ E₀.obj V₀) (s₁ : X₁ ≅ E₀.obj V₁)
    (u₀ : W₀ ≅ T'.obj X₀) (u₁ : W₁ ≅ T'.obj X₁)
    (left : r₀.hom ≫ u₀.hom ≫ T'.map s₀.hom = P.map τ₀.hom ≫ base.hom.app V₀)
    (right : r₁.hom ≫ u₁.hom ≫ T'.map s₁.hom = P.map τ₁.hom ≫ base.hom.app V₁) :
    r₀.inv ≫ P.map (τ₀.hom ≫ T.map m ≫ τ₁.inv) ≫ r₁.hom =
      u₀.hom ≫ T'.map (s₀.hom ≫ E₀.map m ≫ s₁.inv) ≫ u₁.inv := by
  apply (cancel_epi r₀.hom).1
  apply (cancel_mono (u₁.hom ≫ T'.map s₁.hom)).1
  simp only [Category.assoc, Functor.map_comp, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc]
  have cancel₁ := (T'.mapIso s₁).inv_hom_id
  rw [Functor.mapIso_inv, Functor.mapIso_hom] at cancel₁
  rw [cancel₁, Category.comp_id, right]
  have cancel₂ := (P.mapIso τ₁).inv_hom_id_assoc (base.hom.app V₁)
  rw [Functor.mapIso_inv, Functor.mapIso_hom] at cancel₂
  rw [cancel₂]
  have n : P.map (T.map m) ≫ base.hom.app V₁ =
      base.hom.app V₀ ≫ T'.map (E₀.map m) := base.hom.naturality m
  rw [n]
  simpa only [Category.assoc] using (congrArg (· ≫ T'.map (E₀.map m)) left).symm

end Transitions

section Composition

private theorem cancel_iso_on_both_sides {C : Type*} [Category C] {X Y Z W : C}
    (a : X ≅ Y) (b : Y ≅ Z) (c : X ≅ W) (d : Z ≅ W) (eq : a ≪≫ b = c ≪≫ d.symm) :
    b ≪≫ d = a.symm ≪≫ c := calc
  _ = a.symm ≪≫ a ≪≫ b ≪≫ d := (Iso.symm_self_id_assoc a _).symm
  _ = a.symm ≪≫ (a ≪≫ b) ≪≫ d := congrArg (a.symm ≪≫ ·) (Iso.trans_assoc a b d).symm
  _ = a.symm ≪≫ (c ≪≫ d.symm) ≪≫ d := congrArg (fun z => a.symm ≪≫ z ≪≫ d) eq
  _ = _ := by rw [Iso.trans_assoc c, Iso.symm_self_id, Iso.trans_refl]

private theorem append_five {C : Type*} [Category C] {X₀ X₁ X₂ X₃ X₄ X₅ X₆ : C}
    (a : X₀ ≅ X₁) (b : X₁ ≅ X₂) (c : X₂ ≅ X₃) (d : X₃ ≅ X₄) (e : X₄ ≅ X₅) (f : X₅ ≅ X₆) :
    (a ≪≫ b ≪≫ c ≪≫ d ≪≫ e) ≪≫ f = a ≪≫ b ≪≫ c ≪≫ d ≪≫ e ≪≫ f := by
  simp only [Iso.trans_assoc]

set_option maxHeartbeats 500000 in
/-- The right affine comparison written with composition on the side of the
iterated sections, for use in comparing the left adjoint mates. -/
theorem moduleSpecΓPushforwardIso_comp_cancel {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) :
    moduleSpecΓPushforwardIso (f ≫ g) ≪≫
      Functor.isoWhiskerLeft (moduleSpecΓFunctor (R := T)) (ModuleCat.restrictScalarsComp f.hom g.hom) =
    (Functor.isoWhiskerRight
        (pushforwardComp (Spec.map g) (Spec.map f) ≪≫ pushforwardCongr (Spec.map_comp f g).symm)
        (moduleSpecΓFunctor (R := R))).symm ≪≫
    Functor.associator (pushforward (Spec.map g)) (pushforward (Spec.map f)) (moduleSpecΓFunctor (R := R)) ≪≫
    Functor.isoWhiskerLeft (pushforward (Spec.map g)) (moduleSpecΓPushforwardIso f) ≪≫
    (Functor.associator (pushforward (Spec.map g)) (moduleSpecΓFunctor (R := S))
      (ModuleCat.restrictScalars f.hom)).symm ≪≫
    Functor.isoWhiskerRight (moduleSpecΓPushforwardIso g) (ModuleCat.restrictScalars f.hom) ≪≫
    Functor.associator (moduleSpecΓFunctor (R := T)) (ModuleCat.restrictScalars g.hom)
      (ModuleCat.restrictScalars f.hom) := by
  let c := Functor.isoWhiskerRight
    (pushforwardComp (Spec.map g) (Spec.map f) ≪≫ pushforwardCongr (Spec.map_comp f g).symm)
    (moduleSpecΓFunctor (R := R))
  let e := Functor.isoWhiskerLeft (moduleSpecΓFunctor (R := T)) (ModuleCat.restrictScalarsComp f.hom g.hom)
  let a₁ := Functor.associator (pushforward (Spec.map g)) (pushforward (Spec.map f))
    (moduleSpecΓFunctor (R := R))
  let a₂ := Functor.isoWhiskerLeft (pushforward (Spec.map g)) (moduleSpecΓPushforwardIso f)
  let a₃ := (Functor.associator (pushforward (Spec.map g)) (moduleSpecΓFunctor (R := S))
    (ModuleCat.restrictScalars f.hom)).symm
  let a₄ := Functor.isoWhiskerRight (moduleSpecΓPushforwardIso g) (ModuleCat.restrictScalars f.hom)
  let a₅ := Functor.associator (moduleSpecΓFunctor (R := T)) (ModuleCat.restrictScalars g.hom)
    (ModuleCat.restrictScalars f.hom)
  let h := moduleSpecΓPushforwardIso (f ≫ g)
  let path := a₁ ≪≫ a₂ ≪≫ a₃ ≪≫ a₄ ≪≫ a₅
  have eq : c ≪≫ h = path ≪≫ e.symm :=
    (moduleSpecΓPushforwardIso_comp f g).trans (append_five a₁ a₂ a₃ a₄ a₅ e.symm).symm
  exact cancel_iso_on_both_sides c h path e eq

end Composition

end

end SHIGURE.SchemeDescent
