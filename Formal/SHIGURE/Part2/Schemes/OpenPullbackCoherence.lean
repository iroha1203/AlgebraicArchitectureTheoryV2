import Formal.SHIGURE.Part2.Schemes.QuasiCoherentZariski

/-! # Open restriction and pullback coherence

In Appendix B.3 the open-cover calculation uses ordinary restriction
on sections. Descent data use the pullback pseudofunctor. Their comparison
respects compositions, equal maps, and identities.
-/

namespace SHIGURE.SchemeDescent

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Scheme.Modules

noncomputable section

universe u

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
  [IsOpenImmersion f] [IsOpenImmersion g]

/-- The restriction composition comparison is conjugate to the actual
pushforward composition comparison, as needed for the open-cover cocycle. -/
theorem restrictFunctorComp_conjugate :
    conjugateEquiv ((restrictAdjunction g).comp (restrictAdjunction f)) (restrictAdjunction (f ≫ g))
      (restrictFunctorComp f g).hom = (pushforwardComp f g).hom := by
  let adj₁ := (restrictAdjunction g).comp (restrictAdjunction f)
  let adj₂ := restrictAdjunction (f ≫ g)
  let right := (pushforwardComp f g).hom
  apply (conjugateEquiv adj₁ adj₂).symm.injective
  rw [Equiv.symm_apply_apply]
  ext1
  funext M
  apply (adj₂.homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit]
  rw [← unit_conjugateEquiv_symm adj₁ adj₂ right M]
  ext W x
  simp only [adj₁, adj₂, right, Adjunction.comp_unit_app, Functor.comp_obj, Functor.id_obj,
    Hom.comp_app, pushforward_map_app, pushforwardComp_hom_app_app,
    restrictAdjunction_unit_app_app, restrictFunctorComp_hom_app_app, Category.comp_id, AddCommGrpCat.comp_apply, restrict_map]
  rw [← AddCommGrpCat.comp_apply, ← M.presheaf.map_comp, ← AddCommGrpCat.comp_apply,
    ← M.presheaf.map_comp]
  congr 1

private theorem conjugate_leftAdjointUniq_hom {C D : Type*} [Category C] [Category D]
    {L₁ L₂ : C ⥤ D} {R : D ⥤ C} (a : L₁ ⊣ R) (b : L₂ ⊣ R) :
    conjugateEquiv b a (a.leftAdjointUniq b).hom = 𝟙 R := by
  have inverse : conjugateEquiv a b (a.leftAdjointUniq b).inv = 𝟙 R := by
    change (conjugateIsoEquiv a b ((conjugateIsoEquiv a b).symm (Iso.refl R))).hom = 𝟙 R
    rw [Equiv.apply_symm_apply]
    rfl
  have commute := conjugateEquiv_comm a b
    (α := (a.leftAdjointUniq b).inv) (β := (a.leftAdjointUniq b).hom)
    (a.leftAdjointUniq b).hom_inv_id
  simpa only [inverse, Category.id_comp] using commute

set_option maxRecDepth 1200 in
set_option maxHeartbeats 750000 in
/-- The comparison between ordinary restriction and module pullback respects
composition along two open immersions. -/
theorem restrictFunctorIsoPullback_comp :
    (restrictFunctorComp f g).symm ≪≫ restrictFunctorIsoPullback (f ≫ g) =
      Functor.isoWhiskerRight (restrictFunctorIsoPullback g) (restrictFunctor f) ≪≫
      Functor.isoWhiskerLeft (pullback g) (restrictFunctorIsoPullback f) ≪≫
      pullbackComp f g := by
  let a := (restrictAdjunction g).comp (restrictAdjunction f)
  let b := restrictAdjunction (f ≫ g)
  let c := (pullbackPushforwardAdjunction g).comp (restrictAdjunction f)
  let d := (pullbackPushforwardAdjunction g).comp (pullbackPushforwardAdjunction f)
  let e := pullbackPushforwardAdjunction (f ≫ g)
  have h₁ : conjugateEquiv b a (restrictFunctorComp f g).inv = (pushforwardComp f g).inv := by
    exact congrArg Iso.inv (Iso.ext (restrictFunctorComp_conjugate f g) :
      conjugateIsoEquiv a b (restrictFunctorComp f g) = pushforwardComp f g)
  have h₂ : conjugateEquiv e d (pullbackComp f g).hom = (pushforwardComp f g).inv := by
    exact congrArg Iso.inv (Iso.ext (conjugateEquiv_pullbackComp_inv f g) :
      conjugateIsoEquiv d e (pullbackComp f g).symm = pushforwardComp f g)
  have h₃ : conjugateEquiv e b (restrictFunctorIsoPullback (f ≫ g)).hom = 𝟙 _ :=
    conjugate_leftAdjointUniq_hom b e
  have h₄ : conjugateEquiv d c (Functor.whiskerLeft (pullback g) (restrictFunctorIsoPullback f).hom) =
      𝟙 _ := by
    rw [show d = (pullbackPushforwardAdjunction g).comp (pullbackPushforwardAdjunction f) from rfl,
      show c = (pullbackPushforwardAdjunction g).comp (restrictAdjunction f) from rfl,
      conjugateEquiv_whiskerLeft]
    rw [show (restrictFunctorIsoPullback f).hom =
      ((restrictAdjunction f).leftAdjointUniq (pullbackPushforwardAdjunction f)).hom from rfl,
      conjugate_leftAdjointUniq_hom]
    simp
  have h₅ : conjugateEquiv c a (Functor.whiskerRight (restrictFunctorIsoPullback g).hom (restrictFunctor f)) =
      𝟙 _ := by
    rw [show c = (pullbackPushforwardAdjunction g).comp (restrictAdjunction f) from rfl,
      show a = (restrictAdjunction g).comp (restrictAdjunction f) from rfl,
      conjugateEquiv_whiskerRight]
    rw [show (restrictFunctorIsoPullback g).hom =
      ((restrictAdjunction g).leftAdjointUniq (pullbackPushforwardAdjunction g)).hom from rfl,
      conjugate_leftAdjointUniq_hom]
    simp
  apply Iso.ext
  apply (conjugateEquiv e a).injective
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom]
  rw [← conjugateEquiv_comp e b a, ← conjugateEquiv_comp e c a, ← conjugateEquiv_comp e d c]
  rw [h₁, h₂, h₃, h₄, h₅]
  simp

/-- The pullback comparison is unchanged when expressing an open immersion
by an equal morphism. -/
theorem restrictFunctorIsoPullback_congr {a b : X ⟶ Y}
    [IsOpenImmersion a] [IsOpenImmersion b] (same : a = b) :
    restrictFunctorCongr same ≪≫ restrictFunctorIsoPullback b =
      restrictFunctorIsoPullback a ≪≫ pullbackCongr same := by
  subst b
  have congrId : restrictFunctorCongr (rfl : a = a) = Iso.refl _ := by
    apply Iso.ext
    ext M U x
    rw [restrictFunctorCongr_hom_app_app]
    have equal : eqToHom (show a ''ᵁ U = a ''ᵁ U by rfl) = 𝟙 _ := Subsingleton.elim _ _
    rw [equal, op_id, M.presheaf.map_id]
    rfl
  rw [congrId]
  simp [pullbackCongr]

private theorem restrictFunctorId_conjugate (T : Scheme.{u}) :
    conjugateEquiv Adjunction.id (restrictAdjunction (𝟙 T))
      (restrictFunctorId (X := T)).hom = (pushforwardId T).inv := by
  let adj := restrictAdjunction (𝟙 T)
  apply (conjugateEquiv Adjunction.id adj).symm.injective
  rw [Equiv.symm_apply_apply]
  ext1
  funext M
  apply (adj.homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit]
  rw [← unit_conjugateEquiv_symm Adjunction.id adj (pushforwardId T).inv M]
  ext W x
  simp only [adj, Hom.comp_app, pushforward_map_app, pushforwardId_inv_app_app,
    AddCommGrpCat.comp_apply, restrictFunctorId_hom_app_app, restrictAdjunction_unit_app_app,
    Adjunction.id_unit, NatTrans.id_app, Category.id_comp]
  rw [← AddCommGrpCat.comp_apply, ← M.presheaf.map_comp]
  change (M.presheaf.map _) x = x
  calc
    _ = (M.presheaf.map (𝟙 (op W))) x := by
      apply congrArg (fun a : op W ⟶ op W => (M.presheaf.map a) x)
      exact Subsingleton.elim _ _
    _ = x := congrArg (fun a => a x) (M.presheaf.map_id (op W))

/-- For the identity open immersion, the restriction and pullback identity
comparisons agree. -/
theorem restrictFunctorIsoPullback_id (T : Scheme.{u}) :
    restrictFunctorIsoPullback (𝟙 T) ≪≫ pullbackId T = restrictFunctorId := by
  let a := restrictAdjunction (𝟙 T)
  let b := pullbackPushforwardAdjunction (𝟙 T)
  apply Iso.ext
  apply (conjugateEquiv Adjunction.id a).injective
  simp only [Iso.trans_hom]
  rw [← conjugateEquiv_comp Adjunction.id b a]
  rw [conjugateEquiv_pullbackId_hom, restrictFunctorId_conjugate T]
  change _ ≫ conjugateEquiv b a (a.leftAdjointUniq b).hom = _
  rw [conjugate_leftAdjointUniq_hom, Category.comp_id]

end

end SHIGURE.SchemeDescent
