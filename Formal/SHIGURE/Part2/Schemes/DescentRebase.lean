import Mathlib.CategoryTheory.Sites.Descent.DescentData

/-! # Changing the base of a descent comparison while keeping its charts -/

namespace SHIGURE.SchemeDescent

open CategoryTheory CategoryTheory.Pseudofunctor Opposite

noncomputable section

universe t u v a b

section Isomorphism

variable {C : Type u} [Category.{v} C]

/-- Pullback along an isomorphism is an equivalence in any contravariant pseudofunctor. -/
theorem descentPullbackIso_isEquivalence
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{a, b}) {X Y : C} (e : Y ≅ X) :
    (F.map e.hom.op.toLoc).toFunctor.IsEquivalence := by
  let A := (F.map e.hom.op.toLoc).toFunctor
  let B := (F.map e.inv.op.toLoc).toFunctor
  have unit : e.hom.op.toLoc ≫ e.inv.op.toLoc = 𝟙 (LocallyDiscrete.mk (op X)) :=
    congrArg (fun f => f.op.toLoc) e.inv_hom_id
  have counit : e.inv.op.toLoc ≫ e.hom.op.toLoc = 𝟙 (LocallyDiscrete.mk (op Y)) :=
    congrArg (fun f => f.op.toLoc) e.hom_inv_id
  let η : 𝟭 _ ≅ A ⋙ B :=
    (Cat.Hom.toNatIso (F.mapId _)).symm ≪≫
      Cat.Hom.toNatIso (F.mapComp' e.hom.op.toLoc e.inv.op.toLoc _ unit)
  let ε : B ⋙ A ≅ 𝟭 _ :=
    (Cat.Hom.toNatIso (F.mapComp' e.inv.op.toLoc e.hom.op.toLoc _ counit)).symm ≪≫
      Cat.Hom.toNatIso (F.mapId _)
  exact Functor.IsEquivalence.mk' B η ε


end Isomorphism

variable {C : Type u} [Category.{v} C]
  {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{a, b}}
  {X X' : C} {I : Type t} {U : I → C}
  {f : ∀ i, U i ⟶ X} {f' : ∀ i, U i ⟶ X'} (p : X' ⟶ X)
  (w : ∀ i, f i = f' i ≫ p)

include w in
private theorem baseAfterFactor {T : C} {i : I} {a : T ⟶ U i} {q : T ⟶ X'}
    (ha : a ≫ f' i = q) : a ≫ f i = q ≫ p := by
  rw [w i, ← Category.assoc, ha]

/-- Restate a descent datum over a new base through which all the original
chart maps factor. The chart objects and test schemes stay the same. -/
def rebaseDatum (D : F.DescentData f) : F.DescentData f' where
  obj := D.obj
  hom _ q _ _ a b ha hb := D.hom (q ≫ p) a b (baseAfterFactor p w ha) (baseAfterFactor p w hb)
  pullHom_hom _ _ g q q' hq _ _ a b ha hb ga gb hga hgb :=
    D.pullHom_hom g (q ≫ p) (q' ≫ p) (by rw [← Category.assoc, hq])
      a b (baseAfterFactor p w ha) (baseAfterFactor p w hb) ga gb hga hgb
  hom_self _ q _ a ha := D.hom_self (q ≫ p) a (baseAfterFactor p w ha)
  hom_comp _ q _ _ _ a b c ha hb hc :=
    D.hom_comp (q ≫ p) a b c (baseAfterFactor p w ha) (baseAfterFactor p w hb) (baseAfterFactor p w hc)

include w in
private theorem rebaseSquare (i : I) : 𝟙 (U i) ≫ f i = f' i ≫ p :=
  (Category.id_comp _).trans (w i)

/-- Keeping the chart objects agrees with the standard descent restriction
functor, via the pseudofunctor identity isomorphisms on every chart. -/
def pullFunctorRebaseIso (D : F.DescentData f) :
    (DescentData.pullFunctor F (p := p) (f' := f') (α := id) (p' := fun i => 𝟙 (U i)) (rebaseSquare p w)).obj D ≅
      rebaseDatum p w D :=
  DescentData.isoMk (fun i => (Cat.Hom.toNatIso (F.mapId _)).app (D.obj i)) (by
    intro Y q i j a b ha hb
    dsimp [rebaseDatum]
    rw [DescentData.pullFunctorObjHom_eq_assoc _ _ _ _ _ (q ≫ p) a b rfl]
    simp [mapComp'_id_comp_inv_app_assoc, mapComp'_id_comp_hom_app, ← Functor.map_comp])

end

end SHIGURE.SchemeDescent
