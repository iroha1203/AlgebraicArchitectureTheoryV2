import Mathlib.CategoryTheory.Sites.Descent.DescentData

/-! # Transport of descent data across chart isomorphisms -/

namespace SHIGURE.SchemeDescent

open CategoryTheory CategoryTheory.Pseudofunctor Opposite
open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

noncomputable section

universe t u v a b

variable {C : Type u} [Category.{v} C]
  {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{a, b}}
  {B : C} {ι : Type t} {U : ι → C} {f : ∀ i, U i ⟶ B}
  (D : F.DescentData f)
  {X : ∀ i, F.obj (.mk (op (U i)))}
  (e : ∀ i, X i ≅ D.obj i)

private theorem rechart_pull {V W : C} {i j : ι}
    (q : V ⟶ B) (q' : W ⟶ B) (g : W ⟶ V) (h : g ≫ q = q')
    (p₁ : V ⟶ U i) (p₂ : V ⟶ U j) (hp₁ : p₁ ≫ f i = q) (hp₂ : p₂ ≫ f j = q)
    (r₁ : W ⟶ U i) (r₂ : W ⟶ U j) (γ₁ : g ≫ p₁ = r₁) (γ₂ : g ≫ p₂ = r₂)
    (hr₁ : r₁ ≫ f i = q') (hr₂ : r₂ ≫ f j = q') :
    pullHom ((F.map p₁.op.toLoc).toFunctor.map (e i).hom ≫ D.hom q p₁ p₂ hp₁ hp₂ ≫
      (F.map p₂.op.toLoc).toFunctor.map (e j).inv) g r₁ r₂ γ₁ γ₂ =
    (F.map r₁.op.toLoc).toFunctor.map (e i).hom ≫ D.hom q' r₁ r₂ hr₁ hr₂ ≫
      (F.map r₂.op.toLoc).toFunctor.map (e j).inv := by
  let A := Cat.Hom.toNatIso (F.mapComp' p₁.op.toLoc g.op.toLoc r₁.op.toLoc
    (congrArg (fun k => k.op.toLoc) γ₁))
  let B := Cat.Hom.toNatIso (F.mapComp' p₂.op.toLoc g.op.toLoc r₂.op.toLoc
    (congrArg (fun k => k.op.toLoc) γ₂))
  let G := (F.map g.op.toLoc).toFunctor
  let P₁ := (F.map p₁.op.toLoc).toFunctor
  let P₂ := (F.map p₂.op.toLoc).toFunctor
  let R₁ := (F.map r₁.op.toLoc).toFunctor
  let R₂ := (F.map r₂.op.toLoc).toFunctor
  let m := D.hom q p₁ p₂ hp₁ hp₂
  have left : R₁.map (e i).hom ≫ A.hom.app (D.obj i) =
    A.hom.app (X i) ≫ G.map (P₁.map (e i).hom) := A.hom.naturality (e i).hom
  have right : G.map (P₂.map (e j).inv) ≫ B.inv.app (X j) =
    B.inv.app (D.obj j) ≫ R₂.map (e j).inv := B.inv.naturality (e j).inv
  have pull : A.hom.app (D.obj i) ≫ G.map m ≫ B.inv.app (D.obj j) =
    D.hom q' r₁ r₂ hr₁ hr₂ :=
    D.pullHom_hom g q q' h p₁ p₂ hp₁ hp₂ r₁ r₂ γ₁ γ₂
  change A.hom.app (X i) ≫ G.map (P₁.map (e i).hom ≫ m ≫ P₂.map (e j).inv) ≫
    B.inv.app (X j) = R₁.map (e i).hom ≫ D.hom q' r₁ r₂ hr₁ hr₂ ≫ R₂.map (e j).inv
  simp only [Functor.map_comp, Category.assoc]
  rw [← Category.assoc (A.hom.app (X i)), ← left, Category.assoc, right]
  have fact := congrArg (· ≫ R₂.map (e j).inv) pull
  simpa only [Category.assoc] using congrArg (R₁.map (e i).hom ≫ ·) fact

/-- Replacing every chart by an isomorphic chart transports the entire
descent datum on the original covering family. -/
def descentRechart : F.DescentData f where
  obj := X
  hom _ q i j a b ha hb := (F.map a.op.toLoc).toFunctor.map (e i).hom ≫
    D.hom q a b ha hb ≫ (F.map b.op.toLoc).toFunctor.map (e j).inv
  pullHom_hom _ _ g q q' h i j a b ha hb ga gb hga hgb := by
    have ha' : ga ≫ f i = q' :=
      (congrArg (· ≫ f i) hga.symm).trans
        ((Category.assoc g a (f i)).trans ((congrArg (g ≫ ·) ha).trans h))
    have hb' : gb ≫ f j = q' :=
      (congrArg (· ≫ f j) hgb.symm).trans
        ((Category.assoc g b (f j)).trans ((congrArg (g ≫ ·) hb).trans h))
    exact rechart_pull D e q q' g h a b ha hb ga gb hga hgb ha' hb'
  hom_self _ q i a ha := by
    let m := (F.map a.op.toLoc).toFunctor.mapIso (e i)
    change m.hom ≫ D.hom q a a ha ha ≫ m.inv = 𝟙 _
    rw [D.hom_self q a ha, Category.id_comp, m.hom_inv_id]
  hom_comp _ q i j k a b c ha hb hc := by
    let A := (F.map a.op.toLoc).toFunctor.mapIso (e i)
    let B := (F.map b.op.toLoc).toFunctor.mapIso (e j)
    let C := (F.map c.op.toLoc).toFunctor.mapIso (e k)
    let m := D.hom q a b ha hb
    let n := D.hom q b c hb hc
    let p := D.hom q a c ha hc
    change (A.hom ≫ m ≫ B.inv) ≫ (B.hom ≫ n ≫ C.inv) = A.hom ≫ p ≫ C.inv
    have h : m ≫ n = p := D.hom_comp q a b c ha hb hc
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [← Category.assoc m, h]

/-- The transported datum and the original datum agree by the given chart isomorphisms. -/
def descentRechartIso : descentRechart D e ≅ D :=
  DescentData.isoMk e (by
    intro W q i j a b ha hb
    let A := (F.map a.op.toLoc).toFunctor.mapIso (e i)
    let B := (F.map b.op.toLoc).toFunctor.mapIso (e j)
    let m := D.hom q a b ha hb
    change A.hom ≫ m = (A.hom ≫ m ≫ B.inv) ≫ B.hom
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id])

end

end SHIGURE.SchemeDescent
