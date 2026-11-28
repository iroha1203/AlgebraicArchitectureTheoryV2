import Mathlib.CategoryTheory.Sites.Descent.DescentData

/-! # Constructing a descent morphism from test-chart comparisons -/

namespace SHIGURE.SchemeDescent

open CategoryTheory CategoryTheory.Pseudofunctor Opposite
open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

universe u v

private theorem unconjugate_square {C : Type*} [Category C]
    {A B D A' B' C' D' : C}
    (a : A ≅ A') (b : B ≅ B') (c : A ≅ C') (d : D ≅ D')
    (f : A' ⟶ B') (k : C' ⟶ D') (δ : B ⟶ D)
    (square : (a.hom ≫ f ≫ b.inv) ≫ δ = c.hom ≫ k ≫ d.inv) :
    f ≫ (b.inv ≫ δ ≫ d.hom) = (a.inv ≫ c.hom) ≫ k := by
  apply (cancel_epi a.hom).1
  apply (cancel_mono d.inv).1
  simpa only [Category.assoc, a.hom_inv_id_assoc, d.hom_inv_id, Category.comp_id] using square

/-- Changing the chosen representative for a common base map does not
change a descent transition. -/
theorem descentHom_reindex {C : Type*} [Category C]
    {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{u,u+1}}
    {ι : Type v} {X : C} {U : ι → C} {f : ∀ i, U i ⟶ X}
    (D : F.DescentData f) {T : C} {q q' : T ⟶ X} (same : q = q') {i j : ι}
    (l : T ⟶ U i) (m : T ⟶ U j) (hl : l ≫ f i = q) (hm : m ≫ f j = q) :
    D.hom q l m hl hm = D.hom q' l m (hl.trans same) (hm.trans same) := by
  subst q'
  rfl

/-- Compatibility after pulling the chart maps to a common test scheme is
exactly the commutativity required of a morphism of descent data. -/
theorem descent_comm_of_test {C : Type*} [Category C]
    {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{u,u+1}}
    {ι : Type v} {X Y W : C} {U V : ι → C}
    {f : ∀ j, U j ⟶ X} {f' : ∀ j, V j ⟶ Y} {g : Y ⟶ X}
    {p : ∀ j, V j ⟶ U j} (w : ∀ j, p j ≫ f j = f' j ≫ g)
    (D : F.DescentData f) (M : F.obj (.mk (op Y)))
    {i j : ι} (a : W ⟶ V i) (b : W ⟶ V j) (h : W ⟶ Y)
    (ha : a ≫ f' i = h) (hb : b ≫ f' j = h)
    (l : W ⟶ U i) (k : W ⟶ U j) (hl : a ≫ p i = l) (hk : b ≫ p j = k)
    (leftChart : (F.map (f' i).op.toLoc).toFunctor.obj M ⟶
      (F.map (p i).op.toLoc).toFunctor.obj (D.obj i))
    (rightChart : (F.map (f' j).op.toLoc).toFunctor.obj M ⟶
      (F.map (p j).op.toLoc).toFunctor.obj (D.obj j))
    (compatible : pullHom (F := F) (M₁ := M) (M₂ := D.obj i) (f₁ := f' i) (f₂ := p i)
      leftChart a h l ha hl ≫ D.hom (h ≫ g) l k
      (by rw [← hl, Category.assoc, w, ← Category.assoc, ha])
      (by rw [← hk, Category.assoc, w, ← Category.assoc, hb]) =
        pullHom (F := F) (M₁ := M) (M₂ := D.obj j) (f₁ := f' j) (f₂ := p j)
          rightChart b h k hb hk) :
    (F.map a.op.toLoc).toFunctor.map leftChart ≫
        ((DescentData.pullFunctor F (α := fun j => j) w).obj D).hom h a b ha hb =
      ((F.toDescentData f').obj M).hom h a b ha hb ≫
        (F.map b.op.toLoc).toFunctor.map rightChart := by
  let t := D.hom (h ≫ g) l k (by rw [← hl, Category.assoc, w, ← Category.assoc, ha])
    (by rw [← hk, Category.assoc, w, ← Category.assoc, hb])
  let A := (Cat.Hom.toNatIso (F.mapComp' (f' i).op.toLoc a.op.toLoc h.op.toLoc
    (congrArg (fun p => p.op.toLoc) ha))).app M
  let B := (Cat.Hom.toNatIso (F.mapComp' (p i).op.toLoc a.op.toLoc l.op.toLoc
    (congrArg (fun p => p.op.toLoc) hl))).app (D.obj i)
  let E := (Cat.Hom.toNatIso (F.mapComp' (f' j).op.toLoc b.op.toLoc h.op.toLoc
    (congrArg (fun p => p.op.toLoc) hb))).app M
  let G := (Cat.Hom.toNatIso (F.mapComp' (p j).op.toLoc b.op.toLoc k.op.toLoc
    (congrArg (fun p => p.op.toLoc) hk))).app (D.obj j)
  let left := (F.map a.op.toLoc).toFunctor.map leftChart
  let right := (F.map b.op.toLoc).toFunctor.map rightChart
  have normalize : ((DescentData.pullFunctor F (α := fun j => j) w).obj D).hom h a b ha hb =
      B.inv ≫ t ≫ G.hom := by
    simp only [DescentData.pullFunctor_obj, DescentData.pullFunctorObj_hom]
    exact DescentData.pullFunctorObjHom_eq (F := F) (α := fun j => j) w D
      (a ≫ f' i) a b (h ≫ g) l k rfl (hb.trans ha.symm) (congrArg (fun q => q ≫ g) ha) hl hk
  rw [normalize]
  change left ≫ (B.inv ≫ t ≫ G.hom) = (A.inv ≫ E.hom) ≫ right
  change (A.hom ≫ left ≫ B.inv) ≫ t = E.hom ≫ right ≫ G.inv at compatible
  exact unconjugate_square A B E G left right t compatible

/-- Component isomorphisms satisfying the test-chart equation assemble
into an isomorphism of descent data. -/
def comparisonIsoOfTest {C : Type*} [Category C]
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{u,u+1})
    {ι : Type v} {X Y : C} {U V : ι → C}
    {f : ∀ j, U j ⟶ X} {f' : ∀ j, V j ⟶ Y} {g : Y ⟶ X}
    {p : ∀ j, V j ⟶ U j} (w : ∀ j, p j ≫ f j = f' j ≫ g)
    (D : F.DescentData f) (M : F.obj (.mk (op Y)))
    (e : ∀ i, (F.map (f' i).op.toLoc).toFunctor.obj M ≅
      (F.map (p i).op.toLoc).toFunctor.obj (D.obj i))
    (compatible : ∀ {W : C} {i j : ι} (a : W ⟶ V i) (b : W ⟶ V j) (h : W ⟶ Y)
      (ha : a ≫ f' i = h) (hb : b ≫ f' j = h)
      (l : W ⟶ U i) (k : W ⟶ U j) (hl : a ≫ p i = l) (hk : b ≫ p j = k),
      pullHom (F := F) (M₁ := M) (M₂ := D.obj i) (f₁ := f' i) (f₂ := p i)
        (e i).hom a h l ha hl ≫ D.hom (h ≫ g) l k
          (by rw [← hl, Category.assoc, w, ← Category.assoc, ha])
          (by rw [← hk, Category.assoc, w, ← Category.assoc, hb]) =
      pullHom (F := F) (M₁ := M) (M₂ := D.obj j) (f₁ := f' j) (f₂ := p j)
        (e j).hom b h k hb hk) :
    (F.toDescentData f').obj M ≅ (DescentData.pullFunctor F (α := id) w).obj D := by
  refine DescentData.isoMk (F := F) (f := f')
    (D₁ := (F.toDescentData f').obj M)
    (D₂ := (DescentData.pullFunctor F (α := id) w).obj D) e ?_
  intro W h i j a b ha hb
  exact descent_comm_of_test (F := F) w D M a b h ha hb (a ≫ p i) (b ≫ p j) rfl rfl
    (e i).hom (e j).hom (compatible a b h ha hb (a ≫ p i) (b ≫ p j) rfl rfl)

/-- The chart isomorphisms are preserved by the descent isomorphism. -/
theorem comparisonIsoOfTest_hom_hom {C : Type*} [Category C]
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{u,u+1})
    {ι : Type v} {X Y : C} {U V : ι → C}
    {f : ∀ j, U j ⟶ X} {f' : ∀ j, V j ⟶ Y} {g : Y ⟶ X}
    {p : ∀ j, V j ⟶ U j} (w : ∀ j, p j ≫ f j = f' j ≫ g)
    (D : F.DescentData f) (M : F.obj (.mk (op Y)))
    (e : ∀ i, (F.map (f' i).op.toLoc).toFunctor.obj M ≅
      (F.map (p i).op.toLoc).toFunctor.obj (D.obj i))
    (compatible : ∀ {W : C} {i j : ι} (a : W ⟶ V i) (b : W ⟶ V j) (h : W ⟶ Y)
      (ha : a ≫ f' i = h) (hb : b ≫ f' j = h)
      (l : W ⟶ U i) (k : W ⟶ U j) (hl : a ≫ p i = l) (hk : b ≫ p j = k),
      pullHom (F := F) (M₁ := M) (M₂ := D.obj i) (f₁ := f' i) (f₂ := p i)
        (e i).hom a h l ha hl ≫ D.hom (h ≫ g) l k
          (by rw [← hl, Category.assoc, w, ← Category.assoc, ha])
          (by rw [← hk, Category.assoc, w, ← Category.assoc, hb]) =
      pullHom (F := F) (M₁ := M) (M₂ := D.obj j) (f₁ := f' j) (f₂ := p j)
        (e j).hom b h k hb hk) (i : ι) :
    (comparisonIsoOfTest F w D M e compatible).hom.hom i = (e i).hom := rfl

end SHIGURE.SchemeDescent
