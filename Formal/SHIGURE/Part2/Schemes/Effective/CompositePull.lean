import Mathlib.CategoryTheory.Sites.Descent.DescentData

/-! # Pulling a comparison back through a composite -/

namespace SHIGURE.SchemeDescent

open CategoryTheory CategoryTheory.Pseudofunctor Opposite
open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

universe u v a b

variable {C : Type u} [Category.{v} C] {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{a,b}}
  {Y T U V W : C} (s : T ⟶ Y) (p : U ⟶ T) (q : U ⟶ V) (j : W ⟶ U)
  (M : F.obj (.mk (op Y))) (N : F.obj (.mk (op V)))
  (d : (F.map (p ≫ s).op.toLoc).toFunctor.obj M ⟶ (F.map q.op.toLoc).toFunctor.obj N)

/-- The pullback of a comparison whose source is a composite is computed
using the pseudofunctor associativity isomorphism. -/
theorem pullHom_composite_source :
    pullHom (M₁ := (F.map s.op.toLoc).toFunctor.obj M) (M₂ := N)
      ((F.mapComp' s.op.toLoc p.op.toLoc (p ≫ s).op.toLoc rfl).inv.toNatTrans.app M ≫ d)
      j (j ≫ p) (j ≫ q) rfl rfl =
    (F.mapComp' s.op.toLoc (j ≫ p).op.toLoc ((j ≫ p) ≫ s).op.toLoc rfl).inv.toNatTrans.app M ≫
      pullHom d j ((j ≫ p) ≫ s) (j ≫ q) (Category.assoc j p s).symm rfl := by
  simp only [pullHom, Functor.map_comp, Category.assoc]
  rw [F.mapComp'₀₁₃_inv_comp_mapComp'₀₂₃_hom_app_assoc s.op.toLoc p.op.toLoc j.op.toLoc
    (p ≫ s).op.toLoc (j ≫ p).op.toLoc ((j ≫ p) ≫ s).op.toLoc rfl rfl rfl]

/-- The same formula with specified representatives for the two composites. -/
theorem pullHom_composite_source_along (h : W ⟶ T) (k : W ⟶ V)
    (hp : j ≫ p = h) (hq : j ≫ q = k) :
    pullHom (M₁ := (F.map s.op.toLoc).toFunctor.obj M) (M₂ := N)
      ((F.mapComp' s.op.toLoc p.op.toLoc (p ≫ s).op.toLoc rfl).inv.toNatTrans.app M ≫ d)
      j h k hp hq =
    (F.mapComp' s.op.toLoc h.op.toLoc (h ≫ s).op.toLoc rfl).inv.toNatTrans.app M ≫
      pullHom d j (h ≫ s) k (by rw [← Category.assoc, hp]) hq := by
  subst h k
  exact pullHom_composite_source s p q j M N d

end SHIGURE.SchemeDescent
