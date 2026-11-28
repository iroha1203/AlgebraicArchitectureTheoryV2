import Formal.SHIGURE.Part2.Schemes.Effective.LocalOverlap
import Formal.SHIGURE.Part2.Schemes.Effective.RebaseTest

/-! # Comparing transitions with the original datum on test schemes -/

namespace SHIGURE.SchemeDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pseudofunctor Opposite
open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

noncomputable section

universe u v

private theorem remove_chart_comparisons {C : Type*} [Category C]
    {L R L' R' T : C} (a : L ≅ L') (b : R ≅ R')
    (f : L' ⟶ R') (l : L ⟶ T) (r : R ⟶ T)
    (same : f ≫ b.inv ≫ r = a.inv ≫ l) : (a.hom ≫ f ≫ b.inv) ≫ r = l := by
  simpa only [Category.assoc, a.hom_inv_id_assoc] using congrArg (a.hom ≫ ·) same

private abbrev Q := quasiCoherentModulesPseudofunctor.{u}

variable {X Y Z T W : Scheme.{u}} {cover : FppfCover.{u,v} X}
  {D : FppfModuleDescentData cover} {g : Y ⟶ X} {g' : Z ⟶ X}
  (L : EffectiveLocalSolution D g) (K : EffectiveLocalSolution D g')
  (q : T ⟶ X) (s : T ⟶ Y) (t : T ⟶ Z) (es : s ≫ g = q) (et : t ≫ g' = q)
  {i : cover.I₀} (r : W ⟶ T) (k : W ⟶ cover.X i) (same : r ≫ q = k ≫ cover.f i)

namespace EffectiveLocalSolution

set_option maxHeartbeats 750000 in
/-- On a test chart of the original cover, the transition between two local
solutions identifies their comparisons with the original datum. -/
theorem transitionAt_testHom :
    pullHom (F := Q) (M₁ := L.module) (M₂ := K.module)
      (L.transitionAt K q s t es et).hom r (r ≫ s) (r ≫ t) rfl rfl ≫
      K.testHom (r ≫ t) k (by rw [Category.assoc, et, same]) =
    L.testHom (r ≫ s) k (by rw [Category.assoc, es, same]) := by
  let A := (L.directPull s).rebase es
  let B := (K.directPull t).rebase et
  let α := eqToIso ((L.directPull s).rebase_module es)
  let β := eqToIso ((K.directPull t).rebase_module et)
  have sa : r ≫ (s ≫ g) = k ≫ cover.f i := by rw [es, same]
  have sb : r ≫ (t ≫ g') = k ≫ cover.f i := by rw [et, same]
  have left := (L.directPull s).rebase_testHom es r k sa
  have right := (K.directPull t).rebase_testHom et r k sb
  have compare := A.transition_testHom r k same B
  have combined :
      (Q.map r.op.toLoc).toFunctor.map (L.transitionAt K q s t es et).hom ≫
        (K.directPull t).testHom r k sb = (L.directPull s).testHom r k sa := by
    rw [← right]
    change (Q.map r.op.toLoc).toFunctor.map (α.inv ≫ (A.transition B).hom ≫ β.hom) ≫
      ((Q.map r.op.toLoc).toFunctor.map β.inv ≫ B.testHom r k same) = _
    simp only [Functor.map_comp, Category.assoc, Iso.map_hom_inv_id_assoc]
    rw [compare, left]
  rw [L.directPull_testHom, K.directPull_testHom] at combined
  let C := (Cat.Hom.toNatIso (Q.mapComp' s.op.toLoc r.op.toLoc (r ≫ s).op.toLoc rfl)).app L.module
  let E := (Cat.Hom.toNatIso (Q.mapComp' t.op.toLoc r.op.toLoc (r ≫ t).op.toLoc rfl)).app K.module
  exact remove_chart_comparisons C E ((Q.map r.op.toLoc).toFunctor.map
    (L.transitionAt K q s t es et).hom) _ _ combined

end EffectiveLocalSolution

end

end SHIGURE.SchemeDescent
