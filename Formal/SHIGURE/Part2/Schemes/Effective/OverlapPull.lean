import Formal.SHIGURE.Part2.Schemes.Effective.OverlapTest

/-! # Naturality of transitions under further base change -/

namespace SHIGURE.SchemeDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pseudofunctor Opposite
open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

noncomputable section

universe u v

private theorem eq_of_chart_pullHom {C : Type*} [Category C]
    {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{u,u+1}}
    {ι : Type v} {X Y Z : C} {U : ι → C} (p : ∀ i, U i ⟶ Z)
    (ff : (F.toDescentData p).FullyFaithful) (s : Z ⟶ X) (t : Z ⟶ Y)
    {M : F.obj (.mk (op X))} {N : F.obj (.mk (op Y))}
    (a b : (F.map s.op.toLoc).toFunctor.obj M ⟶ (F.map t.op.toLoc).toFunctor.obj N)
    (h : ∀ i, pullHom (F := F) (M₁ := M) (M₂ := N) a (p i) (p i ≫ s) (p i ≫ t) rfl rfl =
      pullHom (F := F) (M₁ := M) (M₂ := N) b (p i) (p i ≫ s) (p i ≫ t) rfl rfl) : a = b := by
  apply ff.map_injective
  apply DescentData.hom_ext
  intro i
  change (F.map (p i).op.toLoc).toFunctor.map a = (F.map (p i).op.toLoc).toFunctor.map b
  rw [map_eq_pullHom a (p i) (p i ≫ s) (p i ≫ t) rfl rfl,
    map_eq_pullHom b (p i) (p i ≫ s) (p i ≫ t) rfl rfl, h i]

private theorem eq_pullHom_of_local_triangles {C : Type*} [Category C]
    {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{u,u+1}}
    {ι : Type v} {X Y Z Z' : C} {U : ι → C} (p : ∀ i, U i ⟶ Z')
    (ff : (F.toDescentData p).FullyFaithful) (v : Z' ⟶ Z)
    (s : Z ⟶ X) (t : Z ⟶ Y) (s' : Z' ⟶ X) (t' : Z' ⟶ Y)
    (hs : v ≫ s = s') (ht : v ≫ t = t')
    {M : F.obj (.mk (op X))} {N : F.obj (.mk (op Y))}
    (m : (F.map s.op.toLoc).toFunctor.obj M ⟶ (F.map t.op.toLoc).toFunctor.obj N)
    (n : (F.map s'.op.toLoc).toFunctor.obj M ⟶ (F.map t'.op.toLoc).toFunctor.obj N)
    (R : ∀ i, F.obj (.mk (op (U i))))
    (right : ∀ i, (F.map (p i ≫ t').op.toLoc).toFunctor.obj N ≅ R i)
    (left : ∀ i, (F.map (p i ≫ s').op.toLoc).toFunctor.obj M ⟶ R i)
    (original : ∀ i, pullHom (F := F) (M₁ := M) (M₂ := N) m (p i ≫ v) (p i ≫ s') (p i ≫ t')
        (by rw [Category.assoc, hs]) (by rw [Category.assoc, ht]) ≫ (right i).hom = left i)
    (new : ∀ i, pullHom (F := F) (M₁ := M) (M₂ := N) n (p i) (p i ≫ s') (p i ≫ t') rfl rfl ≫
      (right i).hom = left i) :
    pullHom (F := F) (M₁ := M) (M₂ := N) m v s' t' hs ht = n := by
  apply eq_of_chart_pullHom (F := F) p ff s' t'
  intro i
  apply (cancel_mono (right i).hom).1
  rw [pullHom_pullHom]
  exact (original i).trans (new i).symm

private abbrev Q := quasiCoherentModulesPseudofunctor.{u}

variable {X Y Z T W : Scheme.{u}} {cover : FppfCover.{u,v} X}
  {D : FppfModuleDescentData cover} {g : Y ⟶ X} {g' : Z ⟶ X}
  (L : EffectiveLocalSolution D g) (K : EffectiveLocalSolution D g')
  (q : T ⟶ X) (s : T ⟶ Y) (t : T ⟶ Z) (es : s ≫ g = q) (et : t ≫ g' = q)
  {i : cover.I₀} (r : W ⟶ T) (k : W ⟶ cover.X i) (same : r ≫ q = k ≫ cover.f i)

namespace EffectiveLocalSolution

/-- The test-chart formula with chosen representatives of the composite maps. -/
theorem transitionAt_testHom_along (s' : W ⟶ Y) (t' : W ⟶ Z)
    (hs : r ≫ s = s') (ht : r ≫ t = t') :
    pullHom (F := Q) (M₁ := L.module) (M₂ := K.module)
      (L.transitionAt K q s t es et).hom r s' t' hs ht ≫
      K.testHom t' k (by rw [← ht, Category.assoc, et, same]) =
    L.testHom s' k (by rw [← hs, Category.assoc, es, same]) := by
  subst s' t'
  exact L.transitionAt_testHom K q s t es et r k same

set_option maxHeartbeats 750000 in
/-- The canonical transition between local solutions commutes with arbitrary
further pullback. Equality is checked on the actual fppf pullback family. -/
theorem transitionAt_pull {W' : Scheme.{u}} (v : W' ⟶ T)
    (q' : W' ⟶ X) (s' : W' ⟶ Y) (t' : W' ⟶ Z)
    (hs : v ≫ s = s') (ht : v ≫ t = t') (es' : s' ≫ g = q') (et' : t' ≫ g' = q') :
    pullHom (F := Q) (M₁ := L.module) (M₂ := K.module)
      (L.transitionAt K q s t es et).hom v s' t' hs ht =
        (L.transitionAt K q' s' t' es' et').hom := by
  let p (i : cover.I₀) := (cover.pullback₁ q').f i
  let k (i : cover.I₀) := cover.pullbackHom q' i
  have rightBase (i : cover.I₀) : p i ≫ q' = k i ≫ cover.f i :=
    (cover.pullbackHom_map q' i).symm
  have hq : v ≫ q = q' := by rw [← es, ← Category.assoc, hs, es']
  have leftBase (i : cover.I₀) : (p i ≫ v) ≫ q = k i ≫ cover.f i := by
    rw [Category.assoc, hq, rightBase]
  let R (i : cover.I₀) := Q.obj (.mk (op ((cover.pullback₁ q').X i)))
  let target (i : cover.I₀) : R i := (Q.map (k i).op.toLoc).toFunctor.obj (D.obj i)
  let right (i : cover.I₀) := K.testIso (p i ≫ t') (k i) (by rw [Category.assoc, et', rightBase])
  let left (i : cover.I₀) := L.testHom (p i ≫ s') (k i) (by rw [Category.assoc, es', rightBase])
  apply eq_pullHom_of_local_triangles (F := Q) (M := L.module) (N := K.module) p
    (fppfModuleComparison_fullyFaithful (cover.pullback₁ q')) v s t s' t' hs ht
    (L.transitionAt K q s t es et).hom (L.transitionAt K q' s' t' es' et').hom
    target right left
  · intro i
    have original := L.transitionAt_testHom_along K q s t es et (p i ≫ v) (k i) (leftBase i)
      (p i ≫ s') (p i ≫ t') (by rw [Category.assoc, hs]) (by rw [Category.assoc, ht])
    simpa only [right, testIso_hom, left] using original
  · intro i
    have new := L.transitionAt_testHom K q' s' t' es' et' (p i) (k i) (rightBase i)
    simpa only [right, testIso_hom, left] using new

end EffectiveLocalSolution

end

end SHIGURE.SchemeDescent
