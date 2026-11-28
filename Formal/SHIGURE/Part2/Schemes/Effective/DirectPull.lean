import Formal.SHIGURE.Part2.Schemes.Effective.PullComponent
import Formal.SHIGURE.Part2.Schemes.Effective.TestNaturality
import Formal.SHIGURE.Part2.Schemes.Effective.DescentChartCompatibility

/-! # Direct restriction of a local solution to a further base -/

namespace SHIGURE.SchemeDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pseudofunctor Opposite
open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

noncomputable section

universe u v

private theorem postcompose_test_square {C : Type*} [Category C]
    {A B P Q : C} (v : A ⟶ B) (x : B ⟶ P) (y : B ⟶ Q) (δ δ' : P ⟶ Q)
    (p : A ⟶ P) (q : A ⟶ Q) (hp : p = v ≫ x) (hq : q = v ≫ y)
    (hδ : δ = δ') (ht : x ≫ δ = y) : p ≫ δ' = q := by
  subst δ'
  rw [hp, hq, Category.assoc, ht]

private abbrev Q := quasiCoherentModulesPseudofunctor.{u}

variable {X Y Z : Scheme.{u}} {cover : FppfCover.{u,v} X}
  {D : FppfModuleDescentData cover} {g : Y ⟶ X}
  (L : EffectiveLocalSolution D g) (s : Z ⟶ Y)

namespace EffectiveLocalSolution

section ChartCompatibility

variable {W : Scheme.{u}} {i j : cover.I₀}
  (a : W ⟶ (cover.pullback₁ (s ≫ g)).X i)
  (b : W ⟶ (cover.pullback₁ (s ≫ g)).X j) (h : W ⟶ Z)
  (ha : a ≫ (cover.pullback₁ (s ≫ g)).f i = h)
  (hb : b ≫ (cover.pullback₁ (s ≫ g)).f j = h)
  (l : W ⟶ cover.X i) (k : W ⟶ cover.X j)
  (hl : a ≫ cover.pullbackHom (s ≫ g) i = l)
  (hk : b ≫ cover.pullbackHom (s ≫ g) j = k)

include ha hl in
private theorem direct_original_base_left : l ≫ cover.f i = h ≫ (s ≫ g) := by
  rw [← hl, Category.assoc, cover.pullbackHom_map, ← Category.assoc, ha]

include hb hk in
private theorem direct_original_base_right : k ≫ cover.f j = h ≫ (s ≫ g) := by
  rw [← hk, Category.assoc, cover.pullbackHom_map, ← Category.assoc, hb]

set_option maxHeartbeats 500000 in
private theorem direct_component_test_comm :
    pullHom (F := Q) (M₁ := (Q.map s.op.toLoc).toFunctor.obj L.module) (M₂ := D.obj i)
      (f₁ := (cover.pullback₁ (s ≫ g)).f i) (f₂ := cover.pullbackHom (s ≫ g) i)
      (L.pullComponentIso s i).hom a h l ha hl ≫
      D.hom (h ≫ (s ≫ g)) l k (direct_original_base_left s a h ha l hl)
        (direct_original_base_right s b h hb k hk) =
    pullHom (F := Q) (M₁ := (Q.map s.op.toLoc).toFunctor.obj L.module) (M₂ := D.obj j)
      (f₁ := (cover.pullback₁ (s ≫ g)).f j) (f₂ := cover.pullbackHom (s ≫ g) j)
      (L.pullComponentIso s j).hom b h k hb hk := by
  let v := (Q.mapComp' s.op.toLoc h.op.toLoc (h ≫ s).op.toLoc rfl).inv.toNatTrans.app L.module
  let t := D.hom (h ≫ (s ≫ g)) l k (direct_original_base_left s a h ha l hl)
    (direct_original_base_right s b h hb k hk)
  have first : (h ≫ s) ≫ g = l ≫ cover.f i := by
    rw [Category.assoc, ← direct_original_base_left s a h ha l hl]
  have second : (h ≫ s) ≫ g = k ≫ cover.f j := by
    rw [Category.assoc, ← direct_original_base_right s b h hb k hk]
  have eqBase : (h ≫ s) ≫ g = h ≫ (s ≫ g) := Category.assoc h s g
  have eqTransition : D.hom ((h ≫ s) ≫ g) l k first.symm second.symm = t :=
    descentHom_reindex (F := Q) D eqBase l k first.symm second.symm
  exact postcompose_test_square v (L.testHom (h ≫ s) l first) (L.testHom (h ≫ s) k second)
    (D.hom ((h ≫ s) ≫ g) l k first.symm second.symm) t _ _
    (L.pullComponentIso_pull s a h l ha hl) (L.pullComponentIso_pull s b h k hb hk)
    eqTransition (L.testHom_comm (h ≫ s) l k first second)


end ChartCompatibility

set_option maxHeartbeats 500000 in
/-- A further base change, with comparison specified component by component. -/
def directPull : EffectiveLocalSolution D (s ≫ g) :=
  ⟨(Q.map s.op.toLoc).toFunctor.obj L.module,
    comparisonIsoOfTest Q (f := cover.f) (f' := (cover.pullback₁ (s ≫ g)).f)
      (p := fun i => cover.pullbackHom (s ≫ g) i) (cover.pullbackHom_map (s ≫ g)) D
      ((Q.map s.op.toLoc).toFunctor.obj L.module) (L.pullComponentIso s)
      (fun {W i j} => L.direct_component_test_comm s (W := W) (i := i) (j := j))⟩

/-- The direct solution uses the specified component comparison. -/
theorem directPull_chartHom (i : cover.I₀) :
    (L.directPull s).chartHom i = (L.pullComponentIso s i).hom :=
  comparisonIsoOfTest_hom_hom Q (f := cover.f) (f' := (cover.pullback₁ (s ≫ g)).f)
    (p := fun i => cover.pullbackHom (s ≫ g) i) (cover.pullbackHom_map (s ≫ g)) D
    ((Q.map s.op.toLoc).toFunctor.obj L.module) (L.pullComponentIso s)
    (fun {W i j} => L.direct_component_test_comm s (W := W) (i := i) (j := j)) i

/-- Evaluation of the directly pulled solution is the original evaluation,
preceded by the pseudofunctor comparison for the composite base map. -/
theorem directPull_testHom {W : Scheme.{u}} {i : cover.I₀}
    (a : W ⟶ Z) (b : W ⟶ cover.X i) (e : a ≫ (s ≫ g) = b ≫ cover.f i) :
    (L.directPull s).testHom a b e =
      (Q.mapComp' s.op.toLoc a.op.toLoc (a ≫ s).op.toLoc rfl).inv.toNatTrans.app L.module ≫
        L.testHom (a ≫ s) b (by rw [Category.assoc, e]) := by
  calc
    _ = pullHom (F := Q) (M₁ := (Q.map s.op.toLoc).toFunctor.obj L.module) (M₂ := D.obj i)
        (f₁ := (cover.pullback₁ (s ≫ g)).f i) (f₂ := cover.pullbackHom (s ≫ g) i)
        ((L.directPull s).chartHom i) (pullback.lift a b e) a b
        (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _) :=
      (L.directPull s).testHom_eq_pull a b e
    _ = pullHom (F := Q) (M₁ := (Q.map s.op.toLoc).toFunctor.obj L.module) (M₂ := D.obj i)
        (f₁ := (cover.pullback₁ (s ≫ g)).f i) (f₂ := cover.pullbackHom (s ≫ g) i)
        (L.pullComponentIso s i).hom (pullback.lift a b e) a b
        (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _) :=
      congrArg (fun d => pullHom (F := Q) (M₁ := (Q.map s.op.toLoc).toFunctor.obj L.module)
        (M₂ := D.obj i) (f₁ := (cover.pullback₁ (s ≫ g)).f i)
        (f₂ := cover.pullbackHom (s ≫ g) i) d (pullback.lift a b e) a b
        (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)) (L.directPull_chartHom s i)
    _ = _ := L.pullComponentIso_pull s (pullback.lift a b e) a b
      (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)

end EffectiveLocalSolution

end

end SHIGURE.SchemeDescent
