import Formal.SHIGURE.Part2.Schemes.Effective.LocalSolution

/-! # A local solution on a test chart of the original family -/

namespace SHIGURE.SchemeDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pseudofunctor Opposite
open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

noncomputable section

universe u v

private abbrev Q := quasiCoherentModulesPseudofunctor.{u}

variable {X Y W : Scheme.{u}} {cover : FppfCover.{u,v} X}
  {D : FppfModuleDescentData cover} {g : Y ⟶ X} (L : EffectiveLocalSolution D g)
  {i : cover.I₀} (a : W ⟶ Y) (b : W ⟶ cover.X i) (e : a ≫ g = b ≫ cover.f i)

namespace EffectiveLocalSolution

/-- The comparison on an actual pulled-back component, with both endpoint
modules and chart maps fixed. -/
def chartHom (i : cover.I₀) :
    (Q.map ((cover.pullback₁ g).f i).op.toLoc).toFunctor.obj L.module ⟶
      (Q.map (cover.pullbackHom g i).op.toLoc).toFunctor.obj (D.obj i) :=
  L.comparison.hom.hom i

/-- The local comparison on a test scheme equipped with maps to the local
base and to a component of the original covering family. -/
def testHom :
    (Q.map a.op.toLoc).toFunctor.obj L.module ⟶
      (Q.map b.op.toLoc).toFunctor.obj (D.obj i) :=
  pullHom (F := Q) (M₁ := L.module) (M₂ := D.obj i)
    (f₁ := (cover.pullback₁ g).f i) (f₂ := cover.pullbackHom g i)
    (L.chartHom i) (pullback.lift a b e) a b
    (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)

/-- Evaluation is the pullback of the fixed component comparison. -/
theorem testHom_eq_pull : L.testHom a b e =
    pullHom (F := Q) (M₁ := L.module) (M₂ := D.obj i)
      (f₁ := (cover.pullback₁ g).f i) (f₂ := cover.pullbackHom g i)
      (L.chartHom i) (pullback.lift a b e) a b
      (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _) := rfl

private theorem isIso_pullHom_of_isIso {C : Type*} [Category C]
    {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{u,u+1}}
    {X₁ X₂ Y T : C} {M₁ : F.obj (.mk (op X₁))} {M₂ : F.obj (.mk (op X₂))}
    {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂}
    (d : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map f₂.op.toLoc).toFunctor.obj M₂)
    [IsIso d] (z : T ⟶ Y) (a : T ⟶ X₁) (b : T ⟶ X₂)
    (ha : z ≫ f₁ = a) (hb : z ≫ f₂ = b) :
    IsIso (pullHom (F := F) (M₁ := M₁) (M₂ := M₂) (f₁ := f₁) (f₂ := f₂) d z a b ha hb) := by
  let left := Cat.Hom.toNatIso (F.mapComp' f₁.op.toLoc z.op.toLoc a.op.toLoc
    (congrArg (fun k => k.op.toLoc) ha))
  let right := Cat.Hom.toNatIso (F.mapComp' f₂.op.toLoc z.op.toLoc b.op.toLoc
    (congrArg (fun k => k.op.toLoc) hb))
  change IsIso (left.hom.app M₁ ≫ (F.map z.op.toLoc).toFunctor.map d ≫ right.inv.app M₂)
  infer_instance

private theorem testHom_isIso : IsIso (L.testHom a b e) := by
  let evaluation : Q.DescentData (cover.pullback₁ g).f ⥤
      Q.obj (.mk (op ((cover.pullback₁ g).X i))) :=
    { obj d := d.obj i, map f := f.hom i, map_id _ := rfl, map_comp _ _ := rfl }
  letI : IsIso (L.chartHom i) := (evaluation.mapIso L.comparison).isIso_hom
  exact isIso_pullHom_of_isIso (F := Q) (M₁ := L.module) (M₂ := D.obj i)
    (f₁ := (cover.pullback₁ g).f i) (f₂ := cover.pullbackHom g i)
    (L.chartHom i) (pullback.lift a b e) a b
    (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)

/-- The test comparison is an isomorphism. -/
def testIso :
    (Q.map a.op.toLoc).toFunctor.obj L.module ≅
      (Q.map b.op.toLoc).toFunctor.obj (D.obj i) :=
  letI := L.testHom_isIso a b e
  asIso (L.testHom a b e)

/-- The morphism underlying the test isomorphism is the test comparison. -/
theorem testIso_hom : (L.testIso a b e).hom = L.testHom a b e := rfl

private theorem pullHom_comp_test {C : Type*} [Category C]
    {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{u,u+1}}
    {X₁ X₂ X₃ K K' : C} {M₁ : F.obj (.mk (op X₁))}
    {M₂ : F.obj (.mk (op X₂))} {M₃ : F.obj (.mk (op X₃))}
    {f₁ : K ⟶ X₁} {f₂ : K ⟶ X₂} {f₃ : K ⟶ X₃}
    (d₁ : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map f₂.op.toLoc).toFunctor.obj M₂)
    (d₂ : (F.map f₂.op.toLoc).toFunctor.obj M₂ ⟶ (F.map f₃.op.toLoc).toFunctor.obj M₃)
    (k : K' ⟶ K) (g₁ : K' ⟶ X₁) (g₂ : K' ⟶ X₂) (g₃ : K' ⟶ X₃)
    (h₁ : k ≫ f₁ = g₁) (h₂ : k ≫ f₂ = g₂) (h₃ : k ≫ f₃ = g₃) :
    pullHom (d₁ ≫ d₂) k g₁ g₃ h₁ h₃ =
      pullHom d₁ k g₁ g₂ h₁ h₂ ≫ pullHom d₂ k g₂ g₃ h₂ h₃ := by
  simp only [pullHom, Functor.map_comp, Category.assoc,
    Cat.Hom.inv_hom_id_toNatTrans_app_assoc]

private theorem pullHom_mapped_test {C : Type*} [Category C]
    {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{u,u+1}}
    {X Y Z : C} {M N : F.obj (.mk (op X))} (d : M ⟶ N)
    (j : Y ⟶ X) (k : Z ⟶ Y) (q : Z ⟶ X) (equal : k ≫ j = q) :
    pullHom ((F.map j.op.toLoc).toFunctor.map d) k q q equal equal =
      (F.map q.op.toLoc).toFunctor.map d := by
  let c := F.mapComp' j.op.toLoc k.op.toLoc q.op.toLoc
    (congrArg (fun z => z.op.toLoc) equal)
  have h : (F.map q.op.toLoc).toFunctor.map d ≫ c.hom.toNatTrans.app N =
      c.hom.toNatTrans.app M ≫
        (F.map k.op.toLoc).toFunctor.map ((F.map j.op.toLoc).toFunctor.map d) :=
    c.hom.toNatTrans.naturality d
  change c.hom.toNatTrans.app M ≫ _ ≫ c.inv.toNatTrans.app N = _
  rw [← Category.assoc, ← h, Category.assoc,
    Cat.Hom.hom_inv_id_toNatTrans_app, Category.comp_id]

private theorem pullHom_intertwines {C : Type*} [Category C]
    {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{u,u+1}}
    {X Y Z W : C} {M N : F.obj (.mk (op X))} {R : F.obj (.mk (op Y))}
    (p : Z ⟶ X) (q : Z ⟶ Y) (j : W ⟶ Z) (r : W ⟶ X) (k : W ⟶ Y)
    (hr : j ≫ p = r) (hk : j ≫ q = k) (m : M ⟶ N)
    (first : (F.map p.op.toLoc).toFunctor.obj M ⟶ (F.map q.op.toLoc).toFunctor.obj R)
    (second : (F.map p.op.toLoc).toFunctor.obj N ⟶ (F.map q.op.toLoc).toFunctor.obj R)
    (compat : (F.map p.op.toLoc).toFunctor.map m ≫ second = first) :
    (F.map r.op.toLoc).toFunctor.map m ≫ pullHom second j r k hr hk =
      pullHom first j r k hr hk := by
  have h := congrArg (fun arrow => pullHom (F := F) arrow j r k hr hk) compat
  change pullHom ((F.map p.op.toLoc).toFunctor.map m ≫ second) j r k hr hk =
    pullHom first j r k hr hk at h
  rw [pullHom_comp_test (F := F) _ _ j r r k hr hr hk,
    pullHom_mapped_test (F := F) m p j r hr] at h
  exact h

/-- The transition between two solutions is identified by either solution's
comparison on every test chart. -/
theorem transition_testHom (K : EffectiveLocalSolution D g) :
    (Q.map a.op.toLoc).toFunctor.map (L.transition K).hom ≫ K.testHom a b e =
      L.testHom a b e := by
  calc
    _ = (Q.map a.op.toLoc).toFunctor.map (L.transition K).hom ≫
        pullHom (F := Q) (M₁ := K.module) (M₂ := D.obj i)
          (f₁ := (cover.pullback₁ g).f i) (f₂ := cover.pullbackHom g i)
          (K.chartHom i) (pullback.lift a b e) a b
          (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _) :=
      congrArg (fun m => (Q.map a.op.toLoc).toFunctor.map (L.transition K).hom ≫ m)
        (K.testHom_eq_pull a b e)
    _ = pullHom (F := Q) (M₁ := L.module) (M₂ := D.obj i)
          (f₁ := (cover.pullback₁ g).f i) (f₂ := cover.pullbackHom g i)
          (L.chartHom i) (pullback.lift a b e) a b
          (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _) :=
      pullHom_intertwines (F := Q) (M := L.module) (N := K.module) (R := D.obj i)
        ((cover.pullback₁ g).f i) (cover.pullbackHom g i) (pullback.lift a b e) a b
        (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _) (L.transition K).hom
        (L.chartHom i) (K.chartHom i) (L.transition_component K i)
    _ = _ := (L.testHom_eq_pull a b e).symm

private theorem pullHom_equal_arrows {C : Type*} [Category C]
    {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{u,u+1}}
    {X₀ X₁ T V : C} {N₀ : F.obj (.mk (op X₀))} {N₁ : F.obj (.mk (op X₁))}
    {a₀ : V ⟶ X₀} {a₁ : V ⟶ X₁}
    (d : (F.map a₀.op.toLoc).toFunctor.obj N₀ ⟶ (F.map a₁.op.toLoc).toFunctor.obj N₁)
    {x y : T ⟶ V} (eq : x = y) (b₀ : T ⟶ X₀) (b₁ : T ⟶ X₁)
    (hx₀ : x ≫ a₀ = b₀) (hx₁ : x ≫ a₁ = b₁)
    (hy₀ : y ≫ a₀ = b₀) (hy₁ : y ≫ a₁ = b₁) :
    pullHom d x b₀ b₁ hx₀ hx₁ = pullHom d y b₀ b₁ hy₀ hy₁ := by
  subst y
  rfl

private theorem pullHom_lift_naturality {C : Type*} [Category C] [HasPullbacks C]
    {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{u,u+1}}
    {X Y U W V : C} (g : Y ⟶ X) (f : U ⟶ X)
    {M : F.obj (.mk (op Y))} {N : F.obj (.mk (op U))}
    (d : (F.map (pullback.fst g f).op.toLoc).toFunctor.obj M ⟶
      (F.map (pullback.snd g f).op.toLoc).toFunctor.obj N)
    (a : W ⟶ Y) (b : W ⟶ U) (e : a ≫ g = b ≫ f)
    (p : V ⟶ W) (a' : V ⟶ Y) (b' : V ⟶ U)
    (pa : p ≫ a = a') (pb : p ≫ b = b') (e' : a' ≫ g = b' ≫ f) :
    pullHom (pullHom d (pullback.lift a b e) a b
      (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)) p a' b' pa pb =
    pullHom d (pullback.lift a' b' e') a' b'
      (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _) := by
  rw [pullHom_pullHom]
  have equal : p ≫ pullback.lift a b e = pullback.lift a' b' e' := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, pa]
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, pb]
  have first : (p ≫ pullback.lift a b e) ≫ pullback.fst g f = a' := by
    rw [Category.assoc, pullback.lift_fst, pa]
  have second : (p ≫ pullback.lift a b e) ≫ pullback.snd g f = b' := by
    rw [Category.assoc, pullback.lift_snd, pb]
  exact pullHom_equal_arrows (F := F) (N₀ := M) (N₁ := N)
    (a₀ := pullback.fst g f) (a₁ := pullback.snd g f)
    (x := p ≫ pullback.lift a b e) (y := pullback.lift a' b' e')
    d equal a' b' first second (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)

/-- Evaluating a local solution on a test chart commutes with further
pullback of that chart. -/
theorem testHom_pull {V : Scheme.{u}} (p : V ⟶ W)
    (a' : V ⟶ Y) (b' : V ⟶ cover.X i) (pa : p ≫ a = a') (pb : p ≫ b = b')
    (e' : a' ≫ g = b' ≫ cover.f i) :
    pullHom (L.testHom a b e) p a' b' pa pb = L.testHom a' b' e' := by
  exact pullHom_lift_naturality (F := Q) g (cover.f i) (L.chartHom i)
    a b e p a' b' pa pb e'

end EffectiveLocalSolution

end

end SHIGURE.SchemeDescent
