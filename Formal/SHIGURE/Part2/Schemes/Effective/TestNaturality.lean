import Formal.SHIGURE.Part2.Schemes.Effective.TestComparison

/-! # Local comparisons respect the original descent transitions -/

namespace SHIGURE.SchemeDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pseudofunctor Opposite
open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

noncomputable section

universe u v

private theorem conjugate_square {C : Type*} [Category C]
    {A B D A' B' C' D' : C}
    (a : A ≅ A') (b : B ≅ B') (c : A ≅ C') (d : D ≅ D')
    (f : A' ⟶ B') (k : C' ⟶ D') (δ : B ⟶ D)
    (square : f ≫ (b.inv ≫ δ ≫ d.hom) = (a.inv ≫ c.hom) ≫ k) :
    (a.hom ≫ f ≫ b.inv) ≫ δ = c.hom ≫ k ≫ d.inv := by
  apply (cancel_mono d.hom).1
  have h := congrArg (a.hom ≫ ·) square
  simpa only [Category.assoc, a.hom_inv_id_assoc, d.inv_hom_id, Category.comp_id] using h

private theorem pullbackDatum_comm {C : Type*} [Category C]
    {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{u,u+1}}
    {ι : Type v} {X Y W : C} {U V : ι → C}
    {f : ∀ j, U j ⟶ X} {f' : ∀ j, V j ⟶ Y} {g : Y ⟶ X}
    {p : ∀ j, V j ⟶ U j} (w : ∀ j, p j ≫ f j = f' j ≫ g)
    (D : F.DescentData f) (M : F.obj (.mk (op Y)))
    (c : (F.toDescentData f').obj M ⟶ (DescentData.pullFunctor F (α := id) w).obj D)
    {i j : ι} (a : W ⟶ V i) (b : W ⟶ V j) (h : W ⟶ Y)
    (ha : a ≫ f' i = h) (hb : b ≫ f' j = h)
    (l : W ⟶ U i) (k : W ⟶ U j) (hl : a ≫ p i = l) (hk : b ≫ p j = k) :
    pullHom (F := F) (M₁ := M) (M₂ := D.obj i) (f₁ := f' i) (f₂ := p i)
      (c.hom i) a h l ha hl ≫ D.hom (h ≫ g) l k
      (by rw [← hl, Category.assoc, w, ← Category.assoc, ha])
      (by rw [← hk, Category.assoc, w, ← Category.assoc, hb]) =
        pullHom (F := F) (M₁ := M) (M₂ := D.obj j) (f₁ := f' j) (f₂ := p j)
          (c.hom j) b h k hb hk := by
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
  let left := (F.map a.op.toLoc).toFunctor.map (c.hom i)
  let right := (F.map b.op.toLoc).toFunctor.map (c.hom j)
  have normalize : ((DescentData.pullFunctor F (α := id) w).obj D).hom h a b ha hb =
      B.inv ≫ t ≫ G.hom := by
    simp only [DescentData.pullFunctor_obj, DescentData.pullFunctorObj_hom]
    exact DescentData.pullFunctorObjHom_eq (F := F) (α := id) w D
      (a ≫ f' i) a b (h ≫ g) l k rfl (hb.trans ha.symm) (congrArg (fun q => q ≫ g) ha) hl hk
  have square := c.comm h a b ha hb
  rw [normalize] at square
  change left ≫ (B.inv ≫ t ≫ G.hom) = (A.inv ≫ E.hom) ≫ right at square
  change (A.hom ≫ left ≫ B.inv) ≫ t = E.hom ≫ right ≫ G.inv
  exact conjugate_square A B E G left right t square

private abbrev Q := quasiCoherentModulesPseudofunctor.{u}

variable {X Y W : Scheme.{u}} {cover : FppfCover.{u,v} X}
  {D : FppfModuleDescentData cover} {g : Y ⟶ X} (L : EffectiveLocalSolution D g)

/-- Two evaluations of one local solution over the same test scheme are
related by the original datum's transition. -/
theorem EffectiveLocalSolution.testHom_comm (a : W ⟶ Y) {i j : cover.I₀}
    (b : W ⟶ cover.X i) (c : W ⟶ cover.X j)
    (eb : a ≫ g = b ≫ cover.f i) (ec : a ≫ g = c ≫ cover.f j) :
    L.testHom a b eb ≫ D.hom (a ≫ g) b c eb.symm ec.symm = L.testHom a c ec := by
  calc
    _ = pullHom (F := Q) (M₁ := L.module) (M₂ := D.obj i)
        (f₁ := (cover.pullback₁ g).f i) (f₂ := cover.pullbackHom g i)
        (L.chartHom i) (pullback.lift a b eb) a b
        (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _) ≫
          D.hom (a ≫ g) b c eb.symm ec.symm :=
      congrArg (fun d => d ≫ D.hom (a ≫ g) b c eb.symm ec.symm) (L.testHom_eq_pull a b eb)
    _ = pullHom (F := Q) (M₁ := L.module) (M₂ := D.obj j)
        (f₁ := (cover.pullback₁ g).f j) (f₂ := cover.pullbackHom g j)
        (L.chartHom j) (pullback.lift a c ec) a c
        (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _) :=
      pullbackDatum_comm (F := Q) (f := cover.f) (f' := (cover.pullback₁ g).f)
        (p := fun i => cover.pullbackHom g i) (cover.pullbackHom_map g) D L.module L.comparison.hom
        (pullback.lift a b eb) (pullback.lift a c ec) a
        (pullback.lift_fst _ _ _) (pullback.lift_fst _ _ _) b c
        (pullback.lift_snd _ _ _) (pullback.lift_snd _ _ _)
    _ = _ := (L.testHom_eq_pull a c ec).symm

end

end SHIGURE.SchemeDescent
