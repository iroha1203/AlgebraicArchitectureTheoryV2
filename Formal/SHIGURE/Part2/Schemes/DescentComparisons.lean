import Mathlib.CategoryTheory.Sites.Descent.DescentData
import Formal.SHIGURE.Part2.Schemes.QuasiCoherentPullback

/-! # Morphisms and composition comparisons for descent -/

namespace SHIGURE.SchemeDescent

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pseudofunctor
open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat Opposite

noncomputable section

universe t u v a b

variable {C : Type u} [Category.{v} C]
  {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{a, b}}
  {X : C} {ι : Type t} {U : ι → C} {f : ∀ i, U i ⟶ X}
  {D₁ D₂ : F.DescentData f}

/-- A family of chart maps is compatible once it commutes with the descent
comparisons on any chosen geometric double pullbacks. -/
theorem descentHom_comm_of_pullbacks
    {V : ι → ι → C} {p₁ : ∀ i j, V i j ⟶ U i} {p₂ : ∀ i j, V i j ⟶ U j}
    (square : ∀ i j, IsPullback (p₁ i j) (p₂ i j) (f i) (f j))
    (m : ∀ i, D₁.obj i ⟶ D₂.obj i)
    (comm : ∀ i j : ι,
      (F.map (p₁ i j).op.toLoc).toFunctor.map (m i) ≫
        D₂.hom (p₁ i j ≫ f i) (p₁ i j) (p₂ i j) rfl (square i j).w.symm =
      D₁.hom (p₁ i j ≫ f i) (p₁ i j) (p₂ i j) rfl (square i j).w.symm ≫
        (F.map (p₂ i j).op.toLoc).toFunctor.map (m j))
    {T : C} (q : T ⟶ X) {i j : ι}
    (l : T ⟶ U i) (r : T ⟶ U j) (hl : l ≫ f i = q) (hr : r ≫ f j = q) :
    (F.map l.op.toLoc).toFunctor.map (m i) ≫ D₂.hom q l r hl hr =
      D₁.hom q l r hl hr ≫ (F.map r.op.toLoc).toFunctor.map (m j) := by
  let s₁ := p₁ i j
  let s₂ := p₂ i j
  let sq := square i j
  let k := sq.lift l r (hl.trans hr.symm)
  have h₁ : k ≫ s₁ = l := sq.lift_fst _ _ _
  have h₂ : k ≫ s₂ = r := sq.lift_snd _ _ _
  let base := s₁ ≫ f i
  have hbase : k ≫ base = q :=
    (Category.assoc k s₁ (f i)).symm.trans ((congrArg (· ≫ f i) h₁).trans hl)
  let δ₁ := D₁.hom base s₁ s₂ rfl sq.w.symm
  let δ₂ := D₂.hom base s₁ s₂ rfl sq.w.symm
  have pull₁ : D₁.hom q l r hl hr = pullHom δ₁ k l r h₁ h₂ :=
    (D₁.pullHom_hom k base q hbase s₁ s₂ rfl sq.w.symm l r h₁ h₂).symm
  have pull₂ : D₂.hom q l r hl hr = pullHom δ₂ k l r h₁ h₂ :=
    (D₂.pullHom_hom k base q hbase s₁ s₂ rfl sq.w.symm l r h₁ h₂).symm
  let A := Cat.Hom.toNatIso (F.mapComp' s₁.op.toLoc k.op.toLoc l.op.toLoc (congrArg (fun g => g.op.toLoc) h₁))
  let B := Cat.Hom.toNatIso (F.mapComp' s₂.op.toLoc k.op.toLoc r.op.toLoc (congrArg (fun g => g.op.toLoc) h₂))
  let K := (F.map k.op.toLoc).toFunctor
  let P := (F.map s₁.op.toLoc).toFunctor
  let Q := (F.map s₂.op.toLoc).toFunctor
  have a : (F.map l.op.toLoc).toFunctor.map (m i) ≫ A.hom.app (D₂.obj i) =
      A.hom.app (D₁.obj i) ≫ K.map (P.map (m i)) := A.hom.naturality (m i)
  have b : K.map (Q.map (m j)) ≫ B.inv.app (D₂.obj j) =
      B.inv.app (D₁.obj j) ≫ (F.map r.op.toLoc).toFunctor.map (m j) := B.inv.naturality (m j)
  rw [pull₁, pull₂]
  change (F.map l.op.toLoc).toFunctor.map (m i) ≫
    (A.hom.app (D₂.obj i) ≫ K.map δ₂ ≫ B.inv.app (D₂.obj j)) =
    (A.hom.app (D₁.obj i) ≫ K.map δ₁ ≫ B.inv.app (D₁.obj j)) ≫
      (F.map r.op.toLoc).toFunctor.map (m j)
  have comm' : P.map (m i) ≫ δ₂ =
    δ₁ ≫ Q.map (m j) := comm i j
  simp only [Category.assoc]
  rw [← Category.assoc, a, Category.assoc, ← K.map_comp_assoc, comm', K.map_comp,
    Category.assoc, b]

section ModuleComparison

open AlgebraicGeometry Scheme.Modules

variable {T V U : Scheme.{u}} (k : T ⟶ V) (p : V ⟶ U)
  (a : T ⟶ U) (e : k ≫ p = a)
  (M : quasiCoherentModulesPseudofunctor.obj (.mk (op U)))

set_option maxHeartbeats 650000 in
/-- Forgetting quasi-coherence identifies the flexible composition comparison
with the actual inverse image comparison on module sheaves. -/
theorem quasiCoherentMapComp'_hom :
    (quasiCoherentModulesProperty.prop (.mk (op T))).ι.map
      ((quasiCoherentModulesPseudofunctor.mapComp' p.op.toLoc k.op.toLoc a.op.toLoc
        (congrArg (fun f => f.op.toLoc) e)).hom.toNatTrans.app M) =
    (pullbackCongr e.symm).hom.app M.obj ≫ (pullbackComp k p).inv.app M.obj := by
  subst a
  let F := quasiCoherentModulesPseudofunctor
  have eq : F.mapComp' p.op.toLoc k.op.toLoc (k ≫ p).op.toLoc rfl = F.mapComp p.op.toLoc k.op.toLoc :=
    F.mapComp'_eq_mapComp p.op.toLoc k.op.toLoc
  rw [eq]
  change (pullbackComp k p).inv.app M.obj = 𝟙 _ ≫ (pullbackComp k p).inv.app M.obj
  rw [Category.id_comp]

set_option maxHeartbeats 650000 in
/-- The inverse flexible comparison forgets to ordinary composition of
inverse images followed by identification along the given equality. -/
theorem quasiCoherentMapComp'_inv :
    (quasiCoherentModulesProperty.prop (.mk (op T))).ι.map
      ((quasiCoherentModulesPseudofunctor.mapComp' p.op.toLoc k.op.toLoc a.op.toLoc
        (congrArg (fun f => f.op.toLoc) e)).inv.toNatTrans.app M) =
    (pullbackComp k p).hom.app M.obj ≫ (pullbackCongr e).hom.app M.obj := by
  subst a
  let F := quasiCoherentModulesPseudofunctor
  have eq : F.mapComp' p.op.toLoc k.op.toLoc (k ≫ p).op.toLoc rfl = F.mapComp p.op.toLoc k.op.toLoc :=
    F.mapComp'_eq_mapComp p.op.toLoc k.op.toLoc
  rw [eq]
  change (pullbackComp k p).hom.app M.obj = (pullbackComp k p).hom.app M.obj ≫ 𝟙 _
  rw [Category.comp_id]

end ModuleComparison

end

end SHIGURE.SchemeDescent
