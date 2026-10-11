import ResearchLean.AG.AtlasDefectComposition.ZeroExtension
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Module.ULift

import Formal.Util.AssertStandardAxioms
/-! # 標準連結射のcocycle持ち上げ・微分・貼り合わせ公式

Implementation notes: 任意SESの持ち上げをdegreewise完全性から作り、mathlib δ_eqに同じ元を渡す。
-/
noncomputable section
open CategoryTheory HomologicalComplex
namespace AAT.AG.AtlasGluingWidth
namespace CohomologyRepresentatives
universe u
variable (F : CochainComplex (ModuleCat.{u} ℚ) ℤ)

/-- 元をULift有理係数からの射として表し、対象の宇宙を保持する。 -/
def scalarPoint {V : ModuleCat.{u} ℚ} (x : V) : ModuleCat.of ℚ (ULift.{u} ℚ) ⟶ V :=
  ModuleCat.ofHom ((LinearMap.toSpanSingleton ℚ V x).comp (ULift.moduleEquiv : ULift.{u} ℚ ≃ₗ[ℚ] ℚ).toLinearMap)

/-- 係数射の評価は通常のスカラー倍。 -/
theorem scalarPoint_apply {V : ModuleCat.{u} ℚ} (x : V) (r : ULift.{u} ℚ) :
    scalarPoint x r = r.down • x := rfl

/-- 係数射と線形射の合成は同じ元の像を表す。 -/
theorem scalarPoint_comp {V W : ModuleCat.{u} ℚ} (x : V) (f : V ⟶ W) :
    scalarPoint x ≫ f = scalarPoint (f x) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  change f (r.down • x) = r.down • f x
  exact map_smul f.hom r.down x

/-- 零元の係数射は零射。 -/
theorem scalarPoint_zero {V : ModuleCat.{u} ℚ} : scalarPoint (0 : V) = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  change r.down • (0 : V) = 0
  exact smul_zero _

/-- cocycleからcyclesへの標準持ち上げ条件を生成する。 -/
theorem scalarPoint_d (m : ℤ) (x : F.X m) (hx : F.d m (m+1) x = 0) :
    scalarPoint x ≫ F.d m (m+1) = 0 := by
  rw [scalarPoint_comp, hx, scalarPoint_zero]

/-- 同じcocycleの標準homology classを取る。 -/
def cycleClass (m : ℤ) (x : F.X m) (hx : F.d m (m+1) x = 0) : F.homology m :=
  (F.liftCycles (scalarPoint x) (m+1) (by simp) (scalarPoint_d F m x hx) ≫ F.homologyπ m) (ULift.up (1 : ℚ))

/-- cyclesの元を表す係数射の持ち上げは、同じcyclesの元である。 -/
theorem liftCycle_point (m : ℤ) (c : F.cycles m)
    (hz : F.d m (m+1) (F.iCycles m c) = 0) :
    (F.liftCycles (scalarPoint (F.iCycles m c)) (m+1) (by simp)
      (scalarPoint_d F m _ hz)) (ULift.up (1 : ℚ)) = c := by
  apply (ModuleCat.mono_iff_injective (F.iCycles m)).mp inferInstance
  have h := congrArg (fun f => f (ULift.up (1 : ℚ)))
    (F.liftCycles_i (scalarPoint (F.iCycles m c)) (m+1) (by simp) (scalarPoint_d F m _ hz))
  change F.iCycles m
      ((F.liftCycles (scalarPoint (F.iCycles m c)) (m+1) (by simp)
        (scalarPoint_d F m _ hz)) (ULift.up (1 : ℚ))) =
    scalarPoint (F.iCycles m c) (ULift.up (1 : ℚ)) at h
  exact h.trans (by
    change (1 : ℚ) • (F.iCycles m c) = F.iCycles m c
    exact one_smul ℚ _)
/-- 全標準homology classは実cocycleのclassとして表せる。 -/
theorem cycleClass_surjective (m : ℤ) (y : F.homology m) :
    ∃ z : F.X m, ∃ hz : F.d m (m+1) z = 0, cycleClass F m z hz = y := by
  obtain ⟨c,hc⟩ := (ModuleCat.epi_iff_surjective (F.homologyπ m)).mp inferInstance y
  have hz : F.d m (m+1) (F.iCycles m c) = 0 := by
    exact congrArg (fun f => f c) (F.iCycles_d m (m+1))
  refine ⟨F.iCycles m c,hz,?_⟩
  change F.homologyπ m
    ((F.liftCycles (scalarPoint (F.iCycles m c)) (m+1) (by simp)
      (scalarPoint_d F m _ hz)) (ULift.up (1 : ℚ))) = y
  rw [liftCycle_point F m c hz, hc]

variable (S : ShortComplex (CochainComplex (ModuleCat.{u} ℚ) ℤ)) (hS : S.ShortExact)

include hS in
/-- 次数別SESからcocycleの持ち上げと微分の原像を存在構成する。 -/
theorem lift_cocycle (m : ℤ) (z : S.X₃.X m) (hz : S.X₃.d m (m+1) z = 0) :
    ∃ (p : S.X₂.X m) (w : S.X₁.X (m+1)),
      S.g.f m p = z ∧ S.f.f (m+1) w = S.X₂.d m (m+1) p ∧
        S.X₁.d (m+1) (m+1+1) w = 0 := by
  have hm := (shortExact_iff_degreewise_shortExact S).mp hS m
  have hn := (shortExact_iff_degreewise_shortExact S).mp hS (m+1)
  obtain ⟨p,hp⟩ := (ModuleCat.epi_iff_surjective _).mp hm.epi_g z
  change S.g.f m p = z at hp
  have hk : S.g.f (m+1) (S.X₂.d m (m+1) p) = 0 := by
    have hc := congrArg (fun f => f p) (S.g.comm m (m+1))
    change S.X₃.d m (m+1) (S.g.f m p) = S.g.f (m+1) (S.X₂.d m (m+1) p) at hc
    rw [hp, hz] at hc
    exact hc.symm
  obtain ⟨w,hw⟩ := ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp hn.exact _).mp hk
  change S.f.f (m+1) w = S.X₂.d m (m+1) p at hw
  refine ⟨p,w,hp,hw,?_⟩
  have hi := (shortExact_iff_degreewise_shortExact S).mp hS (m+1+1)
  apply (ModuleCat.mono_iff_injective _).mp hi.mono_f
  have hc := congrArg (fun f => f w) (S.f.comm (m+1) (m+1+1))
  change S.X₂.d (m+1) (m+1+1) (S.f.f (m+1) w) = S.f.f (m+1+1) (S.X₁.d (m+1) (m+1+1) w) at hc
  rw [hw] at hc
  have hd := congrArg (fun f => f p) (S.X₂.d_comp_d m (m+1) (m+1+1))
  change S.X₂.d (m+1) (m+1+1) (S.X₂.d m (m+1) p) = 0 at hd
  rw [hd] at hc
  simpa only [map_zero] using hc.symm

/-- 持ち上げの微分を貼り合わせたclassは符号込みで標準δの像に一致する。 -/
theorem connecting_cycleClass (m : ℤ) (z : S.X₃.X m) (hz : S.X₃.d m (m+1) z = 0)
    (p : S.X₂.X m) (hp : S.g.f m p = z) (w : S.X₁.X (m+1))
    (hw : S.f.f (m+1) w = S.X₂.d m (m+1) p)
    (hwc : S.X₁.d (m+1) (m+1+1) w = 0) :
    hS.δ m (m+1) rfl (cycleClass S.X₃ m z hz) = cycleClass S.X₁ (m+1) w hwc := by
  have h := hS.δ_eq m (m+1) rfl (scalarPoint z) (scalarPoint_d S.X₃ m z hz)
    (scalarPoint p) (by rw [scalarPoint_comp, hp])
    (scalarPoint w) (by rw [scalarPoint_comp, scalarPoint_comp, hw])
    (m+1+1) (by simp)
  simpa only [cycleClass, ModuleCat.comp_apply] using
    congrArg (fun f => f (ULift.up (1 : ℚ))) h
include hS in
/-- 同じcocycleの任意二つの持ち上げは、同じ標準連結classを与える。 -/
theorem connecting_choice_independent (m : ℤ) (z : S.X₃.X m)
    (hz : S.X₃.d m (m+1) z = 0)
    (p p' : S.X₂.X m) (hp : S.g.f m p = z) (hp' : S.g.f m p' = z)
    (w w' : S.X₁.X (m+1))
    (hw : S.f.f (m+1) w = S.X₂.d m (m+1) p)
    (hw' : S.f.f (m+1) w' = S.X₂.d m (m+1) p')
    (hc : S.X₁.d (m+1) (m+1+1) w = 0)
    (hc' : S.X₁.d (m+1) (m+1+1) w' = 0) :
    cycleClass S.X₁ (m+1) w hc = cycleClass S.X₁ (m+1) w' hc' := by
  rw [← connecting_cycleClass S hS m z hz p hp w hw hc,
    connecting_cycleClass S hS m z hz p' hp' w' hw' hc']
/-- 交差側のhomology classを保つ代表元変更も連結classを保つ。 -/
theorem connecting_representative_independent (m : ℤ) (z z' : S.X₃.X m)
    (hz : S.X₃.d m (m+1) z = 0) (hz' : S.X₃.d m (m+1) z' = 0)
    (heq : cycleClass S.X₃ m z hz = cycleClass S.X₃ m z' hz') :
    hS.δ m (m+1) rfl (cycleClass S.X₃ m z hz) =
      hS.δ m (m+1) rfl (cycleClass S.X₃ m z' hz') := by rw [heq]
end CohomologyRepresentatives
end AAT.AG.AtlasGluingWidth
#assert_standard_axioms_only AAT.AG.AtlasGluingWidth
