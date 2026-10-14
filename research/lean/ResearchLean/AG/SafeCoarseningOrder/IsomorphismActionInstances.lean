import ResearchLean.AG.SafeCoarseningOrder.SafeIsomorphism
import ResearchLean.AG.SafeCoarseningOrder.CertificateInstances

/-!
# 全原始同型作用の原始発火

指定W0の全関係最大元は全自己同型に固定される。
三角形の原始回転はSafeなcutを動かし、順序作用の恒等/合成と実比較の自然性を発火させる。

## Implementation notes

回転は元chartの巡回加算で定義し、source/targetは原始全射Unitの恒等である。
cutの作用は元関係の公開評価で全三元を検査する。単に非恒等同型を作るだけでなく、
指定Safe粗化を実際に動かす。同次元空間の別同型や選んだ安全一覧は入力しない。
-/
noncomputable section
namespace AAT.AG.SafeCoarseningOrder
open CanonicalResolution ResolutionInvariance TwoPhase
/-- W0の最大安全元は全原始自己同型が固定する。 -/
theorem w0_top_fixed (a : PrimitiveIso w0 w0) : a.coarseningOrderIso ⊤ = ⊤ :=
  a.coarseningOrderIso.map_top
/-- W0の固定元は同じ安全集合の極大元でもある。 -/
theorem w0_top_maximal : Maximal w0.Safe ⊤ :=
  ⟨w0_greatest.1,fun _ _ _ => le_top⟩
namespace Triangle
/-- 元chartの一段回転。逆は二段回転。 -/
def rotationChart : Fin 3 ≃ Fin 3 where
  toFun v := v+1
  invFun v := v+2
  left_inv v := by fin_cases v <;> decide +kernel
  right_inv v := by fin_cases v <;> decide +kernel
/-- 元回転のchart評価。 -/
@[simp] theorem rotationChart_apply (v : Fin 3) : rotationChart v = v+1 := rfl
/-- 元逆回転のchart評価。 -/
@[simp] theorem rotationChart_symm_apply (v : Fin 3) : rotationChart.symm v = v+2 := rfl
/-- 原始q・有向辺・台を保つ三角形の全S/T/V自己同型。 -/
def rotation : PrimitiveIso input input where
  source := Equiv.refl Unit
  target := Equiv.refl Unit
  chart := rotationChart
  read_comm _ := rfl
  edge_iff v w := by
    rw [input_edge_iff,input_edge_iff,rotationChart_apply,rotationChart_apply]
    fin_cases v <;> fin_cases w <;> decide +kernel
  support_iff _ _ := ⟨fun _ => True.intro,fun _ => True.intro⟩
/-- 回転の元sourceはUnit恒等。 -/
@[simp] theorem rotation_source : rotation.source = Equiv.refl Unit := rfl
/-- 回転の元targetはUnit恒等。 -/
@[simp] theorem rotation_target : rotation.target = Equiv.refl Unit := rfl
/-- 回転の元chartは一段回転そのもの。 -/
@[simp] theorem rotation_chart : rotation.chart = rotationChart := rfl
/-- 回転は恒等原始同型と異なる。 -/
theorem rotation_ne_refl : rotation ≠ PrimitiveIso.refl input := by
  intro h
  have hh := congrArg (fun a : PrimitiveIso input input => a.chart 0) h
  have hn : (1 : Fin 3) ≠ 0 := by decide +kernel
  exact hn hh
/-- 全cutの元関係を回転すると次のcutになる。 -/
theorem rotation_cut (i : Fin 3) : rotation.coarseningOrderIso (cut i) = cut (i+1) := by
  apply Prod.ext
  · apply Setoid.ext; intro x y
    rw [PrimitiveIso.coarseningOrderIso_target_rel]
  · apply Setoid.ext; intro v w
    rw [PrimitiveIso.coarseningOrderIso_chart_rel,cut_relation_iff,cut_relation_iff]
    fin_cases i <;> fin_cases v <;> fin_cases w <;> decide +kernel
/-- 指定Safe粗化cut0は原始回転で実際に動く。 -/
theorem rotation_moves_cut0 : rotation.coarseningOrderIso (cut 0) ≠ cut 0 := by
  rw [rotation_cut]
  intro h
  have h01 : (cut 0).2.r 0 1 := (cut_relation_iff 0 0 1).mpr
    ((cutMap_values 0).1.trans (cutMap_values 0).2.1.symm)
  have hn : ¬ (cut 1).2.r 0 1 := (cut_relation_iff 1 0 1).not.mpr (by decide +kernel)
  exact hn (h.symm ▸ h01)
/-- 同じcut0のSafeを全原始同型の実比較共役から輸送する。 -/
theorem rotation_cut0_safe : input.Safe (rotation.coarseningOrderIso (cut 0)) :=
  (rotation.safe_iff (cut 0)).mpr (cut_safe 0)
/-- 原始恒等作用では同じcut0を動かせない。 -/
theorem identity_cut0_fixed : (PrimitiveIso.refl input).coarseningOrderIso (cut 0) = cut 0 := by
  rw [PrimitiveIso.coarseningOrderIso_refl]
  rfl
/-- 不安全な全関係の同じ実比較も回転により不安全のまま。 -/
theorem rotation_top_not_safe : ¬ input.Safe (rotation.coarseningOrderIso ⊤) :=
  (rotation.safe_iff ⊤).not.mpr triangle_top_not_safe
end Triangle
end AAT.AG.SafeCoarseningOrder
#assert_standard_axioms_only AAT.AG.SafeCoarseningOrder
