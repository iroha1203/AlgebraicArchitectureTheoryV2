import ResearchLean.AG.SafeCoarseningOrder.FiniteDecisions
import ResearchLean.AG.SafeCoarseningOrder.SafetyInstances

/-!
# 有限分類と失敗出力の原始正負発火

指定W0は全粗化で安全なので全関係が最大元となる。
原始三角形の全関係商は同じ実比較の失敗一覧とcochain証拠を発火させる。
-/
noncomputable section
namespace AAT.AG.SafeCoarseningOrder
open CanonicalResolution ResolutionInvariance TwoPhase AtlasCoefficientFiber
/-- 全関係表は反射・対称・推移の有限検査を満たす。 -/
theorem relationOK_univ : relationOK (Finset.univ : Finset (Bool × Bool)) := by
  rw [relationOK_iff]
  simp
/-- 空表はBoolの反射性を満たさない。 -/
theorem relationOK_empty_false : ¬ relationOK (∅ : Finset (Bool × Bool)) := by
  decide +kernel

/-- 指定W0の全関係は全安全元に対する最大元。 -/
theorem w0_greatest : IsGreatest {R | w0.Safe R} ⊤ :=
  ⟨w0_safe ⊤,fun _ _ => le_top⟩
/-- 全W0極大元の一覧は、実際に全関係だけを含む。 -/
theorem w0_maximalCoarsenings : w0.maximalCoarsenings = {⊤} := by
  classical
  apply Finset.ext
  intro R
  rw [w0.mem_maximalCoarsenings,Finset.mem_singleton]
  constructor
  · intro h
    exact le_antisymm le_top (h.2 (w0_safe ⊤) le_top)
  · intro h
    subst R
    exact ⟨w0_safe ⊤,fun _ _ _ => le_top⟩
/-- W0最大元の同じ有限判定はtrueを返す。 -/
theorem w0_greatestDecision : w0.greatestDecision = true :=
  w0.greatestDecision_eq_true.mpr ⟨⊤,w0_greatest⟩
/-- W0join閉性の同じ全安全対有限判定はtrueを返す。 -/
theorem w0_joinDecision : w0.joinDecision = true :=
  w0.joinDecision_eq_true.mpr (fun R S _ _ => w0_safe (R ⊔ S))
/-- 全W0粗化で実失敗領域一覧は空。 -/
theorem w0_failureRegions (R : Coarsening Unit Bool) : w0.failureRegions R = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro A hA
  exact (w0.mem_failureRegions R A).mp hA (w0_safe R A)
/-- 原始三角形topの同じ有理全A判定はfalseを返す。 -/
theorem triangle_top_decision_false : allAPreservationDecision (Triangle.input.quotientComparison ⊤) = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  exact triangle_top_not_safe ((Triangle.input.safe_iff_decision ⊤).mpr h)
/-- 原始三角形のtop失敗は有限失敗領域一覧に実際に現れる。 -/
theorem triangle_top_failureRegions_nonempty : (Triangle.input.failureRegions ⊤).Nonempty :=
  Triangle.input.failureRegions_nonempty ⊤ triangle_top_not_safe
/-- 原始有限表と同じ判定から、実cochain証拠付き不安全出力を生成。 -/
def triangle_top_unsafeWitness : Triangle.input.UnsafeWitness ⊤ :=
  Triangle.input.unsafeWitness ⊤ triangle_top_not_safe
/-- 生成出力の代表元と汎関数が同じtop実比較の失敗を再検証する。 -/
theorem triangle_top_certificate_not_safe : ¬ Triangle.input.Safe ⊤ :=
  PrimitiveInput.UnsafeWitness.not_safe Triangle.input triangle_top_unsafeWitness
end AAT.AG.SafeCoarseningOrder
#assert_standard_axioms_only AAT.AG.SafeCoarseningOrder
