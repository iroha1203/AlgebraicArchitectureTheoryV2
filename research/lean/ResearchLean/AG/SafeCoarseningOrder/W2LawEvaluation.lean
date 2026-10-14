import ResearchLean.AG.SafeCoarseningOrder.W2SpecifiedEvaluation
import ResearchLean.AG.SafeCoarseningOrder.W2UpperBounds

/-! # W2 元Lawと発生labelの重複度

## Implementation notes

指定合併/joinの同じ実比較を元二label非定数Lawと一label定数Lawへ接続する。同署名によるlabel消去は元直和射を変えるため採用しない。
-/
noncomputable section
namespace AAT.AG.SafeCoarseningOrder.W2
open CanonicalResolution ResolutionInvariance TwoPhase
/-- 元二発生labelを保持する非定数Lawの指定欠損は(2,0)。 -/
theorem separating_fold_defect (b : Bool) :
    blockDefect (Cycle.separatingMap 6 (by decide) (foldCandidate ⊥ b).2)=(2,0) := by
  have hd := fold_defect ⊥ b Set.univ
  rw [if_pos Set.univ_nonempty] at hd
  exact (Cycle.separatingMap_defect 6 (by decide) (foldCandidate ⊥ b).2).trans
    (congrArg (fun d : ℕ × ℕ => (2*d.1,2*d.2)) hd)
/-- 全target分割の一発生label定数Lawで指定欠損は(1,0)。 -/
theorem constant_fold_defect (b : Bool) :
    blockDefect (Cycle.constantMap 6 (by decide) (foldCandidate ⊤ b))=(1,0) := by
  rw [Cycle.constantMap_defect]
  have hd := fold_defect ⊤ b Set.univ
  rw [if_pos Set.univ_nonempty] at hd
  exact hd
/-- 元二labelの同じjoin Law比較は核4を持つ。 -/
theorem separating_joined_defect :
    blockDefect (Cycle.separatingMap 6 (by decide) joined.2)=(4,0) := by
  have hd := joined_defect Set.univ
  rw [if_pos Set.univ_nonempty] at hd
  exact (Cycle.separatingMap_defect 6 (by decide) joined.2).trans
    (congrArg (fun d : ℕ × ℕ => (2*d.1,2*d.2)) hd)
/-- 全target分割の一label定数Lawで同じjoin欠損は(2,0)。 -/
theorem constant_joined_defect :
    blockDefect (Cycle.constantMap 6 (by decide) (⊤,joined.2))=(2,0) := by
  rw [Cycle.constantMap_defect]
  rw [joined_chart_eq_upper_candidate ⊤]
  have hd := upperCandidate_defect ⊤ 14 (by decide) Set.univ
  rw [if_pos Set.univ_nonempty] at hd
  exact hd
end AAT.AG.SafeCoarseningOrder.W2

#assert_standard_axioms_only AAT.AG.SafeCoarseningOrder
