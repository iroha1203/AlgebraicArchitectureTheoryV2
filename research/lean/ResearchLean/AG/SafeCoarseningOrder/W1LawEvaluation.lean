import ResearchLean.AG.SafeCoarseningOrder.W1SpecifiedCuts
import ResearchLean.AG.SafeCoarseningOrder.CycleLaws

/-! # W1 指定Law・値blockと全生成比較

## Implementation notes

元Bool非定数Lawの二labelと定数Lawの一labelを同じ全分割実比較へ通す。
同じ署名を持っても異なる発生labelの二重計上を保持する。
署名の一致をlabelの一致に置換すると元実Law比較を変えるため採用しない。
-/
noncomputable section
namespace AAT.AG.SafeCoarseningOrder.W1
open CanonicalResolution ResolutionInvariance TwoPhase
/-- target等号分割の全原始chart候補について、同じ二label実Law比較を評価する。 -/
theorem separating_candidate_defect (i : Fin 15) (hi : i≠0) :
    blockDefect (Cycle.separatingMap 4 (by decide) (partition i))=(2*(numEdges i-numClasses i),0) := by
  have hd := candidate_defect ⊥ i hi Set.univ
  rw [if_pos Set.univ_nonempty] at hd
  exact (Cycle.separatingMap_defect 4 (by decide) (partition i)).trans
    (congrArg (fun d : ℕ × ℕ => (2*d.1,2*d.2)) hd)
/-- target全関係の全候補で定数Lawの実比較を同じ全領域へ戻す。 -/
theorem constant_candidate_defect (i : Fin 15) (hi : i≠0) :
    blockDefect (Cycle.constantMap 4 (by decide) (candidate ⊤ i))=(numEdges i-numClasses i,0) := by
  rw [Cycle.constantMap_defect]
  have hd := candidate_defect ⊤ i hi Set.univ
  rw [if_pos Set.univ_nonempty] at hd
  exact hd
/-- 元全chart併合でも非定数Lawの二値blockを保持し余核2となる。 -/
theorem separating_top_defect :
    blockDefect (Cycle.separatingMap 4 (by decide) (partition 0))=(0,2) := by
  exact (Cycle.separatingMap_defect 4 (by decide) (partition 0)).trans
    (congrArg (fun d : ℕ × ℕ => (2*d.1,2*d.2)) (top_full_defect ⊥))
/-- target/chart全関係の一つの定数labelは実余核1を保持する。 -/
theorem constant_top_defect :
    blockDefect (Cycle.constantMap 4 (by decide) (candidate ⊤ 0))=(0,1) := by
  rw [Cycle.constantMap_defect]
  exact top_full_defect ⊤
/-- 指定四Riで元非定数Law二labelの同じ実比較も保存される。 -/
theorem specifiedCut_separating_bijective (i : ZMod 4) :
    Function.Bijective (Cycle.separatingMap 4 (by decide) (partition (cutIndex i))) :=
  (input.safe_iff_laws (specifiedCut i)).mp (specifiedCut_safe i)
    Cycle.separatingLaw (Cycle.separating_adequate 4 (by decide) (partition (cutIndex i)))
/-- 指定Riの元非定数実Law比較の核/余核は零。 -/
theorem specifiedCut_separating_defect (i : ZMod 4) :
    blockDefect (Cycle.separatingMap 4 (by decide) (partition (cutIndex i)))=(0,0) :=
  (blockDefect_eq_zero_iff_bijective _).mpr (specifiedCut_separating_bijective i)
end AAT.AG.SafeCoarseningOrder.W1

#assert_standard_axioms_only AAT.AG.SafeCoarseningOrder
