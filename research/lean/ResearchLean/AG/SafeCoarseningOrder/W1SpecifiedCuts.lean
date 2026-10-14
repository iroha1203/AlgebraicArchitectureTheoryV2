import ResearchLean.AG.SafeCoarseningOrder.W1Classification
import ResearchLean.AG.SafeCoarseningOrder.CycleSubsetRank

/-! # W1 の指定四辺縮約と実比較

## Implementation notes

四原始隣接pairだけを合併する関係を全15表へ同定する。
元比較の全領域Jを評価し、target分割も含む全Max分類で極大性の真偽を確定する。
指定四元を極大とする予想を使わず、全分割対の分類へ戻す。
-/
noncomputable section
namespace AAT.AG.SafeCoarseningOrder.W1
open CanonicalResolution ResolutionInvariance TwoPhase
/-- 元四点の等号検査はZMod標準の有限比較である。 -/
local instance zmodFourDecEq : DecidableEq (ZMod 4) := ZMod.decidableEq 4
/-- 各元i/i+1だけのchart併合が全原始一覧に現れるindex。 -/
def cutIndex (i : ZMod 4) : Fin 15 := ![4,10,13,11] i
/-- 固定W1のRi。targetは等号関係、chartは指定隣接pairだけの合併。 -/
def specifiedCut (i : ZMod 4) : Coarsening Bool (ZMod 4) := candidate ⊥ (cutIndex i)
/-- 指定Riのchart関係は同じ一覧の元色値一致。 -/
theorem specifiedCut_chart_iff (i v w : ZMod 4) :
    (specifiedCut i).2.r v w ↔ partitionMap (cutIndex i) v=partitionMap (cutIndex i) w :=
  candidate_chart_iff ⊥ (cutIndex i) v w
/-- 指定Riは隣接二元だけを合併し、他のchartを同一視しない。 -/
theorem specifiedCut_relation (i v w : ZMod 4) :
    (specifiedCut i).2.r v w ↔ v=w ∨ (v=i ∧ w=i+1) ∨ (v=i+1 ∧ w=i) := by
  rw [specifiedCut_chart_iff]
  fin_cases i <;> fin_cases v <;> fin_cases w <;> decide +kernel
/-- 四指定indexは全chart併合index0と異なる。 -/
theorem cutIndex_ne_zero (i : ZMod 4) : cutIndex i≠0 := by fin_cases i <;> decide +kernel
/-- 元指定隣接縮約は三chart・三有向辺を残す。 -/
theorem cut_cell_counts (i : ZMod 4) : numClasses (cutIndex i)=3 ∧ numEdges (cutIndex i)=3 := by
  fin_cases i <;> decide +kernel
/-- 全Ri・空含む全Aの同じ実H¹比較の核/余核欠損は零。 -/
theorem specifiedCut_defect (i : ZMod 4) (A : Set (Quotient (⊥ : Setoid Bool))) :
    blockDefect ((input.quotientComparison (specifiedCut i)).aSubnerveComparisonHom A).h1Map=(0,0) := by
  have hd := candidate_defect ⊥ (cutIndex i) (cutIndex_ne_zero i) A
  rw [(cut_cell_counts i).1,(cut_cell_counts i).2] at hd
  simpa only [Nat.sub_self,ite_self] using hd
/-- 非空Aの全Ri実比較はperiodと全cell比較図式からrank1となる。 -/
theorem specifiedCut_rank (i : ZMod 4) (A : Set (Quotient (⊥ : Setoid Bool)))
    (hA : A.Nonempty) :
    Module.finrank ℚ (LinearMap.range
      ((input.quotientComparison (specifiedCut i)).aSubnerveComparisonHom A).h1Map)=1 :=
  Cycle.actual_nonempty_rank 4 (by decide) (specifiedCut i)
    (quotientEdge ⊥ (cutIndex i) (cutIndex_ne_zero i)) A hA
/-- 全Riは同じ全領域実比較について安全である。 -/
theorem specifiedCut_safe (i : ZMod 4) : input.Safe (specifiedCut i) := by
  apply (input.safe_iff_zeroDefect _).mpr
  exact specifiedCut_defect i
/-- 全Riは全target/chart安全posetの極大元ではない。 -/
theorem specifiedCut_not_maximal (i : ZMod 4) : ¬ Maximal input.Safe (specifiedCut i) := by
  intro hm
  obtain ⟨j,_,he⟩ := (maximal_iff_binary _).mp hm
  have ht : (⊥ : Setoid Bool)=⊤ := congrArg Prod.fst he
  have hft : (⊥ : Setoid Bool).r false true := ht ▸ True.intro
  exact Bool.false_ne_true hft
/-- 指定spikeは同じ元辺0→1だけ1、他辺0。 -/
abbrev specifiedSpike := Cycle.spike 4 (by decide)
/-- 指定periodで元spikeを評価すると1となる。 -/
theorem specifiedSpike_period : Cycle.period 4 (by decide) specifiedSpike=1 :=
  Cycle.period_spike 4 (by decide)
/-- 元spike類は同じ既存実H¹商で非零。 -/
theorem specifiedSpike_nonzero : Cycle.classOf 4 (by decide) specifiedSpike≠0 :=
  Cycle.spike_nonzero 4 (by decide)
end AAT.AG.SafeCoarseningOrder.W1

#assert_standard_axioms_only AAT.AG.SafeCoarseningOrder
