import ResearchLean.AG.SafeCoarseningOrder.W1Classification
import ResearchLean.AG.SafeCoarseningOrder.FiniteDecisions
import ResearchLean.AG.SafeCoarseningOrder.W1SpecifiedCuts

/-! # W1 最大元不存在と全共通上界

## Implementation notes

同じ原始二block安全元1/2を用い、全共通上界のtarget/chart関係を全関係へ
強制する。指定実full比較の余核失敗から全上界を排除し、Bの負出力を発火する。
一つのjoin不安全だけでは最大元不存在を証明できないため、全上界を排除する。
-/
noncomputable section
namespace AAT.AG.SafeCoarseningOrder.W1
open CanonicalResolution ResolutionInvariance TwoPhase
/-- 元色表0は全chart関係である。 -/
theorem partition_zero_top : partition 0=⊤ := by
  apply four_rel_ext <;> exact iff_of_true (by rw [partition_relation_iff]; decide +kernel) True.intro
/-- 指定targettop/charttop候補は分割対の元topである。 -/
theorem candidate_zero_top : candidate ⊤ 0=⊤ := Prod.ext rfl partition_zero_top
/-- 同じ原始二block安全元1/2の上界は全分割対topだけ。 -/
theorem common_upper_bounds_top (W : Coarsening Bool (ZMod 4))
    (h1 : candidate ⊤ 1 ≤ W) (h2 : candidate ⊤ 2 ≤ W) : W=⊤ := by
  have ht : W.1=⊤ := le_antisymm le_top h1.1
  have h0 : ∀ v : ZMod 4, W.2.r 0 v := by
    intro v
    fin_cases v
    · exact W.2.refl 0
    · apply h1.2
      rw [partition_relation_iff]
      decide +kernel
    · apply h1.2
      rw [partition_relation_iff]
      decide +kernel
    · apply h2.2
      rw [partition_relation_iff]
      decide +kernel
  apply Prod.ext ht
  apply Setoid.ext; intro v w
  exact iff_of_true (W.2.trans (W.2.symm (h0 v)) (h0 w)) True.intro
/-- 全共通上界は同じ実余核1を持つtopなので安全でない。 -/
theorem common_upper_bounds_unsafe (W : Coarsening Bool (ZMod 4))
    (h1 : candidate ⊤ 1 ≤ W) (h2 : candidate ⊤ 2 ≤ W) : ¬ input.Safe W := by
  rw [common_upper_bounds_top W h1 h2,← candidate_zero_top]
  exact top_not_safe ⊤
/-- 元二安全候補の全上界を排除するBの指定負出力。 -/
def noGreatestOutput : input.NoGreatestWitness where
  left := candidate ⊤ 1
  right := candidate ⊤ 2
  left_safe := (binary_maximal 1 (by decide +kernel)).1
  right_safe := (binary_maximal 2 (by decide +kernel)).1
  exclude := common_upper_bounds_unsafe
  failures W h1 h2 := input.unsafeWitness W (common_upper_bounds_unsafe W h1 h2)
/-- 指定出力の全共通上界排除から最大安全元は存在しない。 -/
theorem no_greatest : ¬ ∃ R, IsGreatest {W | input.Safe W} R := by
  rintro ⟨R,hR⟩
  exact common_upper_bounds_unsafe R (hR.2 noGreatestOutput.left_safe)
    (hR.2 noGreatestOutput.right_safe) hR.1
/-- 同じ全七極大有限一覧によるB最大元判定はfalse。 -/
theorem greatestDecision_false : input.greatestDecision=false := by
  exact Bool.eq_false_of_not_eq_true (fun h => no_greatest (input.greatestDecision_eq_true.mp h))
/-- 同じfalseからBの一般全上界負producerも発火する。 -/
def generatedNoGreatestOutput : input.NoGreatestWitness :=
  input.noGreatestWitness (by rw [greatestDecision_false]; decide)
/-- 元二安全候補の分割対joinは全分割対top。 -/
theorem specified_join_top : candidate ⊤ 1 ⊔ candidate ⊤ 2=⊤ :=
  common_upper_bounds_top _ le_sup_left le_sup_right
/-- 指定joinの同じ実full比較は余核1を持つ。 -/
theorem specified_join_defect :
    blockDefect ((input.quotientComparison (candidate ⊤ 1 ⊔ candidate ⊤ 2)).aSubnerveComparisonHom Set.univ).h1Map=(0,1) := by
  rw [specified_join_top,← candidate_zero_top]
  exact top_full_defect ⊤

/-- 同じtop実比較の指定spikeとperiodによる明示余核失敗証拠。 -/
def topCokerFailure (P : Setoid Bool) : FailureCertificate.CokerFailure
    ((input.quotientComparison (candidate P 0)).aSubnerveComparisonHom Set.univ) where
  z := Cycle.spike 4 (by decide)
  z_cycle := by funext f; exact f.1.elim
  functional := Cycle.period 4 (by decide)
  annihilate_d0 := Cycle.period_boundary 4 (by decide)
  annihilate_comparison x := by
    have hz : x.1=0 := by funext e; exact isEmptyElim (edgeEquiv P 0 e.1)
    rw [hz,map_zero,map_zero]
  normalized := Cycle.period_spike 4 (by decide)
/-- 指定spikeは同じtop実H¹比較のliteral余核で非零となる。 -/
theorem top_cokernel_spike_nonzero (P : Setoid Bool) :
    (LinearMap.range ((input.quotientComparison (candidate P 0)).aSubnerveComparisonHom Set.univ).h1Map).mkQ
      (Cycle.classOf 4 (by decide) (Cycle.spike 4 (by decide)))≠0 := by
  letI := top_H1_subsingleton P
  intro hz
  obtain ⟨x,hx⟩ := (Submodule.Quotient.mk_eq_zero _).mp hz
  have hx0 : x=0 := Subsingleton.elim _ _
  rw [hx0,map_zero] at hx
  exact Cycle.spike_nonzero 4 (by decide) hx.symm
/-- 同じ安全二元joinのfinite判定は負となる。 -/
theorem joinDecision_false : input.joinDecision=false := by
  apply Bool.eq_false_of_not_eq_true
  intro h
  have hs := input.joinDecision_eq_true.mp h _ _
    (binary_maximal 1 (by decide +kernel)).1 (binary_maximal 2 (by decide +kernel)).1
  rw [specified_join_top,← candidate_zero_top] at hs
  exact top_not_safe ⊤ hs
/-- 同じfalseから実cochain証拠付きB join失敗producerを生成する。 -/
def generatedJoinFailure : input.JoinFailure :=
  input.joinFailure (by rw [joinDecision_false]; decide)
end AAT.AG.SafeCoarseningOrder.W1


#assert_standard_axioms_only AAT.AG.SafeCoarseningOrder
