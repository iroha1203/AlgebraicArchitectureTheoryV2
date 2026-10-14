import ResearchLean.AG.SafeCoarseningOrder.TriangleCuts

/-!
# 最大元とjoinの原始負の発火

同じ三角形の二つの一辺縮約はSafeだが、そのすべての共通上界は全関係になる。
全関係商の実比較の失敗を使い、最大元とjoinの有限負判定とcochain証拠を生成する。
-/
noncomputable section
namespace AAT.AG.SafeCoarseningOrder
open CanonicalResolution ResolutionInvariance TwoPhase
namespace Triangle
/-- 指定二粗化の全共通上界は、target/chartの両方で全関係。 -/
theorem common_upper_bound_top (W : Coarsening Unit (Fin 3)) (h0 : cut 0 ≤ W) (h1 : cut 1 ≤ W) :
    W = ⊤ := by
  have h01 : W.2.r 0 1 := h0.2 ((cut_relation_iff 0 0 1).mpr
    ((cutMap_values 0).1.trans (cutMap_values 0).2.1.symm))
  have h12 : W.2.r 1 2 := h1.2 ((cut_relation_iff 1 1 2).mpr
    ((cutMap_values 1).1.trans (cutMap_values 1).2.1.symm))
  have h0all : ∀ v : Fin 3, W.2.r 0 v := by
    intro v
    fin_cases v
    · exact W.2.iseqv.refl 0
    · exact h01
    · exact W.2.iseqv.trans h01 h12
  apply Prod.ext
  · apply Setoid.ext
    intro x y
    constructor
    · intro _; trivial
    · intro _
      cases x; cases y
      exact W.1.iseqv.refl ()
  · apply Setoid.ext
    intro v w
    constructor
    · intro _; trivial
    · intro _
      exact W.2.iseqv.trans (W.2.iseqv.symm (h0all v)) (h0all w)
/-- 全共通上界を同じ実不安全性で排除する。 -/
theorem common_upper_bounds_unsafe (W : Coarsening Unit (Fin 3))
    (h0 : cut 0 ≤ W) (h1 : cut 1 ≤ W) : ¬ input.Safe W := by
  rw [common_upper_bound_top W h0 h1]
  exact triangle_top_not_safe
/-- 指定Safe二元のjoinは全関係。 -/
theorem cut_join_top : cut 0 ⊔ cut 1 = ⊤ :=
  common_upper_bound_top _ le_sup_left le_sup_right
/-- 同じ原始三角形に最大安全元はない。 -/
theorem no_greatest : ¬ ∃ R, IsGreatest {W | input.Safe W} R := by
  rintro ⟨R,hR⟩
  exact common_upper_bounds_unsafe R (hR.2 (cut_safe 0)) (hR.2 (cut_safe 1)) hR.1
/-- 最大元の入力生成有限判定はfalseを返す。 -/
theorem greatestDecision_false : input.greatestDecision = false := by
  apply Bool.eq_false_iff.mpr
  exact input.greatestDecision_eq_true.not.mpr no_greatest
/-- 全安全対のjoin閉性は同じ原始三角形で不成立。 -/
theorem not_join_closed : ¬ ∀ R S, input.Safe R → input.Safe S → input.Safe (R ⊔ S) := by
  intro h
  have hs := h (cut 0) (cut 1) (cut_safe 0) (cut_safe 1)
  rw [cut_join_top] at hs
  exact triangle_top_not_safe hs
/-- joinの入力生成有限判定もfalseを返す。 -/
theorem joinDecision_false : input.joinDecision = false := by
  apply Bool.eq_false_iff.mpr
  exact input.joinDecision_eq_true.not.mpr not_join_closed
/-- 指定原始二元と全共通上界の実失敗証拠を保持する具体的負出力。 -/
def noGreatestOutput : input.NoGreatestWitness :=
  ⟨cut 0,cut 1,cut_safe 0,cut_safe 1,common_upper_bounds_unsafe,
    fun W h0 h1 => input.unsafeWitness W (common_upper_bounds_unsafe W h0 h1)⟩
/-- 指定Safe二元と同じjoinの実失敗証拠を保持する具体的負出力。 -/
def joinFailureOutput : input.JoinFailure :=
  ⟨cut 0,cut 1,cut_safe 0,cut_safe 1,input.unsafeWitness (cut 0 ⊔ cut 1)
    (by rw [cut_join_top]; exact triangle_top_not_safe)⟩
/-- 全同じ有限判定からの最大元負producerが原始例で発火。 -/
def noGreatestGenerated : input.NoGreatestWitness :=
  input.noGreatestWitness (by rw [greatestDecision_false]; decide)
/-- 全同じ有限判定からのjoin負producerも原始例で発火。 -/
def joinFailureGenerated : input.JoinFailure :=
  input.joinFailure (by rw [joinDecision_false]; decide)
end Triangle
end AAT.AG.SafeCoarseningOrder
#assert_standard_axioms_only AAT.AG.SafeCoarseningOrder
