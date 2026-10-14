import ResearchLean.AG.SafeCoarseningOrder.W1FiniteResults
import ResearchLean.AG.SafeCoarseningOrder.W1NaturalSelection
import ResearchLean.AG.SafeCoarseningOrder.W1LawEvaluation

/-! # W1 同じ有限入力と実評価の一致

## Implementation notes

各原始全15色表を同じG135全領域有理判定へ入力し、実比較の安全性分類と
判定値を同定する。B/Cの正負producerは同じ元入力から発火する。
未評価の存在命題だけを判定値にせず、同じ全A実比較へ有限入力を戻す。
-/
noncomputable section
namespace AAT.AG.SafeCoarseningOrder.W1
open CanonicalResolution ResolutionInvariance TwoPhase AtlasCoefficientFiber
/-- 同じ全A有理判定は、原始全分割の実比較による安全性分類と一致する。 -/
theorem candidate_decision (P : Setoid Bool) (i : Fin 15) :
    allAPreservationDecision (input.quotientComparison (candidate P i))=
      decide (i≠0 ∧ i≠7 ∧ i≠12) := by
  by_cases hs : i≠0 ∧ i≠7 ∧ i≠12
  · have hb := (input.safe_iff_decision (candidate P i)).mp ((candidate_safe_classification P i).mpr hs)
    exact hb.trans ((decide_eq_true_eq.mpr hs).symm)
  · have hb : allAPreservationDecision (input.quotientComparison (candidate P i))≠true := by
      intro h
      exact hs ((candidate_safe_classification P i).mp ((input.safe_iff_decision _).mpr h))
    simp only [Bool.eq_false_of_not_eq_true hb,hs,decide_false]
/-- 指定四Riは同じ全A有理判定で保存trueを返す。 -/
theorem specifiedCut_decision_true (i : ZMod 4) :
    allAPreservationDecision (input.quotientComparison (specifiedCut i))=true :=
  (input.safe_iff_decision _).mp (specifiedCut_safe i)
/-- 全候補表から同じSafe一覧への所属を実分類へ評価する。 -/
theorem mem_safeCoarsenings_candidate (P : Setoid Bool) (i : Fin 15) :
    candidate P i∈input.safeCoarsenings ↔ i≠0 ∧ i≠7 ∧ i≠12 :=
  (input.mem_safeCoarsenings _).trans (candidate_safe_classification P i)
/-- 元全Max一覧の分類を有限所属として保持する。 -/
theorem mem_maximalCoarsenings_iff (R : Coarsening Bool (ZMod 4)) :
    R∈input.maximalCoarsenings ↔ ∃ i : Fin 15, numClasses i=2 ∧ R=candidate ⊤ i :=
  (input.mem_maximalCoarsenings R).trans (maximal_iff_binary R)
/-- 元全Aut有限表の固定極大判定は同じ交互元を返す。 -/
theorem mem_fixedMaximalCoarsenings_iff (R : Coarsening Bool (ZMod 4)) :
    R∈input.fixedMaximalCoarsenings ↔ R=candidate ⊤ 6 :=
  (input.mem_fixedMaximalCoarsenings R).trans (fixed_maximal_iff R)

/-- 全Bool target分割の元二表。 -/
def targetChoice (b : Bool) : Setoid Bool := if b then ⊤ else ⊥
/-- falseで指定する元target分割は等号関係。 -/
theorem targetChoice_false : targetChoice false = ⊥ := rfl
/-- trueで指定する元target分割は全関係。 -/
theorem targetChoice_true : targetChoice true = ⊤ := rfl
/-- 元target二表の関係評価API。 -/
theorem targetChoice_relation (b s t : Bool) : (targetChoice b).r s t ↔ b=true ∨ s=t := by
  cases b
  · constructor
    · intro h; exact Or.inr h
    · rintro (h|h)
      · exact (Bool.false_ne_true h).elim
      · exact h
  · exact iff_of_true True.intro (Or.inl rfl)
/-- 全原始独立分割対をBool×Fin15の全有限表で尽くす。 -/
theorem parameter_candidates_surjective :
    Function.Surjective (fun p : Bool × Fin 15 => candidate (targetChoice p.1) p.2) := by
  intro R
  obtain ⟨i,hi⟩ := classify_coarsening R
  rcases classify_target R.1 with hp|hp
  · exact ⟨(false,i),by simpa only [targetChoice_false,hp] using hi.symm⟩
  · exact ⟨(true,i),by simpa only [targetChoice_true,hp] using hi.symm⟩
/-- 元target二表は同じ非対角対から区別される。 -/
theorem targetChoice_injective : Function.Injective targetChoice := by
  intro b c h
  have hh : (targetChoice b).r false true ↔ (targetChoice c).r false true := by rw [h]
  rw [targetChoice_relation,targetChoice_relation] at hh
  cases b <;> cases c <;> simp_all
/-- 全分割対の元表には重複がない。 -/
theorem parameter_candidates_injective :
    Function.Injective (fun p : Bool × Fin 15 => candidate (targetChoice p.1) p.2) := by
  rintro ⟨b,i⟩ ⟨c,j⟩ h
  have hb := targetChoice_injective (congrArg Prod.fst h)
  have hi := partition_injective (congrArg Prod.snd h)
  exact Prod.ext hb hi
/-- 全分割対は元三十表との全単射を持つ。 -/
def parameterCandidatesEquiv : (Bool × Fin 15) ≃ Coarsening Bool (ZMod 4) :=
  Equiv.ofBijective (fun p => candidate (targetChoice p.1) p.2)
    ⟨parameter_candidates_injective,parameter_candidates_surjective⟩
/-- 原始全表同型は元候補関係を保持する基本API。 -/
@[simp] theorem parameterCandidatesEquiv_apply (p : Bool × Fin 15) :
    parameterCandidatesEquiv p=candidate (targetChoice p.1) p.2 := rfl
/-- 原始target二表×全十五chart表で全粗化は三十個。 -/
theorem allCoarsenings_card_thirty : Fintype.card (Coarsening Bool (ZMod 4))=30 := by
  rw [← Fintype.card_congr parameterCandidatesEquiv,Fintype.card_prod,Fintype.card_bool,Fintype.card_fin]

/-- 実安全性分類を通る元三十表の全parameter。 -/
def safeParameters : Finset (Bool × Fin 15) := Finset.univ.filter (fun p => p.2≠0 ∧ p.2≠7 ∧ p.2≠12)
/-- 元安全parameter有限表の基本所属API。 -/
@[simp] theorem mem_safeParameters (p : Bool × Fin 15) :
    p∈safeParameters ↔ p.2≠0 ∧ p.2≠7 ∧ p.2≠12 := by
  simp only [safeParameters,Finset.mem_filter,Finset.mem_univ,true_and]
/-- 同じ実比較を全三十表へ通して安全parameterは二十四個。 -/
theorem safeParameters_card : safeParameters.card=24 := by decide +kernel
open scoped Classical
/-- B全安全一覧は全原始安全parameterの元候補像に等しい。 -/
theorem safeCoarsenings_eq : input.safeCoarsenings=
    safeParameters.image (fun p => candidate (targetChoice p.1) p.2) := by
  ext R
  rw [input.mem_safeCoarsenings,Finset.mem_image]
  constructor
  · intro hR
    obtain ⟨p,rfl⟩ := parameter_candidates_surjective R
    exact ⟨p,(mem_safeParameters p).mpr ((candidate_safe_classification _ _).mp hR),rfl⟩
  · rintro ⟨p,hp,rfl⟩
    exact (candidate_safe_classification _ _).mpr ((mem_safeParameters p).mp hp)
/-- 全三十候補中の安全元は同じ実比較について二十四個。 -/
theorem safeCoarsenings_card : input.safeCoarsenings.card=24 := by
  rw [safeCoarsenings_eq,Finset.card_image_of_injective _ parameter_candidates_injective,safeParameters_card]
end AAT.AG.SafeCoarseningOrder.W1



#assert_standard_axioms_only AAT.AG.SafeCoarseningOrder
