import ResearchLean.AG.SafeCoarseningOrder.W2LawEvaluation

/-! # W2 同じ有限全候補と全共通上界

## Implementation notes

Bの全候補/全安全表を元両包含で抽出し、全三十上界と十四安全上界の完全性・重複排除を証明する。候補表の実像だけへ量化域を縮める代替は任意上界の被覆を失うため採用しない。
-/
noncomputable section
namespace AAT.AG.SafeCoarseningOrder.W2
open CanonicalResolution ResolutionInvariance TwoPhase
variable (P : Setoid Bool)
/-- 元joinMap全射から各上界の四点分割indexの等号を反映する。 -/
theorem upper_candidate_injective : Function.Injective (upperCandidate P) := by
  intro i j h
  apply W1.partition_injective
  apply Setoid.ext
  intro v w
  obtain ⟨x,hx⟩ := joinMap_surjective v
  obtain ⟨y,hy⟩ := joinMap_surjective w
  have he : (upperCandidate P i).2.r x y ↔ (upperCandidate P j).2.r x y := by rw [h]
  rw [upperCandidate_relation,upperCandidate_relation,hx,hy] at he
  simpa only [W1.partition_relation_iff] using he
/-- target二表とchart全十五表の上界一覧は重複しない。 -/
theorem upper_parameter_injective : Function.Injective
    (fun p : Bool × Fin 15 => upperCandidate (W1.targetChoice p.1) p.2) := by
  rintro ⟨b,i⟩ ⟨c,j⟩ h
  have hb := W1.targetChoice_injective (congrArg Prod.fst h)
  cases hb
  exact Prod.ext rfl (upper_candidate_injective _ h)
/-- 指定二粗化の任意共通上界をBool×Fin15の全原始表で尽くす。 -/
theorem upper_parameter_complete (R : Coarsening Bool (ZMod 6)) (hR : ac ≤ R ∧ df ≤ R) :
    ∃ p : Bool × Fin 15, R=upperCandidate (W1.targetChoice p.1) p.2 := by
  obtain ⟨i,hi⟩ := classify_upper R ((common_upper_bound_iff R).mp hR)
  rcases W1.classify_target R.1 with hp|hp
  · exact ⟨(false,i),by simpa only [W1.targetChoice_false,hp] using hi⟩
  · exact ⟨(true,i),by simpa only [W1.targetChoice_true,hp] using hi⟩
open scoped Classical
/-- Bの全候補有限一覧から指定二粗化の全共通上界を抽出する。 -/
def commonUpperBounds : Finset (Coarsening Bool (ZMod 6)) :=
  (allCoarsenings (T := Bool) (V := ZMod 6)).filter (fun R => ac ≤ R ∧ df ≤ R)
/-- 全共通上界一覧の所属は元関係の両包含と必要十分。 -/
theorem mem_commonUpperBounds (R : Coarsening Bool (ZMod 6)) :
    R∈commonUpperBounds ↔ ac ≤ R ∧ df ≤ R := by
  simp only [commonUpperBounds,Finset.mem_filter,mem_allCoarsenings,true_and]
/-- 全共通上界一覧は原始target二表×四点十五表の像そのもの。 -/
theorem commonUpperBounds_eq : commonUpperBounds=
    Finset.univ.image (fun p : Bool × Fin 15 => upperCandidate (W1.targetChoice p.1) p.2) := by
  ext R
  rw [mem_commonUpperBounds,Finset.mem_image]
  constructor
  · intro hR
    obtain ⟨p,hp⟩ := upper_parameter_complete R hR
    exact ⟨p,Finset.mem_univ p,hp.symm⟩
  · rintro ⟨p,_,rfl⟩
    exact (common_upper_bound_iff _).mpr (joined_le_upper_candidate _ _)
/-- 全原始表の完全性と重複排除から共通上界は30個。 -/
theorem commonUpperBounds_card : commonUpperBounds.card=30 := by
  rw [commonUpperBounds_eq,Finset.card_image_of_injective _ upper_parameter_injective,
    Finset.card_univ,Fintype.card_prod,Fintype.card_bool,Fintype.card_fin]
/-- 元実安全性分類に一致する上界parameterの全有限表。 -/
def safeUpperParameters : Finset (Bool × Fin 15) :=
  Finset.univ.filter (fun p => W1.numClasses p.2=2)
/-- 安全上界parameter所属は二block色表と必要十分。 -/
theorem mem_safeUpperParameters (p : Bool × Fin 15) :
    p∈safeUpperParameters ↔ W1.numClasses p.2=2 := by
  simp only [safeUpperParameters,Finset.mem_filter,Finset.mem_univ,true_and]
/-- target二表×七二block表の安全parameterは14個。 -/
theorem safeUpperParameters_card : safeUpperParameters.card=14 := by decide +kernel
/-- Bの同じ全安全一覧から指定二粗化の共通上界を抽出する。 -/
def safeCommonUpperBounds : Finset (Coarsening Bool (ZMod 6)) :=
  input.safeCoarsenings.filter (fun R => ac ≤ R ∧ df ≤ R)
/-- 安全共通上界の所属は元両包含と同じ実Safeと必要十分。 -/
theorem mem_safeCommonUpperBounds (R : Coarsening Bool (ZMod 6)) :
    R∈safeCommonUpperBounds ↔ ac ≤ R ∧ df ≤ R ∧ input.Safe R := by
  simp only [safeCommonUpperBounds,Finset.mem_filter,input.mem_safeCoarsenings]
  tauto
/-- 同じ全安全共通上界一覧を原始安全parameterの像へ同定する。 -/
theorem safeCommonUpperBounds_eq : safeCommonUpperBounds=
    safeUpperParameters.image (fun p => upperCandidate (W1.targetChoice p.1) p.2) := by
  ext R
  rw [mem_safeCommonUpperBounds,Finset.mem_image]
  constructor
  · rintro ⟨hac,hdf,hs⟩
    obtain ⟨p,hp⟩ := upper_parameter_complete R ⟨hac,hdf⟩
    have hsafe := hs
    rw [hp,upperCandidate_safe_classification] at hsafe
    exact ⟨p,(mem_safeUpperParameters p).mpr hsafe,hp.symm⟩
  · rintro ⟨p,hp,rfl⟩
    have h := (common_upper_bound_iff (upperCandidate (W1.targetChoice p.1) p.2)).mpr
      (joined_le_upper_candidate (W1.targetChoice p.1) p.2)
    exact ⟨h.1,h.2,(upperCandidate_safe_classification _ _).mpr ((mem_safeUpperParameters p).mp hp)⟩
/-- 同じ実比較の安全共通上界は14個である。 -/
theorem safeCommonUpperBounds_card : safeCommonUpperBounds.card=14 := by
  rw [safeCommonUpperBounds_eq,Finset.card_image_of_injective _ upper_parameter_injective,safeUpperParameters_card]

open AtlasCoefficientFiber
/-- 元二点合併は同じ全A有理判定でも不保存falseを返す。 -/
theorem fold_decision_false (P : Setoid Bool) (b : Bool) :
    allAPreservationDecision (input.quotientComparison (foldCandidate P b))=false :=
  Bool.eq_false_of_not_eq_true (fun h => fold_not_safe P b ((input.safe_iff_decision _).mpr h))
/-- 元二対合併joinは同じ全A有理判定で不保存falseを返す。 -/
theorem joined_decision_false :
    allAPreservationDecision (input.quotientComparison joined)=false :=
  Bool.eq_false_of_not_eq_true (fun h => joined_not_safe ((input.safe_iff_decision _).mpr h))
/-- 全上界の実比較分類は同じ全A有理判定と一致する。 -/
theorem upperCandidate_decision (P : Setoid Bool) (i : Fin 15) :
    allAPreservationDecision (input.quotientComparison (upperCandidate P i))=decide (W1.numClasses i=2) := by
  by_cases hi : W1.numClasses i=2
  · exact ((input.safe_iff_decision _).mp ((upperCandidate_safe_classification P i).mpr hi)).trans
      ((decide_eq_true_eq.mpr hi).symm)
  · have hn : allAPreservationDecision (input.quotientComparison (upperCandidate P i))≠true :=
      fun h => hi ((upperCandidate_safe_classification P i).mp ((input.safe_iff_decision _).mpr h))
    simp only [Bool.eq_false_of_not_eq_true hn,hi,decide_false]
/-- 明示安全共通上界は同じ有限判定から保存trueを返す。 -/
theorem specified_upper_decision_true :
    allAPreservationDecision (input.quotientComparison (upperCandidate ⊥ 3))=true := by
  rw [upperCandidate_decision]
  decide +kernel
/-- 二指定合併は両方不安全であり、Safe対join反例の前件は成立しない。 -/
theorem specified_pair_not_safe : ¬ (input.Safe ac ∧ input.Safe df) := by
  intro h
  have hn := fold_not_safe ⊥ false
  rw [fold_false] at hn
  exact hn h.1
end AAT.AG.SafeCoarseningOrder.W2

#assert_standard_axioms_only AAT.AG.SafeCoarseningOrder
