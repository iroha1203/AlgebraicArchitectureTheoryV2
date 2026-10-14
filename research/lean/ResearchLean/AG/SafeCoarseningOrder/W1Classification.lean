import ResearchLean.AG.SafeCoarseningOrder.W1Evaluation
import ResearchLean.AG.SafeCoarseningOrder.FiniteClassification

/-! # W1 全分割対の安全元と極大元

## Implementation notes

原始全15分割とBool全二分割を尽くし、実比較から確定した安全性と
原始関係包含だけで全極大元を分類する。四つの指定辺縮約を極大とは仮定しない。
任意に選んだ極大元だけでは全Max要求を満たさないため、全原始表を分類する。
-/
set_option maxHeartbeats 2400000
noncomputable section
namespace AAT.AG.SafeCoarseningOrder.W1
/-- 元色表の二分割間の包含を全原始chart対で読む基本API。 -/
theorem partition_le_iff (i j : Fin 15) : partition i ≤ partition j ↔
    ∀ v w : ZMod 4, partitionMap i v=partitionMap i w → partitionMap j v=partitionMap j w := Iff.rfl
/-- 元有限色表の関係包含には原始有限全称検査を使う。 -/
instance partitionLEDecidable (i j : Fin 15) : Decidable (partition i ≤ partition j) :=
  inferInstanceAs (Decidable (∀ v w : ZMod 4,
    partitionMap i v=partitionMap i w → partitionMap j v=partitionMap j w))
/-- target/chart独立包含の基本評価API。 -/
theorem candidate_le_iff (P Q : Setoid Bool) (i j : Fin 15) :
    candidate P i ≤ candidate Q j ↔ P ≤ Q ∧ partition i ≤ partition j := Iff.rfl
/-- Bool同値関係は唯一非対角対の関係で全recordが定まる。 -/
theorem bool_rel_ext {P Q : Setoid Bool} (h : P.r false true ↔ Q.r false true) : P=Q := by
  apply Setoid.ext; intro s t
  cases s <;> cases t
  · exact iff_of_true (P.refl false) (Q.refl false)
  · exact h
  · exact (P.comm' (x := true) (y := false)).trans (h.trans (Q.comm' (x := false) (y := true)))
  · exact iff_of_true (P.refl true) (Q.refl true)
/-- target全二分割を排他的仮定なしに原始関係から尽くす。 -/
theorem classify_target (P : Setoid Bool) : P=⊥ ∨ P=⊤ := by
  classical
  by_cases h : P.r false true
  · exact Or.inr (bool_rel_ext (iff_of_true h True.intro))
  · exact Or.inl (bool_rel_ext (iff_of_false h Bool.false_ne_true))
/-- 任意のtarget/chart独立分割対は元候補表に現れる。 -/
theorem classify_coarsening (R : Coarsening Bool (ZMod 4)) :
    ∃ i : Fin 15, R=candidate R.1 i := by
  obtain ⟨i,hi⟩ := classify_chart R.2
  exact ⟨i,Prod.ext rfl hi⟩
/-- 各原始二block色表は実安全性の分類条件を満たす。 -/
theorem binary_index_safe (i : Fin 15) : numClasses i=2 → i≠0 ∧ i≠7 ∧ i≠12 := by
  fin_cases i <;> decide +kernel
/-- 安全な原始色表のうち二block表の上にあるものはその同じ表だけ。 -/
theorem binary_le_iff (i j : Fin 15) :
    numClasses i=2 → (j≠0 ∧ j≠7 ∧ j≠12) → (partition i ≤ partition j ↔ i=j) := by
  fin_cases i <;> fin_cases j <;> decide +kernel
/-- 任意安全候補に対して、上にある原始二block色表を有限構成する。 -/
theorem binary_above (i : Fin 15) : i≠0 → i≠7 → i≠12 →
    ∃ j : Fin 15, numClasses j=2 ∧ partition i ≤ partition j := by
  fin_cases i <;>
    first | exact fun h => (h rfl).elim |
      exact fun _ h => (h rfl).elim | exact fun _ _ h => (h rfl).elim |
      exact fun _ _ _ => ⟨1,by decide +kernel⟩ |
      exact fun _ _ _ => ⟨2,by decide +kernel⟩ |
      exact fun _ _ _ => ⟨3,by decide +kernel⟩ |
      exact fun _ _ _ => ⟨5,by decide +kernel⟩ |
      exact fun _ _ _ => ⟨6,by decide +kernel⟩ |
      exact fun _ _ _ => ⟨8,by decide +kernel⟩ |
      exact fun _ _ _ => ⟨9,by decide +kernel⟩
/-- targetを全関係にした各二block候補は元全安全posetで極大。 -/
theorem binary_maximal (i : Fin 15) (hi : numClasses i=2) :
    Maximal input.Safe (candidate ⊤ i) := by
  refine ⟨(candidate_safe_classification ⊤ i).mpr (binary_index_safe i hi),?_⟩
  intro W hW hle
  obtain ⟨j,hj⟩ := classify_coarsening W
  rw [hj] at hW hle ⊢
  have hsafe := (candidate_safe_classification W.1 j).mp hW
  have horder := (candidate_le_iff ⊤ W.1 i j).mp hle
  have hij := (binary_le_iff i j hi hsafe).mp horder.2
  subst j
  exact (candidate_le_iff W.1 ⊤ i i).mpr ⟨le_top,le_refl _⟩
/-- 全極大安全元はtargettop・原始二block全七表で正確に尽くされる。 -/
theorem maximal_iff_binary (R : Coarsening Bool (ZMod 4)) :
    Maximal input.Safe R ↔ ∃ i : Fin 15, numClasses i=2 ∧ R=candidate ⊤ i := by
  constructor
  · intro hm
    obtain ⟨i,hi⟩ := classify_coarsening R
    have hs := (candidate_safe_classification R.1 i).mp (hi ▸ hm.1)
    obtain ⟨j,hj,hle⟩ := binary_above i hs.1 hs.2.1 hs.2.2
    have hc : R ≤ candidate ⊤ j := by
      rw [hi,candidate_le_iff]
      exact ⟨le_top,hle⟩
    have hback := hm.2 (binary_maximal j hj).1 hc
    exact ⟨j,hj,le_antisymm hc hback⟩
  · rintro ⟨i,hi,rfl⟩
    exact binary_maximal i hi

/-- 元色表の両方向包含は、一覧indexの等号を反映する。 -/
theorem partition_antisymm_indices (i j : Fin 15) :
    partition i ≤ partition j → partition j ≤ partition i → i=j := by
  fin_cases i <;> fin_cases j <;> decide +kernel
/-- 全原始分割一覧に名前だけ異なる重複はない。 -/
theorem partition_injective : Function.Injective partition := by
  intro i j h
  exact partition_antisymm_indices i j (le_of_eq h) (le_of_eq h.symm)
/-- 同じtarget分割で元候補のindexを忘れない。 -/
theorem candidate_injective (P : Setoid Bool) : Function.Injective (candidate P) := by
  intro i j h
  exact partition_injective (congrArg Prod.snd h)
/-- 原始二block色表の全indexを有限生成する。 -/
def binaryIndices : Finset (Fin 15) := Finset.univ.filter (fun i => numClasses i=2)
/-- 原始二block有限一覧の基本所属API。 -/
@[simp] theorem mem_binaryIndices (i : Fin 15) : i∈binaryIndices ↔ numClasses i=2 := by
  simp only [binaryIndices,Finset.mem_filter,Finset.mem_univ,true_and]
/-- 原始有限色表を全量評価した二blockの全七index。 -/
theorem binaryIndices_eq : binaryIndices={1,2,3,5,6,8,9} := by decide +kernel
/-- 元全二block一覧の件数を評価する。 -/
theorem binaryIndices_card : binaryIndices.card=7 := by decide +kernel
open scoped Classical
/-- Bの同じ全極大有限一覧はtargettop・全七二block候補そのもの。 -/
theorem maximalCoarsenings_eq : input.maximalCoarsenings=binaryIndices.image (candidate ⊤) := by
  classical
  ext R
  rw [input.mem_maximalCoarsenings,maximal_iff_binary,Finset.mem_image]
  constructor
  · rintro ⟨i,hi,rfl⟩
    exact ⟨i,(mem_binaryIndices i).mpr hi,rfl⟩
  · rintro ⟨i,hi,hR⟩
    exact ⟨i,(mem_binaryIndices i).mp hi,hR.symm⟩
/-- 全原始極大安全元は正確に七つ。 -/
theorem maximal_card_seven : input.maximalCoarsenings.card=7 := by
  rw [maximalCoarsenings_eq,Finset.card_image_of_injective _ (candidate_injective ⊤),binaryIndices_card]
end AAT.AG.SafeCoarseningOrder.W1


#assert_standard_axioms_only AAT.AG.SafeCoarseningOrder
