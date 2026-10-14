import ResearchLean.AG.SafeCoarseningOrder.FixedMaximalDecision

/-!
# 原始三角形の全粗化・全安全元・全極大元

三chartの全同値関係を原始関係から尽くす。恒等と三つのcutだけがSafeであり、
全極大元は三cutである。原始回転はこの全極大集合のすべてを動かす。

## Implementation notes

三つの非対角関係の真偽を反射・対称・推移に照合して全分割を分類する。
予想した安全一覧を入力せず、全候補分類と同じ実比較の受理済みcut安全性/top失敗から導く。
一つの非自明軌道だけを調べる方法は他の固定極大元を排除しないため用いない。
-/
noncomputable section
namespace AAT.AG.SafeCoarseningOrder
namespace Triangle
open scoped Classical
/-- 三点同値関係は三つの非対角関係で全recordが決まる。 -/
theorem three_rel_ext {P Q : Setoid (Fin 3)}
    (h01 : P.r 0 1 ↔ Q.r 0 1) (h02 : P.r 0 2 ↔ Q.r 0 2) (h12 : P.r 1 2 ↔ Q.r 1 2) : P = Q := by
  apply Setoid.ext; intro x y
  fin_cases x <;> fin_cases y
  · exact iff_of_true (P.refl 0) (Q.refl 0)
  · exact h01
  · exact h02
  · exact (P.comm' (x := 1) (y := 0)).trans (h01.trans (Q.comm' (x := 0) (y := 1)))
  · exact iff_of_true (P.refl 1) (Q.refl 1)
  · exact h12
  · exact (P.comm' (x := 2) (y := 0)).trans (h02.trans (Q.comm' (x := 0) (y := 2)))
  · exact (P.comm' (x := 2) (y := 1)).trans (h12.trans (Q.comm' (x := 1) (y := 2)))
  · exact iff_of_true (P.refl 2) (Q.refl 2)
/-- 三点の全同値関係は恒等・三cut・全関係の五つに尽くされる。 -/
theorem classify_chart (P : Setoid (Fin 3)) :
    P = ⊥ ∨ P = (cut 0).2 ∨ P = (cut 1).2 ∨ P = (cut 2).2 ∨ P = ⊤ := by
  classical
  by_cases h01 : P.r 0 1
  · by_cases h12 : P.r 1 2
    · exact Or.inr (Or.inr (Or.inr (Or.inr (three_rel_ext
        (iff_of_true h01 True.intro) (iff_of_true (P.trans h01 h12) True.intro)
        (iff_of_true h12 True.intro)))))
    · by_cases h02 : P.r 0 2
      · exact (h12 (P.trans (P.symm h01) h02)).elim
      · apply Or.inr; apply Or.inl
        apply three_rel_ext
        · exact iff_of_true h01 (by rw [cut_relation_iff]; decide +kernel)
        · exact iff_of_false h02 (by rw [cut_relation_iff]; decide +kernel)
        · exact iff_of_false h12 (by rw [cut_relation_iff]; decide +kernel)
  · by_cases h12 : P.r 1 2
    · by_cases h02 : P.r 0 2
      · exact (h01 (P.trans h02 (P.symm h12))).elim
      · apply Or.inr; apply Or.inr; apply Or.inl
        apply three_rel_ext
        · exact iff_of_false h01 (by rw [cut_relation_iff]; decide +kernel)
        · exact iff_of_false h02 (by rw [cut_relation_iff]; decide +kernel)
        · exact iff_of_true h12 (by rw [cut_relation_iff]; decide +kernel)
    · by_cases h02 : P.r 0 2
      · apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inl
        apply three_rel_ext
        · exact iff_of_false h01 (by rw [cut_relation_iff]; decide +kernel)
        · exact iff_of_true h02 (by rw [cut_relation_iff]; decide +kernel)
        · exact iff_of_false h12 (by rw [cut_relation_iff]; decide +kernel)
      · apply Or.inl
        apply three_rel_ext
        · exact iff_of_false h01 (by rw [Setoid.bot_def]; decide +kernel)
        · exact iff_of_false h02 (by rw [Setoid.bot_def]; decide +kernel)
        · exact iff_of_false h12 (by rw [Setoid.bot_def]; decide +kernel)
/-- 一点targetの任意同値関係は同じ全recordで一致する。 -/
theorem unit_setoid_eq (P Q : Setoid Unit) : P = Q := by
  apply Setoid.ext; intro x y; cases x; cases y
  exact iff_of_true (P.refl ()) (Q.refl ())
/-- 原始三角形の全target/chart分割対を漏れなく分類する。 -/
theorem classify_coarsening (R : Coarsening Unit (Fin 3)) :
    R = ⊥ ∨ (∃ i : Fin 3, R = cut i) ∨ R = ⊤ := by
  rcases classify_chart R.2 with hb | h0 | h1 | h2 | ht
  · exact Or.inl (Prod.ext (unit_setoid_eq R.1 ⊥) hb)
  · exact Or.inr (Or.inl ⟨0,Prod.ext (unit_setoid_eq R.1 (cut 0).1) h0⟩)
  · exact Or.inr (Or.inl ⟨1,Prod.ext (unit_setoid_eq R.1 (cut 1).1) h1⟩)
  · exact Or.inr (Or.inl ⟨2,Prod.ext (unit_setoid_eq R.1 (cut 2).1) h2⟩)
  · exact Or.inr (Or.inr (Prod.ext (unit_setoid_eq R.1 ⊤) ht))
/-- 同じ実比較で安全な三角形粗化は恒等または三cutのみ。 -/
theorem safe_iff_bottom_or_cut (R : Coarsening Unit (Fin 3)) :
    input.Safe R ↔ R = ⊥ ∨ ∃ i : Fin 3, R = cut i := by
  constructor
  · intro hs
    rcases classify_coarsening R with hb | hc | ht
    · exact Or.inl hb
    · exact Or.inr hc
    · exact (triangle_top_not_safe (ht ▸ hs)).elim
  · rintro (rfl | ⟨i,rfl⟩)
    · exact input.safe_bot
    · exact cut_safe i
/-- 指定隣接二chartを合併するcutはそのcut自身だけ。 -/
theorem cut_neighbor_iff (i j : Fin 3) : (cut j).2.r i (i+1) ↔ i = j := by
  rw [cut_relation_iff]
  fin_cases i <;> fin_cases j <;> decide +kernel
/-- 三cut間の包含は元indexの等号と必要十分。 -/
theorem cut_le_iff (i j : Fin 3) : cut i ≤ cut j ↔ i = j := by
  constructor
  · intro h
    exact (cut_neighbor_iff i j).mp (h.2 ((cut_neighbor_iff i i).mpr rfl))
  · rintro rfl
    exact le_refl _
/-- 各二chart粗化は元恒等分割と異なる。 -/
theorem cut_ne_bot (i : Fin 3) : cut i ≠ ⊥ := by
  intro h
  have hi := (cut_neighbor_iff i i).mpr rfl
  have hh : (⊥ : Coarsening Unit (Fin 3)).2.r i (i+1) := h ▸ hi
  have hn : i ≠ i+1 := by fin_cases i <;> decide +kernel
  exact hn hh
/-- 各cutは同じ全安全集合の極大元。 -/
theorem cut_maximal (i : Fin 3) : Maximal input.Safe (cut i) := by
  refine ⟨cut_safe i,?_⟩
  intro W hW hle
  rcases (safe_iff_bottom_or_cut W).mp hW with rfl | ⟨j,rfl⟩
  · exact bot_le
  · have he := (cut_le_iff i j).mp hle
    subst j
    exact le_refl _
/-- 全極大安全元を三cutで尽くす。 -/
theorem maximal_iff_cut (R : Coarsening Unit (Fin 3)) :
    Maximal input.Safe R ↔ ∃ i : Fin 3, R = cut i := by
  constructor
  · intro h
    rcases (safe_iff_bottom_or_cut R).mp h.1 with rfl | hc
    · have hh := h.2 (cut_safe 0) bot_le
      exact (cut_ne_bot 0 (le_antisymm hh bot_le)).elim
    · exact hc
  · rintro ⟨i,rfl⟩
    exact cut_maximal i
/-- 原始一段回転は各cutを実際に動かす。 -/
theorem rotation_moves_cut (i : Fin 3) : rotation.coarseningOrderIso (cut i) ≠ cut i := by
  rw [rotation_cut]
  intro h
  have hn : i+1 ≠ i := by fin_cases i <;> decide +kernel
  exact hn ((cut_le_iff (i+1) i).mp h.le)
/-- 原始一段回転は全極大元を動かし、固定極大元を一つも残さない。 -/
theorem rotation_moves_all_maximal (R : Coarsening Unit (Fin 3))
    (hm : Maximal input.Safe R) : rotation.coarseningOrderIso R ≠ R := by
  obtain ⟨i,rfl⟩ := (maximal_iff_cut R).mp hm
  exact rotation_moves_cut i
/-- 三cutのindexを全三元で展開する公開API。 -/
theorem exists_cut_iff (R : Coarsening Unit (Fin 3)) :
    (∃ i : Fin 3, R = cut i) ↔ R = cut 0 ∨ R = cut 1 ∨ R = cut 2 := by
  constructor
  · rintro ⟨i,h⟩
    fin_cases i
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · rintro (h | h | h)
    · exact ⟨0,h⟩
    · exact ⟨1,h⟩
    · exact ⟨2,h⟩
/-- 全安全一覧は元恒等と三cutの四元に正確に一致。 -/
theorem safeCoarsenings_eq : input.safeCoarsenings = {⊥,cut 0,cut 1,cut 2} := by
  classical
  apply Finset.ext; intro R
  rw [input.mem_safeCoarsenings,safe_iff_bottom_or_cut,exists_cut_iff]
  simp only [Finset.mem_insert,Finset.mem_singleton]
/-- 全極大一覧は三cutに正確に一致。 -/
theorem maximalCoarsenings_eq : input.maximalCoarsenings = {cut 0,cut 1,cut 2} := by
  classical
  apply Finset.ext; intro R
  rw [input.mem_maximalCoarsenings,maximal_iff_cut,exists_cut_iff]
  simp only [Finset.mem_insert,Finset.mem_singleton]
/-- 異なるindexのcutは元分割として異なる。 -/
theorem cut_injective : Function.Injective cut := fun i j h => (cut_le_iff i j).mp h.le
/-- 全極大安全元の数は三つ。 -/
theorem maximal_card_three : input.maximalCoarsenings.card = 3 := by
  classical
  rw [maximalCoarsenings_eq]
  simp [cut_injective.eq_iff]
/-- 三角形のcut0軌道は全極大元三cutを正確に尽くす。 -/
theorem cut0_orbit : input.orbit (cut 0) = {cut 0,cut 1,cut 2} := by
  apply Finset.ext; intro R
  rw [input.mem_orbit]
  simp only [Finset.mem_insert,Finset.mem_singleton]
  constructor
  · rintro ⟨a,ha⟩
    have hm : Maximal input.Safe R := ha ▸ a.maximal_forward (cut_maximal 0)
    exact (exists_cut_iff R).mp ((maximal_iff_cut R).mp hm)
  · rintro (rfl | rfl | rfl)
    · refine ⟨PrimitiveIso.refl input,?_⟩
      rw [PrimitiveIso.coarseningOrderIso_refl]
      rfl
    · exact ⟨rotation,rotation_cut 0⟩
    · refine ⟨rotation.trans rotation,?_⟩
      rw [PrimitiveIso.coarseningOrderIso_trans,OrderIso.trans_apply,rotation_cut,rotation_cut]
      rfl
/-- 三角形cut0の全軌道は一点軌道ではない。 -/
theorem cut0_orbit_not_singleton : input.orbit (cut 0) ≠ {cut 0} := by
  intro h
  have hf := (input.fixed_iff_orbit_singleton (cut 0)).mpr h
  exact rotation_moves_cut0 (hf rotation)
/-- 全固定極大一覧は空。全Maxに対する原始回転の移動を使う。 -/
theorem fixedMaximalCoarsenings_empty : input.fixedMaximalCoarsenings = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro R hR
  obtain ⟨hm,hf⟩ := (input.mem_fixedMaximalCoarsenings R).mp hR
  exact rotation_moves_all_maximal R hm (hf rotation)
/-- 原始有限表の固定極大判定はfalse。 -/
theorem fixedMaximalDecision_false : input.fixedMaximalDecision = false := by
  have hn : input.fixedMaximalDecision ≠ true := by
    intro h
    obtain ⟨R,hR⟩ := input.fixedMaximalDecision_eq_true.mp h
    rw [fixedMaximalCoarsenings_empty] at hR
    exact Finset.notMem_empty _ hR
  cases hh : input.fixedMaximalDecision
  · rfl
  · exact (hn hh).elim
/-- 指定原始回転による全極大元の移動証拠。全Aut有限表にも所属する。 -/
def specifiedNoFixedOutput : input.NoFixedMaximalWitness where
  move R hm := ⟨rotation,input.mem_allAut rotation,rotation_moves_all_maximal R hm⟩
/-- 同じfalse有限判定から一般の負producerも発火する。 -/
def generatedNoFixedOutput : input.NoFixedMaximalWitness :=
  input.noFixedMaximalWitness (by rw [fixedMaximalDecision_false]; decide +kernel)
end Triangle
end AAT.AG.SafeCoarseningOrder
#assert_standard_axioms_only AAT.AG.SafeCoarseningOrder
