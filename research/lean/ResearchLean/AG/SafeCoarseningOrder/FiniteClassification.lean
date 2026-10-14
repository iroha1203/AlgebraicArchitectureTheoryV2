import ResearchLean.AG.SafeCoarseningOrder.IdentitySafety
import Mathlib.Order.Minimal

/-!
# 全原始分割表と安全元の有限分類

有限な関係表をすべて生成し、反射・対称・推移の有限検査を通る表を同値関係へ戻す。
入力生成された同じ全A有理判定で安全元を選び、関係包含によって全極大元を得る。
## Implementation notes

元順序対の冪集合から全関係表を取る。自己同型軌道で商を取らず、独立な
分割対をそのまま保存する。全一覧のfilterだけで安全性と極大性を定め、
安全性の上方・下方単調性は使用しない。
-/

noncomputable section
namespace AAT.AG.SafeCoarseningOrder
open CanonicalResolution ResolutionInvariance TwoPhase AtlasCoefficientFiber
variable {X : Type} [Fintype X]
/-- 元の同値関係を有限順序対表として記録する。 -/
def relationTable (P : Setoid X) : Finset (X × X) := by
  classical
  exact Finset.univ.filter (fun p => P.r p.1 p.2)
/-- 有限関係表が反射・対称・推移を満たす条件。 -/
def relationOK (F : Finset (X × X)) : Prop :=
  (∀ x, (x,x) ∈ F) ∧ (∀ x y, (x,y) ∈ F → (y,x) ∈ F) ∧
    (∀ x y z, (x,y) ∈ F → (y,z) ∈ F → (x,z) ∈ F)
omit [Fintype X] in
/-- 関係表検査の公開特徴づけ。下流は反射・対称・推移をこのAPIで読む。 -/
theorem relationOK_iff (F : Finset (X × X)) : relationOK F ↔
    (∀ x, (x,x) ∈ F) ∧ (∀ x y, (x,y) ∈ F → (y,x) ∈ F) ∧
      (∀ x y z, (x,y) ∈ F → (y,z) ∈ F → (x,z) ∈ F) := Iff.rfl
/-- 全有限量化を決定し、関係表の反射・対称・推移検査を有限filterへ渡す。 -/
instance [DecidableEq X] (F : Finset (X × X)) : Decidable (relationOK F) := by
  unfold relationOK
  infer_instance
/-- 有限検査を通過した表から同値関係の全fieldを生成。 -/
def fromRelationTable (F : Finset (X × X)) (h : relationOK F) : Setoid X where
  r x y := (x,y) ∈ F
  iseqv := ⟨h.1,fun hxy => h.2.1 _ _ hxy,fun hxy hyz => h.2.2 _ _ _ hxy hyz⟩
/-- 全順序対表の冪集合から全同値関係を尽くす。 -/
noncomputable def allSetoids [DecidableEq X] : Finset (Setoid X) := by
  classical
  exact ((Finset.univ : Finset (X × X)).powerset.filter relationOK).attach.image
    (fun F => fromRelationTable F.1 (Finset.mem_filter.mp F.2).2)
/-- 任意の同値関係は生成一覧に現れる（完全性）。 -/
theorem mem_allSetoids [DecidableEq X] (P : Setoid X) : P ∈ allSetoids := by
  classical
  have hok : relationOK (relationTable P) := by
    refine ⟨?_,?_,?_⟩
    · intro x; simpa [relationTable] using P.iseqv.refl x
    · intro x y h; simpa [relationTable] using P.symm (by simpa [relationTable] using h)
    · intro x y z h k
      simpa [relationTable] using P.trans (by simpa [relationTable] using h)
        (by simpa [relationTable] using k)
  have hmem : relationTable P ∈ (Finset.univ : Finset (X × X)).powerset.filter relationOK := by
    simp only [Finset.mem_filter,Finset.mem_powerset,Finset.subset_univ,true_and]
    exact hok
  apply Finset.mem_image.mpr
  refine ⟨⟨relationTable P,hmem⟩,Finset.mem_attach _ _,?_⟩
  apply Setoid.ext; intro x y
  simp [fromRelationTable,relationTable]

/-- 全有限表の完全性から同値関係全体の有限instanceを生成する。 -/
noncomputable instance setoidFintype : Fintype (Setoid X) := by
  classical
  exact ⟨allSetoids, mem_allSetoids⟩

variable {S T V : Type} [Fintype S] [Fintype T] [Fintype V]
/-- targetとchartの独立な全分割対を尽くす。 -/
def allCoarsenings : Finset (Coarsening T V) := by
  classical
  exact (allSetoids (X := T)).product (allSetoids (X := V))
/-- 全分割対一覧は安全性を仮定せず任意のRを含む。 -/
theorem mem_allCoarsenings (R : Coarsening T V) : R ∈ allCoarsenings := by
  classical
  exact Finset.mem_product.mpr ⟨mem_allSetoids R.1,mem_allSetoids R.2⟩
namespace PrimitiveInput
variable (M : PrimitiveInput S T V)
/-- 同じ原始比較の全A有理判定を通る全安全元。 -/
def safeCoarsenings : Finset (Coarsening T V) := by
  classical
  exact allCoarsenings.filter (fun R => allAPreservationDecision (M.quotientComparison R) = true)
/-- 安全一覧の正しさと完全性。 -/
theorem mem_safeCoarsenings (R : Coarsening T V) : R ∈ M.safeCoarsenings ↔ M.Safe R := by
  classical
  simp only [safeCoarsenings,Finset.mem_filter,mem_allCoarsenings,true_and]
  exact (M.safe_iff_decision R).symm
/-- 全安全元のうち、同じ一覧中に真に粗い安全元を持たないものを尽くす。 -/
def maximalCoarsenings : Finset (Coarsening T V) := by
  classical
  exact M.safeCoarsenings.filter (fun R => ∀ W ∈ M.safeCoarsenings, R ≤ W → W ≤ R)
/-- 極大一覧は元の全安全posetの極大性と必要十分。 -/
theorem mem_maximalCoarsenings (R : Coarsening T V) :
    R ∈ M.maximalCoarsenings ↔ Maximal M.Safe R := by
  classical
  simp only [maximalCoarsenings,Finset.mem_filter,M.mem_safeCoarsenings]
  rfl
omit [Fintype S] in
/-- 各安全元の上に全一覧中の極大安全元が存在。上方閉性を仮定しない。 -/
theorem exists_maximal_above (R : Coarsening T V) (hR : M.Safe R) :
    ∃ W, R ≤ W ∧ Maximal M.Safe W := by
  exact exists_maximal_ge_of_wellFoundedGT M.Safe R hR

omit [Fintype S] in
/-- 有限安全posetの最大元存在は、全極大元がただ一つであることと必要十分。 -/
theorem greatest_iff_unique_maximal :
    (∃ R, IsGreatest {W | M.Safe W} R) ↔ ∃! R, Maximal M.Safe R := by
  constructor
  · rintro ⟨R,hR⟩
    refine ⟨R,⟨hR.1,fun W hW _ => hR.2 hW⟩,?_⟩
    intro W hW
    exact le_antisymm (hR.2 hW.1) (hW.2 hR.1 (hR.2 hW.1))
  · rintro ⟨R,hR,huniq⟩
    refine ⟨R,hR.1,?_⟩
    intro W hW
    obtain ⟨Z,hWZ,hZ⟩ := M.exists_maximal_above W hW
    exact (huniq Z hZ) ▸ hWZ

omit [Fintype S] in
/-- 最大元存在は全安全対の安全な共通上界存在と必要十分。 -/
theorem greatest_iff_safe_upper_bounds (hex : ∃ R, M.Safe R) :
    (∃ R, IsGreatest {W | M.Safe W} R) ↔
      ∀ R S, M.Safe R → M.Safe S → ∃ W, M.Safe W ∧ R ≤ W ∧ S ≤ W := by
  constructor
  · rintro ⟨W,hW⟩ R S hR hS
    exact ⟨W,hW.1,hW.2 hR,hW.2 hS⟩
  · intro hub
    obtain ⟨R,hR⟩ := exists_maximal_of_wellFoundedGT M.Safe hex
    refine ⟨R,hR.1,?_⟩
    intro S hS
    obtain ⟨W,hW,hRW,hSW⟩ := hub R S hR.1 hS
    exact hSW.trans (hR.2 hW hRW)

omit [Fintype S] in
/-- 最大元不存在では全共通上界を排除する安全対が得られる。 -/
theorem no_greatest_witness (hex : ∃ R, M.Safe R)
    (hn : ¬ ∃ R, IsGreatest {W | M.Safe W} R) :
    ∃ R S, M.Safe R ∧ M.Safe S ∧ ∀ W, R ≤ W → S ≤ W → ¬ M.Safe W := by
  classical
  have hnub := (M.greatest_iff_safe_upper_bounds hex).not.mp hn
  push_neg at hnub
  obtain ⟨R,S,hR,hS,hno⟩ := hnub
  refine ⟨R,S,hR,hS,?_⟩
  intro W hRW hSW hW
  exact hno W hW hRW hSW

omit [Fintype S] in
/-- 有限非空安全posetのjoin閉性から最大元存在を導く。 -/
theorem greatest_of_join_closed (hex : ∃ R, M.Safe R)
    (hj : ∀ R S, M.Safe R → M.Safe S → M.Safe (R ⊔ S)) :
    ∃ R, IsGreatest {W | M.Safe W} R := by
  apply (M.greatest_iff_safe_upper_bounds hex).mpr
  intro R S hR hS
  exact ⟨R ⊔ S,hj R S hR hS,le_sup_left,le_sup_right⟩


/-- 恒等分割が実際に含まれるため全安全一覧は非空。 -/
theorem safeCoarsenings_nonempty : M.safeCoarsenings.Nonempty :=
  ⟨⊥,(M.mem_safeCoarsenings ⊥).mpr M.safe_bot⟩
/-- 恒等分割上の極大存在から全極大一覧も非空。 -/
theorem maximalCoarsenings_nonempty : M.maximalCoarsenings.Nonempty := by
  obtain ⟨R,_,hR⟩ := M.exists_maximal_above ⊥ M.safe_bot
  exact ⟨R,(M.mem_maximalCoarsenings R).mpr hR⟩
/-- 入力生成一覧の極大元数が1であることと最大元存在は必要十分。 -/
theorem greatest_iff_card_one : (∃ R, IsGreatest {W | M.Safe W} R) ↔
    M.maximalCoarsenings.card = 1 := by
  classical
  rw [M.greatest_iff_unique_maximal,Finset.card_eq_one]
  simp only [Finset.eq_singleton_iff_unique_mem,M.mem_maximalCoarsenings,ExistsUnique]

end PrimitiveInput
end AAT.AG.SafeCoarseningOrder
#assert_standard_axioms_only AAT.AG.SafeCoarseningOrder
