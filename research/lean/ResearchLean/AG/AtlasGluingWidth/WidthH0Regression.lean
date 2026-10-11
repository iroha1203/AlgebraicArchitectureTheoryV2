import ResearchLean.AG.AtlasGluingWidth.WidthCoefficient

/-! # 低幅H¹観測をH⁰へ強められない原始回帰例

GOAL E / witnesses §5。同じAのplus入力ではa₀だけがなく、w₀が孤立する。
実零微分核の二値評価からH⁰を計算する。n=2を含む一般n≥2の構成。

## Implementation notes

同じ元chartと唯一選択b₋₁の端点を使い、定数値と孤立点値を両方向に構成する。
H¹の同型からH⁰も同型とする代替はこの原始入力で反証される。
-/
noncomputable section
namespace AAT.AG.AtlasGluingWidth.Width
open CanonicalResolution ResolutionInvariance TwoPhase AtlasDefectComposition
variable (n : ℕ) [NeZero n]

/-- 同じplus Aの実chart v₀。 -/
def plusARoot : (selected n true (regionA n)).Chart :=
  ⟨(0,false), (chart_selected n true (regionA n) _).mpr (Or.inl rfl)⟩
/-- 同じplus Aの孤立実chart w₀。 -/
def plusAIsolated : (selected n true (regionA n)).Chart :=
  ⟨(0,true), (chart_selected n true (regionA n) _).mpr (Or.inl rfl)⟩
/-- 同じplus Aの選択b₋₁。 -/
def plusABackEdge : (selected n true (regionA n)).Edge :=
  ⟨⟨(-1,true), by intro _ h; exact Bool.noConfusion (congrArg Prod.snd h)⟩,
    (edge_selected n true (regionA n) _).mpr (by simp [regionA])⟩
/-- plus Aの零微分核はw₋₁とv₀で同じ値を持つ。 -/
theorem plus_a_back_value (z : LinearMap.ker (selected n true (regionA n)).complex.d0) :
    z.1 ((selected n true (regionA n)).left (plusABackEdge n)) = z.1 (plusARoot n) := by
  have h := congrFun z.2 (plusABackEdge n)
  rw [CellSelection.complex_d0_apply] at h
  have h' := (sub_eq_zero.mp h).symm
  simpa [CellSelection.right, plusABackEdge, plusARoot, right] using h'
/-- 指定plus Aの実H⁰核は非孤立成分値と孤立w₀値で二成分に同定する。 -/
def plusAH0Equiv (hn : 2 ≤ n) : LinearMap.ker (selected n true (regionA n)).complex.d0 ≃ₗ[ℚ] (ℚ × ℚ) where
  toFun z := (z.1 (plusARoot n), z.1 (plusAIsolated n))
  invFun z := ⟨fun v => if v.1 = (0,true) then z.2 else z.1, by
    funext e
    have he := (edge_selected n true (regionA n) e.1).mp e.2
    rcases e with ⟨⟨⟨i,b⟩,hcut⟩,hp⟩
    cases b
    · have hi : i = 0 := he
      subst i
      exact False.elim (hcut rfl rfl)
    · have hi : i = -1 := add_eq_zero_iff_eq_neg.mp he
      subst i
      change (if (((-1 : Concept n)+1),false) = (0,true) then z.2 else z.1) -
        (if ((-1 : Concept n),true) = (0,true) then z.2 else z.1) = 0
      simp [neg_one_ne_zero n hn]⟩
  left_inv z := by
    apply Subtype.ext
    funext v
    have hv := (chart_selected n true (regionA n) v.1).mp v.2
    rcases v with ⟨⟨i,b⟩,hp⟩
    cases b
    · have hi : i = 0 := by simpa [regionA] using hv
      subst i
      simp [plusARoot]
    · rcases hv with hi | ⟨_,hi⟩
      · have hi' : i = 0 := hi
        subst i
        simp [plusAIsolated]
      · have hi' : i = -1 := add_eq_zero_iff_eq_neg.mp hi
        subst i
        have hb := plus_a_back_value n z
        simpa [plusABackEdge, CellSelection.left, left, neg_one_ne_zero n hn] using hb.symm
  right_inv z := by simp [plusARoot, plusAIsolated]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
/-- 同じ原始Aのminus/plusではH¹は両方零だがH⁰次元は1と2。 -/
theorem h0_width_regression (hn : 2 ≤ n) :
    Module.finrank ℚ (LinearMap.ker (selected n false (regionA n)).complex.d0) = 1 ∧
    Module.finrank ℚ (LinearMap.ker (selected n true (regionA n)).complex.d0) = 2 ∧
    Subsingleton (selected n false (regionA n)).complex.H1 ∧
    Subsingleton (selected n true (regionA n)).complex.H1 := by
  refine ⟨?_, ?_, proper_H1_zero n false (regionA n) (regionA_proper n hn), plus_H1_zero n (regionA n)⟩
  · rw [(aH0Equiv n).finrank_eq]
    simp
  · rw [(plusAH0Equiv n hn).finrank_eq]
    simp [Module.finrank_prod]
/-- 設計§5の指定n=2回帰例を同じ入力から得る。 -/
theorem h0_width_regression_two :
    Module.finrank ℚ (LinearMap.ker (selected 2 false (regionA 2)).complex.d0) = 1 ∧
    Module.finrank ℚ (LinearMap.ker (selected 2 true (regionA 2)).complex.d0) = 2 ∧
    Subsingleton (selected 2 false (regionA 2)).complex.H1 ∧
    Subsingleton (selected 2 true (regionA 2)).complex.H1 := h0_width_regression 2 (by omega)

end AAT.AG.AtlasGluingWidth.Width
#assert_standard_axioms_only AAT.AG.AtlasGluingWidth.Width
