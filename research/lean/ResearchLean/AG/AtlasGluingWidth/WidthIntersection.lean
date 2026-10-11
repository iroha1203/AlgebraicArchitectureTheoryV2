import ResearchLean.AG.AtlasGluingWidth.WidthLaw
import ResearchLean.AG.AtlasDefectComposition.EndpointNaturality
import Formal.Util.AssertStandardAxioms

/-! # 同じ指定閉路の真のセル交差

A={0}, B=補集合を同じminus入力へ適用する。n≥2で交差chartは順序付き
w₋₁,w₀の二点となり、辺は空。領域集合の交差が選ぶ空nerveと区別する。

## Implementation notes

真交差の元chartを順序付きBoolに移して二点H⁰を評価する。
領域集合の交差を使う代替は空nerveとなり、指定の交差chartと貼り合わせ類を失うため採らない。
-/
noncomputable section
namespace AAT.AG.AtlasGluingWidth.Width
open CanonicalResolution ResolutionInvariance AtlasDefectComposition TwoPhase
variable (n : ℕ) [NeZero n]

/-- 指定Aは概念0のsingleton。 -/
def regionA : Set (Concept n) := {0}
/-- 指定Bは同じ概念集合での補集合。 -/
def regionB : Set (Concept n) := (regionA n)ᶜ
/-- 同じminus入力の真の細セル交差。 -/
def intersection := (selected n false (regionA n)).inter (selected n false (regionB n))
omit [NeZero n] in
/-- n≥2で1と0は異なる。 -/
theorem one_ne_zero (hn : 2 ≤ n) : (1 : Concept n) ≠ 0 := by
  intro h
  have hv := congrArg ZMod.val h
  rw [ZMod.val_one'' (by omega), ZMod.val_zero] at hv
  omega
omit [NeZero n] in
/-- n≥2でw₋₁とw₀は異なる。 -/
theorem neg_one_ne_zero (hn : 2 ≤ n) : (-1 : Concept n) ≠ 0 := by
  intro h
  have := congrArg Neg.neg h
  simp only [neg_neg, neg_zero] at this
  exact one_ne_zero n hn this
/-- 真の細交差のchart選択は二点を正確に指定する。 -/
theorem intersection_chart (hn : 2 ≤ n) (v : Chart n) :
    (intersection n).chart v ↔ v.2 = true ∧ (v.1 = -1 ∨ v.1 = 0) := by
  change ((selected n false (regionA n)).chart v ∧
    (selected n false (regionB n)).chart v) ↔ _
  rw [chart_selected, chart_selected]
  rcases v with ⟨i, b⟩
  have hi : i + 1 = 0 ↔ i = -1 := add_eq_zero_iff_eq_neg
  have hdistinct : ¬ (i = 0 ∧ i = -1) := by
    rintro ⟨rfl, h⟩
    exact neg_one_ne_zero n hn h.symm
  cases b <;> simp [regionA, regionB, hi]
  tauto
/-- 元辺のsingleton台はAとBの両方に交われない。 -/
theorem intersection_edges_empty : IsEmpty (intersection n).Edge := by
  refine ⟨fun e => ?_⟩
  have ha := (edge_selected n false (regionA n) e.1).mp e.2.1
  have hb := (edge_selected n false (regionB n) e.1).mp e.2.2
  exact hb ha
/-- 細交差には元面もない。 -/
instance intersection_faces_empty : IsEmpty (intersection n).Face :=
  ⟨fun f => f.1.elim⟩
/-- 指定交差の二点を同じ元chartから生成する。 -/
def intersectionPoint (hn : 2 ≤ n) (b : Bool) : (intersection n).Chart :=
  ⟨(if b then 0 else -1, true), (intersection_chart n hn _).mpr ⟨rfl, by cases b <;> simp⟩⟩
/-- 指定順序false=w₋₁,true=w₀で真の交差chartを同定する。 -/
def intersectionChartEquiv (hn : 2 ≤ n) : (intersection n).Chart ≃ Bool where
  toFun v := if v.1.1 = 0 then true else false
  invFun := intersectionPoint n hn
  left_inv v := by
    apply Subtype.ext
    have hv := (intersection_chart n hn v.1).mp v.2
    rcases v with ⟨⟨i, b⟩, hp⟩
    dsimp at hv ⊢
    rcases hv with ⟨rfl, hi | hi⟩
    · subst i
      simp [intersectionPoint, neg_one_ne_zero n hn]
    · subst i
      simp [intersectionPoint]
  right_inv b := by cases b <;> simp [intersectionPoint, neg_one_ne_zero n hn]
/-- 真の細セル交差の元chartは正確に二つ。 -/
theorem intersection_card (hn : 2 ≤ n) : Nat.card (intersection n).Chart = 2 := by
  rw [Nat.card_congr (intersectionChartEquiv n hn), Nat.card_eq_fintype_card]
  rfl
/-- 交差H¹は元の空辺から零。 -/
theorem intersection_H1_zero : Subsingleton (intersection n).complex.H1 := by
  letI := intersection_edges_empty n
  exact AtlasCoefficientFiber.h1_subsingleton_of_d0_surjective _ (fun z =>
    ⟨0, by funext e; exact isEmptyElim e⟩)
omit [NeZero n] in
/-- 同じ領域集合の交差は空。 -/
theorem region_inter_empty : regionA n ∩ regionB n = ∅ := by
  exact Set.inter_compl_self _
/-- A∩Bを選ぶ通常細nerveは空chart。 -/
theorem region_inter_charts_empty : IsEmpty (selected n false (regionA n ∩ regionB n)).Chart := by
  refine ⟨fun v => ?_⟩
  have hv := (chart_selected n false (regionA n ∩ regionB n) v.1).mp v.2
  rcases hv with ha | ⟨_, ha⟩
  · exact ha.2 ha.1
  · exact ha.2 ha.1
/-- 指定真交差のH⁰核は同じ順序の二点関数に両方向同定。 -/
def intersectionH0Equiv (hn : 2 ≤ n) :
    LinearMap.ker (intersection n).complex.d0 ≃ₗ[ℚ] (Bool → ℚ) where
  toFun z b := z.1 (intersectionPoint n hn b)
  invFun z := ⟨fun v => z (intersectionChartEquiv n hn v), by
    letI := intersection_edges_empty n
    funext e
    exact isEmptyElim e⟩
  left_inv z := by
    apply Subtype.ext
    funext v
    exact congrArg z.1 ((intersectionChartEquiv n hn).symm_apply_apply v)
  right_inv z := by
    funext b
    exact congrArg z ((intersectionChartEquiv n hn).apply_symm_apply b)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- 空領域を選ぶ同じ細複体は全三次数で零。 -/
theorem empty_degrees_zero (cut : Bool) :
    Subsingleton (selected n cut ∅).complex.C0 ∧
    Subsingleton (selected n cut ∅).complex.C1 ∧
    Subsingleton (selected n cut ∅).complex.C2 := by
  letI : IsEmpty (selected n cut ∅).Chart := ⟨fun v => by
    have hv := (chart_selected n cut ∅ v.1).mp v.2
    simp at hv⟩
  letI : IsEmpty (selected n cut ∅).Edge := ⟨fun e => by
    have he := (edge_selected n cut ∅ e.1).mp e.2
    exact he⟩
  letI : IsEmpty (selected n cut ∅).Face := ⟨fun f => f.1.elim⟩
  refine ⟨?_, ?_, ?_⟩
  · change Subsingleton ((selected n cut ∅).Chart → ℚ)
    infer_instance
  · change Subsingleton ((selected n cut ∅).Edge → ℚ)
    infer_instance
  · change Subsingleton ((selected n cut ∅).Face → ℚ)
    infer_instance

end AAT.AG.AtlasGluingWidth.Width
#assert_standard_axioms_only AAT.AG.AtlasGluingWidth.Width
