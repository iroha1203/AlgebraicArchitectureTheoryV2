import ResearchLean.AG.AtlasGluingWidth.CellSelection

/-! # 元セル関数の和・交差短完全列

各次数に適用する同じ制限・差制限を評価式から構成する。
零延長は次数別の切断である。
-/
noncomputable section
namespace AAT.AG.AtlasGluingWidth.Cellwise
attribute [local instance] Classical.propDecidable
universe u
variable {Cell : Type u} (a b : Cell → Prop)

/-- 和の関数を二つの元セル選択に制限する。 -/
def inclusion : ({c // a c ∨ b c} → ℚ) →ₗ[ℚ]
    ({c // a c} → ℚ) × ({c // b c} → ℚ) where
  toFun x := (fun c => x ⟨c.1, Or.inl c.2⟩, fun c => x ⟨c.1, Or.inr c.2⟩)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- 同じ交差セルにおける第一成分−第二成分。 -/
def difference : (({c // a c} → ℚ) × ({c // b c} → ℚ)) →ₗ[ℚ]
    ({c // a c ∧ b c} → ℚ) where
  toFun x c := x.1 ⟨c.1, c.2.1⟩ - x.2 ⟨c.1, c.2.2⟩
  map_add' x y := by ext c; simp; ring
  map_smul' r x := by ext c; simp; ring

/-- 交差上の関数を第一領域へ零延長する次数別切断。 -/
def extendLeft (z : {c // a c ∧ b c} → ℚ) : {c // a c} → ℚ :=
  fun c => if hb : b c.1 then z ⟨c.1, c.2, hb⟩ else 0

/-- 一致する局所値を、第一領域優先の所属判定で貼り合わせる。 -/
def glue (x : ({c // a c} → ℚ) × ({c // b c} → ℚ)) :
    {c // a c ∨ b c} → ℚ := fun c =>
  if ha : a c.1 then x.1 ⟨c.1, ha⟩ else x.2 ⟨c.1, c.2.resolve_left ha⟩

@[simp] theorem inclusion_apply (x : {c // a c ∨ b c} → ℚ) :
    inclusion a b x =
      (fun c => x ⟨c.1, Or.inl c.2⟩, fun c => x ⟨c.1, Or.inr c.2⟩) := rfl

@[simp] theorem difference_apply (x : ({c // a c} → ℚ) × ({c // b c} → ℚ))
    (c : {c // a c ∧ b c}) :
    difference a b x c = x.1 ⟨c.1, c.2.1⟩ - x.2 ⟨c.1, c.2.2⟩ := rfl

/-- 元セルの二つの制限は和の関数を一意に定める。 -/
theorem inclusion_injective : Function.Injective (inclusion a b) := by
  intro x y h
  funext c
  rcases c.2 with ha | hb
  · exact congrFun (congrArg Prod.fst h) ⟨c.1, ha⟩
  · exact congrFun (congrArg Prod.snd h) ⟨c.1, hb⟩

/-- 次数別零延長の差制限は元の交差値。 -/
@[simp] theorem difference_extendLeft (z : {c // a c ∧ b c} → ℚ) :
    difference a b (extendLeft a b z, 0) = z := by
  funext c
  simp [difference, extendLeft, c.2.2]

/-- 差制限は全交差関数へ全射。 -/
theorem difference_surjective : Function.Surjective (difference a b) := by
  intro z
  exact ⟨(extendLeft a b z, 0), difference_extendLeft a b z⟩

/-- 核の条件は同じ元セルでの局所値の一致。 -/
theorem difference_eq_zero_iff (x : ({c // a c} → ℚ) × ({c // b c} → ℚ)) :
    difference a b x = 0 ↔
      ∀ (c : Cell) (ha : a c) (hb : b c), x.1 ⟨c, ha⟩ = x.2 ⟨c, hb⟩ := by
  constructor
  · intro h c ha hb
    exact sub_eq_zero.mp (congrFun h ⟨c, ha, hb⟩)
  · intro h
    ext c
    exact sub_eq_zero.mpr (h c.1 c.2.1 c.2.2)

/-- 一致する局所値は貼り合わせによって復元する。 -/
theorem inclusion_glue (x : ({c // a c} → ℚ) × ({c // b c} → ℚ))
    (h : difference a b x = 0) : inclusion a b (glue a b x) = x := by
  apply Prod.ext
  · funext c
    simp [inclusion, glue, c.2]
  · funext c
    change (if ha : a c.1 then x.1 ⟨c.1, ha⟩ else
      x.2 ⟨c.1, _⟩) = x.2 c
    split
    · rename_i ha
      exact (difference_eq_zero_iff a b x).1 h c.1 ha c.2
    · rfl

/-- 和・二領域・真のセル交差の完全性。 -/
theorem exact : Function.Exact (inclusion a b) (difference a b) := by
  intro x
  constructor
  · intro h
    exact ⟨glue a b x, inclusion_glue a b x h⟩
  · rintro ⟨z, rfl⟩
    ext c
    simp [inclusion, difference]

end AAT.AG.AtlasGluingWidth.Cellwise
#assert_standard_axioms_only AAT.AG.AtlasGluingWidth
