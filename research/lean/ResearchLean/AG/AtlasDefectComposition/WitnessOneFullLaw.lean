import ResearchLean.AG.AtlasDefectComposition.WitnessOneCancellation
import ResearchLean.AG.AtlasDefectComposition.LawH1Family
import Formal.Util.AssertStandardAxioms

/-! # W1の全Lawでの相殺

二つの実発生ラベルを既存直和から関数表示へ移し、同じ生成比較を成分ごとに読む。
-/
noncomputable section
namespace AAT.AG.AtlasDefectComposition.WitnessOne
open CanonicalResolution ResolutionInvariance TwoPhase

/-- W1の実発生ラベルはBoolと全単射で対応する。 -/
def labelEquivBool : LawValueLabel laws ≃ Bool where
  toFun l := l.value
  invFun := label
  left_inv l := by obtain ⟨a, rfl⟩ := labels_exhaust l; rfl
  right_inv _ := rfl

/-- 実発生ラベルの数は2であり、同台であっても二成分を保持する。 -/
theorem label_card : Fintype.card (LawValueLabel laws) = 2 := by
  rw [Fintype.card_congr labelEquivBool]; rfl

/-- 全Lawの粗H¹を二ラベルの実period族へ移す。 -/
def fullPeriod₀ : (N₀.lawGeneratedComplex laws adequate₀).H1 ≃ₗ[ℚ] (LawValueLabel laws → ℚ) :=
  (lawH1FamilyEquiv N₀ laws adequate₀).trans (LinearEquiv.piCongrRight h1Period₀)

/-- 全Lawの中間H¹を二ラベルの実二period族へ移す。 -/
def fullPeriods₁ : (N₁.lawGeneratedComplex laws adequate₁).H1 ≃ₗ[ℚ] (LawValueLabel laws → ℚ × ℚ) :=
  (lawH1FamilyEquiv N₁ laws adequate₁).trans (LinearEquiv.piCongrRight h1Periods₁)

/-- 全Lawの細H¹を二ラベルの実period族へ移す。 -/
def fullPeriod₂ : (N₂.lawGeneratedComplex laws adequate₂).H1 ≃ₗ[ℚ] (LawValueLabel laws → ℚ) :=
  (lawH1FamilyEquiv N₂ laws adequate₂).trans (LinearEquiv.piCongrRight h1Period₂)

/-- 全Lawの実前段比較。 -/
abbrev fullForward := M₀₁.generatedComparisonH1Map laws adequate₀ adequate₁
/-- 全Lawの実後段比較。 -/
abbrev fullBackward := M₁₂.generatedComparisonH1Map laws adequate₁ adequate₂
/-- 全Lawの実直接比較。 -/
abbrev fullDirect := M₀₂.generatedComparisonH1Map laws adequate₀ adequate₂

/-- 全Lawの前段生成比較は各実ラベルでperiodを包含する。 -/
theorem full_forward_periods (x : (N₀.lawGeneratedComplex laws adequate₀).H1) (l : LawValueLabel laws) :
    fullPeriods₁ (fullForward x) l = (fullPeriod₀ x l, 0) := by
  change h1Periods₁ l (lawH1FamilyEquiv N₁ laws adequate₁ (fullForward x) l) =
    (h1Period₀ l (lawH1FamilyEquiv N₀ laws adequate₀ x l), 0)
  rw [fullForward, lawH1FamilyMap_component]
  exact forward_period l _

/-- 全Lawの後段生成比較は各実ラベルで第一periodを射影する。 -/
theorem full_backward_periods (x : (N₁.lawGeneratedComplex laws adequate₁).H1) (l : LawValueLabel laws) :
    fullPeriod₂ (fullBackward x) l = (fullPeriods₁ x l).1 := by
  change h1Period₂ l (lawH1FamilyEquiv N₂ laws adequate₂ (fullBackward x) l) =
    (h1Periods₁ l (lawH1FamilyEquiv N₁ laws adequate₁ x l)).1
  rw [fullBackward, lawH1FamilyMap_component]
  exact backward_period l _

/-- 全Lawの直接生成比較は各実ラベルのperiodを保持する。 -/
theorem full_direct_period (x : (N₀.lawGeneratedComplex laws adequate₀).H1) (l : LawValueLabel laws) :
    fullPeriod₂ (fullDirect x) l = fullPeriod₀ x l := by
  change h1Period₂ l (lawH1FamilyEquiv N₂ laws adequate₂ (fullDirect x) l) =
    h1Period₀ l (lawH1FamilyEquiv N₀ laws adequate₀ x l)
  rw [fullDirect, lawH1FamilyMap_component]
  exact direct_block_period l _

/-- 全Lawの粗実H¹次元は2。 -/
theorem full_h1_dimension₀ : Module.finrank ℚ (N₀.lawGeneratedComplex laws adequate₀).H1 = 2 := by
  rw [fullPeriod₀.finrank_eq, Module.finrank_pi, label_card]

/-- 全Lawの中間実H¹次元は4。 -/
theorem full_h1_dimension₁ : Module.finrank ℚ (N₁.lawGeneratedComplex laws adequate₁).H1 = 4 := by
  rw [fullPeriods₁.finrank_eq, Module.finrank_pi_fintype]
  simp [Module.finrank_prod, label_card]

/-- 全Lawの細実H¹次元は2。 -/
theorem full_h1_dimension₂ : Module.finrank ℚ (N₂.lawGeneratedComplex laws adequate₂).H1 = 2 := by
  rw [fullPeriod₂.finrank_eq, Module.finrank_pi, label_card]

/-- 全Lawの前段実H¹比較は単射。 -/
theorem full_forward_injective : Function.Injective fullForward := by
  intro x y h
  apply fullPeriod₀.injective
  funext l
  have hp := congrArg (fun v => (fullPeriods₁ v l).1) h
  simpa only [full_forward_periods] using hp

/-- 全Lawの後段実H¹比較は全射。 -/
theorem full_backward_surjective : Function.Surjective fullBackward := by
  intro y
  let p : LawValueLabel laws → ℚ × ℚ := fun l => (fullPeriod₂ y l, 0)
  refine ⟨fullPeriods₁.symm p, ?_⟩
  apply fullPeriod₂.injective
  funext l
  rw [full_backward_periods]
  exact congrArg Prod.fst (congrFun (fullPeriods₁.apply_symm_apply p) l)

/-- 全Lawの直接比較は同型。 -/
theorem full_direct_bijective : Function.Bijective fullDirect := by
  constructor
  · intro x y h
    apply fullPeriod₀.injective
    funext l
    have hp := congrArg (fun v => fullPeriod₂ v l) h
    simpa only [full_direct_period] using hp
  · intro y
    refine ⟨fullPeriod₀.symm (fullPeriod₂ y), ?_⟩
    apply fullPeriod₂.injective
    funext l
    rw [full_direct_period]
    exact congrFun (fullPeriod₀.apply_symm_apply (fullPeriod₂ y)) l

/-- 全Lawの前段欠損は(0,2)。 -/
theorem full_forward_defect : blockDefect fullForward = (0, 2) := by
  have hdim := (LinearEquiv.ofInjective fullForward full_forward_injective).finrank_eq
  rw [full_h1_dimension₀] at hdim
  rw [blockDefect_eq_finrank_sub_range, full_h1_dimension₀, full_h1_dimension₁, ← hdim]

/-- 全Lawの後段欠損は(2,0)。 -/
theorem full_backward_defect : blockDefect fullBackward = (2, 0) := by
  have hdim := (LinearEquiv.ofTop (LinearMap.range fullBackward)
    (LinearMap.range_eq_top.mpr full_backward_surjective)).finrank_eq
  rw [full_h1_dimension₂] at hdim
  rw [blockDefect_eq_finrank_sub_range, full_h1_dimension₁, full_h1_dimension₂, hdim]

/-- 全Lawの直接欠損は(0,0)。 -/
theorem full_direct_defect : blockDefect fullDirect = (0, 0) :=
  (blockDefect_eq_zero_iff_bijective _).mpr full_direct_bijective

/-- 全Lawの実相殺rankは2。 -/
theorem full_cancellation_rank :
    Module.finrank ℚ (LinearMap.range (DefectSequence.cancellation fullForward fullBackward)) = 2 := by
  have hr := DefectSequence.kernel_dimension fullForward fullBackward
  have hf := congrArg Prod.fst full_forward_defect
  have hg := congrArg Prod.fst full_backward_defect
  have hh := congrArg Prod.fst full_direct_defect
  have heq : fullDirect = fullBackward.comp fullForward :=
    generatedComparisonH1Map_comp M₀₁ M₁₂ laws adequate₀ adequate₁ adequate₂
  rw [heq] at hh
  simp only [blockDefect_eq_finrank_sub_range] at hf hg hh
  have hf' := fullForward.finrank_range_add_finrank_ker
  have hg' := fullBackward.finrank_range_add_finrank_ker
  have hh' := (fullBackward.comp fullForward).finrank_range_add_finrank_ker
  omega

end AAT.AG.AtlasDefectComposition.WitnessOne
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition.WitnessOne
