import ResearchLean.AG.AtlasDefectComposition.WitnessOneComparison
import ResearchLean.AG.AtlasDefectComposition.GeneratedDefect
import Formal.Util.AssertStandardAxioms

/-! # W1の同じ実比較での非零相殺

各ラベルの実H¹次元・二射の欠損・直接比較の零欠損と辺34の相殺証人を同時に示す。
-/
noncomputable section
namespace AAT.AG.AtlasDefectComposition.WitnessOne
open CanonicalResolution ResolutionInvariance TwoPhase

/-- W1の既存生成APIによる前段の実H¹写像。 -/
abbrev forward (l : LawValueLabel laws) := M₀₁.generatedBlockComparisonH1Map laws adequate₀ adequate₁ l
/-- W1の既存生成APIによる後段の実H¹写像。 -/
abbrev backward (l : LawValueLabel laws) := M₁₂.generatedBlockComparisonH1Map laws adequate₁ adequate₂ l
/-- W1の既存生成APIによる直接の実H¹写像。 -/
abbrev direct (l : LawValueLabel laws) := M₀₂.generatedBlockComparisonH1Map laws adequate₀ adequate₂ l

/-- 実periodの包含作用から前段の単射性を得る。 -/
theorem forward_injective (l : LawValueLabel laws) : Function.Injective (forward l) := by
  intro x y h
  apply (h1Period₀ l).injective
  have hp := congrArg (fun v => (h1Periods₁ l v).1) h
  simpa only [forward, forward_period] using hp

/-- 実periodの射影作用から後段の全射性を得る。 -/
theorem backward_surjective (l : LawValueLabel laws) : Function.Surjective (backward l) := by
  intro y
  refine ⟨(h1Periods₁ l).symm (h1Period₂ l y, 0), ?_⟩
  apply (h1Period₂ l).injective
  rw [backward, backward_period, LinearEquiv.apply_symm_apply]

/-- 直接実比較はperiodを保持する同型である。 -/
theorem direct_bijective (l : LawValueLabel laws) : Function.Bijective (direct l) := by
  constructor
  · intro x y h
    apply (h1Period₀ l).injective
    simpa only [direct, direct_block_period] using congrArg (h1Period₂ l) h
  · intro y
    refine ⟨(h1Period₀ l).symm (h1Period₂ l y), ?_⟩
    apply (h1Period₂ l).injective
    rw [direct, direct_block_period, LinearEquiv.apply_symm_apply]

/-- 同じ実H¹二射の合成と直接比較の一致。 -/
theorem direct_eq_comp (l : LawValueLabel laws) : direct l = (backward l).comp (forward l) := by
  apply LinearMap.ext
  intro x
  apply (h1Period₂ l).injective
  rw [LinearMap.comp_apply, backward, backward_period, forward, forward_period, direct, direct_block_period]

/-- 前段の実欠損は(0,1)。 -/
theorem forward_defect (l : LawValueLabel laws) : blockDefect (forward l) = (0, 1) := by
  have hdim := (LinearEquiv.ofInjective (forward l) (forward_injective l)).finrank_eq
  rw [h1_dimension₀ l] at hdim
  rw [blockDefect_eq_finrank_sub_range, h1_dimension₀ l, h1_dimension₁ l, ← hdim]

/-- 後段の実欠損は(1,0)。 -/
theorem backward_defect (l : LawValueLabel laws) : blockDefect (backward l) = (1, 0) := by
  have hdim := (LinearEquiv.ofTop (LinearMap.range (backward l))
    (LinearMap.range_eq_top.mpr (backward_surjective l))).finrank_eq
  rw [h1_dimension₂ l] at hdim
  rw [blockDefect_eq_finrank_sub_range, h1_dimension₁ l, h1_dimension₂ l, hdim]

/-- 直接比較の実欠損は(0,0)。 -/
theorem direct_defect (l : LawValueLabel laws) : blockDefect (direct l) = (0, 0) :=
  (blockDefect_eq_zero_iff_bijective _).mpr (direct_bijective l)

/-- 指定された辺34だけが1の、中間実cocycle。 -/
def middleCycle (l : LawValueLabel laws) :
    LinearMap.ker (N₁.lawValueBlockComplex laws adequate₁ l).d1 :=
  ⟨(fullBlockCochainEquiv laws q₁ adequate₁ N₁.edgeSupport edgeSupport_univ₁ l).symm
    ![0, 0, 0, 0, 0, 1], by
    change N₁.lawValueBlockD1 laws adequate₁ l _ = 0
    funext f; exact f.val.cell.elim⟩

/-- 指定中間cocycleの既存H¹商類。 -/
def middleClass (l : LawValueLabel laws) : (N₁.lawValueBlockComplex laws adequate₁ l).H1 :=
  (LinearMap.range (N₁.lawValueBlockComplex laws adequate₁ l).boundaryToCycles).mkQ (middleCycle l)

/-- 指定中間類の二periodは(0,1)。 -/
theorem middle_periods (l : LawValueLabel laws) : h1Periods₁ l (middleClass l) = (0, 1) := by
  rw [middleClass, h1Periods₁_mk]
  change twoTrianglePeriods ((fullBlockCochainEquiv laws q₁ adequate₁ N₁.edgeSupport edgeSupport_univ₁ l)
    ((fullBlockCochainEquiv laws q₁ adequate₁ N₁.edgeSupport edgeSupport_univ₁ l).symm _)) = _
  rw [LinearEquiv.apply_symm_apply]
  simp [twoTrianglePeriods]

/-- 指定中間類は後段の実比較で消える。 -/
theorem middle_killed (l : LawValueLabel laws) : backward l (middleClass l) = 0 := by
  apply (h1Period₂ l).injective
  rw [backward, backward_period, middle_periods, map_zero]

/-- 指定された実相殺写像の入力。 -/
def middleKernel (l : LawValueLabel laws) : LinearMap.ker (backward l) :=
  ⟨middleClass l, middle_killed l⟩

/-- 指定中間類自体も非零である。 -/
theorem middle_nonzero (l : LawValueLabel laws) : middleClass l ≠ 0 := by
  intro h
  have hp := congrArg (fun v => (h1Periods₁ l v).2) h
  dsimp only at hp
  rw [middle_periods, map_zero] at hp
  norm_num at hp

/-- 指定中間類は前段の実像に入らず、実相殺の像で非零となる。 -/
theorem cancellation_nonzero (l : LawValueLabel laws) :
    DefectSequence.cancellation (forward l) (backward l) (middleKernel l) ≠ 0 := by
  intro hc
  change Submodule.Quotient.mk (middleClass l) = 0 at hc
  have hm := (Submodule.Quotient.mk_eq_zero _).mp hc
  obtain ⟨x, hx⟩ := hm
  have hp := congrArg (fun v => (h1Periods₁ l v).2) hx
  dsimp only at hp
  rw [forward, forward_period, middle_periods] at hp
  norm_num at hp

/-- 同じ実比較の六項完全列により、各ラベルの相殺rankは1。 -/
theorem cancellation_rank (l : LawValueLabel laws) :
    Module.finrank ℚ (LinearMap.range (DefectSequence.cancellation (forward l) (backward l))) = 1 := by
  have hr := DefectSequence.kernel_dimension (forward l) (backward l)
  have hf := congrArg Prod.fst (forward_defect l)
  have hg := congrArg Prod.fst (backward_defect l)
  have hh := congrArg Prod.fst (direct_defect l)
  rw [direct_eq_comp l] at hh
  change Module.finrank ℚ (LinearMap.ker (forward l)) = 0 at hf
  change Module.finrank ℚ (LinearMap.ker (backward l)) = 1 at hg
  change Module.finrank ℚ (LinearMap.ker ((backward l).comp (forward l))) = 0 at hh
  omega

/-- 前段実像をperiodで移すと、第一成分の像になる。 -/
theorem forward_range_period (l : LawValueLabel laws) :
    (LinearMap.range (forward l)).map (h1Periods₁ l).toLinearMap =
      LinearMap.range (LinearMap.inl ℚ ℚ ℚ) := by
  ext p
  constructor
  · rintro ⟨x, ⟨y, rfl⟩, rfl⟩
    exact ⟨h1Period₀ l y, (forward_period l y).symm⟩
  · rintro ⟨a, rfl⟩
    refine ⟨forward l ((h1Period₀ l).symm a), ⟨(h1Period₀ l).symm a, rfl⟩, ?_⟩
    change h1Periods₁ l (forward l ((h1Period₀ l).symm a)) = (a, 0)
    rw [forward, forward_period, LinearEquiv.apply_symm_apply]

/-- 前段の実余核をℚ²/(ℚ×0)へ同定する。 -/
def forwardCokernelEquiv (l : LawValueLabel laws) :
    ((N₁.lawValueBlockComplex laws adequate₁ l).H1 ⧸ LinearMap.range (forward l)) ≃ₗ[ℚ]
      ((ℚ × ℚ) ⧸ LinearMap.range (LinearMap.inl ℚ ℚ ℚ)) :=
  Submodule.Quotient.equiv _ _ (h1Periods₁ l) (forward_range_period l)

/-- 実相殺射は、この商同定で中間実periodの商類を読む。 -/
@[simp] theorem cancellation_period_quotient (l : LawValueLabel laws)
    (y : LinearMap.ker (backward l)) :
    forwardCokernelEquiv l (DefectSequence.cancellation (forward l) (backward l) y) =
      (LinearMap.range (LinearMap.inl ℚ ℚ ℚ)).mkQ (h1Periods₁ l y.val) := rfl

/-- 指定辺34の相殺像はℚ²/(ℚ×0)の(0,1)類に一致する。 -/
theorem middle_cancellation_period (l : LawValueLabel laws) :
    forwardCokernelEquiv l
      (DefectSequence.cancellation (forward l) (backward l) (middleKernel l)) =
      (LinearMap.range (LinearMap.inl ℚ ℚ ℚ)).mkQ (0, 1) := by
  rw [cancellation_period_quotient]
  exact congrArg (LinearMap.range (LinearMap.inl ℚ ℚ ℚ)).mkQ (middle_periods l)

end AAT.AG.AtlasDefectComposition.WitnessOne
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition.WitnessOne
