import ResearchLean.AG.SpecifiedRepairLifting.RationalWitnessCoordinates

/-! # 固定W1の指定半整数補正

Implementation notes: 実G-125比較の定義域と値域をそのまま用いる。
座標同型は微分と比較の計算にのみ使い、別複体へ証明対象を移さない。
-/
noncomputable section
open CategoryTheory
namespace AAT.AG.SpecifiedRepairLifting.RationalWitness
open RationalWitnessGeometry RationalWitnessContext RationalWitnessInput RationalWitnessCoordinates
open ObstructionDiagnosticBridge CanonicalResolution ResolutionInvariance Cohomology TwoPhase
open GeneratorPresentation GeneratorPresentation.ActualCechAffineLocalData
/-- 同じ元Čech複体。 -/
abbrev actualComplex := presentation.faceEmptyCechComplex cechCover
/-- 同じLaw生成diagnostic。 -/
abbrev diagnosticComplex := supportedNerve.lawGeneratedComplex laws adequate
/-- 同じ全次数の比較射。 -/
def comparison := actualComparison presentation cechCover adequate
/-- 生成元一個をedgeへ置き、局所状態を零にした実入力。 -/
def localData : ActualCechAffineLocalData presentation cechCover where
  transition := integralOneEquiv.symm 1
  localState := 0
/-- 原始実入力から生成されたmismatchは+1。 -/
theorem mismatch_coordinate : integralOneEquiv localData.actualMismatch = 1 := by
  change integralOneEquiv (integralOneEquiv.symm 1 + actualComplex.d 0 0) = 1
  rw [map_zero,add_zero,AddEquiv.apply_symm_apply]
/-- 固定された指定補正は(1/2,3/2)。 -/
def halfCorrection : diagnosticComplex.C0 := rationalZeroEquiv.symm (fun i => if i then 3/2 else 1/2)
/-- 指定補正の両座標。 -/
theorem halfCorrection_coordinates (i : Bool) :
    rationalZeroEquiv halfCorrection i = if i then 3/2 else 1/2 :=
  congrFun (rationalZeroEquiv.apply_symm_apply _) i
/-- 元の整数補正(0,1)。 -/
def baseCorrection : actualComplex.Cn 0 := integralZeroEquiv.symm (fun i => if i then 1 else 0)
/-- 元整数補正の両座標。 -/
theorem baseCorrection_coordinates (i : Bool) :
    integralZeroEquiv baseCorrection i = if i then 1 else 0 :=
  congrFun (integralZeroEquiv.apply_symm_apply _) i
/-- 指定有理補正は実mismatchと適合する。 -/
theorem half_compatible : (diagnosticNative diagnosticComplex).d 0 1 halfCorrection =
    comparison.f 1 localData.actualMismatch := by
  rw [diagnosticNative_d]
  apply rationalOneEquiv.injective
  change rationalOneEquiv (diagnosticComplex.d0 halfCorrection) =
    rationalOneEquiv (presentation.actualCechCoefficientCochain1 cechCover adequate localData.actualMismatch)
  rw [rational_d0,comparison_one,mismatch_coordinate,halfCorrection_coordinates,halfCorrection_coordinates]
  norm_num
/-- 元の整数補正は同じ実mismatchを消す。 -/
theorem base_boundary : (cechNative actualComplex).d 0 1 baseCorrection = localData.actualMismatch := by
  rw [cechNative_d]
  apply integralOneEquiv.injective
  rw [integral_d0,mismatch_coordinate,baseCorrection_coordinates,baseCorrection_coordinates]
  rfl
/-- 一般Aと同じ閉性。 -/
theorem mismatch_closed : (cechNative actualComplex).d 1 2 localData.actualMismatch = 0 :=
  actualMismatch_closed presentation cechCover localData
/-- 整数は1/2へ写らない。 -/
theorem integer_ne_half (n : ℤ) : (n : ℚ) ≠ 1/2 := by
  intro h
  have h2 : (2 : ℚ) * n = 1 := by linarith
  have hi : (2 : ℤ) * n = 1 := by exact_mod_cast h2
  omega
/-- 同じ実比較で指定半整数そのものを持ち上げることはできない。 -/
theorem no_half_lift : ¬ Nonempty (NonnegativeLift comparison localData.actualMismatch halfCorrection) := by
  rintro ⟨a⟩
  have h := congrArg (fun b => rationalZeroEquiv b false) a.property.2
  change rationalZeroEquiv (presentation.actualCechCoefficientCochain0 cechCover adequate a.val) false = _ at h
  dsimp only at h
  rw [comparison_zero,halfCorrection_coordinates] at h
  exact integer_ne_half _ h
/-- 元のfloor補正を同じ実入力上で評価する。 -/
theorem integral_floor_coordinate (b : diagnosticComplex.C0) (i : Bool) :
    integralZeroEquiv (integralCorrection (P := presentation) (C := cechCover)
      adequate common_support b) i = ⌊rationalZeroEquiv b i⌋ := by
  rw [integralZeroEquiv_apply,faceEmptyCechCochain0Equiv_integralCorrection,coefficientEquiv_apply]
  have h := congrArg (fun f : FreeAbelianGroup presentation.Block →+ FreeAbelianGroup presentation.Block => f
    ((FreeAbelianGroup.equivFinsupp presentation.Block).symm
      (Finsupp.equivFunOnFinite.symm (presentation.blockFloorCorrection
        (rationalChartWitness adequate common_support b) i))))
    presentation.presentationToBlocks_comp_blocksToPresentation
  change presentation.presentationToBlocks (presentation.blocksToPresentation _) = _ at h
  rw [h]
  change ((FreeAbelianGroup.equivFinsupp presentation.Block)
    ((FreeAbelianGroup.equivFinsupp presentation.Block).symm
    (Finsupp.equivFunOnFinite.symm (presentation.blockFloorCorrection
    (rationalChartWitness adequate common_support b) i)))) block = _
  rw [AddEquiv.apply_symm_apply]
  change ⌊b (CommonLabelChartSupport.chartCoordinate adequate common_support i
    (presentation.blockLabel block))⌋ = _
  rw [Subsingleton.elim (presentation.blockLabel block) label]
  rfl
/-- 元G-125のintegralCorrectionは厳密に(0,1)。 -/
theorem original_floor_eq_base : integralCorrection (P := presentation) (C := cechCover)
    adequate common_support halfCorrection = baseCorrection := by
  apply integralZeroEquiv.injective
  funext i
  rw [integral_floor_coordinate,halfCorrection_coordinates,baseCorrection_coordinates]
  cases i <;> norm_num
end AAT.AG.SpecifiedRepairLifting.RationalWitness

#print axioms AAT.AG.SpecifiedRepairLifting.RationalWitness.actualComplex
#print axioms AAT.AG.SpecifiedRepairLifting.RationalWitness.diagnosticComplex
#print axioms AAT.AG.SpecifiedRepairLifting.RationalWitness.comparison
#print axioms AAT.AG.SpecifiedRepairLifting.RationalWitness.localData
#print axioms AAT.AG.SpecifiedRepairLifting.RationalWitness.mismatch_coordinate
#print axioms AAT.AG.SpecifiedRepairLifting.RationalWitness.halfCorrection
#print axioms AAT.AG.SpecifiedRepairLifting.RationalWitness.halfCorrection_coordinates
#print axioms AAT.AG.SpecifiedRepairLifting.RationalWitness.baseCorrection
#print axioms AAT.AG.SpecifiedRepairLifting.RationalWitness.baseCorrection_coordinates
#print axioms AAT.AG.SpecifiedRepairLifting.RationalWitness.half_compatible
#print axioms AAT.AG.SpecifiedRepairLifting.RationalWitness.base_boundary
#print axioms AAT.AG.SpecifiedRepairLifting.RationalWitness.mismatch_closed
#print axioms AAT.AG.SpecifiedRepairLifting.RationalWitness.integer_ne_half
#print axioms AAT.AG.SpecifiedRepairLifting.RationalWitness.no_half_lift
#print axioms AAT.AG.SpecifiedRepairLifting.RationalWitness.integral_floor_coordinate
#print axioms AAT.AG.SpecifiedRepairLifting.RationalWitness.original_floor_eq_base
#assert_standard_axioms_only AAT.AG.SpecifiedRepairLifting.RationalWitness
