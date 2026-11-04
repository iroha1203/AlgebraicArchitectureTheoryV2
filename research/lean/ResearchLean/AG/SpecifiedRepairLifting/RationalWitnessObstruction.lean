import ResearchLean.AG.SpecifiedRepairLifting.RationalWitnessCycles

/-! # W1の同じ残差・障害と整数指定補正

Implementation notes: 一般A/Bの定義を実G-125比較へ直接代入する。
半整数障害と整数指定の一意性を同じ群・同じ射の下で証明する。
-/
noncomputable section
namespace AAT.AG.SpecifiedRepairLifting.RationalWitnessObstruction
open RationalWitnessInput RationalWitnessCoordinates RationalWitness RationalWitnessCycles
/-- 同じ実残差のQ/Z座標は半整数類。 -/
theorem residual_coordinate : cokernelEquiv
    (residualClass comparison localData.actualMismatch halfCorrection baseCorrection base_boundary half_compatible) =
    QuotientAddGroup.mk' (Int.castAddHom ℚ).range (1/2) := by
  change cokernelEquiv (QuotientAddGroup.mk' _
    (residualCycle comparison localData.actualMismatch halfCorrection baseCorrection base_boundary half_compatible)) = _
  rw [cokernelEquiv_class]
  congr 1
  rw [rationalCyclesEquiv_apply,residualCycle_val,map_sub]
  change rationalZeroEquiv halfCorrection false - rationalZeroEquiv
    (presentation.actualCechCoefficientCochain0 cechCover adequate baseCorrection) false = 1/2
  rw [halfCorrection_coordinates,comparison_zero,baseCorrection_coordinates]
  norm_num
/-- Bの実残差は非零。 -/
theorem residual_ne_zero :
    residualClass comparison localData.actualMismatch halfCorrection baseCorrection base_boundary half_compatible ≠ 0 := by
  intro h
  apply half_class_ne_zero
  rw [← residual_coordinate,h,map_zero]
/-- Aの標準mapping-cone障害も非零。 -/
theorem obstruction_ne_zero :
    nonnegativeObstruction comparison localData.actualMismatch halfCorrection mismatch_closed half_compatible ≠ 0 := by
  intro h
  exact no_half_lift ((nonnegativeObstruction_zero_iff_lift _ _ _ _ _).mp h)
/-- 指定値を整数像(0,1)へ変えた場合。 -/
def integerCorrection : diagnosticComplex.C0 := rationalZeroEquiv.symm (fun i => if i then 1 else 0)
/-- 整数指定の両成分。 -/
theorem integerCorrection_coordinates (i : Bool) :
    rationalZeroEquiv integerCorrection i = if i then 1 else 0 :=
  congrFun (rationalZeroEquiv.apply_symm_apply _) i
/-- 同じ元補正がこの指定値そのものを実現する。 -/
theorem base_comparison : comparison.f 0 baseCorrection = integerCorrection := by
  apply rationalZeroEquiv.injective
  funext i
  change rationalZeroEquiv (presentation.actualCechCoefficientCochain0 cechCover adequate baseCorrection) i = _
  rw [comparison_zero,baseCorrection_coordinates,integerCorrection_coordinates]
  cases i <;> norm_num
/-- 同じ実比較の整数指定Lift。 -/
def integerLift : NonnegativeLift comparison localData.actualMismatch integerCorrection :=
  ⟨baseCorrection,base_boundary,base_comparison⟩
/-- 実degree-zero比較の単射性は各整数座標の単射性から従う。 -/
theorem comparison_zero_injective : Function.Injective (comparison.f 0) := by
  intro a b hab
  apply integralZeroEquiv.injective
  funext i
  have h := congrArg (fun c => rationalZeroEquiv c i) hab
  change rationalZeroEquiv (presentation.actualCechCoefficientCochain0 cechCover adequate a) i =
    rationalZeroEquiv (presentation.actualCechCoefficientCochain0 cechCover adequate b) i at h
  rw [comparison_zero,comparison_zero] at h
  exact_mod_cast h
/-- 整数指定の全持ち上げは厳密に元の(0,1)。 -/
theorem integer_lift_unique (a : NonnegativeLift comparison localData.actualMismatch integerCorrection) :
    a = integerLift := by
  apply Subtype.ext
  apply comparison_zero_injective
  exact a.property.2.trans base_comparison.symm
/-- 実補正群の核は零。 -/
theorem correction_kernel_zero : (cycleComparison comparison).ker = ⊥ := by
  apply (nonempty_lift_unique_iff_kernel_zero comparison integerLift).mp
  exact ⟨fun a b => (integer_lift_unique a).trans (integer_lift_unique b).symm⟩
/-- 整数指定も同じ適合条件を満たす。 -/
theorem integer_compatible : (diagnosticNative diagnosticComplex).d 0 1 integerCorrection =
    comparison.f 1 localData.actualMismatch := by
  rw [← base_comparison,← base_boundary]
  exact congrArg (fun f => f baseCorrection) (comparison.comm 0 1)
/-- 整数指定ではBの同じ残差が零。 -/
theorem integer_residual_zero :
    residualClass comparison localData.actualMismatch integerCorrection baseCorrection base_boundary integer_compatible = 0 :=
  (residualClass_zero_iff_lift _ _ _ _ _ _).mpr ⟨integerLift⟩
/-- 整数指定ではAの同じ標準障害が零。 -/
theorem integer_obstruction_zero :
    nonnegativeObstruction comparison localData.actualMismatch integerCorrection mismatch_closed integer_compatible = 0 :=
  (nonnegativeObstruction_zero_iff_lift _ _ _ _ _).mpr ⟨integerLift⟩
end AAT.AG.SpecifiedRepairLifting.RationalWitnessObstruction

#print axioms AAT.AG.SpecifiedRepairLifting.RationalWitnessObstruction.residual_coordinate
#print axioms AAT.AG.SpecifiedRepairLifting.RationalWitnessObstruction.residual_ne_zero
#print axioms AAT.AG.SpecifiedRepairLifting.RationalWitnessObstruction.obstruction_ne_zero
#print axioms AAT.AG.SpecifiedRepairLifting.RationalWitnessObstruction.integerCorrection
#print axioms AAT.AG.SpecifiedRepairLifting.RationalWitnessObstruction.integerCorrection_coordinates
#print axioms AAT.AG.SpecifiedRepairLifting.RationalWitnessObstruction.base_comparison
#print axioms AAT.AG.SpecifiedRepairLifting.RationalWitnessObstruction.integerLift
#print axioms AAT.AG.SpecifiedRepairLifting.RationalWitnessObstruction.comparison_zero_injective
#print axioms AAT.AG.SpecifiedRepairLifting.RationalWitnessObstruction.integer_lift_unique
#print axioms AAT.AG.SpecifiedRepairLifting.RationalWitnessObstruction.correction_kernel_zero
#print axioms AAT.AG.SpecifiedRepairLifting.RationalWitnessObstruction.integer_compatible
#print axioms AAT.AG.SpecifiedRepairLifting.RationalWitnessObstruction.integer_residual_zero
#print axioms AAT.AG.SpecifiedRepairLifting.RationalWitnessObstruction.integer_obstruction_zero
#assert_standard_axioms_only AAT.AG.SpecifiedRepairLifting.RationalWitnessObstruction
