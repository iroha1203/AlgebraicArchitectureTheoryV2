import ResearchLean.AG.SpecifiedRepairLifting.RationalWitness

/-! # W1の実零次cycleとQ/Z

Implementation notes: 実微分のkernelに対角cochainを戻す両方向同型を作る。
同じcycle比較のrangeを整数像と同定して商へ降ろす。
-/
noncomputable section
namespace AAT.AG.SpecifiedRepairLifting.RationalWitnessCycles
open RationalWitnessInput RationalWitnessCoordinates RationalWitness
/-- 元整数cycleの両chart値は等しい。 -/
theorem integral_cycle_diagonal (a : zeroCycles (cechNative actualComplex)) :
    integralZeroEquiv a.val true = integralZeroEquiv a.val false := by
  have h := a.property
  change (cechNative actualComplex).d 0 1 a.val = 0 at h
  rw [cechNative_d] at h
  have hv := congrArg integralOneEquiv h
  rw [integral_d0,map_zero] at hv
  exact sub_eq_zero.mp hv
/-- 元有理cycleの両chart値も等しい。 -/
theorem rational_cycle_diagonal (a : zeroCycles (diagnosticNative diagnosticComplex)) :
    rationalZeroEquiv a.val true = rationalZeroEquiv a.val false := by
  have h := a.property
  change (diagnosticNative diagnosticComplex).d 0 1 a.val = 0 at h
  rw [diagnosticNative_d] at h
  have hv := congrArg rationalOneEquiv h
  change rationalOneEquiv (diagnosticComplex.d0 a.val) = rationalOneEquiv 0 at hv
  rw [rational_d0,map_zero] at hv
  exact sub_eq_zero.mp hv
/-- 元整数cycle群と整数の対角同型。 -/
def integralCyclesEquiv : zeroCycles (cechNative actualComplex) ≃+ ℤ where
  toFun a := integralZeroEquiv a.val false
  invFun n := ⟨integralZeroEquiv.symm (fun _ => n),by
    change (cechNative actualComplex).d 0 1 _ = 0
    rw [cechNative_d]
    apply integralOneEquiv.injective
    rw [integral_d0,AddEquiv.apply_symm_apply,map_zero,sub_self]⟩
  left_inv a := by
    apply Subtype.ext
    apply integralZeroEquiv.injective
    rw [AddEquiv.apply_symm_apply]
    funext i
    cases i
    · rfl
    · exact (integral_cycle_diagonal a).symm
  right_inv n := congrFun (integralZeroEquiv.apply_symm_apply _) false
  map_add' a b := congrFun (map_add integralZeroEquiv a.val b.val) false
/-- 元有理cycle群と有理数の対角同型。 -/
def rationalCyclesEquiv : zeroCycles (diagnosticNative diagnosticComplex) ≃+ ℚ where
  toFun a := rationalZeroEquiv a.val false
  invFun n := ⟨rationalZeroEquiv.symm (fun _ => n),by
    change (diagnosticNative diagnosticComplex).d 0 1 _ = 0
    rw [diagnosticNative_d]
    apply rationalOneEquiv.injective
    change rationalOneEquiv (diagnosticComplex.d0 (rationalZeroEquiv.symm (fun _ => n))) = rationalOneEquiv 0
    rw [rational_d0,AddEquiv.apply_symm_apply,map_zero,sub_self]⟩
  left_inv a := by
    apply Subtype.ext
    apply rationalZeroEquiv.injective
    rw [AddEquiv.apply_symm_apply]
    funext i
    cases i
    · rfl
    · exact (rational_cycle_diagonal a).symm
  right_inv n := congrFun (rationalZeroEquiv.apply_symm_apply _) false
  map_add' a b := congrFun (map_add rationalZeroEquiv a.val b.val) false
/-- 実kは対角座標で整数包含。 -/
theorem cycle_comparison_coordinate (a : zeroCycles (cechNative actualComplex)) :
    rationalCyclesEquiv (cycleComparison comparison a) = (integralCyclesEquiv a : ℚ) := by
  change rationalZeroEquiv
    (RationalWitnessInput.presentation.actualCechCoefficientCochain0
      RationalWitnessInput.cechCover RationalWitnessInput.adequate a.val) false = _
  exact comparison_zero a.val false
/-- 実kの単射性。 -/
theorem cycle_comparison_injective : Function.Injective (cycleComparison comparison) := by
  intro a b hab
  apply integralCyclesEquiv.injective
  have h := congrArg rationalCyclesEquiv hab
  rw [cycle_comparison_coordinate,cycle_comparison_coordinate] at h
  exact_mod_cast h
/-- 実kは半整数cycleを覆えない。 -/
theorem cycle_comparison_not_surjective : ¬ Function.Surjective (cycleComparison comparison) := by
  intro h
  obtain ⟨a,ha⟩ := h (rationalCyclesEquiv.symm (1/2))
  have hc := congrArg rationalCyclesEquiv ha
  rw [cycle_comparison_coordinate,AddEquiv.apply_symm_apply] at hc
  exact integer_ne_half _ hc
/-- 指定されたQ/Z。 -/
abbrev RationalModIntegers := ℚ ⧸ (Int.castAddHom ℚ).range
/-- 実有理cycleを同じQ/Zへ送る。 -/
def cycleQuotient : zeroCycles (diagnosticNative diagnosticComplex) →+ RationalModIntegers :=
  (QuotientAddGroup.mk' (Int.castAddHom ℚ).range).comp rationalCyclesEquiv.toAddMonoidHom
/-- cycle商の値。 -/
theorem cycleQuotient_apply (a : zeroCycles (diagnosticNative diagnosticComplex)) :
    cycleQuotient a = QuotientAddGroup.mk' (Int.castAddHom ℚ).range (rationalCyclesEquiv a) := rfl
/-- 同じ実kの像が商射の核。 -/
theorem cycle_quotient_kernel : cycleQuotient.ker = (cycleComparison comparison).range := by
  ext a
  change cycleQuotient a = 0 ↔ ∃ b, cycleComparison comparison b = a
  rw [cycleQuotient_apply]
  change (QuotientAddGroup.mk (rationalCyclesEquiv a) : RationalModIntegers) = 0 ↔ _
  rw [QuotientAddGroup.eq_zero_iff]
  change (∃ n : ℤ, (n : ℚ) = rationalCyclesEquiv a) ↔ _
  constructor
  · rintro ⟨n,hn⟩
    refine ⟨integralCyclesEquiv.symm n,?_⟩
    apply rationalCyclesEquiv.injective
    rw [cycle_comparison_coordinate,AddEquiv.apply_symm_apply,hn]
  · rintro ⟨b,rfl⟩
    exact ⟨integralCyclesEquiv b,(cycle_comparison_coordinate b).symm⟩
/-- 商射は全射。 -/
theorem cycle_quotient_surjective : Function.Surjective cycleQuotient :=
  (QuotientAddGroup.mk'_surjective _).comp rationalCyclesEquiv.surjective
/-- 実余核はQ/Zそのもの。 -/
def cokernelEquiv : CorrectionCokernel comparison ≃+ RationalModIntegers :=
  (QuotientAddGroup.quotientAddEquivOfEq cycle_quotient_kernel.symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective cycleQuotient cycle_quotient_surjective)
/-- 実余核同型の代表元評価。 -/
theorem cokernelEquiv_class (a : zeroCycles (diagnosticNative diagnosticComplex)) :
    cokernelEquiv (QuotientAddGroup.mk' (cycleComparison comparison).range a) =
      QuotientAddGroup.mk' (Int.castAddHom ℚ).range (rationalCyclesEquiv a) := rfl
/-- 半整数のQ/Z類は非零。 -/
theorem half_class_ne_zero :
    (QuotientAddGroup.mk' (Int.castAddHom ℚ).range (1/2) : RationalModIntegers) ≠ 0 := by
  intro h
  obtain ⟨n,hn⟩ := (QuotientAddGroup.eq_zero_iff _).mp h
  exact integer_ne_half n hn
end AAT.AG.SpecifiedRepairLifting.RationalWitnessCycles

#print axioms AAT.AG.SpecifiedRepairLifting.RationalWitnessCycles.integral_cycle_diagonal
#print axioms AAT.AG.SpecifiedRepairLifting.RationalWitnessCycles.rational_cycle_diagonal
#print axioms AAT.AG.SpecifiedRepairLifting.RationalWitnessCycles.integralCyclesEquiv
#print axioms AAT.AG.SpecifiedRepairLifting.RationalWitnessCycles.rationalCyclesEquiv
#print axioms AAT.AG.SpecifiedRepairLifting.RationalWitnessCycles.cycle_comparison_coordinate
#print axioms AAT.AG.SpecifiedRepairLifting.RationalWitnessCycles.cycle_comparison_injective
#print axioms AAT.AG.SpecifiedRepairLifting.RationalWitnessCycles.cycle_comparison_not_surjective
#print axioms AAT.AG.SpecifiedRepairLifting.RationalWitnessCycles.RationalModIntegers
#print axioms AAT.AG.SpecifiedRepairLifting.RationalWitnessCycles.cycleQuotient
#print axioms AAT.AG.SpecifiedRepairLifting.RationalWitnessCycles.cycleQuotient_apply
#print axioms AAT.AG.SpecifiedRepairLifting.RationalWitnessCycles.cycle_quotient_kernel
#print axioms AAT.AG.SpecifiedRepairLifting.RationalWitnessCycles.cycle_quotient_surjective
#print axioms AAT.AG.SpecifiedRepairLifting.RationalWitnessCycles.cokernelEquiv
#print axioms AAT.AG.SpecifiedRepairLifting.RationalWitnessCycles.cokernelEquiv_class
#print axioms AAT.AG.SpecifiedRepairLifting.RationalWitnessCycles.half_class_ne_zero
#assert_standard_axioms_only AAT.AG.SpecifiedRepairLifting.RationalWitnessCycles
