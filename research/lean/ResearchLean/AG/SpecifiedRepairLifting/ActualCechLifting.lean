import ResearchLean.AG.SpecifiedRepairLifting.ActualCechComplex
/-! # 同じ実 Čech 比較における指定補正

Implementation notes: 元の actualMismatch と任意の診断補正を一般理論へ代入する。
reflection と common-label 条件は床補正を元の補正として生成する節だけで使う。
床補正が指定診断値そのものを実現すると仮定する方式は採らず、その差を実余核へ送る。
局所状態は持ち上げの負値で更新し、元の mismatch の零性を直接検証する。
-/
noncomputable section
open CategoryTheory HomologicalComplex
namespace AAT.AG.SpecifiedRepairLifting
open Cohomology TwoPhase ObstructionDiagnosticBridge CanonicalResolution ResolutionInvariance
open GeneratorPresentation GeneratorPresentation.ActualCechAffineLocalData
universe u
variable {Source : Type u} [Fintype Source] {q : Reading Source} {laws : FiniteLawFamily Source}
variable {U : AtomCarrier.{u}} {A : ArchitectureObject U} {S : Site.AATSite A}
variable {D : TargetSupportedNerve q} {G : ContextOpenSupport S} [IsEmpty D.nerve.FaceComponent]
variable (P : GeneratorPresentation laws) (V : FaceEmptyAATCechCover D G) (ha : laws.Adequate q)
variable (x : ActualCechAffineLocalData P V) (b : D.ChartCoordinate laws ha → ℚ)

omit [Fintype Source] in
/-- 元の mismatch は同じ標準複体でも閉じている。 -/
theorem actualMismatch_closed :
    (cechNative (P.faceEmptyCechComplex V)).d 1 2 x.actualMismatch = 0 := by
  rw [cechNative_d, P.faceEmptyCech_d1_eq_zero V]
  rfl
/-- 診断補正式から同じ比較の適合条件を生成する。 -/
theorem actualMismatch_compatible (hb : D.lawGeneratedD0 laws ha b = x.diagnosticMismatch ha) :
    (diagnosticNative (D.lawGeneratedComplex laws ha)).d 0 1 b =
      (actualComparison P V ha).f 1 x.actualMismatch := by
  rw [diagnosticNative_d]
  change D.lawGeneratedD0 laws ha b = P.actualCechCoefficientCochain1 V ha x.actualMismatch
  rw [x.actual_cech_coefficient_actual_mismatch_eq_diagnostic_mismatch, hb]
/-- 指定診断 cochain そのものを実現する元の持ち上げ。 -/
abbrev ActualLift := NonnegativeLift (actualComparison P V ha) x.actualMismatch b
/-- 同じ持ち上げは元の二つの厳密等式を満たす。 -/
theorem actualLift_equations (a : ActualLift P V ha x b) :
    (P.faceEmptyCechComplex V).d 0 a.val = x.actualMismatch ∧
      P.actualCechCoefficientCochain0 V ha a.val = b := by
  have hd := a.property.1
  rw [cechNative_d] at hd
  exact ⟨hd, a.property.2⟩
/-- 元の二等式から同じ標準持ち上げを構成する。 -/
def actualLiftOfEquations (a : (P.faceEmptyCechComplex V).Cn 0)
    (hd : (P.faceEmptyCechComplex V).d 0 a = x.actualMismatch)
    (hf : P.actualCechCoefficientCochain0 V ha a = b) : ActualLift P V ha x b :=
  ⟨a, by rw [cechNative_d]; exact hd, hf⟩
/-- 同じ指定入力の標準錐障害。元の補正を事前に仮定しない。 -/
def actualObstruction (hb : D.lawGeneratedD0 laws ha b = x.diagnosticMismatch ha) :=
  nonnegativeObstruction (actualComparison P V ha) x.actualMismatch b
    (actualMismatch_closed P V x) (actualMismatch_compatible P V ha x b hb)
/-- 実指定障害を一般理論の同じ標準障害へ同定する公開API。 -/
theorem actualObstruction_eq_nonnegativeObstruction
    (hb : D.lawGeneratedD0 laws ha b = x.diagnosticMismatch ha) :
    actualObstruction P V ha x b hb =
      nonnegativeObstruction (actualComparison P V ha) x.actualMismatch b
        (actualMismatch_closed P V x) (actualMismatch_compatible P V ha x b hb) := rfl
/-- 任意の診断補正について A を元の二等式へ接続する。 -/
theorem actualObstruction_zero_iff (hb : D.lawGeneratedD0 laws ha b = x.diagnosticMismatch ha) :
    actualObstruction P V ha x b hb = 0 ↔ ∃ a : (P.faceEmptyCechComplex V).Cn 0,
      (P.faceEmptyCechComplex V).d 0 a = x.actualMismatch ∧
        P.actualCechCoefficientCochain0 V ha a = b := by
  rw [actualObstruction, nonnegativeObstruction_zero_iff_lift]
  constructor
  · rintro ⟨a⟩
    exact ⟨a.val, actualLift_equations P V ha x b a⟩
  · rintro ⟨a,hd,hf⟩
    exact ⟨actualLiftOfEquations P V ha x b a hd hf⟩
/-- 実持ち上げの負値で元の局所状態を更新すると mismatch は零になる。 -/
theorem actualLift_update (a : ActualLift P V ha x b) :
    (x.adjustLocalState (-a.val)).actualMismatch = 0 := by
  rw [x.actual_mismatch_adjust_local_state, map_neg,
    (actualLift_equations P V ha x b a).1, add_neg_cancel]
/-- B の全解同値を同じ実係数比較の核から構成する。 -/
def actualLiftKernelEquiv (a : ActualLift P V ha x b) :
    CorrectionKernel (actualComparison P V ha) ≃ ActualLift P V ha x b :=
  kernelEquivLift (actualComparison P V ha) a
/-- B の作用は元の cochain の加法である。 -/
theorem actualLiftKernelEquiv_val (a : ActualLift P V ha x b)
    (k : CorrectionKernel (actualComparison P V ha)) :
    (actualLiftKernelEquiv P V ha x b a k).val = a.val + k.val.val := rfl
/-- 非空時の実補正の一意性は同じ零次比較の核の消滅と同値。 -/
theorem actualLift_unique_iff (a : ActualLift P V ha x b) :
    Subsingleton (ActualLift P V ha x b) ↔ (cycleComparison (actualComparison P V ha)).ker = ⊥ :=
  nonempty_lift_unique_iff_kernel_zero _ a
omit [Fintype Source] in
/-- 元の actualClass は同じ mismatch の標準類へ送られる。 -/
theorem actualClass_native :
    cechH1Equiv (P.faceEmptyCechComplex V) x.actualClass =
      oneClass x.actualMismatch (actualMismatch_closed P V x) := rfl
/-- B の p の符号は元の actualClass に対しても同じである。 -/
theorem actualObstruction_projection (hb : D.lawGeneratedD0 laws ha b = x.diagnosticMismatch ha) :
    coneProjection (actualComparison P V ha) (actualObstruction P V ha x b hb) =
      -cechH1Equiv (P.faceEmptyCechComplex V) x.actualClass :=
  coneProjection_obstruction _ _ _ _ _

/-- 任意の元補正から同じ余核の残差を構成する。 -/
def actualResidual (a₀ : (P.faceEmptyCechComplex V).Cn 0)
    (h₀ : (P.faceEmptyCechComplex V).d 0 a₀ = x.actualMismatch)
    (hb : D.lawGeneratedD0 laws ha b = x.diagnosticMismatch ha) :
    CorrectionCokernel (actualComparison P V ha) :=
  residualClass (actualComparison P V ha) x.actualMismatch b a₀
    (by rw [cechNative_d]; exact h₀) (actualMismatch_compatible P V ha x b hb)
/-- 実残差を一般理論の同じ余核類へ同定する公開API。 -/
theorem actualResidual_eq_residualClass (a₀ : (P.faceEmptyCechComplex V).Cn 0)
    (h₀ : (P.faceEmptyCechComplex V).d 0 a₀ = x.actualMismatch)
    (hb : D.lawGeneratedD0 laws ha b = x.diagnosticMismatch ha) :
    actualResidual P V ha x b a₀ h₀ hb =
      residualClass (actualComparison P V ha) x.actualMismatch b a₀
        (by rw [cechNative_d]; exact h₀) (actualMismatch_compatible P V ha x b hb) := rfl
/-- B の j は元補正からの残差を同じ指定障害へ送る。 -/
theorem actualResidual_inclusion (a₀ : (P.faceEmptyCechComplex V).Cn 0)
    (h₀ : (P.faceEmptyCechComplex V).d 0 a₀ = x.actualMismatch)
    (hb : D.lawGeneratedD0 laws ha b = x.diagnosticMismatch ha) :
    cokernelInclusion (actualComparison P V ha) (actualResidual P V ha x b a₀ h₀ hb) =
      actualObstruction P V ha x b hb :=
  cokernelInclusion_residual _ _ _ _ _ _ _
/-- B の残差零性は指定補正の持ち上げと同値。 -/
theorem actualResidual_zero_iff (a₀ : (P.faceEmptyCechComplex V).Cn 0)
    (h₀ : (P.faceEmptyCechComplex V).d 0 a₀ = x.actualMismatch)
    (hb : D.lawGeneratedD0 laws ha b = x.diagnosticMismatch ha) :
    actualResidual P V ha x b a₀ h₀ hb = 0 ↔ Nonempty (ActualLift P V ha x b) :=
  residualClass_zero_iff_lift _ _ _ _ _ _
/-- 明示された反映条件下でのみ既存の床補正を元補正として生成する。 -/
theorem integralCorrection_is_correction (hs : CommonLabelChartSupport D laws ha)
    (hr : P.ReflectionCondition)
    (hb : D.lawGeneratedD0 laws ha b = x.diagnosticMismatch ha) :
    (P.faceEmptyCechComplex V).d 0 (integralCorrection (P := P) (C := V) ha hs b) =
      x.actualMismatch :=
  (x.actual_mismatch_eq_d_integralCorrection ha hs hr b hb.symm).symm
/-- 床補正の残差は同じ実 φ⁰ の値との差であり、指定値との一致を仮定しない。 -/
theorem integralCorrection_residual_value (hs : CommonLabelChartSupport D laws ha)
    (hr : P.ReflectionCondition)
    (hb : D.lawGeneratedD0 laws ha b = x.diagnosticMismatch ha) :
    (residualCycle (actualComparison P V ha) x.actualMismatch b
      (integralCorrection (P := P) (C := V) ha hs b)
      (by rw [cechNative_d]; exact integralCorrection_is_correction P V ha x b hs hr hb)
      (actualMismatch_compatible P V ha x b hb)).val =
        b - P.actualCechCoefficientCochain0 V ha (integralCorrection (P := P) (C := V) ha hs b) := rfl
/-- 床補正で生成した同じ残差の余核類が指定障害そのものを表す。 -/
theorem integralCorrection_residual_obstruction (hs : CommonLabelChartSupport D laws ha)
    (hr : P.ReflectionCondition)
    (hb : D.lawGeneratedD0 laws ha b = x.diagnosticMismatch ha) :
    cokernelInclusion (actualComparison P V ha)
      (actualResidual P V ha x b (integralCorrection (P := P) (C := V) ha hs b)
        (integralCorrection_is_correction P V ha x b hs hr hb) hb) =
      actualObstruction P V ha x b hb :=
  actualResidual_inclusion P V ha x b _ _ hb
end AAT.AG.SpecifiedRepairLifting

#print axioms AAT.AG.SpecifiedRepairLifting.actualMismatch_closed
#print axioms AAT.AG.SpecifiedRepairLifting.actualMismatch_compatible
#print axioms AAT.AG.SpecifiedRepairLifting.ActualLift
#print axioms AAT.AG.SpecifiedRepairLifting.actualLift_equations
#print axioms AAT.AG.SpecifiedRepairLifting.actualLiftOfEquations
#print axioms AAT.AG.SpecifiedRepairLifting.actualObstruction
#print axioms AAT.AG.SpecifiedRepairLifting.actualObstruction_eq_nonnegativeObstruction
#print axioms AAT.AG.SpecifiedRepairLifting.actualObstruction_zero_iff
#print axioms AAT.AG.SpecifiedRepairLifting.actualLift_update
#print axioms AAT.AG.SpecifiedRepairLifting.actualLiftKernelEquiv
#print axioms AAT.AG.SpecifiedRepairLifting.actualLiftKernelEquiv_val
#print axioms AAT.AG.SpecifiedRepairLifting.actualLift_unique_iff
#print axioms AAT.AG.SpecifiedRepairLifting.actualClass_native
#print axioms AAT.AG.SpecifiedRepairLifting.actualObstruction_projection
#print axioms AAT.AG.SpecifiedRepairLifting.actualResidual
#print axioms AAT.AG.SpecifiedRepairLifting.actualResidual_eq_residualClass
#print axioms AAT.AG.SpecifiedRepairLifting.actualResidual_inclusion
#print axioms AAT.AG.SpecifiedRepairLifting.actualResidual_zero_iff
#print axioms AAT.AG.SpecifiedRepairLifting.integralCorrection_is_correction
#print axioms AAT.AG.SpecifiedRepairLifting.integralCorrection_residual_value
#print axioms AAT.AG.SpecifiedRepairLifting.integralCorrection_residual_obstruction
#assert_standard_axioms_only AAT.AG.SpecifiedRepairLifting
