import ResearchLean.AG.SpecifiedRepairLifting.RationalWitnessInput
import Mathlib.LinearAlgebra.Finsupp.Pi

/-! # W1の実係数と実Čech座標

Implementation notes: 元のpresentation quotientをblock正規形で整数へ同定する。
別の係数群を定義して置き換えるのでなく、元G-125の係数比較を評価する。
-/
noncomputable section
namespace AAT.AG.SpecifiedRepairLifting.RationalWitnessCoordinates
open RationalWitnessGeometry RationalWitnessContext RationalWitnessInput
open ObstructionDiagnosticBridge CanonicalResolution ResolutionInvariance Cohomology TwoPhase
/-- 指定nerveの一edgeを座標評価点とする。 -/
local instance : Unique supportedNerve.nerve.EdgeComponent := inferInstanceAs (Unique Unit)
/-- 原始一Law表の一元性を座標同型で使用する。 -/
local instance : Subsingleton laws.Law := inferInstanceAs (Subsingleton Unit)
/-- 元の一生成元presentationの整数座標。 -/
def coefficientEquiv : presentation.PresentationGroup ≃+ ℤ :=
  presentation.presentationGroupEquivBlocks.trans
    ((FreeAbelianGroup.equivFinsupp presentation.Block).trans
      (Finsupp.LinearEquiv.finsuppUnique ℤ ℤ presentation.Block).toAddEquiv)
/-- 座標は元のblock係数を読む。 -/
theorem coefficientEquiv_apply (a : presentation.PresentationGroup) :
    coefficientEquiv a = FreeAbelianGroup.coeff block (presentation.presentationToBlocks a) := by
  rfl
/-- 唯一生成元の係数は厳密に1。 -/
theorem coefficientEquiv_generator :
    coefficientEquiv (presentation.generatorClass ((),())) = 1 := by
  rw [coefficientEquiv_apply,presentation.presentationToBlocks_generatorClass]
  simp [FreeAbelianGroup.coeff,block]
/-- 元の比較は整数から有理数への包含そのもの。 -/
theorem coefficient_comparison (a : presentation.PresentationGroup)
    (l : LawValueLabel laws) :
    presentation.coefficientComparison a l = (coefficientEquiv a : ℚ) := by
  rw [Subsingleton.elim l (presentation.blockLabel block)]
  change presentation.blockToLawCoefficients (presentation.presentationToBlocks a)
    (presentation.blockLabel block) = _
  rw [presentation.blockToLawCoefficients_apply_blockLabel reflection,
    coefficientEquiv_apply]
/-- 元の二chartの整数座標。 -/
def integralZeroEquiv :
    (presentation.faceEmptyCechComplex cechCover).Cn 0 ≃+ (Bool → ℤ) :=
  (presentation.faceEmptyCechCochain0Equiv cechCover).trans
    (AddEquiv.piCongrRight fun _ => coefficientEquiv)
/-- 元の一edgeの整数座標。 -/
def integralOneEquiv :
    (presentation.faceEmptyCechComplex cechCover).Cn 1 ≃+ ℤ :=
  (presentation.faceEmptyCechCochain1Equiv cechCover).trans
    ((AddEquiv.piCongrRight fun _ => coefficientEquiv).trans (AddEquiv.funUnique _ _))
/-- diagnosticのchart座標は元のcellを保持する。 -/
def chartEquiv : supportedNerve.ChartCoordinate laws adequate ≃ Bool where
  toFun := fun c => c.cell
  invFun := fun c => GeneratorPresentation.CommonLabelChartSupport.chartCoordinate
    adequate common_support c label
  left_inv c := by
    apply CellCoordinate.ext
    · rfl
    · exact Subsingleton.elim _ _
    · exact HEq.rfl
  right_inv _ := rfl
/-- diagnosticのedge座標は元の唯一cellを保持する。 -/
def edgeEquiv : supportedNerve.EdgeCoordinate laws adequate ≃ Unit where
  toFun := fun c => c.cell
  invFun := fun c => GeneratorPresentation.CommonLabelChartSupport.edgeCoordinate
    adequate common_support c label
  left_inv c := by
    apply CellCoordinate.ext
    · rfl
    · exact Subsingleton.elim _ _
    · exact HEq.rfl
  right_inv _ := rfl
/-- 実diagnosticの二chart有理座標。 -/
def rationalZeroEquiv : (supportedNerve.lawGeneratedComplex laws adequate).C0 ≃+ (Bool → ℚ) where
  toFun b i := b (chartEquiv.symm i)
  invFun b c := b (chartEquiv c)
  left_inv b := by funext c; simp only [Equiv.symm_apply_apply]
  right_inv b := by funext c; simp only [Equiv.apply_symm_apply]
  map_add' _ _ := rfl
/-- 実diagnosticの一edge有理座標。 -/
def rationalOneEquiv : (supportedNerve.lawGeneratedComplex laws adequate).C1 ≃+ ℚ where
  toFun b := b (edgeEquiv.symm ())
  invFun b := fun _ => b
  left_inv b := by
    funext c
    have h : edgeEquiv.symm () = c := by
      apply edgeEquiv.injective
      exact Subsingleton.elim _ _
    rw [h]
  right_inv _ := rfl
  map_add' _ _ := rfl
/-- chart座標は元の正規化値の整数係数。 -/
theorem integralZeroEquiv_apply (a : (presentation.faceEmptyCechComplex cechCover).Cn 0)
    (i : Bool) : integralZeroEquiv a i =
      coefficientEquiv (presentation.faceEmptyCechCochain0Equiv cechCover a i) := rfl
/-- edge座標は元の正規化値の整数係数。 -/
theorem integralOneEquiv_apply (a : (presentation.faceEmptyCechComplex cechCover).Cn 1) :
    integralOneEquiv a = coefficientEquiv
      (presentation.faceEmptyCechCochain1Equiv cechCover a ()) := rfl
/-- 実Čech微分は右chartから左chartを引く。 -/
theorem integral_d0 (a : (presentation.faceEmptyCechComplex cechCover).Cn 0) :
    integralOneEquiv ((presentation.faceEmptyCechComplex cechCover).d 0 a) =
      integralZeroEquiv a true - integralZeroEquiv a false := by
  rw [integralOneEquiv_apply,presentation.faceEmptyCech_d0_normalizes]
  exact map_sub coefficientEquiv _ _
/-- 実diagnostic微分も同じ差を取る。 -/
theorem rational_d0 (b : (supportedNerve.lawGeneratedComplex laws adequate).C0) :
    rationalOneEquiv ((supportedNerve.lawGeneratedComplex laws adequate).d0 b) =
      rationalZeroEquiv b true - rationalZeroEquiv b false := by
  change b (supportedNerve.edgeRightCoordinate laws adequate
    (GeneratorPresentation.CommonLabelChartSupport.edgeCoordinate adequate common_support () label)) -
    b (supportedNerve.edgeLeftCoordinate laws adequate
    (GeneratorPresentation.CommonLabelChartSupport.edgeCoordinate adequate common_support () label)) = _
  rw [GeneratorPresentation.CommonLabelChartSupport.edgeRightCoordinate_eq,
    GeneratorPresentation.CommonLabelChartSupport.edgeLeftCoordinate_eq]
  rfl
/-- 元のdegree-zero比較は二成分とも整数包含。 -/
theorem comparison_zero (a : (presentation.faceEmptyCechComplex cechCover).Cn 0) (i : Bool) :
    rationalZeroEquiv (presentation.actualCechCoefficientCochain0 cechCover adequate a) i =
      (integralZeroEquiv a i : ℚ) := by
  change presentation.coefficientComparison
    (presentation.faceEmptyCechCochain0Equiv cechCover a i) _ = _
  exact coefficient_comparison _ _
/-- 元のdegree-one比較も同じ整数包含。 -/
theorem comparison_one (a : (presentation.faceEmptyCechComplex cechCover).Cn 1) :
    rationalOneEquiv (presentation.actualCechCoefficientCochain1 cechCover adequate a) =
      (integralOneEquiv a : ℚ) := by
  change presentation.coefficientComparison
    (presentation.faceEmptyCechCochain1Equiv cechCover a ()) _ = _
  exact coefficient_comparison _ _
/-- 元Čechの全ての次数2以上は元の空simplex群。 -/
theorem integral_higher_zero (n : ℕ)
    (a : (cechNative (presentation.faceEmptyCechComplex cechCover)).X (n+2)) : a = 0 :=
  actualCechHigher_zero presentation cechCover n a
/-- diagnosticの次数2は空face座標により零。 -/
theorem rational_two_zero (a : (supportedNerve.lawGeneratedComplex laws adequate).C2) : a = 0 := by
  funext c
  exact isEmptyElim c.cell
end AAT.AG.SpecifiedRepairLifting.RationalWitnessCoordinates

#print axioms AAT.AG.SpecifiedRepairLifting.RationalWitnessCoordinates.coefficientEquiv
#print axioms AAT.AG.SpecifiedRepairLifting.RationalWitnessCoordinates.coefficientEquiv_apply
#print axioms AAT.AG.SpecifiedRepairLifting.RationalWitnessCoordinates.coefficientEquiv_generator
#print axioms AAT.AG.SpecifiedRepairLifting.RationalWitnessCoordinates.coefficient_comparison
#print axioms AAT.AG.SpecifiedRepairLifting.RationalWitnessCoordinates.integralZeroEquiv
#print axioms AAT.AG.SpecifiedRepairLifting.RationalWitnessCoordinates.integralOneEquiv
#print axioms AAT.AG.SpecifiedRepairLifting.RationalWitnessCoordinates.chartEquiv
#print axioms AAT.AG.SpecifiedRepairLifting.RationalWitnessCoordinates.edgeEquiv
#print axioms AAT.AG.SpecifiedRepairLifting.RationalWitnessCoordinates.rationalZeroEquiv
#print axioms AAT.AG.SpecifiedRepairLifting.RationalWitnessCoordinates.rationalOneEquiv
#print axioms AAT.AG.SpecifiedRepairLifting.RationalWitnessCoordinates.integralZeroEquiv_apply
#print axioms AAT.AG.SpecifiedRepairLifting.RationalWitnessCoordinates.integralOneEquiv_apply
#print axioms AAT.AG.SpecifiedRepairLifting.RationalWitnessCoordinates.integral_d0
#print axioms AAT.AG.SpecifiedRepairLifting.RationalWitnessCoordinates.rational_d0
#print axioms AAT.AG.SpecifiedRepairLifting.RationalWitnessCoordinates.comparison_zero
#print axioms AAT.AG.SpecifiedRepairLifting.RationalWitnessCoordinates.comparison_one
#print axioms AAT.AG.SpecifiedRepairLifting.RationalWitnessCoordinates.integral_higher_zero
#print axioms AAT.AG.SpecifiedRepairLifting.RationalWitnessCoordinates.rational_two_zero
#assert_standard_axioms_only AAT.AG.SpecifiedRepairLifting.RationalWitnessCoordinates
