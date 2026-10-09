import ResearchLean.AG.AtlasCoefficientFiber.WitnessFourDiagnostics
import ResearchLean.AG.AtlasCoefficientFiber.LawHomologyCoordinates

/-!
# W4：同じ原三角形の二発生Law

Implementation notes: 元ラベルごとの原η/ε/κ/R/τを実Lawへ両逆座標で集める。
同じ支持を持つfalse/trueを統合せず、係数余核の二periodを保持する。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber.WitnessFourLaw
open CategoryTheory HomologicalComplex CochainComplex
open CanonicalResolution ResolutionInvariance FaceRelationSubdivision TwoPhase AtlasDefectComposition
open FaceRelationSubdivision.WitnessOne (N plus minus qc qf coarser rPlus rMinus laws coarseAdequate fineAdequate)

/-- 元Lawラベルは同じG134の二Bool。 -/
theorem labels_card : Fintype.card (LawValueLabel laws) = 2 := by
  rw [Fintype.card_congr FaceRelationSubdivision.WitnessOne.labelEquiv]
  rfl

/-- 同じ原plus Law literal Rの零性。 -/
theorem plus_R_zero : Subsingleton (lawR rPlus laws coarseAdequate) := by
  letI (l : LawValueLabel laws) := WitnessFourTriangle.plus_R_zero (labelValueFiber laws qc coarseAdequate l)
  exact (lawRFamilyEquiv rPlus laws coarseAdequate).toEquiv.subsingleton
/-- 同じ原minus Law literal Rの零性。 -/
theorem minus_R_zero : Subsingleton (lawR rMinus laws coarseAdequate) := by
  letI (l : LawValueLabel laws) := WitnessFourTriangle.minus_R_zero (labelValueFiber laws qc coarseAdequate l)
  exact (lawRFamilyEquiv rMinus laws coarseAdequate).toEquiv.subsingleton
/-- 同じ原plus Law標準τは零。 -/
theorem plus_tau_zero : lawConnectingTau rPlus laws coarseAdequate = 0 := by
  letI := plus_R_zero
  exact LinearMap.ext fun x => by rw [Subsingleton.elim x 0, map_zero]; rfl
/-- 同じ原minus Law標準τは零。 -/
theorem minus_tau_zero : lawConnectingTau rMinus laws coarseAdequate = 0 := by
  letI := minus_R_zero
  exact LinearMap.ext fun x => by rw [Subsingleton.elim x 0, map_zero]; rfl

/-- 同じ原plus Law aの両逆は各元labelの原aから生成する。 -/
def plusUnitEquiv : (zeroExtension (N.lawGeneratedComplex laws coarseAdequate)).homology (1 : ℤ) ≃ₗ[ℚ]
    (zeroExtension (lawPushforwardComplex rPlus laws coarseAdequate)).homology (1 : ℤ) :=
  (lawCoarseHomologyEquiv (Nc := N) laws coarseAdequate 1).trans
    ((LinearEquiv.piCongrRight (fun l : LawValueLabel laws =>
      LinearEquiv.ofBijective (unitH1 rPlus (labelValueFiber laws qc coarseAdequate l))
        (WitnessFourDiagnostics.plus_unit_bijective _))).trans
      (lawPushforwardHomologyEquiv rPlus laws coarseAdequate 1).symm)
/-- 元Law可逆座標の順写像は同じ原a。 -/
theorem plusUnitEquiv_apply (x) : plusUnitEquiv x = lawUnitH1 rPlus laws coarseAdequate x := by
  apply (lawPushforwardHomologyEquiv rPlus laws coarseAdequate 1).injective
  funext l
  dsimp only [plusUnitEquiv, LinearEquiv.trans_apply, LinearEquiv.piCongrRight_apply]
  rw [LinearEquiv.apply_symm_apply]
  exact (lawUnit_homology_component rPlus laws coarseAdequate 1 x l).symm
/-- 同じ原plus Law係数欠損は零。 -/
theorem plus_unit_defect : blockDefect (lawUnitH1 rPlus laws coarseAdequate) = (0,0) := by
  apply (blockDefect_eq_zero_iff_bijective _).mpr
  have hh : plusUnitEquiv.toLinearMap = lawUnitH1 rPlus laws coarseAdequate := LinearMap.ext plusUnitEquiv_apply
  rw [← hh]
  exact plusUnitEquiv.bijective

/-- 原minus Law εの両逆を同じ元labelのε両逆から生成する。 -/
def minusEvaluationEquiv : (zeroExtension (lawPushforwardComplex rMinus laws coarseAdequate)).homology (1 : ℤ) ≃ₗ[ℚ]
    (zeroExtension (minus.lawGeneratedComplex laws (lawFineAdequate (h := coarser) laws coarseAdequate))).homology (1 : ℤ) :=
  (lawPushforwardHomologyEquiv rMinus laws coarseAdequate 1).trans
    ((LinearEquiv.piCongrRight (fun l : LawValueLabel laws =>
      WitnessFourDiagnostics.minusEvaluationEquiv (labelValueFiber laws qc coarseAdequate l))).trans
      (lawFineHomologyEquiv (Nf := minus) (h := coarser) laws coarseAdequate 1).symm)
/-- 原Law ε両逆の順値は同じ標準評価射。 -/
theorem minusEvaluationEquiv_apply (x) : minusEvaluationEquiv x = lawEvaluationH1 rMinus laws coarseAdequate x := by
  apply (lawFineHomologyEquiv (Nf := minus) (h := coarser) laws coarseAdequate 1).injective
  funext l
  dsimp only [minusEvaluationEquiv, LinearEquiv.trans_apply, LinearEquiv.piCongrRight_apply]
  rw [LinearEquiv.apply_symm_apply]
  rw [LinearEquiv.piCongrRight_apply, WitnessFourDiagnostics.minusEvaluationEquiv_apply]
  exact (lawEvaluation_homology_component rMinus laws coarseAdequate 1 x l).symm
/-- 同じ元Law aは二labelの各原a単射から単射。 -/
theorem minus_unit_injective : Function.Injective (lawUnitH1 rMinus laws coarseAdequate) := by
  intro x y hxy
  apply (lawCoarseHomologyEquiv (Nc := N) laws coarseAdequate 1).injective
  funext l
  apply WitnessFourDiagnostics.minus_unit_injective (labelValueFiber laws qc coarseAdequate l)
    (labelValueFiber_nonempty laws qc coarseAdequate l)
  have hl := congrArg (fun z => lawPushforwardHomologyEquiv rMinus laws coarseAdequate 1 z l) hxy
  change lawPushforwardHomologyEquiv rMinus laws coarseAdequate 1
    (homologyMap (zeroExtensionMap (lawUnitHom rMinus laws coarseAdequate)) 1 x) l =
    lawPushforwardHomologyEquiv rMinus laws coarseAdequate 1
      (homologyMap (zeroExtensionMap (lawUnitHom rMinus laws coarseAdequate)) 1 y) l at hl
  rw [lawUnit_homology_component, lawUnit_homology_component] at hl
  exact hl

/-- 同じ原Law a余核と独立標準T余核を元εの両逆で同定する。 -/
def minusUnitCokernelStandardEquiv :
    ((zeroExtension (lawPushforwardComplex rMinus laws coarseAdequate)).homology (1 : ℤ) ⧸
      LinearMap.range (lawUnitH1 rMinus laws coarseAdequate)) ≃ₗ[ℚ]
    ((zeroExtension (minus.lawGeneratedComplex laws fineAdequate)).homology (1 : ℤ) ⧸
      LinearMap.range (lawDirectH1 rMinus laws coarseAdequate)) :=
  LinearConjugation.cokernelEquiv _ _ (LinearEquiv.refl ℚ _) minusEvaluationEquiv (fun x => by
    rw [minusEvaluationEquiv_apply]
    exact (congrArg (fun f => f x) (lawDirectH1_factor rMinus laws coarseAdequate)).symm)
/-- 原Law a余核は同じ二つの追加periodを保ったℚ²。 -/
def minusUnitCokernelEquiv :
    ((zeroExtension (lawPushforwardComplex rMinus laws coarseAdequate)).homology (1 : ℤ) ⧸
      LinearMap.range (lawUnitH1 rMinus laws coarseAdequate)) ≃ₗ[ℚ] ℚ × ℚ :=
  minusUnitCokernelStandardEquiv.trans
    ((lawOldCokernelStandardEquiv rMinus laws coarseAdequate).symm.trans
      FaceRelationSubdivision.WitnessOne.minusLawCokernel)
/-- 原Law係数欠損は同じa実核・余核から(0,2)。 -/
theorem minus_unit_defect : blockDefect (lawUnitH1 rMinus laws coarseAdequate) = (0,2) := by
  apply Prod.ext
  · rw [blockDefect_kernel_dimension]
    letI : Subsingleton (LinearMap.ker (lawUnitH1 rMinus laws coarseAdequate)) := by
      rw [LinearMap.ker_eq_bot.mpr minus_unit_injective]
      infer_instance
    exact Module.finrank_zero_of_subsingleton
  · rw [blockDefect_cokernel_dimension, minusUnitCokernelEquiv.finrank_eq]
    simp only [Module.finrank_prod, Module.finrank_self]

/-- 同じ原二labelのplus独立実Law診断。 -/
theorem plus_defect : blockDefect FaceRelationSubdivision.WitnessOne.plusLawHom.h1Map = (0,0) := by
  change blockDefect (rPlus.generatedComparisonH1Map laws coarseAdequate
    (lawFineAdequate (h := coarser) laws coarseAdequate)) = (0,0)
  rw [lawCoefficientBlockDefect_sum rPlus laws coarseAdequate]
  have hk (l : LawValueLabel laws) : Module.finrank ℚ (LinearMap.ker (unitH1 rPlus (labelValueFiber laws qc coarseAdequate l))) = 0 := by
    rw [← blockDefect_kernel_dimension, WitnessFourDiagnostics.plus_unit_defect]
  have hc (l : LawValueLabel laws) : Module.finrank ℚ
      ((zeroExtension (pushforwardComplex rPlus (labelValueFiber laws qc coarseAdequate l))).homology (1 : ℤ) ⧸
        LinearMap.range (unitH1 rPlus (labelValueFiber laws qc coarseAdequate l))) = 0 := by
    rw [← blockDefect_cokernel_dimension, WitnessFourDiagnostics.plus_unit_defect]
  have ht (l : LawValueLabel laws) : Module.finrank ℚ (LinearMap.ker (connectingTau rPlus (labelValueFiber laws qc coarseAdequate l))) = 0 := by
    letI := WitnessFourTriangle.plus_R_zero (labelValueFiber laws qc coarseAdequate l)
    exact Module.finrank_zero_of_subsingleton
  simp only [hk, hc, ht, add_zero, Finset.sum_const_zero]
/-- 同じ原二labelのminus独立実Law診断は係数寄与の和で(0,2)。 -/
theorem minus_defect : blockDefect FaceRelationSubdivision.WitnessOne.minusLawHom.h1Map = (0,2) := by
  change blockDefect (rMinus.generatedComparisonH1Map laws coarseAdequate
    (lawFineAdequate (h := coarser) laws coarseAdequate)) = (0,2)
  rw [lawCoefficientBlockDefect_sum rMinus laws coarseAdequate]
  have hk (l : LawValueLabel laws) : Module.finrank ℚ (LinearMap.ker (unitH1 rMinus (labelValueFiber laws qc coarseAdequate l))) = 0 := by
    rw [← blockDefect_kernel_dimension, WitnessFourDiagnostics.minus_unit_defect _ (labelValueFiber_nonempty laws qc coarseAdequate l)]
  have hc (l : LawValueLabel laws) : Module.finrank ℚ
      ((zeroExtension (pushforwardComplex rMinus (labelValueFiber laws qc coarseAdequate l))).homology (1 : ℤ) ⧸
        LinearMap.range (unitH1 rMinus (labelValueFiber laws qc coarseAdequate l))) = 1 := by
    rw [← blockDefect_cokernel_dimension, WitnessFourDiagnostics.minus_unit_defect _ (labelValueFiber_nonempty laws qc coarseAdequate l)]
  have ht (l : LawValueLabel laws) : Module.finrank ℚ (LinearMap.ker (connectingTau rMinus (labelValueFiber laws qc coarseAdequate l))) = 0 := by
    letI := WitnessFourTriangle.minus_R_zero (labelValueFiber laws qc coarseAdequate l)
    exact Module.finrank_zero_of_subsingleton
  simp only [hk, hc, ht, add_zero, Finset.sum_const_zero, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one, labels_card]

/-- 同じ原plus全Law κは元labelの同じ原κ零から零。 -/
theorem plus_kappa_zero : lawKappa rPlus laws coarseAdequate = 0 := by
  apply LinearMap.ext
  intro x
  funext l
  rw [lawKappa_apply, WitnessFourTriangle.plus_kappa_zero, LinearMap.zero_apply]
  rfl
/-- 同じ原plus全Law κ*も元labelの同じ原κ*零から零。 -/
theorem plus_kappaStar_zero : lawKappaStar rPlus laws coarseAdequate = 0 := by
  apply LinearMap.ext
  intro x
  funext l
  rw [lawKappaStar_apply, WitnessFourTriangle.plus_kappaStar_zero, LinearMap.zero_apply]
  rfl
/-- 同じ原minus全Law κは元labelの同じ原κ零から零。 -/
theorem minus_kappa_zero : lawKappa rMinus laws coarseAdequate = 0 := by
  apply LinearMap.ext
  intro x
  funext l
  rw [lawKappa_apply, WitnessFourTriangle.minus_kappa_zero, LinearMap.zero_apply]
  rfl
/-- 同じ原minus全Law κ*も元labelの同じ原κ*零から零。 -/
theorem minus_kappaStar_zero : lawKappaStar rMinus laws coarseAdequate = 0 := by
  apply LinearMap.ext
  intro x
  funext l
  rw [lawKappaStar_apply, WitnessFourTriangle.minus_kappaStar_zero, LinearMap.zero_apply]
  rfl
end AAT.AG.AtlasCoefficientFiber.WitnessFourLaw

#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourLaw.labels_card
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourLaw.plus_R_zero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourLaw.minus_R_zero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourLaw.plus_tau_zero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourLaw.minus_tau_zero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourLaw.plusUnitEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourLaw.plusUnitEquiv_apply
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourLaw.plus_unit_defect
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourLaw.minusEvaluationEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourLaw.minusEvaluationEquiv_apply
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourLaw.minus_unit_injective
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourLaw.minusUnitCokernelStandardEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourLaw.minusUnitCokernelEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourLaw.minus_unit_defect
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourLaw.plus_defect
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourLaw.minus_defect
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourLaw.plus_kappa_zero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourLaw.plus_kappaStar_zero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourLaw.minus_kappa_zero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourLaw.minus_kappaStar_zero
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber.WitnessFourLaw
