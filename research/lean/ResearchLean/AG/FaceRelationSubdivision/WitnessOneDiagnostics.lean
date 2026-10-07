import ResearchLean.AG.FaceRelationSubdivision.WitnessOneCokernel
import ResearchLean.AG.AtlasDefectComposition.GeneratedDefect
import Formal.Util.AssertStandardAxioms
/-!
# W1 の二ラベルを保持する実 Law 診断

## Implementation notes

実全 Law 射を先に独立生成し、既存分解と各実 block の具体 period へ接続する。
実核・余核の同型から欠損数を得る。二つの同型なラベルを統合しない。
-/
noncomputable section
namespace AAT.AG.FaceRelationSubdivision.WitnessOne
open CanonicalResolution ResolutionInvariance TwoPhase AtlasDefectComposition
/-- 二発生ラベルの値族を順序 false/true の対へ移す。 -/
def labelPairEquiv : (LawValueLabel laws → ℚ) ≃ₗ[ℚ] ℚ × ℚ where
  toFun z := (z (label false),z (label true))
  invFun z l := if labelEquiv l then z.2 else z.1
  left_inv z := by
    funext l
    have he := labelEquiv.symm_apply_apply l
    cases h : labelEquiv l <;> rw [h] at he <;>
      simpa only [h,Bool.false_eq_true,↓reduceIte,labelEquiv_symm] using congrArg z he
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
/-- 同じ独立実全 Law minus 比較の余核は二つの追加 period を保った ℚ²。 -/
def minusLawCokernel :
    ((minus.lawGeneratedComplex laws fineAdequate).H1 ⧸ LinearMap.range minusLawHom.h1Map) ≃ₗ[ℚ] ℚ × ℚ :=
  (lawH1CokernelFamilyEquiv N minus laws coarseAdequate rMinus fineAdequate).trans
    ((LinearEquiv.piCongrRight minusBlockCokernel).trans labelPairEquiv)
/-- 実全 Law plus 比較の核は零。 -/
theorem plusLaw_kernel_subsingleton : Subsingleton (LinearMap.ker plusLawHom.h1Map) := by
  letI (l : LawValueLabel laws) : Subsingleton (LinearMap.ker (rPlus.generatedBlockComparisonH1Map laws coarseAdequate fineAdequate l)) := plus_kernel_subsingleton l
  exact (lawH1KernelFamilyEquiv N plus laws coarseAdequate rPlus fineAdequate).toEquiv.subsingleton
/-- 実全 Law plus 比較の余核は零。 -/
theorem plusLaw_cokernel_subsingleton :
    Subsingleton ((plus.lawGeneratedComplex laws fineAdequate).H1 ⧸ LinearMap.range plusLawHom.h1Map) := by
  letI (l : LawValueLabel laws) : Subsingleton
      ((plus.lawValueBlockComplex laws fineAdequate l).H1 ⧸ LinearMap.range (rPlus.generatedBlockComparisonH1Map laws coarseAdequate fineAdequate l)) := plus_cokernel_subsingleton l
  exact (lawH1CokernelFamilyEquiv N plus laws coarseAdequate rPlus fineAdequate).toEquiv.subsingleton
/-- 実全 Law minus 比較の核は零。 -/
theorem minusLaw_kernel_subsingleton : Subsingleton (LinearMap.ker minusLawHom.h1Map) := by
  letI (l : LawValueLabel laws) : Subsingleton (LinearMap.ker (rMinus.generatedBlockComparisonH1Map laws coarseAdequate fineAdequate l)) := minus_kernel_subsingleton l
  exact (lawH1KernelFamilyEquiv N minus laws coarseAdequate rMinus fineAdequate).toEquiv.subsingleton
/-- 一ラベル plus の実欠損は (0,0)。 -/
theorem plus_block_defect (l : LawValueLabel laws) : blockDefect (plusBlockHom l).h1Map=(0,0) :=
  (blockDefect_eq_zero_iff_bijective _).mpr ⟨plus_block_injective l,plus_block_surjective l⟩
/-- 一ラベル minus の実欠損は (0,1)。 -/
theorem minus_block_defect (l : LawValueLabel laws) : blockDefect (minusBlockHom l).h1Map=(0,1) := by
  apply Prod.ext
  · rw [blockDefect_kernel_dimension]
    letI := minus_kernel_subsingleton l
    exact Module.finrank_zero_of_subsingleton
  · rw [blockDefect_cokernel_dimension,(minusBlockCokernel l).finrank_eq]
    exact Module.finrank_self ℚ
/-- 二ラベル全 Law plus の実欠損は (0,0)。 -/
theorem plus_law_defect : blockDefect plusLawHom.h1Map=(0,0) := by
  apply Prod.ext
  · rw [blockDefect_kernel_dimension]
    letI := plusLaw_kernel_subsingleton
    exact Module.finrank_zero_of_subsingleton
  · rw [blockDefect_cokernel_dimension]
    letI := plusLaw_cokernel_subsingleton
    exact Module.finrank_zero_of_subsingleton
/-- 二ラベル全 Law minus の実欠損は (0,2)。 -/
theorem minus_law_defect : blockDefect minusLawHom.h1Map=(0,2) := by
  apply Prod.ext
  · rw [blockDefect_kernel_dimension]
    letI := minusLaw_kernel_subsingleton
    exact Module.finrank_zero_of_subsingleton
  · rw [blockDefect_cokernel_dimension,minusLawCokernel.finrank_eq]
    simp only [Module.finrank_prod,Module.finrank_self]
/-- 粗全 Law H¹ の元ラベル別 k period。 -/
def oldLawPeriod := (lawH1FamilyEquiv N laws coarseAdequate).trans (LinearEquiv.piCongrRight oldBlockPeriod)
/-- plus 全 Law H¹ の元ラベル別 k period。 -/
def plusLawPeriod := (lawH1FamilyEquiv plus laws fineAdequate).trans (LinearEquiv.piCongrRight plusBlockPeriod)
/-- minus 全 Law H¹ の元ラベル別二 period。 -/
def minusLawPeriod := (lawH1FamilyEquiv minus laws fineAdequate).trans (LinearEquiv.piCongrRight minusBlockPeriod)
/-- 全 Law plus 実比較は二つの k period を個別に保持する。 -/
theorem plus_law_period_identity (x : (N.lawGeneratedComplex laws coarseAdequate).H1) :
    plusLawPeriod (plusLawHom.h1Map x)=oldLawPeriod x := by
  funext l
  simp only [plusLawPeriod,oldLawPeriod,LinearEquiv.trans_apply,LinearEquiv.piCongrRight_apply]
  exact (congrArg (plusBlockPeriod l) (rPlus.lawH1Family_natural laws coarseAdequate fineAdequate x l)).trans
    (plus_block_identity l _)
/-- 全 Law minus 実比較は各元ラベルで x→(x,0) になる。 -/
theorem minus_law_period_injection (x : (N.lawGeneratedComplex laws coarseAdequate).H1) (l : LawValueLabel laws) :
    minusLawPeriod (minusLawHom.h1Map x) l=(oldLawPeriod x l,0) := by
  simp only [minusLawPeriod,oldLawPeriod,LinearEquiv.trans_apply,LinearEquiv.piCongrRight_apply]
  exact (congrArg (minusBlockPeriod l) (rMinus.lawH1Family_natural laws coarseAdequate fineAdequate x l)).trans
    (minus_block_injection l _)
end AAT.AG.FaceRelationSubdivision.WitnessOne
#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision.WitnessOne
