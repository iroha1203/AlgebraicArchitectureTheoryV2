import ResearchLean.AG.FaceRelationSubdivision.LawComparisonDefect
import ResearchLean.AG.FaceRelationSubdivision.LawComparisonCone
import ResearchLean.AG.AtlasDefectComposition.LawFiberH1Family
import ResearchLean.AG.AtlasDefectComposition.GeneratedDefect

/-!
# 同じ新比較の実Law診断を原始fiber比較へ読む

## Implementation notes

block/fiberの実三成分正方形から旧H1と標準錐の同型を導く。
数値の和だけを先に置く案は同じ原始fiber射への接続を隠すため採らない。
-/
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
namespace AAT.AG.FaceRelationSubdivision
open CanonicalResolution ResolutionInvariance TwoPhase AtlasDefectComposition
universe u
/-- 標準複体の有限積から、同じラベル族の有限直和を得る局所API。 -/
local instance lawComparisonFiberFiniteBiproducts : HasFiniteBiproducts (CochainComplex (ModuleCat.{u} ℚ) ℤ) :=
  HasFiniteBiproducts.of_hasFiniteProducts
variable {Source : Type u} [Fintype Source]
variable {q r : Reading Source} {h : q.CoarserThan r}
variable (N : TargetSupportedNerve q) (E : TargetSupportedNerve r)
variable (laws : FiniteLawFamily Source) (ha : laws.Adequate q)
variable (M : IncidenceSupportedComparison q r h N E) (hr : laws.Adequate r)

/-- 新比較の同じblock/fiber次数1正方形を既存商へ降ろす。 -/
theorem labelFiberH1_natural (l : LawValueLabel laws)
    (x : (N.lawValueBlockComplex laws ha l).H1) :
    (E.lawValueBlockTargetSubsetComplexEquiv laws hr l).h1Equiv
        ((M.generatedBlockComparisonHom laws ha hr l).h1Map x) =
      (M.labelFiberComparisonHom laws ha hr l).h1Map
        ((N.lawValueBlockTargetSubsetComplexEquiv laws ha l).h1Equiv x) :=
  ThreeCochainComplex.CochainEquiv.h1Equiv_naturality_apply
    (N.lawValueBlockTargetSubsetComplexEquiv laws ha l)
    (E.lawValueBlockTargetSubsetComplexEquiv laws hr l)
    (M.generatedBlockComparisonHom laws ha hr l) (M.labelFiberComparisonHom laws ha hr l)
    (M.labelFiberComparison_naturality1 laws ha hr l) x

/-- 新比較の同じ全Law既存H1は原始各fiber射と可換。 -/
theorem lawFiberH1Comparison_square (x : (N.lawGeneratedComplex laws ha).H1) :
    lawFiberH1FamilyEquiv E laws hr (M.generatedComparisonH1Map laws ha hr x) =
      FiniteLinearFamily.map (fun l => (M.labelFiberComparisonHom laws ha hr l).h1Map)
        (lawFiberH1FamilyEquiv N laws ha x) := by
  funext l
  rw [FiniteLinearFamily.map_apply, lawFiberH1FamilyEquiv_apply, lawFiberH1FamilyEquiv_apply]
  exact (congrArg (E.lawValueBlockTargetSubsetComplexEquiv laws hr l).h1Equiv
    (M.lawH1Family_natural laws ha hr x l)).trans
      (labelFiberH1_natural N E laws ha M hr l _)

/-- 全Law既存実H¹比較の核を、全発生ラベルの実核へ同定する。 -/
def lawFiberH1KernelFamilyEquiv : LinearMap.ker (M.generatedComparisonH1Map laws ha hr) ≃ₗ[ℚ]
    ((l : LawValueLabel laws) → LinearMap.ker ((M.labelFiberComparisonHom laws ha hr l).h1Map)) :=
  (LinearConjugation.kernelEquiv _ _ (lawFiberH1FamilyEquiv N laws ha)
    (lawFiberH1FamilyEquiv E laws hr) (lawFiberH1Comparison_square N E laws ha M hr)).trans
      (FiniteLinearFamily.kernelEquiv _)
/-- 全Law既存実H¹比較の余核を、全発生ラベルの実余核へ同定する。 -/
def lawFiberH1CokernelFamilyEquiv :
    ((E.lawGeneratedComplex laws hr).H1 ⧸ LinearMap.range (M.generatedComparisonH1Map laws ha hr)) ≃ₗ[ℚ]
      ((l : LawValueLabel laws) → (E.targetSubsetComplex (labelValueFiber laws r hr l)).H1 ⧸
        LinearMap.range ((M.labelFiberComparisonHom laws ha hr l).h1Map)) :=
  (LinearConjugation.cokernelEquiv _ _ (lawFiberH1FamilyEquiv N laws ha)
    (lawFiberH1FamilyEquiv E laws hr) (lawFiberH1Comparison_square N E laws ha M hr)).trans
      (FiniteLinearFamily.cokernelEquiv _)
/-- 核同定は同じ実H¹の各ラベル成分を読む。 -/
@[simp] theorem lawFiberH1KernelFamilyEquiv_val
    (x : LinearMap.ker (M.generatedComparisonH1Map laws ha hr)) (l : LawValueLabel laws) :
    (lawFiberH1KernelFamilyEquiv N E laws ha M hr x l).val =
      lawFiberH1FamilyEquiv N laws ha x.val l := rfl
/-- 余核同定は同じ実H¹代表元の各ラベル商類を読む。 -/
@[simp] theorem lawFiberH1CokernelFamilyEquiv_mk (x : (E.lawGeneratedComplex laws hr).H1)
    (l : LawValueLabel laws) : lawFiberH1CokernelFamilyEquiv N E laws ha M hr
      ((LinearMap.range (M.generatedComparisonH1Map laws ha hr)).mkQ x) l =
        (LinearMap.range ((M.labelFiberComparisonHom laws ha hr l).h1Map)).mkQ
          (lawFiberH1FamilyEquiv E laws hr x l) := by
  dsimp only [lawFiberH1CokernelFamilyEquiv,LinearEquiv.trans_apply]
  rw [LinearConjugation.cokernelEquiv_mk,
    FiniteLinearFamily.cokernelEquiv_mk]
/-- 二つのLaw欠損は、全発生ラベルを重複込みで足した値である。 -/
theorem lawFiberH1Defect_sum : blockDefect (M.generatedComparisonH1Map laws ha hr) =
    (∑ l, (blockDefect ((M.labelFiberComparisonHom laws ha hr l).h1Map)).1,
      ∑ l, (blockDefect ((M.labelFiberComparisonHom laws ha hr l).h1Map)).2) := by
  apply Prod.ext
  · simp only [blockDefect_kernel_dimension]
    rw [(lawFiberH1KernelFamilyEquiv N E laws ha M hr).finrank_eq]
    exact Module.finrank_pi_fintype ℚ
  · simp only [blockDefect_cokernel_dimension]
    rw [(lawFiberH1CokernelFamilyEquiv N E laws ha M hr).finrank_eq]
    exact Module.finrank_pi_fintype ℚ
/-- 細fiberのcanonical逆像への全三成分移送は実H¹欠損を保つ。 -/
theorem lawFiberDefect_canonical (l : LawValueLabel laws) :
    blockDefect (M.labelFiberComparisonHom laws ha hr l).h1Map =
      blockDefect (M.aSubnerveComparisonHom (labelValueFiber laws q ha l)).h1Map := by
  have ht := transportHom_defect (congrArg E.targetSubsetComplex
    (labelValueFiber_eq_preimage laws q r ha hr h l)) (M.labelFiberComparisonHom laws ha hr l)
  rw [← subsetTransportHom_eq_transportHom, lawFiberComparison_canonical] at ht
  exact ht.symm
/-- 全Law欠損は、同じ粗fiberとその逆像の実部分集合欠損の和である。 -/
theorem lawH1Defect_subset_sum : blockDefect (M.generatedComparisonH1Map laws ha hr) =
    (∑ l, (blockDefect (M.aSubnerveComparisonHom (labelValueFiber laws q ha l)).h1Map).1,
      ∑ l, (blockDefect (M.aSubnerveComparisonHom (labelValueFiber laws q ha l)).h1Map).2) := by
  rw [lawFiberH1Defect_sum]
  simp only [lawFiberDefect_canonical]
/-- 各発生ラベルの同じ粗fiberとcanonical逆像の実錐族への同型。 -/
def lawSubsetConeFamilyIso : mappingCone (zeroExtensionMap (M.generatedComparisonHom laws ha hr)) ≅
    FiniteComplexFamily.complex (fun l => mappingCone (zeroExtensionMap
      (M.aSubnerveComparisonHom (labelValueFiber laws q ha l)))) :=
  lawConeFamilyIso N E laws ha M hr ≪≫
    FiniteComplexFamily.iso _ _ (fun l => lawBlockCanonicalConeIso N E laws ha M hr l)
/-- 全Lawの実錐は、重複を保持した各粗fiber・逆像錐の有限直和である。 -/
def lawSubsetConeDirectSumIso : mappingCone (zeroExtensionMap (M.generatedComparisonHom laws ha hr)) ≅
    biproduct (fun l => mappingCone (zeroExtensionMap
      (M.aSubnerveComparisonHom (labelValueFiber laws q ha l)))) :=
  lawSubsetConeFamilyIso N E laws ha M hr ≪≫ FiniteComplexFamily.directSumIso _
/-- 全整数次数で、全Law錐homologyと同じ各粗fiber・逆像錐homologyを同定する。 -/
def lawSubsetConeHomologyEquiv (m : ℤ) :
    (mappingCone (zeroExtensionMap (M.generatedComparisonHom laws ha hr))).homology m ≃ₗ[ℚ]
      ((l : LawValueLabel laws) → (mappingCone (zeroExtensionMap
        (M.aSubnerveComparisonHom (labelValueFiber laws q ha l)))).homology m) :=
  (homologyMapIso (lawSubsetConeFamilyIso N E laws ha M hr) m).toLinearEquiv.trans
    (FiniteComplexFamily.homologyEquiv _ m)
/-- 錐の全次数の寄与も各発生ラベルの実部分集合寄与の和である。 -/
theorem lawSubsetConeHomology_dimension (m : ℤ) :
    Module.finrank ℚ ((mappingCone (zeroExtensionMap (M.generatedComparisonHom laws ha hr))).homology m) =
      ∑ l, Module.finrank ℚ ((mappingCone (zeroExtensionMap
        (M.aSubnerveComparisonHom (labelValueFiber laws q ha l)))).homology m) := by
  rw [(lawSubsetConeHomologyEquiv N E laws ha M hr m).finrank_eq]
  exact Module.finrank_pi_fintype ℚ
end AAT.AG.FaceRelationSubdivision
#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision
