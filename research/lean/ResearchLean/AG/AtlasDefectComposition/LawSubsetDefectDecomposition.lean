import ResearchLean.AG.AtlasDefectComposition.LawFiberH1Family
import ResearchLean.AG.AtlasDefectComposition.GeneratedDefect
import ResearchLean.AG.AtlasDefectComposition.LawStandardDecomposition
import ResearchLean.AG.AtlasDefectComposition.FiniteDefectFamily
import ResearchLean.AG.AtlasDefectComposition.ComparisonHomology
import Formal.Util.AssertStandardAxioms
/-! # 実Law比較の核・余核・欠損の全ラベル分解

Implementation notes: 実Law商を各fiberの実商へ移し、canonical逆像への全三成分transportでJの加法式を同じA比較へ戻す。次元一致だけで対象同定を済ませない。
-/
noncomputable section
open CategoryTheory HomologicalComplex
namespace AAT.AG.AtlasDefectComposition
open CanonicalResolution ResolutionInvariance TwoPhase
universe u
variable {Source : Type u} [Fintype Source]
variable {q r : Reading Source} {h : q.CoarserThan r}
variable (N : TargetSupportedNerve q) (E : TargetSupportedNerve r)
variable (laws : FiniteLawFamily Source) (ha : laws.Adequate q)
variable (M : TargetSupportedNerveMorphism q r h N E) (hr : laws.Adequate r)
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
  rw [LinearConjugation.cokernelEquiv_mk,FiniteLinearFamily.cokernelEquiv_mk]
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
  rw [lawFiberComparison_canonical] at ht
  exact ht.symm
/-- 全Law欠損は、同じ粗fiberとその逆像の実部分集合欠損の和である。 -/
theorem lawH1Defect_subset_sum : blockDefect (M.generatedComparisonH1Map laws ha hr) =
    (∑ l, (blockDefect (M.aSubnerveComparisonHom (labelValueFiber laws q ha l)).h1Map).1,
      ∑ l, (blockDefect (M.aSubnerveComparisonHom (labelValueFiber laws q ha l)).h1Map).2) := by
  rw [lawFiberH1Defect_sum]
  simp only [lawFiberDefect_canonical]
end AAT.AG.AtlasDefectComposition
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition
