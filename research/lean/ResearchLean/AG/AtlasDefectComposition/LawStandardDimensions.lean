import ResearchLean.AG.AtlasDefectComposition.LawDefectDecomposition
import Formal.Util.AssertStandardAxioms
/-! # 全整数次数の実Law欠損の重複込み加法式

Implementation notes: 全次数で構成した実核・実余核の族同型から次元を加算する。同じ台の複数ラベルも添字として保持する。
-/
noncomputable section
open HomologicalComplex
namespace AAT.AG.AtlasDefectComposition
open CanonicalResolution ResolutionInvariance TwoPhase
universe u
variable {Source : Type u} [Fintype Source] {q r : Reading Source} {h : q.CoarserThan r}
variable (N : TargetSupportedNerve q) (E : TargetSupportedNerve r)
variable (laws : FiniteLawFamily Source) (ha : laws.Adequate q)
variable (M : TargetSupportedNerveMorphism q r h N E) (hr : laws.Adequate r)
/-- 全次数の二つの実Law欠損は全発生ラベルの実欠損の和である。 -/
theorem lawStandardDefect_sum (m : ℤ) :
    blockDefect (homologyMap (zeroExtensionMap (M.generatedComparisonHom laws ha hr)) m).hom =
      (∑ l, (blockDefect (homologyMap
        (zeroExtensionMap (M.generatedBlockComparisonHom laws ha hr l)) m).hom).1,
        ∑ l, (blockDefect (homologyMap
          (zeroExtensionMap (M.generatedBlockComparisonHom laws ha hr l)) m).hom).2) := by
  apply Prod.ext
  · simp only [blockDefect_kernel_dimension]
    rw [(lawStandardKernelFamilyEquiv N E laws ha M hr m).finrank_eq]
    exact Module.finrank_pi_fintype ℚ
  · simp only [blockDefect_cokernel_dimension]
    rw [(lawStandardCokernelFamilyEquiv N E laws ha M hr m).finrank_eq]
    exact Module.finrank_pi_fintype ℚ
end AAT.AG.AtlasDefectComposition
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition
