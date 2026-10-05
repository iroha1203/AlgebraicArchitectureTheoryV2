import ResearchLean.AG.AtlasDefectComposition.LawConeDecomposition
import ResearchLean.AG.AtlasDefectComposition.LawFiberDecomposition
import Formal.Util.AssertStandardAxioms
/-! # 全Lawの標準錐を同じ粗fiber・逆像の実錐へ分解する

Implementation notes: 各実block錐の同型を同じ粗fiberとcanonical逆像の錐へ合成する。元の発生ラベルの重複度を保持した有限族から圏論的直和を得る。
-/
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
namespace AAT.AG.AtlasDefectComposition
open CanonicalResolution ResolutionInvariance TwoPhase
universe u
local instance lawSubsetConeFiniteBiproducts : HasFiniteBiproducts (CochainComplex (ModuleCat.{u} ℚ) ℤ) :=
  HasFiniteBiproducts.of_hasFiniteProducts
variable {Source : Type u} [Fintype Source]
variable {q r : Reading Source} {h : q.CoarserThan r}
variable (N : TargetSupportedNerve q) (E : TargetSupportedNerve r)
variable (laws : FiniteLawFamily Source) (ha : laws.Adequate q)
variable (M : TargetSupportedNerveMorphism q r h N E) (hr : laws.Adequate r)
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
end AAT.AG.AtlasDefectComposition
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition
