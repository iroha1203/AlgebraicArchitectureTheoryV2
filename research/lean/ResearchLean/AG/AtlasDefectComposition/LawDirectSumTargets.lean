import ResearchLean.AG.AtlasDefectComposition.LawSubsetDefectDecomposition
import ResearchLean.AG.AtlasDefectComposition.LawSubsetConeDecomposition
import ResearchLean.AG.AtlasDefectComposition.LawSixTermDecomposition
import Formal.Util.AssertStandardAxioms
/-! # 実Law対象と実欠損を有限直和表示へ戻す

Implementation notes: 有限族の関数表示を既存の有限直和線形同型で移す。
全発生ラベルを残して各元の成分を保存し、同じ台を持つラベルも集合へ圧縮しない。
-/
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace AAT.AG.AtlasDefectComposition
open CanonicalResolution ResolutionInvariance TwoPhase
universe u
local instance lawDirectSumFiniteBiproducts : HasFiniteBiproducts (CochainComplex (ModuleCat.{u} ℚ) ℤ) :=
  HasFiniteBiproducts.of_hasFiniteProducts
variable {Source : Type u} [Fintype Source] {q r : Reading Source} {h : q.CoarserThan r}
variable (N : TargetSupportedNerve q) (E : TargetSupportedNerve r)
variable (laws : FiniteLawFamily Source) (ha : laws.Adequate q)
variable (M : TargetSupportedNerveMorphism q r h N E) (hr : laws.Adequate r)
/-- 全Law実零延長は同じ全ラベルblock零延長の圏論的有限直和である。 -/
def lawZeroExtensionDirectSumIso : zeroExtension (N.lawGeneratedComplex laws ha) ≅
    biproduct (fun l => zeroExtension (N.lawValueBlockComplex laws ha l)) :=
  lawZeroExtensionIso N laws ha ≪≫ FiniteComplexFamily.directSumIso _
/-- 圏論的直和同型も各独立生成blockのbiproduct比較と可換である。 -/
theorem lawZeroExtensionDirectSumIso_natural :
    zeroExtensionMap (M.generatedComparisonHom laws ha hr) ≫
      (lawZeroExtensionDirectSumIso E laws hr).hom =
    (lawZeroExtensionDirectSumIso N laws ha).hom ≫
      biproduct.map (fun l => zeroExtensionMap (M.generatedBlockComparisonHom laws ha hr l)) := by
  dsimp only [lawZeroExtensionDirectSumIso,Iso.trans_hom]
  rw [← Category.assoc,lawZeroExtensionIso_natural,Category.assoc,
    FiniteComplexFamily.directSumIso_natural]
  simp only [Category.assoc]
/-- 全Law既存実H¹比較の核の有限直和表示。 -/
def lawH1KernelDirectSumEquiv : LinearMap.ker (M.generatedComparisonH1Map laws ha hr) ≃ₗ[ℚ]
    DirectSum (LawValueLabel laws) (fun l => LinearMap.ker (M.generatedBlockComparisonH1Map laws ha hr l)) :=
  (lawH1KernelFamilyEquiv N E laws ha M hr).trans
    (DirectSum.linearEquivFunOnFintype ℚ (LawValueLabel laws) _).symm
/-- 全Law既存実H¹比較の余核の有限直和表示。 -/
def lawH1CokernelDirectSumEquiv :
    ((E.lawGeneratedComplex laws hr).H1 ⧸ LinearMap.range (M.generatedComparisonH1Map laws ha hr)) ≃ₗ[ℚ]
    DirectSum (LawValueLabel laws) (fun l => (E.lawValueBlockComplex laws hr l).H1 ⧸
      LinearMap.range (M.generatedBlockComparisonH1Map laws ha hr l)) :=
  (lawH1CokernelFamilyEquiv N E laws ha M hr).trans
    (DirectSum.linearEquivFunOnFintype ℚ (LawValueLabel laws) _).symm
/-- 全整数次数で実Law標準homology比較の核の有限直和表示。 -/
def lawStandardKernelDirectSumEquiv (m : ℤ) :
    LinearMap.ker (homologyMap (zeroExtensionMap (M.generatedComparisonHom laws ha hr)) m).hom ≃ₗ[ℚ]
    DirectSum (LawValueLabel laws) (fun l => LinearMap.ker
      (homologyMap (zeroExtensionMap (M.generatedBlockComparisonHom laws ha hr l)) m).hom) :=
  (lawStandardKernelFamilyEquiv N E laws ha M hr m).trans
    (DirectSum.linearEquivFunOnFintype ℚ (LawValueLabel laws) _).symm
/-- 全整数次数で実Law標準homology比較の余核の有限直和表示。 -/
def lawStandardCokernelDirectSumEquiv (m : ℤ) :
    ((zeroExtension (E.lawGeneratedComplex laws hr)).homology m ⧸ LinearMap.range
      (homologyMap (zeroExtensionMap (M.generatedComparisonHom laws ha hr)) m).hom) ≃ₗ[ℚ]
    DirectSum (LawValueLabel laws) (fun l => (zeroExtension (E.lawValueBlockComplex laws hr l)).homology m ⧸
      LinearMap.range (homologyMap (zeroExtensionMap (M.generatedBlockComparisonHom laws ha hr l)) m).hom) :=
  (lawStandardCokernelFamilyEquiv N E laws ha M hr m).trans
    (DirectSum.linearEquivFunOnFintype ℚ (LawValueLabel laws) _).symm
end AAT.AG.AtlasDefectComposition
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition
