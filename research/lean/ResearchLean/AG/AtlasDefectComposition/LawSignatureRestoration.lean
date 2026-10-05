import ResearchLean.AG.AtlasDefectComposition.SelectedFamilyReconstruction
import ResearchLean.AG.AtlasDefectComposition.LawSubsetConeDecomposition
import Formal.Util.AssertStandardAxioms
/-! # 実 Law から重複度付き署名による錐復元へ

Implementation notes: 発生 Law・値ラベルと元の粗 fiber を selected 族へ送る。
D の全 Law 錐分解を通し、零性・再添字・元を固定した block 同型だけで復元する。
-/
noncomputable section
open CategoryTheory CochainComplex
namespace AAT.AG.AtlasDefectComposition
open CanonicalResolution ResolutionInvariance TwoPhase SelectedFamilies
universe u
variable {Source : Type u} [Fintype Source] {q r : Reading Source} {h : q.CoarserThan r}
variable (N : TargetSupportedNerve.{u,u} q) (E : TargetSupportedNerve.{u,u} r)
variable (laws : FiniteLawFamily Source) (ha : laws.Adequate q)
/-- 実 Law の全発生ラベルを保持した元の粗 fiber 族。 -/
def lawSelectedFamily : Family (SupportSignature.family N E h) where
  Index := LawValueLabel laws
  finite := inferInstance
  subset := labelValueFiber laws q ha
variable (M : TargetSupportedNerveMorphism q r h N E) (hr : laws.Adequate r)
/-- 全実 Law 錐を同じ粗 fiber 族の実比較錐へ接続する。 -/
def lawSelectedComparisonConeIso : mappingCone (zeroExtensionMap (M.generatedComparisonHom laws ha hr)) ≅
    mappingCone (SelectedFamilyComplex.comparison N E h (lawSelectedFamily N E laws ha) M) :=
  lawSubsetConeFamilyIso N E laws ha M hr ≪≫
    (FiniteConeFamily.iso (SelectedFamilyComplex.comparisonBlock N E h (lawSelectedFamily N E laws ha) M)).symm
/-- 全実 Law の錐は全セル署名の重複度付き canonical 族から復元する。 -/
def lawMultiplicityConeIso : mappingCone (zeroExtensionMap (M.generatedComparisonHom laws ha hr)) ≅
    mappingCone (SelectedFamilyComplex.comparison N E h
      (canonicalFamily (SupportSignature.family N E h)
        (multiplicity (SupportSignature.family N E h) (lawSelectedFamily N E laws ha))) M) :=
  lawSelectedComparisonConeIso N E laws ha M hr ≪≫
    SelectedFamilyComplex.canonicalConeIso N E h M (lawSelectedFamily N E laws ha)
/-- 全整数次数の Law 錐 homology も同じ重複度から復元する。 -/
def lawMultiplicityConeHomologyEquiv (m : ℤ) :=
  (HomologicalComplex.homologyMapIso (lawMultiplicityConeIso N E laws ha M hr) m).toLinearEquiv
end AAT.AG.AtlasDefectComposition
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition
