import ResearchLean.AG.AtlasDefectComposition.LawProjection
import ResearchLean.AG.AtlasDefectComposition.UniqueComplexFamily
import ResearchLean.AG.AtlasDefectComposition.HomologyConjugation
import ResearchLean.AG.AtlasDefectComposition.ComplexIsoRanks
import Formal.Util.AssertStandardAxioms
/-! # 唯一の実Law blockから全Law対象への接続

Implementation notes: 唯一発生ラベルの場合に限り、全Law複体のprojectionを実同型へ強化する。この条件はW3の実入力から放電し、一般Law分解には課さない。
-/
noncomputable section
open CategoryTheory HomologicalComplex CochainComplex
namespace AAT.AG.AtlasDefectComposition
open CanonicalResolution ResolutionInvariance TwoPhase
universe u
variable {Source : Type u} [Fintype Source] {q r : Reading Source} {h : q.CoarserThan r}
variable (N : TargetSupportedNerve q) (E : TargetSupportedNerve r)
variable (laws : FiniteLawFamily Source) (ha : laws.Adequate q) [Subsingleton (LawValueLabel laws)]
variable (M : TargetSupportedNerveMorphism q r h N E) (hr : laws.Adequate r)
/-- 唯一の発生ラベルでは全Law実複体はその実block複体へ同型である。 -/
def lawUniqueBlockZeroExtensionIso (l : LawValueLabel laws) :
    zeroExtension (N.lawGeneratedComplex laws ha) ≅ zeroExtension (N.lawValueBlockComplex laws ha l) :=
  lawZeroExtensionIso N laws ha ≪≫ UniqueComplexFamily.iso _ l
/-- 唯一blockへの同型も同じ原始入力の実比較と可換である。 -/
theorem lawUniqueBlockZeroExtensionIso_natural (l : LawValueLabel laws) :
    zeroExtensionMap (M.generatedComparisonHom laws ha hr) ≫
      (lawUniqueBlockZeroExtensionIso E laws hr l).hom =
    (lawUniqueBlockZeroExtensionIso N laws ha l).hom ≫
      zeroExtensionMap (M.generatedBlockComparisonHom laws ha hr l) := by
  dsimp only [lawUniqueBlockZeroExtensionIso,Iso.trans_hom]
  rw [UniqueComplexFamily.iso_hom,UniqueComplexFamily.iso_hom]
  exact lawBlockZeroExtensionProjection_natural N E laws ha M hr l
/-- 唯一ラベルでは全Law標準錐を同じ実block標準錐へ同定する。 -/
def lawUniqueBlockConeIso (l : LawValueLabel laws) :
    mappingCone (zeroExtensionMap (M.generatedComparisonHom laws ha hr)) ≅
      mappingCone (zeroExtensionMap (M.generatedBlockComparisonHom laws ha hr l)) :=
  coneMapIso _ _ (lawUniqueBlockZeroExtensionIso N laws ha l)
    (lawUniqueBlockZeroExtensionIso E laws hr l)
      (lawUniqueBlockZeroExtensionIso_natural N E laws ha M hr l)
/-- 唯一blockと全Lawの標準homology欠損は全整数次数で等しい。 -/
theorem lawUniqueBlockStandardDefect (l : LawValueLabel laws) (m : ℤ) :
    blockDefect (homologyMap (zeroExtensionMap (M.generatedComparisonHom laws ha hr)) m).hom =
      blockDefect (homologyMap (zeroExtensionMap (M.generatedBlockComparisonHom laws ha hr l)) m).hom :=
  homologyConjugation_defect _ _ (lawUniqueBlockZeroExtensionIso N laws ha l)
    (lawUniqueBlockZeroExtensionIso E laws hr l)
      (lawUniqueBlockZeroExtensionIso_natural N E laws ha M hr l) m
/-- 唯一blockと全Lawの錐homology次元は全整数次数で等しい。 -/
theorem lawUniqueBlockConeHomology_dimension (l : LawValueLabel laws) (m : ℤ) :
    Module.finrank ℚ ((mappingCone (zeroExtensionMap (M.generatedComparisonHom laws ha hr))).homology m) =
      Module.finrank ℚ ((mappingCone (zeroExtensionMap
        (M.generatedBlockComparisonHom laws ha hr l))).homology m) :=
  (homologyMapIso (lawUniqueBlockConeIso N E laws ha M hr l) m).toLinearEquiv.finrank_eq
/-- 唯一blockと全Lawの錐次数別cochain次元も等しい。 -/
theorem lawUniqueBlockConeDegree_dimension (l : LawValueLabel laws) (m : ℤ) :
    Module.finrank ℚ ((mappingCone (zeroExtensionMap (M.generatedComparisonHom laws ha hr))).X m) =
      Module.finrank ℚ ((mappingCone (zeroExtensionMap
        (M.generatedBlockComparisonHom laws ha hr l))).X m) :=
  ((HomologicalComplex.eval _ _ m).mapIso
    (lawUniqueBlockConeIso N E laws ha M hr l)).toLinearEquiv.finrank_eq
/-- 唯一blockと全Lawの錐微分の実rankも全次数で等しい。 -/
theorem lawUniqueBlockCone_d_rank (l : LawValueLabel laws) (i j : ℤ) :
    Module.finrank ℚ (LinearMap.range
      ((mappingCone (zeroExtensionMap (M.generatedComparisonHom laws ha hr))).d i j).hom) =
    Module.finrank ℚ (LinearMap.range
      ((mappingCone (zeroExtensionMap (M.generatedBlockComparisonHom laws ha hr l))).d i j).hom) :=
  complexIso_d_rank (lawUniqueBlockConeIso N E laws ha M hr l) i j
end AAT.AG.AtlasDefectComposition
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition
