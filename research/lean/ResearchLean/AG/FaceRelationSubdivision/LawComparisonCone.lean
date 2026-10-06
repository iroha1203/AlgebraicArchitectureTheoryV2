import ResearchLean.AG.FaceRelationSubdivision.LawComparisonDecomposition
import ResearchLean.AG.FaceRelationSubdivision.LawFiberBridge
import ResearchLean.AG.AtlasDefectComposition.FiniteConeFamily

/-!
# 新混在比較の同じ標準錐を実ラベル錐へ分解する

## Implementation notes

同じ実射のLaw正方形をconeMapIsoへ渡す。元ラベルを保った族を直和にする。
対象同型だけから錐を選ぶ案は比較射と符号の接続を供給しないため採らない。
-/
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
namespace AAT.AG.FaceRelationSubdivision
open CanonicalResolution ResolutionInvariance TwoPhase AtlasDefectComposition
universe u
/-- 標準複体の有限積から、同じラベル族の有限直和を得る局所API。 -/
local instance lawComparisonConeFiniteBiproducts : HasFiniteBiproducts (CochainComplex (ModuleCat.{u} ℚ) ℤ) :=
  HasFiniteBiproducts.of_hasFiniteProducts
variable {Source : Type u} [Fintype Source]
variable {q r : Reading Source} {h : q.CoarserThan r}
variable (N : TargetSupportedNerve q) (E : TargetSupportedNerve r)
variable (laws : FiniteLawFamily Source) (ha : laws.Adequate q)
variable (M : IncidenceSupportedComparison q r h N E) (hr : laws.Adequate r)
/-- 全Law実比較の錐を、各発生ラベルの実比較錐の有限族へ同定する。 -/
def lawConeFamilyIso : mappingCone (zeroExtensionMap (M.generatedComparisonHom laws ha hr)) ≅
    FiniteComplexFamily.complex (fun l =>
      mappingCone (zeroExtensionMap (M.generatedBlockComparisonHom laws ha hr l))) :=
  coneMapIso _ _ (lawZeroExtensionIso N laws ha) (lawZeroExtensionIso E laws hr)
      (M.lawZeroExtension_square laws ha hr) ≪≫
    FiniteConeFamily.iso (fun l => zeroExtensionMap (M.generatedBlockComparisonHom laws ha hr l))
/-- 全Law標準錐は実ラベル錐の圏論的有限直和に同型である。 -/
def lawConeDirectSumIso : mappingCone (zeroExtensionMap (M.generatedComparisonHom laws ha hr)) ≅
    biproduct (fun l => mappingCone
      (zeroExtensionMap (M.generatedBlockComparisonHom laws ha hr l))) :=
  lawConeFamilyIso N E laws ha M hr ≪≫ FiniteComplexFamily.directSumIso _
/-- 全Law錐の全次数homologyは、重複を保持した全ラベル錐homology族である。 -/
def lawConeHomologyEquiv (m : ℤ) :
    (mappingCone (zeroExtensionMap (M.generatedComparisonHom laws ha hr))).homology m ≃ₗ[ℚ]
      ((l : LawValueLabel laws) →
        (mappingCone (zeroExtensionMap (M.generatedBlockComparisonHom laws ha hr l))).homology m) :=
  (homologyMapIso (lawConeFamilyIso N E laws ha M hr) m).toLinearEquiv.trans
    (FiniteComplexFamily.homologyEquiv _ m)
/-- 実Law錐族同型の順射の標準二段構成を読む公開API。 -/
@[simp] theorem lawConeFamilyIso_hom : (lawConeFamilyIso N E laws ha M hr).hom =
    (coneMapIso _ _ (lawZeroExtensionIso N laws ha) (lawZeroExtensionIso E laws hr)
      (M.lawZeroExtension_square laws ha hr)).hom ≫
        (FiniteConeFamily.iso (fun l => zeroExtensionMap
          (M.generatedBlockComparisonHom laws ha hr l))).hom := rfl
/-- 実Law錐homology族の各成分は同じ実錐族同型からのprojectionである。 -/
theorem lawConeHomologyEquiv_component_family (m : ℤ)
    (x : (mappingCone (zeroExtensionMap (M.generatedComparisonHom laws ha hr))).homology m)
    (l : LawValueLabel laws) : lawConeHomologyEquiv N E laws ha M hr m x l =
      homologyMap ((lawConeFamilyIso N E laws ha M hr).hom ≫
        FiniteComplexFamily.projection _ l) m x := by
  dsimp only [lawConeHomologyEquiv,LinearEquiv.trans_apply]
  rw [FiniteComplexFamily.homologyEquiv_component,homologyMap_comp]
  rfl
end AAT.AG.FaceRelationSubdivision
#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision
