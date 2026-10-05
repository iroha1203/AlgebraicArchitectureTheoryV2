import ResearchLean.AG.AtlasDefectComposition.LawDefectDecomposition
import ResearchLean.AG.AtlasDefectComposition.LawFiberDecomposition
import Formal.Util.AssertStandardAxioms
/-! # 全Law既存H¹を同じ各原始fiber比較へ読む

Implementation notes: G-104の全Law既存商の同値とG-107の各fiber既存商の同値を合成する。実比較の自然性は同じ二つの既存APIから導く。
-/
noncomputable section
namespace AAT.AG.AtlasDefectComposition
open CanonicalResolution ResolutionInvariance TwoPhase
universe u
variable {Source : Type u} [Fintype Source]
variable {q r : Reading Source} {h : q.CoarserThan r}
variable (N : TargetSupportedNerve q) (E : TargetSupportedNerve r)
variable (laws : FiniteLawFamily Source) (ha : laws.Adequate q)
variable (M : TargetSupportedNerveMorphism q r h N E) (hr : laws.Adequate r)
/-- 既存実H¹を全発生ラベルの同じ粗fiber複体の既存実H¹族へ同定する。 -/
def lawFiberH1FamilyEquiv : (N.lawGeneratedComplex laws ha).H1 ≃ₗ[ℚ]
    ((l : LawValueLabel laws) → (N.targetSubsetComplex (labelValueFiber laws q ha l)).H1) :=
  (lawH1FamilyEquiv N laws ha).trans (LinearEquiv.piCongrRight fun l =>
    (N.lawValueBlockTargetSubsetComplexEquiv laws ha l).h1Equiv)
/-- 全Law既存H¹の実比較は同じ粗fiber・細fiberの各独立生成実比較と可換である。 -/
theorem lawFiberH1Comparison_square (x : (N.lawGeneratedComplex laws ha).H1) :
    lawFiberH1FamilyEquiv E laws hr (M.generatedComparisonH1Map laws ha hr x) =
      FiniteLinearFamily.map (fun l => (M.labelFiberComparisonHom laws ha hr l).h1Map)
        (lawFiberH1FamilyEquiv N laws ha x) := by
  funext l
  change (E.lawValueBlockTargetSubsetComplexEquiv laws hr l).h1Equiv
    (lawH1FamilyEquiv E laws hr (M.generatedComparisonH1Map laws ha hr x) l) =
      (M.labelFiberComparisonHom laws ha hr l).h1Map
        ((N.lawValueBlockTargetSubsetComplexEquiv laws ha l).h1Equiv
          (lawH1FamilyEquiv N laws ha x l))
  rw [lawH1FamilyMap_component]
  exact M.labelFiberComparison_h1_naturality laws ha hr l _
end AAT.AG.AtlasDefectComposition
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition
