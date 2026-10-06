import ResearchLean.AG.AtlasDefectComposition.ComparisonLaws
import ResearchLean.AG.AtlasDefectComposition.SubsetComparisonNaturality
import Formal.Util.AssertStandardAxioms
/-! # 部分集合の原始恒等比較と同じ生成手続き

Implementation notes: 全三成分を既存の chart/Option 評価式で照合する。
-/
noncomputable section
namespace AAT.AG.AtlasDefectComposition
open CanonicalResolution ResolutionInvariance
universe u
variable {Source : Type u} (q : Reading Source) (N : TargetSupportedNerve.{u,u} q)
/-- 自己 reading の指定比較因子は全 target 元で恒等である。 -/
theorem comparisonFactor_self : comparisonFactor q q (Reading.coarserThan_refl q) = id := by
  symm
  apply comparisonFactor_unique
  intro s
  rfl
/-- 同じ部分集合から生成した実恒等比較は三項複体の恒等射である。 -/
theorem identity_targetSubsetComparisonHom (A : Set q.Target)
    (hA : ∀ t, t ∈ A → comparisonFactor q q (Reading.coarserThan_refl q) t ∈ A) :
    (TargetSupportedNerveMorphism.identityMorphism q N).targetSubsetComparisonHom A A hA =
      cochainId (N.targetSubsetComplex A) := by
  apply cochain_ext
  · apply LinearMap.ext
    intro x
    funext c
    change (TargetSupportedNerveMorphism.identityMorphism q N).targetSubsetPullback0 A A hA x c = x c
    rw [TargetSupportedNerveMorphism.targetSubsetPullback0_apply]
    rfl
  · apply LinearMap.ext
    intro x
    funext c
    change (TargetSupportedNerveMorphism.identityMorphism q N).targetSubsetPullback1 A A hA x c = x c
    rw [TargetSupportedNerveMorphism.targetSubsetPullback1_apply,
      TargetSupportedNerveMorphism.targetSubsetEdgeMapOption_eq_some _ A A hA c c.1 rfl]
    rfl
  · apply LinearMap.ext
    intro x
    funext c
    change (TargetSupportedNerveMorphism.identityMorphism q N).targetSubsetPullback2 A A hA x c = x c
    rw [TargetSupportedNerveMorphism.targetSubsetPullback2_apply,
      TargetSupportedNerveMorphism.targetSubsetFaceMapOption_eq_some _ A A hA c c.1 rfl]
    rfl
end AAT.AG.AtlasDefectComposition
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition
