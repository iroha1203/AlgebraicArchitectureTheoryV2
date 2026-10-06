import ResearchLean.AG.FaceRelationSubdivision.SubsetRestriction

/-!
# 新混在比較と両readingでの同じ支持制限

## Implementation notes

原始セル像が支持包含の前後で同じ名前であることを検証する。
readingが異なる場合も、両subsetの因子適合だけを使用して直接生成射へ接続する。
-/
noncomputable section
open CategoryTheory
namespace AAT.AG.FaceRelationSubdivision
open CanonicalResolution ResolutionInvariance TwoPhase AtlasDefectComposition
universe u
variable {Source : Type u} {qc qf : Reading Source} {h : qc.CoarserThan qf}
variable {Nc : TargetSupportedNerve qc} {Nf : TargetSupportedNerve qf}
namespace IncidenceSupportedComparison
variable (M : IncidenceSupportedComparison qc qf h Nc Nf)
variable (Ac Bc : Set qc.Target) (Af Bf : Set qf.Target)
variable (hc : Ac ⊆ Bc) (hf : Af ⊆ Bf)
variable (hsA : ∀ t, t ∈ Af → comparisonFactor qc qf h t ∈ Ac)
variable (hsB : ∀ t, t ∈ Bf → comparisonFactor qc qf h t ∈ Bc)

/-- 同じ原始chart輸送の実生成射は支持制限と可換。 -/
theorem restrict_pullback0 (z : Nc.ChartInTargetSubset Bc → ℚ) :
    selectedRestrict Nf.chartSupport hf (M.targetSubsetPullback0 Bc Bf hsB z) =
      M.targetSubsetPullback0 Ac Af hsA (selectedRestrict Nc.chartSupport hc z) := by
  funext x
  rw [selectedRestrict_apply, M.targetSubsetPullback0_apply,
    M.targetSubsetPullback0_apply, selectedRestrict_apply]
  apply congrArg z
  apply Subtype.ext
  rw [M.targetSubsetChartMap_val, M.targetSubsetChartMap_val]

/-- 退化を含む同じ原始辺輸送の実生成射は支持制限と可換。 -/
theorem restrict_pullback1 (z : Nc.EdgeInTargetSubset Bc → ℚ) :
    selectedRestrict Nf.edgeSupport hf (M.targetSubsetPullback1 Bc Bf hsB z) =
      M.targetSubsetPullback1 Ac Af hsA (selectedRestrict Nc.edgeSupport hc z) := by
  funext x
  rw [selectedRestrict_apply, M.targetSubsetPullback1_apply, M.targetSubsetPullback1_apply]
  cases hm : M.edgeMap x.val with
  | none =>
    rw [M.targetSubsetEdgeMapOption_eq_none Bc Bf hsB _ hm,
      M.targetSubsetEdgeMapOption_eq_none Ac Af hsA _ hm]
    rfl
  | some e =>
    rw [M.targetSubsetEdgeMapOption_eq_some Bc Bf hsB _ e hm,
      M.targetSubsetEdgeMapOption_eq_some Ac Af hsA _ e hm]
    simp only [Option.elim_some]
    rw [selectedRestrict_apply]
    apply congrArg z
    apply Subtype.ext
    rw [M.targetSubsetEdgeMap_val, M.targetSubsetEdgeMap_val]

/-- 退化を含む同じ原始面輸送の実生成射は支持制限と可換。 -/
theorem restrict_pullback2 (z : Nc.FaceInTargetSubset Bc → ℚ) :
    selectedRestrict Nf.faceSupport hf (M.targetSubsetPullback2 Bc Bf hsB z) =
      M.targetSubsetPullback2 Ac Af hsA (selectedRestrict Nc.faceSupport hc z) := by
  funext x
  rw [selectedRestrict_apply, M.targetSubsetPullback2_apply, M.targetSubsetPullback2_apply]
  cases hm : M.faceMap x.val with
  | none =>
    rw [M.targetSubsetFaceMapOption_eq_none Bc Bf hsB _ hm,
      M.targetSubsetFaceMapOption_eq_none Ac Af hsA _ hm]
    rfl
  | some f =>
    rw [M.targetSubsetFaceMapOption_eq_some Bc Bf hsB _ f hm,
      M.targetSubsetFaceMapOption_eq_some Ac Af hsA _ f hm]
    simp only [Option.elim_some]
    rw [selectedRestrict_apply]
    apply congrArg z
    apply Subtype.ext
    rw [M.targetSubsetFaceMap_val, M.targetSubsetFaceMap_val]

/-- 原始混在比較の同じ三成分Homは両支持制限と可換。 -/
theorem subset_restrict_square :
    cochainComp (M.targetSubsetComparisonHom Bc Bf hsB) (subsetRestrictHom Nf hf) =
      cochainComp (subsetRestrictHom Nc hc) (M.targetSubsetComparisonHom Ac Af hsA) := by
  apply cochain_ext
  · apply LinearMap.ext; intro z
    rw [cochainComp_f0, cochainComp_f0, targetSubsetComparisonHom_f0,
      targetSubsetComparisonHom_f0, subsetRestrictHom_f0, subsetRestrictHom_f0]
    exact M.restrict_pullback0 Ac Bc Af Bf hc hf hsA hsB z
  · apply LinearMap.ext; intro z
    rw [cochainComp_f1, cochainComp_f1, targetSubsetComparisonHom_f1,
      targetSubsetComparisonHom_f1, subsetRestrictHom_f1, subsetRestrictHom_f1]
    exact M.restrict_pullback1 Ac Bc Af Bf hc hf hsA hsB z
  · apply LinearMap.ext; intro z
    rw [cochainComp_f2, cochainComp_f2, targetSubsetComparisonHom_f2,
      targetSubsetComparisonHom_f2, subsetRestrictHom_f2, subsetRestrictHom_f2]
    exact M.restrict_pullback2 Ac Bc Af Bf hc hf hsA hsB z

/-- 同じ混在比較と支持制限は既存H1商でも可換。 -/
theorem subset_restrict_h1_square :
    (subsetRestrictHom Nf hf).h1Map.comp (M.targetSubsetComparisonHom Bc Bf hsB).h1Map =
      (M.targetSubsetComparisonHom Ac Af hsA).h1Map.comp (subsetRestrictHom Nc hc).h1Map := by
  have hn := congrArg ThreeCochainComplex.Hom.h1Map
    (M.subset_restrict_square Ac Bc Af Bf hc hf hsA hsB)
  simpa only [cochainComp_h1Map] using hn

end IncidenceSupportedComparison
end AAT.AG.FaceRelationSubdivision
#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision
