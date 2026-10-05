import ResearchLean.AG.AtlasDefectComposition.SubsetEquivalence
import ResearchLean.AG.AtlasDefectComposition.ConeEquivalence
import Formal.Util.AssertStandardAxioms
/-! # 全セル署名の包含と実比較の自然性

Implementation notes: 署名包含を両側の全選択セル包含へ評価する。
chart の像と edge・face の Option 宣言を同じ原始比較から読み、
実三項比較と台制限の可換正方形を証明する。
-/
noncomputable section
namespace AAT.AG.AtlasDefectComposition.SupportRestriction
open CanonicalResolution ResolutionInvariance TwoPhase CategoryTheory
universe u
variable {Source : Type u} {q r : Reading Source}
variable (N : TargetSupportedNerve q) (E : TargetSupportedNerve r) (h : q.CoarserThan r)
variable {A B : Set q.Target} (hab : SupportSignature.alpha N E h A ⊆ SupportSignature.alpha N E h B)
/-- 全六種類の署名包含から粗側全三次数の実選択包含を導く。 -/
def coarseLE : SubsetRestriction.SelectedLE N A B := by
  refine ⟨?_,?_,?_⟩
  · intro c hc
    exact (SupportSignature.mem_alpha_coarseChart N E h B c).mp
      (hab ((SupportSignature.mem_alpha_coarseChart N E h A c).mpr hc))
  · intro c hc
    exact (SupportSignature.mem_alpha_coarseEdge N E h B c).mp
      (hab ((SupportSignature.mem_alpha_coarseEdge N E h A c).mpr hc))
  · intro c hc
    exact (SupportSignature.mem_alpha_coarseFace N E h B c).mp
      (hab ((SupportSignature.mem_alpha_coarseFace N E h A c).mpr hc))
/-- 全六種類の署名包含から細側逆像の全三次数の実選択包含を導く。 -/
def fineLE : SubsetRestriction.SelectedLE E
    (comparisonFactor q r h ⁻¹' A) (comparisonFactor q r h ⁻¹' B) := by
  refine ⟨?_,?_,?_⟩
  · intro c hc
    exact (SupportSignature.mem_alpha_fineChart N E h B c).mp
      (hab ((SupportSignature.mem_alpha_fineChart N E h A c).mpr hc))
  · intro c hc
    exact (SupportSignature.mem_alpha_fineEdge N E h B c).mp
      (hab ((SupportSignature.mem_alpha_fineEdge N E h A c).mpr hc))
  · intro c hc
    exact (SupportSignature.mem_alpha_fineFace N E h B c).mp
      (hab ((SupportSignature.mem_alpha_fineFace N E h A c).mpr hc))
variable (M : TargetSupportedNerveMorphism q r h N E)
/-- chart の実比較と両側選択包含は元のセルを固定して可換する。 -/
theorem chart_square (c : E.ChartInTargetSubset (comparisonFactor q r h ⁻¹' A)) :
    SubsetRestriction.chartInclusion N (coarseLE N E h hab)
      (M.targetSubsetChartMap A (comparisonFactor q r h ⁻¹' A) (fun _ ht => ht) c) =
    M.targetSubsetChartMap B (comparisonFactor q r h ⁻¹' B) (fun _ ht => ht)
      (SubsetRestriction.chartInclusion E (fineLE N E h hab) c) := by
  apply Subtype.ext
  rfl
/-- edge の実 Option 比較は両側セル包含と可換し、none も保持する。 -/
theorem edge_option_square (c : E.EdgeInTargetSubset (comparisonFactor q r h ⁻¹' A)) :
    Option.map (SubsetRestriction.edgeInclusion N (coarseLE N E h hab))
      (M.targetSubsetEdgeMapOption A (comparisonFactor q r h ⁻¹' A) (fun _ ht => ht) c) =
    M.targetSubsetEdgeMapOption B (comparisonFactor q r h ⁻¹' B) (fun _ ht => ht)
      (SubsetRestriction.edgeInclusion E (fineLE N E h hab) c) := by
  cases hm : M.edgeMap c.1 with
  | none =>
    rw [M.targetSubsetEdgeMapOption_eq_none A _ _ c hm,
      M.targetSubsetEdgeMapOption_eq_none B (comparisonFactor q r h ⁻¹' B) (fun _ ht => ht)
        (SubsetRestriction.edgeInclusion E (fineLE N E h hab) c) hm]
    rfl
  | some d =>
    rw [M.targetSubsetEdgeMapOption_eq_some A _ _ c d hm,
      M.targetSubsetEdgeMapOption_eq_some B (comparisonFactor q r h ⁻¹' B) (fun _ ht => ht)
        (SubsetRestriction.edgeInclusion E (fineLE N E h hab) c) d hm]
    rfl
/-- face の実 Option 比較は両側セル包含と可換し、none も保持する。 -/
theorem face_option_square (c : E.FaceInTargetSubset (comparisonFactor q r h ⁻¹' A)) :
    Option.map (SubsetRestriction.faceInclusion N (coarseLE N E h hab))
      (M.targetSubsetFaceMapOption A (comparisonFactor q r h ⁻¹' A) (fun _ ht => ht) c) =
    M.targetSubsetFaceMapOption B (comparisonFactor q r h ⁻¹' B) (fun _ ht => ht)
      (SubsetRestriction.faceInclusion E (fineLE N E h hab) c) := by
  cases hm : M.faceMap c.1 with
  | none =>
    rw [M.targetSubsetFaceMapOption_eq_none A _ _ c hm,
      M.targetSubsetFaceMapOption_eq_none B (comparisonFactor q r h ⁻¹' B) (fun _ ht => ht)
        (SubsetRestriction.faceInclusion E (fineLE N E h hab) c) hm]
    rfl
  | some d =>
    rw [M.targetSubsetFaceMapOption_eq_some A _ _ c d hm,
      M.targetSubsetFaceMapOption_eq_some B (comparisonFactor q r h ⁻¹' B) (fun _ ht => ht)
        (SubsetRestriction.faceInclusion E (fineLE N E h hab) c) d hm]
    rfl
/-- 次数 0 の実 pullback と署名包含の台制限は可換する。 -/
theorem pullback0_square (x : (N.targetSubsetComplex B).C0) :
    SubsetRestriction.restrict0 E (fineLE N E h hab)
      (M.targetSubsetPullback0 B (comparisonFactor q r h ⁻¹' B) (fun _ ht => ht) x) =
    M.targetSubsetPullback0 A (comparisonFactor q r h ⁻¹' A) (fun _ ht => ht)
      (SubsetRestriction.restrict0 N (coarseLE N E h hab) x) := by
  funext c
  simp only [SubsetRestriction.restrict0_apply,
    TargetSupportedNerveMorphism.targetSubsetPullback0_apply]
  rw [← chart_square N E h hab M c]
/-- 次数 1 の実 pullback と署名包含の台制限は可換する。 -/
theorem pullback1_square (x : (N.targetSubsetComplex B).C1) :
    SubsetRestriction.restrict1 E (fineLE N E h hab)
      (M.targetSubsetPullback1 B (comparisonFactor q r h ⁻¹' B) (fun _ ht => ht) x) =
    M.targetSubsetPullback1 A (comparisonFactor q r h ⁻¹' A) (fun _ ht => ht)
      (SubsetRestriction.restrict1 N (coarseLE N E h hab) x) := by
  funext c
  simp only [SubsetRestriction.restrict1_apply,
    TargetSupportedNerveMorphism.targetSubsetPullback1_apply]
  rw [← edge_option_square N E h hab M c]
  cases M.targetSubsetEdgeMapOption A (comparisonFactor q r h ⁻¹' A) (fun _ ht => ht) c <;> rfl
/-- 次数 2 の実 pullback と署名包含の台制限は可換する。 -/
theorem pullback2_square (x : (N.targetSubsetComplex B).C2) :
    SubsetRestriction.restrict2 E (fineLE N E h hab)
      (M.targetSubsetPullback2 B (comparisonFactor q r h ⁻¹' B) (fun _ ht => ht) x) =
    M.targetSubsetPullback2 A (comparisonFactor q r h ⁻¹' A) (fun _ ht => ht)
      (SubsetRestriction.restrict2 N (coarseLE N E h hab) x) := by
  funext c
  simp only [SubsetRestriction.restrict2_apply,
    TargetSupportedNerveMorphism.targetSubsetPullback2_apply]
  rw [← face_option_square N E h hab M c]
  cases M.targetSubsetFaceMapOption A (comparisonFactor q r h ⁻¹' A) (fun _ ht => ht) c <;> rfl
/-- 実 A-subnerve 比較は署名包含の全三次数制限と可換する。 -/
theorem comparison_square :
    cochainComp (M.aSubnerveComparisonHom B) (SubsetRestriction.hom E (fineLE N E h hab)) =
      cochainComp (SubsetRestriction.hom N (coarseLE N E h hab)) (M.aSubnerveComparisonHom A) := by
  apply cochain_ext
  · ext x
    exact pullback0_square N E h hab M x
  · ext x
    exact pullback1_square N E h hab M x
  · ext x
    exact pullback2_square N E h hab M x
/-- 既存三項比較の零延長も同じ台制限の実正方形を与える。 -/
theorem complex_square :
    zeroExtensionMap (M.aSubnerveComparisonHom B) ≫
      zeroExtensionMap (SubsetRestriction.hom E (fineLE N E h hab)) =
    zeroExtensionMap (SubsetRestriction.hom N (coarseLE N E h hab)) ≫
      zeroExtensionMap (M.aSubnerveComparisonHom A) := by
  rw [← zeroExtensionMap_comp, ← zeroExtensionMap_comp,comparison_square N E h hab M]
end AAT.AG.AtlasDefectComposition.SupportRestriction
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition.SupportRestriction
