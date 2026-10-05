import ResearchLean.AG.AtlasDefectComposition.SupportRestriction
import Formal.Util.AssertStandardAxioms
/-! # 原始比較と任意の実セル制限の正方形

Implementation notes: 両側の実セル選択を指定し、同じ chart と Option 宣言を保持する。
全段共通署名への適用では各選択条件を元の段階セルから放電する。
-/
noncomputable section
namespace AAT.AG.AtlasDefectComposition.SubsetComparisonNaturality
open CanonicalResolution ResolutionInvariance TwoPhase CategoryTheory
universe u
variable {Source : Type u} {q r : Reading Source}
variable (N : TargetSupportedNerve q) (E : TargetSupportedNerve r) (h : q.CoarserThan r)
variable (M : TargetSupportedNerveMorphism q r h N E)
variable {A B : Set q.Target} {A' B' : Set r.Target}
variable (sc : SubsetRestriction.SelectedLE N A B) (sf : SubsetRestriction.SelectedLE E A' B')
variable (ha : ∀ t, t ∈ A' → comparisonFactor q r h t ∈ A)
variable (hb : ∀ t, t ∈ B' → comparisonFactor q r h t ∈ B)
/-- chart の実比較と両側選択包含は元のセルを固定して可換する。 -/
theorem chart_square (c : E.ChartInTargetSubset A') :
    SubsetRestriction.chartInclusion N sc
      (M.targetSubsetChartMap A A' ha c) =
    M.targetSubsetChartMap B B' hb
      (SubsetRestriction.chartInclusion E sf c) := by
  apply Subtype.ext
  rfl
/-- edge の実 Option 比較は両側セル包含と可換し、none も保持する。 -/
theorem edge_option_square (c : E.EdgeInTargetSubset A') :
    Option.map (SubsetRestriction.edgeInclusion N sc)
      (M.targetSubsetEdgeMapOption A A' ha c) =
    M.targetSubsetEdgeMapOption B B' hb
      (SubsetRestriction.edgeInclusion E sf c) := by
  cases hm : M.edgeMap c.1 with
  | none =>
    rw [M.targetSubsetEdgeMapOption_eq_none A _ _ c hm,
      M.targetSubsetEdgeMapOption_eq_none B B' hb
        (SubsetRestriction.edgeInclusion E sf c) hm]
    rfl
  | some d =>
    rw [M.targetSubsetEdgeMapOption_eq_some A _ _ c d hm,
      M.targetSubsetEdgeMapOption_eq_some B B' hb
        (SubsetRestriction.edgeInclusion E sf c) d hm]
    rfl
/-- face の実 Option 比較は両側セル包含と可換し、none も保持する。 -/
theorem face_option_square (c : E.FaceInTargetSubset A') :
    Option.map (SubsetRestriction.faceInclusion N sc)
      (M.targetSubsetFaceMapOption A A' ha c) =
    M.targetSubsetFaceMapOption B B' hb
      (SubsetRestriction.faceInclusion E sf c) := by
  cases hm : M.faceMap c.1 with
  | none =>
    rw [M.targetSubsetFaceMapOption_eq_none A _ _ c hm,
      M.targetSubsetFaceMapOption_eq_none B B' hb
        (SubsetRestriction.faceInclusion E sf c) hm]
    rfl
  | some d =>
    rw [M.targetSubsetFaceMapOption_eq_some A _ _ c d hm,
      M.targetSubsetFaceMapOption_eq_some B B' hb
        (SubsetRestriction.faceInclusion E sf c) d hm]
    rfl
/-- 次数 0 の実 pullback と署名包含の台制限は可換する。 -/
theorem pullback0_square (x : (N.targetSubsetComplex B).C0) :
    SubsetRestriction.restrict0 E sf
      (M.targetSubsetPullback0 B B' hb x) =
    M.targetSubsetPullback0 A A' ha
      (SubsetRestriction.restrict0 N sc x) := by
  funext c
  simp only [SubsetRestriction.restrict0_apply,
    TargetSupportedNerveMorphism.targetSubsetPullback0_apply]
  rw [← chart_square N E h M sc sf ha hb c]
/-- 次数 1 の実 pullback と署名包含の台制限は可換する。 -/
theorem pullback1_square (x : (N.targetSubsetComplex B).C1) :
    SubsetRestriction.restrict1 E sf
      (M.targetSubsetPullback1 B B' hb x) =
    M.targetSubsetPullback1 A A' ha
      (SubsetRestriction.restrict1 N sc x) := by
  funext c
  simp only [SubsetRestriction.restrict1_apply,
    TargetSupportedNerveMorphism.targetSubsetPullback1_apply]
  rw [← edge_option_square N E h M sc sf ha hb c]
  cases M.targetSubsetEdgeMapOption A A' ha c <;> rfl
/-- 次数 2 の実 pullback と署名包含の台制限は可換する。 -/
theorem pullback2_square (x : (N.targetSubsetComplex B).C2) :
    SubsetRestriction.restrict2 E sf
      (M.targetSubsetPullback2 B B' hb x) =
    M.targetSubsetPullback2 A A' ha
      (SubsetRestriction.restrict2 N sc x) := by
  funext c
  simp only [SubsetRestriction.restrict2_apply,
    TargetSupportedNerveMorphism.targetSubsetPullback2_apply]
  rw [← face_option_square N E h M sc sf ha hb c]
  cases M.targetSubsetFaceMapOption A A' ha c <;> rfl
/-- 実 A-subnerve 比較は署名包含の全三次数制限と可換する。 -/
theorem comparison_square :
    cochainComp (M.targetSubsetComparisonHom B B' hb) (SubsetRestriction.hom E sf) =
      cochainComp (SubsetRestriction.hom N sc) (M.targetSubsetComparisonHom A A' ha) := by
  apply cochain_ext
  · ext x
    exact pullback0_square N E h M sc sf ha hb x
  · ext x
    exact pullback1_square N E h M sc sf ha hb x
  · ext x
    exact pullback2_square N E h M sc sf ha hb x
end AAT.AG.AtlasDefectComposition.SubsetComparisonNaturality
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition.SubsetComparisonNaturality
