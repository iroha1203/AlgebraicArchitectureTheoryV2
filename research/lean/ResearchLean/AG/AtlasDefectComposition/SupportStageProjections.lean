import ResearchLean.AG.AtlasDefectComposition.SupportStageSignatures
import Formal.Util.AssertStandardAxioms
/-! # 全段共通署名から各実比較への射影

Implementation notes: 各対の署名は同じ基底 subset の逆像から生成する。
全セル選択の包含を元の段階セルのタグへ評価して商の因子化を放電する。
-/
noncomputable section
namespace AAT.AG.AtlasDefectComposition.SupportStages
open CanonicalResolution ResolutionInvariance TwoPhase
universe u v w
variable {Source : Type u} {base : Reading Source} {I : Type v}
variable (q : I → Reading Source) (N : ∀ i, TargetSupportedNerve.{u,w} (q i))
variable (h : ∀ i, base.CoarserThan (q i)) (i j : I) (hij : (q i).CoarserThan (q j))
/-- 同じ基底からの canonical 因子は任意の二段で合成する。 -/
theorem factor_pair (a : (q j).Target) :
    comparisonFactor base (q i) (h i) (comparisonFactor (q i) (q j) hij a) =
      comparisonFactor base (q j) (h j) a := by
  have hh := congrFun (comparisonFactor_comp (h i) hij) a
  exact hh.symm
/-- 全段署名の包含から各対の同じ逆像族の全セル包含を得る。 -/
theorem pair_alpha_mono {A B : Set base.Target} (hAB : alpha q N h A ⊆ alpha q N h B) :
    SupportSignature.alpha (N i) (N j) hij (comparisonFactor base (q i) (h i) ⁻¹' A) ⊆
      SupportSignature.alpha (N i) (N j) hij (comparisonFactor base (q i) (h i) ⁻¹' B) := by
  intro c hc
  rcases c with ((c | e) | f) | ((c | e) | f)
  · exact (SupportSignature.mem_alpha_coarseChart _ _ _ _ c).mpr
      ((stageLE q N h hAB i).1 c ((SupportSignature.mem_alpha_coarseChart _ _ _ _ c).mp hc))
  · exact (SupportSignature.mem_alpha_coarseEdge _ _ _ _ e).mpr
      ((stageLE q N h hAB i).2.1 e ((SupportSignature.mem_alpha_coarseEdge _ _ _ _ e).mp hc))
  · exact (SupportSignature.mem_alpha_coarseFace _ _ _ _ f).mpr
      ((stageLE q N h hAB i).2.2 f ((SupportSignature.mem_alpha_coarseFace _ _ _ _ f).mp hc))
  · apply (SupportSignature.mem_alpha_fineChart _ _ _ _ c).mpr
    have hc' := (SupportSignature.mem_alpha_fineChart _ _ _ _ c).mp hc
    change (∃ a, a ∈ (N j).chartSupport c ∧ comparisonFactor base (q i) (h i) (comparisonFactor (q i) (q j) hij a) ∈ A) at hc'
    simp only [factor_pair q h i j hij] at hc'
    have hd := (stageLE q N h hAB j).1 c hc'
    simpa only [Set.mem_preimage,factor_pair q h i j hij] using hd
  · apply (SupportSignature.mem_alpha_fineEdge _ _ _ _ e).mpr
    have hc' := (SupportSignature.mem_alpha_fineEdge _ _ _ _ e).mp hc
    change (∃ a, a ∈ (N j).edgeSupport e ∧ comparisonFactor base (q i) (h i) (comparisonFactor (q i) (q j) hij a) ∈ A) at hc'
    simp only [factor_pair q h i j hij] at hc'
    have hd := (stageLE q N h hAB j).2.1 e hc'
    simpa only [Set.mem_preimage,factor_pair q h i j hij] using hd
  · apply (SupportSignature.mem_alpha_fineFace _ _ _ _ f).mpr
    have hc' := (SupportSignature.mem_alpha_fineFace _ _ _ _ f).mp hc
    change (∃ a, a ∈ (N j).faceSupport f ∧ comparisonFactor base (q i) (h i) (comparisonFactor (q i) (q j) hij a) ∈ A) at hc'
    simp only [factor_pair q h i j hij] at hc'
    have hd := (stageLE q N h hAB j).2.2 f hc'
    simpa only [Set.mem_preimage,factor_pair q h i j hij] using hd
/-- 各対の同じ inverse-image 台族の署名商射。 -/
def pairEncode : SupBotHom (Set base.Target) (SupportSignature.Signature (N i) (N j) hij) where
  toFun A := SupportSignature.sigma (N i) (N j) hij (comparisonFactor base (q i) (h i) ⁻¹' A)
  map_sup' A B := by
    change SupportSignature.sigma _ _ _ (_ ⁻¹' (A ∪ B)) = _
    rw [Set.preimage_union]
    exact map_sup (SignatureGeometry.sigmaHom _) _ _
  map_bot' := by
    change SupportSignature.sigma _ _ _ (_ ⁻¹' (∅ : Set base.Target)) = _
    rw [Set.preimage_empty]
    exact map_bot (SignatureGeometry.sigmaHom _)
/-- 同じ全段署名は各対の実署名も同定する。 -/
theorem pair_respects (A B : Set base.Target) (hAB : alpha q N h A = alpha q N h B) :
    pairEncode q N h i j hij A = pairEncode q N h i j hij B :=
  Subtype.ext (Set.Subset.antisymm (pair_alpha_mono q N h i j hij hAB.le)
    (pair_alpha_mono q N h i j hij hAB.ge))
/-- 全段共通署名から指定二段の実署名への bottom・join 射影。 -/
def pairProjection : SupBotHom (Signature q N h) (SupportSignature.Signature (N i) (N j) hij) :=
  SignatureGeometry.quotientFactor _ (pairEncode q N h i j hij) (pair_respects q N h i j hij)
/-- 各対への射影は元の同じ基底 subset の canonical 逆像で評価される。 -/
@[simp] theorem pairProjection_sigma (A : Set base.Target) :
    pairProjection q N h i j hij (sigma q N h A) =
      SupportSignature.sigma (N i) (N j) hij (comparisonFactor base (q i) (h i) ⁻¹' A) :=
  SignatureGeometry.quotientFactor_sigma _ _ _ A
/-- 同じ基底 subset の後段は各対の canonical 逆像と同定する。 -/
theorem pair_preimage (A : Set base.Target) : comparisonFactor (q i) (q j) hij ⁻¹'
    (comparisonFactor base (q i) (h i) ⁻¹' A) = comparisonFactor base (q j) (h j) ⁻¹' A := by
  ext a
  simp only [Set.mem_preimage,factor_pair q h i j hij]
end AAT.AG.AtlasDefectComposition.SupportStages
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition.SupportStages
