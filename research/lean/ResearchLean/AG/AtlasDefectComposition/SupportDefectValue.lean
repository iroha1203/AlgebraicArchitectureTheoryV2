import ResearchLean.AG.AtlasDefectComposition.SupportDefectFunctor
import ResearchLean.AG.AtlasDefectComposition.GeneratedDefect
import ResearchLean.AG.AtlasDefectComposition.ComparisonHomology
import ResearchLean.AG.AtlasDefectComposition.SelectedFamilyUniversal
import ResearchLean.AG.AtlasDefectComposition.LawSubsetDefectDecomposition
import ResearchLean.AG.AtlasDefectComposition.LawSignatureRestoration
import Formal.Util.AssertStandardAxioms
/-! # 実診断の署名値と加法的評価

Implementation notes: J は既存の実 H¹ 商の比較を評価する。
同署名の実可換同型で値を transport し、D の全 Law 和へ接続する。
-/
noncomputable section
open CategoryTheory HomologicalComplex
namespace AAT.AG.AtlasDefectComposition.SupportDefectValue
open CanonicalResolution ResolutionInvariance TwoPhase SelectedFamilies
universe u
variable {Source : Type u} {q r : Reading Source}
variable (N : TargetSupportedNerve.{u,u} q) (E : TargetSupportedNerve.{u,u} r) (h : q.CoarserThan r)
variable (M : TargetSupportedNerveMorphism q r h N E)
/-- 元の実部分集合比較の二欠損。 -/
def actual (A : Set q.Target) := blockDefect (M.aSubnerveComparisonHom A).h1Map
/-- 指定代表上の実 H¹ 比較を読む署名値。 -/
def value (s : SupportSignature.Signature N E h) := actual N E h M (SupportFunctor.representative N E h s)
/-- 実 J は署名反対圏上の実核・余核関手の次元表である。 -/
theorem value_dimension (s : SupportSignature.Signature N E h) : value N E h M s =
    (Module.finrank ℚ (SupportFunctor.h1Kernel N E h M s),
      Module.finrank ℚ (SupportFunctor.h1Cokernel N E h M s)) := by
  rw [value,actual,← standardH1_defect]
  rfl
/-- bottom の値は零署名の実 H¹ 零性から零となる。 -/
theorem value_bot : value N E h M ⊥ = (0,0) := by
  rw [value_dimension]
  let A := SupportFunctor.representative N E h ⊥
  have hz : SupportSignature.sigma N E h A = ⊥ := SignatureGeometry.sigma_gamma_signature _ _
  have hc := SupportZeroBlock.coarse_isZero_X N E h hz 1
  have hf := SupportZeroBlock.fine_isZero_X N E h hz 1
  letI : Subsingleton ((SupportFunctor.coarseComplex N E h ⊥).homology 1) :=
    ModuleCat.subsingleton_of_isZero (((zeroExtension (N.targetSubsetComplex A)).sc 1).isZero_homology_of_isZero_X₂ hc)
  letI : Subsingleton ((SupportFunctor.fineComplex N E h ⊥).homology 1) :=
    ModuleCat.subsingleton_of_isZero (((zeroExtension (E.targetSubsetComplex (comparisonFactor q r h ⁻¹' A))).sc 1).isZero_homology_of_isZero_X₂ hf)
  have hk : Module.finrank ℚ (SupportFunctor.h1Kernel N E h M ⊥) = 0 := Module.finrank_zero_of_subsingleton
  have hq : Module.finrank ℚ (SupportFunctor.h1Cokernel N E h M ⊥) = 0 := Module.finrank_zero_of_subsingleton
  rw [hk,hq]
/-- 全名付きセル署名を保つ実同型は J を保持する。 -/
theorem same_alpha {A B : Set q.Target}
    (heq : SupportSignature.alpha N E h A = SupportSignature.alpha N E h B) : actual N E h M A = actual N E h M B := by
  let ec := (SupportReconstruction.coarseEquiv N E h heq).h1Equiv
  let ef := (SupportReconstruction.fineEquiv N E h heq).h1Equiv
  have hs : ∀ x, ef ((M.aSubnerveComparisonHom B).h1Map x) = (M.aSubnerveComparisonHom A).h1Map (ec x) := by
    intro x
    have hh := congrArg (fun f => f.h1Map x) (SupportReconstruction.comparison_square N E h heq M)
    simpa only [cochainComp_h1Map,LinearMap.comp_apply] using hh
  apply Prod.ext
  · simp only [actual,blockDefect_kernel_dimension]
    exact (LinearConjugation.kernelEquiv _ _ ec ef hs).finrank_eq.symm
  · simp only [actual,blockDefect_cokernel_dimension]
    exact (LinearConjugation.cokernelEquiv _ _ ec ef hs).finrank_eq.symm
/-- 署名値の評価は元の実 subset の J に一致する。 -/
theorem value_sigma (A : Set q.Target) : value N E h M (SupportSignature.sigma N E h A) = actual N E h M A :=
  same_alpha N E h M (SupportReconstruction.representative_eq N E h A)
/-- J の selected 族評価は固定対象・射に対する加法的評価となる。 -/
def evaluation : AdditiveEvaluation (SupportSignature.family N E h) (ℕ × ℕ) :=
  evaluationOfValues _ (value N E h M) (value_bot N E h M)
/-- 実 J 評価は元の全 block 欠損の和である。 -/
theorem evaluation_actual (F : Family (SupportSignature.family N E h)) : (evaluation N E h M).eval F =
    letI := Fintype.ofFinite F.Index; ∑ i, actual N E h M (F.subset i) := by
  classical
  simp only [evaluation,evaluationOfValues_eval,valueSum_eq_sum,value_sigma]
variable [Fintype Source] (laws : FiniteLawFamily Source) (ha : laws.Adequate q) (hr : laws.Adequate r)
/-- 実全 Law の J は署名値の加法的評価に一致する。 -/
theorem law_evaluation : (evaluation N E h M).eval (lawSelectedFamily (h:=h) N E laws ha) =
    blockDefect (M.generatedComparisonH1Map laws ha hr) := by
  rw [evaluation_actual,lawH1Defect_subset_sum]
  have hi : Fintype.ofFinite (lawSelectedFamily (h:=h) N E laws ha).Index =
      inferInstanceAs (Fintype (LawValueLabel laws)) := Subsingleton.elim _ _
  rw [hi]
  change (∑ l : LawValueLabel laws, blockDefect (M.aSubnerveComparisonHom (labelValueFiber laws q ha l)).h1Map) = _
  apply Prod.ext <;> simp only [Prod.fst_sum,Prod.snd_sum]
end AAT.AG.AtlasDefectComposition.SupportDefectValue
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition.SupportDefectValue
