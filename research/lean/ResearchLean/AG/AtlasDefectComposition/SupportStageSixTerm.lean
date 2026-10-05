import ResearchLean.AG.AtlasDefectComposition.SupportStageComparison
import ResearchLean.AG.AtlasDefectComposition.SixTermNaturality
import Formal.Util.AssertStandardAxioms
/-! # 全段共通署名上の実六項列の全射

Implementation notes: すべての射に同じ基底 subset と全段実制限を使う。
可換正方形は原始セル比較から放電し、抽象的な正方形を追加入力にしない。
-/
noncomputable section
namespace AAT.AG.AtlasDefectComposition.SupportStages
open CanonicalResolution ResolutionInvariance TwoPhase
universe u v w
variable {Source : Type u} {base : Reading Source} {I : Type v}
variable (q : I → Reading Source) (N : ∀ i, TargetSupportedNerve.{u,w} (q i))
variable (h : ∀ i, base.CoarserThan (q i)) (i j k : I)
variable (hij : (q i).CoarserThan (q j)) (hjk : (q j).CoarserThan (q k))
variable (Mij : TargetSupportedNerveMorphism (q i) (q j) hij (N i) (N j))
variable (Mjk : TargetSupportedNerveMorphism (q j) (q k) hjk (N j) (N k))
/-- 全段共通逆像族の直接生成比較も独立な既存手続きから合成へ一致する。 -/
theorem pairComparison_comp (A : Set base.Target) :
    pairComparison q N h i k (Reading.coarserThan_trans hij hjk) (comparisonComp Mij Mjk) A =
      cochainComp (pairComparison q N h i j hij Mij A) (pairComparison q N h j k hjk Mjk A) :=
  targetSubsetComparisonHom_comp Mij Mjk _ _ _ (pair_mapsTo q h i j hij A) (pair_mapsTo q h j k hjk A)
/-- 全段実 H¹ 比較の六項列で、全五射と同じ台制限が可換する。 -/
theorem sixTerm_natural {A B : Set base.Target} (hAB : alpha q N h A ⊆ alpha q N h B) :
    let f := (pairComparison q N h i j hij Mij B).h1Map
    let g := (pairComparison q N h j k hjk Mjk B).h1Map
    let f' := (pairComparison q N h i j hij Mij A).h1Map
    let g' := (pairComparison q N h j k hjk Mjk A).h1Map
    let a := (stageRestriction q N h hAB i).h1Map
    let b := (stageRestriction q N h hAB j).h1Map
    let c := (stageRestriction q N h hAB k).h1Map
    let hf := pairH1_square q N h i j hij Mij hAB
    let hg := pairH1_square q N h j k hjk Mjk hAB
    (∀ x, SixTermNaturality.kernelMap _ _ a c (SixTermNaturality.comp_square f g f' g' a b c hf hg)
      (DefectSequence.first f g x) = DefectSequence.first f' g' (SixTermNaturality.kernelMap f f' a b hf x)) ∧
    (∀ x, SixTermNaturality.kernelMap g g' b c hg (DefectSequence.second f g x) =
      DefectSequence.second f' g' (SixTermNaturality.kernelMap _ _ a c (SixTermNaturality.comp_square f g f' g' a b c hf hg) x)) ∧
    (∀ x, SixTermNaturality.cokernelMap f f' a b hf (DefectSequence.cancellation f g x) =
      DefectSequence.cancellation f' g' (SixTermNaturality.kernelMap g g' b c hg x)) ∧
    (∀ x, SixTermNaturality.cokernelMap _ _ a c (SixTermNaturality.comp_square f g f' g' a b c hf hg)
      (DefectSequence.fourth f g x) = DefectSequence.fourth f' g' (SixTermNaturality.cokernelMap f f' a b hf x)) ∧
    (∀ x, SixTermNaturality.cokernelMap g g' b c hg (DefectSequence.fifth f g x) =
      DefectSequence.fifth f' g' (SixTermNaturality.cokernelMap _ _ a c (SixTermNaturality.comp_square f g f' g' a b c hf hg) x)) := by
  dsimp only
  exact ⟨SixTermNaturality.first_natural _ _ _ _ _ _ _ (pairH1_square q N h i j hij Mij hAB) (pairH1_square q N h j k hjk Mjk hAB),
    SixTermNaturality.second_natural _ _ _ _ _ _ _ (pairH1_square q N h i j hij Mij hAB) (pairH1_square q N h j k hjk Mjk hAB),
    SixTermNaturality.cancellation_natural _ _ _ _ _ _ _ (pairH1_square q N h i j hij Mij hAB) (pairH1_square q N h j k hjk Mjk hAB),
    SixTermNaturality.fourth_natural _ _ _ _ _ _ _ (pairH1_square q N h i j hij Mij hAB) (pairH1_square q N h j k hjk Mjk hAB),
    SixTermNaturality.fifth_natural _ _ _ _ _ _ _ (pairH1_square q N h i j hij Mij hAB) (pairH1_square q N h j k hjk Mjk hAB)⟩
/-- 共通署名の全段 canonical 閉集合代表。 -/
def representative (s : Signature q N h) : Set base.Target := SignatureGeometry.gamma (family q N h) s.val
/-- 共通署名の指定代表は全段の元のセル選択を保持する。 -/
@[simp] theorem alpha_representative (s : Signature q N h) : alpha q N h (representative q N h s) = s.val :=
  SignatureGeometry.alpha_gamma_signature _ s
/-- 共通署名包含は指定代表上の実全段制限を生成する。 -/
theorem representativeLE {s t : Signature q N h} (hst : s ≤ t) :
    alpha q N h (representative q N h s) ⊆ alpha q N h (representative q N h t) := by
  simpa only [alpha_representative] using hst
/-- 全六項列は共通署名の反対向き制限上で自然になる。 -/
theorem sixTerm_signature_natural {s t : Signature q N h} (hst : s ≤ t) :
    let f := (pairComparison q N h i j hij Mij (representative q N h t)).h1Map
    let g := (pairComparison q N h j k hjk Mjk (representative q N h t)).h1Map
    let f' := (pairComparison q N h i j hij Mij (representative q N h s)).h1Map
    let g' := (pairComparison q N h j k hjk Mjk (representative q N h s)).h1Map
    let a := (stageRestriction q N h (representativeLE q N h hst) i).h1Map
    let b := (stageRestriction q N h (representativeLE q N h hst) j).h1Map
    let c := (stageRestriction q N h (representativeLE q N h hst) k).h1Map
    let hf := pairH1_square q N h i j hij Mij (representativeLE q N h hst)
    let hg := pairH1_square q N h j k hjk Mjk (representativeLE q N h hst)
    (∀ x, SixTermNaturality.kernelMap _ _ a c (SixTermNaturality.comp_square f g f' g' a b c hf hg)
      (DefectSequence.first f g x) = DefectSequence.first f' g' (SixTermNaturality.kernelMap f f' a b hf x)) ∧
    (∀ x, SixTermNaturality.kernelMap g g' b c hg (DefectSequence.second f g x) =
      DefectSequence.second f' g' (SixTermNaturality.kernelMap _ _ a c (SixTermNaturality.comp_square f g f' g' a b c hf hg) x)) ∧
    (∀ x, SixTermNaturality.cokernelMap f f' a b hf (DefectSequence.cancellation f g x) =
      DefectSequence.cancellation f' g' (SixTermNaturality.kernelMap g g' b c hg x)) ∧
    (∀ x, SixTermNaturality.cokernelMap _ _ a c (SixTermNaturality.comp_square f g f' g' a b c hf hg)
      (DefectSequence.fourth f g x) = DefectSequence.fourth f' g' (SixTermNaturality.cokernelMap f f' a b hf x)) ∧
    (∀ x, SixTermNaturality.cokernelMap g g' b c hg (DefectSequence.fifth f g x) =
      DefectSequence.fifth f' g' (SixTermNaturality.cokernelMap _ _ a c (SixTermNaturality.comp_square f g f' g' a b c hf hg) x)) :=
  sixTerm_natural q N h i j k hij hjk Mij Mjk (representativeLE q N h hst)
end AAT.AG.AtlasDefectComposition.SupportStages
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition.SupportStages
