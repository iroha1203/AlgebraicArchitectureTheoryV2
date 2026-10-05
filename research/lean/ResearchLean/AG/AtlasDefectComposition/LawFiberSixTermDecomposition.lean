import ResearchLean.AG.AtlasDefectComposition.LawFiberH1Family
import ResearchLean.AG.AtlasDefectComposition.FiniteDefectConjugation
import Formal.Util.AssertStandardAxioms
/-! # 同じ粗fiber・逆像族への実Law六項列と相殺の分解

Implementation notes: 同じ原始入力から生成した各label-fiber比較へ全Law六項列を移す。全五射と実相殺像を同定し、細fiberの逆像等号をLawFiberDecompositionで固定する。
-/
noncomputable section
namespace AAT.AG.AtlasDefectComposition.LawFiberSixTermDecomposition
open CanonicalResolution ResolutionInvariance TwoPhase
universe u
variable {Source : Type u} [Fintype Source]
variable {q₀ q₁ q₂ : Reading Source} {h₀₁ : q₀.CoarserThan q₁} {h₁₂ : q₁.CoarserThan q₂}
variable {N₀ : TargetSupportedNerve q₀} {N₁ : TargetSupportedNerve q₁}
variable {N₂ : TargetSupportedNerve q₂}
variable (laws : FiniteLawFamily Source) (h₀ : laws.Adequate q₀)
variable (h₁ : laws.Adequate q₁) (h₂ : laws.Adequate q₂)
variable (M₀₁ : TargetSupportedNerveMorphism q₀ q₁ h₀₁ N₀ N₁)
variable (M₁₂ : TargetSupportedNerveMorphism q₁ q₂ h₁₂ N₁ N₂)
local notation "f" => M₀₁.generatedComparisonH1Map laws h₀ h₁
local notation "g" => M₁₂.generatedComparisonH1Map laws h₁ h₂
local notation "a" => (fun l => ThreeCochainComplex.Hom.h1Map (M₀₁.labelFiberComparisonHom laws h₀ h₁ l))
local notation "b" => (fun l => ThreeCochainComplex.Hom.h1Map (M₁₂.labelFiberComparisonHom laws h₁ h₂ l))
local notation "e₀" => lawFiberH1FamilyEquiv N₀ laws h₀
local notation "e₁" => lawFiberH1FamilyEquiv N₁ laws h₁
local notation "e₂" => lawFiberH1FamilyEquiv N₂ laws h₂
local notation "hf" => lawFiberH1Comparison_square N₀ N₁ laws h₀ M₀₁ h₁
local notation "hg" => lawFiberH1Comparison_square N₁ N₂ laws h₁ M₁₂ h₂
/-- 同じ実入力の前段核の全ラベル同型。 -/
def kernelFirstFamilyEquiv := FiniteDefectConjugation.firstEquiv f a e₀ e₁ hf
/-- 同じ実入力の合成核の全ラベル同型。 -/
def kernelCompositeFamilyEquiv := FiniteDefectConjugation.secondEquiv f g a b e₀ e₁ e₂ hf hg
/-- 同じ実入力の後段核の全ラベル同型。 -/
def kernelLastFamilyEquiv := FiniteDefectConjugation.thirdEquiv g b e₁ e₂ hg
/-- 同じ実入力の前段余核の全ラベル同型。 -/
def cokernelFirstFamilyEquiv := FiniteDefectConjugation.fourthEquiv f a e₀ e₁ hf
/-- 同じ実入力の合成余核の全ラベル同型。 -/
def cokernelCompositeFamilyEquiv := FiniteDefectConjugation.fifthEquiv f g a b e₀ e₁ e₂ hf hg
/-- 同じ実入力の後段余核の全ラベル同型。 -/
def cokernelLastFamilyEquiv := FiniteDefectConjugation.sixthEquiv g b e₁ e₂ hg
/-- 実Law六項列の第一射の各発生ラベル成分。 -/
theorem first_component (x : LinearMap.ker f) (l : LawValueLabel laws) :
    kernelCompositeFamilyEquiv laws h₀ h₁ h₂ M₀₁ M₁₂ (DefectSequence.first f g x) l =
      DefectSequence.first (a l) (b l) (kernelFirstFamilyEquiv laws h₀ h₁ M₀₁ x l) :=
  FiniteDefectConjugation.first_component f g a b e₀ e₁ e₂ hf hg x l
set_option maxHeartbeats 800000 in
/-- 実Law六項列の第二射の各発生ラベル成分。 -/
theorem second_component (x : LinearMap.ker ((g).comp f)) (l : LawValueLabel laws) :
    kernelLastFamilyEquiv laws h₁ h₂ M₁₂ (DefectSequence.second f g x) l =
      DefectSequence.second (a l) (b l)
        (kernelCompositeFamilyEquiv laws h₀ h₁ h₂ M₀₁ M₁₂ x l) :=
  FiniteDefectConjugation.second_component f g a b e₀ e₁ e₂ hf hg x l
/-- 実Law相殺写像の各発生ラベル成分。 -/
theorem cancellation_component (x : LinearMap.ker g) (l : LawValueLabel laws) :
    cokernelFirstFamilyEquiv laws h₀ h₁ M₀₁ (DefectSequence.cancellation f g x) l =
      DefectSequence.cancellation (a l) (b l) (kernelLastFamilyEquiv laws h₁ h₂ M₁₂ x l) :=
  FiniteDefectConjugation.cancellation_component f g a b e₀ e₁ e₂ hf hg x l
/-- 実Law六項列の第四射の各発生ラベル成分。 -/
theorem fourth_component (x : (N₁.lawGeneratedComplex laws h₁).H1 ⧸ LinearMap.range f)
    (l : LawValueLabel laws) : cokernelCompositeFamilyEquiv laws h₀ h₁ h₂ M₀₁ M₁₂
      (DefectSequence.fourth f g x) l =
        DefectSequence.fourth (a l) (b l) (cokernelFirstFamilyEquiv laws h₀ h₁ M₀₁ x l) :=
  FiniteDefectConjugation.fourth_component f g a b e₀ e₁ e₂ hf hg x l
/-- 実Law六項列の第五射の各発生ラベル成分。 -/
theorem fifth_component (x : (N₂.lawGeneratedComplex laws h₂).H1 ⧸ LinearMap.range ((g).comp f))
    (l : LawValueLabel laws) : cokernelLastFamilyEquiv laws h₁ h₂ M₁₂
      (DefectSequence.fifth f g x) l =
        DefectSequence.fifth (a l) (b l)
          (cokernelCompositeFamilyEquiv laws h₀ h₁ h₂ M₀₁ M₁₂ x l) :=
  FiniteDefectConjugation.fifth_component f g a b e₀ e₁ e₂ hf hg x l
/-- 実Law相殺像の全発生ラベル同型。 -/
def cancellationRangeFamilyEquiv :=
  FiniteDefectConjugation.cancellationRangeEquiv f g a b e₀ e₁ e₂ hf hg
/-- 実Law相殺のrankは全発生ラベルの実rankの和である。 -/
theorem cancellation_rank_sum : Module.finrank ℚ (LinearMap.range (DefectSequence.cancellation f g)) =
    ∑ l, Module.finrank ℚ (LinearMap.range (DefectSequence.cancellation (a l) (b l))) := by
  rw [(cancellationRangeFamilyEquiv laws h₀ h₁ h₂ M₀₁ M₁₂).finrank_eq]
  exact Module.finrank_pi_fintype ℚ
end AAT.AG.AtlasDefectComposition.LawFiberSixTermDecomposition
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition.LawFiberSixTermDecomposition
