import ResearchLean.AG.AtlasDefectComposition.SupportStageSixTerm
import Mathlib.Data.Fin.VecNotation
import Formal.Util.AssertStandardAxioms
/-! # T0 の三段共通署名への具体的特殊化

Implementation notes: 三つの原始 nerve を同じ Fin 3 段階添字へ並べる。
各対への射影は全段署名から同じ逆像族の署名を読む。
-/
noncomputable section
namespace AAT.AG.AtlasDefectComposition.ThreeStageSignatures
open CanonicalResolution ResolutionInvariance TwoPhase
universe u w
variable {Source : Type u} (q₀ q₁ q₂ : Reading Source)
/-- 三つの元の reading を段階名で保持する有限族。 -/
def readings : Fin 3 → Reading Source := Fin.cases q₀ (Fin.cases q₁ (fun _ => q₂))
variable (N₀ : TargetSupportedNerve.{u,w} q₀) (N₁ : TargetSupportedNerve.{u,w} q₁) (N₂ : TargetSupportedNerve.{u,w} q₂)
/-- 各段階の元の全支持 nerve。 -/
def nerves : ∀ i, TargetSupportedNerve.{u,w} (readings q₀ q₁ q₂ i) :=
  Fin.cases N₀ (Fin.cases N₁ (fun _ => N₂))
variable (h₀₁ : q₀.CoarserThan q₁) (h₁₂ : q₁.CoarserThan q₂)
/-- 同じ q₀ から全段階への canonical 因子を生成する順序。 -/
def coarsers : ∀ i, q₀.CoarserThan (readings q₀ q₁ q₂ i) :=
  Fin.cases (fun _ _ hh => hh) (Fin.cases h₀₁ (fun _ => Reading.coarserThan_trans h₀₁ h₁₂))
/-- Ω012 は三段の全 chart・edge・face を元の段階・次数・名前で保持する。 -/
abbrev Cell := SupportStages.Cell (readings q₀ q₁ q₂) (nerves q₀ q₁ q₂ N₀ N₁ N₂)
/-- T0 の三段共通署名半束。 -/
abbrev Signature := SupportStages.Signature (readings q₀ q₁ q₂) (nerves q₀ q₁ q₂ N₀ N₁ N₂) (coarsers q₀ q₁ q₂ h₀₁ h₁₂)
/-- T0 の同じ q₀ subset から三段共通署名への商射。 -/
abbrev sigma (A : Set q₀.Target) := SupportStages.sigma (readings q₀ q₁ q₂) (nerves q₀ q₁ q₂ N₀ N₁ N₂) (coarsers q₀ q₁ q₂ h₀₁ h₁₂) A
/-- 三段共通署名から (0,1) の実全セル署名への射影。 -/
def projection₀₁ := SupportStages.pairProjection (readings q₀ q₁ q₂) (nerves q₀ q₁ q₂ N₀ N₁ N₂) (coarsers q₀ q₁ q₂ h₀₁ h₁₂) 0 1 h₀₁
/-- 三段共通署名から独立に生成する直接 (0,2) の実署名への射影。 -/
def projection₀₂ := SupportStages.pairProjection (readings q₀ q₁ q₂) (nerves q₀ q₁ q₂ N₀ N₁ N₂) (coarsers q₀ q₁ q₂ h₀₁ h₁₂) 0 2 (Reading.coarserThan_trans h₀₁ h₁₂)
/-- 三段共通署名から (1,2) の同じ A₁ 逆像族の署名への射影。 -/
def projection₁₂ := SupportStages.pairProjection (readings q₀ q₁ q₂) (nerves q₀ q₁ q₂ N₀ N₁ N₂) (coarsers q₀ q₁ q₂ h₀₁ h₁₂) 1 2 h₁₂
/-- 最初の射影は元の A に対する実比較署名を復元する。 -/
theorem projection₀₁_sigma (A : Set q₀.Target) : projection₀₁ q₀ q₁ q₂ N₀ N₁ N₂ h₀₁ h₁₂ (sigma q₀ q₁ q₂ N₀ N₁ N₂ h₀₁ h₁₂ A) =
    SupportSignature.sigma N₀ N₁ h₀₁ A := by
  rw [projection₀₁,SupportStages.pairProjection_sigma]
  have hi : comparisonFactor q₀ q₀ (fun _ _ hh => hh) = id := by
    symm;exact comparisonFactor_unique q₀ q₀ _ id (fun _ => rfl)
  change SupportSignature.sigma N₀ N₁ h₀₁ (comparisonFactor q₀ q₀ _ ⁻¹' A) = _
  rw [hi,Set.preimage_id]
/-- 直接比較への射影も同じ A を保つ。 -/
theorem projection₀₂_sigma (A : Set q₀.Target) : projection₀₂ q₀ q₁ q₂ N₀ N₁ N₂ h₀₁ h₁₂ (sigma q₀ q₁ q₂ N₀ N₁ N₂ h₀₁ h₁₂ A) =
    SupportSignature.sigma N₀ N₂ (Reading.coarserThan_trans h₀₁ h₁₂) A := by
  rw [projection₀₂,SupportStages.pairProjection_sigma]
  have hi : comparisonFactor q₀ q₀ (fun _ _ hh => hh) = id := by
    symm;exact comparisonFactor_unique q₀ q₀ _ id (fun _ => rfl)
  change SupportSignature.sigma N₀ N₂ _ (comparisonFactor q₀ q₀ _ ⁻¹' A) = _
  rw [hi,Set.preimage_id]
/-- 後段への射影は共通 A₁=π01⁻¹A を保持する。 -/
theorem projection₁₂_sigma (A : Set q₀.Target) : projection₁₂ q₀ q₁ q₂ N₀ N₁ N₂ h₀₁ h₁₂ (sigma q₀ q₁ q₂ N₀ N₁ N₂ h₀₁ h₁₂ A) =
    SupportSignature.sigma N₁ N₂ h₁₂ (comparisonFactor q₀ q₁ h₀₁ ⁻¹' A) :=
  SupportStages.pairProjection_sigma _ _ _ _ _ _ A
end AAT.AG.AtlasDefectComposition.ThreeStageSignatures
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition.ThreeStageSignatures
