import ResearchLean.AG.AtlasDefectComposition.FiniteSubsetPath
import ResearchLean.AG.AtlasDefectComposition.ThreeStageSignatures
import Formal.Util.AssertStandardAxioms
/-! # T0 の原始三比較と有限pathの一致

Implementation notes: 元のreading・全nerve・部分incidence二射を直接並べる。
(0,2) は原始圏の全比較合成であり、生成cochain合成から定義しない。
-/
noncomputable section
open CategoryTheory
namespace AAT.AG.AtlasDefectComposition.ThreeStagePath
open CanonicalResolution ResolutionInvariance
universe u
variable {Source : Type u} {q₀ q₁ q₂ : Reading Source}
variable {N₀ : TargetSupportedNerve.{u,u} q₀} {N₁ : TargetSupportedNerve.{u,u} q₁}
variable {N₂ : TargetSupportedNerve.{u,u} q₂}
variable {h₀₁ : q₀.CoarserThan q₁} {h₁₂ : q₁.CoarserThan q₂}
variable (M₀₁ : TargetSupportedNerveMorphism q₀ q₁ h₀₁ N₀ N₁)
variable (M₁₂ : TargetSupportedNerveMorphism q₁ q₂ h₁₂ N₁ N₂)
/-- T0 の原始三段を同じ Source の有限pathへ並べる。 -/
def path : Fin 3 ⥤ RawResolution Source :=
  ComposableArrows.mk₂
    (⟨h₀₁,M₀₁⟩ : (⟨q₀,N₀⟩ : RawResolution Source) ⟶ ⟨q₁,N₁⟩)
    (⟨h₁₂,M₁₂⟩ : (⟨q₁,N₁⟩ : RawResolution Source) ⟶ ⟨q₂,N₂⟩)
/-- 元の第一全原始射を保持する公開式。 -/
theorem path_first : (path M₀₁ M₁₂).map (homOfLE (show (0 : Fin 3) ≤ 1 by decide)) =
    (⟨h₀₁,M₀₁⟩ : (⟨q₀,N₀⟩ : RawResolution Source) ⟶ ⟨q₁,N₁⟩) := rfl
/-- 元の第二全原始射を保持する公開式。 -/
theorem path_second : (path M₀₁ M₁₂).map (homOfLE (show (1 : Fin 3) ≤ 2 by decide)) =
    (⟨h₁₂,M₁₂⟩ : (⟨q₁,N₁⟩ : RawResolution Source) ⟶ ⟨q₂,N₂⟩) := rfl
/-- 直接原始射は全 chart/Option edge/Option face 成分を持つM1合成である。 -/
theorem path_direct : (path M₀₁ M₁₂).map (homOfLE (show (0 : Fin 3) ≤ 2 by decide)) =
    (⟨Reading.coarserThan_trans h₀₁ h₁₂,comparisonComp M₀₁ M₁₂⟩ :
      (⟨q₀,N₀⟩ : RawResolution Source) ⟶ ⟨q₂,N₂⟩) := rfl
/-- path の reading 族はEの同じ三段族である。 -/
theorem path_readings : pathReadings (path M₀₁ M₁₂) = ThreeStageSignatures.readings q₀ q₁ q₂ := by
  funext i
  fin_cases i <;> rfl
/-- path の全名付きcell族はEの同じ三段全nerve族である。 -/
theorem path_nerves (i : Fin 3) : HEq (pathNerves (path M₀₁ M₁₂) i)
    (ThreeStageSignatures.nerves q₀ q₁ q₂ N₀ N₁ N₂ i) := by
  fin_cases i <;> rfl
/-- (0,2) のsubset射も元の全原始直接比較から独立生成される。 -/
theorem subset_direct (A : Set q₀.Target) :
    (subsetPathDiagram (path M₀₁ M₁₂) A).map (homOfLE (show (0 : Fin 3) ≤ 2 by decide)) =
      zeroExtensionMap (SupportStages.pairComparison
        (pathReadings (path M₀₁ M₁₂)) (pathNerves (path M₀₁ M₁₂))
        (pathCoarser (path M₀₁ M₁₂)) 0 2 (Reading.coarserThan_trans h₀₁ h₁₂)
          (comparisonComp M₀₁ M₁₂) A) := rfl
variable [Fintype Source] (laws : FiniteLawFamily Source) (ha : laws.Adequate q₀)
/-- (0,2) の全Law射も同じ原始直接比較から独立生成される。 -/
theorem law_direct :
    (lawPathDiagram (path M₀₁ M₁₂) laws ha).map (homOfLE (show (0 : Fin 3) ≤ 2 by decide)) =
      zeroExtensionMap ((comparisonComp M₀₁ M₁₂).generatedComparisonHom laws ha
        (adequate_of_coarser laws (Reading.coarserThan_trans h₀₁ h₁₂) ha)) := rfl
end AAT.AG.AtlasDefectComposition.ThreeStagePath
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition.ThreeStagePath
