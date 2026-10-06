import ResearchLean.AG.AtlasDefectComposition.FiniteModelApplication
import ResearchLean.AG.AtlasDefectComposition.ThreeStageFinitePath
import ResearchLean.AG.AtlasDefectComposition.FiniteThreeStageTriangle
import ResearchLean.AG.AtlasDefectComposition.FiniteSignatureDiagram
import ResearchLean.AG.AtlasDefectComposition.LawFiltrationQuotientDecomposition
import Formal.Util.AssertStandardAxioms
/-! # 同じ原始三比較への有限モデルの接続

Implementation notes: 直接射は元のchart/Option比較合成から独立生成する。
subsetの初段逆像同型は既存の指定同型を使い、全Lawは元の全ラベルを保持する。
-/
noncomputable section
open CategoryTheory CochainComplex
namespace AAT.AG.AtlasDefectComposition.ThreeStagePath
open CanonicalResolution ResolutionInvariance
universe u
variable {Source : Type u} {q₀ q₁ q₂ : Reading Source}
variable {N₀ : TargetSupportedNerve.{u,u} q₀} {N₁ : TargetSupportedNerve.{u,u} q₁}
variable {N₂ : TargetSupportedNerve.{u,u} q₂}
variable {h₀₁ : q₀.CoarserThan q₁} {h₁₂ : q₁.CoarserThan q₂}
variable (M₀₁ : TargetSupportedNerveMorphism q₀ q₁ h₀₁ N₀ N₁)
variable (M₁₂ : TargetSupportedNerveMorphism q₁ q₂ h₁₂ N₁ N₂)
/-- 同じq₀ subsetの三段有限モデルは元の全三対比較の錐triangleへ同型になる。 -/
def subsetTowerTriangleIso (A : Set q₀.Target) :
    ConeTower.triangle (subsetTowerInput (path M₀₁ M₁₂) A) 1 ≅
      ConeTower.finiteTriangle (subsetPathDiagram (path M₀₁ M₁₂) A) :=
  ConeTower.finiteTowerTriangleIso _
/-- 初段の同じ元subsetへの同定も指定transportであり追加入力を要求しない。 -/
def subsetInitialIso (A : Set q₀.Target) :
    (subsetPathDiagram (path M₀₁ M₁₂) A).obj 0 ≅ zeroExtension (N₀.targetSubsetComplex A) :=
  subsetPathInitialIso _ _
variable [Fintype Source] (laws : FiniteLawFamily Source) (ha : laws.Adequate q₀)
/-- 原始直接比較の全Law生成射は実隣接二射と合成する。 -/
theorem law_direct_comp :
    zeroExtensionMap ((comparisonComp M₀₁ M₁₂).generatedComparisonHom laws ha
      (adequate_of_coarser laws (Reading.coarserThan_trans h₀₁ h₁₂) ha)) =
    zeroExtensionMap (M₀₁.generatedComparisonHom laws ha (adequate_of_coarser laws h₀₁ ha)) ≫
      zeroExtensionMap (M₁₂.generatedComparisonHom laws (adequate_of_coarser laws h₀₁ ha)
        (adequate_of_coarser laws (Reading.coarserThan_trans h₀₁ h₁₂) ha)) := by
  rw [generatedComparisonHom_comp M₀₁ M₁₂ laws ha (adequate_of_coarser laws h₀₁ ha)
    (adequate_of_coarser laws (Reading.coarserThan_trans h₀₁ h₁₂) ha),zeroExtensionMap_comp]
/-- 有限pathの全Law triangleは独立に生成した元の三比較の実triangleである。 -/
theorem law_finite_triangle :
    ConeTower.finiteTriangle (lawPathDiagram (path M₀₁ M₁₂) laws ha) =
      compositionTriangle
        (zeroExtensionMap (M₀₁.generatedComparisonHom laws ha (adequate_of_coarser laws h₀₁ ha)))
        (zeroExtensionMap (M₁₂.generatedComparisonHom laws (adequate_of_coarser laws h₀₁ ha)
          (adequate_of_coarser laws (Reading.coarserThan_trans h₀₁ h₁₂) ha)))
        (zeroExtensionMap ((comparisonComp M₀₁ M₁₂).generatedComparisonHom laws ha
          (adequate_of_coarser laws (Reading.coarserThan_trans h₀₁ h₁₂) ha)))
        (law_direct_comp M₀₁ M₁₂ laws ha) := rfl
/-- Fの全Law三段モデルとCの元の全三錐triangleとの全三射の指定同型。 -/
def lawTowerTriangleIso :
    ConeTower.triangle (lawTowerInput (path M₀₁ M₁₂) laws ha) 1 ≅
      compositionTriangle
        (zeroExtensionMap (M₀₁.generatedComparisonHom laws ha (adequate_of_coarser laws h₀₁ ha)))
        (zeroExtensionMap (M₁₂.generatedComparisonHom laws (adequate_of_coarser laws h₀₁ ha)
          (adequate_of_coarser laws (Reading.coarserThan_trans h₀₁ h₁₂) ha)))
        (zeroExtensionMap ((comparisonComp M₀₁ M₁₂).generatedComparisonHom laws ha
          (adequate_of_coarser laws (Reading.coarserThan_trans h₀₁ h₁₂) ha)))
        (law_direct_comp M₀₁ M₁₂ laws ha) :=
  ConeTower.finiteTowerTriangleIso _ ≪≫ eqToIso (law_finite_triangle M₀₁ M₁₂ laws ha)
end AAT.AG.AtlasDefectComposition.ThreeStagePath
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition.ThreeStagePath
