import ResearchLean.AG.AtlasDefectComposition.ThreeStageConeIntegration
import ResearchLean.AG.AtlasDefectComposition.WitnessOneFullLawCones
import Formal.Util.AssertStandardAxioms
/-! # W1の同じ全Law入力での有限モデルと実逐次商

Implementation notes: 二ラベルを持つ既存の同じ原始三段へFを特殊化する。
元の隣接射を単射と仮定せず、実filtration商の次数別寄与を指定同値で計算する。
-/
noncomputable section
open CategoryTheory Limits CochainComplex
namespace AAT.AG.AtlasDefectComposition.WitnessOne
/-- 既存W1の原始比較そのものから作る有限三段path。 -/
def finitePath := ThreeStagePath.path M₀₁ M₁₂
/-- W1の同じ非定数Lawの全二ラベルを保持する実tower入力。 -/
def finiteTower := lawTowerInput finitePath laws adequate₀
/-- W1の第一実累積比較は元の全Law生成比較である。 -/
theorem finite_cumulative_first : ConeTower.cumulative finiteTower 1 = zeroExtensionMap fullActual₀₁ := rfl
/-- W1の直接実累積比較は元の原始M02の全Law生成比較である。 -/
theorem finite_cumulative_direct : ConeTower.cumulative finiteTower 2 = zeroExtensionMap fullActual₀₂ := rfl
/-- W1の第二実隣接比較は元の全Law生成比較である。 -/
theorem finite_adjacent_second : ConeTower.adjacent finiteTower 1 = zeroExtensionMap fullActual₁₂ := rfl
/-- W1の元の三錐と有限towerの三錐は全三射で同型になる。 -/
def finiteTriangleIso := ThreeStagePath.lawTowerTriangleIso M₀₁ M₁₂ laws adequate₀
/-- W1の直接実錐へのterminal有限モデルの指定同値。 -/
def finiteTerminalEquiv : HomotopyEquiv (ConeTower.model finiteTower 2)
    (comparisonCone fullActual₀₂) := ConeTower.augmentation finiteTower 2
/-- W1のterminalモデルの実部分複体filtration。 -/
def finiteFiltration := ConeTower.filtration finiteTower 2
/-- W1の第一実逐次商は元の第一全Law錐と指定homotopy同値になる。 -/
def finiteFirstQuotientEquiv :
    HomotopyEquiv (cokernel (ConeTower.filtrationInclusion finiteTower 2 (0 : Fin 2)))
      (comparisonCone fullActual₀₁) := ConeTower.filtrationQuotientEquiv finiteTower 2 0
/-- W1の第二実逐次商は元の第二全Law錐と指定homotopy同値になる。 -/
def finiteSecondQuotientEquiv :
    HomotopyEquiv (cokernel (ConeTower.filtrationInclusion finiteTower 2 (1 : Fin 2)))
      (comparisonCone fullActual₁₂) := ConeTower.filtrationQuotientEquiv finiteTower 2 1
/-- W1の全実逐次商は同署名でも異なる二ラベルの実逐次商へ直和分解される。 -/
def finiteQuotientLawSumIso (i : Fin 2) := lawFiltrationQuotientSumIso finitePath laws adequate₀ i
/-- 第一実逐次商のH0/H1寄与は同じW1全Lawの0,2である。 -/
theorem finite_first_quotient_dimensions :
    Module.finrank ℚ ((cokernel (ConeTower.filtrationInclusion finiteTower 2 (0 : Fin 2))).homology 0)=0 ∧
    Module.finrank ℚ ((cokernel (ConeTower.filtrationInclusion finiteTower 2 (0 : Fin 2))).homology 1)=2 := by
  rw [(finiteFirstQuotientEquiv.toHomologyIso 0).toLinearEquiv.finrank_eq,
    (finiteFirstQuotientEquiv.toHomologyIso 1).toLinearEquiv.finrank_eq]
  exact full_forward_cone_dimensions
/-- 第二実逐次商のH0/H1寄与は同じW1全Lawの2,0である。 -/
theorem finite_second_quotient_dimensions :
    Module.finrank ℚ ((cokernel (ConeTower.filtrationInclusion finiteTower 2 (1 : Fin 2))).homology 0)=2 ∧
    Module.finrank ℚ ((cokernel (ConeTower.filtrationInclusion finiteTower 2 (1 : Fin 2))).homology 1)=0 := by
  rw [(finiteSecondQuotientEquiv.toHomologyIso 0).toLinearEquiv.finrank_eq,
    (finiteSecondQuotientEquiv.toHomologyIso 1).toLinearEquiv.finrank_eq]
  exact full_backward_cone_dimensions
/-- 同じ実terminalモデルのH0/H1は相殺後の直接錐と同じ0,0である。 -/
theorem finite_terminal_dimensions :
    Module.finrank ℚ ((ConeTower.model finiteTower 2).homology 0)=0 ∧
    Module.finrank ℚ ((ConeTower.model finiteTower 2).homology 1)=0 := by
  rw [(finiteTerminalEquiv.toHomologyIso 0).toLinearEquiv.finrank_eq,
    (finiteTerminalEquiv.toHomologyIso 1).toLinearEquiv.finrank_eq]
  exact full_direct_cone_dimensions
end AAT.AG.AtlasDefectComposition.WitnessOne
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition.WitnessOne
