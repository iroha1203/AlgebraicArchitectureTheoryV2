import ResearchLean.AG.AtlasGluingWidth.WidthH0Regression
import ResearchLean.AG.AtlasDefectComposition.WitnessThreeActual

/-! # 一次零欠損から錐acyclicを推論できない実入力

GOAL E / witnesses §5。G-133受理済みW3aの同じSource Bool、粗一chart・細二chart、
全台、空辺・空面の原始入力とその実生成比較を再利用する。

## Implementation notes

既存のactualA_H1_defectとactualA_cone_homology_dimensionsを同じactualAで接続する。
新しいrankを入力した反例を作る代替は、受理済み原始比較の再利用を失うため採らない。
-/
noncomputable section
open CategoryTheory HomologicalComplex
namespace AAT.AG.AtlasGluingWidth.Width
open AtlasDefectComposition ResolutionInvariance

/-- 同じ全台一chart→二chartの原始比較は一次零欠損でも標準錐H⁰が一要素次元。 -/
theorem cone_h0_regression :
    blockDefect WitnessThree.actualA.h1Map = (0,0) ∧
      Module.finrank ℚ ((comparisonCone WitnessThree.actualA).homology (0:ℤ)) = 1 :=
  ⟨WitnessThree.actualA_H1_defect, WitnessThree.actualA_cone_homology_dimensions.2.1⟩
/-- 同じ生成標準錐のH⁰は実際に非零である。 -/
theorem cone_h0_regression_nonzero :
    ¬ Subsingleton ((comparisonCone WitnessThree.actualA).homology (0:ℤ)) := by
  intro h
  letI := h
  have hz : Module.finrank ℚ ((comparisonCone WitnessThree.actualA).homology (0:ℤ)) = 0 :=
    Module.finrank_zero_of_subsingleton
  have h1 := cone_h0_regression.2
  omega

end AAT.AG.AtlasGluingWidth.Width
#assert_standard_axioms_only AAT.AG.AtlasGluingWidth.Width
