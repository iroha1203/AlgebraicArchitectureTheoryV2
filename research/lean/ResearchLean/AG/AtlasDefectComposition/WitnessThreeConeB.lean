import ResearchLean.AG.AtlasDefectComposition.WitnessThreeNamed
import ResearchLean.AG.AtlasDefectComposition.ComparisonHomology
import ResearchLean.AG.AtlasDefectComposition.ConeDimensionCalculus
import Formal.Util.AssertStandardAxioms
/-! # W3bの他次数寄与と標準錐

実生成された名付き比較のH⁰同型、H¹零性、H²核から標準長完全列を読む。
-/
noncomputable section
open CategoryTheory HomologicalComplex CochainComplex
namespace AAT.AG.AtlasDefectComposition.WitnessThree
open TwoPhase ResolutionInvariance
/-- W3bの標準H⁰比較も、原始chart比較からの同型である。 -/
theorem namedB_standardH0_bijective :
    Function.Bijective (HomologicalComplex.homologyMap (zeroExtensionMap namedB) 0).hom :=
  (standardH0_bijective_iff namedB).mpr namedB_H0_bijective
/-- W3bの標準H⁰余核とH⁰核はともに零次元。 -/
theorem namedB_H0_defect :
    blockDefect (HomologicalComplex.homologyMap (zeroExtensionMap namedB) 0).hom = (0,0) :=
  (blockDefect_eq_zero_iff_bijective _).mpr namedB_standardH0_bijective
/-- W3bの標準H¹比較の実欠損は零である。 -/
theorem namedB_H1_defect :
    blockDefect (HomologicalComplex.homologyMap (zeroExtensionMap namedB) 1).hom = (0,0) := by
  have hc := tetrahedron_homology_dimensions.2.1
  have hd := triangle_homology_dimensions.2.1
  rw [blockDefect_eq_finrank_sub_range,hc,hd]
  simp
/-- W3bの既存H¹比較も零欠損である。 -/
theorem namedB_oldH1_defect : blockDefect namedB.h1Map = (0,0) := by
  rw [← standardH1_defect]
  exact namedB_H1_defect
/-- W3bのH²実比較の核は1次元、余核は零次元である。 -/
theorem namedB_H2_defect :
    blockDefect (HomologicalComplex.homologyMap (zeroExtensionMap namedB) 2).hom = (1,0) := by
  have hc := tetrahedron_homology_dimensions.2.2
  have hd := triangle_homology_dimensions.2.2
  have hr : Module.finrank ℚ (LinearMap.range
      (HomologicalComplex.homologyMap (zeroExtensionMap namedB) 2).hom) = 0 := by
    have h := (LinearMap.range
      (HomologicalComplex.homologyMap (zeroExtensionMap namedB) 2).hom).finrank_le
    omega
  rw [blockDefect_eq_finrank_sub_range,hc,hd,hr]
/-- W3bの標準錐の四つのhomology次元は0,0,1,0。 -/
theorem namedB_cone_homology_dimensions :
    Module.finrank ℚ ((comparisonCone namedB).homology (-1)) = 0 ∧
    Module.finrank ℚ ((comparisonCone namedB).homology 0) = 0 ∧
    Module.finrank ℚ ((comparisonCone namedB).homology 1) = 1 ∧
    Module.finrank ℚ ((comparisonCone namedB).homology 2) = 0 := by
  constructor
  · rw [comparisonCone_dimension_minus_one,namedB_H0_defect]
  · constructor
    · rw [comparisonCone_dimension_defect]
      change (blockDefect (HomologicalComplex.homologyMap (zeroExtensionMap namedB) 0).hom).2 +
        (blockDefect (HomologicalComplex.homologyMap (zeroExtensionMap namedB) 1).hom).1 = 0
      rw [namedB_H0_defect,namedB_H1_defect]
      rfl
    · constructor
      · rw [comparisonCone_dimension_defect]
        change (blockDefect (HomologicalComplex.homologyMap (zeroExtensionMap namedB) 1).hom).2 +
          (blockDefect (HomologicalComplex.homologyMap (zeroExtensionMap namedB) 2).hom).1 = 1
        rw [namedB_H1_defect,namedB_H2_defect]
        rfl
      · rw [comparisonCone_dimension_two,namedB_H2_defect]
end AAT.AG.AtlasDefectComposition.WitnessThree
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition.WitnessThree
