import ResearchLean.AG.AtlasDefectComposition.WitnessThreeActual
import ResearchLean.AG.AtlasDefectComposition.LawUniqueBlock
import Formal.Util.AssertStandardAxioms
/-! # W3二つの原始反例の全Law実対象

Implementation notes: W3の原始定数Lawから唯一ラベル性を証明し、全Law複体・錐を同じ実blockへ同定する。既存の実block計算を対象同型で移し、追加寄与を残す。
-/
noncomputable section
open HomologicalComplex
namespace AAT.AG.AtlasDefectComposition.WitnessThree
open ResolutionInvariance
/-- W3の発生ラベルは実入力の唯一の定数Law値である。 -/
instance labelsSubsingleton : Subsingleton (LawValueLabel laws) :=
  ⟨fun x y => (label_unique x).trans (label_unique y).symm⟩
/-- W3aの全Law原始比較から独立生成した三項Hom。 -/
abbrev fullActualA := MA.generatedComparisonHom laws adequate₀ adequate₁
/-- W3bの全Law原始比較から独立生成した三項Hom。 -/
abbrev fullActualB := MB.generatedComparisonHom laws adequate₀ adequate₁
/-- W3a全Lawの全次数実homology比較欠損は同じ実block欠損である。 -/
theorem fullActualA_standard_defect (m : ℤ) :
    blockDefect (homologyMap (zeroExtensionMap fullActualA) m).hom =
      blockDefect (homologyMap (zeroExtensionMap actualA) m).hom :=
  lawUniqueBlockStandardDefect A₀ A₁ laws adequate₀ MA adequate₁ label m
/-- W3b全Lawの全次数実homology比較欠損は同じ実block欠損である。 -/
theorem fullActualB_standard_defect (m : ℤ) :
    blockDefect (homologyMap (zeroExtensionMap fullActualB) m).hom =
      blockDefect (homologyMap (zeroExtensionMap actualB) m).hom :=
  lawUniqueBlockStandardDefect B₀ B₁ laws adequate₀ MB adequate₁ label m
/-- W3a全Lawの既存H¹比較の欠損も零である。 -/
theorem fullActualA_H1_defect : blockDefect fullActualA.h1Map=(0,0) := by
  rw [← standardH1_defect,fullActualA_standard_defect,standardH1_defect]
  exact actualA_H1_defect
/-- W3b全Lawの既存H¹比較の欠損も零である。 -/
theorem fullActualB_H1_defect : blockDefect fullActualB.h1Map=(0,0) := by
  rw [← standardH1_defect,fullActualB_standard_defect,standardH1_defect]
  exact actualB_H1_defect
/-- W3a全Lawにも追加のH⁰余核の1次元が残る。 -/
theorem fullActualA_H0_cokernel_dimension :
    Module.finrank ℚ ((zeroExtension (A₁.lawGeneratedComplex laws adequate₁)).homology 0 ⧸
      LinearMap.range (homologyMap (zeroExtensionMap fullActualA) 0).hom)=1 := by
  rw [← blockDefect_cokernel_dimension,fullActualA_standard_defect,blockDefect_cokernel_dimension]
  exact actualA_H0_cokernel_dimension
/-- W3b全Lawにも追加のH²核の1次元が残る。 -/
theorem fullActualB_H2_kernel_dimension :
    Module.finrank ℚ (LinearMap.ker (homologyMap (zeroExtensionMap fullActualB) 2).hom)=1 := by
  rw [← blockDefect_kernel_dimension,fullActualB_standard_defect,blockDefect_kernel_dimension]
  exact actualB_H2_kernel_dimension
/-- W3a全Law錐の全次数homology次元は実blockと同じである。 -/
theorem fullActualA_cone_homology_dimension (m : ℤ) :
    Module.finrank ℚ ((comparisonCone fullActualA).homology m)=
      Module.finrank ℚ ((comparisonCone actualA).homology m) :=
  lawUniqueBlockConeHomology_dimension A₀ A₁ laws adequate₀ MA adequate₁ label m
/-- W3b全Law錐の全次数homology次元は実blockと同じである。 -/
theorem fullActualB_cone_homology_dimension (m : ℤ) :
    Module.finrank ℚ ((comparisonCone fullActualB).homology m)=
      Module.finrank ℚ ((comparisonCone actualB).homology m) :=
  lawUniqueBlockConeHomology_dimension B₀ B₁ laws adequate₀ MB adequate₁ label m
/-- W3a全Lawの実錐の指定四次数のhomology次元。 -/
theorem fullActualA_cone_homology_dimensions :
    Module.finrank ℚ ((comparisonCone fullActualA).homology (-1))=0 ∧
    Module.finrank ℚ ((comparisonCone fullActualA).homology 0)=1 ∧
    Module.finrank ℚ ((comparisonCone fullActualA).homology 1)=0 ∧
    Module.finrank ℚ ((comparisonCone fullActualA).homology 2)=0 := by
  simp only [fullActualA_cone_homology_dimension]
  exact actualA_cone_homology_dimensions
/-- W3b全Lawの実錐の指定四次数のhomology次元。 -/
theorem fullActualB_cone_homology_dimensions :
    Module.finrank ℚ ((comparisonCone fullActualB).homology (-1))=0 ∧
    Module.finrank ℚ ((comparisonCone fullActualB).homology 0)=0 ∧
    Module.finrank ℚ ((comparisonCone fullActualB).homology 1)=1 ∧
    Module.finrank ℚ ((comparisonCone fullActualB).homology 2)=0 := by
  simp only [fullActualB_cone_homology_dimension]
  exact actualB_cone_homology_dimensions
/-- W3b全Lawの実錐の空間次元も唯一blockと同じである。 -/
theorem fullActualB_cone_degree_dimension (m : ℤ) :
    Module.finrank ℚ ((comparisonCone fullActualB).X m)=
      Module.finrank ℚ ((comparisonCone actualB).X m) :=
  lawUniqueBlockConeDegree_dimension B₀ B₁ laws adequate₀ MB adequate₁ label m
/-- W3b全Lawの実錐の指定四空間次元。 -/
theorem fullActualB_cone_dimensions :
    Module.finrank ℚ ((comparisonCone fullActualB).X (-1))=4 ∧
    Module.finrank ℚ ((comparisonCone fullActualB).X 0)=9 ∧
    Module.finrank ℚ ((comparisonCone fullActualB).X 1)=7 ∧
    Module.finrank ℚ ((comparisonCone fullActualB).X 2)=1 := by
  simp only [fullActualB_cone_degree_dimension]
  exact actualB_cone_dimensions
/-- W3b全Lawの実錐の指定三微分rank。 -/
theorem fullActualB_cone_differential_ranks :
    Module.finrank ℚ (LinearMap.range ((comparisonCone fullActualB).d (-1) 0).hom)=4 ∧
    Module.finrank ℚ (LinearMap.range ((comparisonCone fullActualB).d 0 1).hom)=5 ∧
    Module.finrank ℚ (LinearMap.range ((comparisonCone fullActualB).d 1 2).hom)=1 := by
  simp only [comparisonCone_eq]
  rw [lawUniqueBlockCone_d_rank B₀ B₁ laws adequate₀ MB adequate₁ label (-1) 0,
    lawUniqueBlockCone_d_rank B₀ B₁ laws adequate₀ MB adequate₁ label 0 1,
    lawUniqueBlockCone_d_rank B₀ B₁ laws adequate₀ MB adequate₁ label 1 2]
  simpa only [comparisonCone_eq] using actualB_cone_differential_ranks
end AAT.AG.AtlasDefectComposition.WitnessThree
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition.WitnessThree
