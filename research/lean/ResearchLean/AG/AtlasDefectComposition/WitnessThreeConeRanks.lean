import ResearchLean.AG.AtlasDefectComposition.WitnessThreeConeA
import Formal.Util.AssertStandardAxioms
/-! # W3bの標準錐の指定空間と実微分rank

標準biproduct成分と全次数homology加法式から、4,9,7,1と4,5,1を導く。
-/
noncomputable section
open CategoryTheory HomologicalComplex
namespace AAT.AG.AtlasDefectComposition.WitnessThree
/-- W3bの標準錐の空間次元は順に4,9,7,1。 -/
theorem namedB_cone_dimensions :
    Module.finrank ℚ ((comparisonCone namedB).X (-1)) = 4 ∧
    Module.finrank ℚ ((comparisonCone namedB).X 0) = 9 ∧
    Module.finrank ℚ ((comparisonCone namedB).X 1) = 7 ∧
    Module.finrank ℚ ((comparisonCone namedB).X 2) = 1 := by
  constructor
  · rw [(comparisonConeMinusOneEquiv namedB).finrank_eq]
    change Module.finrank ℚ (Fin 4 → ℚ)=4
    simp
  · constructor
    · rw [(comparisonConeZeroEquiv namedB).finrank_eq]
      change Module.finrank ℚ ((Fin 3 → ℚ) × (Fin 6 → ℚ))=9
      simp
    · constructor
      · rw [(comparisonConeOneEquiv namedB).finrank_eq]
        change Module.finrank ℚ ((Fin 3 → ℚ) × (Fin 4 → ℚ))=7
        simp
      · rw [(comparisonConeTwoEquiv namedB).finrank_eq]
        change Module.finrank ℚ (Fin 1 → ℚ)=1
        simp
/-- W3b錐の全次数の有限次元性は実標準biproductから導く。 -/
instance namedB_cone_finite (m : ℤ) : FiniteDimensional ℚ ((comparisonCone namedB).X m) := by
  change FiniteDimensional ℚ ((CochainComplex.mappingCone (zeroExtensionMap namedB)).X m)
  infer_instance
/-- W3bの標準錐の前端に入る微分は零である。 -/
theorem namedB_cone_d_before_zero : (comparisonCone namedB).d (-2) (-1) = 0 := by
  exact (comparisonCone_isZero namedB (-2) (by decide) (by decide) (by decide) (by decide)).eq_of_src _ _
/-- W3bの標準錐の実三微分のrankは4,5,1。 -/
theorem namedB_cone_differential_ranks :
    Module.finrank ℚ (LinearMap.range ((comparisonCone namedB).d (-1) 0).hom) = 4 ∧
    Module.finrank ℚ (LinearMap.range ((comparisonCone namedB).d 0 1).hom) = 5 ∧
    Module.finrank ℚ (LinearMap.range ((comparisonCone namedB).d 1 2).hom) = 1 := by
  have hm := complex_homology_dimension (comparisonCone namedB) (-1)
  have h0 := complex_homology_dimension (comparisonCone namedB) 0
  have h1 := complex_homology_dimension (comparisonCone namedB) 1
  change Module.finrank ℚ ((comparisonCone namedB).homology (-1)) +
    Module.finrank ℚ (LinearMap.range ((comparisonCone namedB).d (-2) (-1)).hom) +
    Module.finrank ℚ (LinearMap.range ((comparisonCone namedB).d (-1) 0).hom) = _ at hm
  change Module.finrank ℚ ((comparisonCone namedB).homology 0) +
    Module.finrank ℚ (LinearMap.range ((comparisonCone namedB).d (-1) 0).hom) +
    Module.finrank ℚ (LinearMap.range ((comparisonCone namedB).d 0 1).hom) = _ at h0
  change Module.finrank ℚ ((comparisonCone namedB).homology 1) +
    Module.finrank ℚ (LinearMap.range ((comparisonCone namedB).d 0 1).hom) +
    Module.finrank ℚ (LinearMap.range ((comparisonCone namedB).d 1 2).hom) = _ at h1
  rw [namedB_cone_d_before_zero,ModuleCat.hom_zero,LinearMap.range_zero,finrank_bot] at hm
  rw [namedB_cone_homology_dimensions.1,namedB_cone_dimensions.1] at hm
  rw [namedB_cone_homology_dimensions.2.1,namedB_cone_dimensions.2.1] at h0
  rw [namedB_cone_homology_dimensions.2.2.1,namedB_cone_dimensions.2.2.1] at h1
  omega
end AAT.AG.AtlasDefectComposition.WitnessThree
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition.WitnessThree
