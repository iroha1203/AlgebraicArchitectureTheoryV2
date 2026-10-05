import ResearchLean.AG.AtlasDefectComposition.WitnessThreeConeB
import Formal.Util.AssertStandardAxioms
/-! # W3aの次数0余核寄与

原始一chartから二chartへの複製を用い、H¹欠損が零でも標準錐H⁰が非零となる。
-/
noncomputable section
open CategoryTheory HomologicalComplex
namespace AAT.AG.AtlasDefectComposition.WitnessThree
open TwoPhase ResolutionInvariance
/-- 孤立chartの原始次数0微分は零写像である。 -/
theorem A₀_d0_zero : (namedComplex A₀).d0 = 0 := by
  apply LinearMap.ext
  intro x
  funext e
  exact e.elim
/-- W3a粗側の二つの微分の実像はともに零次元。 -/
theorem A₀_ranks : Module.finrank ℚ (LinearMap.range (namedComplex A₀).d0) = 0 ∧
    Module.finrank ℚ (LinearMap.range (namedComplex A₀).d1) = 0 := by
  constructor
  · rw [A₀_d0_zero]
    simp
  · have hz : (namedComplex A₀).d1 = 0 := by
      apply LinearMap.ext; intro x; funext e; exact e.elim
    rw [hz]; simp
/-- W3a細側の二つの微分の実像はともに零次元。 -/
theorem A₁_ranks : Module.finrank ℚ (LinearMap.range (namedComplex A₁).d0) = 0 ∧
    Module.finrank ℚ (LinearMap.range (namedComplex A₁).d1) = 0 := by
  have h0 : (namedComplex A₁).d0 = 0 := by
    apply LinearMap.ext; intro x; funext e; exact e.elim
  have h1 : (namedComplex A₁).d1 = 0 := by
    apply LinearMap.ext; intro x; funext e; exact e.elim
  rw [h0,h1]; simp
/-- W3aの指定孤立複体の全homology次元。 -/
theorem A_homology_dimensions :
    Module.finrank ℚ ((zeroExtension (namedComplex A₀)).homology 0) = 1 ∧
    Module.finrank ℚ ((zeroExtension (namedComplex A₁)).homology 0) = 2 ∧
    Module.finrank ℚ ((zeroExtension (namedComplex A₀)).homology 1) = 0 ∧
    Module.finrank ℚ ((zeroExtension (namedComplex A₁)).homology 1) = 0 ∧
    Module.finrank ℚ ((zeroExtension (namedComplex A₀)).homology 2) = 0 ∧
    Module.finrank ℚ ((zeroExtension (namedComplex A₁)).homology 2) = 0 := by
  have h00 := standardH0_dimension (namedComplex A₀)
  have h01 := standardH0_dimension (namedComplex A₁)
  have h10 := standardH1_dimension (namedComplex A₀)
  have h11 := standardH1_dimension (namedComplex A₁)
  have h20 := standardH2_dimension (namedComplex A₀)
  have h21 := standardH2_dimension (namedComplex A₁)
  rw [A₀_ranks.1] at h00 h10
  rw [A₀_ranks.2] at h10 h20
  rw [A₁_ranks.1] at h01 h11
  rw [A₁_ranks.2] at h11 h21
  have c00 : Module.finrank ℚ (namedComplex A₀).C0 = 1 := by change Module.finrank ℚ (Fin 1 → ℚ)=1; simp
  have c01 : Module.finrank ℚ (namedComplex A₁).C0 = 2 := by change Module.finrank ℚ (Fin 2 → ℚ)=2; simp
  have c10 : Module.finrank ℚ (namedComplex A₀).C1 = 0 := by change Module.finrank ℚ (Empty → ℚ)=0; simp
  have c11 : Module.finrank ℚ (namedComplex A₁).C1 = 0 := by change Module.finrank ℚ (Empty → ℚ)=0; simp
  have c20 : Module.finrank ℚ (namedComplex A₀).C2 = 0 := by change Module.finrank ℚ (Empty → ℚ)=0; simp
  have c21 : Module.finrank ℚ (namedComplex A₁).C2 = 0 := by change Module.finrank ℚ (Empty → ℚ)=0; simp
  omega
/-- 原始chart複製が次数0核上でも単射である。 -/
theorem namedA_oldH0_injective : Function.Injective (oldH0Map namedA) := by
  intro x y h
  apply Subtype.ext
  funext i
  have hv := congrFun (congrArg Subtype.val h) 0
  change namedA.f0 x.val 0 = namedA.f0 y.val 0 at hv
  rw [namedA_f0,namedA_f0] at hv
  have hi : i = 0 := Subsingleton.elim _ _
  simpa only [hi] using hv
/-- 標準H⁰比較は元の核比較と同型を通して共役である。 -/
theorem namedA_H0_injective : Function.Injective
    (HomologicalComplex.homologyMap (zeroExtensionMap namedA) 0).hom := by
  intro x y h
  obtain ⟨a,rfl⟩ := (oldH0Equiv (namedComplex A₀)).surjective x
  obtain ⟨b,rfl⟩ := (oldH0Equiv (namedComplex A₀)).surjective y
  rw [← oldH0Equiv_natural,← oldH0Equiv_natural] at h
  exact congrArg (oldH0Equiv (namedComplex A₀))
    (namedA_oldH0_injective ((oldH0Equiv (namedComplex A₁)).injective h))
/-- W3aの標準H⁰比較は核0、余核1を持つ。 -/
theorem namedA_H0_defect :
    blockDefect (HomologicalComplex.homologyMap (zeroExtensionMap namedA) 0).hom = (0,1) := by
  have hk := LinearMap.ker_eq_bot.mpr namedA_H0_injective
  have hr := (HomologicalComplex.homologyMap (zeroExtensionMap namedA) 0).hom.finrank_range_add_finrank_ker
  rw [hk] at hr
  simp only [finrank_bot,add_zero] at hr
  rw [A_homology_dimensions.1] at hr
  rw [blockDefect_eq_finrank_sub_range,A_homology_dimensions.1,
    A_homology_dimensions.2.1,hr]
/-- W3aの標準H¹比較の核と余核はともに零。 -/
theorem namedA_H1_defect :
    blockDefect (HomologicalComplex.homologyMap (zeroExtensionMap namedA) 1).hom = (0,0) := by
  rw [blockDefect_eq_finrank_sub_range,A_homology_dimensions.2.2.1,
    A_homology_dimensions.2.2.2.1]
  simp
/-- W3aの標準H²比較の核と余核はともに零。 -/
theorem namedA_H2_defect :
    blockDefect (HomologicalComplex.homologyMap (zeroExtensionMap namedA) 2).hom = (0,0) := by
  rw [blockDefect_eq_finrank_sub_range,A_homology_dimensions.2.2.2.2.1,
    A_homology_dimensions.2.2.2.2.2]
  simp
/-- W3aの既存H¹欠損は零である。 -/
theorem namedA_oldH1_defect : blockDefect namedA.h1Map = (0,0) := by
  rw [←standardH1_defect]
  exact namedA_H1_defect
/-- W3aの標準錐の四つのhomology次元は0,1,0,0。 -/
theorem namedA_cone_homology_dimensions :
    Module.finrank ℚ ((comparisonCone namedA).homology (-1)) = 0 ∧
    Module.finrank ℚ ((comparisonCone namedA).homology 0) = 1 ∧
    Module.finrank ℚ ((comparisonCone namedA).homology 1) = 0 ∧
    Module.finrank ℚ ((comparisonCone namedA).homology 2) = 0 := by
  constructor
  · rw [comparisonCone_dimension_minus_one,namedA_H0_defect]
  · constructor
    · rw [comparisonCone_dimension_defect]
      change (blockDefect (HomologicalComplex.homologyMap (zeroExtensionMap namedA) 0).hom).2 +
        (blockDefect (HomologicalComplex.homologyMap (zeroExtensionMap namedA) 1).hom).1 = 1
      rw [namedA_H0_defect,namedA_H1_defect]; rfl
    · constructor
      · rw [comparisonCone_dimension_defect]
        change (blockDefect (HomologicalComplex.homologyMap (zeroExtensionMap namedA) 1).hom).2 +
          (blockDefect (HomologicalComplex.homologyMap (zeroExtensionMap namedA) 2).hom).1 = 0
        rw [namedA_H1_defect,namedA_H2_defect]; rfl
      · rw [comparisonCone_dimension_two,namedA_H2_defect]
end AAT.AG.AtlasDefectComposition.WitnessThree
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition.WitnessThree
