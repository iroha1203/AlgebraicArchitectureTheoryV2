import ResearchLean.AG.AtlasDefectComposition.WitnessOneEndpoints
import Formal.Util.AssertStandardAxioms
/-! # W1の実生成標準錐の次数別寄与

同じ原始入力の各ラベルでH⁰余核とH²核が零であり、H¹欠損だけが二次数へ現れる。
-/
noncomputable section
open CategoryTheory HomologicalComplex
namespace AAT.AG.AtlasDefectComposition.WitnessOne
open ResolutionInvariance
/-- W1第一原始比較の実生成三項Hom。 -/
abbrev actual₀₁ (l : LawValueLabel laws) := M₀₁.generatedBlockComparisonHom laws adequate₀ adequate₁ l
/-- W1第二原始比較の実生成三項Hom。 -/
abbrev actual₁₂ (l : LawValueLabel laws) := M₁₂.generatedBlockComparisonHom laws adequate₁ adequate₂ l
/-- W1直接原始比較の実生成三項Hom。 -/
abbrev actual₀₂ (l : LawValueLabel laws) := M₀₂.generatedBlockComparisonHom laws adequate₀ adequate₂ l
/-- 第一実比較の全整数次数欠損は同じ名付き入力計算へ移る。 -/
theorem forward_standard_defect_named (l : LawValueLabel laws) (m : ℤ) :
    blockDefect (HomologicalComplex.homologyMap (zeroExtensionMap (actual₀₁ l)) m).hom =
    blockDefect (HomologicalComplex.homologyMap (zeroExtensionMap (named₀₁ l)) m).hom :=
  fullBlockNamedHomology_defect M₀₁ laws adequate₀ adequate₁ _ _ _ _ _ _ l m
/-- 第二実比較の全整数次数欠損は同じ名付き入力計算へ移る。 -/
theorem backward_standard_defect_named (l : LawValueLabel laws) (m : ℤ) :
    blockDefect (HomologicalComplex.homologyMap (zeroExtensionMap (actual₁₂ l)) m).hom =
    blockDefect (HomologicalComplex.homologyMap (zeroExtensionMap (named₁₂ l)) m).hom :=
  fullBlockNamedHomology_defect M₁₂ laws adequate₁ adequate₂ _ _ _ _ _ _ l m
/-- 直接実比較の全整数次数欠損は同じ名付き入力計算へ移る。 -/
theorem direct_standard_defect_named (l : LawValueLabel laws) (m : ℤ) :
    blockDefect (HomologicalComplex.homologyMap (zeroExtensionMap (actual₀₂ l)) m).hom =
    blockDefect (HomologicalComplex.homologyMap (zeroExtensionMap (named₀₂ l)) m).hom :=
  fullBlockNamedHomology_defect M₀₂ laws adequate₀ adequate₂ _ _ _ _ _ _ l m
/-- W1三実比較の標準H⁰欠損は零。 -/
theorem actual_H0_defects (l : LawValueLabel laws) :
    blockDefect (HomologicalComplex.homologyMap (zeroExtensionMap (actual₀₁ l)) 0).hom = (0,0) ∧
    blockDefect (HomologicalComplex.homologyMap (zeroExtensionMap (actual₁₂ l)) 0).hom = (0,0) ∧
    blockDefect (HomologicalComplex.homologyMap (zeroExtensionMap (actual₀₂ l)) 0).hom = (0,0) := by
  rw [forward_standard_defect_named,backward_standard_defect_named,direct_standard_defect_named]
  exact named_H0_defects l
/-- W1三実比較の標準H²欠損は零。 -/
theorem actual_H2_defects (l : LawValueLabel laws) :
    blockDefect (HomologicalComplex.homologyMap (zeroExtensionMap (actual₀₁ l)) 2).hom = (0,0) ∧
    blockDefect (HomologicalComplex.homologyMap (zeroExtensionMap (actual₁₂ l)) 2).hom = (0,0) ∧
    blockDefect (HomologicalComplex.homologyMap (zeroExtensionMap (actual₀₂ l)) 2).hom = (0,0) := by
  rw [forward_standard_defect_named,backward_standard_defect_named,direct_standard_defect_named]
  exact named_H2_defects l
/-- 錐の二欠損表示に加わる次数0余核・次数2核の実次元零性。 -/
def extraTermsZero {C D : TwoPhase.ThreeCochainComplex ℚ}
    (f : TwoPhase.ThreeCochainComplex.Hom C D) : Prop :=
  Module.finrank ℚ ((zeroExtension D).homology 0 ⧸
    LinearMap.range (HomologicalComplex.homologyMap (zeroExtensionMap f) 0).hom)=0 ∧
  Module.finrank ℚ (LinearMap.ker
    (HomologicalComplex.homologyMap (zeroExtensionMap f) 2).hom)=0
/-- 二つの実次数欠損の零性から追加項の実商・実核次元の零性を得る。 -/
theorem extraTermsZero_of_defects {C D : TwoPhase.ThreeCochainComplex ℚ}
    (f : TwoPhase.ThreeCochainComplex.Hom C D)
    (h0 : blockDefect (HomologicalComplex.homologyMap (zeroExtensionMap f) 0).hom=(0,0))
    (h2 : blockDefect (HomologicalComplex.homologyMap (zeroExtensionMap f) 2).hom=(0,0)) :
    extraTermsZero f := by
  constructor
  · rw [←blockDefect_cokernel_dimension,h0]
  · rw [←blockDefect_kernel_dimension,h2]
/-- W1の三つの実比較は、全実ラベルで二つの追加項が零である。 -/
theorem actual_extra_terms_zero (l : LawValueLabel laws) :
    extraTermsZero (actual₀₁ l) ∧ extraTermsZero (actual₁₂ l) ∧ extraTermsZero (actual₀₂ l) :=
  ⟨extraTermsZero_of_defects _ (actual_H0_defects l).1 (actual_H2_defects l).1,
    extraTermsZero_of_defects _ (actual_H0_defects l).2.1 (actual_H2_defects l).2.1,
    extraTermsZero_of_defects _ (actual_H0_defects l).2.2 (actual_H2_defects l).2.2⟩
/-- W3aの実追加寄与が、この零性述語を一般入力で恒真とすることを反証する。 -/
theorem extraTermsZero_W3a_false : ¬ extraTermsZero WitnessThree.actualA := by
  intro h
  have h0 := h.1
  have h1 := WitnessThree.actualA_H0_cokernel_dimension
  omega
/-- W1各ラベルの第一実生成標準錐の次数0/1は0,1。 -/
theorem forward_cone_dimensions (l : LawValueLabel laws) :
    Module.finrank ℚ ((comparisonCone (actual₀₁ l)).homology 0)=0 ∧
    Module.finrank ℚ ((comparisonCone (actual₀₁ l)).homology 1)=1 := by
  constructor
  · rw [comparisonCone_dimension_defect]
    change (blockDefect (HomologicalComplex.homologyMap (zeroExtensionMap (actual₀₁ l)) 0).hom).2 +
      (blockDefect (HomologicalComplex.homologyMap (zeroExtensionMap (actual₀₁ l)) 1).hom).1=0
    rw [(actual_H0_defects l).1,standardH1_defect]
    change (0,0).2+(blockDefect (forward l)).1=0
    rw [forward_defect]; rfl
  · rw [comparisonCone_dimension_defect]
    change (blockDefect (HomologicalComplex.homologyMap (zeroExtensionMap (actual₀₁ l)) 1).hom).2 +
      (blockDefect (HomologicalComplex.homologyMap (zeroExtensionMap (actual₀₁ l)) 2).hom).1=1
    rw [(actual_H2_defects l).1,standardH1_defect]
    change (blockDefect (forward l)).2+(0,0).1=1
    rw [forward_defect]; rfl
/-- W1各ラベルの第二実生成標準錐の次数0/1は1,0。 -/
theorem backward_cone_dimensions (l : LawValueLabel laws) :
    Module.finrank ℚ ((comparisonCone (actual₁₂ l)).homology 0)=1 ∧
    Module.finrank ℚ ((comparisonCone (actual₁₂ l)).homology 1)=0 := by
  constructor
  · rw [comparisonCone_dimension_defect]
    change (blockDefect (HomologicalComplex.homologyMap (zeroExtensionMap (actual₁₂ l)) 0).hom).2 +
      (blockDefect (HomologicalComplex.homologyMap (zeroExtensionMap (actual₁₂ l)) 1).hom).1=1
    rw [(actual_H0_defects l).2.1,standardH1_defect]
    change (0,0).2+(blockDefect (backward l)).1=1
    rw [backward_defect]; rfl
  · rw [comparisonCone_dimension_defect]
    change (blockDefect (HomologicalComplex.homologyMap (zeroExtensionMap (actual₁₂ l)) 1).hom).2 +
      (blockDefect (HomologicalComplex.homologyMap (zeroExtensionMap (actual₁₂ l)) 2).hom).1=0
    rw [(actual_H2_defects l).2.1,standardH1_defect]
    change (blockDefect (backward l)).2+(0,0).1=0
    rw [backward_defect]; rfl
/-- W1各ラベルの直接実生成標準錐の次数0/1は0,0。 -/
theorem direct_cone_dimensions (l : LawValueLabel laws) :
    Module.finrank ℚ ((comparisonCone (actual₀₂ l)).homology 0)=0 ∧
    Module.finrank ℚ ((comparisonCone (actual₀₂ l)).homology 1)=0 := by
  constructor
  · rw [comparisonCone_dimension_defect]
    change (blockDefect (HomologicalComplex.homologyMap (zeroExtensionMap (actual₀₂ l)) 0).hom).2 +
      (blockDefect (HomologicalComplex.homologyMap (zeroExtensionMap (actual₀₂ l)) 1).hom).1=0
    rw [(actual_H0_defects l).2.2,standardH1_defect]
    change (0,0).2+(blockDefect (direct l)).1=0
    rw [direct_defect]; rfl
  · rw [comparisonCone_dimension_defect]
    change (blockDefect (HomologicalComplex.homologyMap (zeroExtensionMap (actual₀₂ l)) 1).hom).2 +
      (blockDefect (HomologicalComplex.homologyMap (zeroExtensionMap (actual₀₂ l)) 2).hom).1=0
    rw [(actual_H2_defects l).2.2,standardH1_defect]
    change (blockDefect (direct l)).2+(0,0).1=0
    rw [direct_defect]; rfl
end AAT.AG.AtlasDefectComposition.WitnessOne
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition.WitnessOne
