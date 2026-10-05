import ResearchLean.AG.AtlasDefectComposition.WitnessOneCones
import ResearchLean.AG.AtlasDefectComposition.WitnessOneFullLaw
import ResearchLean.AG.AtlasDefectComposition.LawStandardDimensions
import ResearchLean.AG.AtlasDefectComposition.LawConeDecomposition
import Formal.Util.AssertStandardAxioms
/-! # W1全Lawの二ラベルを保持した標準錐寄与

Implementation notes: 同じW1原始入力の実Law錐同型を使って、各発生ラベルの計算を二回加える。追加のH⁰余核・H²核も実Law欠損の成分和から評価する。
-/
noncomputable section
open HomologicalComplex
namespace AAT.AG.AtlasDefectComposition.WitnessOne
open ResolutionInvariance
/-- W1全Law第一原始比較の実生成Hom。 -/
abbrev fullActual₀₁ := M₀₁.generatedComparisonHom laws adequate₀ adequate₁
/-- W1全Law第二原始比較の実生成Hom。 -/
abbrev fullActual₁₂ := M₁₂.generatedComparisonHom laws adequate₁ adequate₂
/-- W1全Law直接原始比較の実生成Hom。 -/
abbrev fullActual₀₂ := M₀₂.generatedComparisonHom laws adequate₀ adequate₂
/-- 全Law第一実錐の二次数は、各ラベルの0,1を二回読む。 -/
theorem full_forward_cone_dimensions :
    Module.finrank ℚ ((comparisonCone fullActual₀₁).homology 0)=0 ∧
    Module.finrank ℚ ((comparisonCone fullActual₀₁).homology 1)=2 := by
  constructor
  · rw [comparisonCone_eq]
    rw [(lawConeHomologyEquiv N₀ N₁ laws adequate₀ M₀₁ adequate₁ 0).finrank_eq,
      Module.finrank_pi_fintype]
    change (∑ l, Module.finrank ℚ ((comparisonCone (actual₀₁ l)).homology 0))=0
    simp only [fun l => (forward_cone_dimensions l).1,Finset.sum_const_zero]
  · rw [comparisonCone_eq]
    rw [(lawConeHomologyEquiv N₀ N₁ laws adequate₀ M₀₁ adequate₁ 1).finrank_eq,
      Module.finrank_pi_fintype]
    change (∑ l, Module.finrank ℚ ((comparisonCone (actual₀₁ l)).homology 1))=2
    simp only [fun l => (forward_cone_dimensions l).2,Finset.sum_const,
      Finset.card_univ,label_card,smul_eq_mul,Nat.mul_one]
/-- 全Law第二実錐の二次数は、各ラベルの1,0を二回読む。 -/
theorem full_backward_cone_dimensions :
    Module.finrank ℚ ((comparisonCone fullActual₁₂).homology 0)=2 ∧
    Module.finrank ℚ ((comparisonCone fullActual₁₂).homology 1)=0 := by
  constructor
  · rw [comparisonCone_eq]
    rw [(lawConeHomologyEquiv N₁ N₂ laws adequate₁ M₁₂ adequate₂ 0).finrank_eq,
      Module.finrank_pi_fintype]
    change (∑ l, Module.finrank ℚ ((comparisonCone (actual₁₂ l)).homology 0))=2
    simp only [fun l => (backward_cone_dimensions l).1,Finset.sum_const,
      Finset.card_univ,label_card,smul_eq_mul,Nat.mul_one]
  · rw [comparisonCone_eq]
    rw [(lawConeHomologyEquiv N₁ N₂ laws adequate₁ M₁₂ adequate₂ 1).finrank_eq,
      Module.finrank_pi_fintype]
    change (∑ l, Module.finrank ℚ ((comparisonCone (actual₁₂ l)).homology 1))=0
    simp only [fun l => (backward_cone_dimensions l).2,Finset.sum_const_zero]
/-- 全Law直接実錐の二次数も同じ二ラベルから零を得る。 -/
theorem full_direct_cone_dimensions :
    Module.finrank ℚ ((comparisonCone fullActual₀₂).homology 0)=0 ∧
    Module.finrank ℚ ((comparisonCone fullActual₀₂).homology 1)=0 := by
  constructor
  · rw [comparisonCone_eq]
    rw [(lawConeHomologyEquiv N₀ N₂ laws adequate₀ M₀₂ adequate₂ 0).finrank_eq,
      Module.finrank_pi_fintype]
    change (∑ l, Module.finrank ℚ ((comparisonCone (actual₀₂ l)).homology 0))=0
    simp only [fun l => (direct_cone_dimensions l).1,Finset.sum_const_zero]
  · rw [comparisonCone_eq]
    rw [(lawConeHomologyEquiv N₀ N₂ laws adequate₀ M₀₂ adequate₂ 1).finrank_eq,
      Module.finrank_pi_fintype]
    change (∑ l, Module.finrank ℚ ((comparisonCone (actual₀₂ l)).homology 1))=0
    simp only [fun l => (direct_cone_dimensions l).2,Finset.sum_const_zero]
/-- 各ラベルで零と証明した端次数欠損は全Lawでも零である。 -/
theorem full_endpoint_defects (m : ℤ)
    (hf : ∀ l, blockDefect (homologyMap (zeroExtensionMap (actual₀₁ l)) m).hom=(0,0))
    (hb : ∀ l, blockDefect (homologyMap (zeroExtensionMap (actual₁₂ l)) m).hom=(0,0))
    (hd : ∀ l, blockDefect (homologyMap (zeroExtensionMap (actual₀₂ l)) m).hom=(0,0)) :
    blockDefect (homologyMap (zeroExtensionMap fullActual₀₁) m).hom=(0,0) ∧
    blockDefect (homologyMap (zeroExtensionMap fullActual₁₂) m).hom=(0,0) ∧
    blockDefect (homologyMap (zeroExtensionMap fullActual₀₂) m).hom=(0,0) := by
  rw [lawStandardDefect_sum N₀ N₁ laws adequate₀ M₀₁ adequate₁,
    lawStandardDefect_sum N₁ N₂ laws adequate₁ M₁₂ adequate₂,
    lawStandardDefect_sum N₀ N₂ laws adequate₀ M₀₂ adequate₂]
  simpa only [hf,hb,hd,Finset.sum_const_zero] using
    (show (0,0)=(0,0) ∧ (0,0)=(0,0) ∧ (0,0)=(0,0) from ⟨rfl,rfl,rfl⟩)
/-- 全Lawの三実比較にも追加のH⁰余核・H²核の零性が成立する。 -/
theorem full_extra_terms_zero : extraTermsZero fullActual₀₁ ∧
    extraTermsZero fullActual₁₂ ∧ extraTermsZero fullActual₀₂ := by
  have h0 := full_endpoint_defects 0 (fun l => (actual_H0_defects l).1)
    (fun l => (actual_H0_defects l).2.1) (fun l => (actual_H0_defects l).2.2)
  have h2 := full_endpoint_defects 2 (fun l => (actual_H2_defects l).1)
    (fun l => (actual_H2_defects l).2.1) (fun l => (actual_H2_defects l).2.2)
  exact ⟨extraTermsZero_of_defects _ h0.1 h2.1,
    extraTermsZero_of_defects _ h0.2.1 h2.2.1,extraTermsZero_of_defects _ h0.2.2 h2.2.2⟩
end AAT.AG.AtlasDefectComposition.WitnessOne
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition.WitnessOne
