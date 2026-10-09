import ResearchLean.AG.AtlasCoefficientFiber.WitnessFiveLaw
import ResearchLean.AG.AtlasCoefficientFiber.WitnessFiveChain

/-!
# G-135 W5：全A・全Lawの同原rank表

## Implementation notes

空Aは同入力の空商から零を生成する。有限期待値の表を仮定として取り込まず、
元κ*/τ/比較と独立有限producerを各生成定理へ接続する。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber.WitnessFive
open CanonicalResolution ResolutionInvariance TwoPhase FaceRelationSubdivision AtlasDefectComposition
open WitnessCommon WitnessFullSupport

/-- 非空Aの同κ*のrange rankは1。 -/
theorem kappaStar_rank (A : Set Bool) (hA : A.Nonempty) : Module.finrank ℚ (LinearMap.range (kappaStar M A)) = 1 := by
  let e := LinearEquiv.ofInjective (kappaStar M A) (by rw [← kappaStarEquiv_toLinearMap]; exact (kappaStarEquiv A).injective)
  exact e.finrank_eq.symm.trans (wholePhi_dimension A hA)
/-- 空Aでは同粗chartは選択されない。 -/
theorem empty_chart_isEmpty : IsEmpty (Nc.ChartInTargetSubset ∅) where
  false c := by obtain ⟨_,_,ht⟩ := c.2; exact ht
/-- 空Aの全Φ Betti和は同原添字の空和。 -/
theorem empty_phi_dimension_sum :
    letI := Fintype.ofFinite (Nc.ChartInTargetSubset ∅)
    ∑ c : Nc.ChartInTargetSubset ∅, Module.finrank ℚ (phiComplex M ∅ c).H1 = 0 := by
  letI := empty_chart_isEmpty
  letI := Fintype.ofFinite (Nc.ChartInTargetSubset ∅)
  simp only [Finset.univ_eq_empty,Finset.sum_empty]
/-- 空Aの元κ*は零の全Φ始域から零。 -/
theorem empty_kappaStar_zero : kappaStar M ∅ = 0 := by
  letI := empty_chart_isEmpty
  apply LinearMap.ext; intro x
  rw [Subsingleton.elim x 0,map_zero]; rfl
/-- 全Aの同原κ* rankは非空支持で1、空支持で0。 -/
theorem allA_kappaStar_rank (A : Set Bool) : Module.finrank ℚ (LinearMap.range (kappaStar M A)) =
    @ite ℕ A.Nonempty (Classical.propDecidable _) 1 0 := by
  classical
  by_cases hA : A.Nonempty
  · rw [if_pos hA]; exact kappaStar_rank A hA
  · rw [if_neg hA]
    have he : A = ∅ := Set.not_nonempty_iff_eq_empty.mp hA
    subst A
    rw [empty_kappaStar_zero,LinearMap.range_zero]
    exact Module.finrank_zero_of_subsingleton
/-- 全Aの同原Φ全Betti和、空Aも同選択規則。 -/
theorem allA_phi_dimension_sum (A : Set Bool) :
    letI := Fintype.ofFinite (Nc.ChartInTargetSubset A)
    ∑ c : Nc.ChartInTargetSubset A, Module.finrank ℚ (phiComplex M A c).H1 =
      @ite ℕ A.Nonempty (Classical.propDecidable _) 1 0 := by
  classical
  by_cases hA : A.Nonempty
  · rw [if_pos hA]; exact phi_dimension_sum A hA
  · rw [if_neg hA]
    have he : A = ∅ := Set.not_nonempty_iff_eq_empty.mp hA
    subst A; exact empty_phi_dimension_sum
/-- literalRの次元は全Aで零。 -/
theorem R_dimension (A : Set Bool) : Module.finrank ℚ (R M A) = 0 := by
  letI := R_subsingleton A
  exact Module.finrank_zero_of_subsingleton
/-- 同標準τのrange rankは全Aで零。 -/
theorem tau_rank (A : Set Bool) : Module.finrank ℚ (LinearMap.range (connectingTau M A)) = 0 := by
  rw [tau_zero,LinearMap.range_zero]
  exact Module.finrank_zero_of_subsingleton
/-- 独立原有限producerの全A診断も00。 -/
theorem primitive_J (A : Set Bool) : primitiveDiagnostic M A = (0,0) :=
  (primitiveDiagnostic_eq_blockDefect M A).trans (defect A)
/-- 同原W5全A表、どの項も原P/比較/κ/τと一致。 -/
theorem full_rank_table (A : Set Bool) :
    blockDefect (unitH1 M A) = (0,0) ∧
    (letI := Fintype.ofFinite (Nc.ChartInTargetSubset A); ∑ c : Nc.ChartInTargetSubset A, Module.finrank ℚ (phiComplex M A c).H1 =
      @ite ℕ A.Nonempty (Classical.propDecidable _) 1 0) ∧
    Module.finrank ℚ (LinearMap.range (kappaStar M A)) = @ite ℕ A.Nonempty (Classical.propDecidable _) 1 0 ∧
    Module.finrank ℚ (R M A) = 0 ∧ Module.finrank ℚ (LinearMap.range (connectingTau M A)) = 0 ∧ primitiveDiagnostic M A = (0,0) :=
  ⟨unit_defect A,allA_phi_dimension_sum A,allA_kappaStar_rank A,R_dimension A,tau_rank A,primitive_J A⟩
/-- 同二Law表、同台二labelのκ* rank2を保持。 -/
theorem law_full_rank_table :
    blockDefect (lawUnitH1 M laws adequate_coarse) = (0,0) ∧
    Module.finrank ℚ ((l : LawValueLabel laws) → (c : Nc.ChartInTargetSubset (labelValueFiber laws qc adequate_coarse l)) →
      (phiComplex M (labelValueFiber laws qc adequate_coarse l) c).H1) = 2 ∧
    Module.finrank ℚ (LinearMap.range (lawKappaStar M laws adequate_coarse)) = 2 ∧
    Module.finrank ℚ (lawR M laws adequate_coarse) = 0 ∧
    Module.finrank ℚ (LinearMap.range (lawConnectingTau M laws adequate_coarse)) = 0 ∧
    primitiveLawDiagnostic M laws adequate_coarse = (0,0) :=
  ⟨law_unit_defect,law_wholePhi_dimension,law_kappaStar_rank,law_R_dimension,law_tau_rank,primitive_law_J⟩

/-- 同原粗H¹全商は非空Aで二次元。 -/
theorem coarse_H1_dimension (A : Set Bool) (hA : A.Nonempty) : Module.finrank ℚ (Nc.targetSubsetComplex A).H1 = 2 :=
  (coarseCoordinates A hA).finrank_eq.trans (Module.finrank_fin_fun ℚ)
/-- 同原細H¹全商も非空Aで二次元。 -/
theorem fine_H1_dimension (A : Set Bool) (hA : A.Nonempty) :
    Module.finrank ℚ (Nf.targetSubsetComplex (comparisonFactor qc qf coarser ⁻¹' A)).H1 = 2 :=
  (fineCoordinates A hA).finrank_eq.trans (Module.finrank_fin_fun ℚ)
/-- 同原Pの三次数は非空Aで1/2/0、独立Kanのまま評価。 -/
theorem p_degrees_dimension (A : Set Bool) (hA : A.Nonempty) :
    Module.finrank ℚ (pushforwardComplex M A).C0 = 1 ∧ Module.finrank ℚ (pushforwardComplex M A).C1 = 2 ∧
    Module.finrank ℚ (pushforwardComplex M A).C2 = 0 := by
  refine ⟨(pNamedEquiv A hA).e0.finrank_eq.trans ?_,(pNamedEquiv A hA).e1.finrank_eq.trans (Module.finrank_fin_fun ℚ),?_⟩
  · exact Module.finrank_fintype_fun_eq_card ℚ
  · letI := pC2_subsingleton A
    exact Module.finrank_zero_of_subsingleton
/-- 同原P H²の次元零、期待値を入力にしない。 -/
theorem pH2_dimension (A : Set Bool) : Module.finrank ℚ ((zeroExtension (pushforwardComplex M A)).homology (2:ℤ)) = 0 := by
  letI := pH2_subsingleton A
  exact Module.finrank_zero_of_subsingleton
/-- 全Aの原有限保存Boolは同実欠損零からtrue。 -/
theorem primitive_preservation_true (A : Set Bool) : primitivePreservationDecision M A = true :=
  (primitivePreservationDecision_eq_true_iff M A).mpr (defect A)
/-- 全Setを走査する同原有限保存Boolもtrue。 -/
theorem allA_preservation_true : allAPreservationDecision M = true :=
  (allAPreservationDecision_eq_true_iff M).mpr defect
/-- 二発生labelを走査する同原Law保存Boolもtrue。 -/
theorem law_preservation_true : lawPreservationDecision M laws adequate_coarse = true :=
  (lawPreservationDecision_eq_true_iff M laws adequate_coarse).mpr law_defect

end AAT.AG.AtlasCoefficientFiber.WitnessFive
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.kappaStar_rank
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.empty_chart_isEmpty
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.empty_phi_dimension_sum
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.empty_kappaStar_zero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.allA_kappaStar_rank
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.allA_phi_dimension_sum
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.R_dimension
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.tau_rank
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.primitive_J
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.full_rank_table
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.law_full_rank_table
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.coarse_H1_dimension
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.fine_H1_dimension
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.p_degrees_dimension
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.pH2_dimension
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.primitive_preservation_true
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.allA_preservation_true
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.law_preservation_true
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber.WitnessFive
