import ResearchLean.AG.AtlasCoefficientFiber.WitnessThreeTransgression
import ResearchLean.AG.AtlasCoefficientFiber.WitnessThreePairedFiber

/-!
# G-135 W3：全Aの同原Phi Betti和

## Implementation notes

原xだけのk全商とy/z原零商を保って有限和を計算する。
全原Phiを一点の入力へ交換する方法は採らない。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber.WitnessThree
open CanonicalResolution ResolutionInvariance TwoPhase FaceRelationSubdivision AtlasDefectComposition
open WitnessCommon WitnessFullSupport

/-- 全原chartのPhi Betti数、xの同kのみ1。 -/
theorem phi_dimension (A : Set Bool) (c : Nc.ChartInTargetSubset A) :
    Module.finrank ℚ (phiComplex M A c).H1 = @ite ℕ (c.1 = 0) (Classical.propDecidable _) 1 0 := by
  classical
  by_cases hc : c.1 = 0
  · rw [if_pos hc]
    have hA : A.Nonempty := by obtain ⟨t,ht,ha⟩ := c.2; exact ⟨t,ha⟩
    have he : c = xChart A hA := Subtype.ext hc
    subst c
    exact (phiXCoordinates A hA).finrank_eq.trans (Module.finrank_self ℚ)
  · rw [if_neg hc]
    letI := phi_other_subsingleton A c hc
    exact Module.finrank_zero_of_subsingleton
/-- 非空Aの原Phi全Betti和は同kの1。 -/
theorem phi_dimension_sum (A : Set Bool) (hA : A.Nonempty) :
    letI := Fintype.ofFinite (Nc.ChartInTargetSubset A)
    ∑ c : Nc.ChartInTargetSubset A, Module.finrank ℚ (phiComplex M A c).H1 = 1 := by
  classical
  letI := Fintype.ofFinite (Nc.ChartInTargetSubset A)
  rw [Finset.sum_eq_single (xChart A hA)]
  · rw [phi_dimension,if_pos (show (xChart A hA).1 = 0 from rfl)]
  · intro c _ hc
    have hn : c.1 ≠ 0 := fun he => hc (Subtype.ext he)
    rw [phi_dimension,if_neg hn]
  · intro hh
    exact False.elim (hh (Finset.mem_univ _))
/-- mなし原Phi全Betti和も同kの1。 -/
theorem paired_phi_dimension_sum (A : Set Bool) (hA : A.Nonempty) :
    letI := Fintype.ofFinite (Nc.ChartInTargetSubset A)
    ∑ c : Nc.ChartInTargetSubset A, Module.finrank ℚ (phiComplex pairedM A c).H1 = 1 := by
  letI := Fintype.ofFinite (Nc.ChartInTargetSubset A)
  have he (c : Nc.ChartInTargetSubset A) := (pairedPhiEquiv A c).h1Equiv.finrank_eq
  simp only [he]
  exact phi_dimension_sum A hA
/-- 空Aにも原Phi Betti和は零。 -/
theorem empty_phi_dimension_sum :
    letI := Fintype.ofFinite (Nc.ChartInTargetSubset ∅)
    ∑ c : Nc.ChartInTargetSubset ∅, Module.finrank ℚ (phiComplex M ∅ c).H1 = 0 := by
  letI : IsEmpty (Nc.ChartInTargetSubset ∅) := ⟨fun c => by obtain ⟨t,ht,ha⟩ := c.2; exact ha⟩
  letI := Fintype.ofFinite (Nc.ChartInTargetSubset ∅)
  simp only [Finset.univ_eq_empty,Finset.sum_empty]
/-- 元κ* rankは全Aで零。 -/
theorem kappaStar_rank (A : Set Bool) : Module.finrank ℚ (LinearMap.range (kappaStar M A)) = 0 := by
  rw [kappaStar_zero,LinearMap.range_zero]
  exact Module.finrank_zero_of_subsingleton
/-- mなし元κ* rankも全Aで零。 -/
theorem paired_kappaStar_rank (A : Set Bool) : Module.finrank ℚ (LinearMap.range (kappaStar pairedM A)) = 0 := by
  rw [paired_kappaStar_zero,LinearMap.range_zero]
  exact Module.finrank_zero_of_subsingleton
/-- mなし元τ rankは全Aで零。 -/
theorem paired_tau_rank (A : Set Bool) : Module.finrank ℚ (LinearMap.range (connectingTau pairedM A)) = 0 := by
  rw [paired_tau_zero,LinearMap.range_zero]
  exact Module.finrank_zero_of_subsingleton
/-- 元全非空Aの面あり行、すべて同じ射と原Phiを使用。 -/
theorem full_rank_table (A : Set Bool) (hA : A.Nonempty) :
    blockDefect (unitH1 M A) = (0,0) ∧
    (letI := Fintype.ofFinite (Nc.ChartInTargetSubset A); ∑ c : Nc.ChartInTargetSubset A, Module.finrank ℚ (phiComplex M A c).H1 = 1) ∧
    Module.finrank ℚ (LinearMap.range (kappaStar M A)) = 0 ∧ Module.finrank ℚ (R M A) = 1 ∧
    Module.finrank ℚ (LinearMap.range (connectingTau M A)) = 1 ∧ primitiveDiagnostic M A = (0,0) :=
  ⟨unit_defect A,phi_dimension_sum A hA,kappaStar_rank A,r_dimension A hA,tau_rank A hA,primitive_J A hA⟩
/-- 元全非空Aのmなし行、m以外の同原Phi/比較を保持。 -/
theorem paired_full_rank_table (A : Set Bool) (hA : A.Nonempty) :
    blockDefect (unitH1 pairedM A) = (0,0) ∧
    (letI := Fintype.ofFinite (Nc.ChartInTargetSubset A); ∑ c : Nc.ChartInTargetSubset A, Module.finrank ℚ (phiComplex pairedM A c).H1 = 1) ∧
    Module.finrank ℚ (LinearMap.range (kappaStar pairedM A)) = 0 ∧ Module.finrank ℚ (R pairedM A) = 1 ∧
    Module.finrank ℚ (LinearMap.range (connectingTau pairedM A)) = 0 ∧ primitiveDiagnostic pairedM A = (0,1) :=
  ⟨paired_unit_defect A hA,paired_phi_dimension_sum A hA,paired_kappaStar_rank A,paired_R_dimension A hA,paired_tau_rank A,paired_primitive_J A hA⟩

/-- 空Aを含む原Phi全Betti和。 -/
theorem allA_phi_dimension_sum (A : Set Bool) :
    letI := Fintype.ofFinite (Nc.ChartInTargetSubset A)
    ∑ c : Nc.ChartInTargetSubset A, Module.finrank ℚ (phiComplex M A c).H1 =
      @ite ℕ A.Nonempty (Classical.propDecidable _) 1 0 := by
  classical
  by_cases hA : A.Nonempty
  · rw [if_pos hA]; exact phi_dimension_sum A hA
  · rw [if_neg hA]
    have he : A = ∅ := Set.not_nonempty_iff_eq_empty.mp hA
    subst A
    exact empty_phi_dimension_sum
/-- mなしも空Aを含む同じ原Phi全Betti和。 -/
theorem allA_paired_phi_dimension_sum (A : Set Bool) :
    letI := Fintype.ofFinite (Nc.ChartInTargetSubset A)
    ∑ c : Nc.ChartInTargetSubset A, Module.finrank ℚ (phiComplex pairedM A c).H1 =
      @ite ℕ A.Nonempty (Classical.propDecidable _) 1 0 := by
  letI := Fintype.ofFinite (Nc.ChartInTargetSubset A)
  have he (c : Nc.ChartInTargetSubset A) := (pairedPhiEquiv A c).h1Equiv.finrank_eq
  simp only [he]
  exact allA_phi_dimension_sum A
/-- 空Aの原τは零の始域から零。 -/
theorem empty_tau_zero : connectingTau M ∅ = 0 := by
  letI := empty_R_subsingleton
  apply LinearMap.ext; intro x
  rw [Subsingleton.elim x 0,map_zero,LinearMap.zero_apply]
/-- 全Aの原τ rank、非空成分で同型・空成分で零。 -/
theorem allA_tau_rank (A : Set Bool) :
    Module.finrank ℚ (LinearMap.range (connectingTau M A)) =
      @ite ℕ A.Nonempty (Classical.propDecidable _) 1 0 := by
  classical
  by_cases hA : A.Nonempty
  · rw [if_pos hA]; exact tau_rank A hA
  · rw [if_neg hA]
    have he : A = ∅ := Set.not_nonempty_iff_eq_empty.mp hA
    subst A
    rw [empty_tau_zero,LinearMap.range_zero]
    exact Module.finrank_zero_of_subsingleton
/-- mなし全Aの原a欠損零。 -/
theorem allA_paired_unit_defect (A : Set Bool) : blockDefect (unitH1 pairedM A) = (0,0) :=
  (blockDefect_eq_zero_iff_bijective _).mpr (allA_paired_unit_bijective A)

end AAT.AG.AtlasCoefficientFiber.WitnessThree
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.phi_dimension
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.phi_dimension_sum
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.paired_phi_dimension_sum
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.empty_phi_dimension_sum
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.kappaStar_rank
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.paired_kappaStar_rank
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.paired_tau_rank
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.full_rank_table
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.paired_full_rank_table
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.allA_phi_dimension_sum
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.allA_paired_phi_dimension_sum
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.empty_tau_zero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.allA_tau_rank
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.allA_paired_unit_defect
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber.WitnessThree
