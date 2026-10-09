import ResearchLean.AG.AtlasCoefficientFiber.WitnessOneInput
import ResearchLean.AG.AtlasCoefficientFiber.WitnessFullSupport
import ResearchLean.AG.AtlasCoefficientFiber.MappedEvaluation

/-!
# G-135 W1：指定両比較の元fiber・L・Q・κ・τ

## Implementation notes

原Optionの全mapped条件を証明済み表から適用し、元商と実評価射を保持する。
空Aも同じ式に含む。Φの点は原chart名の両逆から生成する。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber.WitnessOne
open CategoryTheory CanonicalResolution ResolutionInvariance TwoPhase FaceRelationSubdivision
open WitnessCommon WitnessFullSupport AtlasDefectComposition

/-- W1a原Φ chartは唯一の細chartと両逆同定する。 -/
def a_phi_point (A : Set Bool) (c : Nc.ChartInTargetSubset A) : PhiChart Ma A c ≃ Fin 1 := by
  have hA : A.Nonempty := by obtain ⟨t,ht,ha⟩ := c.2; exact ⟨t,ha⟩
  exact {
    toFun v := v.1.1
    invFun i := ⟨fullSelected Na.chartSupport (fun _ => rfl) _ (fine_nonempty A hA) i,by
      apply Subtype.ext
      exact Subsingleton.elim _ _⟩
    left_inv v := by apply Subtype.ext; apply Subtype.ext; rfl
    right_inv _ := rfl }

/-- W1aの原Lは全三次数で零。 -/
theorem a_L_zero (A : Set Bool) : degenerateL0 Ma A = ⊥ ∧
    degenerateL1 Ma A = ⊥ ∧ degenerateL2 Ma A = ⊥ :=
  ⟨MappedCells.L0_eq_bot Ma A Ma_all_mapped,
    MappedCells.L1_eq_bot Ma A Ma_all_mapped Ma_faces_mapped,
    MappedCells.L2_eq_bot Ma A Ma_faces_mapped⟩

/-- W1a原Qは全三次数で零空間。 -/
theorem a_Q_zero (A : Set Bool) : Subsingleton (restrictionComplex Ma A).C0 ∧
    Subsingleton (restrictionComplex Ma A).C1 ∧ Subsingleton (restrictionComplex Ma A).C2 := by
  letI : Subsingleton (degenerateL0 Ma A) := Submodule.subsingleton_iff_eq_bot.mpr (a_L_zero A).1
  letI : Subsingleton (degenerateL1 Ma A) := Submodule.subsingleton_iff_eq_bot.mpr (a_L_zero A).2.1
  letI : Subsingleton (degenerateL2 Ma A) := Submodule.subsingleton_iff_eq_bot.mpr (a_L_zero A).2.2
  exact ⟨inferInstance,inferInstance,inferInstance⟩

/-- W1a同じ実εの全整数次数複体同型。 -/
def a_evaluation_iso (A : Set Bool) :=
  MappedCells.evaluationStandardIso Ma A Ma_all_mapped Ma_faces_mapped

/-- W1a全原Φ H¹は零、mapped loopを垂直辺へ含めない。 -/
theorem a_phi_H1_zero (A : Set Bool) (c : Nc.ChartInTargetSubset A) :
    Module.finrank ℚ (phiComplex Ma A c).H1 = 0 := by
  letI := MappedCells.phiH1_subsingleton Ma A Ma_all_mapped c
  exact Module.finrank_zero_of_subsingleton

/-- W1a混在面なしから元κは零射。 -/
theorem a_kappa_zero (A : Set Bool) : kappa Ma A = 0 := by
  letI := MappedCells.mixedFace_isEmpty Ma A Ma_faces_mapped
  haveI : Subsingleton (mixedCycles Ma A) := inferInstance
  apply LinearMap.ext
  intro z
  rw [Subsingleton.elim z 0,map_zero,LinearMap.zero_apply]

/-- W1a全原Φからの同じκ*は零射。 -/
theorem a_kappaStar_zero (A : Set Bool) : kappaStar Ma A = 0 := by
  letI (c : Nc.ChartInTargetSubset A) := MappedCells.phiH1_subsingleton Ma A Ma_all_mapped c
  apply LinearMap.ext
  intro z
  rw [Subsingleton.elim z 0,map_zero,LinearMap.zero_apply]

/-- W1a literal R=kerκ*の次元は零。 -/
theorem a_R_dimension (A : Set Bool) : Module.finrank ℚ (R Ma A) = 0 := by
  letI := MappedCells.R_subsingleton Ma A Ma_all_mapped
  exact Module.finrank_zero_of_subsingleton

/-- W1a同じ元transgressionは零。 -/
theorem a_tau_zero (A : Set Bool) : connectingTau Ma A = 0 :=
  MappedCells.tau_zero Ma A Ma_all_mapped

/-- W1a実κ*のrankは零。 -/
theorem a_kappaStar_rank (A : Set Bool) : Module.finrank ℚ (LinearMap.range (kappaStar Ma A)) = 0 := by
  rw [a_kappaStar_zero,LinearMap.range_zero]
  exact Module.finrank_zero_of_subsingleton

/-- W1a実τのrankは零。 -/
theorem a_tau_rank (A : Set Bool) : Module.finrank ℚ (LinearMap.range (connectingTau Ma A)) = 0 := by
  rw [a_tau_zero,LinearMap.range_zero]
  exact Module.finrank_zero_of_subsingleton

/-- W1b原Φ chartは唯一の細chartと両逆同定する。 -/
def b_phi_point (A : Set Bool) (c : Nc.ChartInTargetSubset A) : PhiChart Mb A c ≃ Fin 1 := by
  have hA : A.Nonempty := by obtain ⟨t,ht,ha⟩ := c.2; exact ⟨t,ha⟩
  exact {
    toFun v := v.1.1
    invFun i := ⟨fullSelected Nb.chartSupport (fun _ => rfl) _ (fine_nonempty A hA) i,by
      apply Subtype.ext
      exact Subsingleton.elim _ _⟩
    left_inv v := by apply Subtype.ext; apply Subtype.ext; rfl
    right_inv _ := rfl }

/-- W1bの原Lは全三次数で零。 -/
theorem b_L_zero (A : Set Bool) : degenerateL0 Mb A = ⊥ ∧
    degenerateL1 Mb A = ⊥ ∧ degenerateL2 Mb A = ⊥ :=
  ⟨MappedCells.L0_eq_bot Mb A Mb_all_mapped,
    MappedCells.L1_eq_bot Mb A Mb_all_mapped Mb_faces_mapped,
    MappedCells.L2_eq_bot Mb A Mb_faces_mapped⟩

/-- W1b原Qは全三次数で零空間。 -/
theorem b_Q_zero (A : Set Bool) : Subsingleton (restrictionComplex Mb A).C0 ∧
    Subsingleton (restrictionComplex Mb A).C1 ∧ Subsingleton (restrictionComplex Mb A).C2 := by
  letI : Subsingleton (degenerateL0 Mb A) := Submodule.subsingleton_iff_eq_bot.mpr (b_L_zero A).1
  letI : Subsingleton (degenerateL1 Mb A) := Submodule.subsingleton_iff_eq_bot.mpr (b_L_zero A).2.1
  letI : Subsingleton (degenerateL2 Mb A) := Submodule.subsingleton_iff_eq_bot.mpr (b_L_zero A).2.2
  exact ⟨inferInstance,inferInstance,inferInstance⟩

/-- W1b同じ実εの全整数次数複体同型。 -/
def b_evaluation_iso (A : Set Bool) :=
  MappedCells.evaluationStandardIso Mb A Mb_all_mapped Mb_faces_mapped

/-- W1b全原Φ H¹は零、mapped loopを垂直辺へ含めない。 -/
theorem b_phi_H1_zero (A : Set Bool) (c : Nc.ChartInTargetSubset A) :
    Module.finrank ℚ (phiComplex Mb A c).H1 = 0 := by
  letI := MappedCells.phiH1_subsingleton Mb A Mb_all_mapped c
  exact Module.finrank_zero_of_subsingleton

/-- W1b混在面なしから元κは零射。 -/
theorem b_kappa_zero (A : Set Bool) : kappa Mb A = 0 := by
  letI := MappedCells.mixedFace_isEmpty Mb A Mb_faces_mapped
  haveI : Subsingleton (mixedCycles Mb A) := inferInstance
  apply LinearMap.ext
  intro z
  rw [Subsingleton.elim z 0,map_zero,LinearMap.zero_apply]

/-- W1b全原Φからの同じκ*は零射。 -/
theorem b_kappaStar_zero (A : Set Bool) : kappaStar Mb A = 0 := by
  letI (c : Nc.ChartInTargetSubset A) := MappedCells.phiH1_subsingleton Mb A Mb_all_mapped c
  apply LinearMap.ext
  intro z
  rw [Subsingleton.elim z 0,map_zero,LinearMap.zero_apply]

/-- W1b literal R=kerκ*の次元は零。 -/
theorem b_R_dimension (A : Set Bool) : Module.finrank ℚ (R Mb A) = 0 := by
  letI := MappedCells.R_subsingleton Mb A Mb_all_mapped
  exact Module.finrank_zero_of_subsingleton

/-- W1b同じ元transgressionは零。 -/
theorem b_tau_zero (A : Set Bool) : connectingTau Mb A = 0 :=
  MappedCells.tau_zero Mb A Mb_all_mapped

/-- W1b実κ*のrankは零。 -/
theorem b_kappaStar_rank (A : Set Bool) : Module.finrank ℚ (LinearMap.range (kappaStar Mb A)) = 0 := by
  rw [b_kappaStar_zero,LinearMap.range_zero]
  exact Module.finrank_zero_of_subsingleton

/-- W1b実τのrankは零。 -/
theorem b_tau_rank (A : Set Bool) : Module.finrank ℚ (LinearMap.range (connectingTau Mb A)) = 0 := by
  rw [b_tau_zero,LinearMap.range_zero]
  exact Module.finrank_zero_of_subsingleton

/-- 元全chartを一つずつ保ったW1aの指定fiber Betti数和。 -/
theorem a_phi_H1_sum (A : Set Bool) :
    letI := Fintype.ofFinite (Nc.ChartInTargetSubset A)
    ∑ c : Nc.ChartInTargetSubset A, Module.finrank ℚ (phiComplex Ma A c).H1 = 0 := by
  classical
  exact Finset.sum_eq_zero (fun c _ => a_phi_H1_zero A c)

/-- 元全chartを一つずつ保ったW1bの指定fiber Betti数和。 -/
theorem b_phi_H1_sum (A : Set Bool) :
    letI := Fintype.ofFinite (Nc.ChartInTargetSubset A)
    ∑ c : Nc.ChartInTargetSubset A, Module.finrank ℚ (phiComplex Mb A c).H1 = 0 := by
  classical
  exact Finset.sum_eq_zero (fun c _ => b_phi_H1_zero A c)

end AAT.AG.AtlasCoefficientFiber.WitnessOne
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.a_phi_point
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.a_L_zero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.a_Q_zero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.a_evaluation_iso
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.a_phi_H1_zero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.a_kappa_zero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.a_kappaStar_zero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.a_R_dimension
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.a_tau_zero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.a_kappaStar_rank
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.a_tau_rank
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.b_phi_point
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.b_L_zero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.b_Q_zero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.b_evaluation_iso
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.b_phi_H1_zero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.b_kappa_zero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.b_kappaStar_zero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.b_R_dimension
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.b_tau_zero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.b_kappaStar_rank
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.b_tau_rank
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.a_phi_H1_sum
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.b_phi_H1_sum
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber.WitnessOne
