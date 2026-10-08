import ResearchLean.AG.AtlasCoefficientFiber.DefectShortExact
import ResearchLean.AG.AtlasCoefficientFiber.WitnessThreeNonzero
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# G-135 C：同じ旧診断の加法式と保存必要十分

原二射の六項列と実五項列から、同じ旧H¹比較のblockDefectへ戻す。
次元は自然数加法式を主とし、全Φ H¹の有限和を保持する。

## Implementation notes

保存条件の逆方向も原制限と完全性から証明する。τ単射性を入力幾何へ移さない。
rank式はEの有限有理行列アルゴリズムの代替ではない。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber
open CategoryTheory CanonicalResolution ResolutionInvariance FaceRelationSubdivision TwoPhase
open AtlasDefectComposition
universe u
variable {Source : Type u} {qc qf : Reading Source} {h : qc.CoarserThan qf}
variable {Nc : TargetSupportedNerve.{u,u} qc} {Nf : TargetSupportedNerve.{u,u} qf}
variable (M : IncidenceSupportedComparison qc qf h Nc Nf) (A : Set qc.Target)

/-- 同じ標準Tの欠損は既存実比較のblockDefectである。 -/
theorem directH1_defect : blockDefect (directH1 M A) =
    blockDefect (M.aSubnerveComparisonHom A).h1Map := by
  rw [directH1_eq_standard]
  exact standardH1_defect _

/-- 既存診断の第一成分は同じ原aの核次元。 -/
theorem coefficient_kernel_dimension : (blockDefect (M.aSubnerveComparisonHom A).h1Map).1 =
    Module.finrank ℚ (LinearMap.ker (unitH1 M A)) := by
  rw [← directH1_defect, blockDefect_kernel_dimension]
  exact (directKernelUnitEquiv M A).finrank_eq

/-- 同じ二射のG-133六項式は相殺零により核次元等式へ特殊化する。 -/
theorem coefficientSixTerm_kernel_dimension : Module.finrank ℚ (LinearMap.ker (directH1 M A)) =
    Module.finrank ℚ (LinearMap.ker (unitH1 M A)) := by
  have he := DefectSequence.kernel_dimension (unitH1 M A) (evaluationH1 M A)
  rw [← directH1_factor, coefficientCancellation_zero, LinearMap.range_zero,
    finrank_bot, evaluationH1_kernel, finrank_bot] at he
  simpa only [add_zero] using he

/-- 同じ二射のG-133六項式は相殺零により余核次元の加法式へ特殊化する。 -/
theorem coefficientSixTerm_cokernel_dimension :
    Module.finrank ℚ ((zeroExtension (Nf.targetSubsetComplex (comparisonFactor qc qf h ⁻¹' A))).homology (1 : ℤ) ⧸
      LinearMap.range (directH1 M A)) =
    Module.finrank ℚ ((zeroExtension (pushforwardComplex M A)).homology (1 : ℤ) ⧸ LinearMap.range (unitH1 M A)) +
    Module.finrank ℚ ((zeroExtension (Nf.targetSubsetComplex (comparisonFactor qc qf h ⁻¹' A))).homology (1 : ℤ) ⧸
      LinearMap.range (evaluationH1 M A)) := by
  have he := DefectSequence.cokernel_dimension (unitH1 M A) (evaluationH1 M A)
  rw [← directH1_factor, coefficientCancellation_zero, LinearMap.range_zero, finrank_bot] at he
  simpa only [add_zero] using he

/-- 設計§4の第一自然数加法式。余核fiber寄与はkerτである。 -/
theorem coefficient_cokernel_dimension :
    (blockDefect (M.aSubnerveComparisonHom A).h1Map).2 +
      Module.finrank ℚ (LinearMap.range (connectingTau M A)) =
    Module.finrank ℚ ((zeroExtension (pushforwardComplex M A)).homology (1 : ℤ) ⧸ LinearMap.range (unitH1 M A)) +
      Module.finrank ℚ (R M A) := by
  rw [← directH1_defect, blockDefect_cokernel_dimension]
  have he := coefficientSixTerm_cokernel_dimension M A
  have ht := (connectingTau M A).finrank_range_add_finrank_ker
  have hq := (evaluationCokernelTauKernelEquiv M A).finrank_eq
  omega

/-- 全Φ H¹の有限直和次元は原粗chartの有限和である。 -/
theorem allPhiH1_finrank_sum :
    letI := Fintype.ofFinite (Nc.ChartInTargetSubset A)
    Module.finrank ℚ ((c : Nc.ChartInTargetSubset A) → (phiComplex M A c).H1) =
      ∑ c : Nc.ChartInTargetSubset A, Module.finrank ℚ (phiComplex M A c).H1 := by
  classical
  letI := Fintype.ofFinite (Nc.ChartInTargetSubset A)
  exact Module.finrank_pi_fintype ℚ

/-- 設計§4の第二自然数加法式。原κ*のrankも同じ全Φ空間へ戻す。 -/
theorem coefficient_cokernel_kappa_dimension :
    letI := Fintype.ofFinite (Nc.ChartInTargetSubset A)
    (blockDefect (M.aSubnerveComparisonHom A).h1Map).2 +
      Module.finrank ℚ (LinearMap.range (connectingTau M A)) +
      Module.finrank ℚ (LinearMap.range (kappaStar M A)) =
    Module.finrank ℚ ((zeroExtension (pushforwardComplex M A)).homology (1 : ℤ) ⧸ LinearMap.range (unitH1 M A)) +
      ∑ c : Nc.ChartInTargetSubset A, Module.finrank ℚ (phiComplex M A c).H1 := by
  classical
  letI := Fintype.ofFinite (Nc.ChartInTargetSubset A)
  have ht := coefficient_cokernel_dimension M A
  have hk := (kappaStar M A).finrank_range_add_finrank_ker
  rw [← fiberR_eq_ker] at hk
  rw [allPhiH1_finrank_sum] at hk
  omega

/-- 整数表示の減算式は同じ第一自然数加法式から得る。 -/
theorem coefficient_cokernel_dimension_int :
    ((blockDefect (M.aSubnerveComparisonHom A).h1Map).2 : ℤ) =
    (Module.finrank ℚ ((zeroExtension (pushforwardComplex M A)).homology (1 : ℤ) ⧸ LinearMap.range (unitH1 M A)) : ℤ) +
      (Module.finrank ℚ (R M A) : ℤ) - (Module.finrank ℚ (LinearMap.range (connectingTau M A)) : ℤ) := by
  have he := coefficient_cokernel_dimension M A
  omega

/-- 実εのH¹全射性は同じτの単射性と必要十分。 -/
theorem evaluationH1_surjective_iff : Function.Surjective (evaluationH1 M A) ↔
    Function.Injective (connectingTau M A) := by
  constructor
  · intro hg r s hrs
    have hz : connectingTau M A (r-s) = 0 := by rw [map_sub, hrs, sub_self]
    obtain ⟨x, hx⟩ := (fiveTerm_exact_at_fiber M A (r-s)).mp hz
    obtain ⟨p, rfl⟩ := hg x
    have hp : fiberRestrictionH1 M A (evaluationH1 M A p) = 0 :=
      (fiveTerm_exact_at_fineH1 M A _).mpr ⟨p, rfl⟩
    exact sub_eq_zero.mp (hx.symm.trans hp)
  · intro ht x
    have hz : connectingTau M A (fiberRestrictionH1 M A x) = 0 :=
      (fiveTerm_exact_at_fiber M A _).mpr ⟨x, rfl⟩
    have hf : fiberRestrictionH1 M A x = 0 := ht (hz.trans (map_zero _).symm)
    exact (fiveTerm_exact_at_fineH1 M A x).mp hf

/-- 同じ独立Tの同型性は原aの同型性と原τ単射性に必要十分。 -/
theorem directH1_bijective_iff : Function.Bijective (directH1 M A) ↔
    Function.Bijective (unitH1 M A) ∧ Function.Injective (connectingTau M A) := by
  constructor
  · intro ht
    have hsurj : Function.Surjective (evaluationH1 M A) := by
      intro w
      obtain ⟨x, hx⟩ := ht.2 w
      refine ⟨unitH1 M A x, ?_⟩
      rw [directH1_factor, LinearMap.comp_apply] at hx
      exact hx
    refine ⟨⟨?_, ?_⟩, (evaluationH1_surjective_iff M A).mp hsurj⟩
    · intro x y hxy
      apply ht.1
      rw [directH1_factor, LinearMap.comp_apply, LinearMap.comp_apply, hxy]
    · intro p
      obtain ⟨x, hx⟩ := ht.2 (evaluationH1 M A p)
      rw [directH1_factor, LinearMap.comp_apply] at hx
      exact ⟨x, evaluationH1_injective M A hx⟩
  · rintro ⟨ha, ht⟩
    rw [directH1_factor]
    have hg : Function.Bijective (evaluationH1 M A) :=
      ⟨evaluationH1_injective M A, (evaluationH1_surjective_iff M A).mpr ht⟩
    exact hg.comp ha

/-- 指定J=0 iff a同型かつτ単射は同じ既存blockDefectの両成分に対する必要十分。 -/
theorem coefficient_zeroDefect_iff : blockDefect (M.aSubnerveComparisonHom A).h1Map = (0,0) ↔
    Function.Bijective (unitH1 M A) ∧ Function.Injective (connectingTau M A) := by
  rw [← directH1_defect, blockDefect_eq_zero_iff_bijective, directH1_bijective_iff]

/-- 同じ旧零診断から原aの両方向線形同型を生成する。 -/
def unitH1EquivOfZeroDefect (hJ : blockDefect (M.aSubnerveComparisonHom A).h1Map = (0,0)) :
    (zeroExtension (Nc.targetSubsetComplex A)).homology (1 : ℤ) ≃ₗ[ℚ]
      (zeroExtension (pushforwardComplex M A)).homology (1 : ℤ) :=
  LinearEquiv.ofBijective (unitH1 M A) ((coefficient_zeroDefect_iff M A).mp hJ).1

/-- 生成した同型の順写像は同じ原aである。 -/
@[simp] theorem unitH1EquivOfZeroDefect_apply
    (hJ : blockDefect (M.aSubnerveComparisonHom A).h1Map = (0,0))
    (x : (zeroExtension (Nc.targetSubsetComplex A)).homology (1 : ℤ)) :
    unitH1EquivOfZeroDefect M A hJ x = unitH1 M A x := rfl

/-- 同じ旧零診断から実τの核零性を生成する。 -/
theorem tauKernel_eq_bot_of_zeroDefect
    (hJ : blockDefect (M.aSubnerveComparisonHom A).h1Map = (0,0)) :
    LinearMap.ker (connectingTau M A) = ⊥ :=
  LinearMap.ker_eq_bot.mpr ((coefficient_zeroDefect_iff M A).mp hJ).2

/-- 同じ指定W3入力ではG-133相殺は零で、別の原τは非零である。 -/
theorem witnessThree_cancellation_zero_and_tau_ne_zero :
    DefectSequence.cancellation (unitH1 WitnessThree.M Set.univ)
      (evaluationH1 WitnessThree.M Set.univ) = 0 ∧
      connectingTau WitnessThree.M Set.univ ≠ 0 :=
  ⟨coefficientCancellation_zero WitnessThree.M Set.univ, WitnessThree.connectingTau_ne_zero⟩

end AAT.AG.AtlasCoefficientFiber

#print axioms AAT.AG.AtlasCoefficientFiber.directH1_defect
#print axioms AAT.AG.AtlasCoefficientFiber.coefficient_kernel_dimension
#print axioms AAT.AG.AtlasCoefficientFiber.coefficientSixTerm_kernel_dimension
#print axioms AAT.AG.AtlasCoefficientFiber.coefficientSixTerm_cokernel_dimension
#print axioms AAT.AG.AtlasCoefficientFiber.coefficient_cokernel_dimension
#print axioms AAT.AG.AtlasCoefficientFiber.allPhiH1_finrank_sum
#print axioms AAT.AG.AtlasCoefficientFiber.coefficient_cokernel_kappa_dimension
#print axioms AAT.AG.AtlasCoefficientFiber.coefficient_cokernel_dimension_int
#print axioms AAT.AG.AtlasCoefficientFiber.evaluationH1_surjective_iff
#print axioms AAT.AG.AtlasCoefficientFiber.directH1_bijective_iff
#print axioms AAT.AG.AtlasCoefficientFiber.coefficient_zeroDefect_iff
#print axioms AAT.AG.AtlasCoefficientFiber.unitH1EquivOfZeroDefect
#print axioms AAT.AG.AtlasCoefficientFiber.unitH1EquivOfZeroDefect_apply
#print axioms AAT.AG.AtlasCoefficientFiber.tauKernel_eq_bot_of_zeroDefect
#print axioms AAT.AG.AtlasCoefficientFiber.witnessThree_cancellation_zero_and_tau_ne_zero
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber
