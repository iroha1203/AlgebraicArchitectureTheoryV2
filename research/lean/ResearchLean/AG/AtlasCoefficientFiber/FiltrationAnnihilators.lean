import ResearchLean.AG.AtlasCoefficientFiber.FilteredComplexes

/-!
# G-135 B：原filtrationの双対端次数

## Implementation notes

非自明な核はFilteredComplexesでcarrier部分空間のannihilatorへ同定済みである。
ここでは残りの全chart、全辺、全面次数のannihilatorが実零空間であることを
同じ自由双対評価で証明し、F¹/F²/F³の各零次数を接続する。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber
open CategoryTheory CanonicalResolution ResolutionInvariance FaceRelationSubdivision
universe u

/-- 全原自由chainをannihilateするcochainは零、逆も同じ評価で成り立つ。 -/
theorem cochain_zero_iff_annihilate_all (I : Type u) (z : I → ℚ) :
    z = 0 ↔ ∀ x : I →₀ ℚ, freeDualEquiv I z x = 0 := by
  constructor
  · rintro rfl x
    rw [map_zero, LinearMap.zero_apply]
  · intro hz
    apply (freeDualEquiv I).injective
    rw [map_zero]
    exact LinearMap.ext hz

variable {Source : Type u} {qc qf : Reading Source} {h : qc.CoarserThan qf}
variable {Nc : TargetSupportedNerve.{u,u} qc} {Nf : TargetSupportedNerve.{u,u} qf}
variable (M : IncidenceSupportedComparison qc qf h Nc Nf) (A : Set qc.Target)

/-- F¹/F²/F³のchart次数は同じcarrier鎖0次annihilatorで零。 -/
theorem carrierChart_annihilator_iff (p : ℕ)
    (z : (Nf.targetSubsetComplex (comparisonFactor qc qf h ⁻¹' A)).C0) :
    z = 0 ↔ ∀ x ∈ carrierChain0 (Nf := Nf) A p, freeDualEquiv _ z x = 0 := by
  change z = 0 ↔ ∀ x ∈ (⊤ : Submodule ℚ (K0 Nf (comparisonFactor qc qf h ⁻¹' A))), _
  simpa only [Submodule.mem_top, forall_true_left] using cochain_zero_iff_annihilate_all _ z

/-- F²の辺次数はcarrier≤1全辺annihilatorで零。 -/
theorem carrierEdge_one_annihilator_iff
    (z : (Nf.targetSubsetComplex (comparisonFactor qc qf h ⁻¹' A)).C1) :
    z = 0 ↔ ∀ x ∈ carrierChain1 M A 1, freeDualEquiv _ z x = 0 := by
  change z = 0 ↔ ∀ x ∈ (⊤ : Submodule ℚ (K1 Nf (comparisonFactor qc qf h ⁻¹' A))), _
  simpa only [Submodule.mem_top, forall_true_left] using cochain_zero_iff_annihilate_all _ z

/-- F³の辺次数はcarrier≤2全辺annihilatorで零。 -/
theorem carrierEdge_two_annihilator_iff
    (z : (Nf.targetSubsetComplex (comparisonFactor qc qf h ⁻¹' A)).C1) :
    z = 0 ↔ ∀ x ∈ carrierChain1 M A 2, freeDualEquiv _ z x = 0 := by
  change z = 0 ↔ ∀ x ∈ (⊤ : Submodule ℚ (K1 Nf (comparisonFactor qc qf h ⁻¹' A))), _
  simpa only [Submodule.mem_top, forall_true_left] using cochain_zero_iff_annihilate_all _ z

/-- F³の面次数はcarrier≤2全面annihilatorで零。 -/
theorem carrierFace_two_annihilator_iff
    (z : (Nf.targetSubsetComplex (comparisonFactor qc qf h ⁻¹' A)).C2) :
    z = 0 ↔ ∀ x ∈ carrierChain2 M A 2, freeDualEquiv _ z x = 0 := by
  change z = 0 ↔ ∀ x ∈ (⊤ : Submodule ℚ (K2 Nf (comparisonFactor qc qf h ⁻¹' A))), _
  simpa only [Submodule.mem_top, forall_true_left] using cochain_zero_iff_annihilate_all _ z

end AAT.AG.AtlasCoefficientFiber
#print axioms AAT.AG.AtlasCoefficientFiber.cochain_zero_iff_annihilate_all
#print axioms AAT.AG.AtlasCoefficientFiber.carrierChart_annihilator_iff
#print axioms AAT.AG.AtlasCoefficientFiber.carrierEdge_one_annihilator_iff
#print axioms AAT.AG.AtlasCoefficientFiber.carrierEdge_two_annihilator_iff
#print axioms AAT.AG.AtlasCoefficientFiber.carrierFace_two_annihilator_iff
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber
