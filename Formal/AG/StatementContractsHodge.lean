import Formal.AG.Measurement.Hodge

noncomputable section

/-!
Fixed statement contracts for VIII.Theorems 8.5 and 8.6.
-/

namespace AAT.AG.Measurement

universe u v

section RealFiniteHodge

variable {Cminus C Cplus : Type v}
variable [NormedAddCommGroup Cminus] [InnerProductSpace ℝ Cminus]
variable [FiniteDimensional ℝ Cminus]
variable [NormedAddCommGroup C] [InnerProductSpace ℝ C]
variable [FiniteDimensional ℝ C]
variable [NormedAddCommGroup Cplus] [InnerProductSpace ℝ Cplus]
variable [FiniteDimensional ℝ Cplus]

open RealFiniteInnerProductComplex

example (K : RealFiniteInnerProductComplex Cminus C Cplus) : Submodule ℝ C := K.cycles
example (K : RealFiniteInnerProductComplex Cminus C Cplus) :
    Submodule ℝ K.cycles := K.boundariesInCycles
example (K : RealFiniteInnerProductComplex Cminus C Cplus) : Type v := K.cohomology
example (K : RealFiniteInnerProductComplex Cminus C Cplus) :
    Submodule ℝ K.cycles := K.harmonicCycles
example (K : RealFiniteInnerProductComplex Cminus C Cplus) : C →ₗ[ℝ] C := K.exactPart
example (K : RealFiniteInnerProductComplex Cminus C Cplus) : C →ₗ[ℝ] C := K.harmonicPart
example (K : RealFiniteInnerProductComplex Cminus C Cplus) : C →ₗ[ℝ] C := K.coexactPart
example (K : RealFiniteInnerProductComplex Cminus C Cplus) :
    ∀ x : C, K.laplacian x = 0 ↔ K.dPrevAdjoint x = 0 ∧ K.dNext x = 0 :=
  K.laplacian_eq_zero_iff
example (K : RealFiniteInnerProductComplex Cminus C Cplus) :
    ∀ x : C, K.exactPart x + K.harmonicPart x + K.coexactPart x = x :=
  K.hodge_decomposition
example (K : RealFiniteInnerProductComplex Cminus C Cplus) :
    ∀ x : C, K.exactPart x ∈ K.dPrev.range := K.exactPart_mem_range
example (K : RealFiniteInnerProductComplex Cminus C Cplus) :
    ∀ x : C, K.harmonicPart x ∈ K.laplacian.ker :=
  K.harmonicPart_mem_laplacian_kernel
example (K : RealFiniteInnerProductComplex Cminus C Cplus) :
    ∀ x : C, K.coexactPart x ∈ K.dNextAdjoint.range :=
  K.coexactPart_mem_adjoint_range
example (K : RealFiniteInnerProductComplex Cminus C Cplus) :
    ∀ x y : C, inner ℝ (K.exactPart x) (K.harmonicPart y) = 0 :=
  K.exact_harmonic_orthogonal
example (K : RealFiniteInnerProductComplex Cminus C Cplus) :
    ∀ x y : C, inner ℝ (K.harmonicPart x) (K.coexactPart y) = 0 :=
  K.harmonic_coexact_orthogonal
example (K : RealFiniteInnerProductComplex Cminus C Cplus) :
    ∀ x y : C, inner ℝ (K.exactPart x) (K.coexactPart y) = 0 :=
  K.exact_coexact_orthogonal
example (K : RealFiniteInnerProductComplex Cminus C Cplus) :
    K.laplacian.ker ≃ₗ[ℝ] K.cohomology := K.laplacianKernelEquivCohomology
example (K : RealFiniteInnerProductComplex Cminus C Cplus) :
    RealFiniteHodgeDecomposition K := K.derivedHodgeDecomposition
example (K : RealFiniteInnerProductComplex Cminus C Cplus) :
    K.derivedHodgeDecomposition.CohomologyClass = K.cohomology := rfl
example (K : RealFiniteInnerProductComplex Cminus C Cplus) : C → Cminus :=
  K.selectedCorrection
example (K : RealFiniteInnerProductComplex Cminus C Cplus) :
    ∀ x : C, K.dPrev (K.selectedCorrection x) = K.exactPart x :=
  K.selectedCorrection_maps_to_exactPart
example (K : RealFiniteInnerProductComplex Cminus C Cplus) :
    ∀ {g : C}, K.dNext g = 0 → ∀ c : Cminus,
      ‖K.harmonicPart g‖ ≤ ‖g - K.dPrev c‖ := by
  intro g hg c
  exact K.harmonic_norm_le_corrected hg c
example (K : RealFiniteInnerProductComplex Cminus C Cplus) :
    ∀ {g : C}, K.dNext g = 0 →
      g - K.dPrev (K.selectedCorrection g) = K.harmonicPart g := by
  intro g hg
  exact K.selected_residual_eq_harmonic hg
example (K : RealFiniteInnerProductComplex Cminus C Cplus) :
    RealHarmonicDebtMinimality K.derivedHodgeDecomposition :=
  K.derivedHarmonicDebtMinimality
example (K : RealFiniteInnerProductComplex Cminus C Cplus) :
    ∀ (x : C), K.dNext x = 0 →
      K.derivedHarmonicDebtMinimality.correctionResidual
          (K.derivedHarmonicDebtMinimality.selectedCorrection x) x =
        ‖K.derivedHodgeDecomposition.harmonicPart x‖ :=
  K.derivedHarmonicDebtMinimality.cocycle_selected_residual_eq_harmonic_norm
example (K : RealFiniteInnerProductComplex Cminus C Cplus) :
    ∀ (x : C), K.dNext x = 0 → ∀ c : Cminus,
      ‖K.derivedHodgeDecomposition.harmonicPart x‖ ≤
        K.derivedHarmonicDebtMinimality.correctionResidual c x :=
  K.derivedHarmonicDebtMinimality.cocycle_harmonic_lower_bound

end RealFiniteHodge

section GenericCellularBridge

variable {M : MeasurementProfile.{u, v}} {CM : CellularMeasurementModel M}
variable (L : SheafLaplacianReading CM)
variable {Cminus Cplus : Type v}
variable [NormedAddCommGroup Cminus] [InnerProductSpace ℝ Cminus]
variable [FiniteDimensional ℝ Cminus]
variable [NormedAddCommGroup (CM.Cochain L.degree)]
variable [InnerProductSpace ℝ (CM.Cochain L.degree)]
variable [FiniteDimensional ℝ (CM.Cochain L.degree)]
variable [NormedAddCommGroup Cplus] [InnerProductSpace ℝ Cplus]
variable [FiniteDimensional ℝ Cplus]

open RealFiniteInnerProductComplex

example (K : RealFiniteInnerProductComplex Cminus (CM.Cochain L.degree) Cplus) :
    FiniteHodgeDecompositionData L :=
  derivedFiniteHodgeDecompositionData L K

example (K : RealFiniteInnerProductComplex Cminus (CM.Cochain L.degree) Cplus) :
    FiniteHodgeDecomposition (derivedFiniteHodgeDecompositionData L K) :=
  derivedFiniteHodgeDecompositionPackage L K

example (K : RealFiniteInnerProductComplex Cminus (CM.Cochain L.degree) Cplus)
    (readNorm : CM.NormValue → ℝ)
    (readNorm_eq : ∀ x, readNorm (CM.norm L.degree x) = ‖x‖)
    (g : CM.Cochain L.degree) (hg : K.dNext g = 0) :
    HarmonicDebtMinimalityData (derivedFiniteHodgeDecompositionData L K) :=
  derivedHarmonicDebtMinimalityData L K readNorm readNorm_eq g hg

example (K : RealFiniteInnerProductComplex Cminus (CM.Cochain L.degree) Cplus)
    (readNorm : CM.NormValue → ℝ)
    (readNorm_eq : ∀ x, readNorm (CM.norm L.degree x) = ‖x‖)
    (g : CM.Cochain L.degree) (hg : K.dNext g = 0) :
    HarmonicDebtMinimality
      (derivedHarmonicDebtMinimalityData L K readNorm readNorm_eq g hg) :=
  derivedHarmonicDebtMinimalityPackage L K readNorm readNorm_eq g hg

end GenericCellularBridge

end AAT.AG.Measurement
