import Formal.AG.Measurement.Examples

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
variable [NormedAddCommGroup (CM.Cochain L.previousDegree)]
variable [InnerProductSpace ℝ (CM.Cochain L.previousDegree)]
variable [FiniteDimensional ℝ (CM.Cochain L.previousDegree)]
variable [NormedAddCommGroup (CM.Cochain L.degree)]
variable [InnerProductSpace ℝ (CM.Cochain L.degree)]
variable [FiniteDimensional ℝ (CM.Cochain L.degree)]
variable [NormedAddCommGroup (CM.Cochain L.nextDegree)]
variable [InnerProductSpace ℝ (CM.Cochain L.nextDegree)]
variable [FiniteDimensional ℝ (CM.Cochain L.nextDegree)]

open RealFiniteInnerProductComplex

example (K : RealFiniteInnerProductComplex
      (CM.Cochain L.previousDegree) (CM.Cochain L.degree)
        (CM.Cochain L.nextDegree))
    (B : CellularRealFiniteComplexComparison L K) :
    K.dPrev.toFun = L.d_prev_operator := B.dPrev_eq
example (K : RealFiniteInnerProductComplex
      (CM.Cochain L.previousDegree) (CM.Cochain L.degree)
        (CM.Cochain L.nextDegree))
    (B : CellularRealFiniteComplexComparison L K) :
    K.dNext.toFun = L.d_next_operator := B.dNext_eq
example (K : RealFiniteInnerProductComplex
      (CM.Cochain L.previousDegree) (CM.Cochain L.degree)
        (CM.Cochain L.nextDegree))
    (B : CellularRealFiniteComplexComparison L K) :
    K.dPrevAdjoint.toFun = L.d_prev_adjoint_operator := B.dPrevAdjoint_eq
example (K : RealFiniteInnerProductComplex
      (CM.Cochain L.previousDegree) (CM.Cochain L.degree)
        (CM.Cochain L.nextDegree))
    (B : CellularRealFiniteComplexComparison L K) :
    K.dNextAdjoint.toFun = L.d_next_adjoint_operator := B.dNextAdjoint_eq
example (K : RealFiniteInnerProductComplex
      (CM.Cochain L.previousDegree) (CM.Cochain L.degree)
        (CM.Cochain L.nextDegree))
    (B : CellularRealFiniteComplexComparison L K) :
    L.LaplacianOperator = (CM.Cochain L.degree →ₗ[ℝ] CM.Cochain L.degree) :=
  B.laplacianOperator_eq
example (K : RealFiniteInnerProductComplex
      (CM.Cochain L.previousDegree) (CM.Cochain L.degree)
        (CM.Cochain L.nextDegree))
    (B : CellularRealFiniteComplexComparison L K) :
    cast B.laplacianOperator_eq L.laplacian = K.laplacian := B.laplacian_eq
example (K : RealFiniteInnerProductComplex
      (CM.Cochain L.previousDegree) (CM.Cochain L.degree)
        (CM.Cochain L.nextDegree))
    (B : CellularRealFiniteComplexComparison L K) :
    ∀ x y, B.innerProductReading (CM.innerProduct L.degree x y) = inner ℝ x y :=
  B.innerProduct_eq

example (K : RealFiniteInnerProductComplex
      (CM.Cochain L.previousDegree) (CM.Cochain L.degree)
        (CM.Cochain L.nextDegree))
    (B : CellularRealFiniteComplexComparison L K) :
    FiniteHodgeDecompositionData L :=
  derivedFiniteHodgeDecompositionData L K B

example (K : RealFiniteInnerProductComplex
      (CM.Cochain L.previousDegree) (CM.Cochain L.degree)
        (CM.Cochain L.nextDegree))
    (B : CellularRealFiniteComplexComparison L K) :
    FiniteHodgeDecomposition (derivedFiniteHodgeDecompositionData L K B) :=
  derivedFiniteHodgeDecompositionPackage L K B

example (K : RealFiniteInnerProductComplex
      (CM.Cochain L.previousDegree) (CM.Cochain L.degree)
        (CM.Cochain L.nextDegree))
    (B : CellularRealFiniteComplexComparison L K)
    (readNorm : CM.NormValue → ℝ)
    (readNorm_eq : ∀ x, readNorm (CM.norm L.degree x) = ‖x‖)
    (g : CM.Cochain L.degree) (hg : K.dNext g = 0) :
    HarmonicDebtMinimalityData (derivedFiniteHodgeDecompositionData L K B) :=
  derivedHarmonicDebtMinimalityData L K B readNorm readNorm_eq g hg

example (K : RealFiniteInnerProductComplex
      (CM.Cochain L.previousDegree) (CM.Cochain L.degree)
        (CM.Cochain L.nextDegree))
    (B : CellularRealFiniteComplexComparison L K)
    (readNorm : CM.NormValue → ℝ)
    (readNorm_eq : ∀ x, readNorm (CM.norm L.degree x) = ‖x‖)
    (g : CM.Cochain L.degree) (hg : K.dNext g = 0) :
    HarmonicDebtMinimality
      (derivedHarmonicDebtMinimalityData L K B readNorm readNorm_eq g hg) :=
  derivedHarmonicDebtMinimalityPackage L K B readNorm readNorm_eq g hg

end GenericCellularBridge

section ThreeAxisFixture

example : Fin 3 → LowDegreeRealCochain := threeAxisVector
example : threeAxisRealComplex.laplacian.ker := threeAxisHarmonicKernel
example :
    RealFiniteInnerProductComplex ℝ (EuclideanSpace ℝ (Fin 3)) ℝ :=
  threeAxisRealComplex
example : threeAxisRealComplex.exactPart (threeAxisVector 0) ≠ 0 :=
  threeAxis_exactPart_nonzero
example :
    threeAxisRealComplex.coexactPart (threeAxisRealComplex.dNextAdjoint 1) ≠ 0 :=
  threeAxis_coexactPart_nonzero
example : threeAxisRealComplex.harmonicPart (threeAxisVector 1) ≠ 0 :=
  threeAxis_harmonicPart_nonzero
example :
    threeAxisRealComplex.laplacianKernelEquivCohomology
      threeAxisHarmonicKernel ≠ 0 :=
  threeAxisCohomologyClass_nonzero
example : ‖threeAxisRealComplex.harmonicPart (threeAxisVector 1)‖ = 1 :=
  threeAxis_harmonic_norm_eq_one
example :
    ‖threeAxisVector 1 - threeAxisRealComplex.dPrev
      (threeAxisRealComplex.selectedCorrection (threeAxisVector 1))‖ = 1 :=
  threeAxis_selected_residual_norm_eq_one
example (c : ℝ) :
    1 ≤ ‖threeAxisVector 1 - threeAxisRealComplex.dPrev c‖ :=
  threeAxis_harmonic_minimum c

end ThreeAxisFixture

end AAT.AG.Measurement
