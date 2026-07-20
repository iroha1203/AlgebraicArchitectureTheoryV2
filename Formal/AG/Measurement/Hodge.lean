import Formal.AG.Measurement.CellularLaplacian
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.LinearAlgebra.Projection

noncomputable section

namespace AAT.AG
namespace Measurement

universe u v

/-!
Part VIII R6 / AC14-AC16 finite Hodge, harmonic debt, repair lower bound, and
spectral reading surfaces.

The theorem packages are relative to explicit finite inner-product cochain
model data. They do not assert general Hilbert complex theory or derive
lawfulness from small analytic residuals.
-/

/-- VIII.Theorem 8.5 supporting data for a selected finite Hodge decomposition. -/
structure FiniteHodgeDecompositionData {M : MeasurementProfile.{u, v}}
    {C : CellularMeasurementModel M} (L : SheafLaplacianReading C) where
  HarmonicRepresentative : Type v
  CohomologyClass : Type v
  ExactComponent : Type v
  CoexactComponent : Type v
  KernelPredicate : C.Cochain L.degree -> Prop
  harmonicProjection : C.Cochain L.degree -> HarmonicRepresentative
  cohomologyClassOf : C.Cochain L.degree -> CohomologyClass
  exactComponentOf : C.Cochain L.degree -> ExactComponent
  coexactComponentOf : C.Cochain L.degree -> CoexactComponent
  harmonicComponentOf : C.Cochain L.degree -> HarmonicRepresentative
  harmonicRepresentativeAsCochain : HarmonicRepresentative -> C.Cochain L.degree
  harmonicInKernel :
    (h : HarmonicRepresentative) -> KernelPredicate (harmonicRepresentativeAsCochain h)
  cohomologyOfHarmonic : HarmonicRepresentative -> CohomologyClass
  kernelReadsLaplacian : Prop
  kernelReadsLaplacian_cert : kernelReadsLaplacian
  decompositionMapsReadCochain : Prop
  decompositionMapsReadCochain_cert : decompositionMapsReadCochain
  cohomologyEquivHarmonic : Prop
  cohomologyEquivHarmonic_cert : cohomologyEquivHarmonic
  finiteHodgeDecomposition : Prop
  finiteHodgeDecomposition_cert : finiteHodgeDecomposition
  harmonicKernelIdentifiesCohomology : Prop
  harmonicKernelIdentifiesCohomology_cert : harmonicKernelIdentifiesCohomology
  exactCoexactHarmonicOrthogonal : Prop
  exactCoexactHarmonicOrthogonal_cert : exactCoexactHarmonicOrthogonal

/-- VIII.Theorem 8.5: finite Hodge decomposition theorem package. -/
structure FiniteHodgeDecomposition {M : MeasurementProfile.{u, v}}
    {C : CellularMeasurementModel M} {L : SheafLaplacianReading C}
    (D : FiniteHodgeDecompositionData L) where
  kernel_reads_laplacian_holds : D.kernelReadsLaplacian
  decomposition_maps_read_cochain_holds : D.decompositionMapsReadCochain
  cohomology_equiv_harmonic_holds : D.cohomologyEquivHarmonic
  decomposition_holds : D.finiteHodgeDecomposition
  harmonic_cohomology_holds : D.harmonicKernelIdentifiesCohomology
  orthogonal_decomposition_holds : D.exactCoexactHarmonicOrthogonal

namespace FiniteHodgeDecomposition

/-- VIII.Theorem 8.5: expose that `ker L_n` is the selected harmonic predicate. -/
theorem kernel_reads_laplacian_holds_of_package {M : MeasurementProfile.{u, v}}
    {C : CellularMeasurementModel M} {L : SheafLaplacianReading C}
    {D : FiniteHodgeDecompositionData L} (T : FiniteHodgeDecomposition D) :
    D.kernelReadsLaplacian :=
  T.kernel_reads_laplacian_holds

/-- VIII.Theorem 8.5: expose the selected exact/coexact/harmonic cochain maps. -/
theorem decomposition_maps_read_cochain_holds_of_package {M : MeasurementProfile.{u, v}}
    {C : CellularMeasurementModel M} {L : SheafLaplacianReading C}
    {D : FiniteHodgeDecompositionData L} (T : FiniteHodgeDecomposition D) :
    D.decompositionMapsReadCochain :=
  T.decomposition_maps_read_cochain_holds

/-- VIII.Theorem 8.5: expose `C^n = im d_{n-1} ⊕ ker L_n ⊕ im d_n^*`. -/
theorem decomposition_holds_of_package {M : MeasurementProfile.{u, v}}
    {C : CellularMeasurementModel M} {L : SheafLaplacianReading C}
    {D : FiniteHodgeDecompositionData L} (T : FiniteHodgeDecomposition D) :
    D.finiteHodgeDecomposition :=
  T.decomposition_holds

/-- VIII.Theorem 8.5: expose `ker L_n` as selected cohomology representatives. -/
theorem harmonic_cohomology_holds_of_package {M : MeasurementProfile.{u, v}}
    {C : CellularMeasurementModel M} {L : SheafLaplacianReading C}
    {D : FiniteHodgeDecompositionData L} (T : FiniteHodgeDecomposition D) :
    D.harmonicKernelIdentifiesCohomology :=
  T.harmonic_cohomology_holds

/-- VIII.Theorem 8.5: expose the selected harmonic representative/cohomology equivalence. -/
theorem cohomology_equiv_harmonic_holds_of_package {M : MeasurementProfile.{u, v}}
    {C : CellularMeasurementModel M} {L : SheafLaplacianReading C}
    {D : FiniteHodgeDecompositionData L} (T : FiniteHodgeDecomposition D) :
    D.cohomologyEquivHarmonic :=
  T.cohomology_equiv_harmonic_holds

end FiniteHodgeDecomposition

/-- VIII.Theorem 8.5: construct the selected finite Hodge theorem package. -/
def finiteHodgeDecompositionPackage {M : MeasurementProfile.{u, v}}
    {C : CellularMeasurementModel M} {L : SheafLaplacianReading C}
    (D : FiniteHodgeDecompositionData L) :
    FiniteHodgeDecomposition D where
  kernel_reads_laplacian_holds := D.kernelReadsLaplacian_cert
  decomposition_maps_read_cochain_holds := D.decompositionMapsReadCochain_cert
  cohomology_equiv_harmonic_holds := D.cohomologyEquivHarmonic_cert
  decomposition_holds := D.finiteHodgeDecomposition_cert
  harmonic_cohomology_holds := D.harmonicKernelIdentifiesCohomology_cert
  orthogonal_decomposition_holds := D.exactCoexactHarmonicOrthogonal_cert

/-- VIII.Theorem 8.5: selected finite Hodge package exists under explicit data. -/
theorem finiteHodgeDecomposition {M : MeasurementProfile.{u, v}}
    {C : CellularMeasurementModel M} {L : SheafLaplacianReading C}
    (D : FiniteHodgeDecompositionData L) :
    Nonempty (FiniteHodgeDecomposition D) :=
  ⟨finiteHodgeDecompositionPackage D⟩

/-- VIII.Theorem 8.6 supporting data for harmonic debt minimality. -/
structure HarmonicDebtMinimalityData {M : MeasurementProfile.{u, v}}
    {C : CellularMeasurementModel M} {L : SheafLaplacianReading C}
    (D : FiniteHodgeDecompositionData L) where
  GaugeCorrection : Type v
  correctionAction : GaugeCorrection -> C.Cochain L.degree
  correctedMismatch : GaugeCorrection -> C.Cochain L.degree
  correctionResidual : GaugeCorrection -> C.NormValue
  selectedMinimumCorrection : GaugeCorrection
  debtNorm : C.Cochain L.degree -> C.NormValue
  harmonicDebt : C.Cochain L.degree -> C.NormValue
  harmonicNorm : D.HarmonicRepresentative -> C.NormValue
  selectedMismatch : C.Cochain L.degree
  harmonicRepresentative : D.HarmonicRepresentative
  harmonicDebtValue : C.NormValue
  projectionReadsHarmonicRepresentative : Prop
  projectionReadsHarmonicRepresentative_cert : projectionReadsHarmonicRepresentative
  minimumReadsCorrectionResidual : Prop
  minimumReadsCorrectionResidual_cert : minimumReadsCorrectionResidual
  harmonicDebt_eq_harmonicNorm : Prop
  harmonicDebt_eq_harmonicNorm_cert : harmonicDebt_eq_harmonicNorm
  minimizationStatement : Prop
  minimizationStatement_cert : minimizationStatement

/-- VIII.Theorem 8.6: harmonic debt minimality theorem package. -/
structure HarmonicDebtMinimality {M : MeasurementProfile.{u, v}}
    {C : CellularMeasurementModel M} {L : SheafLaplacianReading C}
    {D : FiniteHodgeDecompositionData L} (H : HarmonicDebtMinimalityData D) where
  projectionReadsHarmonicRepresentative_holds :
    H.projectionReadsHarmonicRepresentative
  minimum_reads_correction_residual_holds :
    H.minimumReadsCorrectionResidual
  harmonic_debt_eq_harmonic_norm_holds :
    H.harmonicDebt_eq_harmonicNorm
  minimization_holds : H.minimizationStatement

namespace HarmonicDebtMinimality

/-- VIII.Theorem 8.6: expose that the selected minimum is read from correction residuals. -/
theorem minimum_reads_correction_residual_holds_of_package {M : MeasurementProfile.{u, v}}
    {C : CellularMeasurementModel M} {L : SheafLaplacianReading C}
    {D : FiniteHodgeDecompositionData L} {H : HarmonicDebtMinimalityData D}
    (T : HarmonicDebtMinimality H) : H.minimumReadsCorrectionResidual :=
  T.minimum_reads_correction_residual_holds

/-- VIII.Theorem 8.6: expose that debt is the norm of the selected harmonic part. -/
theorem harmonic_debt_eq_harmonic_norm_holds_of_package {M : MeasurementProfile.{u, v}}
    {C : CellularMeasurementModel M} {L : SheafLaplacianReading C}
    {D : FiniteHodgeDecompositionData L} {H : HarmonicDebtMinimalityData D}
    (T : HarmonicDebtMinimality H) : H.harmonicDebt_eq_harmonicNorm :=
  T.harmonic_debt_eq_harmonic_norm_holds

/-- VIII.Theorem 8.6: expose selected harmonic debt minimality. -/
theorem minimization_holds_of_package {M : MeasurementProfile.{u, v}}
    {C : CellularMeasurementModel M} {L : SheafLaplacianReading C}
    {D : FiniteHodgeDecompositionData L} {H : HarmonicDebtMinimalityData D}
    (T : HarmonicDebtMinimality H) : H.minimizationStatement :=
  T.minimization_holds

end HarmonicDebtMinimality

/-- VIII.Theorem 8.6: construct the selected harmonic debt minimality package. -/
def harmonicDebtMinimalityPackage {M : MeasurementProfile.{u, v}}
    {C : CellularMeasurementModel M} {L : SheafLaplacianReading C}
    {D : FiniteHodgeDecompositionData L} (H : HarmonicDebtMinimalityData D) :
    HarmonicDebtMinimality H where
  projectionReadsHarmonicRepresentative_holds :=
    H.projectionReadsHarmonicRepresentative_cert
  minimum_reads_correction_residual_holds :=
    H.minimumReadsCorrectionResidual_cert
  harmonic_debt_eq_harmonic_norm_holds :=
    H.harmonicDebt_eq_harmonicNorm_cert
  minimization_holds := H.minimizationStatement_cert

/-- VIII.Theorem 8.6: selected harmonic debt minimality exists under explicit data. -/
theorem harmonicDebtMinimality {M : MeasurementProfile.{u, v}}
    {C : CellularMeasurementModel M} {L : SheafLaplacianReading C}
    {D : FiniteHodgeDecompositionData L} (H : HarmonicDebtMinimalityData D) :
    Nonempty (HarmonicDebtMinimality H) :=
  ⟨harmonicDebtMinimalityPackage H⟩

/-- VIII.Corollary 8.7 supporting data for the essential repair lower bound. -/
structure EssentialRepairLowerBoundData {M : MeasurementProfile.{u, v}}
    {C : CellularMeasurementModel M} {L : SheafLaplacianReading C}
    {D : FiniteHodgeDecompositionData L} (H : HarmonicDebtMinimalityData D) where
  RepairRoute : Type u
  RepairCostValue : Type v
  LipschitzConstant : Type v
  LowerBoundExpression : Type v
  repairCost : RepairRoute -> RepairCostValue
  lipschitzConstant : LipschitzConstant
  selectedRepairRoute : RepairRoute
  harmonicDebtValue : C.NormValue
  lowerBoundExpression : LowerBoundExpression
  lipschitzAssumption : Prop
  lipschitzAssumption_cert : lipschitzAssumption
  routeResolvesHarmonicMismatch : Prop
  routeResolvesHarmonicMismatch_cert : routeResolvesHarmonicMismatch
  lowerBoundReads_harmonicDebt_over_L : Prop
  lowerBoundReads_harmonicDebt_over_L_cert : lowerBoundReads_harmonicDebt_over_L
  lowerBoundStatement : Prop
  lowerBoundStatement_cert : lowerBoundStatement

/-- VIII.Corollary 8.7: essential repair lower bound package. -/
structure EssentialRepairLowerBound {M : MeasurementProfile.{u, v}}
    {C : CellularMeasurementModel M} {L : SheafLaplacianReading C}
    {D : FiniteHodgeDecompositionData L} {H : HarmonicDebtMinimalityData D}
    (B : EssentialRepairLowerBoundData H) where
  lipschitz_holds : B.lipschitzAssumption
  route_resolves_holds : B.routeResolvesHarmonicMismatch
  lower_bound_reads_harmonic_debt_over_L_holds :
    B.lowerBoundReads_harmonicDebt_over_L
  lowerBound_holds : B.lowerBoundStatement

namespace EssentialRepairLowerBound

/-- VIII.Corollary 8.7: expose the selected `harmonic debt / L` lower-bound reading. -/
theorem lower_bound_reads_harmonic_debt_over_L_holds_of_package
    {M : MeasurementProfile.{u, v}}
    {C : CellularMeasurementModel M} {L : SheafLaplacianReading C}
    {D : FiniteHodgeDecompositionData L} {H : HarmonicDebtMinimalityData D}
    {B : EssentialRepairLowerBoundData H} (T : EssentialRepairLowerBound B) :
    B.lowerBoundReads_harmonicDebt_over_L :=
  T.lower_bound_reads_harmonic_debt_over_L_holds

/-- VIII.Corollary 8.7: expose the selected repair lower bound. -/
theorem lowerBound_holds_of_package {M : MeasurementProfile.{u, v}}
    {C : CellularMeasurementModel M} {L : SheafLaplacianReading C}
    {D : FiniteHodgeDecompositionData L} {H : HarmonicDebtMinimalityData D}
    {B : EssentialRepairLowerBoundData H} (T : EssentialRepairLowerBound B) :
    B.lowerBoundStatement :=
  T.lowerBound_holds

end EssentialRepairLowerBound

/-- VIII.Corollary 8.7: construct the selected essential repair lower bound package. -/
def essentialRepairLowerBoundPackage {M : MeasurementProfile.{u, v}}
    {C : CellularMeasurementModel M} {L : SheafLaplacianReading C}
    {D : FiniteHodgeDecompositionData L} {H : HarmonicDebtMinimalityData D}
    (B : EssentialRepairLowerBoundData H) :
    EssentialRepairLowerBound B where
  lipschitz_holds := B.lipschitzAssumption_cert
  route_resolves_holds := B.routeResolvesHarmonicMismatch_cert
  lower_bound_reads_harmonic_debt_over_L_holds :=
    B.lowerBoundReads_harmonicDebt_over_L_cert
  lowerBound_holds := B.lowerBoundStatement_cert

/-- VIII.Corollary 8.7: selected repair lower bound exists under explicit data. -/
theorem essentialRepairLowerBound {M : MeasurementProfile.{u, v}}
    {C : CellularMeasurementModel M} {L : SheafLaplacianReading C}
    {D : FiniteHodgeDecompositionData L} {H : HarmonicDebtMinimalityData D}
    (B : EssentialRepairLowerBoundData H) :
    Nonempty (EssentialRepairLowerBound B) :=
  ⟨essentialRepairLowerBoundPackage B⟩

/-! ### peer-review hardening VIII-1: finite real inner-product Hodge bridge -/

/--
VIII.Theorem 8.5 hardening: a finite real inner-product cochain fragment.

This is the load-bearing Mathlib-facing surface used by peer-review hardening AC15.  The
cochain spaces are actual finite-dimensional real inner-product spaces, the
differentials are `LinearMap`s, and `d_next ∘ d_prev = 0` is an equality.
-/
structure RealFiniteInnerProductComplex
    (Cminus C Cplus : Type v)
    [NormedAddCommGroup Cminus] [InnerProductSpace ℝ Cminus]
    [FiniteDimensional ℝ Cminus]
    [NormedAddCommGroup C] [InnerProductSpace ℝ C] [FiniteDimensional ℝ C]
    [NormedAddCommGroup Cplus] [InnerProductSpace ℝ Cplus]
    [FiniteDimensional ℝ Cplus] where
  dPrev : Cminus →ₗ[ℝ] C
  dNext : C →ₗ[ℝ] Cplus
  d_comp_d : dNext.comp dPrev = 0

namespace RealFiniteInnerProductComplex

variable {Cminus C Cplus : Type v}
variable [NormedAddCommGroup Cminus] [InnerProductSpace ℝ Cminus]
variable [FiniteDimensional ℝ Cminus]
variable [NormedAddCommGroup C] [InnerProductSpace ℝ C] [FiniteDimensional ℝ C]
variable [NormedAddCommGroup Cplus] [InnerProductSpace ℝ Cplus]
variable [FiniteDimensional ℝ Cplus]

/-- VIII.Theorem 8.5 hardening: the Mathlib adjoint of `dPrev`. -/
def dPrevAdjoint (K : RealFiniteInnerProductComplex Cminus C Cplus) :
    C →ₗ[ℝ] Cminus :=
  LinearMap.adjoint K.dPrev

/-- VIII.Theorem 8.5 hardening: the Mathlib adjoint of `dNext`. -/
def dNextAdjoint (K : RealFiniteInnerProductComplex Cminus C Cplus) :
    Cplus →ₗ[ℝ] C :=
  LinearMap.adjoint K.dNext

/-- VIII.Theorem 8.5 hardening: the finite Hodge Laplacian `dd* + d*d`. -/
def laplacian (K : RealFiniteInnerProductComplex Cminus C Cplus) :
    C →ₗ[ℝ] C :=
  K.dPrev.comp K.dPrevAdjoint + K.dNextAdjoint.comp K.dNext

/-- VIII.Theorem 8.5: cocycles in the selected degree. -/
def cycles (K : RealFiniteInnerProductComplex Cminus C Cplus) : Submodule ℝ C :=
  K.dNext.ker

/-- VIII.Theorem 8.5: boundaries, regarded as a subspace of cocycles. -/
def boundariesInCycles (K : RealFiniteInnerProductComplex Cminus C Cplus) :
    Submodule ℝ K.cycles :=
  K.dPrev.range.comap K.cycles.subtype

/-- VIII.Theorem 8.5: cohomology is the quotient of cocycles by boundaries. -/
def cohomology (K : RealFiniteInnerProductComplex Cminus C Cplus) :=
  K.cycles ⧸ K.boundariesInCycles

noncomputable instance cohomologyAddCommGroup
    (K : RealFiniteInnerProductComplex Cminus C Cplus) : AddCommGroup K.cohomology := by
  dsimp only [cohomology]
  infer_instance

noncomputable instance cohomologyModule
    (K : RealFiniteInnerProductComplex Cminus C Cplus) : Module ℝ K.cohomology := by
  dsimp only [cohomology]
  infer_instance

/-- VIII.Theorem 8.5: harmonic cocycles are the orthogonal complement of boundaries in cycles. -/
def harmonicCycles (K : RealFiniteInnerProductComplex Cminus C Cplus) :
    Submodule ℝ K.cycles :=
  K.boundariesInCyclesᗮ

/-- VIII.Theorem 8.5: the exact component is orthogonal projection onto `im dPrev`. -/
noncomputable def exactPart (K : RealFiniteInnerProductComplex Cminus C Cplus) :
    C →ₗ[ℝ] C :=
  K.dPrev.range.starProjection.toLinearMap

/-- VIII.Theorem 8.5: the coexact component is orthogonal projection onto `im dNextAdjoint`. -/
noncomputable def coexactPart (K : RealFiniteInnerProductComplex Cminus C Cplus) :
    C →ₗ[ℝ] C :=
  K.dNextAdjoint.range.starProjection.toLinearMap

/-- VIII.Theorem 8.5: the harmonic component left after exact and coexact projection. -/
noncomputable def harmonicPart (K : RealFiniteInnerProductComplex Cminus C Cplus) :
    C →ₗ[ℝ] C :=
  LinearMap.id - K.exactPart - K.coexactPart

/-- The complex equation evaluated on one cochain. -/
theorem dNext_dPrev (K : RealFiniteInnerProductComplex Cminus C Cplus) (x : Cminus) :
    K.dNext (K.dPrev x) = 0 := by
  have h := LinearMap.congr_fun K.d_comp_d x
  simpa using h

/-- The exact and coexact ranges are orthogonal, derived from `dNext ∘ dPrev = 0`. -/
theorem exactRange_isOrtho_coexactRange
    (K : RealFiniteInnerProductComplex Cminus C Cplus) :
    K.dPrev.range ⟂ K.dNextAdjoint.range := by
  rw [Submodule.isOrtho_iff_inner_eq]
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
  rw [dNextAdjoint, LinearMap.adjoint_inner_right K.dNext]
  simp [K.dNext_dPrev]

/-- VIII.Theorem 8.5: the exact projection lands in `im dPrev`. -/
theorem exactPart_mem_range
    (K : RealFiniteInnerProductComplex Cminus C Cplus) (x : C) :
    K.exactPart x ∈ K.dPrev.range := by
  exact Submodule.starProjection_apply_mem _ _

/-- VIII.Theorem 8.5: the coexact projection lands in `im dNextAdjoint`. -/
theorem coexactPart_mem_adjoint_range
    (K : RealFiniteInnerProductComplex Cminus C Cplus) (x : C) :
    K.coexactPart x ∈ K.dNextAdjoint.range := by
  exact Submodule.starProjection_apply_mem _ _

/-- VIII.Theorem 8.5: exact and coexact components are orthogonal. -/
theorem exact_coexact_orthogonal
    (K : RealFiniteInnerProductComplex Cminus C Cplus) (x y : C) :
    inner ℝ (K.exactPart x) (K.coexactPart y) = 0 :=
  K.exactRange_isOrtho_coexactRange.inner_eq
    (K.exactPart_mem_range x) (K.coexactPart_mem_adjoint_range y)

/-- VIII.Theorem 8.5: the three derived components sum to the original cochain. -/
theorem hodge_decomposition
    (K : RealFiniteInnerProductComplex Cminus C Cplus) (x : C) :
    K.exactPart x + K.harmonicPart x + K.coexactPart x = x := by
  simp only [harmonicPart, LinearMap.sub_apply, LinearMap.id_apply]
  abel

/-- A vector and its exact-projection residual are orthogonal. -/
theorem exactPart_inner_residual
    (K : RealFiniteInnerProductComplex Cminus C Cplus) (x y : C) :
    inner ℝ (K.exactPart x) (y - K.exactPart y) = 0 := by
  rw [real_inner_comm]
  exact K.dPrev.range.starProjection_inner_eq_zero y _ (K.exactPart_mem_range x)

/-- VIII.Theorem 8.5: exact and harmonic components are orthogonal. -/
theorem exact_harmonic_orthogonal
    (K : RealFiniteInnerProductComplex Cminus C Cplus) (x y : C) :
    inner ℝ (K.exactPart x) (K.harmonicPart y) = 0 := by
  rw [show K.harmonicPart y = y - K.exactPart y - K.coexactPart y by
    simp [harmonicPart]]
  rw [inner_sub_right, K.exactPart_inner_residual x y,
    K.exact_coexact_orthogonal x y, sub_zero]

/-- A vector and its coexact-projection residual are orthogonal. -/
theorem residual_inner_coexactPart
    (K : RealFiniteInnerProductComplex Cminus C Cplus) (x y : C) :
    inner ℝ (x - K.coexactPart x) (K.coexactPart y) = 0 :=
  K.dNextAdjoint.range.starProjection_inner_eq_zero x _
    (K.coexactPart_mem_adjoint_range y)

/-- VIII.Theorem 8.5: harmonic and coexact components are orthogonal. -/
theorem harmonic_coexact_orthogonal
    (K : RealFiniteInnerProductComplex Cminus C Cplus) (x y : C) :
    inner ℝ (K.harmonicPart x) (K.coexactPart y) = 0 := by
  rw [show K.harmonicPart x = x - K.coexactPart x - K.exactPart x by
    simp [harmonicPart, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]]
  rw [inner_sub_left, K.residual_inner_coexactPart x y,
    K.exact_coexact_orthogonal x y, zero_sub, neg_zero]

/-- VIII.Theorem 8.5 hardening: `dPrevAdjoint` is the Mathlib adjoint. -/
theorem dPrev_adjoint_inner_right
    (K : RealFiniteInnerProductComplex Cminus C Cplus) (x : Cminus) (y : C) :
    inner ℝ x (K.dPrevAdjoint y) = inner ℝ (K.dPrev x) y :=
  LinearMap.adjoint_inner_right K.dPrev x y

/-- VIII.Theorem 8.5 hardening: `dNextAdjoint` is the Mathlib adjoint. -/
theorem dNext_adjoint_inner_right
    (K : RealFiniteInnerProductComplex Cminus C Cplus) (x : C) (y : Cplus) :
    inner ℝ x (K.dNextAdjoint y) = inner ℝ (K.dNext x) y :=
  LinearMap.adjoint_inner_right K.dNext x y

/-- The harmonic component lies in the orthogonal complement of `im dPrev`. -/
theorem harmonicPart_mem_exactRange_orthogonal
    (K : RealFiniteInnerProductComplex Cminus C Cplus) (x : C) :
    K.harmonicPart x ∈ K.dPrev.rangeᗮ := by
  rw [show K.harmonicPart x = (x - K.exactPart x) - K.coexactPart x by
    simp [harmonicPart]]
  apply Submodule.sub_mem
  · exact K.dPrev.range.sub_starProjection_mem_orthogonal x
  · exact K.exactRange_isOrtho_coexactRange.ge (K.coexactPart_mem_adjoint_range x)

/-- The harmonic component lies in the orthogonal complement of `im dNextAdjoint`. -/
theorem harmonicPart_mem_coexactRange_orthogonal
    (K : RealFiniteInnerProductComplex Cminus C Cplus) (x : C) :
    K.harmonicPart x ∈ K.dNextAdjoint.rangeᗮ := by
  rw [show K.harmonicPart x = (x - K.coexactPart x) - K.exactPart x by
    simp [harmonicPart, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]]
  apply Submodule.sub_mem
  · exact K.dNextAdjoint.range.sub_starProjection_mem_orthogonal x
  · exact K.exactRange_isOrtho_coexactRange.le (K.exactPart_mem_range x)

/-- The harmonic component is killed by the previous adjoint. -/
theorem dPrevAdjoint_harmonicPart_eq_zero
    (K : RealFiniteInnerProductComplex Cminus C Cplus) (x : C) :
    K.dPrevAdjoint (K.harmonicPart x) = 0 := by
  have hinner :
      inner ℝ (K.dPrevAdjoint (K.harmonicPart x))
        (K.dPrevAdjoint (K.harmonicPart x)) = 0 := by
    rw [K.dPrev_adjoint_inner_right]
    exact K.harmonicPart_mem_exactRange_orthogonal x _ ⟨_, rfl⟩
  have hnormSq : ‖K.dPrevAdjoint (K.harmonicPart x)‖ ^ 2 = 0 := by
    simpa [real_inner_self_eq_norm_sq] using hinner
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hnormSq)

/-- The harmonic component is a cocycle. -/
theorem dNext_harmonicPart_eq_zero
    (K : RealFiniteInnerProductComplex Cminus C Cplus) (x : C) :
    K.dNext (K.harmonicPart x) = 0 := by
  have hinner :
      inner ℝ (K.dNext (K.harmonicPart x)) (K.dNext (K.harmonicPart x)) = 0 := by
    rw [← K.dNext_adjoint_inner_right, real_inner_comm]
    exact K.harmonicPart_mem_coexactRange_orthogonal x _ ⟨_, rfl⟩
  have hnormSq : ‖K.dNext (K.harmonicPart x)‖ ^ 2 = 0 := by
    simpa [real_inner_self_eq_norm_sq] using hinner
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hnormSq)

/-- The Laplacian quadratic form is the sum of the two differential norm squares. -/
theorem inner_laplacian_self
    (K : RealFiniteInnerProductComplex Cminus C Cplus) (x : C) :
    inner ℝ x (K.laplacian x) =
      inner ℝ (K.dPrevAdjoint x) (K.dPrevAdjoint x) +
        inner ℝ (K.dNext x) (K.dNext x) := by
  calc
    inner ℝ x (K.laplacian x) =
        inner ℝ x (K.dPrev (K.dPrevAdjoint x)) +
          inner ℝ x (K.dNextAdjoint (K.dNext x)) := by
      simp [laplacian, inner_add_right]
    _ = inner ℝ (K.dPrevAdjoint x) (K.dPrevAdjoint x) +
          inner ℝ (K.dNext x) (K.dNext x) := by
      congr 1
      · calc
          inner ℝ x (K.dPrev (K.dPrevAdjoint x)) =
              inner ℝ (K.dPrev (K.dPrevAdjoint x)) x :=
            real_inner_comm _ _
          _ = inner ℝ (K.dPrevAdjoint x) (K.dPrevAdjoint x) :=
            (K.dPrev_adjoint_inner_right _ _).symm
      · exact K.dNext_adjoint_inner_right _ _

/-- VIII.Theorem 8.5: Laplacian zero is exactly the harmonic system. -/
theorem laplacian_eq_zero_iff
    (K : RealFiniteInnerProductComplex Cminus C Cplus) (x : C) :
    K.laplacian x = 0 ↔ K.dPrevAdjoint x = 0 ∧ K.dNext x = 0 := by
  constructor
  · intro hx
    have hinner : inner ℝ x (K.laplacian x) = 0 := by rw [hx, inner_zero_right]
    rw [K.inner_laplacian_self,
      real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at hinner
    have hPrevSq : 0 ≤ ‖K.dPrevAdjoint x‖ ^ 2 := sq_nonneg _
    have hNextSq : 0 ≤ ‖K.dNext x‖ ^ 2 := sq_nonneg _
    have hPrevNorm : ‖K.dPrevAdjoint x‖ = 0 := by nlinarith
    have hNextNorm : ‖K.dNext x‖ = 0 := by nlinarith
    exact ⟨norm_eq_zero.mp hPrevNorm, norm_eq_zero.mp hNextNorm⟩
  · rintro ⟨hPrev, hNext⟩
    simp [laplacian, hPrev, hNext]

/-- VIII.Theorem 8.5: the derived harmonic component lies in `ker laplacian`. -/
theorem harmonicPart_mem_laplacian_kernel
    (K : RealFiniteInnerProductComplex Cminus C Cplus) (x : C) :
    K.harmonicPart x ∈ K.laplacian.ker := by
  rw [LinearMap.mem_ker, K.laplacian_eq_zero_iff]
  exact ⟨K.dPrevAdjoint_harmonicPart_eq_zero x, K.dNext_harmonicPart_eq_zero x⟩

/-- A Laplacian-kernel vector, regarded as a harmonic cocycle. -/
noncomputable def laplacianKernelToHarmonicCycles
    (K : RealFiniteInnerProductComplex Cminus C Cplus) :
    K.laplacian.ker →ₗ[ℝ] K.harmonicCycles where
  toFun x := by
    have hx := (K.laplacian_eq_zero_iff x).mp x.property
    refine ⟨⟨x, hx.2⟩, ?_⟩
    intro b hb
    rcases hb with ⟨a, ha⟩
    change inner ℝ (b : C) (x : C) = 0
    rw [show (b : C) = K.dPrev a from ha.symm,
      ← K.dPrev_adjoint_inner_right, hx.1, inner_zero_right]
  map_add' x y := by
    ext
    rfl
  map_smul' r x := by
    ext
    rfl

/-- A harmonic cocycle is killed by the previous adjoint. -/
theorem dPrevAdjoint_harmonicCycle_eq_zero
    (K : RealFiniteInnerProductComplex Cminus C Cplus) (x : K.harmonicCycles) :
    K.dPrevAdjoint (x : C) = 0 := by
  have hinner : inner ℝ (K.dPrevAdjoint (x : C)) (K.dPrevAdjoint (x : C)) = 0 := by
    rw [K.dPrev_adjoint_inner_right]
    let b : K.cycles :=
      ⟨K.dPrev (K.dPrevAdjoint (x : C)), K.dNext_dPrev _⟩
    have hb : b ∈ K.boundariesInCycles := ⟨K.dPrevAdjoint (x : C), rfl⟩
    exact x.property b hb
  have hnormSq : ‖K.dPrevAdjoint (x : C)‖ ^ 2 = 0 := by
    simpa [real_inner_self_eq_norm_sq] using hinner
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hnormSq)

/-- VIII.Theorem 8.5: `ker laplacian` is linearly equivalent to harmonic cocycles. -/
noncomputable def laplacianKernelEquivHarmonicCycles
    (K : RealFiniteInnerProductComplex Cminus C Cplus) :
    K.laplacian.ker ≃ₗ[ℝ] K.harmonicCycles :=
  LinearEquiv.ofBijective K.laplacianKernelToHarmonicCycles ⟨by
    intro x y hxy
    apply Subtype.ext
    have hcoe := congrArg (fun z : K.harmonicCycles => (z : C)) hxy
    simpa [laplacianKernelToHarmonicCycles] using hcoe
  , by
    intro x
    have hxLap : K.laplacian (x : C) = 0 :=
      (K.laplacian_eq_zero_iff (x : C)).mpr
        ⟨K.dPrevAdjoint_harmonicCycle_eq_zero x, x.1.property⟩
    refine ⟨⟨(x : C), hxLap⟩, ?_⟩
    apply Subtype.ext
    simp [laplacianKernelToHarmonicCycles]⟩

/--
VIII.Theorem 8.5: concrete linear equivalence `ker laplacian ≃ H`, where `H` is
the quotient of cocycles by boundaries.
-/
noncomputable def laplacianKernelEquivCohomology
    (K : RealFiniteInnerProductComplex Cminus C Cplus) :
    K.laplacian.ker ≃ₗ[ℝ] K.cohomology :=
  K.laplacianKernelEquivHarmonicCycles.trans <| by
    simpa only [cohomology, harmonicCycles] using
      (Submodule.quotientEquivOfIsCompl K.boundariesInCycles K.harmonicCycles
        K.boundariesInCycles.isCompl_orthogonal_of_hasOrthogonalProjection).symm

end RealFiniteInnerProductComplex

/--
VIII.Theorem 8.5 hardening: finite Hodge decomposition over a real inner-product
complex.

The fields are concrete equations, range witnesses, kernel membership, and
orthogonality statements over the Mathlib cochain space.  This replaces the
old use of standalone `Prop + cert` tokens for the Hodge conclusion.
-/
structure RealFiniteHodgeDecomposition {Cminus C Cplus : Type v}
    [NormedAddCommGroup Cminus] [InnerProductSpace ℝ Cminus]
    [FiniteDimensional ℝ Cminus]
    [NormedAddCommGroup C] [InnerProductSpace ℝ C] [FiniteDimensional ℝ C]
    [NormedAddCommGroup Cplus] [InnerProductSpace ℝ Cplus]
    [FiniteDimensional ℝ Cplus]
    (K : RealFiniteInnerProductComplex Cminus C Cplus) where
  exactPart : C -> C
  harmonicPart : C -> C
  coexactPart : C -> C
  exactPart_mem_range :
    ∀ x : C, ∃ y : Cminus, K.dPrev y = exactPart x
  harmonicPart_mem_kernel :
    ∀ x : C, K.laplacian (harmonicPart x) = 0
  coexactPart_mem_adjoint_range :
    ∀ x : C, ∃ y : Cplus, K.dNextAdjoint y = coexactPart x
  decomposition :
    ∀ x : C, exactPart x + harmonicPart x + coexactPart x = x
  exact_harmonic_orthogonal :
    ∀ x y : C, inner ℝ (exactPart x) (harmonicPart y) = 0
  harmonic_coexact_orthogonal :
    ∀ x y : C, inner ℝ (harmonicPart x) (coexactPart y) = 0
  exact_coexact_orthogonal :
    ∀ x y : C, inner ℝ (exactPart x) (coexactPart y) = 0
  cohomologyClassOf : C -> C
  cohomologyClass_eq_harmonic :
    ∀ x : C, cohomologyClassOf x = harmonicPart x

namespace RealFiniteInnerProductComplex

variable {Cminus C Cplus : Type v}
variable [NormedAddCommGroup Cminus] [InnerProductSpace ℝ Cminus]
variable [FiniteDimensional ℝ Cminus]
variable [NormedAddCommGroup C] [InnerProductSpace ℝ C] [FiniteDimensional ℝ C]
variable [NormedAddCommGroup Cplus] [InnerProductSpace ℝ Cplus]
variable [FiniteDimensional ℝ Cplus]

/--
VIII.Theorem 8.5 compatibility bridge: build the existing package from the
derived orthogonal projections.  No decomposition or orthogonality conclusion
is supplied by the caller.
-/
noncomputable def derivedHodgeDecomposition
    (K : RealFiniteInnerProductComplex Cminus C Cplus) :
    RealFiniteHodgeDecomposition K where
  exactPart := K.exactPart
  harmonicPart := K.harmonicPart
  coexactPart := K.coexactPart
  exactPart_mem_range x := by
    rcases K.exactPart_mem_range x with ⟨y, hy⟩
    exact ⟨y, hy⟩
  harmonicPart_mem_kernel x :=
    LinearMap.mem_ker.mp (K.harmonicPart_mem_laplacian_kernel x)
  coexactPart_mem_adjoint_range x := by
    rcases K.coexactPart_mem_adjoint_range x with ⟨y, hy⟩
    exact ⟨y, hy⟩
  decomposition := K.hodge_decomposition
  exact_harmonic_orthogonal := K.exact_harmonic_orthogonal
  harmonic_coexact_orthogonal := K.harmonic_coexact_orthogonal
  exact_coexact_orthogonal := K.exact_coexact_orthogonal
  cohomologyClassOf := K.harmonicPart
  cohomologyClass_eq_harmonic := fun _ => rfl

/-- A selected preimage of the derived exact projection. -/
noncomputable def selectedCorrection
    (K : RealFiniteInnerProductComplex Cminus C Cplus) (x : C) : Cminus :=
  Classical.choose (K.exactPart_mem_range x)

/-- The selected correction maps to the derived exact component. -/
theorem selectedCorrection_maps_to_exactPart
    (K : RealFiniteInnerProductComplex Cminus C Cplus) (x : C) :
    K.dPrev (K.selectedCorrection x) = K.exactPart x :=
  Classical.choose_spec (K.exactPart_mem_range x)

/-- Orthogonal projection onto boundaries minimizes the correction residual. -/
theorem selectedResidual_norm_le
    (K : RealFiniteInnerProductComplex Cminus C Cplus) (x : C) (c : Cminus) :
    ‖x - K.dPrev (K.selectedCorrection x)‖ ≤ ‖x - K.dPrev c‖ := by
  rw [K.selectedCorrection_maps_to_exactPart]
  have hboundary : K.exactPart x - K.dPrev c ∈ K.dPrev.range :=
    Submodule.sub_mem _ (K.exactPart_mem_range x) ⟨c, rfl⟩
  have horth :
      inner ℝ (x - K.exactPart x) (K.exactPart x - K.dPrev c) = 0 :=
    K.dPrev.range.starProjection_inner_eq_zero x _ hboundary
  have hsum :
      (x - K.exactPart x) + (K.exactPart x - K.dPrev c) = x - K.dPrev c := by
    abel
  have hpyth :=
    norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
      (x - K.exactPart x) (K.exactPart x - K.dPrev c) horth
  rw [hsum] at hpyth
  nlinarith [sq_nonneg ‖x - K.exactPart x‖,
    sq_nonneg ‖K.exactPart x - K.dPrev c‖,
    norm_nonneg (x - K.exactPart x), norm_nonneg (x - K.dPrev c)]

/-- A cocycle has zero coexact projection. -/
theorem coexactPart_eq_zero_of_cocycle
    (K : RealFiniteInnerProductComplex Cminus C Cplus) {g : C}
    (hg : K.dNext g = 0) :
    K.coexactPart g = 0 := by
  change K.dNextAdjoint.range.starProjection g = 0
  rw [Submodule.starProjection_apply_eq_zero_iff]
  intro y hy
  rcases hy with ⟨z, rfl⟩
  rw [real_inner_comm, K.dNext_adjoint_inner_right, hg, inner_zero_left]

/-- VIII.Theorem 8.6: the selected residual of a cocycle is its harmonic component. -/
theorem selected_residual_eq_harmonic
    (K : RealFiniteInnerProductComplex Cminus C Cplus)
    {g : C} (hg : K.dNext g = 0) :
    g - K.dPrev (K.selectedCorrection g) = K.harmonicPart g := by
  rw [K.selectedCorrection_maps_to_exactPart]
  have hdecomp := K.hodge_decomposition g
  rw [K.coexactPart_eq_zero_of_cocycle hg, add_zero] at hdecomp
  calc
    g - K.exactPart g =
        (K.exactPart g + K.harmonicPart g) - K.exactPart g := by rw [hdecomp]
    _ = K.harmonicPart g := by abel

/-- VIII.Theorem 8.6: every local correction has at least the harmonic residual norm. -/
theorem harmonic_norm_le_corrected
    (K : RealFiniteInnerProductComplex Cminus C Cplus)
    {g : C} (hg : K.dNext g = 0) (c : Cminus) :
    ‖K.harmonicPart g‖ ≤ ‖g - K.dPrev c‖ := by
  rw [← K.selected_residual_eq_harmonic hg]
  exact K.selectedResidual_norm_le g c

end RealFiniteInnerProductComplex

namespace RealFiniteHodgeDecomposition

variable {Cminus C Cplus : Type v}
variable [NormedAddCommGroup Cminus] [InnerProductSpace ℝ Cminus]
variable [FiniteDimensional ℝ Cminus]
variable [NormedAddCommGroup C] [InnerProductSpace ℝ C] [FiniteDimensional ℝ C]
variable [NormedAddCommGroup Cplus] [InnerProductSpace ℝ Cplus]
variable [FiniteDimensional ℝ Cplus]
variable {K : RealFiniteInnerProductComplex Cminus C Cplus}

/-- VIII.Theorem 8.5 hardening: expose the actual decomposition equality. -/
theorem decomposition_holds (D : RealFiniteHodgeDecomposition K) (x : C) :
    D.exactPart x + D.harmonicPart x + D.coexactPart x = x :=
  D.decomposition x

/-- VIII.Theorem 8.5 hardening: expose harmonic kernel membership. -/
theorem harmonic_mem_kernel (D : RealFiniteHodgeDecomposition K) (x : C) :
    K.laplacian (D.harmonicPart x) = 0 :=
  D.harmonicPart_mem_kernel x

/-- VIII.Theorem 8.5 hardening: expose exact/harmonic orthogonality. -/
theorem exact_harmonic_orthogonal_holds
    (D : RealFiniteHodgeDecomposition K) (x y : C) :
    inner ℝ (D.exactPart x) (D.harmonicPart y) = 0 :=
  D.exact_harmonic_orthogonal x y

end RealFiniteHodgeDecomposition

/--
VIII.Theorem 8.6 hardening: harmonic debt minimality over the real Hodge bridge.

The minimum is an actual inequality over real residual values rather than a
standalone certificate token.
-/
structure RealHarmonicDebtMinimality {Cminus C Cplus : Type v}
    [NormedAddCommGroup Cminus] [InnerProductSpace ℝ Cminus]
    [FiniteDimensional ℝ Cminus]
    [NormedAddCommGroup C] [InnerProductSpace ℝ C] [FiniteDimensional ℝ C]
    [NormedAddCommGroup Cplus] [InnerProductSpace ℝ Cplus]
    [FiniteDimensional ℝ Cplus]
    {K : RealFiniteInnerProductComplex Cminus C Cplus}
    (D : RealFiniteHodgeDecomposition K) where
  GaugeCorrection : Type u
  correctionResidual : GaugeCorrection -> C -> ℝ
  selectedCorrection : C -> GaugeCorrection
  harmonicDebt : C -> ℝ
  harmonicDebt_eq_norm :
    ∀ x : C, harmonicDebt x = ‖D.harmonicPart x‖
  selected_minimizes :
    ∀ (x : C) (g : GaugeCorrection),
      correctionResidual (selectedCorrection x) x ≤ correctionResidual g x

namespace RealFiniteInnerProductComplex

variable {Cminus C Cplus : Type v}
variable [NormedAddCommGroup Cminus] [InnerProductSpace ℝ Cminus]
variable [FiniteDimensional ℝ Cminus]
variable [NormedAddCommGroup C] [InnerProductSpace ℝ C] [FiniteDimensional ℝ C]
variable [NormedAddCommGroup Cplus] [InnerProductSpace ℝ Cplus]
variable [FiniteDimensional ℝ Cplus]

/--
VIII.Theorem 8.6 compatibility bridge: derive the existing minimum package from
orthogonal projection onto `im dPrev`.
-/
noncomputable def derivedHarmonicDebtMinimality
    (K : RealFiniteInnerProductComplex Cminus C Cplus) :
    RealHarmonicDebtMinimality K.derivedHodgeDecomposition where
  GaugeCorrection := Cminus
  correctionResidual := fun c x => ‖x - K.dPrev c‖
  selectedCorrection := K.selectedCorrection
  harmonicDebt := fun x => ‖K.harmonicPart x‖
  harmonicDebt_eq_norm := fun _ => rfl
  selected_minimizes := K.selectedResidual_norm_le

end RealFiniteInnerProductComplex

section RealFiniteHodgeStatementContract

variable {Cminus C Cplus : Type v}
variable [NormedAddCommGroup Cminus] [InnerProductSpace ℝ Cminus]
variable [FiniteDimensional ℝ Cminus]
variable [NormedAddCommGroup C] [InnerProductSpace ℝ C] [FiniteDimensional ℝ C]
variable [NormedAddCommGroup Cplus] [InnerProductSpace ℝ Cplus]
variable [FiniteDimensional ℝ Cplus]

open RealFiniteInnerProductComplex

/-- Fixed-signature contract tests for VIII.Theorems 8.5 and 8.6. -/
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

end RealFiniteHodgeStatementContract

namespace RealHarmonicDebtMinimality

variable {Cminus C Cplus : Type v}
variable [NormedAddCommGroup Cminus] [InnerProductSpace ℝ Cminus]
variable [FiniteDimensional ℝ Cminus]
variable [NormedAddCommGroup C] [InnerProductSpace ℝ C] [FiniteDimensional ℝ C]
variable [NormedAddCommGroup Cplus] [InnerProductSpace ℝ Cplus]
variable [FiniteDimensional ℝ Cplus]
variable {K : RealFiniteInnerProductComplex Cminus C Cplus}
variable {D : RealFiniteHodgeDecomposition K}

/-- VIII.Theorem 8.6 hardening: expose harmonic debt as a real norm. -/
theorem harmonicDebt_eq_norm_holds (H : RealHarmonicDebtMinimality D) (x : C) :
    H.harmonicDebt x = ‖D.harmonicPart x‖ :=
  H.harmonicDebt_eq_norm x

/-- VIII.Theorem 8.6 hardening: expose the selected real residual minimum. -/
theorem selected_minimizes_holds
    (H : RealHarmonicDebtMinimality D) (x : C) (g : H.GaugeCorrection) :
    H.correctionResidual (H.selectedCorrection x) x ≤ H.correctionResidual g x :=
  H.selected_minimizes x g

end RealHarmonicDebtMinimality

/--
VIII.Corollary 8.7 hardening: essential repair lower bound over the real Hodge
bridge.  The lower bound is an actual real inequality.
-/
structure RealEssentialRepairLowerBound {Cminus C Cplus : Type v}
    [NormedAddCommGroup Cminus] [InnerProductSpace ℝ Cminus]
    [FiniteDimensional ℝ Cminus]
    [NormedAddCommGroup C] [InnerProductSpace ℝ C] [FiniteDimensional ℝ C]
    [NormedAddCommGroup Cplus] [InnerProductSpace ℝ Cplus]
    [FiniteDimensional ℝ Cplus]
    {K : RealFiniteInnerProductComplex Cminus C Cplus}
    {D : RealFiniteHodgeDecomposition K}
    (H : RealHarmonicDebtMinimality D) where
  RepairRoute : C -> Type u
  repairCost : (x : C) -> RepairRoute x -> ℝ
  lowerBound : C -> ℝ
  lowerBound_reads_harmonicDebt :
    ∀ x : C, lowerBound x = H.harmonicDebt x
  lowerBound_le_repairCost :
    ∀ (x : C) (r : RepairRoute x), lowerBound x ≤ repairCost x r

namespace RealEssentialRepairLowerBound

variable {Cminus C Cplus : Type v}
variable [NormedAddCommGroup Cminus] [InnerProductSpace ℝ Cminus]
variable [FiniteDimensional ℝ Cminus]
variable [NormedAddCommGroup C] [InnerProductSpace ℝ C] [FiniteDimensional ℝ C]
variable [NormedAddCommGroup Cplus] [InnerProductSpace ℝ Cplus]
variable [FiniteDimensional ℝ Cplus]
variable {K : RealFiniteInnerProductComplex Cminus C Cplus}
variable {D : RealFiniteHodgeDecomposition K}
variable {H : RealHarmonicDebtMinimality D}

/-- VIII.Corollary 8.7 hardening: expose the harmonic-debt lower-bound reading. -/
theorem lowerBound_reads_harmonicDebt_holds
    (B : RealEssentialRepairLowerBound H) (x : C) :
    B.lowerBound x = H.harmonicDebt x :=
  B.lowerBound_reads_harmonicDebt x

/-- VIII.Corollary 8.7 hardening: expose the real lower-bound inequality. -/
theorem lowerBound_le_repairCost_holds
    (B : RealEssentialRepairLowerBound H) (x : C) (r : B.RepairRoute x) :
    B.lowerBound x ≤ B.repairCost x r :=
  B.lowerBound_le_repairCost x r

end RealEssentialRepairLowerBound

/-- VIII.Definition 8.8: spectral gap reading for the selected Laplacian. -/
structure SpectralGapReading {M : MeasurementProfile.{u, v}}
    {C : CellularMeasurementModel M} (L : SheafLaplacianReading C) where
  PositiveEigenvalue : Type v
  lambdaOnePositive : PositiveEigenvalue
  gapReadsLaplacian : Prop
  gapReadsLaplacian_cert : gapReadsLaplacian
  spectralGapReading : Prop
  spectralGapReading_cert : spectralGapReading
  analyticIndicatorOnly : Prop
  analyticIndicatorOnly_cert : analyticIndicatorOnly

/-- VIII.Definition 8.9: curvature transfer spectrum reading. -/
structure CurvatureTransferSpectrum {M : MeasurementProfile.{u, v}} where
  FiniteWeightedDirectedGraph : Type u
  AdjacencyOperator : Type v
  Spectrum : Type v
  graph : FiniteWeightedDirectedGraph
  adjacency : AdjacencyOperator
  adjacencySpectrum : AdjacencyOperator -> Spectrum
  spectrum : Spectrum
  spectrum_eq_adjacencySpectrum : Prop
  spectrum_eq_adjacencySpectrum_cert : spectrum_eq_adjacencySpectrum
  finiteGraphReading : Prop
  finiteGraphReading_cert : finiteGraphReading
  curvatureTransferReading : Prop
  curvatureTransferReading_cert : curvatureTransferReading

/--
VIII.Theorem candidate 8.10: spectral hotspot reading statement-only interface.

This is a candidate interface for Perron-Frobenius style hotspot readings, not
a proved spectral theorem.
-/
structure SpectralHotspotReadingCandidate {M : MeasurementProfile.{u, v}}
    (S : CurvatureTransferSpectrum.{u, v} (M := M)) where
  PerronFrobeniusRegime : Prop
  Hotspot : Type u
  hotspotScore : Type v
  hotspotOfSpectrum : S.Spectrum -> Hotspot
  selectedHotspot : Hotspot
  scoreValue : hotspotScore
  scoreReadsSpectrum : Prop
  scoreReadsSpectrum_cert : scoreReadsSpectrum
  hotspotConclusion : Prop
  hotspotCandidateStatement : Prop
  hotspotCandidateStatement_shape :
    hotspotCandidateStatement = (PerronFrobeniusRegime -> hotspotConclusion)
  candidateOnly : Prop
  candidateOnly_cert : candidateOnly

end Measurement
end AAT.AG
