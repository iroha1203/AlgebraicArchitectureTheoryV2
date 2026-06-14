import Formal.AG.Measurement.CellularLaplacian

noncomputable section

namespace AAT.AG
namespace Measurement

universe u v

/-!
PRD-8 R6 / AC14-AC16 finite Hodge, harmonic debt, repair lower bound, and
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
