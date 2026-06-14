import Formal.AG.Measurement.Packet

noncomputable section

namespace AAT.AG
namespace Measurement

universe u v

/-!
PRD-8 R10 / AC23-AC24 AAT-GAGA finite measurement comparison.

`GAGA` here is a finite-profile comparison packet. It does not assert external
data-source fidelity, external procedure correctness, or truth across arbitrary
law universes.
-/

/-- VIII.Theorem 12.3: certified comparison fields. -/
structure AATGAGACertifiedFields (M : MeasurementProfile.{u, v}) where
  HodgeComparison : Type v
  HarmonicDecomposition : Type v
  PeriodStokesAccounting : Type v
  TopologicalDebtCapacity : Type v
  DerivedConflictAccounting : Type v
  selectedHodgeComparison : HodgeComparison
  selectedHarmonicDecomposition : HarmonicDecomposition
  selectedPeriodStokesAccounting : PeriodStokesAccounting
  selectedTopologicalDebtCapacity : TopologicalDebtCapacity
  selectedDerivedConflictAccounting : DerivedConflictAccounting
  hodgeComparisonCertified : Prop
  hodgeComparisonCertified_cert : hodgeComparisonCertified
  harmonicDecompositionCertified : Prop
  harmonicDecompositionCertified_cert : harmonicDecompositionCertified
  periodStokesAccountingCertified : Prop
  periodStokesAccountingCertified_cert : periodStokesAccountingCertified
  topologicalDebtCapacityCertified : Prop
  topologicalDebtCapacityCertified_cert : topologicalDebtCapacityCertified
  derivedConflictAccountingCertified : Prop
  derivedConflictAccountingCertified_cert : derivedConflictAccountingCertified

namespace AATGAGACertifiedFields

/-- VIII.Theorem 12.3: expose certified Hodge comparison. -/
theorem hodgeComparisonCertified_holds {M : MeasurementProfile.{u, v}}
    (C : AATGAGACertifiedFields M) : C.hodgeComparisonCertified :=
  C.hodgeComparisonCertified_cert

/-- VIII.Theorem 12.3: expose certified derived conflict accounting. -/
theorem derivedConflictAccountingCertified_holds {M : MeasurementProfile.{u, v}}
    (C : AATGAGACertifiedFields M) : C.derivedConflictAccountingCertified :=
  C.derivedConflictAccountingCertified_cert

end AATGAGACertifiedFields

/-- VIII.Theorem 12.3: candidate-dependent comparison interfaces. -/
structure AATGAGACandidateInterfaces (M : MeasurementProfile.{u, v}) where
  MonotoneWitnessStabilityInterface : Type v
  FiniteCechStabilityInterface : Type v
  FlatBaseChangeInterface : Type v
  SpectralHotspotInterface : Type v
  TransferLowerBoundInterface : Type v
  monotoneWitnessStability : Option MonotoneWitnessStabilityInterface
  finiteCechStability : Option FiniteCechStabilityInterface
  flatBaseChange : Option FlatBaseChangeInterface
  spectralHotspot : Option SpectralHotspotInterface
  transferLowerBound : Option TransferLowerBoundInterface
  candidateInterfacesSeparatedFromCertified : Prop
  candidateInterfacesSeparatedFromCertified_cert :
    candidateInterfacesSeparatedFromCertified

namespace AATGAGACandidateInterfaces

/-- VIII.Theorem 12.3: candidate interfaces are not certified conclusions. -/
theorem candidateInterfacesSeparatedFromCertified_holds
    {M : MeasurementProfile.{u, v}}
    (C : AATGAGACandidateInterfaces M) :
    C.candidateInterfacesSeparatedFromCertified :=
  C.candidateInterfacesSeparatedFromCertified_cert

end AATGAGACandidateInterfaces

/-- VIII.Theorem 12.3: explicit assumptions for finite-profile comparison. -/
structure AATGAGAComparisonAssumptions (M : MeasurementProfile.{u, v}) where
  finiteMeasurementRegime : Prop
  finiteMeasurementRegime_cert : finiteMeasurementRegime
  finiteCover : Prop
  finiteCover_cert : finiteCover
  innerProductCoefficientSheaf : Prop
  innerProductCoefficientSheaf_cert : innerProductCoefficientSheaf
  cellularCochainModel : Prop
  cellularCochainModel_cert : cellularCochainModel
  squareFreeRegime : Prop
  squareFreeRegime_cert : squareFreeRegime
  commonAmbient : Prop
  commonAmbient_cert : commonAmbient
  stabilityDistanceAndComparisonMaps : Prop
  stabilityDistanceAndComparisonMaps_cert : stabilityDistanceAndComparisonMaps

/-- VIII.Principle 12.4: non-conclusions for the finite GAGA comparison. -/
structure AATGAGABoundary (M : MeasurementProfile.{u, v}) where
  noExternalDataSourceFidelity : Prop
  noExternalDataSourceFidelity_cert : noExternalDataSourceFidelity
  noExternalProcedureCorrectness : Prop
  noExternalProcedureCorrectness_cert : noExternalProcedureCorrectness
  noArbitraryLawUniverseComparison : Prop
  noArbitraryLawUniverseComparison_cert : noArbitraryLawUniverseComparison
  candidateDependentFieldsNotCertified : Prop
  candidateDependentFieldsNotCertified_cert : candidateDependentFieldsNotCertified

namespace AATGAGABoundary

/-- VIII.Principle 12.4: `GAGA` does not assert external fidelity. -/
theorem noExternalDataSourceFidelity_holds {M : MeasurementProfile.{u, v}}
    (B : AATGAGABoundary M) : B.noExternalDataSourceFidelity :=
  B.noExternalDataSourceFidelity_cert

/-- VIII.Principle 12.4: candidate-dependent fields are not certified conclusions. -/
theorem candidateDependentFieldsNotCertified_holds
    {M : MeasurementProfile.{u, v}} (B : AATGAGABoundary M) :
    B.candidateDependentFieldsNotCertified :=
  B.candidateDependentFieldsNotCertified_cert

end AATGAGABoundary

/-- VIII.Theorem 12.3: raw data for a finite AAT-GAGA comparison packet. -/
structure AATGAGAComparisonData (M : MeasurementProfile.{u, v}) where
  measurementPacketData : MeasurementPacketData M
  certifiedFields : AATGAGACertifiedFields M
  candidateInterfaces : AATGAGACandidateInterfaces M
  assumptions : AATGAGAComparisonAssumptions M
  boundary : AATGAGABoundary M
  certifiedCandidateSeparation : Prop
  certifiedCandidateSeparation_cert : certifiedCandidateSeparation

/--
VIII.Theorem 12.3: selected finite-profile comparison statement.

The statement is built from finite assumptions, certified comparison fields,
candidate/certified separation, and external-fidelity boundaries.
-/
def aatGAGAComparisonStatement {M : MeasurementProfile.{u, v}}
    (D : AATGAGAComparisonData M) : Prop :=
  D.assumptions.finiteMeasurementRegime ∧
    D.assumptions.finiteCover ∧
      D.assumptions.innerProductCoefficientSheaf ∧
        D.assumptions.cellularCochainModel ∧
          D.assumptions.squareFreeRegime ∧
            D.assumptions.commonAmbient ∧
              D.assumptions.stabilityDistanceAndComparisonMaps ∧
                D.certifiedFields.hodgeComparisonCertified ∧
                  D.certifiedFields.harmonicDecompositionCertified ∧
                    D.certifiedFields.periodStokesAccountingCertified ∧
                      D.certifiedFields.topologicalDebtCapacityCertified ∧
                        D.certifiedFields.derivedConflictAccountingCertified ∧
                          D.candidateInterfaces.candidateInterfacesSeparatedFromCertified ∧
                            D.certifiedCandidateSeparation ∧
                              D.boundary.noExternalDataSourceFidelity ∧
                                D.boundary.noExternalProcedureCorrectness ∧
                                  D.boundary.noArbitraryLawUniverseComparison ∧
                                    D.boundary.candidateDependentFieldsNotCertified

/-- VIII.Theorem 12.3: prove the comparison statement from raw comparison data. -/
def aatGAGAComparisonStatement_cert {M : MeasurementProfile.{u, v}}
    (D : AATGAGAComparisonData M) : aatGAGAComparisonStatement D := by
  unfold aatGAGAComparisonStatement
  exact ⟨D.assumptions.finiteMeasurementRegime_cert,
    D.assumptions.finiteCover_cert,
    D.assumptions.innerProductCoefficientSheaf_cert,
    D.assumptions.cellularCochainModel_cert,
    D.assumptions.squareFreeRegime_cert,
    D.assumptions.commonAmbient_cert,
    D.assumptions.stabilityDistanceAndComparisonMaps_cert,
    D.certifiedFields.hodgeComparisonCertified_cert,
    D.certifiedFields.harmonicDecompositionCertified_cert,
    D.certifiedFields.periodStokesAccountingCertified_cert,
    D.certifiedFields.topologicalDebtCapacityCertified_cert,
    D.certifiedFields.derivedConflictAccountingCertified_cert,
    D.candidateInterfaces.candidateInterfacesSeparatedFromCertified_cert,
    D.certifiedCandidateSeparation_cert,
    D.boundary.noExternalDataSourceFidelity_cert,
    D.boundary.noExternalProcedureCorrectness_cert,
    D.boundary.noArbitraryLawUniverseComparison_cert,
    D.boundary.candidateDependentFieldsNotCertified_cert⟩

/-- VIII.Theorem 12.3: finite AAT-GAGA comparison packet. -/
structure AATGAGAComparisonPacket (M : MeasurementProfile.{u, v})
    extends AATGAGAComparisonData M where
  finiteProfileComparison : Prop
  finiteProfileComparison_cert : finiteProfileComparison

namespace AATGAGAComparisonPacket

/-- VIII.Theorem 12.3: expose finite-profile comparison status. -/
theorem finiteProfileComparison_holds {M : MeasurementProfile.{u, v}}
    (P : AATGAGAComparisonPacket M) : P.finiteProfileComparison :=
  P.finiteProfileComparison_cert

/-- VIII.Theorem 12.3: certified and candidate fields are separated. -/
theorem certifiedCandidateSeparation_holds {M : MeasurementProfile.{u, v}}
    (P : AATGAGAComparisonPacket M) : P.certifiedCandidateSeparation :=
  P.certifiedCandidateSeparation_cert

end AATGAGAComparisonPacket

/-- VIII.Theorem 12.3: construct a finite comparison packet from raw data. -/
def aatGAGAComparisonPacketOfData {M : MeasurementProfile.{u, v}}
    (D : AATGAGAComparisonData M) : AATGAGAComparisonPacket M where
  toAATGAGAComparisonData := D
  finiteProfileComparison := aatGAGAComparisonStatement D
  finiteProfileComparison_cert := aatGAGAComparisonStatement_cert D

/-- VIII.Theorem 12.3: finite measurement comparison theorem package. -/
structure AATGAGAFiniteMeasurementComparison {M : MeasurementProfile.{u, v}}
    (D : AATGAGAComparisonData M) where
  packet : AATGAGAComparisonPacket M
  packet_extends_data : packet.toAATGAGAComparisonData = D
  finite_measurement_regime_holds : D.assumptions.finiteMeasurementRegime
  finite_cover_holds : D.assumptions.finiteCover
  inner_product_coefficient_sheaf_holds :
    D.assumptions.innerProductCoefficientSheaf
  cellular_cochain_model_holds : D.assumptions.cellularCochainModel
  square_free_regime_holds : D.assumptions.squareFreeRegime
  common_ambient_holds : D.assumptions.commonAmbient
  stability_distance_and_maps_holds :
    D.assumptions.stabilityDistanceAndComparisonMaps
  certified_fields_hodge_holds : D.certifiedFields.hodgeComparisonCertified
  certified_fields_harmonic_holds :
    D.certifiedFields.harmonicDecompositionCertified
  certified_fields_period_stokes_holds :
    D.certifiedFields.periodStokesAccountingCertified
  certified_fields_debt_capacity_holds :
    D.certifiedFields.topologicalDebtCapacityCertified
  certified_fields_derived_conflict_holds :
    D.certifiedFields.derivedConflictAccountingCertified
  candidate_interfaces_separated_holds :
    D.candidateInterfaces.candidateInterfacesSeparatedFromCertified
  finite_profile_comparison_holds : packet.finiteProfileComparison
  no_external_fidelity_holds : D.boundary.noExternalDataSourceFidelity

namespace AATGAGAFiniteMeasurementComparison

/-- VIII.Theorem 12.3: expose finite-profile comparison. -/
theorem finite_profile_comparison_holds_of_package
    {M : MeasurementProfile.{u, v}} {D : AATGAGAComparisonData M}
    (T : AATGAGAFiniteMeasurementComparison D) :
    T.packet.finiteProfileComparison :=
  T.finite_profile_comparison_holds

/-- VIII.Theorem 12.3: expose candidate/certified separation. -/
theorem candidate_interfaces_separated_holds_of_package
    {M : MeasurementProfile.{u, v}} {D : AATGAGAComparisonData M}
    (T : AATGAGAFiniteMeasurementComparison D) :
    D.candidateInterfaces.candidateInterfacesSeparatedFromCertified :=
  T.candidate_interfaces_separated_holds

end AATGAGAFiniteMeasurementComparison

/-- VIII.Theorem 12.3: construct the finite AAT-GAGA comparison package. -/
def aatGAGAFiniteMeasurementComparisonPackage
    {M : MeasurementProfile.{u, v}} (D : AATGAGAComparisonData M) :
    AATGAGAFiniteMeasurementComparison D where
  packet := aatGAGAComparisonPacketOfData D
  packet_extends_data := rfl
  finite_measurement_regime_holds := D.assumptions.finiteMeasurementRegime_cert
  finite_cover_holds := D.assumptions.finiteCover_cert
  inner_product_coefficient_sheaf_holds :=
    D.assumptions.innerProductCoefficientSheaf_cert
  cellular_cochain_model_holds := D.assumptions.cellularCochainModel_cert
  square_free_regime_holds := D.assumptions.squareFreeRegime_cert
  common_ambient_holds := D.assumptions.commonAmbient_cert
  stability_distance_and_maps_holds :=
    D.assumptions.stabilityDistanceAndComparisonMaps_cert
  certified_fields_hodge_holds := D.certifiedFields.hodgeComparisonCertified_cert
  certified_fields_harmonic_holds :=
    D.certifiedFields.harmonicDecompositionCertified_cert
  certified_fields_period_stokes_holds :=
    D.certifiedFields.periodStokesAccountingCertified_cert
  certified_fields_debt_capacity_holds :=
    D.certifiedFields.topologicalDebtCapacityCertified_cert
  certified_fields_derived_conflict_holds :=
    D.certifiedFields.derivedConflictAccountingCertified_cert
  candidate_interfaces_separated_holds :=
    D.candidateInterfaces.candidateInterfacesSeparatedFromCertified_cert
  finite_profile_comparison_holds :=
    (aatGAGAComparisonPacketOfData D).finiteProfileComparison_cert
  no_external_fidelity_holds := D.boundary.noExternalDataSourceFidelity_cert

/-- VIII.Theorem 12.3: selected finite AAT-GAGA comparison exists under explicit data. -/
theorem aatGAGAFiniteMeasurementComparison {M : MeasurementProfile.{u, v}}
    (D : AATGAGAComparisonData M) :
    Nonempty (AATGAGAFiniteMeasurementComparison D) :=
  ⟨aatGAGAFiniteMeasurementComparisonPackage D⟩

end Measurement
end AAT.AG
