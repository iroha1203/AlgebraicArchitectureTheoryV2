import Formal.AG.Measurement.SupportTransfer
import Formal.AG.Measurement.Verdict

noncomputable section

namespace AAT.AG
namespace Measurement

universe u v

/-!
Part VIII R9 / AC21-AC22 measurement packets and finite measurement synthesis.

The packet separates certified structural verdicts from analytic readings,
candidate interfaces, and conditional readings. The synthesis theorem is
assumption-relative and constructs a bounded packet from explicitly supplied
finite measurement data.
-/

/-- VIII.Definition 11.1: selected computed invariant handles. -/
structure ComputedInvariants (M : MeasurementProfile.{u, v}) where
  CohomologyHandle : Type v
  TorHandle : Type v
  GeneratorHandle : Type v
  SupportHandle : Type u
  DimensionHandle : Type v
  RankHandle : Type v
  RepresentativeHandle : Type v
  selectedCohomology : Option CohomologyHandle
  selectedTor : Option TorHandle
  selectedGenerators : Option GeneratorHandle
  selectedSupports : Option SupportHandle
  selectedDimensions : Option DimensionHandle
  selectedRanks : Option RankHandle
  selectedRepresentatives : Option RepresentativeHandle
  finiteInvariantHandles : Prop
  finiteInvariantHandles_cert : finiteInvariantHandles
  invariantReadingsProfileRelative : Prop
  invariantReadingsProfileRelative_cert : invariantReadingsProfileRelative

namespace ComputedInvariants

/-- VIII.Definition 11.1: expose finite selected invariant handles. -/
theorem finiteInvariantHandles_holds {M : MeasurementProfile.{u, v}}
    (I : ComputedInvariants M) : I.finiteInvariantHandles :=
  I.finiteInvariantHandles_cert

end ComputedInvariants

/-- VIII.Definition 11.1: selected analytic reading handles. -/
structure AnalyticReadings (M : MeasurementProfile.{u, v}) where
  DistanceReading : Type v
  MassReading : Type v
  SpectrumReading : Type v
  ResidualNormReading : Type v
  HarmonicMassReading : Type v
  BarcodeReading : Type v
  RepairCostReading : Type v
  WassersteinTransferCost : Type v
  MorseCollapseReading : Type v
  MonodromyIndexReading : Type v
  selectedDistance : Option DistanceReading
  selectedMass : Option MassReading
  selectedSpectrum : Option SpectrumReading
  selectedResidualNorm : Option ResidualNormReading
  selectedHarmonicMass : Option HarmonicMassReading
  selectedBarcode : Option BarcodeReading
  selectedRepairCost : Option RepairCostReading
  selectedWassersteinTransferCost : Option WassersteinTransferCost
  selectedMorseCollapse : Option MorseCollapseReading
  selectedMonodromyIndex : Option MonodromyIndexReading
  analyticReadingsSeparatedFromVerdict : Prop
  analyticReadingsSeparatedFromVerdict_cert : analyticReadingsSeparatedFromVerdict
  finiteAnalyticReadingHandles : Prop
  finiteAnalyticReadingHandles_cert : finiteAnalyticReadingHandles

namespace AnalyticReadings

/-- VIII.Definition 11.1: analytic readings do not coerce to structural verdicts. -/
theorem analyticReadingsSeparatedFromVerdict_holds {M : MeasurementProfile.{u, v}}
    (A : AnalyticReadings M) : A.analyticReadingsSeparatedFromVerdict :=
  A.analyticReadingsSeparatedFromVerdict_cert

end AnalyticReadings

/-- VIII.Definition 11.1: explicit assumptions required by finite synthesis. -/
structure MeasurementAssumptions (M : MeasurementProfile.{u, v}) where
  finiteMeasurementRegime : Prop
  finiteMeasurementRegime_cert : finiteMeasurementRegime
  coverAdequate : Prop
  coverAdequate_cert : coverAdequate
  witnessExactnessWhereReflected : Prop
  witnessExactnessWhereReflected_cert : witnessExactnessWhereReflected
  axisExactnessWhereReflected : Prop
  axisExactnessWhereReflected_cert : axisExactnessWhereReflected
  effectiveCoefficientObjects : Prop
  effectiveCoefficientObjects_cert : effectiveCoefficientObjects
  commonAmbientForSelectedLawConflict : Prop
  commonAmbientForSelectedLawConflict_cert : commonAmbientForSelectedLawConflict
  supportLocalizedPairingFixed : Prop
  supportLocalizedPairingFixed_cert : supportLocalizedPairingFixed
  verdictDisciplineFixed : Prop
  verdictDisciplineFixed_cert : verdictDisciplineFixed

/-- VIII.Definition 11.1: non-conclusions carried by a bounded packet. -/
structure MeasurementNonConclusions (M : MeasurementProfile.{u, v}) where
  unselectedLaws : Prop
  unselectedLaws_cert : unselectedLaws
  unmeasuredSupport : Prop
  unmeasuredSupport_cert : unmeasuredSupport
  unprovidedCoefficientData : Prop
  unprovidedCoefficientData_cert : unprovidedCoefficientData
  undecidedPredicates : Prop
  undecidedPredicates_cert : undecidedPredicates
  candidateDependentReadingsSeparated : Prop
  candidateDependentReadingsSeparated_cert : candidateDependentReadingsSeparated

namespace MeasurementNonConclusions

/-- VIII.Principle 11.2: candidate-dependent readings remain separated. -/
theorem candidateDependentReadingsSeparated_holds {M : MeasurementProfile.{u, v}}
    (N : MeasurementNonConclusions M) : N.candidateDependentReadingsSeparated :=
  N.candidateDependentReadingsSeparated_cert

end MeasurementNonConclusions

/-- VIII.Definition 11.1: raw fields for a bounded measurement packet. -/
structure MeasurementPacketData (M : MeasurementProfile.{u, v}) where
  selectedDomain : M.Domain
  structuralVerdict : StructuralVerdict M selectedDomain
  computedInvariants : ComputedInvariants M
  analyticReadings : AnalyticReadings M
  CertifiedReading : Type v
  CandidateInterface : Type v
  ConditionalReading : Type v
  certifiedReadings : List CertifiedReading
  candidateInterfaces : List CandidateInterface
  conditionalReadings : List ConditionalReading
  assumptions : MeasurementAssumptions M
  nonConclusions : MeasurementNonConclusions M
  certifiedSeparatedFromCandidate : Prop
  certifiedSeparatedFromCandidate_cert : certifiedSeparatedFromCandidate

/--
VIII.Principle 11.2: the selected bounded packet statement used by synthesis.

The statement is intentionally built from explicit assumptions and separation
certificates instead of being an opaque packet field supplied in advance.
-/
def boundedMeasurementStatement {M : MeasurementProfile.{u, v}}
    (D : MeasurementPacketData M) : Prop :=
  D.assumptions.finiteMeasurementRegime ∧
    D.assumptions.coverAdequate ∧
      D.assumptions.witnessExactnessWhereReflected ∧
        D.assumptions.axisExactnessWhereReflected ∧
          D.assumptions.effectiveCoefficientObjects ∧
            D.assumptions.commonAmbientForSelectedLawConflict ∧
              D.assumptions.supportLocalizedPairingFixed ∧
                D.assumptions.verdictDisciplineFixed ∧
                  D.certifiedSeparatedFromCandidate ∧
                    D.nonConclusions.candidateDependentReadingsSeparated

/-- VIII.Principle 11.2: prove the bounded statement from explicit packet data. -/
def boundedMeasurementStatement_cert {M : MeasurementProfile.{u, v}}
    (D : MeasurementPacketData M) : boundedMeasurementStatement D := by
  unfold boundedMeasurementStatement
  exact ⟨D.assumptions.finiteMeasurementRegime_cert,
    D.assumptions.coverAdequate_cert,
    D.assumptions.witnessExactnessWhereReflected_cert,
    D.assumptions.axisExactnessWhereReflected_cert,
    D.assumptions.effectiveCoefficientObjects_cert,
    D.assumptions.commonAmbientForSelectedLawConflict_cert,
    D.assumptions.supportLocalizedPairingFixed_cert,
    D.assumptions.verdictDisciplineFixed_cert,
    D.certifiedSeparatedFromCandidate_cert,
    D.nonConclusions.candidateDependentReadingsSeparated_cert⟩

/-- VIII.Definition 11.1: bounded measurement packet. -/
structure MeasurementPacket (M : MeasurementProfile.{u, v})
    extends MeasurementPacketData M where
  boundedMathematicalMeasurement : Prop
  boundedMathematicalMeasurement_cert : boundedMathematicalMeasurement

namespace MeasurementPacket

/-- VIII.Principle 11.2: expose bounded mathematical measurement status. -/
theorem boundedMathematicalMeasurement_holds {M : MeasurementProfile.{u, v}}
    (P : MeasurementPacket M) : P.boundedMathematicalMeasurement :=
  P.boundedMathematicalMeasurement_cert

/-- VIII.Definition 11.1: certified readings and candidate interfaces are separated. -/
theorem certifiedSeparatedFromCandidate_holds {M : MeasurementProfile.{u, v}}
    (P : MeasurementPacket M) : P.certifiedSeparatedFromCandidate :=
  P.certifiedSeparatedFromCandidate_cert

end MeasurementPacket

/-- VIII.Theorem 12.1: construct a bounded packet from raw packet data. -/
def measurementPacketOfData {M : MeasurementProfile.{u, v}}
    (D : MeasurementPacketData M) : MeasurementPacket M where
  toMeasurementPacketData := D
  boundedMathematicalMeasurement := boundedMeasurementStatement D
  boundedMathematicalMeasurement_cert := boundedMeasurementStatement_cert D

/-- VIII.Theorem 12.1: finite measurement synthesis theorem package. -/
structure FiniteMeasurementSynthesis {M : MeasurementProfile.{u, v}}
    (D : MeasurementPacketData M) where
  packet : MeasurementPacket M
  packet_extends_data : packet.toMeasurementPacketData = D
  finite_regime_holds : D.assumptions.finiteMeasurementRegime
  cover_adequate_holds : D.assumptions.coverAdequate
  witness_exactness_holds : D.assumptions.witnessExactnessWhereReflected
  axis_exactness_holds : D.assumptions.axisExactnessWhereReflected
  effective_coefficients_holds : D.assumptions.effectiveCoefficientObjects
  common_ambient_holds : D.assumptions.commonAmbientForSelectedLawConflict
  support_pairing_holds : D.assumptions.supportLocalizedPairingFixed
  verdict_discipline_holds : D.assumptions.verdictDisciplineFixed
  bounded_packet_holds : packet.boundedMathematicalMeasurement
  certified_candidate_separation_holds : D.certifiedSeparatedFromCandidate

namespace FiniteMeasurementSynthesis

/-- VIII.Theorem 12.1: expose the bounded packet conclusion. -/
theorem bounded_packet_holds_of_package {M : MeasurementProfile.{u, v}}
    {D : MeasurementPacketData M} (T : FiniteMeasurementSynthesis D) :
    T.packet.boundedMathematicalMeasurement :=
  T.bounded_packet_holds

/-- VIII.Theorem 12.1: expose certified/candidate separation. -/
theorem certified_candidate_separation_holds_of_package
    {M : MeasurementProfile.{u, v}}
    {D : MeasurementPacketData M} (T : FiniteMeasurementSynthesis D) :
    D.certifiedSeparatedFromCandidate :=
  T.certified_candidate_separation_holds

end FiniteMeasurementSynthesis

/-- VIII.Theorem 12.1: construct the selected finite measurement synthesis package. -/
def finiteMeasurementSynthesisPackage {M : MeasurementProfile.{u, v}}
    (D : MeasurementPacketData M) : FiniteMeasurementSynthesis D where
  packet := measurementPacketOfData D
  packet_extends_data := rfl
  finite_regime_holds := D.assumptions.finiteMeasurementRegime_cert
  cover_adequate_holds := D.assumptions.coverAdequate_cert
  witness_exactness_holds := D.assumptions.witnessExactnessWhereReflected_cert
  axis_exactness_holds := D.assumptions.axisExactnessWhereReflected_cert
  effective_coefficients_holds := D.assumptions.effectiveCoefficientObjects_cert
  common_ambient_holds := D.assumptions.commonAmbientForSelectedLawConflict_cert
  support_pairing_holds := D.assumptions.supportLocalizedPairingFixed_cert
  verdict_discipline_holds := D.assumptions.verdictDisciplineFixed_cert
  bounded_packet_holds := (measurementPacketOfData D).boundedMathematicalMeasurement_cert
  certified_candidate_separation_holds := D.certifiedSeparatedFromCandidate_cert

/-- VIII.Theorem 12.1: selected finite measurement synthesis exists under explicit data. -/
theorem finiteMeasurementSynthesis {M : MeasurementProfile.{u, v}}
    (D : MeasurementPacketData M) : Nonempty (FiniteMeasurementSynthesis D) :=
  ⟨finiteMeasurementSynthesisPackage D⟩

end Measurement
end AAT.AG
