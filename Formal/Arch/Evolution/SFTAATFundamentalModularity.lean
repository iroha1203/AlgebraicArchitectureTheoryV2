import Formal.Arch.Evolution.SFTFundamentalModularity
import Formal.Arch.Evolution.SFTInterfaceBoundary

/-!
AAT-supported boundary surface for the finite selected SFT Grand Theorem.

This module reads the existing finite selected Fundamental Modularity theorem
package through an AAT selected-architecture boundary. It does not promote AAT
theorem status, ArchSig reports, empirical evidence, or operational governance
into assumption-free SFT conclusions.
-/

namespace Formal.Arch
namespace SFTAATFundamentalModularity

open SFTFundamentalModularity

universe u v w x y z a

/-- Selected architecture slice supplied by AAT to an SFT theorem package. -/
structure AATSelectedArchitectureSlice where
  selectedArchitecture : Prop
  projectionBoundary : Prop
  observationBoundary : Prop
  reconstructionBoundary : Prop
  missingEvidence : Prop
  theoremStatusBoundary : Prop
  nonConclusions : Prop

namespace AATSelectedArchitectureSlice

def RecordsSelectedArchitecture (slice : AATSelectedArchitectureSlice) : Prop :=
  slice.selectedArchitecture

def RecordsProjectionBoundary (slice : AATSelectedArchitectureSlice) : Prop :=
  slice.projectionBoundary

def RecordsObservationBoundary (slice : AATSelectedArchitectureSlice) : Prop :=
  slice.observationBoundary

def RecordsReconstructionBoundary (slice : AATSelectedArchitectureSlice) : Prop :=
  slice.reconstructionBoundary

def RecordsMissingEvidence (slice : AATSelectedArchitectureSlice) : Prop :=
  slice.missingEvidence

def RecordsTheoremStatusBoundary (slice : AATSelectedArchitectureSlice) : Prop :=
  slice.theoremStatusBoundary

def RecordsNonConclusions (slice : AATSelectedArchitectureSlice) : Prop :=
  slice.nonConclusions

end AATSelectedArchitectureSlice

/--
AAT-supported SFT boundary package.

The package ties one selected AAT architecture slice to a finite exact SFT model,
selected source, and selected horizon. It stores the interface relation that
reads AAT theorem status as an SFT local premise, while preserving projection,
observation, reconstruction, missing-evidence, theorem, report, and
non-conclusion boundaries.
-/
structure AATSupportedSFTBoundary
    {Global : Type u} {Index : Type v} {Local : Type w}
    {OperationG : Type x} {OperationL : Type y}
    {Governance : Type z}
    (exactModel :
      FiniteExactSFTModel Global Index Local OperationG OperationL Governance)
    (source : Global) (horizon : Nat) where
  selectedSlice : AATSelectedArchitectureSlice
  aatStatus : AATTheoremStatus
  forecastStatus : SFTForecastStatus
  interfaceBoundary : AATToSFTInterfaceBoundary aatStatus forecastStatus
  selectedSourceBoundary : Prop
  selectedHorizonBoundary : Prop
  recordsFiniteSelectedModel : exactModel.RecordsFiniteModelBoundary
  recordsExactCoverBoundary : exactModel.RecordsExactCoverBoundary
  recordsObservationBoundary : exactModel.RecordsObservationBoundary
  recordsAATProjectionBoundary : selectedSlice.RecordsProjectionBoundary
  recordsAATObservationBoundary : selectedSlice.RecordsObservationBoundary
  recordsAATReconstructionBoundary : selectedSlice.RecordsReconstructionBoundary
  recordsAATMissingEvidence : selectedSlice.RecordsMissingEvidence
  archSigReportBoundary : Prop
  theoremBoundary : Prop
  typedFailureBoundary : Prop
  nonConclusions : Prop

namespace AATSupportedSFTBoundary

variable {Global : Type u} {Index : Type v} {Local : Type w}
variable {OperationG : Type x} {OperationL : Type y}
variable {Governance : Type z}
variable {exactModel :
  FiniteExactSFTModel Global Index Local OperationG OperationL Governance}
variable {source : Global} {horizon : Nat}

/--
Construct an AAT-supported SFT boundary from the selected slice, interface
boundary, finite exact model boundaries, and explicit non-conclusion boundaries.
-/
def ofSelectedSliceAndFiniteExactModel
    (selectedSlice : AATSelectedArchitectureSlice)
    (aatStatus : AATTheoremStatus)
    (forecastStatus : SFTForecastStatus)
    (interfaceBoundary :
      AATToSFTInterfaceBoundary aatStatus forecastStatus)
    (selectedSourceBoundary : Prop)
    (selectedHorizonBoundary : Prop)
    (hFinite : exactModel.RecordsFiniteModelBoundary)
    (hExact : exactModel.RecordsExactCoverBoundary)
    (hObservation : exactModel.RecordsObservationBoundary)
    (hProjection : selectedSlice.RecordsProjectionBoundary)
    (hAATObservation : selectedSlice.RecordsObservationBoundary)
    (hReconstruction : selectedSlice.RecordsReconstructionBoundary)
    (hMissingEvidence : selectedSlice.RecordsMissingEvidence)
    (archSigReportBoundary theoremBoundary typedFailureBoundary
      nonConclusions : Prop) :
    AATSupportedSFTBoundary exactModel source horizon where
  selectedSlice := selectedSlice
  aatStatus := aatStatus
  forecastStatus := forecastStatus
  interfaceBoundary := interfaceBoundary
  selectedSourceBoundary := selectedSourceBoundary
  selectedHorizonBoundary := selectedHorizonBoundary
  recordsFiniteSelectedModel := hFinite
  recordsExactCoverBoundary := hExact
  recordsObservationBoundary := hObservation
  recordsAATProjectionBoundary := hProjection
  recordsAATObservationBoundary := hAATObservation
  recordsAATReconstructionBoundary := hReconstruction
  recordsAATMissingEvidence := hMissingEvidence
  archSigReportBoundary := archSigReportBoundary
  theoremBoundary := theoremBoundary
  typedFailureBoundary := typedFailureBoundary
  nonConclusions := nonConclusions

def RecordsSelectedFiniteBoundary
    (boundary : AATSupportedSFTBoundary exactModel source horizon) : Prop :=
  boundary.selectedSlice.RecordsSelectedArchitecture ∧
    exactModel.RecordsFiniteModelBoundary ∧
      boundary.selectedSourceBoundary ∧ boundary.selectedHorizonBoundary

def RecordsAATSliceBoundaries
    (boundary : AATSupportedSFTBoundary exactModel source horizon) : Prop :=
  boundary.selectedSlice.RecordsProjectionBoundary ∧
    boundary.selectedSlice.RecordsObservationBoundary ∧
      boundary.selectedSlice.RecordsReconstructionBoundary ∧
        boundary.selectedSlice.RecordsMissingEvidence

def RecordsTheoremAndModelBoundaries
    (boundary : AATSupportedSFTBoundary exactModel source horizon) : Prop :=
  exactModel.RecordsExactCoverBoundary ∧
    exactModel.RecordsObservationBoundary ∧
      boundary.aatStatus.RecordsTheoremBoundary ∧
        boundary.forecastStatus.RecordsTheoremBoundary ∧
          boundary.archSigReportBoundary ∧
            boundary.theoremBoundary ∧ boundary.typedFailureBoundary

def RecordsNonConclusions
    (boundary : AATSupportedSFTBoundary exactModel source horizon) : Prop :=
  boundary.nonConclusions ∧
    boundary.selectedSlice.RecordsNonConclusions ∧
      boundary.aatStatus.RecordsNonConclusions ∧
        boundary.forecastStatus.RecordsNonConclusions ∧
          exactModel.RecordsNonConclusions

theorem aat_status_as_sft_local_premise
    (boundary : AATSupportedSFTBoundary exactModel source horizon)
    (hAAT : boundary.aatStatus.RecordsTheoremPackage) :
    boundary.forecastStatus.RecordsLocalPremise :=
  boundary.interfaceBoundary.aat_theorem_status_as_local_premise hAAT

theorem records_projection_observation_reconstruction_missingEvidence
    (boundary : AATSupportedSFTBoundary exactModel source horizon) :
    boundary.RecordsAATSliceBoundaries :=
  ⟨boundary.recordsAATProjectionBoundary,
    boundary.recordsAATObservationBoundary,
    boundary.recordsAATReconstructionBoundary,
    boundary.recordsAATMissingEvidence⟩

theorem records_selected_finite_source_horizon
    (boundary : AATSupportedSFTBoundary exactModel source horizon)
    (hSlice : boundary.selectedSlice.RecordsSelectedArchitecture)
    (hSource : boundary.selectedSourceBoundary)
    (hHorizon : boundary.selectedHorizonBoundary) :
    boundary.RecordsSelectedFiniteBoundary :=
  ⟨hSlice, boundary.recordsFiniteSelectedModel,
    hSource, hHorizon⟩

theorem records_selected_source_boundary
    (boundary : AATSupportedSFTBoundary exactModel source horizon)
    (hSource : boundary.selectedSourceBoundary) :
    boundary.selectedSourceBoundary :=
  hSource

theorem records_selected_horizon_boundary
    (boundary : AATSupportedSFTBoundary exactModel source horizon)
    (hHorizon : boundary.selectedHorizonBoundary) :
    boundary.selectedHorizonBoundary :=
  hHorizon

theorem records_aat_projection_boundary
    (boundary : AATSupportedSFTBoundary exactModel source horizon) :
    boundary.selectedSlice.RecordsProjectionBoundary :=
  boundary.recordsAATProjectionBoundary

theorem records_aat_observation_boundary
    (boundary : AATSupportedSFTBoundary exactModel source horizon) :
    boundary.selectedSlice.RecordsObservationBoundary :=
  boundary.recordsAATObservationBoundary

theorem records_aat_reconstruction_boundary
    (boundary : AATSupportedSFTBoundary exactModel source horizon) :
    boundary.selectedSlice.RecordsReconstructionBoundary :=
  boundary.recordsAATReconstructionBoundary

theorem records_aat_missingEvidence_boundary
    (boundary : AATSupportedSFTBoundary exactModel source horizon) :
    boundary.selectedSlice.RecordsMissingEvidence :=
  boundary.recordsAATMissingEvidence

theorem preserves_nonConclusions
    (boundary : AATSupportedSFTBoundary exactModel source horizon)
    (hBoundary : boundary.nonConclusions)
    (hSlice : boundary.selectedSlice.RecordsNonConclusions)
    (hAAT : boundary.aatStatus.RecordsNonConclusions)
    (hExact : exactModel.RecordsNonConclusions) :
    boundary.RecordsNonConclusions :=
  ⟨hBoundary, hSlice, hAAT,
    boundary.interfaceBoundary.interface_preserves_nonConclusions hAAT,
    hExact⟩

theorem report_boundary_does_not_strengthen_theorem_status
    (boundary : AATSupportedSFTBoundary exactModel source horizon)
    (hTooling : boundary.aatStatus.RecordsToolingBoundary) :
    boundary.forecastStatus.RecordsToolingBoundary :=
  boundary.interfaceBoundary.tool_report_output_does_not_strengthen_aat_theorem_status
    hTooling

theorem records_report_and_theorem_status_boundaries
    (boundary : AATSupportedSFTBoundary exactModel source horizon)
    (hAATTheorem : boundary.aatStatus.RecordsTheoremBoundary)
    (hForecastTheorem : boundary.forecastStatus.RecordsTheoremBoundary)
    (hArchSigReport : boundary.archSigReportBoundary)
    (hTheoremBoundary : boundary.theoremBoundary)
    (hTypedFailureBoundary : boundary.typedFailureBoundary) :
    boundary.RecordsTheoremAndModelBoundaries :=
  ⟨boundary.recordsExactCoverBoundary, boundary.recordsObservationBoundary,
    hAATTheorem, hForecastTheorem, hArchSigReport,
    hTheoremBoundary, hTypedFailureBoundary⟩

theorem constructor_preserves_nonConclusions
    (selectedSlice : AATSelectedArchitectureSlice)
    (aatStatus : AATTheoremStatus)
    (forecastStatus : SFTForecastStatus)
    (interfaceBoundary :
      AATToSFTInterfaceBoundary aatStatus forecastStatus)
    (selectedSourceBoundary : Prop)
    (selectedHorizonBoundary : Prop)
    (hFinite : exactModel.RecordsFiniteModelBoundary)
    (hExact : exactModel.RecordsExactCoverBoundary)
    (hObservation : exactModel.RecordsObservationBoundary)
    (hProjection : selectedSlice.RecordsProjectionBoundary)
    (hAATObservation : selectedSlice.RecordsObservationBoundary)
    (hReconstruction : selectedSlice.RecordsReconstructionBoundary)
    (hMissingEvidence : selectedSlice.RecordsMissingEvidence)
    (archSigReportBoundary theoremBoundary typedFailureBoundary
      nonConclusions : Prop)
    (hBoundary : nonConclusions)
    (hSlice : selectedSlice.RecordsNonConclusions)
    (hAAT : aatStatus.RecordsNonConclusions)
    (hExactNonConclusions : exactModel.RecordsNonConclusions) :
    (ofSelectedSliceAndFiniteExactModel
      (exactModel := exactModel) (source := source) (horizon := horizon)
      selectedSlice aatStatus forecastStatus interfaceBoundary
      selectedSourceBoundary selectedHorizonBoundary hFinite hExact
      hObservation hProjection hAATObservation hReconstruction
      hMissingEvidence archSigReportBoundary theoremBoundary
      typedFailureBoundary nonConclusions).RecordsNonConclusions :=
  (ofSelectedSliceAndFiniteExactModel
    (exactModel := exactModel) (source := source) (horizon := horizon)
    selectedSlice aatStatus forecastStatus interfaceBoundary
    selectedSourceBoundary selectedHorizonBoundary hFinite hExact
    hObservation hProjection hAATObservation hReconstruction
    hMissingEvidence archSigReportBoundary theoremBoundary
    typedFailureBoundary nonConclusions).preserves_nonConclusions
      hBoundary hSlice hAAT hExactNonConclusions

end AATSupportedSFTBoundary

/-- AAT/SFT boundary failure classes that can be read as typed SFT failures. -/
inductive AATSFTBoundaryFailureKind where
  | expressionBoundary
  | projectionBoundary
  | observationBoundary
  | reconstructionBoundary
  | missingEvidence
  | theoremStatusBoundary
  | archSigReportBoundary
  deriving DecidableEq, Repr

/-- AAT/SFT boundary failure witness before it is read as an SFT typed failure. -/
structure AATSFTBoundaryFailure where
  kind : AATSFTBoundaryFailureKind
  explainsAATBoundary : Prop
  evidenceBoundary : Prop
  nonConclusions : Prop

namespace AATSFTBoundaryFailure

/-- Generic constructor for a typed AAT/SFT boundary failure. -/
def ofKind
    (kind : AATSFTBoundaryFailureKind)
    (explainsAATBoundary evidenceBoundary nonConclusions : Prop) :
    AATSFTBoundaryFailure where
  kind := kind
  explainsAATBoundary := explainsAATBoundary
  evidenceBoundary := evidenceBoundary
  nonConclusions := nonConclusions

def expressionBoundary :=
  ofKind AATSFTBoundaryFailureKind.expressionBoundary

def projectionBoundary :=
  ofKind AATSFTBoundaryFailureKind.projectionBoundary

def observationBoundary :=
  ofKind AATSFTBoundaryFailureKind.observationBoundary

def reconstructionBoundary :=
  ofKind AATSFTBoundaryFailureKind.reconstructionBoundary

def missingEvidence :=
  ofKind AATSFTBoundaryFailureKind.missingEvidence

def theoremStatusBoundary :=
  ofKind AATSFTBoundaryFailureKind.theoremStatusBoundary

def archSigReportBoundary :=
  ofKind AATSFTBoundaryFailureKind.archSigReportBoundary

/-- Constructor helpers preserve the fine-grained AAT/SFT boundary kind. -/
theorem ofKind_records_kind
    (kind : AATSFTBoundaryFailureKind)
    (explainsAATBoundary evidenceBoundary nonConclusions : Prop) :
    (ofKind kind explainsAATBoundary evidenceBoundary nonConclusions).kind =
      kind :=
  rfl

def toFundamentalBoundaryFailureKind
    (_failure : AATSFTBoundaryFailure) :
    FundamentalBoundaryFailureKind :=
  FundamentalBoundaryFailureKind.theoremFamilyAssumptionMissing

def toTypedComputationBoundaryFailure
    (failure : AATSFTBoundaryFailure) :
    TypedComputationBoundaryFailure where
  kind := failure.toFundamentalBoundaryFailureKind
  explainsBrokenBoundary := failure.explainsAATBoundary
  evidenceBoundary := failure.evidenceBoundary
  nonConclusions := failure.nonConclusions

/--
Typed SFT failure together with the AAT/SFT-specific boundary kind that produced
it.

`TypedComputationBoundaryFailure` uses the coarser final-assembly failure
vocabulary.  This wrapper keeps the finer AAT/SFT boundary classification
available after the typed conversion.
-/
structure AATTypedComputationBoundaryFailure where
  sourceFailure : AATSFTBoundaryFailure
  typedFailure : TypedComputationBoundaryFailure
  recordsKind : AATSFTBoundaryFailureKind
  recordsKind_eq_source : recordsKind = sourceFailure.kind
  typedFailure_eq_source : typedFailure = sourceFailure.toTypedComputationBoundaryFailure
  explains_preserved :
    typedFailure.explainsBrokenBoundary = sourceFailure.explainsAATBoundary
  nonConclusions_preserved :
    typedFailure.nonConclusions = sourceFailure.nonConclusions

def toAATTypedComputationBoundaryFailure
    (failure : AATSFTBoundaryFailure) :
    AATTypedComputationBoundaryFailure where
  sourceFailure := failure
  typedFailure := failure.toTypedComputationBoundaryFailure
  recordsKind := failure.kind
  recordsKind_eq_source := rfl
  typedFailure_eq_source := rfl
  explains_preserved := rfl
  nonConclusions_preserved := rfl

theorem toTypedComputationBoundaryFailure_explains
    (failure : AATSFTBoundaryFailure) :
    failure.toTypedComputationBoundaryFailure.explainsBrokenBoundary =
      failure.explainsAATBoundary :=
  rfl

theorem toTypedComputationBoundaryFailure_preserves_nonConclusions
    (failure : AATSFTBoundaryFailure) :
    failure.toTypedComputationBoundaryFailure.nonConclusions =
      failure.nonConclusions :=
  rfl

theorem toAATTypedComputationBoundaryFailure_records_kind
    (failure : AATSFTBoundaryFailure) :
    failure.toAATTypedComputationBoundaryFailure.recordsKind = failure.kind :=
  rfl

theorem toAATTypedComputationBoundaryFailure_preserves_typed_failure
    (failure : AATSFTBoundaryFailure) :
    failure.toAATTypedComputationBoundaryFailure.typedFailure =
      failure.toTypedComputationBoundaryFailure :=
  rfl

theorem toAATTypedComputationBoundaryFailure_preserves_explanation
    (failure : AATSFTBoundaryFailure) :
    failure.toAATTypedComputationBoundaryFailure.typedFailure.explainsBrokenBoundary =
      failure.explainsAATBoundary :=
  rfl

theorem toAATTypedComputationBoundaryFailure_preserves_nonConclusions
    (failure : AATSFTBoundaryFailure) :
    failure.toAATTypedComputationBoundaryFailure.typedFailure.nonConclusions =
      failure.nonConclusions :=
  rfl

end AATSFTBoundaryFailure

/--
Final AAT-supported Fundamental Modularity package.

It wraps the existing finite selected final theorem package with the AAT/SFT
boundary record that made the selected slice and theorem-status reading
explicit.
-/
structure AATSupportedFundamentalModularityPackage
    {Global : Type u} {Index : Type v} {Local : Type w}
    {OperationG : Type x} {OperationL : Type y}
    {Governance : Type z}
    (exactModel :
      FiniteExactSFTModel Global Index Local OperationG OperationL Governance)
    (source : Global) (horizon : Nat) where
  boundary : AATSupportedSFTBoundary exactModel source horizon
  finalPackage :
    FiniteSelectedFundamentalModularityTheorem exactModel source horizon
  recordsBoundary : boundary.RecordsTheoremAndModelBoundaries
  recordsNonConclusions : boundary.RecordsNonConclusions
  recordsFinalNonConclusions : finalPackage.RecordsNonConclusions

namespace AATSupportedFundamentalModularityPackage

variable {Global : Type u} {Index : Type v} {Local : Type w}
variable {OperationG : Type x} {OperationL : Type y}
variable {Governance : Type z}
variable {exactModel :
  FiniteExactSFTModel Global Index Local OperationG OperationL Governance}
variable {source : Global} {horizon : Nat}

def ofBoundaryAndFiniteSelectedHypotheses
    (boundary : AATSupportedSFTBoundary exactModel source horizon)
    (hypotheses : FundamentalModularityHypotheses)
    (hGovernance : exactModel.RecordsGovernanceBasisBoundary)
    (hAATTheorem : boundary.aatStatus.RecordsTheoremBoundary)
    (hForecastTheorem : boundary.forecastStatus.RecordsTheoremBoundary)
    (hArchSigReport : boundary.archSigReportBoundary)
    (hTheoremBoundary : boundary.theoremBoundary)
    (hTypedFailureBoundary : boundary.typedFailureBoundary)
    (hBoundaryNonConclusions : boundary.nonConclusions)
    (hSliceNonConclusions : boundary.selectedSlice.RecordsNonConclusions)
    (hAATNonConclusions : boundary.aatStatus.RecordsNonConclusions)
    (hExactNonConclusions : exactModel.RecordsNonConclusions)
    (hHypothesesNonConclusions : hypotheses.nonConclusions) :
    AATSupportedFundamentalModularityPackage exactModel source horizon where
  boundary := boundary
  finalPackage :=
    FiniteSelectedFundamentalModularityTheorem.ofFiniteExactComponents
      (exactModel := exactModel) (source := source) (horizon := horizon)
      hypotheses boundary.recordsExactCoverBoundary
      boundary.recordsFiniteSelectedModel boundary.recordsObservationBoundary
      hGovernance boundary.theoremBoundary boundary.nonConclusions
  recordsBoundary :=
    ⟨boundary.recordsExactCoverBoundary, boundary.recordsObservationBoundary,
      hAATTheorem, hForecastTheorem, hArchSigReport,
      hTheoremBoundary, hTypedFailureBoundary⟩
  recordsNonConclusions :=
    boundary.preserves_nonConclusions hBoundaryNonConclusions
      hSliceNonConclusions hAATNonConclusions hExactNonConclusions
  recordsFinalNonConclusions :=
    ⟨hBoundaryNonConclusions, hExactNonConclusions, hHypothesesNonConclusions⟩

theorem finiteSelected_fundamental_modularity
    (package :
      AATSupportedFundamentalModularityPackage exactModel source horizon) :
    package.finalPackage.hypotheses.descent.modularityAsDescent ∧
      package.finalPackage.hypotheses.obstruction.technicalDebtAsObstruction ∧
      package.finalPackage.hypotheses.review.minimalDecisionPreservingEnvelope ∧
      package.finalPackage.hypotheses.governance.governanceAsObstructionCutting ∧
      package.finalPackage.hypotheses.calibration.boundaryExplicitFixedPoint ∧
      package.finalPackage.hypotheses.agentic.agenticConfluence ∧
      (package.finalPackage.hypotheses.governed.governedBoundary ∨
        package.finalPackage.hypotheses.failure.explainsBrokenBoundary) :=
  package.finalPackage.finiteSelected_fundamental_modularity

theorem governed_or_typed_boundary_failure
    (package :
      AATSupportedFundamentalModularityPackage exactModel source horizon) :
    package.finalPackage.hypotheses.governed.governedBoundary ∨
      package.finalPackage.hypotheses.failure.explainsBrokenBoundary :=
  package.finalPackage.governed_or_typed_failure

theorem modularity_iff_forecastConeDescent
    (package :
      AATSupportedFundamentalModularityPackage exactModel source horizon) :
    package.finalPackage.roadmapPackage.modularity ↔
      package.finalPackage.roadmapPackage.forecastConeDescent :=
  package.finalPackage.modularity_iff_forecastConeDescent

theorem preserves_boundary_nonConclusions
    (package :
      AATSupportedFundamentalModularityPackage exactModel source horizon) :
    package.boundary.RecordsNonConclusions :=
  package.recordsNonConclusions

theorem does_not_promote_to_unconditional_claim
    (package :
      AATSupportedFundamentalModularityPackage exactModel source horizon) :
    package.boundary.RecordsNonConclusions ∧
      package.finalPackage.RecordsNonConclusions :=
  ⟨package.recordsNonConclusions, package.recordsFinalNonConclusions⟩

/--
Final typed conclusion for the AAT-supported package.

The first two branches are the existing finite selected final-assembly
conclusion.  The third branch exposes an AAT/SFT boundary failure while keeping
the finer AAT/SFT boundary kind available through
`AATTypedComputationBoundaryFailure.recordsKind`.
-/
def AATSupportedFinalTypedConclusion
    (package :
      AATSupportedFundamentalModularityPackage exactModel source horizon) :
    Prop :=
  package.finalPackage.hypotheses.governed.governedBoundary ∨
    package.finalPackage.hypotheses.failure.explainsBrokenBoundary ∨
      ∃ failure : AATSFTBoundaryFailure.AATTypedComputationBoundaryFailure,
        failure.typedFailure.explainsBrokenBoundary

theorem governed_or_finite_failure_or_aat_boundary_failure
    (package :
      AATSupportedFundamentalModularityPackage exactModel source horizon) :
    package.AATSupportedFinalTypedConclusion :=
  match package.governed_or_typed_boundary_failure with
  | Or.inl hGoverned => Or.inl hGoverned
  | Or.inr hFiniteFailure => Or.inr (Or.inl hFiniteFailure)

theorem aat_boundary_failure_enters_final_typed_conclusion
    (package :
      AATSupportedFundamentalModularityPackage exactModel source horizon)
    (failure : AATSFTBoundaryFailure)
    (hFailure : failure.explainsAATBoundary) :
    package.AATSupportedFinalTypedConclusion :=
  Or.inr (Or.inr
    ⟨failure.toAATTypedComputationBoundaryFailure,
      by
        simpa
          [AATSFTBoundaryFailure.toAATTypedComputationBoundaryFailure,
            AATSFTBoundaryFailure.toTypedComputationBoundaryFailure]
          using hFailure⟩)

theorem aat_boundary_failure_kind_preserved_in_final_typed_conclusion
    (failure : AATSFTBoundaryFailure) :
    failure.toAATTypedComputationBoundaryFailure.recordsKind = failure.kind :=
  failure.toAATTypedComputationBoundaryFailure_records_kind

theorem aat_boundary_failure_nonConclusions_preserved_in_final_typed_conclusion
    (failure : AATSFTBoundaryFailure) :
    failure.toAATTypedComputationBoundaryFailure.typedFailure.nonConclusions =
      failure.nonConclusions :=
  failure.toAATTypedComputationBoundaryFailure_preserves_nonConclusions

/--
Explicit assumption ledger for the AAT-supported Grand Theorem package.

This is a reading surface: it records the selected finite model, selected
source/horizon, AAT/SFT boundary, final component hypotheses, and
non-conclusion boundaries that support the final typed conclusion.  It does not
discharge those assumptions unconditionally.
-/
structure ExplicitAssumptionLedger
    (package :
      AATSupportedFundamentalModularityPackage exactModel source horizon) where
  selectedFiniteBoundary : package.boundary.RecordsSelectedFiniteBoundary
  aatSliceBoundaries : package.boundary.RecordsAATSliceBoundaries
  theoremAndModelBoundaries : package.boundary.RecordsTheoremAndModelBoundaries
  finalDescent : package.finalPackage.hypotheses.descent.modularityAsDescent
  finalObstruction :
    package.finalPackage.hypotheses.obstruction.technicalDebtAsObstruction
  finalReview :
    package.finalPackage.hypotheses.review.minimalDecisionPreservingEnvelope
  finalGovernance :
    package.finalPackage.hypotheses.governance.governanceAsObstructionCutting
  finalCalibration :
    package.finalPackage.hypotheses.calibration.boundaryExplicitFixedPoint
  finalAgentic : package.finalPackage.hypotheses.agentic.agenticConfluence
  finalTypedConclusion : package.AATSupportedFinalTypedConclusion
  nonConclusionBoundary :
    package.boundary.RecordsNonConclusions ∧
      package.finalPackage.RecordsNonConclusions

namespace ExplicitAssumptionLedger

def SupportsFinalTypedConclusion
    {package :
      AATSupportedFundamentalModularityPackage exactModel source horizon}
    (_ledger : ExplicitAssumptionLedger package) : Prop :=
  package.finalPackage.hypotheses.descent.modularityAsDescent ∧
    package.finalPackage.hypotheses.obstruction.technicalDebtAsObstruction ∧
      package.finalPackage.hypotheses.review.minimalDecisionPreservingEnvelope ∧
        package.finalPackage.hypotheses.governance.governanceAsObstructionCutting ∧
          package.finalPackage.hypotheses.calibration.boundaryExplicitFixedPoint ∧
            package.finalPackage.hypotheses.agentic.agenticConfluence ∧
              package.AATSupportedFinalTypedConclusion

def SupportsNonConclusionBoundary
    {package :
      AATSupportedFundamentalModularityPackage exactModel source horizon}
    (_ledger : ExplicitAssumptionLedger package) : Prop :=
  package.boundary.RecordsSelectedFiniteBoundary ∧
    package.boundary.RecordsAATSliceBoundaries ∧
      package.boundary.RecordsTheoremAndModelBoundaries ∧
        package.boundary.RecordsNonConclusions ∧
          package.finalPackage.RecordsNonConclusions

end ExplicitAssumptionLedger

def explicitAssumptionLedger
    (package :
      AATSupportedFundamentalModularityPackage exactModel source horizon)
    (hSelected :
      package.boundary.selectedSlice.RecordsSelectedArchitecture)
    (hSource : package.boundary.selectedSourceBoundary)
    (hHorizon : package.boundary.selectedHorizonBoundary) :
    ExplicitAssumptionLedger package where
  selectedFiniteBoundary :=
    package.boundary.records_selected_finite_source_horizon
      hSelected hSource hHorizon
  aatSliceBoundaries :=
    package.boundary.records_projection_observation_reconstruction_missingEvidence
  theoremAndModelBoundaries := package.recordsBoundary
  finalDescent := package.finalPackage.hypotheses.hModularity
  finalObstruction := package.finalPackage.hypotheses.hDebt
  finalReview := package.finalPackage.hypotheses.hReview
  finalGovernance := package.finalPackage.hypotheses.hGovernance
  finalCalibration := package.finalPackage.hypotheses.hLearning
  finalAgentic := package.finalPackage.hypotheses.hAgentic
  finalTypedConclusion := package.governed_or_finite_failure_or_aat_boundary_failure
  nonConclusionBoundary := package.does_not_promote_to_unconditional_claim

theorem explicitAssumptionLedger_supports_final_typed_conclusion
    {package :
      AATSupportedFundamentalModularityPackage exactModel source horizon}
    (ledger : ExplicitAssumptionLedger package) :
    ledger.SupportsFinalTypedConclusion :=
  ⟨ledger.finalDescent, ledger.finalObstruction, ledger.finalReview,
    ledger.finalGovernance, ledger.finalCalibration, ledger.finalAgentic,
    ledger.finalTypedConclusion⟩

theorem explicitAssumptionLedger_supports_nonConclusion_boundary
    {package :
      AATSupportedFundamentalModularityPackage exactModel source horizon}
    (ledger : ExplicitAssumptionLedger package) :
    ledger.SupportsNonConclusionBoundary :=
  ⟨ledger.selectedFiniteBoundary, ledger.aatSliceBoundaries,
    ledger.theoremAndModelBoundaries, ledger.nonConclusionBoundary⟩

theorem finite_failure_enters_final_typed_conclusion
    (package :
      AATSupportedFundamentalModularityPackage exactModel source horizon)
    (hFailure :
      package.finalPackage.hypotheses.failure.explainsBrokenBoundary) :
    package.AATSupportedFinalTypedConclusion :=
  Or.inr (Or.inl hFailure)

theorem final_typed_conclusion_records_finite_or_aat_failure_taxonomy
    (package :
      AATSupportedFundamentalModularityPackage exactModel source horizon) :
    package.finalPackage.hypotheses.governed.governedBoundary ∨
      package.finalPackage.hypotheses.failure.explainsBrokenBoundary ∨
        ∃ failure : AATSFTBoundaryFailure.AATTypedComputationBoundaryFailure,
          failure.typedFailure.explainsBrokenBoundary :=
  package.governed_or_finite_failure_or_aat_boundary_failure

theorem final_failure_taxonomy_preserves_nonConclusions
    (package :
      AATSupportedFundamentalModularityPackage exactModel source horizon)
    (failure : AATSFTBoundaryFailure) :
    package.boundary.RecordsNonConclusions ∧
      package.finalPackage.RecordsNonConclusions ∧
      failure.toAATTypedComputationBoundaryFailure.typedFailure.nonConclusions =
        failure.nonConclusions :=
  ⟨package.recordsNonConclusions, package.recordsFinalNonConclusions,
    failure.toAATTypedComputationBoundaryFailure_preserves_nonConclusions⟩

/--
Lifecycle bifurcation as a sidecar to the final typed-failure reading.

The sidecar records lifecycle pressure facts next to the final typed
conclusion.  Its non-conclusion field keeps the reading from becoming a
runtime-failure or empirical-incident theorem.
-/
structure LifecycleTypedFailureSidecar
    (package :
      AATSupportedFundamentalModularityPackage exactModel source horizon)
    {Field : Type a}
    (lifecycle : SFTTheoremRoadmap.LifecycleBifurcationPackage Field)
    (field : Field) where
  finalTypedConclusion : package.AATSupportedFinalTypedConclusion
  lifecycleBifurcation : ¬ lifecycle.repairOnlyPreservesTarget field
  pressureRegimeNotRepair :
    lifecycle.pressureRegime field ≠
      SFTTheoremRoadmap.LifecyclePressureRegime.repair
  sidecarBoundary : lifecycle.lifecycleBoundary
  nonConclusionBoundary :
    package.boundary.RecordsNonConclusions ∧
      package.finalPackage.RecordsNonConclusions ∧ lifecycle.nonConclusions

def lifecycleTypedFailureSidecar_of_threshold
    (package :
      AATSupportedFundamentalModularityPackage exactModel source horizon)
    {Field : Type a}
    (lifecycle : SFTTheoremRoadmap.LifecycleBifurcationPackage Field)
    (field : Field)
    (hGe : lifecycle.threshold <= lifecycle.obstructionMeasure field)
    (hBoundary : lifecycle.lifecycleBoundary)
    (hLifecycleNonConclusions : lifecycle.nonConclusions) :
    LifecycleTypedFailureSidecar package lifecycle field where
  finalTypedConclusion := package.governed_or_finite_failure_or_aat_boundary_failure
  lifecycleBifurcation :=
    lifecycle.lifecycle_bifurcation_above_threshold field hGe
  pressureRegimeNotRepair :=
    lifecycle.lifecycle_pressure_regime_of_threshold field hGe
  sidecarBoundary := hBoundary
  nonConclusionBoundary :=
    ⟨package.recordsNonConclusions, package.recordsFinalNonConclusions,
      hLifecycleNonConclusions⟩

/-- Lifecycle sidecar accessor for the final typed conclusion. -/
theorem lifecycleTypedFailureSidecar_records_final_typed_conclusion
    (package :
      AATSupportedFundamentalModularityPackage exactModel source horizon)
    {Field : Type a}
    (lifecycle : SFTTheoremRoadmap.LifecycleBifurcationPackage Field)
    (field : Field)
    (hGe : lifecycle.threshold <= lifecycle.obstructionMeasure field)
    (hBoundary : lifecycle.lifecycleBoundary)
    (hLifecycleNonConclusions : lifecycle.nonConclusions) :
    package.AATSupportedFinalTypedConclusion :=
  (lifecycleTypedFailureSidecar_of_threshold package lifecycle field hGe
      hBoundary hLifecycleNonConclusions).finalTypedConclusion

/--
Field-shaping fixed-point sidecar for AAT-supported Grand Theorem packages.

The selected fixed points come from the SFT roadmap package; the sidecar does
not claim runtime behavior equivalence or empirical outcome preservation.
-/
structure FieldShapingConclusionSidecar
    (package :
      AATSupportedFundamentalModularityPackage exactModel source horizon)
    {Transformation : Type a}
    {shape : Transformation -> Transformation}
    (fieldShaping :
      SFTTheoremRoadmap.FieldShapingFixedPointPackage Transformation shape) where
  finalTypedConclusion : package.AATSupportedFinalTypedConclusion
  selectedFixedPoints :
    ∃ least greatest,
      SFTTheoremRoadmap.IsLeastFixedPoint fieldShaping.le shape least ∧
        SFTTheoremRoadmap.IsGreatestFixedPoint fieldShaping.le shape greatest
  minimalPreservesDesiredAndExcludesBad :
    fieldShaping.RecordsMinimalPreservesDesiredAndExcludesBad
  sidecarBoundary : fieldShaping.fieldShapingBoundary
  nonConclusionBoundary :
    package.boundary.RecordsNonConclusions ∧
      package.finalPackage.RecordsNonConclusions ∧
        fieldShaping.nonConclusions

def fieldShapingConclusionSidecar_of_fixedPointPackage
    (package :
      AATSupportedFundamentalModularityPackage exactModel source horizon)
    {Transformation : Type a}
    {shape : Transformation -> Transformation}
    (fieldShaping :
      SFTTheoremRoadmap.FieldShapingFixedPointPackage Transformation shape)
    (hComplete : fieldShaping.supportTransformationsCompleteLattice)
    (hMonotone : fieldShaping.monotone)
    (hMinimal :
      fieldShaping.RecordsMinimalPreservesDesiredAndExcludesBad)
    (hBoundary : fieldShaping.fieldShapingBoundary)
    (hNonConclusions : fieldShaping.nonConclusions) :
    FieldShapingConclusionSidecar package fieldShaping where
  finalTypedConclusion := package.governed_or_finite_failure_or_aat_boundary_failure
  selectedFixedPoints :=
    fieldShaping.fieldShaping_fixedPoints hComplete hMonotone
  minimalPreservesDesiredAndExcludesBad :=
    hMinimal
  sidecarBoundary := hBoundary
  nonConclusionBoundary :=
    ⟨package.recordsNonConclusions, package.recordsFinalNonConclusions,
      hNonConclusions⟩

theorem fieldShapingConclusionSidecar_records_final_typed_conclusion
    (package :
      AATSupportedFundamentalModularityPackage exactModel source horizon)
    {Transformation : Type a}
    {shape : Transformation -> Transformation}
    (fieldShaping :
      SFTTheoremRoadmap.FieldShapingFixedPointPackage Transformation shape)
    (hComplete : fieldShaping.supportTransformationsCompleteLattice)
    (hMonotone : fieldShaping.monotone)
    (hMinimal :
      fieldShaping.RecordsMinimalPreservesDesiredAndExcludesBad)
    (hBoundary : fieldShaping.fieldShapingBoundary)
    (hNonConclusions : fieldShaping.nonConclusions) :
    package.AATSupportedFinalTypedConclusion :=
  (fieldShapingConclusionSidecar_of_fixedPointPackage package fieldShaping
      hComplete hMonotone hMinimal hBoundary hNonConclusions).finalTypedConclusion

/--
Allowed transformation between two selected AAT-supported Grand Theorem
packages.

The preservation maps are explicit assumptions.  They are not a theorem about
arbitrary refactorings, runtime behavior, or empirical outcomes.
-/
structure AllowedGrandTheoremTransformation
    (sourcePackage :
      AATSupportedFundamentalModularityPackage exactModel source horizon)
    {Global' : Type u} {Index' : Type v} {Local' : Type w}
    {OperationG' : Type x} {OperationL' : Type y}
    {Governance' : Type z}
    {exactModel' :
      FiniteExactSFTModel Global' Index' Local' OperationG' OperationL'
        Governance'}
    {source' : Global'} {horizon' : Nat}
    (targetPackage :
      AATSupportedFundamentalModularityPackage exactModel' source' horizon') where
  preservesFinalTypedConclusion :
    sourcePackage.AATSupportedFinalTypedConclusion ->
      targetPackage.AATSupportedFinalTypedConclusion
  preservesNonConclusionBoundary :
    sourcePackage.boundary.RecordsNonConclusions ∧
      sourcePackage.finalPackage.RecordsNonConclusions ->
        targetPackage.boundary.RecordsNonConclusions ∧
          targetPackage.finalPackage.RecordsNonConclusions
  transformationBoundary : Prop
  nonConclusions : Prop

/--
Evolutionary-invariance sidecar for AAT-supported Grand Theorem packages.

The `evolutionarilyEquivalent` field comes from the roadmap package.  Final
typed-conclusion and non-conclusion preservation come only from the selected
allowed transformation, keeping semantic equivalence and operational safety out
of the conclusion.
-/
structure EvolutionaryConclusionPreservation
    (sourcePackage :
      AATSupportedFundamentalModularityPackage exactModel source horizon)
    {Global' : Type u} {Index' : Type v} {Local' : Type w}
    {OperationG' : Type x} {OperationL' : Type y}
    {Governance' : Type z}
    {exactModel' :
      FiniteExactSFTModel Global' Index' Local' OperationG' OperationL'
        Governance'}
    {source' : Global'} {horizon' : Nat}
    (targetPackage :
      AATSupportedFundamentalModularityPackage exactModel' source' horizon')
    {Field : Type a}
    (invariance : SFTTheoremRoadmap.EvolutionaryInvariancePackage Field)
    (F G : Field) where
  evolutionarilyEquivalent : invariance.evolutionarilyEquivalent F G
  targetFinalTypedConclusion : targetPackage.AATSupportedFinalTypedConclusion
  targetNonConclusionBoundary :
    targetPackage.boundary.RecordsNonConclusions ∧
      targetPackage.finalPackage.RecordsNonConclusions
  invarianceBoundary : invariance.invarianceBoundary
  transformationBoundary : Prop
  transformationNonConclusions : Prop
  nonConclusions : invariance.nonConclusions ∧ transformationNonConclusions

def evolutionaryConclusionPreservation_of_allowedTransformation
    (sourcePackage :
      AATSupportedFundamentalModularityPackage exactModel source horizon)
    {Global' : Type u} {Index' : Type v} {Local' : Type w}
    {OperationG' : Type x} {OperationL' : Type y}
    {Governance' : Type z}
    {exactModel' :
      FiniteExactSFTModel Global' Index' Local' OperationG' OperationL'
        Governance'}
    {source' : Global'} {horizon' : Nat}
    (targetPackage :
      AATSupportedFundamentalModularityPackage exactModel' source' horizon')
    {Field : Type a}
    (invariance : SFTTheoremRoadmap.EvolutionaryInvariancePackage Field)
    (F G : Field)
    (hCone : invariance.forecastConesNaturallyEquivalent F G)
    (transformation :
      AllowedGrandTheoremTransformation sourcePackage targetPackage)
    (hInvarianceBoundary : invariance.invarianceBoundary)
    (hInvarianceNonConclusions : invariance.nonConclusions)
    (hTransformationNonConclusions : transformation.nonConclusions) :
    EvolutionaryConclusionPreservation sourcePackage targetPackage
      invariance F G where
  evolutionarilyEquivalent := invariance.evolutionary_invariance F G hCone
  targetFinalTypedConclusion :=
    transformation.preservesFinalTypedConclusion
      sourcePackage.governed_or_finite_failure_or_aat_boundary_failure
  targetNonConclusionBoundary :=
    transformation.preservesNonConclusionBoundary
      sourcePackage.does_not_promote_to_unconditional_claim
  invarianceBoundary := hInvarianceBoundary
  transformationBoundary := transformation.transformationBoundary
  transformationNonConclusions := transformation.nonConclusions
  nonConclusions := ⟨hInvarianceNonConclusions, hTransformationNonConclusions⟩

end AATSupportedFundamentalModularityPackage

end SFTAATFundamentalModularity
end Formal.Arch
