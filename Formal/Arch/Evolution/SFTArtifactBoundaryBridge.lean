import Formal.Arch.Evolution.SFTAATFundamentalModularity
import Formal.Arch.Evolution.SFTArchSigBoundary
import Formal.Arch.Signature.ArchMap

/-!
Artifact-to-theorem-boundary bridge for AAT-supported SFT.

This module connects ArchMap and ArchSig-style artifact boundaries to the
existing AAT-supported finite selected SFT boundary surface.  The bridge keeps
the artifact evidence on the precondition/boundary side: it does not turn a
tool artifact into extractor completeness, calibrated forecast correctness, or
an assumption-free Grand Theorem.
-/

namespace Formal.Arch
namespace SFTAATFundamentalModularity

open SFTFundamentalModularity

universe u v w x y z q r s t a b c d e f

namespace AATSelectedArchitectureSlice

variable {Src : Type u} {Tgt : Type v} {Abs : Type w}
variable {StaticObs : Type q} {SrcExpr : Type r}
variable {TgtExpr : Type s} {SemanticObs : Type t}
variable {M : ArchMapModel Src Tgt Abs StaticObs SrcExpr TgtExpr SemanticObs}

/--
Read an ArchMap preservation package as the selected AAT architecture slice
needed by AAT-supported SFT.

The fields are boundary/precondition readings of the ArchMap package. They do
not assert completeness for a real extractor or for an ambient repository.
-/
def ofArchMapPreservationPackage
    (_pkg : ArchMapModel.ArchMapPreservationPackage M) :
    AATSelectedArchitectureSlice where
  selectedArchitecture := ArchMapModel.AATStructurePreserved M
  projectionBoundary :=
    ArchMapModel.ObjectRelationPreservation M ∧
      M.forgettingBoundary ∧ M.unsupportedRelationBoundary
  observationBoundary := M.coverageBoundary ∧ M.exactnessBoundary
  reconstructionBoundary :=
    ArchMapModel.SemanticDiagramPreservation M ∧
      ArchMapModel.SemanticCommutationPreservation M ∧
        ArchMapModel.NonfillabilityWitnessPreservation M
  missingEvidence := M.semanticCoverageGapBoundary
  theoremStatusBoundary := M.formalPromotionGuardrail
  nonConclusions := M.nonConclusions

theorem archMap_records_selectedArchitecture
    (pkg : ArchMapModel.ArchMapPreservationPackage M) :
    (ofArchMapPreservationPackage pkg).RecordsSelectedArchitecture :=
  pkg.aatStructurePreserved

theorem archMap_records_projectionBoundary
    (pkg : ArchMapModel.ArchMapPreservationPackage M) :
    (ofArchMapPreservationPackage pkg).RecordsProjectionBoundary :=
  ⟨pkg.objectRelationPreservation,
    pkg.forgettingBoundary, pkg.unsupportedRelationBoundary⟩

theorem archMap_records_observationBoundary
    (pkg : ArchMapModel.ArchMapPreservationPackage M) :
    (ofArchMapPreservationPackage pkg).RecordsObservationBoundary :=
  ⟨pkg.coverageBoundary, pkg.exactnessBoundary⟩

theorem archMap_records_reconstructionBoundary
    (pkg : ArchMapModel.ArchMapPreservationPackage M) :
    (ofArchMapPreservationPackage pkg).RecordsReconstructionBoundary :=
  ⟨pkg.semanticDiagramPreservation,
    pkg.semanticCommutationPreservation,
    pkg.nonfillabilityWitnessPreservation⟩

theorem archMap_records_missingEvidence
    (pkg : ArchMapModel.ArchMapPreservationPackage M) :
    (ofArchMapPreservationPackage pkg).RecordsMissingEvidence :=
  pkg.semanticMeasuredZeroUnmeasuredSeparated.2

theorem archMap_records_theoremStatusBoundary
    (pkg : ArchMapModel.ArchMapPreservationPackage M) :
    (ofArchMapPreservationPackage pkg).RecordsTheoremStatusBoundary :=
  pkg.formalPromotionGuardrail

theorem archMap_preserves_nonConclusions
    (pkg : ArchMapModel.ArchMapPreservationPackage M) :
    (ofArchMapPreservationPackage pkg).RecordsNonConclusions :=
  pkg.nonConclusions

/--
ArchMap-to-AAT homomorphic reading used by the AAT/SFT artifact bridge.

This packages the selected architecture, projection, observation,
reconstruction, missing-evidence, theorem-status, and non-conclusion readings
of the ArchMap package. It is a boundary/precondition reading, not a claim that
the supplied tooling artifact is complete or globally correct.
-/
def ArchMapAATHomomorphicReading
    (pkg : ArchMapModel.ArchMapPreservationPackage M) :
    Prop :=
  (ofArchMapPreservationPackage pkg).RecordsSelectedArchitecture ∧
  (ofArchMapPreservationPackage pkg).RecordsProjectionBoundary ∧
  (ofArchMapPreservationPackage pkg).RecordsObservationBoundary ∧
  (ofArchMapPreservationPackage pkg).RecordsReconstructionBoundary ∧
  (ofArchMapPreservationPackage pkg).RecordsMissingEvidence ∧
  (ofArchMapPreservationPackage pkg).RecordsTheoremStatusBoundary ∧
  (ofArchMapPreservationPackage pkg).RecordsNonConclusions

theorem archMap_aatHomomorphicReading
    (pkg : ArchMapModel.ArchMapPreservationPackage M) :
    ArchMapAATHomomorphicReading pkg :=
  ⟨archMap_records_selectedArchitecture pkg,
    archMap_records_projectionBoundary pkg,
    archMap_records_observationBoundary pkg,
    archMap_records_reconstructionBoundary pkg,
    archMap_records_missingEvidence pkg,
    archMap_records_theoremStatusBoundary pkg,
    archMap_preserves_nonConclusions pkg⟩

end AATSelectedArchitectureSlice

/--
SFT-side reading of an ArchSig report boundary.

This record bundles the existing report/estimate boundary with the concrete
report facts needed by the AAT-supported constructor.  It is report-boundary
evidence only, not a theorem package or calibrated forecast certificate.
-/
structure ArchSigDerivedSFTReportBoundary
    {FieldState : Type a} {C : Type b} {A : Type c}
    {StaticObs : Type d} {SemanticExpr : Type e}
    {SemanticObs : Type f}
    (report :
      ArchSigSFTReport FieldState C A StaticObs SemanticExpr SemanticObs)
    (estimate :
      SoftwareFieldEstimate FieldState C A StaticObs SemanticExpr SemanticObs)
    (forecast : SFTForecastStatus) where
  boundary : ArchSigSFTReportEstimateBoundary report estimate forecast
  recordsObservationBoundary : report.RecordsObservationBoundary
  recordsReconstructionBoundary : report.RecordsReconstructionBoundary
  recordsMissingInvariants : report.RecordsMissingInvariants
  recordsTheoremBoundary : report.RecordsTheoremBoundary
  recordsForecastBoundary : report.RecordsForecastBoundary
  recordsReportBoundary : report.RecordsReportBoundary
  recordsNonConclusions : report.RecordsNonConclusions

namespace ArchSigDerivedSFTReportBoundary

variable {FieldState : Type a} {C : Type b} {A : Type c}
variable {StaticObs : Type d} {SemanticExpr : Type e}
variable {SemanticObs : Type f}
variable
  {report :
    ArchSigSFTReport FieldState C A StaticObs SemanticExpr SemanticObs}
variable
  {estimate :
    SoftwareFieldEstimate FieldState C A StaticObs SemanticExpr SemanticObs}
variable {forecast : SFTForecastStatus}

theorem report_preserves_observationBoundary
    (derived :
      ArchSigDerivedSFTReportBoundary report estimate forecast) :
    estimate.RecordsObservationBoundary :=
  derived.boundary.report_preserves_observationBoundary
    derived.recordsObservationBoundary

theorem report_preserves_reconstructionBoundary
    (derived :
      ArchSigDerivedSFTReportBoundary report estimate forecast) :
    estimate.RecordsReconstructionBoundary :=
  derived.boundary.report_preserves_reconstructionBoundary
    derived.recordsReconstructionBoundary

theorem report_missing_invariants_remain_missingEvidence
    (derived :
      ArchSigDerivedSFTReportBoundary report estimate forecast) :
    estimate.RecordsMissingEvidence :=
  derived.boundary.report_missing_invariants_remain_missingEvidence
    derived.recordsMissingInvariants

theorem report_preserves_theoremBoundary
    (derived :
      ArchSigDerivedSFTReportBoundary report estimate forecast) :
    forecast.RecordsTheoremBoundary :=
  derived.boundary.report_preserves_theoremBoundary
    derived.recordsTheoremBoundary

theorem report_preserves_forecastBoundary
    (derived :
      ArchSigDerivedSFTReportBoundary report estimate forecast) :
    forecast.RecordsForecastBoundary :=
  derived.boundary.report_preserves_forecastBoundary
    derived.recordsForecastBoundary

theorem report_boundary_remains_toolingBoundary
    (derived :
      ArchSigDerivedSFTReportBoundary report estimate forecast) :
    forecast.RecordsToolingBoundary :=
  derived.boundary.report_boundary_remains_toolingBoundary
    derived.recordsReportBoundary

theorem report_preserves_nonConclusions
    (derived :
      ArchSigDerivedSFTReportBoundary report estimate forecast) :
    estimate.RecordsNonConclusions ∧ forecast.RecordsNonConclusions :=
  derived.boundary.report_preserves_nonConclusions
    derived.recordsNonConclusions

/--
The derived report boundary exposes theorem-boundary data, not stronger AAT
theorem status.
-/
theorem report_boundary_does_not_strengthen_theorem_status
    (derived :
      ArchSigDerivedSFTReportBoundary report estimate forecast) :
    forecast.RecordsTheoremBoundary :=
  derived.boundary.report_existence_does_not_promote_aat_theorem_status
    derived.recordsTheoremBoundary

/--
The derived report boundary keeps calibrated forecast correctness as a
forecast-boundary obligation.
-/
theorem report_boundary_does_not_calibrate_forecast
    (derived :
      ArchSigDerivedSFTReportBoundary report estimate forecast) :
    forecast.RecordsForecastBoundary :=
  derived.boundary.report_existence_does_not_promote_calibrated_forecast
    derived.recordsForecastBoundary

end ArchSigDerivedSFTReportBoundary

/--
Combined homomorphic boundary reading from an ArchMap-selected AAT slice and an
ArchSig-derived SFT report boundary.

The first component records that the ArchMap package can be read as a bounded
homomorphic AAT slice.  The second component records that the ArchSig report
preserves the selected SFT estimate / forecast boundaries.  This combined
relation is intentionally boundary-level: it does not prove calibrated forecast
correctness or turn tool output into a Lean theorem witness.
-/
def ArchMapAATSFTHomomorphicBoundary
    {Src : Type a} {Tgt : Type b} {Abs : Type c}
    {MapStaticObs : Type d} {SrcExpr : Type e}
    {TgtExpr : Type f} {MapSemanticObs : Type q}
    {M :
      ArchMapModel Src Tgt Abs MapStaticObs SrcExpr TgtExpr MapSemanticObs}
    {FieldState : Type r} {ReportC : Type s} {ReportA : Type t}
    {ReportStaticObs : Type u} {ReportSemanticExpr : Type v}
    {ReportSemanticObs : Type w}
    {report :
      ArchSigSFTReport FieldState ReportC ReportA ReportStaticObs
        ReportSemanticExpr ReportSemanticObs}
    {estimate :
      SoftwareFieldEstimate FieldState ReportC ReportA ReportStaticObs
        ReportSemanticExpr ReportSemanticObs}
    {forecast : SFTForecastStatus}
    (archMapPackage : ArchMapModel.ArchMapPreservationPackage M)
    (_archSigBoundary :
      ArchSigDerivedSFTReportBoundary report estimate forecast) :
    Prop :=
  AATSelectedArchitectureSlice.ArchMapAATHomomorphicReading
    archMapPackage ∧
  estimate.RecordsObservationBoundary ∧
  estimate.RecordsReconstructionBoundary ∧
  estimate.RecordsMissingEvidence ∧
  forecast.RecordsTheoremBoundary ∧
  forecast.RecordsForecastBoundary ∧
  forecast.RecordsToolingBoundary ∧
  estimate.RecordsNonConclusions ∧
  forecast.RecordsNonConclusions

theorem archMap_archSig_aatSftHomomorphicBoundary
    {Src : Type a} {Tgt : Type b} {Abs : Type c}
    {MapStaticObs : Type d} {SrcExpr : Type e}
    {TgtExpr : Type f} {MapSemanticObs : Type q}
    {M :
      ArchMapModel Src Tgt Abs MapStaticObs SrcExpr TgtExpr MapSemanticObs}
    {FieldState : Type r} {ReportC : Type s} {ReportA : Type t}
    {ReportStaticObs : Type u} {ReportSemanticExpr : Type v}
    {ReportSemanticObs : Type w}
    {report :
      ArchSigSFTReport FieldState ReportC ReportA ReportStaticObs
        ReportSemanticExpr ReportSemanticObs}
    {estimate :
      SoftwareFieldEstimate FieldState ReportC ReportA ReportStaticObs
        ReportSemanticExpr ReportSemanticObs}
    {forecast : SFTForecastStatus}
    (archMapPackage : ArchMapModel.ArchMapPreservationPackage M)
    (archSigBoundary :
      ArchSigDerivedSFTReportBoundary report estimate forecast) :
    ArchMapAATSFTHomomorphicBoundary archMapPackage archSigBoundary :=
  ⟨AATSelectedArchitectureSlice.archMap_aatHomomorphicReading
      archMapPackage,
    archSigBoundary.report_preserves_observationBoundary,
    archSigBoundary.report_preserves_reconstructionBoundary,
    archSigBoundary.report_missing_invariants_remain_missingEvidence,
    archSigBoundary.report_preserves_theoremBoundary,
    archSigBoundary.report_preserves_forecastBoundary,
    archSigBoundary.report_boundary_remains_toolingBoundary,
    (archSigBoundary.report_preserves_nonConclusions).1,
    (archSigBoundary.report_preserves_nonConclusions).2⟩

namespace AATSupportedSFTBoundary

variable {Global : Type u} {Index : Type v} {Local : Type w}
variable {OperationG : Type x} {OperationL : Type y}
variable {Governance : Type z}
variable {exactModel :
  FiniteExactSFTModel Global Index Local OperationG OperationL Governance}
variable {source : Global} {horizon : Nat}
variable {Src : Type a} {Tgt : Type b} {Abs : Type c}
variable {MapStaticObs : Type d} {SrcExpr : Type e}
variable {TgtExpr : Type f} {MapSemanticObs : Type q}
variable
  {M :
    ArchMapModel Src Tgt Abs MapStaticObs SrcExpr TgtExpr MapSemanticObs}
variable {FieldState : Type r} {ReportC : Type s} {ReportA : Type t}
variable {ReportStaticObs : Type u} {ReportSemanticExpr : Type v}
variable {ReportSemanticObs : Type w}
variable
  {report :
    ArchSigSFTReport FieldState ReportC ReportA ReportStaticObs
      ReportSemanticExpr ReportSemanticObs}
variable
  {estimate :
    SoftwareFieldEstimate FieldState ReportC ReportA ReportStaticObs
      ReportSemanticExpr ReportSemanticObs}
variable {aatStatus : AATTheoremStatus}
variable {forecast : SFTForecastStatus}

/--
Construct an AAT-supported SFT boundary from an ArchMap-derived selected slice
and an ArchSig-derived SFT report boundary.
-/
def ofArchMapAndArchSigBoundaries
    (archMapPackage : ArchMapModel.ArchMapPreservationPackage M)
    (_archSigBoundary :
      ArchSigDerivedSFTReportBoundary report estimate forecast)
    (interfaceBoundary : AATToSFTInterfaceBoundary aatStatus forecast)
    (selectedSourceBoundary : Prop)
    (selectedHorizonBoundary : Prop)
    (hFinite : exactModel.RecordsFiniteModelBoundary)
    (hExact : exactModel.RecordsExactCoverBoundary)
    (hObservation : exactModel.RecordsObservationBoundary)
    (theoremBoundary typedFailureBoundary nonConclusions : Prop) :
    AATSupportedSFTBoundary exactModel source horizon :=
  ofSelectedSliceAndFiniteExactModel
    (exactModel := exactModel) (source := source) (horizon := horizon)
    (AATSelectedArchitectureSlice.ofArchMapPreservationPackage
      archMapPackage)
    aatStatus forecast interfaceBoundary
    selectedSourceBoundary selectedHorizonBoundary
    hFinite hExact hObservation
    (AATSelectedArchitectureSlice.archMap_records_projectionBoundary
      archMapPackage)
    (AATSelectedArchitectureSlice.archMap_records_observationBoundary
      archMapPackage)
    (AATSelectedArchitectureSlice.archMap_records_reconstructionBoundary
      archMapPackage)
    (AATSelectedArchitectureSlice.archMap_records_missingEvidence
      archMapPackage)
    forecast.RecordsToolingBoundary
    theoremBoundary typedFailureBoundary nonConclusions

theorem artifact_constructor_records_archMap_boundaries
    (archMapPackage : ArchMapModel.ArchMapPreservationPackage M)
    (archSigBoundary :
      ArchSigDerivedSFTReportBoundary report estimate forecast)
    (interfaceBoundary : AATToSFTInterfaceBoundary aatStatus forecast)
    (selectedSourceBoundary selectedHorizonBoundary : Prop)
    (hFinite : exactModel.RecordsFiniteModelBoundary)
    (hExact : exactModel.RecordsExactCoverBoundary)
    (hObservation : exactModel.RecordsObservationBoundary)
    (theoremBoundary typedFailureBoundary nonConclusions : Prop) :
    (ofArchMapAndArchSigBoundaries
      (exactModel := exactModel) (source := source) (horizon := horizon)
      archMapPackage archSigBoundary interfaceBoundary
      selectedSourceBoundary selectedHorizonBoundary hFinite hExact
      hObservation theoremBoundary typedFailureBoundary
      nonConclusions).RecordsAATSliceBoundaries :=
  (ofArchMapAndArchSigBoundaries
      (exactModel := exactModel) (source := source) (horizon := horizon)
      archMapPackage archSigBoundary interfaceBoundary
      selectedSourceBoundary selectedHorizonBoundary hFinite hExact
      hObservation theoremBoundary typedFailureBoundary
      nonConclusions).records_projection_observation_reconstruction_missingEvidence

theorem artifact_constructor_reads_aat_status_as_sft_local_premise
    (archMapPackage : ArchMapModel.ArchMapPreservationPackage M)
    (archSigBoundary :
      ArchSigDerivedSFTReportBoundary report estimate forecast)
    (interfaceBoundary : AATToSFTInterfaceBoundary aatStatus forecast)
    (selectedSourceBoundary selectedHorizonBoundary : Prop)
    (hFinite : exactModel.RecordsFiniteModelBoundary)
    (hExact : exactModel.RecordsExactCoverBoundary)
    (hObservation : exactModel.RecordsObservationBoundary)
    (theoremBoundary typedFailureBoundary nonConclusions : Prop)
    (hAAT : aatStatus.RecordsTheoremPackage) :
    (ofArchMapAndArchSigBoundaries
      (exactModel := exactModel) (source := source) (horizon := horizon)
      archMapPackage archSigBoundary interfaceBoundary
      selectedSourceBoundary selectedHorizonBoundary hFinite hExact
      hObservation theoremBoundary typedFailureBoundary
      nonConclusions).forecastStatus.RecordsLocalPremise :=
  (ofArchMapAndArchSigBoundaries
      (exactModel := exactModel) (source := source) (horizon := horizon)
      archMapPackage archSigBoundary interfaceBoundary
      selectedSourceBoundary selectedHorizonBoundary hFinite hExact
      hObservation theoremBoundary typedFailureBoundary
      nonConclusions).aat_status_as_sft_local_premise hAAT

theorem artifact_constructor_preserves_nonConclusions
    (archMapPackage : ArchMapModel.ArchMapPreservationPackage M)
    (archSigBoundary :
      ArchSigDerivedSFTReportBoundary report estimate forecast)
    (interfaceBoundary : AATToSFTInterfaceBoundary aatStatus forecast)
    (selectedSourceBoundary selectedHorizonBoundary : Prop)
    (hFinite : exactModel.RecordsFiniteModelBoundary)
    (hExact : exactModel.RecordsExactCoverBoundary)
    (hObservation : exactModel.RecordsObservationBoundary)
    (theoremBoundary typedFailureBoundary nonConclusions : Prop)
    (hBoundary : nonConclusions)
    (hAAT : aatStatus.RecordsNonConclusions)
    (hExactNonConclusions : exactModel.RecordsNonConclusions) :
    (ofArchMapAndArchSigBoundaries
      (exactModel := exactModel) (source := source) (horizon := horizon)
      archMapPackage archSigBoundary interfaceBoundary
      selectedSourceBoundary selectedHorizonBoundary hFinite hExact
      hObservation theoremBoundary typedFailureBoundary
      nonConclusions).RecordsNonConclusions :=
  (ofArchMapAndArchSigBoundaries
      (exactModel := exactModel) (source := source) (horizon := horizon)
      archMapPackage archSigBoundary interfaceBoundary
      selectedSourceBoundary selectedHorizonBoundary hFinite hExact
      hObservation theoremBoundary typedFailureBoundary
      nonConclusions).preserves_nonConclusions
      hBoundary
      (AATSelectedArchitectureSlice.archMap_preserves_nonConclusions
        archMapPackage)
      hAAT hExactNonConclusions

end AATSupportedSFTBoundary

end SFTAATFundamentalModularity
end Formal.Arch
