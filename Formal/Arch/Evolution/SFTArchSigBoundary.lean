import Formal.Arch.Evolution.SFTField
import Formal.Arch.Evolution.SFTInterfaceBoundary

namespace Formal.Arch

universe u v w q r s

/--
Lean-side boundary record for an ArchSig report read as SFT input.

The report stores one selected `SoftwareFieldEstimate` together with
tooling-facing candidates and explicit boundaries. It is not a ground-truth
architecture object, an AAT theorem package, or a calibrated forecast
certificate.
-/
structure ArchSigSFTReport
    (FieldState : Type s) (C : Type u) (A : Type v)
    (StaticObs : Type w) (SemanticExpr : Type q)
    (SemanticObs : Type r) where
  selectedEstimate :
    SoftwareFieldEstimate FieldState C A StaticObs SemanticExpr SemanticObs
  actionClassCandidates : Prop
  targetRegions : Prop
  candidateOperationFamilies : Prop
  comparableSignatureAxes : Prop
  coverageAssumptions : Prop
  observationBoundary : Prop
  reconstructionBoundary : Prop
  missingInvariants : Prop
  unmeasuredAxes : Prop
  theoremBoundary : Prop
  forecastBoundary : Prop
  reportBoundary : Prop
  nonConclusions : Prop

namespace ArchSigSFTReport

variable {FieldState : Type s} {C : Type u} {A : Type v}
variable {StaticObs : Type w} {SemanticExpr : Type q}
variable {SemanticObs : Type r}

/-- The selected SFT estimate carried by the report. -/
def estimate
    (report : ArchSigSFTReport FieldState C A StaticObs SemanticExpr SemanticObs) :
    SoftwareFieldEstimate FieldState C A StaticObs SemanticExpr SemanticObs :=
  report.selectedEstimate

/-- Action-class candidates remain report-side candidate data. -/
def RecordsActionClassCandidates
    (report : ArchSigSFTReport FieldState C A StaticObs SemanticExpr SemanticObs) :
    Prop :=
  report.actionClassCandidates

/-- Target regions remain report-side candidate data. -/
def RecordsTargetRegions
    (report : ArchSigSFTReport FieldState C A StaticObs SemanticExpr SemanticObs) :
    Prop :=
  report.targetRegions

/-- Candidate operation families remain report-side candidate data. -/
def RecordsCandidateOperationFamilies
    (report : ArchSigSFTReport FieldState C A StaticObs SemanticExpr SemanticObs) :
    Prop :=
  report.candidateOperationFamilies

/-- Comparable signature axes are explicit and selected. -/
def RecordsComparableSignatureAxes
    (report : ArchSigSFTReport FieldState C A StaticObs SemanticExpr SemanticObs) :
    Prop :=
  report.comparableSignatureAxes

/-- Coverage assumptions remain explicit when a report is read as an estimate. -/
def RecordsCoverageAssumptions
    (report : ArchSigSFTReport FieldState C A StaticObs SemanticExpr SemanticObs) :
    Prop :=
  report.coverageAssumptions

/-- Observation boundaries remain explicit when a report is read as an estimate. -/
def RecordsObservationBoundary
    (report : ArchSigSFTReport FieldState C A StaticObs SemanticExpr SemanticObs) :
    Prop :=
  report.observationBoundary

/-- Reconstruction boundaries remain explicit when a report is read as an estimate. -/
def RecordsReconstructionBoundary
    (report : ArchSigSFTReport FieldState C A StaticObs SemanticExpr SemanticObs) :
    Prop :=
  report.reconstructionBoundary

/-- Missing invariants remain missing-evidence boundary data. -/
def RecordsMissingInvariants
    (report : ArchSigSFTReport FieldState C A StaticObs SemanticExpr SemanticObs) :
    Prop :=
  report.missingInvariants

/-- Unmeasured axes remain explicit rather than measured-zero evidence. -/
def RecordsUnmeasuredAxes
    (report : ArchSigSFTReport FieldState C A StaticObs SemanticExpr SemanticObs) :
    Prop :=
  report.unmeasuredAxes

/-- Theorem/modeling boundaries remain explicit. -/
def RecordsTheoremBoundary
    (report : ArchSigSFTReport FieldState C A StaticObs SemanticExpr SemanticObs) :
    Prop :=
  report.theoremBoundary

/-- Forecast correctness/calibration boundaries remain explicit. -/
def RecordsForecastBoundary
    (report : ArchSigSFTReport FieldState C A StaticObs SemanticExpr SemanticObs) :
    Prop :=
  report.forecastBoundary

/-- Report/tooling boundaries remain explicit. -/
def RecordsReportBoundary
    (report : ArchSigSFTReport FieldState C A StaticObs SemanticExpr SemanticObs) :
    Prop :=
  report.reportBoundary

/-- Report-level non-conclusions remain explicit. -/
def RecordsNonConclusions
    (report : ArchSigSFTReport FieldState C A StaticObs SemanticExpr SemanticObs) :
    Prop :=
  report.nonConclusions

/-- The report estimate accessor returns the stored selected estimate. -/
theorem estimate_eq_selectedEstimate
    (report : ArchSigSFTReport FieldState C A StaticObs SemanticExpr SemanticObs) :
    report.estimate = report.selectedEstimate :=
  rfl

end ArchSigSFTReport

/--
Boundary relation for reading an ArchSig report as an SFT estimate and forecast
status.

The relation preserves coverage, observation, reconstruction, missing evidence,
unmeasured axes, theorem boundaries, tooling/report boundaries, forecast
boundaries, and non-conclusions. It deliberately exposes preservation
obligations instead of claiming extractor completeness, AAT theorem promotion,
or calibrated forecast correctness.
-/
structure ArchSigSFTReportEstimateBoundary
    {FieldState : Type s} {C : Type u} {A : Type v}
    {StaticObs : Type w} {SemanticExpr : Type q}
    {SemanticObs : Type r}
    (report :
      ArchSigSFTReport FieldState C A StaticObs SemanticExpr SemanticObs)
    (estimate :
      SoftwareFieldEstimate FieldState C A StaticObs SemanticExpr SemanticObs)
    (forecast : SFTForecastStatus) :
    Prop where
  reportSelectsEstimate : estimate = report.estimate
  preservesCoverageAssumptions :
    report.RecordsCoverageAssumptions -> estimate.RecordsCoverageAssumptions
  preservesObservationBoundary :
    report.RecordsObservationBoundary -> estimate.RecordsObservationBoundary
  preservesReconstructionBoundary :
    report.RecordsReconstructionBoundary -> estimate.RecordsReconstructionBoundary
  preservesMissingInvariants :
    report.RecordsMissingInvariants -> estimate.RecordsMissingEvidence
  preservesUnmeasuredAxes :
    report.RecordsUnmeasuredAxes -> forecast.RecordsUnmeasuredAxisBoundary
  preservesTheoremBoundary :
    report.RecordsTheoremBoundary -> forecast.RecordsTheoremBoundary
  preservesForecastBoundary :
    report.RecordsForecastBoundary -> forecast.RecordsForecastBoundary
  recordsReportBoundary :
    report.RecordsReportBoundary -> forecast.RecordsToolingBoundary
  recordsNonConclusions :
    report.RecordsNonConclusions ->
      estimate.RecordsNonConclusions ∧ forecast.RecordsNonConclusions

namespace ArchSigSFTReportEstimateBoundary

variable {FieldState : Type s} {C : Type u} {A : Type v}
variable {StaticObs : Type w} {SemanticExpr : Type q}
variable {SemanticObs : Type r}
variable
  {report :
    ArchSigSFTReport FieldState C A StaticObs SemanticExpr SemanticObs}
variable
  {estimate :
    SoftwareFieldEstimate FieldState C A StaticObs SemanticExpr SemanticObs}
variable {forecast : SFTForecastStatus}

/-- The report boundary identifies the selected SFT estimate. -/
theorem estimate_eq_report_estimate
    (hBoundary :
      ArchSigSFTReportEstimateBoundary report estimate forecast) :
    estimate = report.estimate :=
  hBoundary.reportSelectsEstimate

/-- Report coverage assumptions are preserved when read as an SFT estimate. -/
theorem report_preserves_coverageAssumptions
    (hBoundary :
      ArchSigSFTReportEstimateBoundary report estimate forecast)
    (hCoverage : report.RecordsCoverageAssumptions) :
    estimate.RecordsCoverageAssumptions :=
  hBoundary.preservesCoverageAssumptions hCoverage

/-- Report observation boundaries are preserved when read as an SFT estimate. -/
theorem report_preserves_observationBoundary
    (hBoundary :
      ArchSigSFTReportEstimateBoundary report estimate forecast)
    (hObservation : report.RecordsObservationBoundary) :
    estimate.RecordsObservationBoundary :=
  hBoundary.preservesObservationBoundary hObservation

/-- Report reconstruction boundaries are preserved when read as an SFT estimate. -/
theorem report_preserves_reconstructionBoundary
    (hBoundary :
      ArchSigSFTReportEstimateBoundary report estimate forecast)
    (hReconstruction : report.RecordsReconstructionBoundary) :
    estimate.RecordsReconstructionBoundary :=
  hBoundary.preservesReconstructionBoundary hReconstruction

/-- Missing invariants stay missing-evidence boundary data on the estimate. -/
theorem report_missing_invariants_remain_missingEvidence
    (hBoundary :
      ArchSigSFTReportEstimateBoundary report estimate forecast)
    (hMissing : report.RecordsMissingInvariants) :
    estimate.RecordsMissingEvidence :=
  hBoundary.preservesMissingInvariants hMissing

/-- Unmeasured axes stay forecast-boundary obligations, not measured-zero evidence. -/
theorem report_unmeasured_axes_remain_forecast_boundary
    (hBoundary :
      ArchSigSFTReportEstimateBoundary report estimate forecast)
    (hUnmeasured : report.RecordsUnmeasuredAxes) :
    forecast.RecordsUnmeasuredAxisBoundary :=
  hBoundary.preservesUnmeasuredAxes hUnmeasured

/-- Report theorem-boundary items remain SFT theorem-boundary items. -/
theorem report_preserves_theoremBoundary
    (hBoundary :
      ArchSigSFTReportEstimateBoundary report estimate forecast)
    (hTheoremBoundary : report.RecordsTheoremBoundary) :
    forecast.RecordsTheoremBoundary :=
  hBoundary.preservesTheoremBoundary hTheoremBoundary

/-- Report forecast-boundary items remain forecast-boundary items. -/
theorem report_preserves_forecastBoundary
    (hBoundary :
      ArchSigSFTReportEstimateBoundary report estimate forecast)
    (hForecastBoundary : report.RecordsForecastBoundary) :
    forecast.RecordsForecastBoundary :=
  hBoundary.preservesForecastBoundary hForecastBoundary

/--
Having an ArchSig report does not promote report output into stronger AAT
theorem status; the theorem boundary is still visible on the SFT side.
-/
theorem report_existence_does_not_promote_aat_theorem_status
    (hBoundary :
      ArchSigSFTReportEstimateBoundary report estimate forecast)
    (hTheoremBoundary : report.RecordsTheoremBoundary) :
    forecast.RecordsTheoremBoundary :=
  hBoundary.preservesTheoremBoundary hTheoremBoundary

/--
Having an ArchSig report does not promote the selected estimate into calibrated
forecast correctness; the forecast boundary is still visible.
-/
theorem report_existence_does_not_promote_calibrated_forecast
    (hBoundary :
      ArchSigSFTReportEstimateBoundary report estimate forecast)
    (hForecastBoundary : report.RecordsForecastBoundary) :
    forecast.RecordsForecastBoundary :=
  hBoundary.preservesForecastBoundary hForecastBoundary

/-- Report/tooling boundaries remain SFT tooling boundaries. -/
theorem report_boundary_remains_toolingBoundary
    (hBoundary :
      ArchSigSFTReportEstimateBoundary report estimate forecast)
    (hReportBoundary : report.RecordsReportBoundary) :
    forecast.RecordsToolingBoundary :=
  hBoundary.recordsReportBoundary hReportBoundary

/-- Report non-conclusions are preserved on both estimate and forecast status. -/
theorem report_preserves_nonConclusions
    (hBoundary :
      ArchSigSFTReportEstimateBoundary report estimate forecast)
    (hNonConclusions : report.RecordsNonConclusions) :
    estimate.RecordsNonConclusions ∧ forecast.RecordsNonConclusions :=
  hBoundary.recordsNonConclusions hNonConclusions

end ArchSigSFTReportEstimateBoundary

end Formal.Arch
