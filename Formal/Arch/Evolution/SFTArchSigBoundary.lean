import Formal.Arch.Evolution.SFTField
import Formal.Arch.Evolution.SFTInterfaceBoundary
import Formal.Arch.Signature.AATCoreBridge

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

/--
ArchSig-side transition between two Atom-axiomatized AAT cores.

The transition is read through ArchSig bridges, but the bridges consume AATCore
packages; they do not define AAT and do not create atom existence.
-/
structure ArchSigAATCoreTransition
    {system : AtomAxiomSystem.{u, v}}
    (source target : AAT.AATCore system)
    {C : Type u} {A : Type v} {Obs : Type w}
    (X : ArchitectureSignature.ArchitectureLawModel C A Obs) where
  transition : AATCoreTransition source target
  sourceBridge :
    ArchitectureSignature.AATCoreSignatureLawfulnessBridge source X
  targetBridge :
    ArchitectureSignature.AATCoreSignatureLawfulnessBridge target X
  transitionBoundary : Prop
  transitionBoundaryEvidence : transitionBoundary
  archsigDoesNotDefineAAT : Prop
  archsigDoesNotDefineAATEvidence : archsigDoesNotDefineAAT
  fieldSigAnalysisBoundary : Prop
  fieldSigAnalysisBoundaryEvidence : fieldSigAnalysisBoundary
  nonConclusions : Prop

namespace ArchSigAATCoreTransition

variable {system : AtomAxiomSystem.{u, v}}
variable {source target : AAT.AATCore system}
variable {C : Type u} {A : Type v} {Obs : Type w}
variable {X : ArchitectureSignature.ArchitectureLawModel C A Obs}

/-- The ArchSig transition records its selected transition boundary. -/
theorem records_transition_boundary
    (archsigTransition : ArchSigAATCoreTransition source target X) :
    archsigTransition.transitionBoundary :=
  archsigTransition.transitionBoundaryEvidence

/-- The ArchSig transition does not define AAT. -/
theorem archsig_transition_does_not_define_aat
    (archsigTransition : ArchSigAATCoreTransition source target X) :
    archsigTransition.archsigDoesNotDefineAAT :=
  archsigTransition.archsigDoesNotDefineAATEvidence

/-- The transition remains an analysis boundary for FieldSig. -/
theorem records_fieldsig_analysis_boundary
    (archsigTransition : ArchSigAATCoreTransition source target X) :
    archsigTransition.fieldSigAnalysisBoundary :=
  archsigTransition.fieldSigAnalysisBoundaryEvidence

/-- The underlying AATCore transition does not create atom existence. -/
theorem transition_does_not_create_atoms
    (archsigTransition : ArchSigAATCoreTransition source target X) :
    system.noToolOutputCreatesAtoms :=
  archsigTransition.transition.operation_does_not_create_atoms

end ArchSigAATCoreTransition

/--
FieldSig analysis boundary over an ArchSig-observed AATCore transition.

FieldSig reads the ArchSig transition as SFT analysis input.  It preserves the
report / forecast boundaries and does not promote the report to forecast
correctness, AAT definition, or global future safety.
-/
structure FieldSigAATCoreTransitionAnalysis
    {system : AtomAxiomSystem.{u, v}}
    {source target : AAT.AATCore system}
    {C : Type u} {A : Type v} {StaticObs : Type w}
    {SemanticExpr : Type q} {SemanticObs : Type r}
    {FieldState : Type s}
    {X : ArchitectureSignature.ArchitectureLawModel C A StaticObs}
    (archsigTransition : ArchSigAATCoreTransition source target X)
    (report :
      ArchSigSFTReport FieldState C A StaticObs SemanticExpr SemanticObs)
    (estimate :
      SoftwareFieldEstimate FieldState C A StaticObs SemanticExpr SemanticObs)
    (forecast : SFTForecastStatus) :
    Prop where
  reportBoundary : ArchSigSFTReportEstimateBoundary report estimate forecast
  readsArchSigTransitionAsSFTAnalysisEvidence :
    archsigTransition.fieldSigAnalysisBoundary
  fieldSigDoesNotDefineAATEvidence :
    archsigTransition.archsigDoesNotDefineAAT
  transitionDoesNotCreateAtoms : system.noToolOutputCreatesAtoms
  forecastBoundary : forecast.RecordsForecastBoundary
  theoremBoundary : forecast.RecordsTheoremBoundary
  nonConclusions : forecast.RecordsNonConclusions

namespace FieldSigAATCoreTransitionAnalysis

variable {system : AtomAxiomSystem.{u, v}}
variable {source target : AAT.AATCore system}
variable {C : Type u} {A : Type v} {StaticObs : Type w}
variable {SemanticExpr : Type q} {SemanticObs : Type r}
variable {FieldState : Type s}
variable {X : ArchitectureSignature.ArchitectureLawModel C A StaticObs}
variable
  {archsigTransition : ArchSigAATCoreTransition source target X}
variable
  {report :
    ArchSigSFTReport FieldState C A StaticObs SemanticExpr SemanticObs}
variable
  {estimate :
    SoftwareFieldEstimate FieldState C A StaticObs SemanticExpr SemanticObs}
variable {forecast : SFTForecastStatus}

/-- FieldSig reads the ArchSig transition as SFT analysis input. -/
theorem fieldsig_reads_archsig_transition_as_sft_analysis
    (analysis :
      FieldSigAATCoreTransitionAnalysis
        archsigTransition report estimate forecast) :
    archsigTransition.fieldSigAnalysisBoundary :=
  analysis.readsArchSigTransitionAsSFTAnalysisEvidence

/-- FieldSig analysis does not define AAT. -/
theorem fieldsig_does_not_define_aat
    (analysis :
      FieldSigAATCoreTransitionAnalysis
        archsigTransition report estimate forecast) :
    archsigTransition.archsigDoesNotDefineAAT :=
  analysis.fieldSigDoesNotDefineAATEvidence

/-- FieldSig analysis over the transition does not create atom existence. -/
theorem transition_does_not_create_atoms
    (analysis :
      FieldSigAATCoreTransitionAnalysis
        archsigTransition report estimate forecast) :
    system.noToolOutputCreatesAtoms :=
  analysis.transitionDoesNotCreateAtoms

/-- Forecast correctness remains a forecast boundary. -/
theorem forecast_correctness_remains_boundary
    (analysis :
      FieldSigAATCoreTransitionAnalysis
        archsigTransition report estimate forecast) :
    forecast.RecordsForecastBoundary :=
  analysis.forecastBoundary

/-- Theorem and non-conclusion boundaries remain visible. -/
theorem theorem_and_nonConclusions_remain_boundaries
    (analysis :
      FieldSigAATCoreTransitionAnalysis
        archsigTransition report estimate forecast) :
    forecast.RecordsTheoremBoundary ∧ forecast.RecordsNonConclusions :=
  ⟨analysis.theoremBoundary, analysis.nonConclusions⟩

end FieldSigAATCoreTransitionAnalysis

end Formal.Arch
