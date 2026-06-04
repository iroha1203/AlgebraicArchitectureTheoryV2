import Formal.Arch.Evolution.SFTField
import Formal.Arch.Evolution.SFTInterfaceBoundary
import Formal.Arch.Signature.AATCoreBridge

namespace Formal.Arch

universe u v w q r s

/--
Lean-side boundary record for an ArchSig analysis/report state read as SFT input.

The report stores one selected `SoftwareFieldEstimate` together with
tooling-facing candidates and explicit boundaries. It is not a ground-truth
architecture object, an AAT theorem package, or a calibrated forecast
certificate. In the LLM-native tooling pipeline, FieldSig receives the
ArchSig analysis packet as bounded local AAT state rather than raw ArchMap
observations.
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

/--
Generated ArchSig-side transition between two Atom-generated AAT cores.

Unlike `ArchSigAATCoreTransition`, this record does not accept caller-supplied
Signature bridges.  The source and target bridges are computed from the
generated law models, so callers cannot discharge the transition by manually
filling an `architectureLawfulFromAAT` field.
-/
structure GeneratedArchSigAATCoreTransition
    {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    {sourceObject targetObject :
      AAT.GeneratedArchitectureObject presentation}
    (sourceModel : AAT.GeneratedArchitectureLawModel sourceObject)
    (targetModel : AAT.GeneratedArchitectureLawModel targetObject) where
  transition :
    AATCoreTransition
      sourceModel.generatedAATCore targetModel.generatedAATCore
  analyzesUsingAAT : Prop
  analyzesUsingAATEvidence : analyzesUsingAAT
  transitionBoundary : Prop
  transitionBoundaryEvidence : transitionBoundary
  archsigDoesNotDefineAAT : Prop
  archsigDoesNotDefineAATEvidence : archsigDoesNotDefineAAT
  fieldSigAnalysisBoundary : Prop
  fieldSigAnalysisBoundaryEvidence : fieldSigAnalysisBoundary
  unknownRejectedUnmeasuredSeparated : Prop
  unknownRejectedUnmeasuredSeparatedEvidence :
    unknownRejectedUnmeasuredSeparated
  measuredZeroBoundary : Prop
  validationIsNotTheoremDischarge : Prop
  nonConclusions : Prop

namespace GeneratedArchSigAATCoreTransition

variable {system : AtomAxiomSystem.{u, v}}
variable {presentation : AtomShapePresentation system}
variable
  {sourceObject targetObject :
    AAT.GeneratedArchitectureObject presentation}
variable
  {sourceModel : AAT.GeneratedArchitectureLawModel sourceObject}
variable
  {targetModel : AAT.GeneratedArchitectureLawModel targetObject}

/-- Generated transitions analyze the generated source and target AAT cores. -/
def generatedAnalyzesUsingAAT
    (_transition :
      AATCoreTransition
        sourceModel.generatedAATCore targetModel.generatedAATCore) :
    Prop :=
  sourceModel.generatedAATCore.laws sourceModel.generatedDesignLaw ∧
    targetModel.generatedAATCore.laws targetModel.generatedDesignLaw

/-- The generated source and target laws are selected in their generated cores. -/
theorem generatedAnalyzesUsingAAT_recorded
    (transition :
      AATCoreTransition
        sourceModel.generatedAATCore targetModel.generatedAATCore) :
    generatedAnalyzesUsingAAT transition :=
  ⟨sourceModel.generated_law_on_core,
    targetModel.generated_law_on_core⟩

/--
Generated ArchSig handoff does not define AAT: it reads generated cores whose
observation boundary is fixed by the root atom system and whose transition
does not create atoms.
-/
def generatedArchSigDoesNotDefineAAT
    (_transition :
      AATCoreTransition
        sourceModel.generatedAATCore targetModel.generatedAATCore) :
    Prop :=
  sourceModel.generatedAATCore.noObservationDependency ∧
    targetModel.generatedAATCore.noObservationDependency ∧
      system.noToolOutputCreatesAtoms

/-- Generated ArchSig non-definition is recorded by generated core and root facts. -/
theorem generatedArchSigDoesNotDefineAAT_recorded
    (transition :
      AATCoreTransition
        sourceModel.generatedAATCore targetModel.generatedAATCore) :
    generatedArchSigDoesNotDefineAAT transition :=
  ⟨sourceModel.generatedAATCoreNoObservationDependency_recorded,
    targetModel.generatedAATCoreNoObservationDependency_recorded,
    transition.operation_does_not_create_atoms⟩

/-- Generated transition boundaries are rooted in transition atom non-creation. -/
def generatedTransitionBoundary
    (_transition :
      AATCoreTransition
        sourceModel.generatedAATCore targetModel.generatedAATCore) :
    Prop :=
  system.noToolOutputCreatesAtoms

/-- The generated transition boundary is recorded by the operation package. -/
theorem generatedTransitionBoundary_recorded
    (transition :
      AATCoreTransition
        sourceModel.generatedAATCore targetModel.generatedAATCore) :
    generatedTransitionBoundary transition :=
  transition.operation_does_not_create_atoms

/-- FieldSig analysis over a generated transition remains a generated handoff boundary. -/
def generatedFieldSigAnalysisBoundary
    (_transition :
      AATCoreTransition
        sourceModel.generatedAATCore targetModel.generatedAATCore) :
    Prop :=
  system.noToolOutputCreatesAtoms

/-- The FieldSig analysis boundary is recorded by transition non-creation. -/
theorem generatedFieldSigAnalysisBoundary_recorded
    (transition :
      AATCoreTransition
        sourceModel.generatedAATCore targetModel.generatedAATCore) :
    generatedFieldSigAnalysisBoundary transition :=
  transition.operation_does_not_create_atoms

/-- Unknown / rejected / unmeasured readings stay separated by generated circuit boundaries. -/
def generatedUnknownRejectedUnmeasuredSeparated
    (_transition :
      AATCoreTransition
        sourceModel.generatedAATCore targetModel.generatedAATCore) :
    Prop :=
  sourceModel.generatedAATCore.circuitBoundary ∧
    targetModel.generatedAATCore.circuitBoundary

/-- Generated circuit boundaries record the unknown/rejected/unmeasured separation. -/
theorem generatedUnknownRejectedUnmeasuredSeparated_recorded
    (transition :
      AATCoreTransition
        sourceModel.generatedAATCore targetModel.generatedAATCore) :
    generatedUnknownRejectedUnmeasuredSeparated transition :=
  ⟨sourceModel.generatedAATCoreCircuitBoundary_recorded,
    targetModel.generatedAATCoreCircuitBoundary_recorded⟩

/-- Generated measured-zero boundary is the generated source/target lawfulness reading. -/
def generatedMeasuredZeroBoundary
    (_transition :
      AATCoreTransition
        sourceModel.generatedAATCore targetModel.generatedAATCore) :
    Prop :=
  ArchitectureSignature.ArchitectureLawful sourceModel.toArchitectureLawModel ∧
    ArchitectureSignature.ArchitectureLawful targetModel.toArchitectureLawModel

/-- Source and target generated lawfulness record the measured-zero boundary. -/
theorem generatedMeasuredZeroBoundary_recorded
    (transition :
      AATCoreTransition
        sourceModel.generatedAATCore targetModel.generatedAATCore) :
    generatedMeasuredZeroBoundary transition :=
  ⟨sourceModel.generatedArchitectureLawful,
    targetModel.generatedArchitectureLawful⟩

/-- Validation does not discharge theorem status by creating atoms. -/
def generatedValidationIsNotTheoremDischarge
    (_transition :
      AATCoreTransition
        sourceModel.generatedAATCore targetModel.generatedAATCore) :
    Prop :=
  system.noToolOutputCreatesAtoms

/-- Generated validation boundary is recorded by transition non-creation. -/
theorem generatedValidationIsNotTheoremDischarge_recorded
    (transition :
      AATCoreTransition
        sourceModel.generatedAATCore targetModel.generatedAATCore) :
    generatedValidationIsNotTheoremDischarge transition :=
  transition.operation_does_not_create_atoms

/-- Generated transition non-conclusions remain attached to source and target cores. -/
def generatedNonConclusions
    (_transition :
      AATCoreTransition
        sourceModel.generatedAATCore targetModel.generatedAATCore) :
    Prop :=
  sourceModel.generatedAATCore.nonConclusions ∧
    targetModel.generatedAATCore.nonConclusions

/-- Construct a generated ArchSig transition without caller-supplied bridge fields. -/
def ofTransition
    (transition :
      AATCoreTransition
        sourceModel.generatedAATCore targetModel.generatedAATCore) :
    GeneratedArchSigAATCoreTransition sourceModel targetModel where
  transition := transition
  analyzesUsingAAT := generatedAnalyzesUsingAAT transition
  analyzesUsingAATEvidence :=
    generatedAnalyzesUsingAAT_recorded transition
  transitionBoundary := generatedTransitionBoundary transition
  transitionBoundaryEvidence :=
    generatedTransitionBoundary_recorded transition
  archsigDoesNotDefineAAT :=
    generatedArchSigDoesNotDefineAAT transition
  archsigDoesNotDefineAATEvidence :=
    generatedArchSigDoesNotDefineAAT_recorded transition
  fieldSigAnalysisBoundary :=
    generatedFieldSigAnalysisBoundary transition
  fieldSigAnalysisBoundaryEvidence :=
    generatedFieldSigAnalysisBoundary_recorded transition
  unknownRejectedUnmeasuredSeparated :=
    generatedUnknownRejectedUnmeasuredSeparated transition
  unknownRejectedUnmeasuredSeparatedEvidence :=
    generatedUnknownRejectedUnmeasuredSeparated_recorded transition
  measuredZeroBoundary :=
    generatedMeasuredZeroBoundary transition
  validationIsNotTheoremDischarge :=
    generatedValidationIsNotTheoremDischarge transition
  nonConclusions := generatedNonConclusions transition

/-- Source-side Signature bridge generated from the source law model. -/
noncomputable def sourceBridge
    (archsigTransition :
      GeneratedArchSigAATCoreTransition sourceModel targetModel) :
    ArchitectureSignature.AATCoreSignatureLawfulnessBridge
      sourceModel.generatedAATCore sourceModel.toArchitectureLawModel :=
  ArchitectureSignature.AATCoreSignatureLawfulnessBridge.ofGeneratedLawModel
    sourceModel
    archsigTransition.analyzesUsingAAT
    archsigTransition.archsigDoesNotDefineAAT
    archsigTransition.unknownRejectedUnmeasuredSeparated
    archsigTransition.measuredZeroBoundary
    archsigTransition.validationIsNotTheoremDischarge
    archsigTransition.nonConclusions
    archsigTransition.analyzesUsingAATEvidence
    archsigTransition.archsigDoesNotDefineAATEvidence
    archsigTransition.unknownRejectedUnmeasuredSeparatedEvidence

/-- Target-side Signature bridge generated from the target law model. -/
noncomputable def targetBridge
    (archsigTransition :
      GeneratedArchSigAATCoreTransition sourceModel targetModel) :
    ArchitectureSignature.AATCoreSignatureLawfulnessBridge
      targetModel.generatedAATCore targetModel.toArchitectureLawModel :=
  ArchitectureSignature.AATCoreSignatureLawfulnessBridge.ofGeneratedLawModel
    targetModel
    archsigTransition.analyzesUsingAAT
    archsigTransition.archsigDoesNotDefineAAT
    archsigTransition.unknownRejectedUnmeasuredSeparated
    archsigTransition.measuredZeroBoundary
    archsigTransition.validationIsNotTheoremDischarge
    archsigTransition.nonConclusions
    archsigTransition.analyzesUsingAATEvidence
    archsigTransition.archsigDoesNotDefineAATEvidence
    archsigTransition.unknownRejectedUnmeasuredSeparatedEvidence

/-- The generated ArchSig transition records its selected boundary. -/
theorem records_transition_boundary
    (archsigTransition :
      GeneratedArchSigAATCoreTransition sourceModel targetModel) :
    archsigTransition.transitionBoundary :=
  archsigTransition.transitionBoundaryEvidence

/-- Generated ArchSig transition analysis does not define AAT. -/
theorem archsig_transition_does_not_define_aat
    (archsigTransition :
      GeneratedArchSigAATCoreTransition sourceModel targetModel) :
    archsigTransition.archsigDoesNotDefineAAT :=
  archsigTransition.archsigDoesNotDefineAATEvidence

/-- The generated transition remains an analysis boundary for FieldSig. -/
theorem records_fieldsig_analysis_boundary
    (archsigTransition :
      GeneratedArchSigAATCoreTransition sourceModel targetModel) :
    archsigTransition.fieldSigAnalysisBoundary :=
  archsigTransition.fieldSigAnalysisBoundaryEvidence

/-- The underlying generated AATCore transition does not create atom existence. -/
theorem transition_does_not_create_atoms
    (archsigTransition :
      GeneratedArchSigAATCoreTransition sourceModel targetModel) :
    system.noToolOutputCreatesAtoms :=
  archsigTransition.transition.operation_does_not_create_atoms

/-- The generated source bridge derives Signature lawfulness from the source model. -/
theorem source_bridge_architectureLawful
    (archsigTransition :
      GeneratedArchSigAATCoreTransition sourceModel targetModel) :
    ArchitectureSignature.ArchitectureLawful
      sourceModel.toArchitectureLawModel := by
  exact
    ArchitectureSignature.AATCoreSignatureLawfulnessBridge.architectureLawful
      archsigTransition.sourceBridge

/-- The generated target bridge derives Signature lawfulness from the target model. -/
theorem target_bridge_architectureLawful
    (archsigTransition :
      GeneratedArchSigAATCoreTransition sourceModel targetModel) :
    ArchitectureSignature.ArchitectureLawful
      targetModel.toArchitectureLawModel := by
  exact
    ArchitectureSignature.AATCoreSignatureLawfulnessBridge.architectureLawful
      archsigTransition.targetBridge

end GeneratedArchSigAATCoreTransition

/--
FieldSig analysis boundary over a generated ArchSig-observed AATCore transition.

The analysis consumes a generated transition and a selected ArchSig report
boundary.  It keeps report, theorem, forecast, and non-conclusion boundaries
visible, and does not turn generated AAT evidence into forecast correctness.
-/
structure GeneratedFieldSigAATCoreTransitionAnalysis
    {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    {sourceObject targetObject :
      AAT.GeneratedArchitectureObject presentation}
    {sourceModel : AAT.GeneratedArchitectureLawModel sourceObject}
    {targetModel : AAT.GeneratedArchitectureLawModel targetObject}
    {SemanticExpr : Type q} {SemanticObs : Type r}
    {FieldState : Type s}
    (archsigTransition :
      GeneratedArchSigAATCoreTransition sourceModel targetModel)
    (report :
      ArchSigSFTReport
        FieldState
        (AAT.GeneratedCarrier sourceObject)
        (AAT.GeneratedCarrier sourceObject)
        AAT.GeneratedObservationCoordinate
        SemanticExpr
        SemanticObs)
    (estimate :
      SoftwareFieldEstimate
        FieldState
        (AAT.GeneratedCarrier sourceObject)
        (AAT.GeneratedCarrier sourceObject)
        AAT.GeneratedObservationCoordinate
        SemanticExpr
        SemanticObs)
    (forecast : SFTForecastStatus) :
    Prop where
  reportBoundary : ArchSigSFTReportEstimateBoundary report estimate forecast
  readsGeneratedArchSigTransitionAsSFTAnalysisEvidence :
    archsigTransition.fieldSigAnalysisBoundary
  fieldSigDoesNotDefineAATEvidence :
    archsigTransition.archsigDoesNotDefineAAT
  transitionDoesNotCreateAtoms : system.noToolOutputCreatesAtoms
  forecastBoundary : forecast.RecordsForecastBoundary
  theoremBoundary : forecast.RecordsTheoremBoundary
  nonConclusions : forecast.RecordsNonConclusions

namespace GeneratedFieldSigAATCoreTransitionAnalysis

variable {system : AtomAxiomSystem.{u, v}}
variable {presentation : AtomShapePresentation system}
variable
  {sourceObject targetObject :
    AAT.GeneratedArchitectureObject presentation}
variable
  {sourceModel : AAT.GeneratedArchitectureLawModel sourceObject}
variable
  {targetModel : AAT.GeneratedArchitectureLawModel targetObject}
variable {SemanticExpr : Type q} {SemanticObs : Type r}
variable {FieldState : Type s}
variable
  {archsigTransition :
    GeneratedArchSigAATCoreTransition sourceModel targetModel}
variable
  {report :
    ArchSigSFTReport
      FieldState
      (AAT.GeneratedCarrier sourceObject)
      (AAT.GeneratedCarrier sourceObject)
      AAT.GeneratedObservationCoordinate
      SemanticExpr
      SemanticObs}
variable
  {estimate :
    SoftwareFieldEstimate
      FieldState
      (AAT.GeneratedCarrier sourceObject)
      (AAT.GeneratedCarrier sourceObject)
      AAT.GeneratedObservationCoordinate
      SemanticExpr
      SemanticObs}
variable {forecast : SFTForecastStatus}

/-- FieldSig reads the generated ArchSig transition as SFT analysis input. -/
theorem fieldsig_reads_generated_archsig_transition_as_sft_analysis
    (analysis :
      GeneratedFieldSigAATCoreTransitionAnalysis
        archsigTransition report estimate forecast) :
    archsigTransition.fieldSigAnalysisBoundary :=
  analysis.readsGeneratedArchSigTransitionAsSFTAnalysisEvidence

/-- FieldSig analysis over a generated transition does not define AAT. -/
theorem fieldsig_does_not_define_aat
    (analysis :
      GeneratedFieldSigAATCoreTransitionAnalysis
        archsigTransition report estimate forecast) :
    archsigTransition.archsigDoesNotDefineAAT :=
  analysis.fieldSigDoesNotDefineAATEvidence

/-- FieldSig analysis over a generated transition does not create atom existence. -/
theorem transition_does_not_create_atoms
    (analysis :
      GeneratedFieldSigAATCoreTransitionAnalysis
        archsigTransition report estimate forecast) :
    system.noToolOutputCreatesAtoms :=
  analysis.transitionDoesNotCreateAtoms

/-- Forecast correctness remains a forecast boundary. -/
theorem forecast_correctness_remains_boundary
    (analysis :
      GeneratedFieldSigAATCoreTransitionAnalysis
        archsigTransition report estimate forecast) :
    forecast.RecordsForecastBoundary :=
  analysis.forecastBoundary

/-- Theorem and non-conclusion boundaries remain visible. -/
theorem theorem_and_nonConclusions_remain_boundaries
    (analysis :
      GeneratedFieldSigAATCoreTransitionAnalysis
        archsigTransition report estimate forecast) :
    forecast.RecordsTheoremBoundary ∧ forecast.RecordsNonConclusions :=
  ⟨analysis.theoremBoundary, analysis.nonConclusions⟩

end GeneratedFieldSigAATCoreTransitionAnalysis

/--
Generated ArchSig-side transport transition between two Atom-generated AAT
cores.

This variant consumes `AATCoreTransportTransition`, so generated operations can
move a selected source molecule/law to a selected target molecule/law instead
of being coerced into preservation of the same molecule and law.
-/
structure GeneratedArchSigAATCoreTransportTransition
    {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    {sourceObject targetObject :
      AAT.GeneratedArchitectureObject presentation}
    (sourceModel : AAT.GeneratedArchitectureLawModel sourceObject)
    (targetModel : AAT.GeneratedArchitectureLawModel targetObject) where
  transportTransition :
    AATCoreTransportTransition
      sourceModel.generatedAATCore targetModel.generatedAATCore
  analyzesUsingAAT : Prop
  analyzesUsingAATEvidence : analyzesUsingAAT
  transitionBoundary : Prop
  transitionBoundaryEvidence : transitionBoundary
  archsigDoesNotDefineAAT : Prop
  archsigDoesNotDefineAATEvidence : archsigDoesNotDefineAAT
  fieldSigAnalysisBoundary : Prop
  fieldSigAnalysisBoundaryEvidence : fieldSigAnalysisBoundary
  unknownRejectedUnmeasuredSeparated : Prop
  unknownRejectedUnmeasuredSeparatedEvidence :
    unknownRejectedUnmeasuredSeparated
  measuredZeroBoundary : Prop
  validationIsNotTheoremDischarge : Prop
  nonConclusions : Prop

namespace GeneratedArchSigAATCoreTransportTransition

variable {system : AtomAxiomSystem.{u, v}}
variable {presentation : AtomShapePresentation system}
variable
  {sourceObject targetObject :
    AAT.GeneratedArchitectureObject presentation}
variable
  {sourceModel : AAT.GeneratedArchitectureLawModel sourceObject}
variable
  {targetModel : AAT.GeneratedArchitectureLawModel targetObject}

/-- Generated transport transitions analyze the generated source and target AAT cores. -/
def generatedAnalyzesUsingAAT
    (_transition :
      AATCoreTransportTransition
        sourceModel.generatedAATCore targetModel.generatedAATCore) :
    Prop :=
  sourceModel.generatedAATCore.laws sourceModel.generatedDesignLaw ∧
    targetModel.generatedAATCore.laws targetModel.generatedDesignLaw

/-- The generated source and target laws are selected in transport handoff cores. -/
theorem generatedAnalyzesUsingAAT_recorded
    (transition :
      AATCoreTransportTransition
        sourceModel.generatedAATCore targetModel.generatedAATCore) :
    generatedAnalyzesUsingAAT transition :=
  ⟨sourceModel.generated_law_on_core,
    targetModel.generated_law_on_core⟩

/-- Generated transport handoff does not define AAT or create atoms. -/
def generatedArchSigDoesNotDefineAAT
    (_transition :
      AATCoreTransportTransition
        sourceModel.generatedAATCore targetModel.generatedAATCore) :
    Prop :=
  sourceModel.generatedAATCore.noObservationDependency ∧
    targetModel.generatedAATCore.noObservationDependency ∧
      system.noToolOutputCreatesAtoms

/-- Generated transport non-definition is recorded by generated core and root facts. -/
theorem generatedArchSigDoesNotDefineAAT_recorded
    (transition :
      AATCoreTransportTransition
        sourceModel.generatedAATCore targetModel.generatedAATCore) :
    generatedArchSigDoesNotDefineAAT transition :=
  ⟨sourceModel.generatedAATCoreNoObservationDependency_recorded,
    targetModel.generatedAATCoreNoObservationDependency_recorded,
    transition.operation_does_not_create_atoms⟩

/-- Generated transport boundaries are rooted in transport atom non-creation. -/
def generatedTransitionBoundary
    (_transition :
      AATCoreTransportTransition
        sourceModel.generatedAATCore targetModel.generatedAATCore) :
    Prop :=
  system.noToolOutputCreatesAtoms

/-- The generated transport boundary is recorded by the transport package. -/
theorem generatedTransitionBoundary_recorded
    (transition :
      AATCoreTransportTransition
        sourceModel.generatedAATCore targetModel.generatedAATCore) :
    generatedTransitionBoundary transition :=
  transition.operation_does_not_create_atoms

/-- FieldSig analysis over generated transport remains a generated handoff boundary. -/
def generatedFieldSigAnalysisBoundary
    (_transition :
      AATCoreTransportTransition
        sourceModel.generatedAATCore targetModel.generatedAATCore) :
    Prop :=
  system.noToolOutputCreatesAtoms

/-- The generated transport FieldSig boundary is recorded by transport non-creation. -/
theorem generatedFieldSigAnalysisBoundary_recorded
    (transition :
      AATCoreTransportTransition
        sourceModel.generatedAATCore targetModel.generatedAATCore) :
    generatedFieldSigAnalysisBoundary transition :=
  transition.operation_does_not_create_atoms

/-- Unknown / rejected / unmeasured transport readings stay circuit-boundary separated. -/
def generatedUnknownRejectedUnmeasuredSeparated
    (_transition :
      AATCoreTransportTransition
        sourceModel.generatedAATCore targetModel.generatedAATCore) :
    Prop :=
  sourceModel.generatedAATCore.circuitBoundary ∧
    targetModel.generatedAATCore.circuitBoundary

/-- Generated source/target circuit boundaries record transport separation. -/
theorem generatedUnknownRejectedUnmeasuredSeparated_recorded
    (transition :
      AATCoreTransportTransition
        sourceModel.generatedAATCore targetModel.generatedAATCore) :
    generatedUnknownRejectedUnmeasuredSeparated transition :=
  ⟨sourceModel.generatedAATCoreCircuitBoundary_recorded,
    targetModel.generatedAATCoreCircuitBoundary_recorded⟩

/-- Generated transport measured-zero boundary is source/target lawfulness. -/
def generatedMeasuredZeroBoundary
    (_transition :
      AATCoreTransportTransition
        sourceModel.generatedAATCore targetModel.generatedAATCore) :
    Prop :=
  ArchitectureSignature.ArchitectureLawful sourceModel.toArchitectureLawModel ∧
    ArchitectureSignature.ArchitectureLawful targetModel.toArchitectureLawModel

/-- Source and target generated lawfulness record the transport measured-zero boundary. -/
theorem generatedMeasuredZeroBoundary_recorded
    (transition :
      AATCoreTransportTransition
        sourceModel.generatedAATCore targetModel.generatedAATCore) :
    generatedMeasuredZeroBoundary transition :=
  ⟨sourceModel.generatedArchitectureLawful,
    targetModel.generatedArchitectureLawful⟩

/-- Transport validation does not discharge theorem status by creating atoms. -/
def generatedValidationIsNotTheoremDischarge
    (_transition :
      AATCoreTransportTransition
        sourceModel.generatedAATCore targetModel.generatedAATCore) :
    Prop :=
  system.noToolOutputCreatesAtoms

/-- Generated transport validation boundary is recorded by transport non-creation. -/
theorem generatedValidationIsNotTheoremDischarge_recorded
    (transition :
      AATCoreTransportTransition
        sourceModel.generatedAATCore targetModel.generatedAATCore) :
    generatedValidationIsNotTheoremDischarge transition :=
  transition.operation_does_not_create_atoms

/-- Generated transport non-conclusions remain attached to source and target cores. -/
def generatedNonConclusions
    (_transition :
      AATCoreTransportTransition
        sourceModel.generatedAATCore targetModel.generatedAATCore) :
    Prop :=
  sourceModel.generatedAATCore.nonConclusions ∧
    targetModel.generatedAATCore.nonConclusions

/-- Construct a generated ArchSig transport transition without caller-supplied bridge fields. -/
def ofTransportTransition
    (transportTransition :
      AATCoreTransportTransition
        sourceModel.generatedAATCore targetModel.generatedAATCore) :
    GeneratedArchSigAATCoreTransportTransition sourceModel targetModel where
  transportTransition := transportTransition
  analyzesUsingAAT :=
    generatedAnalyzesUsingAAT transportTransition
  analyzesUsingAATEvidence :=
    generatedAnalyzesUsingAAT_recorded transportTransition
  transitionBoundary :=
    generatedTransitionBoundary transportTransition
  transitionBoundaryEvidence :=
    generatedTransitionBoundary_recorded transportTransition
  archsigDoesNotDefineAAT :=
    generatedArchSigDoesNotDefineAAT transportTransition
  archsigDoesNotDefineAATEvidence :=
    generatedArchSigDoesNotDefineAAT_recorded transportTransition
  fieldSigAnalysisBoundary :=
    generatedFieldSigAnalysisBoundary transportTransition
  fieldSigAnalysisBoundaryEvidence :=
    generatedFieldSigAnalysisBoundary_recorded transportTransition
  unknownRejectedUnmeasuredSeparated :=
    generatedUnknownRejectedUnmeasuredSeparated transportTransition
  unknownRejectedUnmeasuredSeparatedEvidence :=
    generatedUnknownRejectedUnmeasuredSeparated_recorded transportTransition
  measuredZeroBoundary :=
    generatedMeasuredZeroBoundary transportTransition
  validationIsNotTheoremDischarge :=
    generatedValidationIsNotTheoremDischarge transportTransition
  nonConclusions := generatedNonConclusions transportTransition

/-- Source-side Signature bridge generated from the source law model. -/
noncomputable def sourceBridge
    (archsigTransition :
      GeneratedArchSigAATCoreTransportTransition sourceModel targetModel) :
    ArchitectureSignature.AATCoreSignatureLawfulnessBridge
      sourceModel.generatedAATCore sourceModel.toArchitectureLawModel :=
  ArchitectureSignature.AATCoreSignatureLawfulnessBridge.ofGeneratedLawModel
    sourceModel
    archsigTransition.analyzesUsingAAT
    archsigTransition.archsigDoesNotDefineAAT
    archsigTransition.unknownRejectedUnmeasuredSeparated
    archsigTransition.measuredZeroBoundary
    archsigTransition.validationIsNotTheoremDischarge
    archsigTransition.nonConclusions
    archsigTransition.analyzesUsingAATEvidence
    archsigTransition.archsigDoesNotDefineAATEvidence
    archsigTransition.unknownRejectedUnmeasuredSeparatedEvidence

/-- Target-side Signature bridge generated from the target law model. -/
noncomputable def targetBridge
    (archsigTransition :
      GeneratedArchSigAATCoreTransportTransition sourceModel targetModel) :
    ArchitectureSignature.AATCoreSignatureLawfulnessBridge
      targetModel.generatedAATCore targetModel.toArchitectureLawModel :=
  ArchitectureSignature.AATCoreSignatureLawfulnessBridge.ofGeneratedLawModel
    targetModel
    archsigTransition.analyzesUsingAAT
    archsigTransition.archsigDoesNotDefineAAT
    archsigTransition.unknownRejectedUnmeasuredSeparated
    archsigTransition.measuredZeroBoundary
    archsigTransition.validationIsNotTheoremDischarge
    archsigTransition.nonConclusions
    archsigTransition.analyzesUsingAATEvidence
    archsigTransition.archsigDoesNotDefineAATEvidence
    archsigTransition.unknownRejectedUnmeasuredSeparatedEvidence

/-- The generated transport transition records its selected boundary. -/
theorem records_transition_boundary
    (archsigTransition :
      GeneratedArchSigAATCoreTransportTransition sourceModel targetModel) :
    archsigTransition.transitionBoundary :=
  archsigTransition.transitionBoundaryEvidence

/-- Generated ArchSig transport transition analysis does not define AAT. -/
theorem archsig_transition_does_not_define_aat
    (archsigTransition :
      GeneratedArchSigAATCoreTransportTransition sourceModel targetModel) :
    archsigTransition.archsigDoesNotDefineAAT :=
  archsigTransition.archsigDoesNotDefineAATEvidence

/-- The generated transport transition remains an analysis boundary for FieldSig. -/
theorem records_fieldsig_analysis_boundary
    (archsigTransition :
      GeneratedArchSigAATCoreTransportTransition sourceModel targetModel) :
    archsigTransition.fieldSigAnalysisBoundary :=
  archsigTransition.fieldSigAnalysisBoundaryEvidence

/-- The underlying generated transport transition does not create atom existence. -/
theorem transition_does_not_create_atoms
    (archsigTransition :
      GeneratedArchSigAATCoreTransportTransition sourceModel targetModel) :
    system.noToolOutputCreatesAtoms :=
  archsigTransition.transportTransition.operation_does_not_create_atoms

/-- The generated source bridge derives Signature lawfulness from the source model. -/
theorem source_bridge_architectureLawful
    (archsigTransition :
      GeneratedArchSigAATCoreTransportTransition sourceModel targetModel) :
    ArchitectureSignature.ArchitectureLawful
      sourceModel.toArchitectureLawModel := by
  exact
    ArchitectureSignature.AATCoreSignatureLawfulnessBridge.architectureLawful
      archsigTransition.sourceBridge

/-- The generated target bridge derives Signature lawfulness from the target model. -/
theorem target_bridge_architectureLawful
    (archsigTransition :
      GeneratedArchSigAATCoreTransportTransition sourceModel targetModel) :
    ArchitectureSignature.ArchitectureLawful
      targetModel.toArchitectureLawModel := by
  exact
    ArchitectureSignature.AATCoreSignatureLawfulnessBridge.architectureLawful
      archsigTransition.targetBridge

end GeneratedArchSigAATCoreTransportTransition

/--
FieldSig analysis boundary over a generated ArchSig-observed transport
transition.

The analysis consumes a generated transport transition and keeps report,
theorem, forecast, and non-conclusion boundaries visible.
-/
structure GeneratedFieldSigAATCoreTransportTransitionAnalysis
    {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    {sourceObject targetObject :
      AAT.GeneratedArchitectureObject presentation}
    {sourceModel : AAT.GeneratedArchitectureLawModel sourceObject}
    {targetModel : AAT.GeneratedArchitectureLawModel targetObject}
    {SemanticExpr : Type q} {SemanticObs : Type r}
    {FieldState : Type s}
    (archsigTransition :
      GeneratedArchSigAATCoreTransportTransition sourceModel targetModel)
    (report :
      ArchSigSFTReport
        FieldState
        (AAT.GeneratedCarrier sourceObject)
        (AAT.GeneratedCarrier sourceObject)
        AAT.GeneratedObservationCoordinate
        SemanticExpr
        SemanticObs)
    (estimate :
      SoftwareFieldEstimate
        FieldState
        (AAT.GeneratedCarrier sourceObject)
        (AAT.GeneratedCarrier sourceObject)
        AAT.GeneratedObservationCoordinate
        SemanticExpr
        SemanticObs)
    (forecast : SFTForecastStatus) :
    Prop where
  reportBoundary : ArchSigSFTReportEstimateBoundary report estimate forecast
  readsGeneratedArchSigTransitionAsSFTAnalysisEvidence :
    archsigTransition.fieldSigAnalysisBoundary
  fieldSigDoesNotDefineAATEvidence :
    archsigTransition.archsigDoesNotDefineAAT
  transitionDoesNotCreateAtoms : system.noToolOutputCreatesAtoms
  forecastBoundary : forecast.RecordsForecastBoundary
  theoremBoundary : forecast.RecordsTheoremBoundary
  nonConclusions : forecast.RecordsNonConclusions

namespace GeneratedFieldSigAATCoreTransportTransitionAnalysis

variable {system : AtomAxiomSystem.{u, v}}
variable {presentation : AtomShapePresentation system}
variable
  {sourceObject targetObject :
    AAT.GeneratedArchitectureObject presentation}
variable
  {sourceModel : AAT.GeneratedArchitectureLawModel sourceObject}
variable
  {targetModel : AAT.GeneratedArchitectureLawModel targetObject}
variable {SemanticExpr : Type q} {SemanticObs : Type r}
variable {FieldState : Type s}
variable
  {archsigTransition :
    GeneratedArchSigAATCoreTransportTransition sourceModel targetModel}
variable
  {report :
    ArchSigSFTReport
      FieldState
      (AAT.GeneratedCarrier sourceObject)
      (AAT.GeneratedCarrier sourceObject)
      AAT.GeneratedObservationCoordinate
      SemanticExpr
      SemanticObs}
variable
  {estimate :
    SoftwareFieldEstimate
      FieldState
      (AAT.GeneratedCarrier sourceObject)
      (AAT.GeneratedCarrier sourceObject)
      AAT.GeneratedObservationCoordinate
      SemanticExpr
      SemanticObs}
variable {forecast : SFTForecastStatus}

/-- FieldSig reads the generated transport transition as SFT analysis input. -/
theorem fieldsig_reads_generated_archsig_transport_transition_as_sft_analysis
    (analysis :
      GeneratedFieldSigAATCoreTransportTransitionAnalysis
        archsigTransition report estimate forecast) :
    archsigTransition.fieldSigAnalysisBoundary :=
  analysis.readsGeneratedArchSigTransitionAsSFTAnalysisEvidence

/-- FieldSig analysis over a generated transport transition does not define AAT. -/
theorem fieldsig_does_not_define_aat
    (analysis :
      GeneratedFieldSigAATCoreTransportTransitionAnalysis
        archsigTransition report estimate forecast) :
    archsigTransition.archsigDoesNotDefineAAT :=
  analysis.fieldSigDoesNotDefineAATEvidence

/-- FieldSig analysis over a generated transport transition does not create atom existence. -/
theorem transition_does_not_create_atoms
    (analysis :
      GeneratedFieldSigAATCoreTransportTransitionAnalysis
        archsigTransition report estimate forecast) :
    system.noToolOutputCreatesAtoms :=
  analysis.transitionDoesNotCreateAtoms

/-- Forecast correctness remains a forecast boundary. -/
theorem forecast_correctness_remains_boundary
    (analysis :
      GeneratedFieldSigAATCoreTransportTransitionAnalysis
        archsigTransition report estimate forecast) :
    forecast.RecordsForecastBoundary :=
  analysis.forecastBoundary

/-- Theorem and non-conclusion boundaries remain visible. -/
theorem theorem_and_nonConclusions_remain_boundaries
    (analysis :
      GeneratedFieldSigAATCoreTransportTransitionAnalysis
        archsigTransition report estimate forecast) :
    forecast.RecordsTheoremBoundary ∧ forecast.RecordsNonConclusions :=
  ⟨analysis.theoremBoundary, analysis.nonConclusions⟩

end GeneratedFieldSigAATCoreTransportTransitionAnalysis

end Formal.Arch
