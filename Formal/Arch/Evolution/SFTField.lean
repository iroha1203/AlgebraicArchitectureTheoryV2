import Formal.Arch.Extension.Flatness

namespace Formal.Arch

universe u v w q r s

/--
Selected computable SFT field state.

`SoftwareField` is a wrapper around a selected field carrier together with an
architecture projection and explicit modeling boundaries. The field itself is
not identified with the projected `ArchitectureObject`; downstream theorems
must go through the projection accessor.
-/
structure SoftwareField
    (FieldState : Type s) (C : Type u) (A : Type v)
    (StaticObs : Type w) (SemanticExpr : Type q)
    (SemanticObs : Type r) where
  state : FieldState
  architectureProjection :
    ArchitectureObject C A StaticObs SemanticExpr SemanticObs
  observedSignatureRecord : Prop
  historyBoundary : Prop
  operationSupportBoundary : Prop
  operationPolicyBoundary : Prop
  constraintEnvironmentBoundary : Prop
  observationModelBoundary : Prop
  governanceInterventionBoundary : Prop
  exogenousArtifactInputBoundary : Prop
  fieldBoundary : Prop
  nonConclusions : Prop

namespace SoftwareField

variable {FieldState : Type s} {C : Type u} {A : Type v}
variable {StaticObs : Type w} {SemanticExpr : Type q}
variable {SemanticObs : Type r}

/-- The AAT architecture object selected by this SFT field state. -/
def arch
    (field : SoftwareField FieldState C A StaticObs SemanticExpr SemanticObs) :
    ArchitectureObject C A StaticObs SemanticExpr SemanticObs :=
  field.architectureProjection

/-- The selected field state records observable signature evidence. -/
def RecordsObservedSignature
    (field : SoftwareField FieldState C A StaticObs SemanticExpr SemanticObs) :
    Prop :=
  field.observedSignatureRecord

/-- The selected field state records its history boundary. -/
def RecordsHistoryBoundary
    (field : SoftwareField FieldState C A StaticObs SemanticExpr SemanticObs) :
    Prop :=
  field.historyBoundary

/-- Operation support is retained as an explicit field boundary. -/
def RecordsOperationSupportBoundary
    (field : SoftwareField FieldState C A StaticObs SemanticExpr SemanticObs) :
    Prop :=
  field.operationSupportBoundary

/-- Operation policy is retained as an explicit field boundary. -/
def RecordsOperationPolicyBoundary
    (field : SoftwareField FieldState C A StaticObs SemanticExpr SemanticObs) :
    Prop :=
  field.operationPolicyBoundary

/-- Constraint environment assumptions remain explicit. -/
def RecordsConstraintEnvironmentBoundary
    (field : SoftwareField FieldState C A StaticObs SemanticExpr SemanticObs) :
    Prop :=
  field.constraintEnvironmentBoundary

/-- Observation-model assumptions remain explicit. -/
def RecordsObservationModelBoundary
    (field : SoftwareField FieldState C A StaticObs SemanticExpr SemanticObs) :
    Prop :=
  field.observationModelBoundary

/-- Governance intervention assumptions remain explicit. -/
def RecordsGovernanceInterventionBoundary
    (field : SoftwareField FieldState C A StaticObs SemanticExpr SemanticObs) :
    Prop :=
  field.governanceInterventionBoundary

/-- Exogenous artifact inputs remain explicit boundary data. -/
def RecordsExogenousArtifactInputBoundary
    (field : SoftwareField FieldState C A StaticObs SemanticExpr SemanticObs) :
    Prop :=
  field.exogenousArtifactInputBoundary

/--
Boundary accessor recording that callers should use `arch field` rather than
reading the whole `SoftwareField` as an `ArchitectureObject`.
-/
def RecordsFieldNotArchitectureObjectBoundary
    (field : SoftwareField FieldState C A StaticObs SemanticExpr SemanticObs) :
    Prop :=
  field.fieldBoundary

/-- SoftwareField-level non-conclusions remain explicit. -/
def RecordsNonConclusions
    (field : SoftwareField FieldState C A StaticObs SemanticExpr SemanticObs) :
    Prop :=
  field.nonConclusions

/-- The architecture projection accessor returns the stored projection. -/
theorem arch_eq_architectureProjection
    (field : SoftwareField FieldState C A StaticObs SemanticExpr SemanticObs) :
    field.arch = field.architectureProjection :=
  rfl

end SoftwareField

/--
Partial estimate of a selected software field.

The estimate packages one selected `SoftwareField` with coverage, observation,
and reconstruction boundaries. It does not claim complete reconstruction of a
larger development field or extractor completeness.
-/
structure SoftwareFieldEstimate
    (FieldState : Type s) (C : Type u) (A : Type v)
    (StaticObs : Type w) (SemanticExpr : Type q)
    (SemanticObs : Type r) where
  field : SoftwareField FieldState C A StaticObs SemanticExpr SemanticObs
  coverageAssumptions : Prop
  observationBoundary : Prop
  reconstructionBoundary : Prop
  estimatorBoundary : Prop
  missingEvidence : Prop
  nonConclusions : Prop

namespace SoftwareFieldEstimate

variable {FieldState : Type s} {C : Type u} {A : Type v}
variable {StaticObs : Type w} {SemanticExpr : Type q}
variable {SemanticObs : Type r}

/-- The selected field state carried by the estimate. -/
def selectedField
    (estimate :
      SoftwareFieldEstimate FieldState C A StaticObs SemanticExpr SemanticObs) :
    SoftwareField FieldState C A StaticObs SemanticExpr SemanticObs :=
  estimate.field

/-- The AAT architecture object projected from the selected estimated field. -/
def arch
    (estimate :
      SoftwareFieldEstimate FieldState C A StaticObs SemanticExpr SemanticObs) :
    ArchitectureObject C A StaticObs SemanticExpr SemanticObs :=
  estimate.field.arch

/-- Coverage assumptions are caller-supplied and remain explicit. -/
def RecordsCoverageAssumptions
    (estimate :
      SoftwareFieldEstimate FieldState C A StaticObs SemanticExpr SemanticObs) :
    Prop :=
  estimate.coverageAssumptions

/-- Observation boundaries are caller-supplied and remain explicit. -/
def RecordsObservationBoundary
    (estimate :
      SoftwareFieldEstimate FieldState C A StaticObs SemanticExpr SemanticObs) :
    Prop :=
  estimate.observationBoundary

/-- Reconstruction boundaries are caller-supplied and remain explicit. -/
def RecordsReconstructionBoundary
    (estimate :
      SoftwareFieldEstimate FieldState C A StaticObs SemanticExpr SemanticObs) :
    Prop :=
  estimate.reconstructionBoundary

/-- Estimator/model boundaries are caller-supplied and remain explicit. -/
def RecordsEstimatorBoundary
    (estimate :
      SoftwareFieldEstimate FieldState C A StaticObs SemanticExpr SemanticObs) :
    Prop :=
  estimate.estimatorBoundary

/-- Missing evidence remains a first-class estimate boundary. -/
def RecordsMissingEvidence
    (estimate :
      SoftwareFieldEstimate FieldState C A StaticObs SemanticExpr SemanticObs) :
    Prop :=
  estimate.missingEvidence

/-- Estimate-level non-conclusions remain explicit. -/
def RecordsNonConclusions
    (estimate :
      SoftwareFieldEstimate FieldState C A StaticObs SemanticExpr SemanticObs) :
    Prop :=
  estimate.nonConclusions ∧ estimate.field.RecordsNonConclusions

/-- The estimate projection is exactly the selected field projection. -/
theorem arch_eq_field_arch
    (estimate :
      SoftwareFieldEstimate FieldState C A StaticObs SemanticExpr SemanticObs) :
    estimate.arch = estimate.field.arch :=
  rfl

end SoftwareFieldEstimate

/--
Boundary package for reading an SFT field estimate through an AAT architecture
projection.

This record is a one-way boundary: it preserves selected coverage,
observation, reconstruction, missing-evidence, and non-conclusion obligations,
but it does not turn the whole field into an architecture object or prove
complete trace-grounded reconstruction.
-/
structure ArchitectureProjectionBoundary
    {FieldState : Type s} {C : Type u} {A : Type v}
    {StaticObs : Type w} {SemanticExpr : Type q}
    {SemanticObs : Type r}
    (estimate :
      SoftwareFieldEstimate FieldState C A StaticObs SemanticExpr SemanticObs)
    (arch : ArchitectureObject C A StaticObs SemanticExpr SemanticObs) :
    Prop where
  projectsToSelectedArchitecture : arch = estimate.arch
  preservesCoverageAssumptions :
    estimate.RecordsCoverageAssumptions
  preservesObservationBoundary :
    estimate.RecordsObservationBoundary
  preservesReconstructionBoundary :
    estimate.RecordsReconstructionBoundary
  preservesMissingEvidence :
    estimate.RecordsMissingEvidence
  recordsFieldBoundary :
    estimate.field.RecordsFieldNotArchitectureObjectBoundary
  recordsNonConclusions :
    estimate.RecordsNonConclusions

namespace ArchitectureProjectionBoundary

variable {FieldState : Type s} {C : Type u} {A : Type v}
variable {StaticObs : Type w} {SemanticExpr : Type q}
variable {SemanticObs : Type r}
variable
  {estimate :
    SoftwareFieldEstimate FieldState C A StaticObs SemanticExpr SemanticObs}
variable {arch : ArchitectureObject C A StaticObs SemanticExpr SemanticObs}

/-- The projection boundary identifies the selected AAT architecture object. -/
theorem projection_eq_selected_arch
    (hBoundary : ArchitectureProjectionBoundary estimate arch) :
    arch = estimate.arch :=
  hBoundary.projectsToSelectedArchitecture

/-- The projection boundary preserves estimate coverage assumptions. -/
theorem projection_preserves_coverageAssumptions
    (hBoundary : ArchitectureProjectionBoundary estimate arch) :
    estimate.RecordsCoverageAssumptions :=
  hBoundary.preservesCoverageAssumptions

/-- The projection boundary preserves estimate observation boundaries. -/
theorem projection_preserves_observationBoundary
    (hBoundary : ArchitectureProjectionBoundary estimate arch) :
    estimate.RecordsObservationBoundary :=
  hBoundary.preservesObservationBoundary

/-- The projection boundary preserves estimate reconstruction boundaries. -/
theorem projection_preserves_reconstructionBoundary
    (hBoundary : ArchitectureProjectionBoundary estimate arch) :
    estimate.RecordsReconstructionBoundary :=
  hBoundary.preservesReconstructionBoundary

/-- The projection boundary preserves missing evidence records. -/
theorem projection_preserves_missingEvidence
    (hBoundary : ArchitectureProjectionBoundary estimate arch) :
    estimate.RecordsMissingEvidence :=
  hBoundary.preservesMissingEvidence

/--
The projection theorem records the boundary that `SoftwareField` is read
through `arch`, not identified with the projected `ArchitectureObject`.
-/
theorem projection_records_fieldNotArchitectureObjectBoundary
    (hBoundary : ArchitectureProjectionBoundary estimate arch) :
    estimate.field.RecordsFieldNotArchitectureObjectBoundary :=
  hBoundary.recordsFieldBoundary

/-- Projection-boundary non-conclusions are preserved explicitly. -/
theorem projection_records_nonConclusions
    (hBoundary : ArchitectureProjectionBoundary estimate arch) :
    estimate.RecordsNonConclusions :=
  hBoundary.recordsNonConclusions

end ArchitectureProjectionBoundary

end Formal.Arch
