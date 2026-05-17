import Formal.Arch.Evolution.SFTForecastCone

namespace Formal.Arch

universe u v

/--
A selected SFT forecast record.

The record stores one checked `ForecastCone` witness together with explicit
forecast and non-conclusion boundaries. It is not a point prediction,
probability distribution, causal proof, calibration claim, or accuracy claim.
-/
structure ForecastRecord
    {Field : Type u} {Operation : Type v}
    (support : OperationSupport Field Operation)
    (relation : StepRelation Field Operation)
    (source : Field) (horizon : Nat) where
  target : Field
  path : FieldPath support relation source target
  coneMember : ForecastCone support relation source horizon target path
  forecastBoundary : Prop
  nonConclusions : Prop

namespace ForecastRecord

variable {Field : Type u} {Operation : Type v}
variable {support : OperationSupport Field Operation}
variable {relation : StepRelation Field Operation}
variable {source : Field} {horizon : Nat}

/-- Forecast membership exposes the finite horizon bound for the stored path. -/
theorem length_le_horizon
    (record : ForecastRecord support relation source horizon) :
    ArchitecturePath.length record.path <= horizon :=
  ForecastCone.length_le_horizon record.coneMember

/-- The forecast record keeps the selected forecast/model boundary explicit. -/
def RecordsForecastBoundary
    (record : ForecastRecord support relation source horizon) : Prop :=
  record.forecastBoundary

/-- The forecast record keeps forecast non-conclusions explicit. -/
def RecordsNonConclusions
    (record : ForecastRecord support relation source horizon) : Prop :=
  record.nonConclusions

end ForecastRecord

/--
Observed feedback for a selected SFT update.

These fields are proposition-valued so the core can record boundaries without
choosing a metric, schema, PR artifact, CI report, or runtime adapter.
-/
structure ObservedOutcome (Field : Type u) where
  observedField : Field
  forecastError : Prop
  missingEvidence : Prop
  unexpectedWitness : Prop
  policyDrift : Prop
  observationBoundary : Prop
  nonConclusions : Prop

namespace ObservedOutcome

variable {Field : Type u}

/-- The observed outcome records its selected observation boundary. -/
def RecordsObservationBoundary (observed : ObservedOutcome Field) : Prop :=
  observed.observationBoundary

/-- The observed outcome records its non-conclusion boundary. -/
def RecordsNonConclusions (observed : ObservedOutcome Field) : Prop :=
  observed.nonConclusions

end ObservedOutcome

/--
Posterior field record after a selected update.

The posterior stores the evidence classes that the update is allowed to carry
forward. Its calibration boundary is explicit: the record does not say that a
later forecast is more accurate.
-/
structure PosteriorFieldRecord (Field : Type u) where
  posteriorField : Field
  forecastError : Prop
  missingEvidence : Prop
  unexpectedWitness : Prop
  policyDrift : Prop
  updateBoundary : Prop
  calibrationBoundary : Prop
  nonConclusions : Prop

namespace PosteriorFieldRecord

variable {Field : Type u}

/-- The posterior record exposes the selected update boundary. -/
def RecordsUpdateBoundary (posterior : PosteriorFieldRecord Field) : Prop :=
  posterior.updateBoundary

/--
The posterior record exposes the calibration boundary: preserved feedback is
not an accuracy-improvement theorem.
-/
def RecordsCalibrationBoundary (posterior : PosteriorFieldRecord Field) : Prop :=
  posterior.calibrationBoundary

/-- The posterior record stores its non-conclusion boundary. -/
def RecordsNonConclusions (posterior : PosteriorFieldRecord Field) : Prop :=
  posterior.nonConclusions

end PosteriorFieldRecord

/--
A selected closed-loop SFT field update.

The update links a prior forecast record, an observed outcome, and a posterior
record. It carries update-level boundaries but does not itself claim forecast
correctness, calibration, governance effectiveness, or extractor completeness.
-/
structure FieldUpdate
    {Field : Type u} {Operation : Type v}
    (support : OperationSupport Field Operation)
    (relation : StepRelation Field Operation)
    (source : Field) (horizon : Nat) where
  forecast : ForecastRecord support relation source horizon
  observed : ObservedOutcome Field
  posterior : PosteriorFieldRecord Field
  updateBoundary : Prop
  nonConclusions : Prop

namespace FieldUpdate

variable {Field : Type u} {Operation : Type v}
variable {support : OperationSupport Field Operation}
variable {relation : StepRelation Field Operation}
variable {source : Field} {horizon : Nat}

/-- The update-level boundary is explicit and caller supplied. -/
def RecordsUpdateBoundary
    (update : FieldUpdate support relation source horizon) : Prop :=
  update.updateBoundary

/-- FieldUpdate non-conclusions combine forecast, observation, posterior, and update boundaries. -/
def RecordsNonConclusions
    (update : FieldUpdate support relation source horizon) : Prop :=
  update.nonConclusions ∧
    update.forecast.RecordsNonConclusions ∧
    update.observed.RecordsNonConclusions ∧
    update.posterior.RecordsNonConclusions

/--
Soundness predicate for a selected update rule.

The predicate only says that selected observed feedback classes are recorded in
the posterior record and that the update/calibration/non-conclusion boundaries
are present. It does not assert that the posterior improves future forecasts.
-/
structure UpdateSound
    (update : FieldUpdate support relation source horizon) : Prop where
  preservesForecastError :
    update.observed.forecastError -> update.posterior.forecastError
  preservesMissingEvidence :
    update.observed.missingEvidence -> update.posterior.missingEvidence
  preservesUnexpectedWitness :
    update.observed.unexpectedWitness -> update.posterior.unexpectedWitness
  preservesPolicyDrift :
    update.observed.policyDrift -> update.posterior.policyDrift
  preservesNonConclusions :
    update.observed.RecordsNonConclusions ->
      update.posterior.RecordsNonConclusions
  recordsUpdateBoundary : update.RecordsUpdateBoundary
  recordsPosteriorUpdateBoundary : update.posterior.RecordsUpdateBoundary
  recordsCalibrationBoundary : update.posterior.RecordsCalibrationBoundary
  recordsNonConclusions : update.RecordsNonConclusions

namespace UpdateSound

variable {update : FieldUpdate support relation source horizon}

/--
The selected sound update rule preserves forecast error and missing evidence
records in the posterior field.
-/
theorem fieldUpdate_preserves_forecastError_and_missingEvidence
    (hSound : UpdateSound update) :
    (update.observed.forecastError -> update.posterior.forecastError) ∧
      (update.observed.missingEvidence -> update.posterior.missingEvidence) :=
  ⟨hSound.preservesForecastError, hSound.preservesMissingEvidence⟩

/--
The same update rule preserves unexpected witnesses and policy drift records.
-/
theorem fieldUpdate_preserves_unexpectedWitness_and_policyDrift
    (hSound : UpdateSound update) :
    (update.observed.unexpectedWitness -> update.posterior.unexpectedWitness) ∧
      (update.observed.policyDrift -> update.posterior.policyDrift) :=
  ⟨hSound.preservesUnexpectedWitness, hSound.preservesPolicyDrift⟩

/--
The update rule preserves the observed non-conclusion boundary in the posterior
record.
-/
theorem fieldUpdate_preserves_nonConclusions
    (hSound : UpdateSound update) :
    update.observed.RecordsNonConclusions ->
      update.posterior.RecordsNonConclusions :=
  hSound.preservesNonConclusions

/--
The update theorem exposes the calibration boundary instead of turning feedback
preservation into an accuracy-improvement claim.
-/
theorem fieldUpdate_records_calibrationBoundary
    (hSound : UpdateSound update) :
    update.posterior.RecordsCalibrationBoundary :=
  hSound.recordsCalibrationBoundary

/--
The update package records all non-conclusion boundaries needed by downstream
SFT theorem packages.
-/
theorem fieldUpdate_records_nonConclusions
    (hSound : UpdateSound update) :
    update.RecordsNonConclusions :=
  hSound.recordsNonConclusions

end UpdateSound

end FieldUpdate

end Formal.Arch
