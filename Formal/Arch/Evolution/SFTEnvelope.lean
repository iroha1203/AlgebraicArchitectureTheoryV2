import Formal.Arch.Evolution.SFTFieldUpdate

namespace Formal.Arch

universe u v

/--
A selected family of SFT forecast records.

The family is a nonempty list of checked forecast records for one selected
support/relation/source/horizon slice. It is intentionally not an inverse image
of an envelope report: downstream projections may forget path counts,
unobserved coordinates, weights, and support completeness.
-/
structure ConeFamily
    {Field : Type u} {Operation : Type v}
    (support : OperationSupport Field Operation)
    (relation : StepRelation Field Operation)
    (source : Field) (horizon : Nat) where
  records : List (ForecastRecord support relation source horizon)
  nonempty : records ≠ []
  familyBoundary : Prop
  unknownRemainder : Prop
  nonConclusions : Prop

namespace ConeFamily

variable {Field : Type u} {Operation : Type v}
variable {support : OperationSupport Field Operation}
variable {relation : StepRelation Field Operation}
variable {source : Field} {horizon : Nat}

/-- Every forecast record in a selected list keeps its non-conclusion boundary. -/
def RecordsForecastListNonConclusions :
    List (ForecastRecord support relation source horizon) -> Prop
  | [] => True
  | record :: rest =>
      record.RecordsNonConclusions ∧ RecordsForecastListNonConclusions rest

/-- The selected cone family records that it is not empty. -/
def RecordsNonempty
    (family : ConeFamily support relation source horizon) : Prop :=
  family.records ≠ []

/-- Every stored forecast record keeps its own non-conclusion boundary. -/
def RecordsForecastNonConclusions
    (family : ConeFamily support relation source horizon) : Prop :=
  RecordsForecastListNonConclusions family.records

/-- The selected cone-family modeling boundary remains explicit. -/
def RecordsFamilyBoundary
    (family : ConeFamily support relation source horizon) : Prop :=
  family.familyBoundary

/-- Unknown or unmodeled remainder is preserved as a first-class boundary item. -/
def RecordsUnknownRemainder
    (family : ConeFamily support relation source horizon) : Prop :=
  family.unknownRemainder

/-- Cone-family non-conclusions combine family and per-forecast boundaries. -/
def RecordsNonConclusions
    (family : ConeFamily support relation source horizon) : Prop :=
  family.nonConclusions ∧ family.RecordsForecastNonConclusions

/-- The nonempty witness stored by the family is available as an accessor. -/
theorem records_nonempty
    (family : ConeFamily support relation source horizon) :
    family.RecordsNonempty :=
  family.nonempty

end ConeFamily

/--
Observation boundary used by an SFT envelope projection.

All fields are proposition-valued so the Lean core can track preservation of
boundaries without choosing a concrete metric schema, tooling report format, or
review UI.
-/
structure ObservationBoundary (Field : Type u) where
  pathClassesVisible : Prop
  affectedRegionsVisible : Prop
  comparableAxes : Prop
  observedProjectionBoundary : Prop
  missingBoundary : Prop
  theoremBoundary : Prop
  unknownRemainder : Prop
  nonConclusions : Prop

namespace ObservationBoundary

variable {Field : Type u}

/-- The boundary records which path classes are visible to the projection. -/
def RecordsPathClassesVisible (boundary : ObservationBoundary Field) : Prop :=
  boundary.pathClassesVisible

/-- The boundary records which affected regions are visible to the projection. -/
def RecordsAffectedRegionsVisible (boundary : ObservationBoundary Field) : Prop :=
  boundary.affectedRegionsVisible

/-- The boundary records which axes are comparable in the selected measurement universe. -/
def RecordsComparableAxes (boundary : ObservationBoundary Field) : Prop :=
  boundary.comparableAxes

/-- Missing boundary items remain explicit. -/
def RecordsMissingBoundary (boundary : ObservationBoundary Field) : Prop :=
  boundary.missingBoundary

/-- The theorem/modeling boundary remains explicit. -/
def RecordsTheoremBoundary (boundary : ObservationBoundary Field) : Prop :=
  boundary.theoremBoundary

/-- Unknown or unmodeled remainder remains explicit. -/
def RecordsUnknownRemainder (boundary : ObservationBoundary Field) : Prop :=
  boundary.unknownRemainder

/-- Observation-boundary non-conclusions remain explicit. -/
def RecordsNonConclusions (boundary : ObservationBoundary Field) : Prop :=
  boundary.nonConclusions

end ObservationBoundary

/--
Reviewer-facing SFT consequence envelope.

This is a loss-aware report projection target, not a `ForecastCone` witness and
not a causal, probabilistic, calibrated, or uniquely invertible forecast claim.
-/
structure ConsequenceEnvelope
    {Field : Type u} {Operation : Type v}
    (support : OperationSupport Field Operation)
    (relation : StepRelation Field Operation)
    (source : Field) (horizon : Nat) where
  selectedConeCount : Nat
  pathClasses : Prop
  affectedRegions : Prop
  comparableAxes : Prop
  axisDeltaRanges : Prop
  obstructionCandidates : Prop
  missingBoundaryItems : Prop
  theoremBoundaryItems : Prop
  unknownRemainder : Prop
  forecastBoundary : Prop
  nonConclusions : Prop
  projectionBoundary : Prop

namespace ConsequenceEnvelope

variable {Field : Type u} {Operation : Type v}
variable {support : OperationSupport Field Operation}
variable {relation : StepRelation Field Operation}
variable {source : Field} {horizon : Nat}

/-- The envelope records selected path classes visible through the boundary. -/
def RecordsPathClasses
    (envelope : ConsequenceEnvelope support relation source horizon) : Prop :=
  envelope.pathClasses

/-- The envelope records affected region evidence visible through the boundary. -/
def RecordsAffectedRegions
    (envelope : ConsequenceEnvelope support relation source horizon) : Prop :=
  envelope.affectedRegions

/-- The envelope records comparable axes under the selected measurement boundary. -/
def RecordsComparableAxes
    (envelope : ConsequenceEnvelope support relation source horizon) : Prop :=
  envelope.comparableAxes

/-- The envelope records missing boundary items rather than discharging them. -/
def RecordsMissingBoundary
    (envelope : ConsequenceEnvelope support relation source horizon) : Prop :=
  envelope.missingBoundaryItems

/-- The envelope records theorem/modeling boundary items. -/
def RecordsTheoremBoundary
    (envelope : ConsequenceEnvelope support relation source horizon) : Prop :=
  envelope.theoremBoundaryItems

/-- The envelope keeps unknown or unmodeled remainder as a report component. -/
def RecordsUnknownRemainder
    (envelope : ConsequenceEnvelope support relation source horizon) : Prop :=
  envelope.unknownRemainder

/-- The envelope keeps forecast/model boundaries explicit. -/
def RecordsForecastBoundary
    (envelope : ConsequenceEnvelope support relation source horizon) : Prop :=
  envelope.forecastBoundary

/-- The envelope keeps the report projection boundary explicit. -/
def RecordsProjectionBoundary
    (envelope : ConsequenceEnvelope support relation source horizon) : Prop :=
  envelope.projectionBoundary

/-- Envelope-level non-conclusions remain explicit. -/
def RecordsNonConclusions
    (envelope : ConsequenceEnvelope support relation source horizon) : Prop :=
  envelope.nonConclusions

end ConsequenceEnvelope

/--
Loss-aware projection from a selected cone family through an observation
boundary into a reviewer-facing envelope.

The relation stores preservation obligations for report boundaries. It does not
state that the envelope can reconstruct the selected cone family.
-/
structure EnvelopeProjection
    {Field : Type u} {Operation : Type v}
    {support : OperationSupport Field Operation}
    {relation : StepRelation Field Operation}
    {source : Field} {horizon : Nat}
    (family : ConeFamily support relation source horizon)
    (boundary : ObservationBoundary Field)
    (envelope : ConsequenceEnvelope support relation source horizon) :
    Prop where
  recordsSelectedConeCount :
    envelope.selectedConeCount = family.records.length
  preservesPathClasses :
    boundary.RecordsPathClassesVisible -> envelope.RecordsPathClasses
  preservesAffectedRegions :
    boundary.RecordsAffectedRegionsVisible -> envelope.RecordsAffectedRegions
  preservesComparableAxes :
    boundary.RecordsComparableAxes -> envelope.RecordsComparableAxes
  preservesMissingBoundary :
    boundary.RecordsMissingBoundary -> envelope.RecordsMissingBoundary
  preservesTheoremBoundary :
    boundary.RecordsTheoremBoundary -> envelope.RecordsTheoremBoundary
  preservesFamilyUnknownRemainder :
    family.RecordsUnknownRemainder -> envelope.RecordsUnknownRemainder
  preservesBoundaryUnknownRemainder :
    boundary.RecordsUnknownRemainder -> envelope.RecordsUnknownRemainder
  preservesForecastNonConclusions :
    family.RecordsNonConclusions -> envelope.RecordsNonConclusions
  preservesBoundaryNonConclusions :
    boundary.RecordsNonConclusions -> envelope.RecordsNonConclusions
  recordsForecastBoundary : envelope.RecordsForecastBoundary
  recordsProjectionBoundary : envelope.RecordsProjectionBoundary
  recordsNonConclusions : envelope.RecordsNonConclusions

namespace EnvelopeProjection

variable {Field : Type u} {Operation : Type v}
variable {support : OperationSupport Field Operation}
variable {relation : StepRelation Field Operation}
variable {source : Field} {horizon : Nat}
variable {family : ConeFamily support relation source horizon}
variable {boundary : ObservationBoundary Field}
variable {envelope : ConsequenceEnvelope support relation source horizon}

/-- The projection records how many selected cones were projected. -/
theorem envelope_records_selectedConeCount
    (hProjection : EnvelopeProjection family boundary envelope) :
    envelope.selectedConeCount = family.records.length :=
  hProjection.recordsSelectedConeCount

/-- The projection preserves selected missing-boundary items. -/
theorem envelope_preserves_missingBoundary
    (hProjection : EnvelopeProjection family boundary envelope) :
    boundary.RecordsMissingBoundary -> envelope.RecordsMissingBoundary :=
  hProjection.preservesMissingBoundary

/-- The projection preserves selected theorem-boundary items. -/
theorem envelope_preserves_theoremBoundary
    (hProjection : EnvelopeProjection family boundary envelope) :
    boundary.RecordsTheoremBoundary -> envelope.RecordsTheoremBoundary :=
  hProjection.preservesTheoremBoundary

/-- Unknown remainder from the selected cone family remains visible in the envelope. -/
theorem envelope_preserves_unknownRemainder
    (hProjection : EnvelopeProjection family boundary envelope) :
    family.RecordsUnknownRemainder -> envelope.RecordsUnknownRemainder :=
  hProjection.preservesFamilyUnknownRemainder

/--
Forecast non-conclusions inherited from the selected cone family remain visible
in the envelope.
-/
theorem envelope_preserves_nonConclusions
    (hProjection : EnvelopeProjection family boundary envelope) :
    family.RecordsNonConclusions -> envelope.RecordsNonConclusions :=
  hProjection.preservesForecastNonConclusions

/--
The projection exposes the forecast and report boundaries instead of
strengthening the envelope into a point prediction, causal proof, calibrated
forecast, or unique cone-family reconstruction.
-/
theorem envelope_does_not_strengthen_forecast_claim
    (hProjection : EnvelopeProjection family boundary envelope) :
    envelope.RecordsForecastBoundary ∧ envelope.RecordsProjectionBoundary ∧
      envelope.RecordsNonConclusions :=
  ⟨hProjection.recordsForecastBoundary,
    hProjection.recordsProjectionBoundary,
    hProjection.recordsNonConclusions⟩

end EnvelopeProjection

end Formal.Arch
