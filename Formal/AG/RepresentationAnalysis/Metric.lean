import Formal.AG.RepresentationAnalysis.SignatureCurvature

noncomputable section

namespace AAT.AG
namespace RepresentationAnalysis

universe u v w

/--
VII.定義9.1: enriched distance value used by metric readings.

`measuredZero` is a measured zero certificate.  `unmeasured` is a separate
boundary marker and is not a zero certificate.
-/
inductive DistanceValue (Payload : Type u) where
  | measured : Payload -> DistanceValue Payload
  | measuredZero : DistanceValue Payload
  | unmeasured : DistanceValue Payload
  | unavailable : DistanceValue Payload
  | incomparable : DistanceValue Payload
  | infinite : DistanceValue Payload
  deriving DecidableEq

namespace DistanceValue

variable {Payload : Type u}

/-- VII.定義9.1: a measured nonzero-or-valued payload is present. -/
def HasMeasuredPayload : DistanceValue Payload -> Prop
  | measured _ => True
  | _ => False

/-- VII.定義9.1: measured zero certificate. -/
def IsMeasuredZero (d : DistanceValue Payload) : Prop :=
  d = measuredZero

/-- VII.定義9.1: measured value or measured zero, excluding boundary markers. -/
def IsMeasured : DistanceValue Payload -> Prop
  | measured _ => True
  | measuredZero => True
  | _ => False

/-- VII.定義9.1: unmeasured boundary marker. -/
def IsUnmeasured (d : DistanceValue Payload) : Prop :=
  d = unmeasured

/-- VII.定義9.1: optional measured payload; boundary markers return `none`. -/
def measuredPayload? : DistanceValue Payload -> Option Payload
  | measured payload => some payload
  | measuredZero => none
  | unmeasured => none
  | unavailable => none
  | incomparable => none
  | infinite => none

/-- VII.定義9.1: `unmeasured` is definitionally distinct from `measuredZero`. -/
theorem unmeasured_ne_measuredZero :
    (unmeasured : DistanceValue Payload) ≠ measuredZero := by
  intro h
  cases h

/-- VII.定義9.1: measured zero is definitionally distinct from `unmeasured`. -/
theorem measuredZero_ne_unmeasured :
    (measuredZero : DistanceValue Payload) ≠ unmeasured := by
  intro h
  cases h

/-- VII.定義9.1: `unmeasured` is not a measured zero certificate. -/
theorem unmeasured_not_measuredZero :
    ¬ (unmeasured : DistanceValue Payload).IsMeasuredZero := by
  intro h
  exact unmeasured_ne_measuredZero h

/-- VII.定義9.1: an unmeasured boundary marker is not measured. -/
theorem unmeasured_not_measured :
    ¬ (unmeasured : DistanceValue Payload).IsMeasured := by
  intro h
  exact h

/-- VII.定義9.1: unavailable is not a measured zero certificate. -/
theorem unavailable_not_measuredZero :
    ¬ (unavailable : DistanceValue Payload).IsMeasuredZero := by
  intro h
  cases h

/-- VII.定義9.1: incomparable is not a measured zero certificate. -/
theorem incomparable_not_measuredZero :
    ¬ (incomparable : DistanceValue Payload).IsMeasuredZero := by
  intro h
  cases h

/-- VII.定義9.1: infinite is not a measured zero certificate. -/
theorem infinite_not_measuredZero :
    ¬ (infinite : DistanceValue Payload).IsMeasuredZero := by
  intro h
  cases h

/-- VII.定義9.1: an unmeasured value cannot also be measured zero. -/
theorem isUnmeasured_not_measuredZero {d : DistanceValue Payload}
    (h : d.IsUnmeasured) : ¬ d.IsMeasuredZero := by
  cases d <;> simp [IsUnmeasured, IsMeasuredZero] at h ⊢

/-- VII.定義9.1: an unmeasured value cannot also be measured. -/
theorem isUnmeasured_not_measured {d : DistanceValue Payload}
    (h : d.IsUnmeasured) : ¬ d.IsMeasured := by
  cases d <;> simp [IsUnmeasured, IsMeasured] at h ⊢

/-- VII.定義9.1: `unmeasured` has no measured payload. -/
theorem measuredPayload?_unmeasured :
    measuredPayload? (unmeasured : DistanceValue Payload) = none :=
  rfl

/-- VII.定義9.1: measured zero has no nonzero measured payload. -/
theorem measuredPayload?_measuredZero :
    measuredPayload? (measuredZero : DistanceValue Payload) = none :=
  rfl

/-- VII.定義9.1: measured payload values round-trip through `measuredPayload?`. -/
theorem measuredPayload?_measured (payload : Payload) :
    measuredPayload? (measured payload) = some payload :=
  rfl

end DistanceValue

/-- VII.定義9.1: explicit partial-order interface for enriched distance values. -/
structure DistanceValuePartialOrder (Payload : Type u) where
  le : DistanceValue Payload -> DistanceValue Payload -> Prop
  le_refl : ∀ value, le value value
  le_trans : ∀ {a b c}, le a b -> le b c -> le a c
  le_antisymm : ∀ {a b}, le a b -> le b a -> a = b

namespace DistanceValuePartialOrder

variable {Payload : Type u}

/-- VII.定義9.1: the discrete selected partial order is always available. -/
def discrete : DistanceValuePartialOrder Payload where
  le a b := a = b
  le_refl _value := rfl
  le_trans hab hbc := hab.trans hbc
  le_antisymm hab _hba := hab

end DistanceValuePartialOrder

/-- VII.原則9.2: aggregation profile separating measured and unmeasured axes. -/
structure DistanceAggregationProfile
    (Axis : Type u) (Payload : Type v) (Scalar : Type w) where
  valueAt : Axis -> DistanceValue Payload
  scalarAggregate : Scalar
  measuredSupport : Set Axis
  unmeasuredSupport : Set Axis
  measuredSupport_exact :
    ∀ axis, axis ∈ measuredSupport ↔ (valueAt axis).IsMeasured
  unmeasuredSupport_exact :
    ∀ axis, axis ∈ unmeasuredSupport ↔ (valueAt axis).IsUnmeasured
  scalarUsesMeasuredSupport : Prop
  scalarUsesMeasuredSupport_holds : scalarUsesMeasuredSupport
  unmeasuredSupportReportedSeparately : Prop
  unmeasuredSupportReportedSeparately_holds :
    unmeasuredSupportReportedSeparately

namespace DistanceAggregationProfile

variable {Axis : Type u} {Payload : Type v} {Scalar : Type w}

/-- VII.原則9.2: expose the selected measured-support discipline. -/
theorem scalarUsesMeasuredSupport_certificate
    (P : DistanceAggregationProfile Axis Payload Scalar) :
    P.scalarUsesMeasuredSupport :=
  P.scalarUsesMeasuredSupport_holds

/-- VII.原則9.2: expose that unmeasured support is reported separately. -/
theorem unmeasuredSupportReportedSeparately_certificate
    (P : DistanceAggregationProfile Axis Payload Scalar) :
    P.unmeasuredSupportReportedSeparately :=
  P.unmeasuredSupportReportedSeparately_holds

/-- VII.原則9.2: membership in unmeasured support reads as `DistanceValue.unmeasured`. -/
theorem valueAt_isUnmeasured_of_mem_unmeasuredSupport
    (P : DistanceAggregationProfile Axis Payload Scalar)
    {axis : Axis} (haxis : axis ∈ P.unmeasuredSupport) :
    (P.valueAt axis).IsUnmeasured :=
  (P.unmeasuredSupport_exact axis).mp haxis

/--
VII.原則9.2: aggregation does not collapse an unmeasured axis to measured zero.
-/
theorem unmeasuredSupport_not_measuredZero
    (P : DistanceAggregationProfile Axis Payload Scalar)
    {axis : Axis} (haxis : axis ∈ P.unmeasuredSupport) :
    ¬ (P.valueAt axis).IsMeasuredZero :=
  DistanceValue.isUnmeasured_not_measuredZero
    (P.valueAt_isUnmeasured_of_mem_unmeasuredSupport haxis)

/--
VII.原則9.2: an unmeasured support axis is not part of the measured support.
-/
theorem not_mem_measuredSupport_of_mem_unmeasuredSupport
    (P : DistanceAggregationProfile Axis Payload Scalar)
    {axis : Axis} (haxis : axis ∈ P.unmeasuredSupport) :
    axis ∉ P.measuredSupport := by
  intro hmeasured
  exact DistanceValue.isUnmeasured_not_measured
    (P.valueAt_isUnmeasured_of_mem_unmeasuredSupport haxis)
    ((P.measuredSupport_exact axis).mp hmeasured)

end DistanceAggregationProfile

/--
VII.原則9.2: scalar aggregation keeps measured scalar data and unmeasured
support reports as separate fields.
-/
structure ScalarDistanceAggregationProfile
    (Axis : Type u) (Payload : Type v) (Scalar : Type w)
    extends DistanceAggregationProfile Axis Payload Scalar where
  measuredScalar : Axis -> Option Scalar
  measuredScalar_some_only_measured :
    ∀ {axis scalar}, measuredScalar axis = some scalar -> axis ∈ measuredSupport
  unmeasuredSupportReport : Set Axis
  unmeasuredSupportReport_exact :
    ∀ axis, axis ∈ unmeasuredSupportReport ↔ axis ∈ unmeasuredSupport

namespace ScalarDistanceAggregationProfile

variable {Axis : Type u} {Payload : Type v} {Scalar : Type w}

/-- VII.原則9.2: scalar payloads are drawn only from measured support. -/
theorem measuredScalar_mem_measuredSupport
    (P : ScalarDistanceAggregationProfile Axis Payload Scalar)
    {axis : Axis} {scalar : Scalar}
    (hscalar : P.measuredScalar axis = some scalar) :
    axis ∈ P.measuredSupport :=
  P.measuredScalar_some_only_measured hscalar

/-- VII.原則9.2: the separate report exposes unmeasured support membership. -/
theorem mem_unmeasuredSupport_of_mem_report
    (P : ScalarDistanceAggregationProfile Axis Payload Scalar)
    {axis : Axis} (haxis : axis ∈ P.unmeasuredSupportReport) :
    axis ∈ P.unmeasuredSupport :=
  (P.unmeasuredSupportReport_exact axis).mp haxis

/--
VII.原則9.2: scalar aggregation does not turn a separately reported
unmeasured axis into measured zero.
-/
theorem unmeasuredReport_not_measuredZero
    (P : ScalarDistanceAggregationProfile Axis Payload Scalar)
    {axis : Axis} (haxis : axis ∈ P.unmeasuredSupportReport) :
    ¬ (P.valueAt axis).IsMeasuredZero :=
  P.toDistanceAggregationProfile.unmeasuredSupport_not_measuredZero
    (P.mem_unmeasuredSupport_of_mem_report haxis)

/--
VII.原則9.2: a separately reported unmeasured axis is not measured support.
-/
theorem unmeasuredReport_not_mem_measuredSupport
    (P : ScalarDistanceAggregationProfile Axis Payload Scalar)
    {axis : Axis} (haxis : axis ∈ P.unmeasuredSupportReport) :
    axis ∉ P.measuredSupport :=
  P.toDistanceAggregationProfile.not_mem_measuredSupport_of_mem_unmeasuredSupport
    (P.mem_unmeasuredSupport_of_mem_report haxis)

/--
VII.原則9.2: a separately reported unmeasured axis has no measured scalar
payload.
-/
theorem measuredScalar_eq_none_of_mem_unmeasuredReport
    (P : ScalarDistanceAggregationProfile Axis Payload Scalar)
    {axis : Axis} (haxis : axis ∈ P.unmeasuredSupportReport) :
    P.measuredScalar axis = none := by
  cases hscalar : P.measuredScalar axis with
  | none => rfl
  | some scalar =>
      have hmeasured : axis ∈ P.measuredSupport :=
        P.measuredScalar_mem_measuredSupport hscalar
      exact False.elim (P.unmeasuredReport_not_mem_measuredSupport haxis hmeasured)

end ScalarDistanceAggregationProfile

/-- VII.定義8.1: metric on atoms. -/
structure AtomMetricBundle (U : AtomCarrier.{u}) where
  Payload : Type u
  distance : U.Atom -> U.Atom -> DistanceValue Payload
  distanceOrder : DistanceValuePartialOrder Payload

/-- VII.定義8.1: metric on selected architecture configurations. -/
structure ConfigurationMetric {U : AtomCarrier.{u}} (Obj : ArchitectureObject U) where
  Configuration : Type u
  distance : Configuration -> Configuration -> DistanceValue Nat
  representsObject : Configuration -> Prop
  representsObject_holds : ∃ configuration, representsObject configuration

/-- VII.定義8.1: metric on selected signature axes. -/
structure SignatureMetric (U : AtomCarrier.{u}) where
  signatureAxes : SignatureAxes U
  axisDistance :
    signatureAxes.Axis -> signatureAxes.Axis -> DistanceValue Nat
  aggregation :
    DistanceAggregationProfile signatureAxes.Axis Nat Nat

/-- VII.定義8.1: selected operation cost reading. -/
structure OperationCost {U : AtomCarrier.{u}} (Obj : ArchitectureObject U) where
  Operation : Type u
  cost : Operation -> DistanceValue Nat
  appliesTo : Operation -> U.Atom -> Prop

/-- VII.定義8.1: selected path-length reading built from operation paths. -/
structure PathLength {U : AtomCarrier.{u}} {Obj : ArchitectureObject U}
    (operationCost : OperationCost Obj) where
  Path : Type u
  startsAt : Path -> U.Atom
  endsAt : Path -> U.Atom
  length : Path -> DistanceValue Nat
  operationsMeasuredSeparately : Prop
  operationsMeasuredSeparately_holds : operationsMeasuredSeparately

/-- VII.定義8.1: selected homotopy filling-cost reading. -/
structure HomotopyFillingCost {U : AtomCarrier.{u}} (Obj : ArchitectureObject U) where
  HomotopyBoundary : Type u
  fillingCost : HomotopyBoundary -> DistanceValue Nat
  finiteWitnessBoundary : Prop
  finiteWitnessBoundary_holds : finiteWitnessBoundary

/-- VII.定義8.1: selected obstruction-measure reading. -/
structure ObstructionMeasure {U : AtomCarrier.{u}} (Obj : ArchitectureObject U) where
  ObstructionIndex : Type u
  measure : ObstructionIndex -> DistanceValue Nat
  supportAggregation :
    DistanceAggregationProfile ObstructionIndex Nat Nat

/-- VII.定義8.1: selected representation-metric reading. -/
structure RepresentationMetric {U : AtomCarrier.{u}} (Obj : ArchitectureObject U) where
  RepresentationState : Type u
  distance : RepresentationState -> RepresentationState -> DistanceValue Nat
  boundedReading : Prop
  boundedReading_holds : boundedReading

/--
VII.定義8.1: Metric AAT as metric enrichment data over a selected
architecture geometry.
-/
structure MetricAAT {U : AtomCarrier.{u}} (Obj : ArchitectureObject U) where
  atomMetricBundle : AtomMetricBundle U
  configurationMetric : ConfigurationMetric Obj
  signatureMetric : SignatureMetric U
  operationCost : OperationCost Obj
  pathLength : PathLength operationCost
  homotopyFillingCost : HomotopyFillingCost Obj
  obstructionMeasure : ObstructionMeasure Obj
  representationMetric : RepresentationMetric Obj

namespace MetricAAT

variable {U : AtomCarrier.{u}} {Obj : ArchitectureObject U}

/-- VII.定義8.1: expose the selected atom metric bundle. -/
def atomMetric (M : MetricAAT Obj) : AtomMetricBundle U :=
  M.atomMetricBundle

/-- VII.定義8.1: expose the selected signature metric. -/
def signatureMetricReading (M : MetricAAT Obj) : SignatureMetric U :=
  M.signatureMetric

/-- VII.定義8.1: expose the selected obstruction measure. -/
def obstructionMeasureReading (M : MetricAAT Obj) : ObstructionMeasure Obj :=
  M.obstructionMeasure

end MetricAAT

end RepresentationAnalysis
end AAT.AG
