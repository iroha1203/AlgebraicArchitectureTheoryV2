import Formal.Arch.Evolution.SFTForecastCone

namespace Formal.Arch

universe u v

/-- A selected SFT region over field states. -/
abbrev FieldRegion (Field : Type u) :=
  Field -> Prop

/--
May-reachability into a selected target region within a finite horizon.

This is an existential statement over the selected `ForecastCone`. It does not
assert probability, default behavior, calibration, recurrence, or convergence.
-/
def MayReach
    {Field : Type u} {Operation : Type v}
    (support : OperationSupport Field Operation)
    (relation : StepRelation Field Operation)
    (source : Field) (horizon : Nat) (targetRegion : FieldRegion Field) :
    Prop :=
  ∃ target : Field,
    ∃ path : FieldPath support relation source target,
      ForecastCone support relation source horizon target path ∧
        targetRegion target

/--
Must-reachability into a selected target region within a finite horizon.

All endpoints admitted by the selected `ForecastCone` must lie in the target
region. This is still relative to the supplied support, relation, and horizon;
it is not a global safety or attractor theorem.
-/
def MustReach
    {Field : Type u} {Operation : Type v}
    (support : OperationSupport Field Operation)
    (relation : StepRelation Field Operation)
    (source : Field) (horizon : Nat) (targetRegion : FieldRegion Field) :
    Prop :=
  ∀ target : Field,
    ∀ path : FieldPath support relation source target,
      ForecastCone support relation source horizon target path ->
        targetRegion target

/--
A selected region is stable under one supported SFT field step.

The predicate is one-step closure for the supplied support and step relation.
It does not add recurrence, global basin, stochastic transition, or convergence
semantics.
-/
def StableRegion
    {Field : Type u} {Operation : Type v}
    (support : OperationSupport Field Operation)
    (relation : StepRelation Field Operation)
    (region : FieldRegion Field) : Prop :=
  ∀ {source target : Field} {operation : Operation},
    region source ->
      support.Supports source operation ->
        relation.Realizes source operation target ->
          region target

/--
The finite-horizon preimage of a selected region under may-reachability.

This is definitional vocabulary for `MayReach`; it is not a basin theorem.
-/
def ReachablePreimage
    {Field : Type u} {Operation : Type v}
    (support : OperationSupport Field Operation)
    (relation : StepRelation Field Operation)
    (horizon : Nat) (targetRegion : FieldRegion Field)
    (source : Field) : Prop :=
  MayReach support relation source horizon targetRegion

/--
Boundary data for SFT reachability vocabulary.

The flags keep strong attractor / basin / probability / recurrence claims as
explicit caller-supplied boundaries rather than consequences of reachability
membership.
-/
structure SFTReachabilityBoundary
    {Field : Type u} {Operation : Type v}
    (support : OperationSupport Field Operation)
    (relation : StepRelation Field Operation) where
  probabilityBoundary : Prop
  attractorBoundary : Prop
  basinBoundary : Prop
  recurrenceBoundary : Prop
  nonConclusions : Prop

namespace SFTReachabilityBoundary

variable {Field : Type u} {Operation : Type v}
variable {support : OperationSupport Field Operation}
variable {relation : StepRelation Field Operation}

/-- Probability / transition-kernel assumptions remain explicit boundary data. -/
def RecordsProbabilityBoundary
    (boundary : SFTReachabilityBoundary support relation) : Prop :=
  boundary.probabilityBoundary

/-- Strong attractor assumptions remain explicit boundary data. -/
def RecordsAttractorBoundary
    (boundary : SFTReachabilityBoundary support relation) : Prop :=
  boundary.attractorBoundary

/-- Strong basin assumptions remain explicit boundary data. -/
def RecordsBasinBoundary
    (boundary : SFTReachabilityBoundary support relation) : Prop :=
  boundary.basinBoundary

/-- Recurrence assumptions remain explicit boundary data. -/
def RecordsRecurrenceBoundary
    (boundary : SFTReachabilityBoundary support relation) : Prop :=
  boundary.recurrenceBoundary

/--
Reachability non-conclusions combine the boundary record with the underlying
support and relation non-conclusions.
-/
def RecordsNonConclusions
    (boundary : SFTReachabilityBoundary support relation) : Prop :=
  boundary.nonConclusions ∧
    support.RecordsNonConclusions ∧ relation.RecordsNonConclusions

end SFTReachabilityBoundary

namespace MayReach

variable {Field : Type u} {Operation : Type v}
variable {support : OperationSupport Field Operation}
variable {relation : StepRelation Field Operation}

/-- Build `MayReach` from an explicit forecast-cone witness. -/
theorem of_forecastCone
    {source target : Field} {horizon : Nat}
    {targetRegion : FieldRegion Field}
    {path : FieldPath support relation source target}
    (hCone : ForecastCone support relation source horizon target path)
    (hTarget : targetRegion target) :
    MayReach support relation source horizon targetRegion :=
  ⟨target, path, hCone, hTarget⟩

/-- A source already in the region may-reaches the region by the nil path. -/
theorem nil
    {source : Field} {horizon : Nat}
    {targetRegion : FieldRegion Field}
    (hSource : targetRegion source) :
    MayReach support relation source horizon targetRegion :=
  of_forecastCone
    (ForecastCone.monotone_horizon (ForecastCone.nil_mem source)
      (Nat.zero_le horizon))
    hSource

/-- Extract the endpoint, path, cone membership, and target-region witness. -/
theorem witness
    {source : Field} {horizon : Nat}
    {targetRegion : FieldRegion Field}
    (hMay : MayReach support relation source horizon targetRegion) :
    ∃ target : Field,
      ∃ path : FieldPath support relation source target,
        ForecastCone support relation source horizon target path ∧
          targetRegion target :=
  hMay

end MayReach

namespace MustReach

variable {Field : Type u} {Operation : Type v}
variable {support : OperationSupport Field Operation}
variable {relation : StepRelation Field Operation}

/-- Apply `MustReach` to an explicit forecast-cone endpoint. -/
theorem target
    {source target : Field} {horizon : Nat}
    {targetRegion : FieldRegion Field}
    (hMust : MustReach support relation source horizon targetRegion)
    {path : FieldPath support relation source target}
    (hCone : ForecastCone support relation source horizon target path) :
    targetRegion target :=
  hMust target path hCone

/-- Any must-reach region contains the source, via the nil path. -/
theorem source_mem
    {source : Field} {horizon : Nat}
    {targetRegion : FieldRegion Field}
    (hMust : MustReach support relation source horizon targetRegion) :
    targetRegion source :=
  hMust source (ArchitecturePath.nil source)
    (ForecastCone.monotone_horizon (ForecastCone.nil_mem source)
      (Nat.zero_le horizon))

/-- Must-reachability immediately implies may-reachability. -/
theorem mayReach
    {source : Field} {horizon : Nat}
    {targetRegion : FieldRegion Field}
    (hMust : MustReach support relation source horizon targetRegion) :
    MayReach support relation source horizon targetRegion :=
  MayReach.nil (hMust.source_mem)

end MustReach

namespace StableRegion

variable {Field : Type u} {Operation : Type v}
variable {support : OperationSupport Field Operation}
variable {relation : StepRelation Field Operation}

/-- Apply one-step stable-region closure to a supported field step. -/
theorem supportedStep
    {region : FieldRegion Field}
    (hStable : StableRegion support relation region)
    {source target : Field}
    (step : SupportedFieldStep support relation source target)
    (hSource : region source) :
    region target :=
  hStable hSource step.supported step.realizes

/-- A stable region is preserved by every supported finite field path. -/
theorem fieldPath_target
    {region : FieldRegion Field}
    (hStable : StableRegion support relation region) :
    {source target : Field} ->
      (path : FieldPath support relation source target) ->
        region source -> region target
  | _, _, ArchitecturePath.nil _, hSource => hSource
  | _, _, ArchitecturePath.cons step rest, hSource =>
      fieldPath_target hStable rest
        (hStable.supportedStep step hSource)

/--
Cone membership plus source membership in a stable region puts the endpoint in
that region. The cone is used only as the selected finite-path witness.
-/
theorem forecastCone_target
    {region : FieldRegion Field}
    (hStable : StableRegion support relation region)
    {source target : Field} {horizon : Nat}
    {path : FieldPath support relation source target}
    (_hCone : ForecastCone support relation source horizon target path)
    (hSource : region source) :
    region target :=
  hStable.fieldPath_target path hSource

/-- Stable-region closure gives must-reachability for every finite horizon. -/
theorem mustReach
    {region : FieldRegion Field}
    (hStable : StableRegion support relation region)
    {source : Field} {horizon : Nat}
    (hSource : region source) :
    MustReach support relation source horizon region := by
  intro target path hCone
  exact hStable.forecastCone_target hCone hSource

end StableRegion

namespace ReachablePreimage

variable {Field : Type u} {Operation : Type v}
variable {support : OperationSupport Field Operation}
variable {relation : StepRelation Field Operation}

/-- `ReachablePreimage` is definitionally the source predicate of `MayReach`. -/
theorem iff_mayReach
    {source : Field} {horizon : Nat}
    {targetRegion : FieldRegion Field} :
    ReachablePreimage support relation horizon targetRegion source ↔
      MayReach support relation source horizon targetRegion :=
  Iff.rfl

/-- Membership in the target region gives membership in its reachable preimage. -/
theorem of_mem
    {source : Field} {horizon : Nat}
    {targetRegion : FieldRegion Field}
    (hSource : targetRegion source) :
    ReachablePreimage support relation horizon targetRegion source :=
  MayReach.nil hSource

end ReachablePreimage

end Formal.Arch
