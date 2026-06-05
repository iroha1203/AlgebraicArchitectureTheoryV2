import Formal.Arch.Evolution.SignatureDynamics
import Formal.Arch.Signature.AnalyticRepresentation

/-!
Bounded distance, measure, and architecture-geometry surfaces for AAT Part IV.

This module deliberately keeps metric diagnostics relative to an explicitly
selected scope.  In particular, an unmeasured axis is not a measured zero, and
distance data alone does not prove global lawfulness, flatness, repair
termination, or semantic completeness.
-/

namespace Formal.Arch

universe u v w

/--
Diagnostic distance values with an explicit separation between measured zero
and unmeasured axes.
-/
inductive DistanceValue where
  | zero
  | measured (value : Nat)
  | unmeasured
  | unavailable
  | incomparable
  | infinite
  deriving DecidableEq, Repr

namespace DistanceValue

/-- The axis is measured and its selected diagnostic value is zero. -/
def IsMeasuredZero : DistanceValue -> Prop
  | zero => True
  | _ => False

/-- The axis has some measured distance payload. -/
def HasMeasuredDistance : DistanceValue -> Prop
  | zero => True
  | measured _ => True
  | _ => False

/-- The axis is explicitly outside the selected measurement scope. -/
def IsUnmeasured : DistanceValue -> Prop
  | unmeasured => True
  | _ => False

/-- Measured payload as a natural number when the selected axis is measured. -/
def measuredNat? : DistanceValue -> Option Nat
  | zero => some 0
  | measured n => some n
  | _ => none

theorem zero_is_measuredZero : IsMeasuredZero zero := by
  trivial

theorem zero_hasMeasuredDistance : HasMeasuredDistance zero := by
  trivial

theorem measured_hasMeasuredDistance (n : Nat) :
    HasMeasuredDistance (measured n) := by
  trivial

theorem unmeasured_isUnmeasured : IsUnmeasured unmeasured := by
  trivial

theorem unmeasured_not_zero : unmeasured ≠ zero := by
  intro h
  cases h

theorem zero_not_unmeasured : zero ≠ unmeasured := by
  intro h
  cases h

theorem unmeasured_not_measuredZero :
    ¬ IsMeasuredZero unmeasured := by
  intro h
  cases h

theorem unmeasured_not_hasMeasuredDistance :
    ¬ HasMeasuredDistance unmeasured := by
  intro h
  cases h

theorem unavailable_not_measuredZero :
    ¬ IsMeasuredZero unavailable := by
  intro h
  cases h

theorem incomparable_not_measuredZero :
    ¬ IsMeasuredZero incomparable := by
  intro h
  cases h

theorem infinite_not_measuredZero :
    ¬ IsMeasuredZero infinite := by
  intro h
  cases h

end DistanceValue

/--
Policy metadata for a selected distance profile.

The fields are `Prop` on purpose: the Lean package records the assumptions and
non-conclusions required by the selected diagnostic profile without calibrating
or proving an empirical metric model.
-/
structure DistanceProfile where
  atomWeightPolicy : Prop
  signatureWeightPolicy : Prop
  operationCostPolicy : Prop
  aggregationPolicy : Prop
  unmeasuredAxisPolicy : Prop
  lawOverlayBoundary : Prop
  nonConclusions : Prop

namespace DistanceProfile

def RecordsUnmeasuredPolicy (profile : DistanceProfile) : Prop :=
  profile.unmeasuredAxisPolicy

def RecordsNonConclusions (profile : DistanceProfile) : Prop :=
  profile.nonConclusions

theorem records_unmeasured_policy
    (profile : DistanceProfile)
    (h : profile.unmeasuredAxisPolicy) :
    profile.RecordsUnmeasuredPolicy :=
  h

theorem records_nonConclusions
    (profile : DistanceProfile)
    (h : profile.nonConclusions) :
    profile.RecordsNonConclusions :=
  h

end DistanceProfile

/--
Selected diagnostic scope for distance measurement.

`measuredAxis` and `unmeasuredAxis` are part of the scope, not inferred from
ambient mathematics.  This keeps absence of measurement separate from a zero
measurement.
-/
structure SelectedDistanceScope (Axis : Type u) where
  profile : DistanceProfile
  measuredAxis : Axis -> Prop
  unmeasuredAxis : Axis -> Prop
  selectedCoverage : Prop
  witnessPolicy : Prop
  nonConclusions : Prop

namespace SelectedDistanceScope

variable {Axis : Type u}

def AxisMeasured (scope : SelectedDistanceScope Axis) (axis : Axis) : Prop :=
  scope.measuredAxis axis

def AxisUnmeasured (scope : SelectedDistanceScope Axis) (axis : Axis) : Prop :=
  scope.unmeasuredAxis axis

def RecordsNonConclusions (scope : SelectedDistanceScope Axis) : Prop :=
  scope.nonConclusions

end SelectedDistanceScope

/--
A bounded diagnostic conclusion over a selected scope.

The conclusion is positive only inside the selected scope and explicitly records
what it does not conclude.
-/
structure BoundedDiagnosticConclusion (Axis : Type u) where
  scope : SelectedDistanceScope Axis
  value : Axis -> DistanceValue
  selectedConclusion : Prop
  doesNotConcludeGlobalLawfulness : Prop
  doesNotConcludeGlobalFlatness : Prop
  doesNotConcludeUnmeasuredZero : Prop

namespace BoundedDiagnosticConclusion

variable {Axis : Type u}

def RecordsNonConclusions
    (conclusion : BoundedDiagnosticConclusion Axis) : Prop :=
  conclusion.doesNotConcludeGlobalLawfulness ∧
  conclusion.doesNotConcludeGlobalFlatness ∧
  conclusion.doesNotConcludeUnmeasuredZero

theorem records_nonConclusions
    (conclusion : BoundedDiagnosticConclusion Axis)
    (hLaw : conclusion.doesNotConcludeGlobalLawfulness)
    (hFlat : conclusion.doesNotConcludeGlobalFlatness)
    (hUnmeasured : conclusion.doesNotConcludeUnmeasuredZero) :
    conclusion.RecordsNonConclusions :=
  ⟨hLaw, hFlat, hUnmeasured⟩

end BoundedDiagnosticConclusion

/-- A selected natural-number distance schema on observed signatures. -/
structure SignatureDistanceSchema (State : Type u) (Sig : Type v) where
  observation : SignatureObservation State Sig
  distance : Sig -> Sig -> Nat
  self_zero : ∀ sig : Sig, distance sig sig = 0
  triangle : ∀ a b c : Sig, distance a c ≤ distance a b + distance b c
  measuredScope : Prop
  nonConclusions : Prop

namespace SignatureDistanceSchema

variable {State : Type u} {Sig : Type v}

/-- Endpoint distance induced by the selected observation schema. -/
def endpointDistance
    (schema : SignatureDistanceSchema State Sig)
    {X Y : State} (_plan : ArchitectureEvolution State X Y) : Nat :=
  schema.distance (schema.observation.observe X) (schema.observation.observe Y)

/-- Path length obtained by summing selected per-step signature distances. -/
def pathLength
    (schema : SignatureDistanceSchema State Sig) :
    {X Y : State} -> ArchitectureEvolution State X Y -> Nat
  | _, _, ArchitecturePath.nil _ => 0
  | X, _, ArchitecturePath.cons (Y := Y) _step rest =>
      schema.distance (schema.observation.observe X)
        (schema.observation.observe Y) + schema.pathLength rest

/-- Hidden excursion is the path length not visible from endpoints alone. -/
def hiddenExcursion
    (schema : SignatureDistanceSchema State Sig)
    {X Y : State} (plan : ArchitectureEvolution State X Y) : Nat :=
  schema.pathLength plan - schema.endpointDistance plan

theorem endpointDistance_nil
    (schema : SignatureDistanceSchema State Sig) (X : State) :
    schema.endpointDistance (ArchitecturePath.nil X) = 0 := by
  simp [endpointDistance, schema.self_zero]

theorem endpointDistance_le_pathLength
    (schema : SignatureDistanceSchema State Sig) :
    {X Y : State} -> (plan : ArchitectureEvolution State X Y) ->
      schema.endpointDistance plan ≤ schema.pathLength plan
  | X, _, ArchitecturePath.nil _ => by
      simp [endpointDistance, pathLength, schema.self_zero]
  | X, _, ArchitecturePath.cons (Y := Y) (Z := Z) _step rest => by
      have hTriangle :
          schema.distance (schema.observation.observe X)
            (schema.observation.observe Z) ≤
          schema.distance (schema.observation.observe X)
            (schema.observation.observe Y) +
          schema.distance (schema.observation.observe Y)
            (schema.observation.observe Z) :=
        schema.triangle _ _ _
      have hRest :
          schema.distance (schema.observation.observe Y)
              (schema.observation.observe Z) ≤
            schema.pathLength rest :=
        endpointDistance_le_pathLength schema rest
      calc
        schema.endpointDistance (ArchitecturePath.cons _step rest)
            ≤ schema.distance (schema.observation.observe X)
                (schema.observation.observe Y) +
              schema.distance (schema.observation.observe Y)
                (schema.observation.observe Z) := by
              simpa [endpointDistance] using hTriangle
        _ ≤ schema.distance (schema.observation.observe X)
                (schema.observation.observe Y) +
              schema.pathLength rest := by
              exact Nat.add_le_add_left hRest _
        _ = schema.pathLength (ArchitecturePath.cons _step rest) := by
              rfl

/-- A path remains inside the selected distance margin. -/
def PathLengthWithinMargin
    (schema : SignatureDistanceSchema State Sig)
    {X Y : State} (plan : ArchitectureEvolution State X Y)
    (margin : Nat) : Prop :=
  schema.pathLength plan < margin

/--
Measured-scope margin stability.

The theorem is bounded by the supplied stepwise preservation witness; the
distance margin is recorded as part of the selected diagnostic package rather
than treated as a global empirical safety theorem.
-/
theorem margin_stability
    (schema : SignatureDistanceSchema State Sig)
    (R : SafeRegion Sig)
    {X Y : State} (plan : ArchitectureEvolution State X Y)
    (margin : Nat)
    (hStart : StateInSafeRegion schema.observation R X)
    (_hWithin : schema.PathLengthWithinMargin plan margin)
    (hPreserves : EveryStepPreservesSafeRegion schema.observation R plan) :
    SignatureTrajectoryInSafeRegion R
      (SignatureTrajectory schema.observation plan) :=
  trajectory_preserves_safeRegion schema.observation R plan hStart hPreserves

end SignatureDistanceSchema

/-- Cost data for selected operations. -/
structure OperationCostModel (Operation : Type u) where
  cost : Operation -> Nat
  costPolicy : Prop
  nonConclusions : Prop

namespace OperationCostModel

variable {Operation : Type u}

/-- Sum of selected costs along a finite operation path. -/
def pathCost (model : OperationCostModel Operation) :
    List Operation -> Nat
  | [] => 0
  | op :: rest => model.cost op + model.pathCost rest

end OperationCostModel

/-- Public alias used by Part IV issue text. -/
abbrev OperationPathCost {Operation : Type u}
    (model : OperationCostModel Operation) : List Operation -> Nat :=
  model.pathCost

/--
Distance to a selected flat region.

Zero reflection is one-way and scoped: it can be used only with the supplied
flatness predicate and coverage assumptions.
-/
structure DistanceToFlatRegion (State : Type u) where
  flatRegion : State -> Prop
  distanceToFlat : State -> Nat
  zeroReflectsFlat : ∀ X : State, distanceToFlat X = 0 -> flatRegion X
  coverageAssumptions : Prop
  nonConclusions : Prop

namespace DistanceToFlatRegion

variable {State : Type u}

theorem flat_of_distance_zero
    (region : DistanceToFlatRegion State)
    (X : State)
    (hZero : region.distanceToFlat X = 0) :
    region.flatRegion X :=
  region.zeroReflectsFlat X hZero

end DistanceToFlatRegion

/--
Bounded side-effect repair step.

The record only states that one selected target distance decreases while the
selected protected movement stays under `epsilon`.
-/
structure BoundedSideEffectRepair (State : Type u) where
  source : State
  target : State
  targetDistance : State -> Nat
  protectedMovement : State -> State -> Nat
  epsilon : Nat
  targetDistanceDecreases :
    targetDistance target < targetDistance source
  protectedMovementWithinBound :
    protectedMovement source target ≤ epsilon
  nonConclusions : Prop

namespace BoundedSideEffectRepair

variable {State : Type u}

theorem targetDistance_decreases
    (repair : BoundedSideEffectRepair State) :
    repair.targetDistance repair.target <
      repair.targetDistance repair.source :=
  repair.targetDistanceDecreases

theorem protectedMovement_within_bound
    (repair : BoundedSideEffectRepair State) :
    repair.protectedMovement repair.source repair.target ≤
      repair.epsilon :=
  repair.protectedMovementWithinBound

end BoundedSideEffectRepair

/-- A bounded lower-bound package for filling cost diagnostics. -/
structure FillingCostLowerBound where
  observationGap : Nat
  fillingCost : Nat
  lipschitzConstant : Nat
  lowerBound : observationGap ≤ lipschitzConstant * fillingCost
  nonConclusions : Prop

namespace FillingCostLowerBound

theorem observationGap_le_lipschitz_mul_fillingCost
    (pkg : FillingCostLowerBound) :
    pkg.observationGap ≤ pkg.lipschitzConstant * pkg.fillingCost :=
  pkg.lowerBound

end FillingCostLowerBound

/--
Selected Lipschitz representation between structural and analytic distances.
-/
structure LipschitzRepresentation
    (State : Type u) (Analytic : Type v) where
  represent : State -> Analytic
  structuralDistance : State -> State -> Nat
  analyticDistance : Analytic -> Analytic -> Nat
  comparable : State -> State -> Prop
  lipschitzConstant : Nat
  lipschitz :
    ∀ X Y : State, comparable X Y ->
      analyticDistance (represent X) (represent Y) ≤
        lipschitzConstant * structuralDistance X Y
  coverageAssumptions : Prop
  witnessCompletenessAssumptions : Prop
  nonConclusions : Prop

namespace LipschitzRepresentation

variable {State : Type u} {Analytic : Type v}

theorem analyticDistance_le_lipschitz
    (rep : LipschitzRepresentation State Analytic)
    {X Y : State}
    (hComparable : rep.comparable X Y) :
    rep.analyticDistance (rep.represent X) (rep.represent Y) ≤
      rep.lipschitzConstant * rep.structuralDistance X Y :=
  rep.lipschitz X Y hComparable

end LipschitzRepresentation

/--
Selected bi-Lipschitz representation.  Reflection is available only under the
stored comparability, coverage, and witness-completeness assumptions.
-/
structure BiLipschitzRepresentation
    (State : Type u) (Analytic : Type v)
    extends LipschitzRepresentation State Analytic where
  lowerConstant : Nat
  lowerBound :
    ∀ X Y : State, comparable X Y ->
      lowerConstant * structuralDistance X Y ≤
        analyticDistance (represent X) (represent Y)

namespace BiLipschitzRepresentation

variable {State : Type u} {Analytic : Type v}

theorem structuralDistance_le_analyticDistance
    (rep : BiLipschitzRepresentation State Analytic)
    {X Y : State}
    (hComparable : rep.comparable X Y) :
    rep.lowerConstant * rep.structuralDistance X Y ≤
      rep.analyticDistance (rep.represent X) (rep.represent Y) :=
  rep.lowerBound X Y hComparable

theorem analyticDistance_le_lipschitz
    (rep : BiLipschitzRepresentation State Analytic)
    {X Y : State}
    (hComparable : rep.comparable X Y) :
    rep.analyticDistance (rep.represent X) (rep.represent Y) ≤
      rep.lipschitzConstant * rep.structuralDistance X Y :=
  rep.lipschitz X Y hComparable

end BiLipschitzRepresentation

end Formal.Arch
