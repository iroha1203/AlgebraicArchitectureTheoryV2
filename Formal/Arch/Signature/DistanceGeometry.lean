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

theorem hiddenExcursion_eq_pathLength_sub_endpointDistance
    (schema : SignatureDistanceSchema State Sig)
    {X Y : State} (plan : ArchitectureEvolution State X Y) :
    schema.hiddenExcursion plan =
      schema.pathLength plan - schema.endpointDistance plan := by
  rfl

theorem endpointDistance_add_hiddenExcursion_eq_pathLength
    (schema : SignatureDistanceSchema State Sig)
    {X Y : State} (plan : ArchitectureEvolution State X Y) :
    schema.endpointDistance plan + schema.hiddenExcursion plan =
      schema.pathLength plan := by
  unfold hiddenExcursion
  exact Nat.add_sub_of_le
    (SignatureDistanceSchema.endpointDistance_le_pathLength schema plan)

theorem hiddenExcursion_positive_of_endpointDistance_lt_pathLength
    (schema : SignatureDistanceSchema State Sig)
    {X Y : State} (plan : ArchitectureEvolution State X Y)
    (hVisibleGap : schema.endpointDistance plan < schema.pathLength plan) :
    0 < schema.hiddenExcursion plan := by
  unfold hiddenExcursion
  exact Nat.sub_pos_of_lt hVisibleGap

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

/--
A supplied finite route witness and its selected cost.

This records the cost of one concrete route.  It is not a global shortest-path
claim and does not enumerate every possible route.
-/
structure FiniteRouteCost (Route : Type u) where
  route : Route
  cost : Nat
  costEvidence : Prop
  selectedScope : Prop
  nonConclusions : Prop

namespace FiniteRouteCost

variable {Route : Type u}

def RecordsSelectedScope (witness : FiniteRouteCost Route) : Prop :=
  witness.selectedScope

def RecordsNonConclusions (witness : FiniteRouteCost Route) : Prop :=
  witness.nonConclusions

theorem records_selectedScope
    (witness : FiniteRouteCost Route)
    (h : witness.selectedScope) :
    witness.RecordsSelectedScope :=
  h

theorem records_nonConclusions
    (witness : FiniteRouteCost Route)
    (h : witness.nonConclusions) :
    witness.RecordsNonConclusions :=
  h

end FiniteRouteCost

/--
A supplied finite filler witness and its selected cost.

The witness is intentionally finite and supplied; it does not assert universal
filler completeness.
-/
structure FiniteFillerCost (Filler : Type u) where
  filler : Filler
  cost : Nat
  costEvidence : Prop
  selectedScope : Prop
  nonConclusions : Prop

namespace FiniteFillerCost

variable {Filler : Type u}

def RecordsSelectedScope (witness : FiniteFillerCost Filler) : Prop :=
  witness.selectedScope

def RecordsNonConclusions (witness : FiniteFillerCost Filler) : Prop :=
  witness.nonConclusions

theorem records_selectedScope
    (witness : FiniteFillerCost Filler)
    (h : witness.selectedScope) :
    witness.RecordsSelectedScope :=
  h

theorem records_nonConclusions
    (witness : FiniteFillerCost Filler)
    (h : witness.nonConclusions) :
    witness.RecordsNonConclusions :=
  h

end FiniteFillerCost

/--
A supplied finite homotopy generator sequence and its selected cost.
-/
structure FiniteHomotopyCost (Generator : Type u) where
  generators : List Generator
  cost : Nat
  costEvidence : Prop
  selectedScope : Prop
  nonConclusions : Prop

namespace FiniteHomotopyCost

variable {Generator : Type u}

def RecordsSelectedScope (witness : FiniteHomotopyCost Generator) : Prop :=
  witness.selectedScope

def RecordsNonConclusions (witness : FiniteHomotopyCost Generator) : Prop :=
  witness.nonConclusions

theorem records_selectedScope
    (witness : FiniteHomotopyCost Generator)
    (h : witness.selectedScope) :
    witness.RecordsSelectedScope :=
  h

theorem records_nonConclusions
    (witness : FiniteHomotopyCost Generator)
    (h : witness.nonConclusions) :
    witness.RecordsNonConclusions :=
  h

end FiniteHomotopyCost

/--
`bound` is a lower bound for all selected candidates in the supplied finite
candidate universe.
-/
def LowerBoundForSelectedCandidates
    {Candidate : Type u}
    (candidates : List Candidate)
    (selected : Candidate -> Prop)
    (cost : Candidate -> Nat)
    (bound : Nat) : Prop :=
  ∀ candidate, candidate ∈ candidates -> selected candidate ->
    bound ≤ cost candidate

/--
Selected finite optimum inside a supplied candidate universe.

The selected candidate is optimal only within `candidates`; no global optimizer
or route-completeness claim is included.
-/
structure SelectedFiniteOptimum (Candidate : Type u) where
  candidates : List Candidate
  selected : Candidate -> Prop
  cost : Candidate -> Nat
  optimal : Candidate
  optimal_mem : optimal ∈ candidates
  optimal_selected : selected optimal
  cost_le_of_mem_selected :
    ∀ candidate, candidate ∈ candidates -> selected candidate ->
      cost optimal ≤ cost candidate
  nonConclusions : Prop

namespace SelectedFiniteOptimum

variable {Candidate : Type u}

def lowerBound
    (optimum : SelectedFiniteOptimum Candidate) : Nat :=
  optimum.cost optimum.optimal

theorem lowerBound_for_selected_candidates
    (optimum : SelectedFiniteOptimum Candidate) :
    LowerBoundForSelectedCandidates optimum.candidates optimum.selected
      optimum.cost optimum.lowerBound := by
  intro candidate hMem hSelected
  exact optimum.cost_le_of_mem_selected candidate hMem hSelected

theorem optimal_cost_le
    (optimum : SelectedFiniteOptimum Candidate)
    {candidate : Candidate}
    (hMem : candidate ∈ optimum.candidates)
    (hSelected : optimum.selected candidate) :
    optimum.cost optimum.optimal ≤ optimum.cost candidate :=
  optimum.cost_le_of_mem_selected candidate hMem hSelected

theorem records_nonConclusions
    (optimum : SelectedFiniteOptimum Candidate)
    (h : optimum.nonConclusions) :
    optimum.nonConclusions :=
  h

end SelectedFiniteOptimum

/--
Abstract infimum-style interface backed by lower-bound and approximation
witnesses.  This is intentionally an interface, not a computable global
optimizer or a completeness theorem for all possible candidates.
-/
structure AbstractInfimumInterface (Candidate : Type u) where
  candidate : Candidate -> Prop
  cost : Candidate -> Nat
  infimumValue : Nat
  isLowerBound : ∀ c, candidate c -> infimumValue ≤ cost c
  approximatingWitness :
    ∀ tolerance : Nat,
      ∃ c, candidate c ∧ cost c ≤ infimumValue + tolerance
  nonConclusions : Prop

namespace AbstractInfimumInterface

variable {Candidate : Type u}

theorem lowerBound
    (interface : AbstractInfimumInterface Candidate)
    {candidate : Candidate}
    (hCandidate : interface.candidate candidate) :
    interface.infimumValue ≤ interface.cost candidate :=
  interface.isLowerBound candidate hCandidate

theorem exists_approximatingWitness
    (interface : AbstractInfimumInterface Candidate)
    (tolerance : Nat) :
    ∃ candidate, interface.candidate candidate ∧
      interface.cost candidate ≤ interface.infimumValue + tolerance :=
  interface.approximatingWitness tolerance

def ofSelectedFiniteOptimum
    (optimum : SelectedFiniteOptimum Candidate) :
    AbstractInfimumInterface Candidate where
  candidate := fun candidate =>
    candidate ∈ optimum.candidates ∧ optimum.selected candidate
  cost := optimum.cost
  infimumValue := optimum.cost optimum.optimal
  isLowerBound := by
    intro candidate hCandidate
    exact optimum.cost_le_of_mem_selected candidate hCandidate.1 hCandidate.2
  approximatingWitness := by
    intro tolerance
    exact
      ⟨ optimum.optimal
      , ⟨optimum.optimal_mem, optimum.optimal_selected⟩
      , Nat.le_add_right _ _⟩
  nonConclusions := optimum.nonConclusions

end AbstractInfimumInterface

/--
Selected distance to a region such as a lawful or flat region.

Zero reflection is always available from the supplied field.  The converse
requires the stored exactness assumptions; this prevents distance values from
becoming unscoped global lawfulness or flatness claims.
-/
structure SelectedDistanceToRegion (State : Type u) where
  region : State -> Prop
  distanceToRegion : State -> Nat
  zeroReflectsRegion : ∀ X : State, distanceToRegion X = 0 -> region X
  exactnessAssumptions : Prop
  regionReflectsZero :
    exactnessAssumptions -> ∀ X : State, region X -> distanceToRegion X = 0
  coverageAssumptions : Prop
  nonConclusions : Prop

namespace SelectedDistanceToRegion

variable {State : Type u}

theorem region_of_distance_zero
    (pkg : SelectedDistanceToRegion State)
    (X : State)
    (hZero : pkg.distanceToRegion X = 0) :
    pkg.region X :=
  pkg.zeroReflectsRegion X hZero

theorem distance_zero_of_region
    (pkg : SelectedDistanceToRegion State)
    (hExact : pkg.exactnessAssumptions)
    (X : State)
    (hRegion : pkg.region X) :
    pkg.distanceToRegion X = 0 :=
  pkg.regionReflectsZero hExact X hRegion

def RecordsNonConclusions
    (pkg : SelectedDistanceToRegion State) : Prop :=
  pkg.nonConclusions

theorem records_nonConclusions
    (pkg : SelectedDistanceToRegion State)
    (h : pkg.nonConclusions) :
    pkg.RecordsNonConclusions :=
  h

end SelectedDistanceToRegion

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

/-- Selected operations can be read by bounded distortion predicates. -/
structure MetricOperationAction
    (State : Type u) (Operation : Type v) where
  apply : Operation -> State -> State
  distance : State -> State -> Nat
  selectedOperation : Operation -> Prop
  selectedScope : Prop
  nonConclusions : Prop

namespace MetricOperationAction

variable {State : Type u} {Operation : Type v}

def PreservesDistance
    (action : MetricOperationAction State Operation)
    (operation : Operation) : Prop :=
  ∀ X Y : State,
    action.distance (action.apply operation X) (action.apply operation Y) =
      action.distance X Y

def NonExpansive
    (action : MetricOperationAction State Operation)
    (operation : Operation) : Prop :=
  ∀ X Y : State,
    action.distance (action.apply operation X) (action.apply operation Y) ≤
      action.distance X Y

def Lipschitz
    (action : MetricOperationAction State Operation)
    (operation : Operation)
    (constant : Nat) : Prop :=
  ∀ X Y : State,
    action.distance (action.apply operation X) (action.apply operation Y) ≤
      constant * action.distance X Y

structure SelectedMetricGaloisPackage
    (action : MetricOperationAction State Operation) where
  operations : List Operation
  invariant : State -> Prop
  operationStable :
    ∀ operation, operation ∈ operations -> action.selectedOperation operation ->
      action.NonExpansive operation
  invariantStable :
    ∀ operation X, operation ∈ operations ->
      action.selectedOperation operation -> invariant X ->
        invariant (action.apply operation X)
  selectedScope : Prop
  nonConclusions : Prop

namespace SelectedMetricGaloisPackage

theorem operation_nonExpansive
    {action : MetricOperationAction State Operation}
    (pkg : SelectedMetricGaloisPackage action)
    {operation : Operation}
    (hMem : operation ∈ pkg.operations)
    (hSelected : action.selectedOperation operation) :
    action.NonExpansive operation :=
  pkg.operationStable operation hMem hSelected

theorem invariant_stable
    {action : MetricOperationAction State Operation}
    (pkg : SelectedMetricGaloisPackage action)
    {operation : Operation} {X : State}
    (hMem : operation ∈ pkg.operations)
    (hSelected : action.selectedOperation operation)
    (hInvariant : pkg.invariant X) :
    pkg.invariant (action.apply operation X) :=
  pkg.invariantStable operation X hMem hSelected hInvariant

end SelectedMetricGaloisPackage

end MetricOperationAction

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

/-- A finite selected repair sequence. -/
structure FiniteRepairSequence (State : Type u) where
  steps : List (BoundedSideEffectRepair State)
  selectedTarget : State -> Prop
  selectedScope : Prop
  nonConclusions : Prop

namespace FiniteRepairSequence

variable {State : Type u}

def AllStepsDecrease (sequence : FiniteRepairSequence State) : Prop :=
  ∀ step, step ∈ sequence.steps ->
    step.targetDistance step.target < step.targetDistance step.source

theorem allStepsDecrease
    (sequence : FiniteRepairSequence State) :
    sequence.AllStepsDecrease := by
  intro step _hMem
  exact step.targetDistance_decreases

end FiniteRepairSequence

/--
One selected repair step is contractive in the supplied Nat-compatible
ratio.  The inequality is cross-multiplied to avoid introducing real analysis
into the bounded theorem package.
-/
structure ContractiveRepairStep (State : Type u) where
  source : State
  target : State
  targetDistance : State -> Nat
  numerator : Nat
  denominator : Nat
  ratioBound : numerator < denominator
  contractive :
    denominator * targetDistance target ≤
      numerator * targetDistance source
  selectedScope : Prop
  nonConclusions : Prop

namespace ContractiveRepairStep

variable {State : Type u}

theorem target_contracts
    (step : ContractiveRepairStep State) :
    step.denominator * step.targetDistance step.target ≤
      step.numerator * step.targetDistance step.source :=
  step.contractive

theorem ratio_lt_one
    (step : ContractiveRepairStep State) :
    step.numerator < step.denominator :=
  step.ratioBound

end ContractiveRepairStep

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

/-- Quantitative homotopy bound over a selected finite generator sequence. -/
structure QuantitativeHomotopyBound where
  observationDistance : Nat
  homotopyCost : Nat
  lipschitzConstant : Nat
  bound : observationDistance ≤ lipschitzConstant * homotopyCost
  selectedScope : Prop
  nonConclusions : Prop

namespace QuantitativeHomotopyBound

theorem observationDistance_le
    (pkg : QuantitativeHomotopyBound) :
    pkg.observationDistance ≤ pkg.lipschitzConstant * pkg.homotopyCost :=
  pkg.bound

end QuantitativeHomotopyBound

/-- Finite Dehn-style upper bound over a supplied loop candidate list. -/
structure FiniteDehnBound (Loop : Type u) where
  candidates : List Loop
  boundaryLength : Loop -> Nat
  fillingArea : Loop -> Nat
  boundaryLimit : Nat
  dehnValue : Nat
  upperBound :
    ∀ loop, loop ∈ candidates -> boundaryLength loop ≤ boundaryLimit ->
      fillingArea loop ≤ dehnValue
  selectedScope : Prop
  nonConclusions : Prop

namespace FiniteDehnBound

variable {Loop : Type u}

theorem fillingArea_le_dehnValue
    (pkg : FiniteDehnBound Loop)
    {loop : Loop}
    (hMem : loop ∈ pkg.candidates)
    (hBoundary : pkg.boundaryLength loop ≤ pkg.boundaryLimit) :
    pkg.fillingArea loop ≤ pkg.dehnValue :=
  pkg.upperBound loop hMem hBoundary

end FiniteDehnBound

/--
Persistent non-fillability at a selected scale.  This is a bounded predicate
over the supplied candidate universe, not a universal non-fillability theorem.
-/
structure PersistentNonFillability (Filler : Type u) where
  scale : Nat
  candidate : Filler -> Prop
  fillerCost : Filler -> Nat
  noFillerWithinScale :
    ∀ filler, candidate filler -> fillerCost filler ≤ scale -> False
  selectedScope : Prop
  nonConclusions : Prop

namespace PersistentNonFillability

variable {Filler : Type u}

theorem no_candidate_filler_within_scale
    (pkg : PersistentNonFillability Filler)
    {filler : Filler}
    (hCandidate : pkg.candidate filler)
    (hWithin : pkg.fillerCost filler ≤ pkg.scale) :
    False :=
  pkg.noFillerWithinScale filler hCandidate hWithin

end PersistentNonFillability

/-- Selected curvature readings on named axes. -/
structure SelectedCurvatureReading
    (Axis : Type u) (State : Type v) where
  curvatureMass : Axis -> State -> Nat
  measuredAxis : Axis -> Prop
  selectedScope : Prop
  nonConclusions : Prop

/-- Curvature transport between two selected axes across one operation/read. -/
structure CurvatureTransport
    (Axis : Type u) (State : Type v) where
  reading : SelectedCurvatureReading Axis State
  before : State
  after : State
  targetAxis : Axis
  transportedAxis : Axis
  targetMeasured : reading.measuredAxis targetAxis
  transportedMeasured : reading.measuredAxis transportedAxis
  targetDecreases :
    reading.curvatureMass targetAxis after <
      reading.curvatureMass targetAxis before
  transportedIncreases :
    reading.curvatureMass transportedAxis before <
      reading.curvatureMass transportedAxis after
  selectedScope : Prop
  nonConclusions : Prop

namespace CurvatureTransport

variable {Axis : Type u} {State : Type v}

theorem target_curvature_decreases
    (pkg : CurvatureTransport Axis State) :
    pkg.reading.curvatureMass pkg.targetAxis pkg.after <
      pkg.reading.curvatureMass pkg.targetAxis pkg.before :=
  pkg.targetDecreases

theorem transported_curvature_increases
    (pkg : CurvatureTransport Axis State) :
    pkg.reading.curvatureMass pkg.transportedAxis pkg.before <
      pkg.reading.curvatureMass pkg.transportedAxis pkg.after :=
  pkg.transportedIncreases

end CurvatureTransport

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

theorem analyticDistance_le_of_structuralDistance_le
    (rep : LipschitzRepresentation State Analytic)
    {X Y : State}
    (hComparable : rep.comparable X Y)
    {epsilon : Nat}
    (hStructural : rep.structuralDistance X Y ≤ epsilon) :
    rep.analyticDistance (rep.represent X) (rep.represent Y) ≤
      rep.lipschitzConstant * epsilon := by
  calc
    rep.analyticDistance (rep.represent X) (rep.represent Y)
        ≤ rep.lipschitzConstant * rep.structuralDistance X Y :=
      rep.analyticDistance_le_lipschitz hComparable
    _ ≤ rep.lipschitzConstant * epsilon :=
      Nat.mul_le_mul_left rep.lipschitzConstant hStructural

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

/--
Spectral / analytic stability package for a selected comparable pair.
-/
structure SpectralStabilityPackage
    (State : Type u) (Spectral : Type v) where
  represent : State -> Spectral
  structuralDistance : State -> State -> Nat
  spectralDistance : Spectral -> Spectral -> Nat
  source : State
  target : State
  epsilon : Nat
  lipschitzConstant : Nat
  structuralWithin : structuralDistance source target ≤ epsilon
  spectralBound :
    spectralDistance (represent source) (represent target) ≤
      lipschitzConstant * epsilon
  coverageAssumptions : Prop
  witnessCompletenessAssumptions : Prop
  nonConclusions : Prop

namespace SpectralStabilityPackage

variable {State : Type u} {Spectral : Type v}

theorem spectralDistance_le
    (pkg : SpectralStabilityPackage State Spectral) :
    pkg.spectralDistance (pkg.represent pkg.source) (pkg.represent pkg.target) ≤
      pkg.lipschitzConstant * pkg.epsilon :=
  pkg.spectralBound

end SpectralStabilityPackage

end Formal.Arch
