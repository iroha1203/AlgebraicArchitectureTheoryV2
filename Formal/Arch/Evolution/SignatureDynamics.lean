import Formal.Arch.Evolution.ArchitectureEvolution

namespace Formal.Arch

universe u v w

/--
An observation schema from architecture states to a signature domain.

The schema is intentionally generic in `Sig`: concrete `ArchitectureSignatureV1`
and dataset-facing signed measurements can be connected in later modules without
making this core depend on PRs, AI patch distributions, or report schemas.
-/
structure SignatureObservation (State : Type u) (Sig : Type v) where
  observe : State -> Sig
  coverageAssumptions : Prop
  nonConclusions : Prop

namespace SignatureObservation

variable {State : Type u} {Sig : Type v}

/-- A state has the selected observed signature. -/
def Observes (O : SignatureObservation State Sig) (X : State) (sig : Sig) :
    Prop :=
  O.observe X = sig

/-- The observation package explicitly records its non-conclusion boundary. -/
def RecordsNonConclusions (O : SignatureObservation State Sig) : Prop :=
  O.nonConclusions

end SignatureObservation

/--
An abstract delta operation on signatures.

No algebraic laws are assumed here. Endpoint and telescoping theorems can later
specialize this schema with additive or signed delta structure as needed.
-/
structure SignatureDelta (Sig : Type v) (Delta : Type w) where
  delta : Sig -> Sig -> Delta
  nonConclusions : Prop

namespace SignatureDelta

variable {Sig : Type v} {Delta : Type w}

/-- The selected abstract delta between two signatures. -/
def between (D : SignatureDelta Sig Delta) (source target : Sig) : Delta :=
  D.delta source target

/-- The delta package explicitly records its non-conclusion boundary. -/
def RecordsNonConclusions (D : SignatureDelta Sig Delta) : Prop :=
  D.nonConclusions

end SignatureDelta

variable {State : Type u} {Sig : Type v} {Delta : Type w}

/--
A selected safe region in the observed signature domain.

This is a predicate on signatures, not a claim that review, CI, policy, or an
empirical process has enough capacity to keep a real codebase inside it.
-/
abbrev SafeRegion (Sig : Type v) :=
  Sig -> Prop

/-- A state is safe when its selected observation is inside the safe region. -/
def StateInSafeRegion
    (O : SignatureObservation State Sig) (R : SafeRegion Sig) (X : State) :
    Prop :=
  R (O.observe X)

/--
A primitive evolution transition preserves the selected observed safe region.

The predicate is relative to the supplied observation schema and safe region;
it does not follow from the transition tag or from the existence of a review /
CI / policy process.
-/
def StepPreservesSafeRegion
    (O : SignatureObservation State Sig) (R : SafeRegion Sig)
    {X Y : State} (_step : ArchitectureTransition State X Y) : Prop :=
  StateInSafeRegion O R X -> StateInSafeRegion O R Y

/-- Every primitive transition in a path preserves the selected safe region. -/
def EveryStepPreservesSafeRegion
    (O : SignatureObservation State Sig) (R : SafeRegion Sig) :
    {X Y : State} -> ArchitectureEvolution State X Y -> Prop
  | _, _, ArchitecturePath.nil _ => True
  | _, _, ArchitecturePath.cons step rest =>
      StepPreservesSafeRegion O R step ∧
        EveryStepPreservesSafeRegion O R rest

/-- Every observed signature in a trajectory lies inside the selected region. -/
def SignatureTrajectoryInSafeRegion
    (R : SafeRegion Sig) (trajectory : List Sig) : Prop :=
  ∀ sig, sig ∈ trajectory -> R sig

/--
Observe every state visited by an endpoint-indexed architecture evolution path.

For a path `X -> ... -> Y`, the resulting list starts with the observation of
`X` and ends with the observation of `Y`. The endpoint theorem is left as the
next proof obligation.
-/
def SignatureTrajectory (O : SignatureObservation State Sig) :
    {X Y : State} -> ArchitectureEvolution State X Y -> List Sig
  | X, _, ArchitecturePath.nil _ => [O.observe X]
  | X, _, ArchitecturePath.cons _step rest =>
      O.observe X :: SignatureTrajectory O rest

/--
Observe the per-step signature deltas along an architecture evolution path.

The list has one delta for each primitive transition. Net delta aggregation and
telescoping laws are intentionally deferred to the theorem package for #640.
-/
def SignatureDeltaSequence
    (O : SignatureObservation State Sig) (D : SignatureDelta Sig Delta) :
    {X Y : State} -> ArchitectureEvolution State X Y -> List Delta
  | _, _, ArchitecturePath.nil _ => []
  | X, _, ArchitecturePath.cons (Y := Y) _step rest =>
      D.between (O.observe X) (O.observe Y) ::
        SignatureDeltaSequence O D rest

/--
Add the selected per-step signature deltas into one net delta.

This is only a fold API over the supplied `Delta` type. It does not assert that
the deltas are complete measurements, comparable across all axes, or connected
to empirical PR outcomes.
-/
def NetSignatureDelta [Zero Delta] [Add Delta] : List Delta -> Delta
  | [] => 0
  | delta :: rest => delta + NetSignatureDelta rest

/--
The endpoint delta observed over an architecture evolution path.

This keeps endpoint aggregation separate from the per-step sequence so that the
telescoping theorem can state the exact algebraic assumption it needs.
-/
def EndpointSignatureDelta
    (O : SignatureObservation State Sig) (D : SignatureDelta Sig Delta) :
    {X Y : State} -> ArchitectureEvolution State X Y -> Delta
  | X, Y, _plan => D.between (O.observe X) (O.observe Y)

/--
Local additive laws sufficient for net signature deltas to telescope.

The laws are explicit assumptions about the selected delta package. They do not
claim that unmeasured axes, empirical cost, incident risk, review quality, or PR
outcomes are represented by the additive delta.
-/
structure AdditiveSignatureDeltaLaw [Zero Delta] [Add Delta]
    (D : SignatureDelta Sig Delta) where
  self_zero : ∀ sig : Sig, D.between sig sig = 0
  step_telescope :
    ∀ source mid target : Sig,
      D.between source mid + D.between mid target =
        D.between source target
  nonConclusions : Prop

namespace AdditiveSignatureDeltaLaw

variable [Zero Delta] [Add Delta] {D : SignatureDelta Sig Delta}

/-- The law package explicitly records its non-conclusion boundary. -/
def RecordsNonConclusions (_law : AdditiveSignatureDeltaLaw D) : Prop :=
  _law.nonConclusions

end AdditiveSignatureDeltaLaw

/--
Per-step signature deltas telescope to the endpoint delta.

The theorem is relative to `AdditiveSignatureDeltaLaw`: it proves a finite path
calculus fact about the selected additive delta, not an empirical claim about
unmeasured signature axes, cost, incidents, or PR outcomes.
-/
theorem netSignatureDelta_telescopes [Zero Delta] [Add Delta]
    (O : SignatureObservation State Sig) (D : SignatureDelta Sig Delta)
    (law : AdditiveSignatureDeltaLaw D) :
    {X Y : State} -> (plan : ArchitectureEvolution State X Y) ->
      NetSignatureDelta (SignatureDeltaSequence O D plan) =
        EndpointSignatureDelta O D plan
  | X, _, ArchitecturePath.nil _ => by
      simpa [SignatureDeltaSequence, NetSignatureDelta, EndpointSignatureDelta]
        using (law.self_zero (O.observe X)).symm
  | X, Z, ArchitecturePath.cons (Y := Y) _step rest => by
      calc
        NetSignatureDelta
            (SignatureDeltaSequence O D
              (ArchitecturePath.cons (Y := Y) _step rest))
            =
              D.between (O.observe X) (O.observe Y) +
                NetSignatureDelta (SignatureDeltaSequence O D rest) := by
                  rfl
        _ =
              D.between (O.observe X) (O.observe Y) +
                EndpointSignatureDelta O D rest := by
                  rw [netSignatureDelta_telescopes O D law rest]
        _ = EndpointSignatureDelta O D
              (ArchitecturePath.cons (Y := Y) _step rest) := by
                  simpa [EndpointSignatureDelta] using
                    law.step_telescope
                      (O.observe X) (O.observe Y) (O.observe Z)

/--
If the initial observation is safe and every selected transition preserves the
safe region, then the whole observed signature trajectory stays inside it.

The theorem is only about the explicit path and explicit preservation
assumption. It does not claim that empirical review / CI / policy mechanisms
automatically provide those preserving steps.
-/
theorem trajectory_preserves_safeRegion
    (O : SignatureObservation State Sig) (R : SafeRegion Sig) :
    {X Y : State} -> (plan : ArchitectureEvolution State X Y) ->
      StateInSafeRegion O R X ->
      EveryStepPreservesSafeRegion O R plan ->
        SignatureTrajectoryInSafeRegion R (SignatureTrajectory O plan)
  | X, _, ArchitecturePath.nil _, hStart, _hEvery => by
      intro sig hMem
      simp [SignatureTrajectory] at hMem
      simpa [StateInSafeRegion, hMem] using hStart
  | X, _, ArchitecturePath.cons _step rest, hStart, hEvery => by
      intro sig hMem
      simp [SignatureTrajectory] at hMem
      cases hMem with
      | inl hHead =>
          simpa [StateInSafeRegion, hHead] using hStart
      | inr hTail =>
          exact
            trajectory_preserves_safeRegion O R rest
              (hEvery.1 hStart) hEvery.2 sig hTail

/--
A finite observed-trajectory attractor candidate.

The candidate is relative to a supplied finite signature trajectory and selected
region. It records that, after a selected entry index, all remaining observed
signatures stay in that region. It does not assert a global attractor theorem,
completeness of a real codebase universe, stochastic convergence, or empirical
AI patch behavior.
-/
structure AttractorCandidate (Sig : Type v) where
  trajectory : List Sig
  region : SafeRegion Sig
  entryIndex : Nat
  entryWithinTrajectory : entryIndex < trajectory.length
  staysAfterEntry :
    ∀ sig, sig ∈ trajectory.drop entryIndex -> region sig
  coverageAssumptions : Prop
  nonConclusions : Prop

namespace AttractorCandidate

variable {Sig : Type v}

/-- The selected suffix of the finite trajectory that stays in the region. -/
def observedSuffix (candidate : AttractorCandidate Sig) : List Sig :=
  candidate.trajectory.drop candidate.entryIndex

/-- The attractor candidate explicitly records its non-conclusion boundary. -/
def RecordsNonConclusions (candidate : AttractorCandidate Sig) : Prop :=
  candidate.nonConclusions

/-- The selected observed suffix stays inside the candidate region. -/
theorem observedSuffix_in_region (candidate : AttractorCandidate Sig) :
    SignatureTrajectoryInSafeRegion
      candidate.region candidate.observedSuffix := by
  intro sig hMem
  exact candidate.staysAfterEntry sig hMem

end AttractorCandidate

/--
A finite-list basin candidate for a selected attractor candidate.

The schema is intentionally bounded: it speaks only about the supplied finite
initial-state list and bounded operation script. The `reachesAttractor`
predicate is caller-supplied so later modules can instantiate it with a concrete
operation semantics, simulation report, or proof-carrying transition package.
-/
structure BasinCandidate (State : Type u) (Sig : Type v) (Op : Type w) where
  observation : SignatureObservation State Sig
  initialStates : List State
  attractor : AttractorCandidate Sig
  script : List Op
  reachesAttractor : State -> Prop
  everyInitialReaches :
    ∀ X, X ∈ initialStates -> reachesAttractor X
  coverageAssumptions : Prop
  nonConclusions : Prop

namespace BasinCandidate

variable {State : Type u} {Sig : Type v} {Op : Type w}

/-- The basin candidate explicitly records its non-conclusion boundary. -/
def RecordsNonConclusions
    (candidate : BasinCandidate State Sig Op) : Prop :=
  candidate.nonConclusions

/-- Every selected initial state is classified as reaching the candidate. -/
def CoversSelectedInitialStates
    (candidate : BasinCandidate State Sig Op) : Prop :=
  ∀ X, X ∈ candidate.initialStates -> candidate.reachesAttractor X

/--
The finite initial-state list is covered by the caller-supplied reachability
predicate.
-/
theorem coversSelectedInitialStates
    (candidate : BasinCandidate State Sig Op) :
    candidate.CoversSelectedInitialStates :=
  candidate.everyInitialReaches

end BasinCandidate

/--
Iterating a deterministic self-map for a bounded dynamics proof obligation.

This is kept separate from `ArchitectureEvolution`: it is a small future-proof
obligation substrate for eventually periodic finite dynamics, not a theorem
that every observed architecture trajectory is globally periodic.
-/
def IterateSelfMap (step : State -> State) : Nat -> State -> State
  | 0, X => X
  | n + 1, X => IterateSelfMap step n (step X)

/--
Future proof-obligation statement for deterministic finite dynamics.

Later theorem packages can prove this under an explicit finite universe and
orbit-closure assumption. Keeping it as a predicate here prevents the attractor
candidate schema from silently claiming global convergence.
-/
def DeterministicSelfMapEventuallyPeriodic
    (step : State -> State) (start : State) : Prop :=
  ∃ preperiod period : Nat,
    0 < period ∧
      ∀ n, preperiod ≤ n ->
        IterateSelfMap step (n + period) start =
          IterateSelfMap step n start

/--
Two two-step transition orders are observationally commutative when they start
from the same state and their selected final observations agree.

The two intermediate and final states are allowed to differ. This keeps the
predicate about observed signatures rather than definitional equality of
architecture states.
-/
def TwoStepObservationCommutative
    (O : SignatureObservation State Sig)
    {X YLeft ZLeft YRight ZRight : State}
    (_leftFirst : ArchitectureTransition State X YLeft)
    (_leftSecond : ArchitectureTransition State YLeft ZLeft)
    (_rightFirst : ArchitectureTransition State X YRight)
    (_rightSecond : ArchitectureTransition State YRight ZRight) : Prop :=
  O.observe ZLeft = O.observe ZRight

/--
Two two-step transition orders are merge-order sensitive when their selected
final observations differ.

This is a bounded observation predicate. It does not claim that a real PR merge
order predicts incident risk, review cost, or unmeasured signature axes.
-/
def MergeOrderSensitive
    (O : SignatureObservation State Sig)
    {X YLeft ZLeft YRight ZRight : State}
    (_leftFirst : ArchitectureTransition State X YLeft)
    (_leftSecond : ArchitectureTransition State YLeft ZLeft)
    (_rightFirst : ArchitectureTransition State X YRight)
    (_rightSecond : ArchitectureTransition State YRight ZRight) : Prop :=
  O.observe ZLeft ≠ O.observe ZRight

/--
A 0/1 bounded merge-order sensitivity metric for two selected two-step orders.

The value is `0` exactly when the selected final observations agree, and `1`
when they differ. The metric is intentionally local to the supplied observation
schema and does not measure empirical PR risk or hidden axes.
-/
def MergeOrderSensitivity [DecidableEq Sig]
    (O : SignatureObservation State Sig)
    {X YLeft ZLeft YRight ZRight : State}
    (_leftFirst : ArchitectureTransition State X YLeft)
    (_leftSecond : ArchitectureTransition State YLeft ZLeft)
    (_rightFirst : ArchitectureTransition State X YRight)
    (_rightSecond : ArchitectureTransition State YRight ZRight) : Nat :=
  if O.observe ZLeft = O.observe ZRight then 0 else 1

/--
If two selected two-step transition orders are observationally commutative, the
bounded merge-order sensitivity metric is zero.
-/
theorem mergeOrderSensitivity_eq_zero_of_twoStepObservationCommutative
    [DecidableEq Sig]
    (O : SignatureObservation State Sig)
    {X YLeft ZLeft YRight ZRight : State}
    (leftFirst : ArchitectureTransition State X YLeft)
    (leftSecond : ArchitectureTransition State YLeft ZLeft)
    (rightFirst : ArchitectureTransition State X YRight)
    (rightSecond : ArchitectureTransition State YRight ZRight)
    (hCommutes :
      TwoStepObservationCommutative O leftFirst leftSecond rightFirst rightSecond) :
    MergeOrderSensitivity O leftFirst leftSecond rightFirst rightSecond = 0 := by
  dsimp [MergeOrderSensitivity]
  exact if_pos (by
    simpa [TwoStepObservationCommutative] using hCommutes)

/--
Observational commutativity rules out selected merge-order sensitivity.
-/
theorem not_mergeOrderSensitive_of_twoStepObservationCommutative
    (O : SignatureObservation State Sig)
    {X YLeft ZLeft YRight ZRight : State}
    (leftFirst : ArchitectureTransition State X YLeft)
    (leftSecond : ArchitectureTransition State YLeft ZLeft)
    (rightFirst : ArchitectureTransition State X YRight)
    (rightSecond : ArchitectureTransition State YRight ZRight)
    (hCommutes :
      TwoStepObservationCommutative O leftFirst leftSecond rightFirst rightSecond) :
    ¬ MergeOrderSensitive O leftFirst leftSecond rightFirst rightSecond := by
  intro hSensitive
  exact hSensitive (by
    simpa [TwoStepObservationCommutative] using hCommutes)

/-
A tiny finite-state witness that locally lawful steps can still be
order-sensitive under a selected observation.

The example is deliberately synthetic: it proves only that local lawfulness
fields do not force final observations to agree.
-/
namespace MergeOrderCounterexample

abbrev ExampleState := Nat
abbrev ExampleSig := Nat

def observation : SignatureObservation ExampleState ExampleSig where
  observe := id
  coverageAssumptions := True
  nonConclusions := True

def leftFirst : ArchitectureTransition ExampleState 0 1 where
  kind := ArchitectureTransitionKind.featureExtension
  lawful := True
  coverageAssumptions := True
  exactnessAssumptions := True
  nonConclusions := True

def leftSecond : ArchitectureTransition ExampleState 1 3 where
  kind := ArchitectureTransitionKind.policyUpdate
  lawful := True
  coverageAssumptions := True
  exactnessAssumptions := True
  nonConclusions := True

def rightFirst : ArchitectureTransition ExampleState 0 2 where
  kind := ArchitectureTransitionKind.policyUpdate
  lawful := True
  coverageAssumptions := True
  exactnessAssumptions := True
  nonConclusions := True

def rightSecond : ArchitectureTransition ExampleState 2 4 where
  kind := ArchitectureTransitionKind.featureExtension
  lawful := True
  coverageAssumptions := True
  exactnessAssumptions := True
  nonConclusions := True

/-- Each selected primitive step in the counterexample is locally lawful. -/
theorem steps_lawful :
    leftFirst.lawful ∧ leftSecond.lawful ∧
      rightFirst.lawful ∧ rightSecond.lawful := by
  simp [leftFirst, leftSecond, rightFirst, rightSecond]

/-- The two selected orders do not commute observationally. -/
theorem not_twoStepObservationCommutative :
    ¬ TwoStepObservationCommutative
        observation leftFirst leftSecond rightFirst rightSecond := by
  simp [TwoStepObservationCommutative, observation]

/-- The selected orders are merge-order sensitive. -/
theorem mergeOrderSensitive :
    MergeOrderSensitive
        observation leftFirst leftSecond rightFirst rightSecond := by
  simp [MergeOrderSensitive, observation]

/-- The bounded merge-order sensitivity metric evaluates to `1`. -/
theorem mergeOrderSensitivity_eq_one :
    MergeOrderSensitivity
        observation leftFirst leftSecond rightFirst rightSecond = 1 := by
  simp [MergeOrderSensitivity, observation]

end MergeOrderCounterexample

end Formal.Arch
