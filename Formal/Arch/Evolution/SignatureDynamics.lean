import Mathlib.Data.Fintype.Pigeonhole
import Formal.Arch.Evolution.ArchitectureEvolution
import Formal.Arch.Signature.Signature

namespace Formal.Arch

universe u v w x

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
A bounded recurrence witness inside an explicitly supplied finite trajectory.

The predicate asks for a nonempty repeated finite block containing the selected
signature. It is a finite-list witness only; it does not assert a global
recurrent class, convergence theorem, or empirical attractor discovery claim.
-/
def SignatureTrajectoryHasBoundedReturn
    (trajectory : List Sig) (sig : Sig) : Prop :=
  ∃ pre cycle post : List Sig,
    cycle ≠ [] ∧ sig ∈ cycle ∧
      trajectory = pre ++ cycle ++ cycle ++ post

/--
A selected recurrent signature region for a finite observed trajectory.

Every signature in the supplied region must have a bounded repeated-block
witness in the supplied trajectory. The region is still caller-selected and
finite-trajectory relative.
-/
def RecurrentSignatureRegion
    (trajectory : List Sig) (region : SafeRegion Sig) : Prop :=
  ∀ sig, region sig -> SignatureTrajectoryHasBoundedReturn trajectory sig

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
The observed trajectory can be decomposed into a prefix followed by the target
observation.
-/
theorem signatureTrajectory_endsWith_target
    (O : SignatureObservation State Sig) :
    {X Y : State} -> (plan : ArchitectureEvolution State X Y) ->
      ∃ pre : List Sig,
        SignatureTrajectory O plan = pre ++ [O.observe Y]
  | _, _, ArchitecturePath.nil _ => by
      exact ⟨[], by simp [SignatureTrajectory]⟩
  | X, _, ArchitecturePath.cons _step rest => by
      obtain ⟨pre, hPre⟩ :=
        signatureTrajectory_endsWith_target O rest
      exact ⟨O.observe X :: pre, by simp [SignatureTrajectory, hPre]⟩

/-- The observed trajectory has one more entry than the path step length. -/
theorem signatureTrajectory_length
    (O : SignatureObservation State Sig) :
    {X Y : State} -> (plan : ArchitectureEvolution State X Y) ->
      (SignatureTrajectory O plan).length = ArchitecturePath.length plan + 1
  | _, _, ArchitecturePath.nil _ => by
      simp [SignatureTrajectory, ArchitecturePath.length]
  | _, _, ArchitecturePath.cons _step rest => by
      simp [SignatureTrajectory, ArchitecturePath.length,
        signatureTrajectory_length O rest]

/-- The per-step delta sequence has exactly the path step length. -/
theorem signatureDeltaSequence_length
    (O : SignatureObservation State Sig) (D : SignatureDelta Sig Delta) :
    {X Y : State} -> (plan : ArchitectureEvolution State X Y) ->
      (SignatureDeltaSequence O D plan).length = ArchitecturePath.length plan
  | _, _, ArchitecturePath.nil _ => by
      simp [SignatureDeltaSequence, ArchitecturePath.length]
  | _, _, ArchitecturePath.cons _step rest => by
      simp [SignatureDeltaSequence, ArchitecturePath.length,
        signatureDeltaSequence_length O D rest]

/-- A trajectory is nonempty, so its head consed with its tail reconstructs it. -/
theorem signatureTrajectory_head_cons_tail
    (O : SignatureObservation State Sig) :
    {X Y : State} -> (plan : ArchitectureEvolution State X Y) ->
      O.observe X :: (SignatureTrajectory O plan).tail =
        SignatureTrajectory O plan
  | _, _, ArchitecturePath.nil _ => by
      simp [SignatureTrajectory]
  | _, _, ArchitecturePath.cons _step rest => by
      simp [SignatureTrajectory]

/--
Observed trajectory over an appended path splits by segment, with the shared
middle observation contributed by the left segment and dropped from the right
segment via `List.tail`.
-/
theorem signatureTrajectory_append
    (O : SignatureObservation State Sig)
    {X Y Z : State} (left : ArchitectureEvolution State X Y)
    (right : ArchitectureEvolution State Y Z) :
    SignatureTrajectory O (ArchitecturePath.append left right) =
      SignatureTrajectory O left ++ (SignatureTrajectory O right).tail := by
  induction left with
  | nil X =>
      simpa [ArchitecturePath.append, SignatureTrajectory] using
        (signatureTrajectory_head_cons_tail O right).symm
  | cons step rest ih =>
      simp [ArchitecturePath.append, SignatureTrajectory, ih]

/-- Per-step delta sequences concatenate exactly under path append. -/
theorem signatureDeltaSequence_append
    (O : SignatureObservation State Sig) (D : SignatureDelta Sig Delta)
    {X Y Z : State} (left : ArchitectureEvolution State X Y)
    (right : ArchitectureEvolution State Y Z) :
    SignatureDeltaSequence O D (ArchitecturePath.append left right) =
      SignatureDeltaSequence O D left ++ SignatureDeltaSequence O D right := by
  induction left with
  | nil X =>
      simp [ArchitecturePath.append, SignatureDeltaSequence]
  | cons step rest ih =>
      simp [ArchitecturePath.append, SignatureDeltaSequence, ih]

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

namespace ArchitectureSignatureV1MeasuredAxisDelta

abbrev V1Signature := ArchitectureSignature.ArchitectureSignatureV1
abbrev V1Axis := ArchitectureSignature.ArchitectureSignatureV1Axis

/--
Selected measured-axis delta schema for concrete `ArchitectureSignatureV1`
values.

The schema records the axes selected for signed endpoint / net-delta reading.
It does not assert that every `ArchitectureSignatureV1` value measures those
axes; the measured trajectory domain below carries `some n` evidence per
state.
-/
structure Schema where
  selectedAxes : List V1Axis
  coverageAssumptions : Prop
  nonConclusions : Prop

namespace Schema

/-- The selected axis predicate for the concrete V1 measured-delta schema. -/
def AxisSelected (schema : Schema) (axis : V1Axis) : Prop :=
  axis ∈ schema.selectedAxes

/-- The schema explicitly records its non-conclusion boundary. -/
def RecordsNonConclusions (schema : Schema) : Prop :=
  schema.nonConclusions

/--
The concrete measured-axis package keeps `none` outside available-zero
evidence, even for selected axes.
-/
def RecordsUnmeasuredNonConclusion (schema : Schema) : Prop :=
  ∀ sig axis,
    schema.AxisSelected axis ->
      ArchitectureSignature.ArchitectureSignatureV1.axisValue sig axis =
        none ->
        ¬ ArchitectureSignature.ArchitectureSignatureV1.axisAvailableAndZero
          sig axis

/-- A selected unmeasured axis is not available-and-zero evidence. -/
theorem unmeasured_not_axisAvailableAndZero
    (schema : Schema) {sig : V1Signature} {axis : V1Axis}
    (_hSelected : schema.AxisSelected axis)
    (hNone :
      ArchitectureSignature.ArchitectureSignatureV1.axisValue sig axis =
        none) :
    ¬ ArchitectureSignature.ArchitectureSignatureV1.axisAvailableAndZero
        sig axis :=
  ArchitectureSignature.ArchitectureSignatureV1.not_axisAvailableAndZero_of_axisValue_none
    hNone

end Schema

/--
A concrete Signature V1 sample whose selected axis is actually measured.

The `value_eq` field is the bridge from `Option Nat` to the measured natural
value used by the signed additive delta theorem.
-/
structure MeasuredAxisSignature (axis : V1Axis) where
  signature : V1Signature
  value : Nat
  value_eq :
    ArchitectureSignature.ArchitectureSignatureV1.axisValue signature axis =
      some value

/--
An unmeasured V1 axis cannot be represented as a measured-axis signature
sample for the same axis.
-/
theorem not_measuredAxisSignature_of_axisValue_none
    {axis : V1Axis} {sig : V1Signature}
    (hNone :
      ArchitectureSignature.ArchitectureSignatureV1.axisValue sig axis =
        none) :
    ¬ ∃ sample : MeasuredAxisSignature axis, sample.signature = sig := by
  intro hSample
  rcases hSample with ⟨sample, hSig⟩
  have hSome :
      ArchitectureSignature.ArchitectureSignatureV1.axisValue sig axis =
        some sample.value := by
    simpa [hSig] using sample.value_eq
  rw [hNone] at hSome
  cases hSome

/-- Observe the measured value of a fixed concrete Signature V1 axis. -/
def measuredAxisObservation (axis : V1Axis) :
    SignatureObservation (MeasuredAxisSignature axis) Nat where
  observe := fun sig => sig.value
  coverageAssumptions := True
  nonConclusions :=
    ∀ sig : V1Signature,
      ArchitectureSignature.ArchitectureSignatureV1.axisValue sig axis =
        none ->
        ¬ ArchitectureSignature.ArchitectureSignatureV1.axisAvailableAndZero
          sig axis

/-- Signed natural-number delta used for measured V1 axis values. -/
def signedNatAxisDelta : SignatureDelta Nat Int where
  delta source target := (target : Int) - (source : Int)
  nonConclusions := True

/-- The signed natural-number delta satisfies the selected additive law. -/
def signedNatAxisDelta_additiveLaw :
    AdditiveSignatureDeltaLaw signedNatAxisDelta where
  self_zero := by
    intro sig
    simp [SignatureDelta.between, signedNatAxisDelta]
  step_telescope := by
    intro source mid target
    simp [SignatureDelta.between, signedNatAxisDelta]
  nonConclusions := True

/--
For a selected measured V1 axis, the net sum of per-step signed deltas equals
the endpoint signed delta.

The theorem is intentionally over `MeasuredAxisSignature axis`, so states with
`axisValue = none` are not silently treated as zero-valued measurements.
-/
theorem selectedMeasuredAxis_netDelta_telescopes
    (schema : Schema) {axis : V1Axis}
    (_hSelected : schema.AxisSelected axis) :
    {X Y : MeasuredAxisSignature axis} ->
      (plan : ArchitectureEvolution (MeasuredAxisSignature axis) X Y) ->
        NetSignatureDelta
            (SignatureDeltaSequence (measuredAxisObservation axis)
              signedNatAxisDelta plan) =
          EndpointSignatureDelta (measuredAxisObservation axis)
            signedNatAxisDelta plan
  | _, _, plan =>
      netSignatureDelta_telescopes
        (measuredAxisObservation axis) signedNatAxisDelta
        signedNatAxisDelta_additiveLaw plan

/-- Endpoint delta for a measured V1 axis is the signed target-source value. -/
theorem measuredAxis_endpointDelta_eq
    {axis : V1Axis} {X Y : MeasuredAxisSignature axis}
    (plan : ArchitectureEvolution (MeasuredAxisSignature axis) X Y) :
    EndpointSignatureDelta (measuredAxisObservation axis)
        signedNatAxisDelta plan =
      (Y.value : Int) - (X.value : Int) := by
  rfl

end ArchitectureSignatureV1MeasuredAxisDelta

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
Selected damping / control schema for accepted architecture transitions.

The schema treats review, CI, type checking, policy, or another controller as a
boundary predicate on primitive transitions. It only proves consequences for
steps explicitly classified as accepted, and records rejected steps as a
separate boundary without deriving target-state guarantees from rejection
alone.
-/
structure DampingControlSchema (State : Type u) (Sig : Type v) where
  observation : SignatureObservation State Sig
  invariant : SafeRegion Sig
  accepted : {X Y : State} -> ArchitectureTransition State X Y -> Prop
  rejected : {X Y : State} -> ArchitectureTransition State X Y -> Prop
  acceptedPreservesInvariant :
    ∀ {X Y : State} (t : ArchitectureTransition State X Y),
      accepted t -> StepPreservesSafeRegion observation invariant t
  coverageAssumptions : Prop
  nonConclusions : Prop

namespace DampingControlSchema

variable {State : Type u} {Sig : Type v} {Score : Type w}

/-- The selected controller accepts this primitive transition. -/
def AcceptedStep
    (control : DampingControlSchema State Sig)
    {X Y : State} (t : ArchitectureTransition State X Y) : Prop :=
  control.accepted t

/-- The selected controller rejects this primitive transition. -/
def RejectedStep
    (control : DampingControlSchema State Sig)
    {X Y : State} (t : ArchitectureTransition State X Y) : Prop :=
  control.rejected t

/-- The control package explicitly records its non-conclusion boundary. -/
def RecordsNonConclusions
    (control : DampingControlSchema State Sig) : Prop :=
  control.nonConclusions

/-- Every primitive transition in the evolution path is accepted. -/
def AcceptedEvolution
    (control : DampingControlSchema State Sig) :
    {X Y : State} -> ArchitectureEvolution State X Y -> Prop
  | _, _, ArchitecturePath.nil _ => True
  | _, _, ArchitecturePath.cons step rest =>
      control.AcceptedStep step ∧ AcceptedEvolution control rest

/--
An accepted step preserves the selected invariant by the explicit controller
assumption.
-/
theorem acceptedStep_preserves_selectedInvariant
    (control : DampingControlSchema State Sig)
    {X Y : State} (t : ArchitectureTransition State X Y)
    (hAccepted : control.AcceptedStep t) :
    StepPreservesSafeRegion control.observation control.invariant t :=
  control.acceptedPreservesInvariant t hAccepted

/--
If every step in a finite evolution is accepted, every step preserves the
selected invariant.
-/
theorem everyStepPreservesSafeRegion_of_acceptedEvolution
    (control : DampingControlSchema State Sig) :
    {X Y : State} -> (plan : ArchitectureEvolution State X Y) ->
      control.AcceptedEvolution plan ->
        EveryStepPreservesSafeRegion
          control.observation control.invariant plan
  | _, _, ArchitecturePath.nil _, _hAccepted => trivial
  | _, _, ArchitecturePath.cons step rest, hAccepted => by
      exact
        And.intro
          (control.acceptedStep_preserves_selectedInvariant step hAccepted.1)
          (everyStepPreservesSafeRegion_of_acceptedEvolution
            control rest hAccepted.2)

/--
Accepted finite evolutions preserve the selected invariant over the observed
signature trajectory.
-/
theorem acceptedEvolution_preserves_selectedInvariant
    (control : DampingControlSchema State Sig) :
    {X Y : State} -> (plan : ArchitectureEvolution State X Y) ->
      StateInSafeRegion control.observation control.invariant X ->
      control.AcceptedEvolution plan ->
        SignatureTrajectoryInSafeRegion
          control.invariant (SignatureTrajectory control.observation plan)
  | _, _, plan, hStart, hAccepted =>
      trajectory_preserves_safeRegion
        control.observation control.invariant plan hStart
        (control.everyStepPreservesSafeRegion_of_acceptedEvolution
          plan hAccepted)

/--
Explicit damping assumption for a selected bad-axis measure.

The bad-axis order is caller supplied. This package is the only place where
nonincrease is assumed; a controller, review process, CI run, or policy label
does not imply a bad-axis decrease by itself.
-/
structure BadAxisDampingAssumption
    (control : DampingControlSchema State Sig) (Score : Type w)
    [LE Score] where
  badAxis : Sig -> Score
  selfNonincreasing :
    ∀ sig : Sig, badAxis sig ≤ badAxis sig
  transNonincreasing :
    ∀ {lower middle upper : Score},
      lower ≤ middle -> middle ≤ upper -> lower ≤ upper
  acceptedStepNonincreasing :
    ∀ {X Y : State} (t : ArchitectureTransition State X Y),
      control.AcceptedStep t ->
        badAxis (control.observation.observe Y) ≤
          badAxis (control.observation.observe X)
  nonConclusions : Prop

namespace BadAxisDampingAssumption

variable [LE Score]
variable {control : DampingControlSchema State Sig}

/-- The damping assumption explicitly records its non-conclusion boundary. -/
def RecordsNonConclusions
    (assumption : BadAxisDampingAssumption control Score) : Prop :=
  assumption.nonConclusions

end BadAxisDampingAssumption

/--
Under an explicit damping assumption, an accepted step is nonincreasing on the
selected bad-axis measure.
-/
theorem badAxis_nonincrease_of_acceptedStep [LE Score]
    (control : DampingControlSchema State Sig)
    (assumption : BadAxisDampingAssumption control Score)
    {X Y : State} (t : ArchitectureTransition State X Y)
    (hAccepted : control.AcceptedStep t) :
    assumption.badAxis (control.observation.observe Y) ≤
      assumption.badAxis (control.observation.observe X) :=
  assumption.acceptedStepNonincreasing t hAccepted

/--
Under an explicit damping assumption, an accepted finite evolution is
nonincreasing from target to source on the selected bad-axis measure.
-/
theorem badAxis_nonincrease_of_acceptedEvolution [LE Score]
    (control : DampingControlSchema State Sig)
    (assumption : BadAxisDampingAssumption control Score) :
    {X Y : State} -> (plan : ArchitectureEvolution State X Y) ->
      control.AcceptedEvolution plan ->
        assumption.badAxis (control.observation.observe Y) ≤
          assumption.badAxis (control.observation.observe X)
  | X, _, ArchitecturePath.nil _, _hAccepted => by
      exact assumption.selfNonincreasing (control.observation.observe X)
  | X, Z, ArchitecturePath.cons (Y := Y) step rest, hAccepted => by
      exact
        assumption.transNonincreasing
          (badAxis_nonincrease_of_acceptedEvolution
            control assumption rest hAccepted.2)
          (assumption.acceptedStepNonincreasing step hAccepted.1)

end DampingControlSchema

/--
Abstract force reading for an accepted finite transition sequence.

The schema is deliberately relative to a selected `DampingControlSchema`,
selected signature delta, and selected additive law. It does not mention real
GitHub PR metadata, report calibration, incidents, review cost, or PR outcome;
those remain explicit boundary propositions.
-/
structure AcceptedTransitionForceSchema
    (State : Type u) (Sig : Type v) (Delta : Type w)
    [Zero Delta] [Add Delta] where
  control : DampingControlSchema State Sig
  delta : SignatureDelta Sig Delta
  additiveLaw : AdditiveSignatureDeltaLaw delta
  acceptedTransitionBoundary : Prop
  coverageAssumptions : Prop
  prOutcomeBoundary : Prop
  incidentBoundary : Prop
  reviewCostBoundary : Prop
  githubMetadataBoundary : Prop
  reportCalibrationBoundary : Prop
  nonConclusions : Prop

namespace AcceptedTransitionForceSchema

variable {State : Type u} {Sig : Type v} {Delta : Type w}
variable [Zero Delta] [Add Delta]

/-- The selected finite evolution is accepted by the supplied controller. -/
def AcceptedSequence
    (schema : AcceptedTransitionForceSchema State Sig Delta)
    {X Y : State} (plan : ArchitectureEvolution State X Y) : Prop :=
  schema.control.AcceptedEvolution plan

/-- The per-step observed force sequence of an accepted-transition reading. -/
def ObservedForceSequence
    (schema : AcceptedTransitionForceSchema State Sig Delta)
    {X Y : State} (plan : ArchitectureEvolution State X Y) : List Delta :=
  SignatureDeltaSequence schema.control.observation schema.delta plan

/-- Net force obtained by adding the selected per-step force sequence. -/
def NetForce
    (schema : AcceptedTransitionForceSchema State Sig Delta)
    {X Y : State} (plan : ArchitectureEvolution State X Y) : Delta :=
  NetSignatureDelta (schema.ObservedForceSequence plan)

/-- Endpoint force read directly from the selected source / target signatures. -/
def EndpointForce
    (schema : AcceptedTransitionForceSchema State Sig Delta)
    {X Y : State} (plan : ArchitectureEvolution State X Y) : Delta :=
  EndpointSignatureDelta schema.control.observation schema.delta plan

/-- The schema explicitly records its accepted-transition boundary. -/
def RecordsAcceptedTransitionBoundary
    (schema : AcceptedTransitionForceSchema State Sig Delta) : Prop :=
  schema.acceptedTransitionBoundary

/-- The schema explicitly records that PR outcomes are outside the theorem. -/
def RecordsPROutcomeBoundary
    (schema : AcceptedTransitionForceSchema State Sig Delta) : Prop :=
  schema.prOutcomeBoundary

/-- The schema explicitly records that incidents are outside the theorem. -/
def RecordsIncidentBoundary
    (schema : AcceptedTransitionForceSchema State Sig Delta) : Prop :=
  schema.incidentBoundary

/-- The schema explicitly records that review cost is outside the theorem. -/
def RecordsReviewCostBoundary
    (schema : AcceptedTransitionForceSchema State Sig Delta) : Prop :=
  schema.reviewCostBoundary

/-- The schema explicitly records that GitHub metadata is outside the theorem. -/
def RecordsGitHubMetadataBoundary
    (schema : AcceptedTransitionForceSchema State Sig Delta) : Prop :=
  schema.githubMetadataBoundary

/-- The schema explicitly records that report calibration is outside the theorem. -/
def RecordsReportCalibrationBoundary
    (schema : AcceptedTransitionForceSchema State Sig Delta) : Prop :=
  schema.reportCalibrationBoundary

/-- The schema explicitly records its non-conclusion boundary. -/
def RecordsNonConclusions
    (schema : AcceptedTransitionForceSchema State Sig Delta) : Prop :=
  schema.nonConclusions

/--
For an accepted transition sequence, the net observed force equals the selected
endpoint delta under the supplied additive delta law.

The acceptedness premise bounds the interpretation as an accepted-transition
force reading; the algebraic equality itself is the endpoint telescoping law.
-/
theorem netForce_eq_endpointForce
    (schema : AcceptedTransitionForceSchema State Sig Delta)
    {X Y : State} (plan : ArchitectureEvolution State X Y)
    (_hAccepted : schema.AcceptedSequence plan) :
    schema.NetForce plan = schema.EndpointForce plan :=
  netSignatureDelta_telescopes
    schema.control.observation schema.delta schema.additiveLaw plan

/--
Accepted force reading together with selected invariant preservation.

This packages the two bounded conclusions that are valid for an accepted
sequence: the selected observed trajectory stays in the selected invariant when
the source starts there, and the net force telescopes to the endpoint delta.
-/
theorem preservesInvariant_and_netForce_eq_endpointForce
    (schema : AcceptedTransitionForceSchema State Sig Delta)
    {X Y : State} (plan : ArchitectureEvolution State X Y)
    (hStart :
      StateInSafeRegion schema.control.observation schema.control.invariant X)
    (hAccepted : schema.AcceptedSequence plan) :
    SignatureTrajectoryInSafeRegion
        schema.control.invariant
        (SignatureTrajectory schema.control.observation plan) ∧
      schema.NetForce plan = schema.EndpointForce plan :=
  ⟨schema.control.acceptedEvolution_preserves_selectedInvariant
      plan hStart hAccepted,
    schema.netForce_eq_endpointForce plan hAccepted⟩

/--
Accepted force reading together with selected bad-axis nonincrease.

Bad-axis nonincrease is not derived from the force value. It is paired with the
force endpoint theorem only under an explicit `BadAxisDampingAssumption`.
-/
theorem badAxisNonincrease_and_netForce_eq_endpointForce
    {Score : Type x} [LE Score]
    (schema : AcceptedTransitionForceSchema State Sig Delta)
    (assumption :
      DampingControlSchema.BadAxisDampingAssumption
        schema.control Score)
    {X Y : State} (plan : ArchitectureEvolution State X Y)
    (hAccepted : schema.AcceptedSequence plan) :
    assumption.badAxis (schema.control.observation.observe Y) ≤
        assumption.badAxis (schema.control.observation.observe X) ∧
      schema.NetForce plan = schema.EndpointForce plan :=
  ⟨DampingControlSchema.badAxis_nonincrease_of_acceptedEvolution
      schema.control assumption plan hAccepted,
    schema.netForce_eq_endpointForce plan hAccepted⟩

end AcceptedTransitionForceSchema

/--
Bounded semantics connecting operation identifiers to primitive architecture
transitions.

The relation is intentionally explicit: an operation identifier, tag, proposal,
or script entry does not produce preservation, acceptance, or nonincrease by
itself. Later tooling can instantiate this relation with a proof-carrying
transition package.
-/
structure OperationTransitionSemantics
    (State : Type u) (OperationId : Type w) where
  realizes :
    OperationId -> {X Y : State} -> ArchitectureTransition State X Y -> Prop
  coverageAssumptions : Prop
  nonConclusions : Prop

namespace OperationTransitionSemantics

variable {State : Type u} {Sig : Type v} {OperationId : Type w}

/-- The selected operation identifier realizes this primitive transition. -/
def Realizes
    (sem : OperationTransitionSemantics State OperationId)
    (op : OperationId) {X Y : State}
    (t : ArchitectureTransition State X Y) : Prop :=
  sem.realizes op t

/-- The semantics package explicitly records its non-conclusion boundary. -/
def RecordsNonConclusions
    (sem : OperationTransitionSemantics State OperationId) : Prop :=
  sem.nonConclusions

/--
The selected operation identifier preserves the selected safe region whenever
it realizes a primitive transition.
-/
def OperationPreservesSafeRegion
    (sem : OperationTransitionSemantics State OperationId)
    (O : SignatureObservation State Sig) (R : SafeRegion Sig)
    (op : OperationId) : Prop :=
  ∀ {X Y : State} (t : ArchitectureTransition State X Y),
    sem.Realizes op t -> StepPreservesSafeRegion O R t

/--
Every operation in a selected operation family preserves the selected safe
region, relative to the supplied transition semantics.
-/
def OperationFamilyPreservesSafeRegion
    (sem : OperationTransitionSemantics State OperationId)
    (O : SignatureObservation State Sig) (R : SafeRegion Sig)
    (operationFamily : OperationId -> Prop) : Prop :=
  ∀ op, operationFamily op -> sem.OperationPreservesSafeRegion O R op

end OperationTransitionSemantics

/--
A bounded operation script with an explicit selected operation family.

`operationsInFamily` only says that the listed operation identifiers are in the
selected family. It does not assert that the family preserves any invariant;
that remains a separate theorem assumption.
-/
structure BoundedOperationScript (OperationId : Type w) where
  operations : List OperationId
  operationFamily : OperationId -> Prop
  operationsInFamily : ∀ op, op ∈ operations -> operationFamily op
  coverageAssumptions : Prop
  nonConclusions : Prop

namespace BoundedOperationScript

variable {State : Type u} {Sig : Type v} {OperationId : Type w}
variable {Score : Type x}

/-- The script package explicitly records its non-conclusion boundary. -/
def RecordsNonConclusions (script : BoundedOperationScript OperationId) :
    Prop :=
  script.nonConclusions

/--
The selected operation list realizes an endpoint-indexed architecture evolution.

The relation requires one operation identifier per primitive transition. A
length mismatch is false, keeping bounded script semantics separate from any
total interpreter or proposal-completeness claim.
-/
def ScriptRealizesEvolution
    (sem : OperationTransitionSemantics State OperationId) :
    List OperationId -> {X Y : State} -> ArchitectureEvolution State X Y -> Prop
  | [], _, _, ArchitecturePath.nil _ => True
  | [], _, _, ArchitecturePath.cons _step _rest => False
  | _op :: _ops, _, _, ArchitecturePath.nil _ => False
  | op :: ops, _, _, ArchitecturePath.cons step rest =>
      sem.Realizes op step ∧ ScriptRealizesEvolution sem ops rest

/-- This bounded script realizes the selected architecture evolution. -/
def RealizesEvolution
    (script : BoundedOperationScript OperationId)
    (sem : OperationTransitionSemantics State OperationId)
    {X Y : State} (plan : ArchitectureEvolution State X Y) : Prop :=
  ScriptRealizesEvolution sem script.operations plan

/--
Every step in a realized operation script is accepted by the selected control
schema.
-/
def EveryScriptStepAccepted
    (control : DampingControlSchema State Sig)
    (sem : OperationTransitionSemantics State OperationId) :
    List OperationId -> {X Y : State} -> ArchitectureEvolution State X Y -> Prop
  | [], _, _, ArchitecturePath.nil _ => True
  | [], _, _, ArchitecturePath.cons _step _rest => False
  | _op :: _ops, _, _, ArchitecturePath.nil _ => False
  | op :: ops, _, _, ArchitecturePath.cons step rest =>
      sem.Realizes op step ∧ control.AcceptedStep step ∧
        EveryScriptStepAccepted control sem ops rest

/-- This bounded script is realized as accepted steps in the selected plan. -/
def AcceptedEvolution
    (script : BoundedOperationScript OperationId)
    (control : DampingControlSchema State Sig)
    (sem : OperationTransitionSemantics State OperationId)
    {X Y : State} (plan : ArchitectureEvolution State X Y) : Prop :=
  EveryScriptStepAccepted control sem script.operations plan

/--
If each realized operation in a script preserves the selected safe region, each
primitive transition in the realized plan preserves that safe region.
-/
theorem everyStepPreservesSafeRegion_of_scriptRealizes
    (sem : OperationTransitionSemantics State OperationId)
    (O : SignatureObservation State Sig) (R : SafeRegion Sig) :
    (operations : List OperationId) ->
      {X Y : State} -> (plan : ArchitectureEvolution State X Y) ->
      ScriptRealizesEvolution sem operations plan ->
      (∀ op, op ∈ operations -> sem.OperationPreservesSafeRegion O R op) ->
        EveryStepPreservesSafeRegion O R plan
  | [], _, _, ArchitecturePath.nil _, _hRealizes, _hOps => trivial
  | [], _, _, ArchitecturePath.cons _step _rest, hRealizes, _hOps =>
      False.elim hRealizes
  | _op :: _ops, _, _, ArchitecturePath.nil _, hRealizes, _hOps =>
      False.elim hRealizes
  | op :: ops, _, _, ArchitecturePath.cons step rest, hRealizes, hOps => by
      have hStep : StepPreservesSafeRegion O R step :=
        hOps op (by simp) step hRealizes.1
      have hOpsRest :
          ∀ op', op' ∈ ops -> sem.OperationPreservesSafeRegion O R op' := by
        intro op' hMem
        exact hOps op' (by simp [hMem])
      exact
        And.intro hStep
          (everyStepPreservesSafeRegion_of_scriptRealizes
            sem O R ops rest hRealizes.2 hOpsRest)

/--
If the selected operation family preserves the safe region and the bounded
script only contains family members, then the realized plan preserves the safe
region step-by-step.
-/
theorem everyStepPreservesSafeRegion_of_scriptFamily
    (sem : OperationTransitionSemantics State OperationId)
    (O : SignatureObservation State Sig) (R : SafeRegion Sig)
    (script : BoundedOperationScript OperationId)
    {X Y : State} (plan : ArchitectureEvolution State X Y)
    (hRealizes : script.RealizesEvolution sem plan)
    (hFamily :
      sem.OperationFamilyPreservesSafeRegion O R script.operationFamily) :
    EveryStepPreservesSafeRegion O R plan :=
  everyStepPreservesSafeRegion_of_scriptRealizes
    sem O R script.operations plan hRealizes
    (by
      intro op hMem
      exact hFamily op (script.operationsInFamily op hMem))

/--
A bounded operation script preserves the selected observed safe region along
the whole signature trajectory, provided preservation is supplied for the
selected operation family.
-/
theorem script_preserves_safeRegion
    (sem : OperationTransitionSemantics State OperationId)
    (O : SignatureObservation State Sig) (R : SafeRegion Sig)
    (script : BoundedOperationScript OperationId)
    {X Y : State} (plan : ArchitectureEvolution State X Y)
    (hStart : StateInSafeRegion O R X)
    (hRealizes : script.RealizesEvolution sem plan)
    (hFamily :
      sem.OperationFamilyPreservesSafeRegion O R script.operationFamily) :
    SignatureTrajectoryInSafeRegion R (SignatureTrajectory O plan) :=
  trajectory_preserves_safeRegion O R plan hStart
    (everyStepPreservesSafeRegion_of_scriptFamily
      sem O R script plan hRealizes hFamily)

/--
An accepted operation script induces an accepted finite architecture evolution.
-/
theorem acceptedEvolution_of_scriptAccepted
    (control : DampingControlSchema State Sig)
    (sem : OperationTransitionSemantics State OperationId) :
    (operations : List OperationId) ->
      {X Y : State} -> (plan : ArchitectureEvolution State X Y) ->
      EveryScriptStepAccepted control sem operations plan ->
        control.AcceptedEvolution plan
  | [], _, _, ArchitecturePath.nil _, _hAccepted => trivial
  | [], _, _, ArchitecturePath.cons _step _rest, hAccepted =>
      False.elim hAccepted
  | _op :: _ops, _, _, ArchitecturePath.nil _, hAccepted =>
      False.elim hAccepted
  | _op :: ops, _, _, ArchitecturePath.cons _step rest, hAccepted => by
      exact
        And.intro hAccepted.2.1
          (acceptedEvolution_of_scriptAccepted
            control sem ops rest hAccepted.2.2)

/--
Under an explicit bad-axis damping assumption, an accepted bounded operation
script is nonincreasing from target to source on the selected bad-axis measure.
-/
theorem badAxis_nonincrease_of_acceptedScript [LE Score]
    (control : DampingControlSchema State Sig)
    (assumption : DampingControlSchema.BadAxisDampingAssumption control Score)
    (sem : OperationTransitionSemantics State OperationId)
    (script : BoundedOperationScript OperationId)
    {X Y : State} (plan : ArchitectureEvolution State X Y)
    (hAccepted : script.AcceptedEvolution control sem plan) :
    assumption.badAxis (control.observation.observe Y) ≤
      assumption.badAxis (control.observation.observe X) :=
  DampingControlSchema.badAxis_nonincrease_of_acceptedEvolution
    control assumption plan
    (acceptedEvolution_of_scriptAccepted
      control sem script.operations plan hAccepted)

end BoundedOperationScript

/--
A finite support kernel for operation selection.

The kernel records only the finite support of candidate operation identifiers
at each source state. Weight sources, normalization, proposal completeness, and
AI patch distributions remain boundary propositions and non-conclusions rather
than probability-measure theorems.
-/
structure FiniteOperationKernel
    (State : Type u) (OperationId : Type w) where
  support : State -> List OperationId
  coverageAssumptions : Prop
  weightSourceBoundary : Prop
  normalizationBoundary : Prop
  nonConclusions : Prop

namespace FiniteOperationKernel

variable {State : Type u} {Sig : Type v} {OperationId : Type w}

/-- The selected operation identifier is in the finite support at this state. -/
def Supports
    (kernel : FiniteOperationKernel State OperationId)
    (X : State) (op : OperationId) : Prop :=
  op ∈ kernel.support X

/-- The kernel explicitly records its weight-source boundary. -/
def RecordsWeightSourceBoundary
    (kernel : FiniteOperationKernel State OperationId) : Prop :=
  kernel.weightSourceBoundary

/-- The kernel explicitly records its normalization boundary. -/
def RecordsNormalizationBoundary
    (kernel : FiniteOperationKernel State OperationId) : Prop :=
  kernel.normalizationBoundary

/-- The kernel explicitly records its non-conclusion boundary. -/
def RecordsNonConclusions
    (kernel : FiniteOperationKernel State OperationId) : Prop :=
  kernel.nonConclusions

/--
Every operation in the selected finite support preserves the selected safe
region whenever it realizes a primitive transition.
-/
def SupportOperationsPreserveSafeRegion
    (kernel : FiniteOperationKernel State OperationId)
    (sem : OperationTransitionSemantics State OperationId)
    (O : SignatureObservation State Sig) (R : SafeRegion Sig) : Prop :=
  ∀ {X : State} (op : OperationId),
    kernel.Supports X op -> sem.OperationPreservesSafeRegion O R op

/--
The selected support operation realizes this primitive transition from its
source state.
-/
def SupportStep
    (kernel : FiniteOperationKernel State OperationId)
    (sem : OperationTransitionSemantics State OperationId)
    (op : OperationId) {X Y : State}
    (t : ArchitectureTransition State X Y) : Prop :=
  kernel.Supports X op ∧ sem.Realizes op t

/--
If every support operation preserves the selected safe region, then any
realized step selected from the support preserves it.
-/
theorem supportStep_preserves_safeRegion
    (kernel : FiniteOperationKernel State OperationId)
    (sem : OperationTransitionSemantics State OperationId)
    (O : SignatureObservation State Sig) (R : SafeRegion Sig)
    (op : OperationId) {X Y : State}
    (t : ArchitectureTransition State X Y)
    (hStep : kernel.SupportStep sem op t)
    (hPreserves : kernel.SupportOperationsPreserveSafeRegion sem O R) :
    StepPreservesSafeRegion O R t :=
  hPreserves op hStep.1 t hStep.2

/--
The operation list uses only operations in the selected finite support along
the endpoint-indexed evolution. A length mismatch is false, matching bounded
script realization semantics.
-/
def ScriptUsesSupport
    (kernel : FiniteOperationKernel State OperationId) :
    List OperationId -> {X Y : State} -> ArchitectureEvolution State X Y -> Prop
  | [], _, _, ArchitecturePath.nil _ => True
  | [], _, _, ArchitecturePath.cons _step _rest => False
  | _op :: _ops, _, _, ArchitecturePath.nil _ => False
  | op :: ops, X, _, ArchitecturePath.cons _step rest =>
      kernel.Supports X op ∧ ScriptUsesSupport kernel ops rest

/--
If a realized operation list uses only finite-support operations and all
support operations preserve the safe region, then every realized transition
preserves that region.
-/
theorem everyStepPreservesSafeRegion_of_scriptUsesSupport
    (kernel : FiniteOperationKernel State OperationId)
    (sem : OperationTransitionSemantics State OperationId)
    (O : SignatureObservation State Sig) (R : SafeRegion Sig) :
    (operations : List OperationId) ->
      {X Y : State} -> (plan : ArchitectureEvolution State X Y) ->
      BoundedOperationScript.ScriptRealizesEvolution sem operations plan ->
      kernel.ScriptUsesSupport operations plan ->
      kernel.SupportOperationsPreserveSafeRegion sem O R ->
        EveryStepPreservesSafeRegion O R plan
  | [], _, _, ArchitecturePath.nil _, _hRealizes, _hSupport, _hPreserves =>
      trivial
  | [], _, _, ArchitecturePath.cons _step _rest, hRealizes, _hSupport,
      _hPreserves =>
      False.elim hRealizes
  | _op :: _ops, _, _, ArchitecturePath.nil _, hRealizes, _hSupport,
      _hPreserves =>
      False.elim hRealizes
  | op :: ops, _, _, ArchitecturePath.cons step rest, hRealizes, hSupport,
      hPreserves => by
      have hStep : StepPreservesSafeRegion O R step :=
        supportStep_preserves_safeRegion
          kernel sem O R op step ⟨hSupport.1, hRealizes.1⟩ hPreserves
      exact
        And.intro hStep
          (everyStepPreservesSafeRegion_of_scriptUsesSupport
            kernel sem O R ops rest hRealizes.2 hSupport.2 hPreserves)

/--
A bounded sampled script preserves the selected observed safe region when the
script realizes the plan, uses only operations from the finite support at each
source state, and all support operations preserve that region.
-/
theorem boundedSampledScript_preserves_safeRegion
    (kernel : FiniteOperationKernel State OperationId)
    (sem : OperationTransitionSemantics State OperationId)
    (O : SignatureObservation State Sig) (R : SafeRegion Sig)
    (script : BoundedOperationScript OperationId)
    {X Y : State} (plan : ArchitectureEvolution State X Y)
    (hStart : StateInSafeRegion O R X)
    (hRealizes : script.RealizesEvolution sem plan)
    (hSupport : kernel.ScriptUsesSupport script.operations plan)
    (hPreserves : kernel.SupportOperationsPreserveSafeRegion sem O R) :
    SignatureTrajectoryInSafeRegion R (SignatureTrajectory O plan) :=
  trajectory_preserves_safeRegion O R plan hStart
    (everyStepPreservesSafeRegion_of_scriptUsesSupport
      kernel sem O R script.operations plan hRealizes hSupport hPreserves)

end FiniteOperationKernel

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

variable {Sig : Type v} {Score : Type w}

/-- The selected suffix of the finite trajectory that stays in the region. -/
def observedSuffix (candidate : AttractorCandidate Sig) : List Sig :=
  candidate.trajectory.drop candidate.entryIndex

/-- The candidate region is recurrent relative to the selected observed suffix. -/
def RecurrentRegion (candidate : AttractorCandidate Sig) : Prop :=
  RecurrentSignatureRegion candidate.observedSuffix candidate.region

/--
The selected observed suffix is safe with respect to a caller-supplied safe
region.
-/
def IsSafeAttractor
    (candidate : AttractorCandidate Sig) (safeRegion : SafeRegion Sig) :
    Prop :=
  SignatureTrajectoryInSafeRegion safeRegion candidate.observedSuffix

/--
The selected observed suffix contains a signature that is bad according to a
caller-supplied bad-axis measurement and bad-score predicate.
-/
def IsBadAttractor
    (candidate : AttractorCandidate Sig)
    (badAxis : Sig -> Score) (isBad : Score -> Prop) : Prop :=
  ∃ sig, sig ∈ candidate.observedSuffix ∧ isBad (badAxis sig)

/-- The attractor candidate explicitly records its non-conclusion boundary. -/
def RecordsNonConclusions (candidate : AttractorCandidate Sig) : Prop :=
  candidate.nonConclusions

/-- The selected observed suffix stays inside the candidate region. -/
theorem observedSuffix_in_region (candidate : AttractorCandidate Sig) :
    SignatureTrajectoryInSafeRegion
      candidate.region candidate.observedSuffix := by
  intro sig hMem
  exact candidate.staysAfterEntry sig hMem

/-- The candidate is safe with respect to its own selected region. -/
theorem isSafeAttractor_region (candidate : AttractorCandidate Sig) :
    candidate.IsSafeAttractor candidate.region :=
  candidate.observedSuffix_in_region

/--
If the candidate region is included in another selected safe region, the
candidate suffix is safe for that region as well.
-/
theorem isSafeAttractor_of_region_subset
    (candidate : AttractorCandidate Sig) (safeRegion : SafeRegion Sig)
    (hSubset : ∀ sig, candidate.region sig -> safeRegion sig) :
    candidate.IsSafeAttractor safeRegion := by
  intro sig hMem
  exact hSubset sig (candidate.observedSuffix_in_region sig hMem)

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
The selected initial states reach a caller-supplied safe suffix predicate for
the candidate attractor.
-/
def SelectedInitialStatesReachSafeSuffix
    (candidate : BasinCandidate State Sig Op) (safeRegion : SafeRegion Sig) :
    Prop :=
  candidate.attractor.IsSafeAttractor safeRegion ∧
    candidate.CoversSelectedInitialStates

/--
The finite initial-state list is covered by the caller-supplied reachability
predicate.
-/
theorem coversSelectedInitialStates
    (candidate : BasinCandidate State Sig Op) :
    candidate.CoversSelectedInitialStates :=
  candidate.everyInitialReaches

/--
If the attractor suffix is safe for a selected region, the basin package shows
that every selected initial state reaches that safe suffix.
-/
theorem selectedInitialStates_reach_safeSuffix_of_safeAttractor
    (candidate : BasinCandidate State Sig Op) (safeRegion : SafeRegion Sig)
    (hSafe : candidate.attractor.IsSafeAttractor safeRegion) :
    candidate.SelectedInitialStatesReachSafeSuffix safeRegion :=
  ⟨hSafe, candidate.coversSelectedInitialStates⟩

/--
Every selected initial state reaches the attractor suffix that is safe for the
candidate's own selected region.
-/
theorem selectedInitialStates_reach_attractorRegionSuffix
    (candidate : BasinCandidate State Sig Op) :
    candidate.SelectedInitialStatesReachSafeSuffix candidate.attractor.region :=
  candidate.selectedInitialStates_reach_safeSuffix_of_safeAttractor
    candidate.attractor.region candidate.attractor.isSafeAttractor_region

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
An explicit finite universe for deterministic signature dynamics states.

The list is proof-carrying. Closure under a selected self-map is named
separately as `FiniteStateUniverse.StepClosed`, even though full coverage can
discharge it.
-/
structure FiniteStateUniverse (State : Type u) where
  states : List State
  nodup : states.Nodup
  covers : ∀ X : State, X ∈ states

namespace FiniteStateUniverse

variable {State : Type u}

/-- The selected self-map stays inside the listed finite universe. -/
def StepClosed (U : FiniteStateUniverse State) (step : State -> State) : Prop :=
  ∀ X : State, X ∈ U.states -> step X ∈ U.states

/--
For a full finite state universe, self-map closure follows from coverage.

It remains an explicit theorem so later theorem statements can name the closure
precondition without deriving it silently from the transition function.
-/
theorem stepClosed_of_covers (U : FiniteStateUniverse State)
    (step : State -> State) : U.StepClosed step := by
  intro X _hMem
  exact U.covers (step X)

/-- Build a full finite state universe from a duplicate-free covering list. -/
def full (states : List State) (nodup : states.Nodup)
    (covers : ∀ X : State, X ∈ states) :
    FiniteStateUniverse State where
  states := states
  nodup := nodup
  covers := covers

/-- The explicit universe induces a `Fintype` instance for finite dynamics. -/
noncomputable def fintype [DecidableEq State]
    (U : FiniteStateUniverse State) : Fintype State where
  elems := U.states.toFinset
  complete := by
    intro X
    simpa using U.covers X

end FiniteStateUniverse

/-- Iterating a self-map over an added horizon composes the two iterates. -/
theorem iterateSelfMap_add
    (step : State -> State) (m n : Nat) (X : State) :
    IterateSelfMap step (m + n) X =
      IterateSelfMap step m (IterateSelfMap step n X) := by
  induction n generalizing X with
  | zero =>
      simp [IterateSelfMap]
  | succ n ih =>
      simp [IterateSelfMap, ih]

/--
Statement for deterministic finite dynamics.

The theorem below proves this under finite-state assumptions. Keeping it as a
predicate prevents the attractor candidate schema from silently claiming global
convergence.
-/
def DeterministicSelfMapEventuallyPeriodic
    (step : State -> State) (start : State) : Prop :=
  ∃ preperiod period : Nat,
    0 < period ∧
      ∀ n, preperiod ≤ n ->
        IterateSelfMap step (n + period) start =
          IterateSelfMap step n start

/--
Once an orbit revisits a previous state, the suffix from that point is periodic
with the selected positive period.
-/
theorem deterministicSelfMap_periodic_from_repetition
    (step : State -> State) (start : State)
    {preperiod period : Nat} (hCycle : 0 < period)
    (hRepeat :
      IterateSelfMap step (preperiod + period) start =
        IterateSelfMap step preperiod start) :
    DeterministicSelfMapEventuallyPeriodic step start := by
  refine ⟨preperiod, period, hCycle, ?_⟩
  intro n hn
  let offset := n - preperiod
  have hn_eq : n = preperiod + offset := by
    omega
  rw [hn_eq]
  have hReassoc :
      preperiod + offset + period = offset + (preperiod + period) := by
    omega
  calc
    IterateSelfMap step (preperiod + offset + period) start =
        IterateSelfMap step (offset + (preperiod + period)) start := by
          rw [hReassoc]
    _ = IterateSelfMap step offset
          (IterateSelfMap step (preperiod + period) start) := by
          rw [iterateSelfMap_add]
    _ = IterateSelfMap step offset (IterateSelfMap step preperiod start) := by
          rw [hRepeat]
    _ = IterateSelfMap step (offset + preperiod) start := by
          rw [iterateSelfMap_add]
    _ = IterateSelfMap step (preperiod + offset) start := by
          rw [Nat.add_comm offset preperiod]

/--
Finite deterministic self-map dynamics are eventually periodic.

This is only a finite-state orbit theorem. It does not assert a global
attractor, stochastic convergence, empirical AI patch behavior, or completeness
of a real codebase extraction universe.
-/
theorem deterministicSelfMapEventuallyPeriodic_of_finite
    [Finite State] (step : State -> State) (start : State) :
    DeterministicSelfMapEventuallyPeriodic step start := by
  obtain ⟨i, j, hNe, hEq⟩ :=
    Finite.exists_ne_map_eq_of_infinite
      (fun n : Nat => IterateSelfMap step n start)
  rcases lt_or_gt_of_ne hNe with hlt | hgt
  · have hPeriod : 0 < j - i := by
      omega
    have hRepeat :
        IterateSelfMap step (i + (j - i)) start =
          IterateSelfMap step i start := by
      have hSum : i + (j - i) = j := by
        omega
      simpa [hSum] using hEq.symm
    exact deterministicSelfMap_periodic_from_repetition
      step start hPeriod hRepeat
  · have hPeriod : 0 < i - j := by
      omega
    have hRepeat :
        IterateSelfMap step (j + (i - j)) start =
          IterateSelfMap step j start := by
      have hSum : j + (i - j) = i := by
        omega
      simpa [hSum] using hEq
    exact deterministicSelfMap_periodic_from_repetition
      step start hPeriod hRepeat

/--
Explicit-universe version of finite deterministic eventual periodicity.

The universe supplies a duplicate-free covering list and an explicit closure
predicate for the selected self-map. The conclusion remains only the bounded
eventual-periodicity predicate.
-/
theorem deterministicSelfMapEventuallyPeriodic_of_finiteUniverse
    [DecidableEq State] (U : FiniteStateUniverse State)
    (step : State -> State) (_hClosed : U.StepClosed step) (start : State) :
    DeterministicSelfMapEventuallyPeriodic step start := by
  letI : Fintype State := U.fintype
  exact deterministicSelfMapEventuallyPeriodic_of_finite step start

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
