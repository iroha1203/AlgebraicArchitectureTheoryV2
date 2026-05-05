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

end Formal.Arch
