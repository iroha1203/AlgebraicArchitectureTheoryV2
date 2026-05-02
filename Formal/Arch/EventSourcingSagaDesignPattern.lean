import Formal.Arch.StateTransitionDesignPattern

namespace Formal.Arch

universe u v w

/-- Event sequences are the finite histories used by Event Sourcing packages. -/
abbrev EventSequence (Event : Type v) := List Event

/-- Empty event history. -/
def eventSequenceUnit {Event : Type v} : EventSequence Event :=
  []

/-- Event history composition. -/
def eventSequenceAppend {Event : Type v}
    (xs ys : EventSequence Event) : EventSequence Event :=
  xs ++ ys

/-- The selected event-sequence composition laws. -/
def EventSequenceMonoidLawful (Event : Type v) : Prop :=
  (∀ xs : EventSequence Event, eventSequenceAppend eventSequenceUnit xs = xs) ∧
  (∀ xs : EventSequence Event, eventSequenceAppend xs eventSequenceUnit = xs) ∧
  (∀ xs ys zs : EventSequence Event,
    eventSequenceAppend (eventSequenceAppend xs ys) zs =
      eventSequenceAppend xs (eventSequenceAppend ys zs))

/-- Finite event histories form the selected monoid used by Event Sourcing. -/
theorem eventSequenceMonoidLawful (Event : Type v) :
    EventSequenceMonoidLawful Event := by
  constructor
  · intro xs
    rfl
  · constructor
    · intro xs
      exact List.append_nil xs
    · intro xs ys zs
      exact List.append_assoc xs ys zs

/-- Empty selected replay cases are lawful by vacuity. -/
theorem stateReplayLawful_nil
    {State : Type u} {Event : Type v} {Obs : Type w}
    (sem : Semantics (StateTransitionExpr State Event) Obs) :
    StateReplayLawful sem ([] : List (StateReplayCase State Event)) := by
  intro d hRequired
  simp [RequiredDiagramsByList, RequiredByList, stateReplayDiagrams] at hRequired

/-- Empty selected roundtrip cases are lawful by vacuity. -/
theorem stateRoundtripLawful_nil
    {State : Type u} {Event : Type v} {Obs : Type w}
    (sem : Semantics (StateTransitionExpr State Event) Obs) :
    StateRoundtripLawful sem ([] : List (StateRoundtripCase State Event)) := by
  intro d hRequired
  simp [RequiredDiagramsByList, RequiredByList, stateRoundtripDiagrams] at hRequired

/-- Empty selected compensation cases are lawful by vacuity. -/
theorem stateCompensationLawful_nil
    {State : Type u} {Event : Type v} {Obs : Type w}
    (sem : Semantics (StateTransitionExpr State Event) Obs) :
    StateCompensationLawful sem ([] : List (StateCompensationCase State Event)) := by
  intro d hRequired
  simp [RequiredDiagramsByList, RequiredByList, stateCompensationDiagrams] at hRequired

/-- One selected projection law case for Event Sourcing. -/
structure StateProjectionCase (State : Type u) (Event : Type v) : Type (max u v) where
  start : State
  events : EventSequence Event

/--
Projection law for selected Event Sourcing cases.

The projection exposed by the carrier must agree with the observation obtained
by replaying the same event sequence in the selected semantics.
-/
def StateProjectionLawful {State : Type u} {Event : Type v} {Obs : Type w}
    (carrier : StateTransitionCarrier State Event Obs)
    (cases : List (StateProjectionCase State Event)) : Prop :=
  ∀ c, c ∈ cases ->
    carrier.project c.start c.events =
      carrier.sem.eval (StateTransitionExpr.replay c.start c.events)

/-- Selected Event Sourcing state: carrier plus replay and projection cases. -/
structure EventSourcingPatternState (State : Type u) (Event : Type v)
    (Obs : Type w) where
  carrier : StateTransitionCarrier State Event Obs
  replayCases : List (StateReplayCase State Event)
  projectionCases : List (StateProjectionCase State Event)

/-- Event Sourcing replay and projection law family. -/
def EventSourcingLawFamilyLawful
    {State : Type u} {Event : Type v} {Obs : Type w}
    (state : EventSourcingPatternState State Event Obs) : Prop :=
  StateReplayLawful state.carrier.sem state.replayCases ∧
  StateProjectionLawful state.carrier state.projectionCases

/--
Proof-carrying Event Sourcing operation.

The operation claims only target-side replay and projection lawfulness for the
selected finite cases.
-/
structure EventSourcingOperation (State : Type u) (Event : Type v)
    (Obs : Type w) where
  source : EventSourcingPatternState State Event Obs
  target : EventSourcingPatternState State Event Obs
  replayLaw : StateReplayLawful target.carrier.sem target.replayCases
  projectionLaw : StateProjectionLawful target.carrier target.projectionCases

/-- View an Event Sourcing state as a generic state-transition pattern state. -/
def eventSourcingPatternState_toStateTransitionPatternState
    {State : Type u} {Event : Type v} {Obs : Type w}
    (state : EventSourcingPatternState State Event Obs) :
    StateTransitionPatternState State Event Obs where
  carrier := state.carrier
  replayCases := state.replayCases
  roundtripCases := []
  compensationCases := []

/-- View an Event Sourcing operation as a generic state-transition operation. -/
def eventSourcingOperation_toStateTransitionOperation
    {State : Type u} {Event : Type v} {Obs : Type w}
    (op : EventSourcingOperation State Event Obs) :
    StateTransitionOperation State Event Obs where
  source := eventSourcingPatternState_toStateTransitionPatternState op.source
  target := eventSourcingPatternState_toStateTransitionPatternState op.target
  lawFamily :=
    ⟨op.replayLaw, stateRoundtripLawful_nil op.target.carrier.sem,
      stateCompensationLawful_nil op.target.carrier.sem⟩

/--
The generic state-transition invariant closure applies to the Event Sourcing
operation viewed through the state-transition carrier.
-/
theorem eventSourcingOperation_stateTransitionClosure
    {State : Type u} {Event : Type v} {Obs : Type w}
    (op : EventSourcingOperation State Event Obs) :
    Ops stateTransitionOperationSource stateTransitionOperationTarget
      stateTransitionInvariantHolds stateTransitionInvariantFamily
      (eventSourcingOperation_toStateTransitionOperation op) :=
  stateTransitionOperation_preserves_stateTransitionInvariant
    (eventSourcingOperation_toStateTransitionOperation op)

/-- Source map for Event Sourcing operations. -/
def eventSourcingOperationSource
    {State : Type u} {Event : Type v} {Obs : Type w}
    (op : EventSourcingOperation State Event Obs) :
    EventSourcingPatternState State Event Obs :=
  op.source

/-- Target map for Event Sourcing operations. -/
def eventSourcingOperationTarget
    {State : Type u} {Event : Type v} {Obs : Type w}
    (op : EventSourcingOperation State Event Obs) :
    EventSourcingPatternState State Event Obs :=
  op.target

/-- Selected Event Sourcing invariant axes. -/
inductive EventSourcingInvariant where
  | eventSequenceMonoid
  | replayLawful
  | projectionLawful
  | lawFamilyLawful

/-- Interpretation of Event Sourcing invariants on a selected state. -/
def eventSourcingInvariantHolds
    {State : Type u} {Event : Type v} {Obs : Type w} :
    EventSourcingInvariant ->
      EventSourcingPatternState State Event Obs -> Prop
  | EventSourcingInvariant.eventSequenceMonoid, _state =>
      EventSequenceMonoidLawful Event
  | EventSourcingInvariant.replayLawful, state =>
      StateReplayLawful state.carrier.sem state.replayCases
  | EventSourcingInvariant.projectionLawful, state =>
      StateProjectionLawful state.carrier state.projectionCases
  | EventSourcingInvariant.lawFamilyLawful, state =>
      EventSourcingLawFamilyLawful state

/-- The representative Event Sourcing invariant family. -/
def eventSourcingInvariantFamily (_ : EventSourcingInvariant) : Prop :=
  True

/-- The representative Event Sourcing operation family. -/
def eventSourcingOperationFamily
    {State : Type u} {Event : Type v} {Obs : Type w}
    (_op : EventSourcingOperation State Event Obs) : Prop :=
  True

/-- A proof-carrying Event Sourcing operation preserves replay lawfulness. -/
theorem eventSourcingOperation_preserves_replayLawful
    {State : Type u} {Event : Type v} {Obs : Type w}
    (op : EventSourcingOperation State Event Obs) :
    StateReplayLawful op.target.carrier.sem op.target.replayCases :=
  op.replayLaw

/-- A proof-carrying Event Sourcing operation preserves projection lawfulness. -/
theorem eventSourcingOperation_preserves_projectionLawful
    {State : Type u} {Event : Type v} {Obs : Type w}
    (op : EventSourcingOperation State Event Obs) :
    StateProjectionLawful op.target.carrier op.target.projectionCases :=
  op.projectionLaw

/-- A proof-carrying Event Sourcing operation preserves its selected law family. -/
theorem eventSourcingOperation_preserves_lawFamilyLawful
    {State : Type u} {Event : Type v} {Obs : Type w}
    (op : EventSourcingOperation State Event Obs) :
    EventSourcingLawFamilyLawful op.target :=
  ⟨op.replayLaw, op.projectionLaw⟩

/-- Event Sourcing proof-carrying operations preserve every selected invariant. -/
theorem eventSourcingOperation_preserves_eventSourcingInvariant
    {State : Type u} {Event : Type v} {Obs : Type w}
    (op : EventSourcingOperation State Event Obs) :
    Ops eventSourcingOperationSource eventSourcingOperationTarget
      eventSourcingInvariantHolds eventSourcingInvariantFamily op := by
  intro invariant _hInvariant _hSource
  cases invariant
  · exact eventSequenceMonoidLawful Event
  · exact eventSourcingOperation_preserves_replayLawful op
  · exact eventSourcingOperation_preserves_projectionLawful op
  · exact eventSourcingOperation_preserves_lawFamilyLawful op

/-- The Event Sourcing operation family is contained in `Ops(S)`. -/
theorem eventSourcingOperationFamily_subset_ops
    {State : Type u} {Event : Type v} {Obs : Type w} :
    PredicateSubset
      (eventSourcingOperationFamily :
        EventSourcingOperation State Event Obs -> Prop)
      (Ops eventSourcingOperationSource eventSourcingOperationTarget
        eventSourcingInvariantHolds eventSourcingInvariantFamily) := by
  intro op _hOp
  exact eventSourcingOperation_preserves_eventSourcingInvariant op

/-- Event Sourcing selected invariants are preserved by the operation family. -/
theorem eventSourcingInvariantFamily_subset_inv
    {State : Type u} {Event : Type v} {Obs : Type w} :
    PredicateSubset eventSourcingInvariantFamily
      (Inv
        (eventSourcingOperationSource :
          EventSourcingOperation State Event Obs ->
            EventSourcingPatternState State Event Obs)
        eventSourcingOperationTarget eventSourcingInvariantHolds
        eventSourcingOperationFamily) := by
  intro invariant _hInvariant op _hOp
  exact eventSourcingOperation_preserves_eventSourcingInvariant
    op invariant trivial

/-- Non-conclusion clauses for the Event Sourcing theorem package. -/
inductive EventSourcingNonConclusionClause where
  | extractorCompleteness
  | eventLogCompleteness
  | projectionCompleteness
  | operationalCostImprovement

/-- Event Sourcing non-conclusion clauses are recorded. -/
def EventSourcingNonConclusion : Prop :=
  ∀ _clause : EventSourcingNonConclusionClause, True

/-- Event Sourcing non-conclusion clauses are available as theorem data. -/
theorem eventSourcing_nonConclusion :
    EventSourcingNonConclusion := by
  intro clause
  cases clause <;> trivial

/--
Representative `DesignPattern` schema for Event Sourcing.

This package is bounded by selected finite replay / projection cases. It does
not claim completeness of a real codebase event log or empirical cost effects.
-/
def eventSourcingDesignPattern
    {State : Type u} {Event : Type v} {Obs : Type w} :
    DesignPattern
      (eventSourcingOperationSource :
        EventSourcingOperation State Event Obs ->
          EventSourcingPatternState State Event Obs)
      eventSourcingOperationTarget eventSourcingInvariantHolds where
  operationFamily := eventSourcingOperationFamily
  invariantFamily := eventSourcingInvariantFamily
  operationsPreserveInvariants := eventSourcingOperationFamily_subset_ops
  invariantsPreservedByOperations := eventSourcingInvariantFamily_subset_inv
  nonConclusion := EventSourcingNonConclusion

/-- Event Sourcing exposes the expected two closure laws. -/
theorem eventSourcingDesignPattern_closure_law
    {State : Type u} {Event : Type v} {Obs : Type w} :
    PredicateSubset
        (eventSourcingDesignPattern
          (State := State) (Event := Event) (Obs := Obs)).operationFamily
        (Ops eventSourcingOperationSource eventSourcingOperationTarget
          eventSourcingInvariantHolds
          (eventSourcingDesignPattern
            (State := State) (Event := Event) (Obs := Obs)).invariantFamily) ∧
      PredicateSubset
        (eventSourcingDesignPattern
          (State := State) (Event := Event) (Obs := Obs)).invariantFamily
        (Inv eventSourcingOperationSource eventSourcingOperationTarget
          eventSourcingInvariantHolds
          (eventSourcingDesignPattern
            (State := State) (Event := Event) (Obs := Obs)).operationFamily) :=
  DesignPattern.closure_law eventSourcingDesignPattern

/-- The Event Sourcing package records its non-conclusion clauses. -/
theorem eventSourcingDesignPattern_records_nonConclusion
    {State : Type u} {Event : Type v} {Obs : Type w} :
    (eventSourcingDesignPattern
      (State := State) (Event := Event) (Obs := Obs)).RecordsNonConclusions :=
  eventSourcing_nonConclusion

/-- Selected Saga state: carrier plus weak-recovery compensation cases. -/
structure SagaPatternState (State : Type u) (Event : Type v)
    (Obs : Type w) where
  carrier : StateTransitionCarrier State Event Obs
  compensationCases : List (StateCompensationCase State Event)

/-- Saga lawfulness is selected weak recovery by compensation cases. -/
def SagaWeakRecoveryLawful
    {State : Type u} {Event : Type v} {Obs : Type w}
    (state : SagaPatternState State Event Obs) : Prop :=
  StateCompensationLawful state.carrier.sem state.compensationCases

/-- Proof-carrying Saga operation with target-side weak recovery evidence. -/
structure SagaOperation (State : Type u) (Event : Type v) (Obs : Type w) where
  source : SagaPatternState State Event Obs
  target : SagaPatternState State Event Obs
  weakRecoveryLaw : SagaWeakRecoveryLawful target

/-- View a Saga state as a generic state-transition pattern state. -/
def sagaPatternState_toStateTransitionPatternState
    {State : Type u} {Event : Type v} {Obs : Type w}
    (state : SagaPatternState State Event Obs) :
    StateTransitionPatternState State Event Obs where
  carrier := state.carrier
  replayCases := []
  roundtripCases := []
  compensationCases := state.compensationCases

/-- View a Saga operation as a generic state-transition operation. -/
def sagaOperation_toStateTransitionOperation
    {State : Type u} {Event : Type v} {Obs : Type w}
    (op : SagaOperation State Event Obs) :
    StateTransitionOperation State Event Obs where
  source := sagaPatternState_toStateTransitionPatternState op.source
  target := sagaPatternState_toStateTransitionPatternState op.target
  lawFamily :=
    ⟨stateReplayLawful_nil op.target.carrier.sem,
      stateRoundtripLawful_nil op.target.carrier.sem, op.weakRecoveryLaw⟩

/--
The generic state-transition invariant closure applies to the Saga operation
viewed through the state-transition carrier.
-/
theorem sagaOperation_stateTransitionClosure
    {State : Type u} {Event : Type v} {Obs : Type w}
    (op : SagaOperation State Event Obs) :
    Ops stateTransitionOperationSource stateTransitionOperationTarget
      stateTransitionInvariantHolds stateTransitionInvariantFamily
      (sagaOperation_toStateTransitionOperation op) :=
  stateTransitionOperation_preserves_stateTransitionInvariant
    (sagaOperation_toStateTransitionOperation op)

/-- Source map for Saga operations. -/
def sagaOperationSource
    {State : Type u} {Event : Type v} {Obs : Type w}
    (op : SagaOperation State Event Obs) : SagaPatternState State Event Obs :=
  op.source

/-- Target map for Saga operations. -/
def sagaOperationTarget
    {State : Type u} {Event : Type v} {Obs : Type w}
    (op : SagaOperation State Event Obs) : SagaPatternState State Event Obs :=
  op.target

/-- Selected Saga invariant axes. -/
inductive SagaInvariant where
  | compensationWeakRecovery
  | lawFamilyLawful

/-- Interpretation of Saga invariants on a selected state. -/
def sagaInvariantHolds
    {State : Type u} {Event : Type v} {Obs : Type w} :
    SagaInvariant -> SagaPatternState State Event Obs -> Prop
  | SagaInvariant.compensationWeakRecovery, state =>
      SagaWeakRecoveryLawful state
  | SagaInvariant.lawFamilyLawful, state =>
      SagaWeakRecoveryLawful state

/-- The representative Saga invariant family. -/
def sagaInvariantFamily (_ : SagaInvariant) : Prop :=
  True

/-- The representative Saga operation family. -/
def sagaOperationFamily
    {State : Type u} {Event : Type v} {Obs : Type w}
    (_op : SagaOperation State Event Obs) : Prop :=
  True

/-- A proof-carrying Saga operation preserves weak recovery. -/
theorem sagaOperation_preserves_weakRecovery
    {State : Type u} {Event : Type v} {Obs : Type w}
    (op : SagaOperation State Event Obs) :
    SagaWeakRecoveryLawful op.target :=
  op.weakRecoveryLaw

/-- Saga proof-carrying operations preserve every selected invariant. -/
theorem sagaOperation_preserves_sagaInvariant
    {State : Type u} {Event : Type v} {Obs : Type w}
    (op : SagaOperation State Event Obs) :
    Ops sagaOperationSource sagaOperationTarget
      sagaInvariantHolds sagaInvariantFamily op := by
  intro invariant _hInvariant _hSource
  cases invariant
  · exact sagaOperation_preserves_weakRecovery op
  · exact sagaOperation_preserves_weakRecovery op

/-- The Saga operation family is contained in `Ops(S)`. -/
theorem sagaOperationFamily_subset_ops
    {State : Type u} {Event : Type v} {Obs : Type w} :
    PredicateSubset
      (sagaOperationFamily : SagaOperation State Event Obs -> Prop)
      (Ops sagaOperationSource sagaOperationTarget
        sagaInvariantHolds sagaInvariantFamily) := by
  intro op _hOp
  exact sagaOperation_preserves_sagaInvariant op

/-- Saga selected invariants are preserved by the operation family. -/
theorem sagaInvariantFamily_subset_inv
    {State : Type u} {Event : Type v} {Obs : Type w} :
    PredicateSubset sagaInvariantFamily
      (Inv
        (sagaOperationSource :
          SagaOperation State Event Obs -> SagaPatternState State Event Obs)
        sagaOperationTarget sagaInvariantHolds sagaOperationFamily) := by
  intro invariant _hInvariant op _hOp
  exact sagaOperation_preserves_sagaInvariant op invariant trivial

/-- Non-conclusion clauses for the Saga theorem package. -/
inductive SagaNonConclusionClause where
  | compensationIsGeneralInverse
  | failureModeCompleteness
  | operationalRecoveryCostImprovement
  | extractorCompleteness

/-- Saga non-conclusion clauses are recorded. -/
def SagaNonConclusion : Prop :=
  ∀ _clause : SagaNonConclusionClause, True

/-- Saga non-conclusion clauses are available as theorem data. -/
theorem saga_nonConclusion : SagaNonConclusion := by
  intro clause
  cases clause <;> trivial

/--
Representative `DesignPattern` schema for Saga.

Compensation is treated as selected weak recovery. The package does not claim a
general inverse law, all failure-mode coverage, or operational cost improvement.
-/
def sagaDesignPattern
    {State : Type u} {Event : Type v} {Obs : Type w} :
    DesignPattern
      (sagaOperationSource :
        SagaOperation State Event Obs -> SagaPatternState State Event Obs)
      sagaOperationTarget sagaInvariantHolds where
  operationFamily := sagaOperationFamily
  invariantFamily := sagaInvariantFamily
  operationsPreserveInvariants := sagaOperationFamily_subset_ops
  invariantsPreservedByOperations := sagaInvariantFamily_subset_inv
  nonConclusion := SagaNonConclusion

/-- Saga exposes the expected two closure laws. -/
theorem sagaDesignPattern_closure_law
    {State : Type u} {Event : Type v} {Obs : Type w} :
    PredicateSubset
        (sagaDesignPattern
          (State := State) (Event := Event) (Obs := Obs)).operationFamily
        (Ops sagaOperationSource sagaOperationTarget sagaInvariantHolds
          (sagaDesignPattern
            (State := State) (Event := Event) (Obs := Obs)).invariantFamily) ∧
      PredicateSubset
        (sagaDesignPattern
          (State := State) (Event := Event) (Obs := Obs)).invariantFamily
        (Inv sagaOperationSource sagaOperationTarget sagaInvariantHolds
          (sagaDesignPattern
            (State := State) (Event := Event) (Obs := Obs)).operationFamily) :=
  DesignPattern.closure_law sagaDesignPattern

/-- The Saga package records its non-conclusion clauses. -/
theorem sagaDesignPattern_records_nonConclusion
    {State : Type u} {Event : Type v} {Obs : Type w} :
    (sagaDesignPattern
      (State := State) (Event := Event) (Obs := Obs)).RecordsNonConclusions :=
  saga_nonConclusion

end Formal.Arch
