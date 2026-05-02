import Formal.Arch.Operation.OperationInvariant
import Formal.Arch.Law.StateEffect

namespace Formal.Arch

universe u v w

/--
Minimal carrier for the state-transition algebra layer.

The executable transition data and observation boundary are kept explicit, while
lawfulness is still read through the existing `StateTransitionExpr` semantics.
This lets Event Sourcing / Saga theorem packages specialize the carrier without
claiming extractor completeness for real event logs.
-/
structure StateTransitionCarrier (State : Type u) (Event : Type v)
    (Obs : Type w) where
  step : State -> Event -> State
  observe : State -> Obs
  replay : State -> List Event -> State
  project : State -> List Event -> Obs
  compensate : State -> List Event -> List Event
  sem : Semantics (StateTransitionExpr State Event) Obs

/--
State universe for state-transition design patterns.

The finite law cases are part of the selected theorem package.  They are not a
claim that all histories, projections, or compensations in a concrete codebase
have been measured.
-/
structure StateTransitionPatternState (State : Type u) (Event : Type v)
    (Obs : Type w) where
  carrier : StateTransitionCarrier State Event Obs
  replayCases : List (StateReplayCase State Event)
  roundtripCases : List (StateRoundtripCase State Event)
  compensationCases : List (StateCompensationCase State Event)

/--
A proof-carrying state-transition operation.

The target state carries the bounded replay / roundtrip / compensation law
family needed to read the operation through the generic `DesignPattern` schema.
-/
structure StateTransitionOperation (State : Type u) (Event : Type v)
    (Obs : Type w) where
  source : StateTransitionPatternState State Event Obs
  target : StateTransitionPatternState State Event Obs
  lawFamily :
    StateTransitionLawFamilyLawful target.carrier.sem target.replayCases
      target.roundtripCases target.compensationCases

/-- Source map for state-transition operations. -/
def stateTransitionOperationSource
    {State : Type u} {Event : Type v} {Obs : Type w}
    (op : StateTransitionOperation State Event Obs) :
    StateTransitionPatternState State Event Obs :=
  op.source

/-- Target map for state-transition operations. -/
def stateTransitionOperationTarget
    {State : Type u} {Event : Type v} {Obs : Type w}
    (op : StateTransitionOperation State Event Obs) :
    StateTransitionPatternState State Event Obs :=
  op.target

/--
Selected invariant axes for the state-transition algebra layer.

`replayLawful` covers the replay / projection boundary exposed by
`StateTransitionExpr.history` and `StateTransitionExpr.replay`; compensation is
kept as weak recovery, not as a general inverse law.
-/
inductive StateTransitionInvariant where
  | replayLawful
  | roundtripLawful
  | compensationLawful
  | lawFamilyLawful

/-- Interpretation of state-transition invariants on a selected state. -/
def stateTransitionInvariantHolds
    {State : Type u} {Event : Type v} {Obs : Type w} :
    StateTransitionInvariant ->
      StateTransitionPatternState State Event Obs -> Prop
  | StateTransitionInvariant.replayLawful, state =>
      StateReplayLawful state.carrier.sem state.replayCases
  | StateTransitionInvariant.roundtripLawful, state =>
      StateRoundtripLawful state.carrier.sem state.roundtripCases
  | StateTransitionInvariant.compensationLawful, state =>
      StateCompensationLawful state.carrier.sem state.compensationCases
  | StateTransitionInvariant.lawFamilyLawful, state =>
      StateTransitionLawFamilyLawful state.carrier.sem state.replayCases
        state.roundtripCases state.compensationCases

/-- The representative invariant family selected by the state-transition schema. -/
def stateTransitionInvariantFamily (_ : StateTransitionInvariant) : Prop :=
  True

/-- The representative operation family: proof-carrying state-transition operations. -/
def stateTransitionOperationFamily
    {State : Type u} {Event : Type v} {Obs : Type w}
    (_op : StateTransitionOperation State Event Obs) : Prop :=
  True

/-- A proof-carrying operation provides replay lawfulness at its target. -/
theorem stateTransitionOperation_preserves_replayLawful
    {State : Type u} {Event : Type v} {Obs : Type w}
    (op : StateTransitionOperation State Event Obs) :
    StateReplayLawful op.target.carrier.sem op.target.replayCases :=
  op.lawFamily.1

/-- A proof-carrying operation provides roundtrip lawfulness at its target. -/
theorem stateTransitionOperation_preserves_roundtripLawful
    {State : Type u} {Event : Type v} {Obs : Type w}
    (op : StateTransitionOperation State Event Obs) :
    StateRoundtripLawful op.target.carrier.sem op.target.roundtripCases :=
  op.lawFamily.2.1

/-- A proof-carrying operation provides compensation lawfulness at its target. -/
theorem stateTransitionOperation_preserves_compensationLawful
    {State : Type u} {Event : Type v} {Obs : Type w}
    (op : StateTransitionOperation State Event Obs) :
    StateCompensationLawful op.target.carrier.sem op.target.compensationCases :=
  op.lawFamily.2.2

/-- A proof-carrying operation provides aggregate law-family lawfulness. -/
theorem stateTransitionOperation_preserves_lawFamilyLawful
    {State : Type u} {Event : Type v} {Obs : Type w}
    (op : StateTransitionOperation State Event Obs) :
    StateTransitionLawFamilyLawful op.target.carrier.sem op.target.replayCases
      op.target.roundtripCases op.target.compensationCases :=
  op.lawFamily

/--
The proof-carrying state-transition operation preserves every selected
state-transition invariant.
-/
theorem stateTransitionOperation_preserves_stateTransitionInvariant
    {State : Type u} {Event : Type v} {Obs : Type w}
    (op : StateTransitionOperation State Event Obs) :
    Ops stateTransitionOperationSource stateTransitionOperationTarget
      stateTransitionInvariantHolds stateTransitionInvariantFamily op := by
  intro invariant _hInvariant _hSource
  cases invariant
  · exact stateTransitionOperation_preserves_replayLawful op
  · exact stateTransitionOperation_preserves_roundtripLawful op
  · exact stateTransitionOperation_preserves_compensationLawful op
  · exact stateTransitionOperation_preserves_lawFamilyLawful op

/-- The state-transition operation family is contained in `Ops(S)`. -/
theorem stateTransitionOperationFamily_subset_ops
    {State : Type u} {Event : Type v} {Obs : Type w} :
    PredicateSubset
      (stateTransitionOperationFamily :
        StateTransitionOperation State Event Obs -> Prop)
      (Ops stateTransitionOperationSource stateTransitionOperationTarget
        stateTransitionInvariantHolds stateTransitionInvariantFamily) := by
  intro op _hOp
  exact stateTransitionOperation_preserves_stateTransitionInvariant op

/-- The selected state-transition invariants are preserved by the operation family. -/
theorem stateTransitionInvariantFamily_subset_inv
    {State : Type u} {Event : Type v} {Obs : Type w} :
    PredicateSubset stateTransitionInvariantFamily
      (Inv
        (stateTransitionOperationSource :
          StateTransitionOperation State Event Obs ->
            StateTransitionPatternState State Event Obs)
        stateTransitionOperationTarget stateTransitionInvariantHolds
        stateTransitionOperationFamily) := by
  intro invariant _hInvariant op _hOp
  exact stateTransitionOperation_preserves_stateTransitionInvariant
    op invariant trivial

/--
Non-conclusion clauses recorded by the state-transition schema.

These clauses keep Event Sourcing / Saga / CRUD interpretation bounded by the
selected carrier and finite law cases.
-/
inductive StateTransitionNonConclusionClause where
  | extractorCompleteness
  | eventLogCompleteness
  | operationalCostImprovement
  | crudUniversalDesignPattern

/-- The state-transition non-conclusion clauses are recorded. -/
def StateTransitionNonConclusion : Prop :=
  ∀ _clause : StateTransitionNonConclusionClause, True

/-- The state-transition non-conclusion clauses are available as theorem data. -/
theorem stateTransition_nonConclusion :
    StateTransitionNonConclusion := by
  intro clause
  cases clause <;> trivial

/--
Representative `DesignPattern` schema for the state-transition algebra layer.

Event Sourcing and Saga can instantiate this carrier with selected replay,
projection, and weak-compensation law cases.  CRUD remains outside this theorem
package unless a separate selected carrier and invariant family are supplied.
-/
def stateTransitionDesignPattern
    {State : Type u} {Event : Type v} {Obs : Type w} :
    DesignPattern
      (stateTransitionOperationSource :
        StateTransitionOperation State Event Obs ->
          StateTransitionPatternState State Event Obs)
      stateTransitionOperationTarget stateTransitionInvariantHolds where
  operationFamily := stateTransitionOperationFamily
  invariantFamily := stateTransitionInvariantFamily
  operationsPreserveInvariants := stateTransitionOperationFamily_subset_ops
  invariantsPreservedByOperations := stateTransitionInvariantFamily_subset_inv
  nonConclusion := StateTransitionNonConclusion

/-- The state-transition design pattern exposes the expected two closure laws. -/
theorem stateTransitionDesignPattern_closure_law
    {State : Type u} {Event : Type v} {Obs : Type w} :
    PredicateSubset
        (stateTransitionDesignPattern
          (State := State) (Event := Event) (Obs := Obs)).operationFamily
        (Ops stateTransitionOperationSource stateTransitionOperationTarget
          stateTransitionInvariantHolds
          (stateTransitionDesignPattern
            (State := State) (Event := Event) (Obs := Obs)).invariantFamily) ∧
      PredicateSubset
        (stateTransitionDesignPattern
          (State := State) (Event := Event) (Obs := Obs)).invariantFamily
        (Inv stateTransitionOperationSource stateTransitionOperationTarget
          stateTransitionInvariantHolds
          (stateTransitionDesignPattern
            (State := State) (Event := Event) (Obs := Obs)).operationFamily) :=
  DesignPattern.closure_law stateTransitionDesignPattern

/-- The schema records the state-transition non-conclusion clauses. -/
theorem stateTransitionDesignPattern_records_nonConclusion
    {State : Type u} {Event : Type v} {Obs : Type w} :
    (stateTransitionDesignPattern
      (State := State) (Event := Event) (Obs := Obs)).RecordsNonConclusions :=
  stateTransition_nonConclusion

end Formal.Arch
