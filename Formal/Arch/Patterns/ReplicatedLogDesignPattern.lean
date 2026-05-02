import Formal.Arch.Operation.OperationInvariant

namespace Formal.Arch

universe u v

/--
State universe for the distributed convergence layer.

Failure model, quorum predicate, ordering relation, replica-local log presence,
and selected entries are explicit.  The schema only states conditional
convergence for those selected entries under the supplied model.
-/
structure ReplicatedLogState (Replica : Type u) (Entry : Type v) where
  failed : Replica -> Prop
  quorum : (Replica -> Prop) -> Prop
  orderedBefore : Entry -> Entry -> Prop
  presentAt : Replica -> Entry -> Prop
  converged : Entry -> Prop
  selectedEntries : List Entry

/-- Selected quorum evidence for entries in the bounded package. -/
def ReplicatedLogQuorumCondition
    {Replica : Type u} {Entry : Type v}
    (state : ReplicatedLogState Replica Entry) : Prop :=
  ∀ entry, entry ∈ state.selectedEntries ->
    ∃ q : Replica -> Prop,
      state.quorum q ∧
        ∀ replica, q replica ->
          ¬ state.failed replica ∧ state.presentAt replica entry

/-- Selected ordering evidence for entries in the bounded package. -/
def ReplicatedLogOrderingCondition
    {Replica : Type u} {Entry : Type v}
    (state : ReplicatedLogState Replica Entry) : Prop :=
  ∀ left, left ∈ state.selectedEntries ->
    ∀ right, right ∈ state.selectedEntries ->
      state.orderedBefore left right -> ¬ state.orderedBefore right left

/-- Conditional convergence evidence for selected converged entries. -/
def ReplicatedLogConvergenceCondition
    {Replica : Type u} {Entry : Type v}
    (state : ReplicatedLogState Replica Entry) : Prop :=
  ∀ entry, entry ∈ state.selectedEntries -> state.converged entry ->
    ∃ q : Replica -> Prop,
      state.quorum q ∧
        ∀ replica, q replica -> state.presentAt replica entry

/-- Aggregate law family for the selected replicated-log package. -/
def ReplicatedLogLawFamilyLawful
    {Replica : Type u} {Entry : Type v}
    (state : ReplicatedLogState Replica Entry) : Prop :=
  ReplicatedLogQuorumCondition state ∧
    ReplicatedLogOrderingCondition state ∧
      ReplicatedLogConvergenceCondition state

/--
A proof-carrying replicated-log operation.

The target carries quorum, ordering, and conditional convergence evidence.
This is a bounded theorem package, not a proof of a concrete consensus
protocol implementation.
-/
structure ReplicatedLogOperation (Replica : Type u) (Entry : Type v) where
  source : ReplicatedLogState Replica Entry
  target : ReplicatedLogState Replica Entry
  lawFamily : ReplicatedLogLawFamilyLawful target

/-- Source map for replicated-log operations. -/
def replicatedLogOperationSource
    {Replica : Type u} {Entry : Type v}
    (op : ReplicatedLogOperation Replica Entry) :
    ReplicatedLogState Replica Entry :=
  op.source

/-- Target map for replicated-log operations. -/
def replicatedLogOperationTarget
    {Replica : Type u} {Entry : Type v}
    (op : ReplicatedLogOperation Replica Entry) :
    ReplicatedLogState Replica Entry :=
  op.target

/--
Selected invariant axes for the distributed convergence layer.

The convergence axis is conditional on the supplied failure model, quorum
predicate, ordering relation, and selected entries.
-/
inductive ReplicatedLogInvariant where
  | quorumCondition
  | orderingCondition
  | conditionalConvergence
  | lawFamilyLawful

/-- Interpretation of replicated-log invariants on a selected state. -/
def replicatedLogInvariantHolds
    {Replica : Type u} {Entry : Type v} :
    ReplicatedLogInvariant -> ReplicatedLogState Replica Entry -> Prop
  | ReplicatedLogInvariant.quorumCondition, state =>
      ReplicatedLogQuorumCondition state
  | ReplicatedLogInvariant.orderingCondition, state =>
      ReplicatedLogOrderingCondition state
  | ReplicatedLogInvariant.conditionalConvergence, state =>
      ReplicatedLogConvergenceCondition state
  | ReplicatedLogInvariant.lawFamilyLawful, state =>
      ReplicatedLogLawFamilyLawful state

/-- The representative invariant family selected by the replicated-log schema. -/
def replicatedLogInvariantFamily (_ : ReplicatedLogInvariant) : Prop :=
  True

/-- The representative operation family: proof-carrying replicated-log operations. -/
def replicatedLogOperationFamily
    {Replica : Type u} {Entry : Type v}
    (_op : ReplicatedLogOperation Replica Entry) : Prop :=
  True

/-- A proof-carrying operation provides quorum evidence at its target. -/
theorem replicatedLogOperation_preserves_quorumCondition
    {Replica : Type u} {Entry : Type v}
    (op : ReplicatedLogOperation Replica Entry) :
    ReplicatedLogQuorumCondition op.target :=
  op.lawFamily.1

/-- A proof-carrying operation provides ordering evidence at its target. -/
theorem replicatedLogOperation_preserves_orderingCondition
    {Replica : Type u} {Entry : Type v}
    (op : ReplicatedLogOperation Replica Entry) :
    ReplicatedLogOrderingCondition op.target :=
  op.lawFamily.2.1

/-- A proof-carrying operation provides conditional convergence at its target. -/
theorem replicatedLogOperation_preserves_conditionalConvergence
    {Replica : Type u} {Entry : Type v}
    (op : ReplicatedLogOperation Replica Entry) :
    ReplicatedLogConvergenceCondition op.target :=
  op.lawFamily.2.2

/-- A proof-carrying operation provides aggregate law-family lawfulness. -/
theorem replicatedLogOperation_preserves_lawFamilyLawful
    {Replica : Type u} {Entry : Type v}
    (op : ReplicatedLogOperation Replica Entry) :
    ReplicatedLogLawFamilyLawful op.target :=
  op.lawFamily

/--
The proof-carrying replicated-log operation preserves every selected
replicated-log invariant.
-/
theorem replicatedLogOperation_preserves_replicatedLogInvariant
    {Replica : Type u} {Entry : Type v}
    (op : ReplicatedLogOperation Replica Entry) :
    Ops replicatedLogOperationSource replicatedLogOperationTarget
      replicatedLogInvariantHolds replicatedLogInvariantFamily op := by
  intro invariant _hInvariant _hSource
  cases invariant
  · exact replicatedLogOperation_preserves_quorumCondition op
  · exact replicatedLogOperation_preserves_orderingCondition op
  · exact replicatedLogOperation_preserves_conditionalConvergence op
  · exact replicatedLogOperation_preserves_lawFamilyLawful op

/-- The replicated-log operation family is contained in `Ops(S)`. -/
theorem replicatedLogOperationFamily_subset_ops
    {Replica : Type u} {Entry : Type v} :
    PredicateSubset
      (replicatedLogOperationFamily :
        ReplicatedLogOperation Replica Entry -> Prop)
      (Ops replicatedLogOperationSource replicatedLogOperationTarget
        replicatedLogInvariantHolds replicatedLogInvariantFamily) := by
  intro op _hOp
  exact replicatedLogOperation_preserves_replicatedLogInvariant op

/-- The selected replicated-log invariants are preserved by the operation family. -/
theorem replicatedLogInvariantFamily_subset_inv
    {Replica : Type u} {Entry : Type v} :
    PredicateSubset replicatedLogInvariantFamily
      (Inv
        (replicatedLogOperationSource :
          ReplicatedLogOperation Replica Entry ->
            ReplicatedLogState Replica Entry)
        replicatedLogOperationTarget replicatedLogInvariantHolds
        replicatedLogOperationFamily) := by
  intro invariant _hInvariant op _hOp
  exact replicatedLogOperation_preserves_replicatedLogInvariant
    op invariant trivial

/--
Non-conclusion clauses recorded by the replicated-log schema.

These clauses keep the package from claiming unconditional availability,
partition tolerance, convergence outside the selected model, or correctness of
any concrete consensus protocol implementation.
-/
inductive ReplicatedLogNonConclusionClause where
  | unconditionalAvailability
  | partitionTolerance
  | unconditionalConvergence
  | protocolCorrectnessCompleteness
  | concreteImplementationCorrectness

/-- The replicated-log non-conclusion clauses are recorded. -/
def ReplicatedLogNonConclusion : Prop :=
  ∀ _clause : ReplicatedLogNonConclusionClause, True

/-- The replicated-log non-conclusion clauses are available as theorem data. -/
theorem replicatedLog_nonConclusion :
    ReplicatedLogNonConclusion := by
  intro clause
  cases clause <;> trivial

/--
Representative `DesignPattern` schema for Replicated Log.

The closure laws are bounded by the supplied failure model, quorum predicate,
ordering relation, convergence predicate, and selected entries.
-/
def replicatedLogDesignPattern
    {Replica : Type u} {Entry : Type v} :
    DesignPattern
      (replicatedLogOperationSource :
        ReplicatedLogOperation Replica Entry ->
          ReplicatedLogState Replica Entry)
      replicatedLogOperationTarget replicatedLogInvariantHolds where
  operationFamily := replicatedLogOperationFamily
  invariantFamily := replicatedLogInvariantFamily
  operationsPreserveInvariants := replicatedLogOperationFamily_subset_ops
  invariantsPreservedByOperations := replicatedLogInvariantFamily_subset_inv
  nonConclusion := ReplicatedLogNonConclusion

/-- The replicated-log design pattern exposes the expected two closure laws. -/
theorem replicatedLogDesignPattern_closure_law
    {Replica : Type u} {Entry : Type v} :
    PredicateSubset
        (replicatedLogDesignPattern
          (Replica := Replica) (Entry := Entry)).operationFamily
        (Ops replicatedLogOperationSource replicatedLogOperationTarget
          replicatedLogInvariantHolds
          (replicatedLogDesignPattern
            (Replica := Replica) (Entry := Entry)).invariantFamily) ∧
      PredicateSubset
        (replicatedLogDesignPattern
          (Replica := Replica) (Entry := Entry)).invariantFamily
        (Inv replicatedLogOperationSource replicatedLogOperationTarget
          replicatedLogInvariantHolds
          (replicatedLogDesignPattern
            (Replica := Replica) (Entry := Entry)).operationFamily) :=
  DesignPattern.closure_law replicatedLogDesignPattern

/-- The schema records the replicated-log non-conclusion clauses. -/
theorem replicatedLogDesignPattern_records_nonConclusion
    {Replica : Type u} {Entry : Type v} :
    (replicatedLogDesignPattern
      (Replica := Replica) (Entry := Entry)).RecordsNonConclusions :=
  replicatedLog_nonConclusion

end Formal.Arch
