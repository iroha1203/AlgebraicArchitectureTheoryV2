import Formal.Arch.LocalReplacement
import Formal.Arch.OperationInvariant
import Formal.Arch.Examples.SolidCounterexample

namespace Formal.Arch

universe u v w

/--
State universe for the local-contract layer.

It keeps the concrete graph, the interface projection, the abstract graph, and
the public observation together so that LSP and DIP obligations share the same
projection boundary.
-/
structure LocalContractState (C : Type u) (A : Type v) (Obs : Type w) where
  G : ArchGraph C
  π : InterfaceProjection C A
  GA : AbstractGraph A
  O : Observation C Obs

/--
A local replacement operation whose target state carries the selected local
replacement contract.

The source state is retained so this package can be read by the generic
operation/invariant Galois API.
-/
structure LocalReplacementOperation (C : Type u) (A : Type v) (Obs : Type w) where
  source : LocalContractState C A Obs
  target : LocalContractState C A Obs
  contract : LocalReplacementContract target.G target.π target.GA target.O

/-- Source map for local replacement operations. -/
def localReplacementOperationSource
    {C : Type u} {A : Type v} {Obs : Type w}
    (op : LocalReplacementOperation C A Obs) : LocalContractState C A Obs :=
  op.source

/-- Target map for local replacement operations. -/
def localReplacementOperationTarget
    {C : Type u} {A : Type v} {Obs : Type w}
    (op : LocalReplacementOperation C A Obs) : LocalContractState C A Obs :=
  op.target

/--
The minimal invariant family exposed by the local-contract layer bridge.

These are local contract axes.  Global layering is recorded as a non-conclusion,
not as an invariant selected by this family.
-/
inductive LocalContractInvariant where
  | projectionSound
  | lspCompatible
  | dipCompatible

/-- Interpretation of local-contract invariants on a selected state. -/
def localContractInvariantHolds
    {C : Type u} {A : Type v} {Obs : Type w} :
    LocalContractInvariant -> LocalContractState C A Obs -> Prop
  | LocalContractInvariant.projectionSound, state =>
      ProjectionSound state.G state.π state.GA
  | LocalContractInvariant.lspCompatible, state =>
      LSPCompatible state.π state.O
  | LocalContractInvariant.dipCompatible, state =>
      DIPCompatible state.G state.π state.GA

/-- The representative local contract invariant family used by the schema. -/
def localContractInvariantFamily (_ : LocalContractInvariant) : Prop :=
  True

/-- The representative operation family: proof-carrying local replacements. -/
def localReplacementOperationFamily
    {C : Type u} {A : Type v} {Obs : Type w}
    (_op : LocalReplacementOperation C A Obs) : Prop :=
  True

/-- A local replacement operation preserves projection soundness at its target. -/
theorem localReplacementOperation_preserves_projectionSound
    {C : Type u} {A : Type v} {Obs : Type w}
    (op : LocalReplacementOperation C A Obs) :
    ProjectionSound op.target.G op.target.π op.target.GA :=
  projectionSound_of_localReplacementContract op.contract

/-- A local replacement operation preserves LSP compatibility at its target. -/
theorem localReplacementOperation_preserves_lspCompatible
    {C : Type u} {A : Type v} {Obs : Type w}
    (op : LocalReplacementOperation C A Obs) :
    LSPCompatible op.target.π op.target.O :=
  lspCompatible_of_localReplacementContract op.contract

/-- A local replacement operation preserves DIP compatibility at its target. -/
theorem localReplacementOperation_preserves_dipCompatible
    {C : Type u} {A : Type v} {Obs : Type w}
    (op : LocalReplacementOperation C A Obs) :
    DIPCompatible op.target.G op.target.π op.target.GA :=
  op.contract.1

/--
The proof-carrying local replacement operation preserves every invariant in the
selected local-contract invariant family.
-/
theorem localReplacementOperation_preserves_localContractInvariant
    {C : Type u} {A : Type v} {Obs : Type w}
    (op : LocalReplacementOperation C A Obs) :
    Ops localReplacementOperationSource localReplacementOperationTarget
      localContractInvariantHolds localContractInvariantFamily op := by
  intro invariant _hInvariant _hSource
  cases invariant
  · exact localReplacementOperation_preserves_projectionSound op
  · exact localReplacementOperation_preserves_lspCompatible op
  · exact localReplacementOperation_preserves_dipCompatible op

/-- The local replacement operation family is contained in `Ops(S)`. -/
theorem localReplacementOperationFamily_subset_ops
    {C : Type u} {A : Type v} {Obs : Type w} :
    PredicateSubset
      (localReplacementOperationFamily :
        LocalReplacementOperation C A Obs -> Prop)
      (Ops localReplacementOperationSource localReplacementOperationTarget
        localContractInvariantHolds localContractInvariantFamily) := by
  intro op _hOp
  exact localReplacementOperation_preserves_localContractInvariant op

/-- The selected local-contract invariants are preserved by the operation family. -/
theorem localContractInvariantFamily_subset_inv
    {C : Type u} {A : Type v} {Obs : Type w} :
    PredicateSubset localContractInvariantFamily
      (Inv
        (localReplacementOperationSource :
          LocalReplacementOperation C A Obs -> LocalContractState C A Obs)
        localReplacementOperationTarget localContractInvariantHolds
        localReplacementOperationFamily) := by
  intro invariant _hInvariant op _hOp
  exact localReplacementOperation_preserves_localContractInvariant op invariant trivial

/--
Recorded non-conclusion for the local-contract layer.

Local replacement, LSP, and DIP compatibility do not amount to an unconditional
global `Decomposable` / `StrictLayered` theorem.
-/
def LocalContractLayerNonConclusion : Prop :=
  (¬ (∀ {C A Obs : Type} (G : ArchGraph C) (π : InterfaceProjection C A)
      (GA : AbstractGraph A) (O : Observation C Obs),
      LocalReplacementContract G π GA O -> Decomposable G)) ∧
  (¬ (∀ {C A Obs : Type} (G : ArchGraph C) (π : InterfaceProjection C A)
      (GA : AbstractGraph A) (O : Observation C Obs),
      LocalReplacementContract G π GA O -> StrictLayered G))

/--
The strong abstract-cycle counterexample witnesses the local-contract
non-conclusion.
-/
theorem localContractLayer_nonConclusion :
    LocalContractLayerNonConclusion := by
  constructor
  · intro hGlobal
    exact StrongAbstractCycleComponent.not_decomposable
      (hGlobal StrongAbstractCycleComponent.graph
        StrongAbstractCycleComponent.projection
        StrongAbstractCycleComponent.abstractGraph
        StrongAbstractCycleComponent.observation
        ⟨StrongAbstractCycleComponent.dipCompatible,
          StrongAbstractCycleComponent.observation_factors⟩)
  · intro hGlobal
    exact StrongAbstractCycleComponent.not_decomposable
      (hGlobal StrongAbstractCycleComponent.graph
        StrongAbstractCycleComponent.projection
        StrongAbstractCycleComponent.abstractGraph
        StrongAbstractCycleComponent.observation
        ⟨StrongAbstractCycleComponent.dipCompatible,
          StrongAbstractCycleComponent.observation_factors⟩)

/--
Representative `DesignPattern` schema for local contract replacement.

The closure laws are exactly the selected preservation laws above; global
layering is only recorded as a non-conclusion.
-/
def localContractDesignPattern
    {C : Type u} {A : Type v} {Obs : Type w} :
    DesignPattern
      (localReplacementOperationSource :
        LocalReplacementOperation C A Obs -> LocalContractState C A Obs)
      localReplacementOperationTarget localContractInvariantHolds where
  operationFamily := localReplacementOperationFamily
  invariantFamily := localContractInvariantFamily
  operationsPreserveInvariants := localReplacementOperationFamily_subset_ops
  invariantsPreservedByOperations := localContractInvariantFamily_subset_inv
  nonConclusion := LocalContractLayerNonConclusion

/-- The local contract design pattern exposes the expected two closure laws. -/
theorem localContractDesignPattern_closure_law
    {C : Type u} {A : Type v} {Obs : Type w} :
    PredicateSubset
        (localContractDesignPattern (C := C) (A := A) (Obs := Obs)).operationFamily
        (Ops localReplacementOperationSource localReplacementOperationTarget
          localContractInvariantHolds
          (localContractDesignPattern (C := C) (A := A) (Obs := Obs)).invariantFamily) ∧
      PredicateSubset
        (localContractDesignPattern (C := C) (A := A) (Obs := Obs)).invariantFamily
        (Inv localReplacementOperationSource localReplacementOperationTarget
          localContractInvariantHolds
          (localContractDesignPattern (C := C) (A := A) (Obs := Obs)).operationFamily) :=
  DesignPattern.closure_law localContractDesignPattern

/-- The schema records the local-contract non-conclusion clause. -/
theorem localContractDesignPattern_records_nonConclusion
    {C : Type u} {A : Type v} {Obs : Type w} :
    (localContractDesignPattern (C := C) (A := A) (Obs := Obs)).RecordsNonConclusions :=
  localContractLayer_nonConclusion

end Formal.Arch
