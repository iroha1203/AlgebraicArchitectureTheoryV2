import Formal.Arch.Law.LSP
import Formal.Arch.Operation.OperationInvariant

namespace Formal.Arch

universe u v w

/--
State universe for the Interface Segregation Principle package.

The abstract interface universe is fixed for the theorem package.  A split or
refinement is represented by changing the selected projection inside that
universe, together with a collapse map back to the source projection.
-/
structure InterfaceProjectionRefinementState
    (C : Type u) (A : Type v) (Obs : Type w) where
  G : ArchGraph C
  π : InterfaceProjection C A
  GA : AbstractGraph A
  O : Observation C Obs

/--
A proof-carrying interface projection refinement operation.

The `collapse` map records that the target projection is a refinement of the
source projection: every target interface view can be collapsed back to the
source interface view.  The selected theorem package only requires target-side
projection soundness and observation factorization.
-/
structure InterfaceProjectionRefinementOperation
    (C : Type u) (A : Type v) (Obs : Type w) where
  source : InterfaceProjectionRefinementState C A Obs
  target : InterfaceProjectionRefinementState C A Obs
  collapse : A -> A
  refinesProjection : ∀ c : C, collapse (target.π.expose c) = source.π.expose c
  targetProjectionSound : ProjectionSound target.G target.π target.GA
  targetObservationFactors : ObservationFactorsThrough target.π target.O

/-- Source map for interface projection refinement operations. -/
def interfaceProjectionRefinementOperationSource
    {C : Type u} {A : Type v} {Obs : Type w}
    (op : InterfaceProjectionRefinementOperation C A Obs) :
    InterfaceProjectionRefinementState C A Obs :=
  op.source

/-- Target map for interface projection refinement operations. -/
def interfaceProjectionRefinementOperationTarget
    {C : Type u} {A : Type v} {Obs : Type w}
    (op : InterfaceProjectionRefinementOperation C A Obs) :
    InterfaceProjectionRefinementState C A Obs :=
  op.target

/--
Selected invariant axes for the bounded ISP theorem package.

These are projection and observation-boundary facts.  They do not claim that a
chosen interface split is globally optimal or usable as an API design.
-/
inductive InterfaceProjectionRefinementInvariant where
  | projectionSound
  | observationBoundaryFactors
  | lspCompatible

/-- Interpretation of ISP invariants on a selected projection-refinement state. -/
def interfaceProjectionRefinementInvariantHolds
    {C : Type u} {A : Type v} {Obs : Type w} :
    InterfaceProjectionRefinementInvariant ->
      InterfaceProjectionRefinementState C A Obs -> Prop
  | InterfaceProjectionRefinementInvariant.projectionSound, state =>
      ProjectionSound state.G state.π state.GA
  | InterfaceProjectionRefinementInvariant.observationBoundaryFactors, state =>
      ObservationFactorsThrough state.π state.O
  | InterfaceProjectionRefinementInvariant.lspCompatible, state =>
      LSPCompatible state.π state.O

/-- The representative invariant family selected by the bounded ISP schema. -/
def interfaceProjectionRefinementInvariantFamily
    (_ : InterfaceProjectionRefinementInvariant) : Prop :=
  True

/-- The representative operation family: proof-carrying projection refinements. -/
def interfaceProjectionRefinementOperationFamily
    {C : Type u} {A : Type v} {Obs : Type w}
    (_op : InterfaceProjectionRefinementOperation C A Obs) : Prop :=
  True

/-- An ISP refinement operation exposes the target-side projection soundness. -/
theorem interfaceProjectionRefinementOperation_preserves_projectionSound
    {C : Type u} {A : Type v} {Obs : Type w}
    (op : InterfaceProjectionRefinementOperation C A Obs) :
    ProjectionSound op.target.G op.target.π op.target.GA :=
  op.targetProjectionSound

/-- An ISP refinement operation exposes the selected target observation boundary. -/
theorem interfaceProjectionRefinementOperation_preserves_observationBoundaryFactors
    {C : Type u} {A : Type v} {Obs : Type w}
    (op : InterfaceProjectionRefinementOperation C A Obs) :
    ObservationFactorsThrough op.target.π op.target.O :=
  op.targetObservationFactors

/--
Target observation factorization gives the selected LSP compatibility axis for
the refined projection.
-/
theorem interfaceProjectionRefinementOperation_preserves_lspCompatible
    {C : Type u} {A : Type v} {Obs : Type w}
    (op : InterfaceProjectionRefinementOperation C A Obs) :
    LSPCompatible op.target.π op.target.O :=
  lspCompatible_of_observationFactorsThrough op.targetObservationFactors

/-- The operation records that the target projection refines the source projection. -/
theorem interfaceProjectionRefinementOperation_refinesProjection
    {C : Type u} {A : Type v} {Obs : Type w}
    (op : InterfaceProjectionRefinementOperation C A Obs) (c : C) :
    op.collapse (op.target.π.expose c) = op.source.π.expose c :=
  op.refinesProjection c

/--
The proof-carrying ISP operation preserves every selected projection /
observation invariant at its target.
-/
theorem interfaceProjectionRefinementOperation_preserves_invariant
    {C : Type u} {A : Type v} {Obs : Type w}
    (op : InterfaceProjectionRefinementOperation C A Obs) :
    Ops interfaceProjectionRefinementOperationSource
      interfaceProjectionRefinementOperationTarget
      interfaceProjectionRefinementInvariantHolds
      interfaceProjectionRefinementInvariantFamily op := by
  intro invariant _hInvariant _hSource
  cases invariant
  · exact interfaceProjectionRefinementOperation_preserves_projectionSound op
  · exact interfaceProjectionRefinementOperation_preserves_observationBoundaryFactors op
  · exact interfaceProjectionRefinementOperation_preserves_lspCompatible op

/-- The ISP operation family is contained in `Ops(S)`. -/
theorem interfaceProjectionRefinementOperationFamily_subset_ops
    {C : Type u} {A : Type v} {Obs : Type w} :
    PredicateSubset
      (interfaceProjectionRefinementOperationFamily :
        InterfaceProjectionRefinementOperation C A Obs -> Prop)
      (Ops interfaceProjectionRefinementOperationSource
        interfaceProjectionRefinementOperationTarget
        interfaceProjectionRefinementInvariantHolds
        interfaceProjectionRefinementInvariantFamily) := by
  intro op _hOp
  exact interfaceProjectionRefinementOperation_preserves_invariant op

/-- The selected ISP invariants are preserved by the operation family. -/
theorem interfaceProjectionRefinementInvariantFamily_subset_inv
    {C : Type u} {A : Type v} {Obs : Type w} :
    PredicateSubset interfaceProjectionRefinementInvariantFamily
      (Inv
        (interfaceProjectionRefinementOperationSource :
          InterfaceProjectionRefinementOperation C A Obs ->
            InterfaceProjectionRefinementState C A Obs)
        interfaceProjectionRefinementOperationTarget
        interfaceProjectionRefinementInvariantHolds
        interfaceProjectionRefinementOperationFamily) := by
  intro invariant _hInvariant op _hOp
  exact interfaceProjectionRefinementOperation_preserves_invariant
    op invariant trivial

/--
Non-conclusion clauses recorded by the bounded ISP schema.

They mark properties intentionally left outside the theorem package.
-/
inductive InterfaceProjectionRefinementNonConclusionClause where
  | naturalLanguageISP
  | apiUsability
  | globallyOptimalInterfaceGranularity

/-- The ISP schema records all explicit non-conclusion clauses. -/
def InterfaceProjectionRefinementNonConclusion : Prop :=
  ∀ _clause : InterfaceProjectionRefinementNonConclusionClause, True

/-- The ISP non-conclusion clauses are recorded. -/
theorem interfaceProjectionRefinement_nonConclusion :
    InterfaceProjectionRefinementNonConclusion := by
  intro clause
  cases clause <;> trivial

/--
Representative `DesignPattern` schema for the Interface Segregation Principle.

The closure laws are selected projection soundness and observation-boundary
factorization for proof-carrying interface refinements.  API usability and
global interface-granularity optimality remain non-conclusions.
-/
def interfaceProjectionRefinementDesignPattern
    {C : Type u} {A : Type v} {Obs : Type w} :
    DesignPattern
      (interfaceProjectionRefinementOperationSource :
        InterfaceProjectionRefinementOperation C A Obs ->
          InterfaceProjectionRefinementState C A Obs)
      interfaceProjectionRefinementOperationTarget
      interfaceProjectionRefinementInvariantHolds where
  operationFamily := interfaceProjectionRefinementOperationFamily
  invariantFamily := interfaceProjectionRefinementInvariantFamily
  operationsPreserveInvariants := interfaceProjectionRefinementOperationFamily_subset_ops
  invariantsPreservedByOperations := interfaceProjectionRefinementInvariantFamily_subset_inv
  nonConclusion := InterfaceProjectionRefinementNonConclusion

/-- The ISP design pattern exposes the expected two closure laws. -/
theorem interfaceProjectionRefinementDesignPattern_closure_law
    {C : Type u} {A : Type v} {Obs : Type w} :
    PredicateSubset
        (interfaceProjectionRefinementDesignPattern (C := C) (A := A) (Obs := Obs)).operationFamily
        (Ops interfaceProjectionRefinementOperationSource
          interfaceProjectionRefinementOperationTarget
          interfaceProjectionRefinementInvariantHolds
          (interfaceProjectionRefinementDesignPattern (C := C) (A := A) (Obs := Obs)).invariantFamily) ∧
      PredicateSubset
        (interfaceProjectionRefinementDesignPattern (C := C) (A := A) (Obs := Obs)).invariantFamily
        (Inv interfaceProjectionRefinementOperationSource
          interfaceProjectionRefinementOperationTarget
          interfaceProjectionRefinementInvariantHolds
          (interfaceProjectionRefinementDesignPattern (C := C) (A := A) (Obs := Obs)).operationFamily) :=
  DesignPattern.closure_law interfaceProjectionRefinementDesignPattern

/-- The schema records the ISP non-conclusion clauses. -/
theorem interfaceProjectionRefinementDesignPattern_records_nonConclusion
    {C : Type u} {A : Type v} {Obs : Type w} :
    (interfaceProjectionRefinementDesignPattern (C := C) (A := A) (Obs := Obs)).RecordsNonConclusions :=
  interfaceProjectionRefinement_nonConclusion

end Formal.Arch
