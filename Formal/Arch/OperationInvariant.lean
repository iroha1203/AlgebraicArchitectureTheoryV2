namespace Formal.Arch

universe u v w

/--
An operation preserves an invariant when the invariant holding at the operation
source implies that it holds at the operation target.

`holds` lets the theorem package talk about named invariant families rather than
only predicates on states.
-/
def PreservesInvariant {State : Type u} {Operation : Type v} {Invariant : Type w}
    (source target : Operation -> State)
    (holds : Invariant -> State -> Prop)
    (op : Operation) (I : Invariant) : Prop :=
  holds I (source op) -> holds I (target op)

/-- Operations that preserve every invariant selected by `S`. -/
def Ops {State : Type u} {Operation : Type v} {Invariant : Type w}
    (source target : Operation -> State)
    (holds : Invariant -> State -> Prop)
    (S : Invariant -> Prop) : Operation -> Prop :=
  fun op => ∀ I, S I -> PreservesInvariant source target holds op I

/-- Invariants preserved by every operation selected by `T`. -/
def Inv {State : Type u} {Operation : Type v} {Invariant : Type w}
    (source target : Operation -> State)
    (holds : Invariant -> State -> Prop)
    (T : Operation -> Prop) : Invariant -> Prop :=
  fun I => ∀ op, T op -> PreservesInvariant source target holds op I

/-- Predicate-family inclusion, used to state the weak Galois correspondence. -/
def PredicateSubset {α : Type u} (A B : α -> Prop) : Prop :=
  ∀ x, A x -> B x

/--
Invariant families closed by the operation/invariant preservation closure.

This is only the closure equation induced by the selected preservation relation;
it does not assert that every meaningful invariant family has been classified.
-/
def ClosedInvariantSet {State : Type u} {Operation : Type v} {Invariant : Type w}
    (source target : Operation -> State)
    (holds : Invariant -> State -> Prop)
    (S : Invariant -> Prop) : Prop :=
  S = Inv source target holds (Ops source target holds S)

/--
Operation families closed by the operation/invariant preservation closure.

This is the dual closure equation induced by the selected preservation relation;
it does not assert a lattice isomorphism.
-/
def ClosedOperationSet {State : Type u} {Operation : Type v} {Invariant : Type w}
    (source target : Operation -> State)
    (holds : Invariant -> State -> Prop)
    (T : Operation -> Prop) : Prop :=
  T = Ops source target holds (Inv source target holds T)

/--
The weak Galois correspondence induced by preservation.

It states exactly:

`T ⊆ Ops(S) ↔ S ⊆ Inv(T)`.
-/
theorem operationInvariant_galois
    {State : Type u} {Operation : Type v} {Invariant : Type w}
    (source target : Operation -> State)
    (holds : Invariant -> State -> Prop)
    (T : Operation -> Prop) (S : Invariant -> Prop) :
    PredicateSubset T (Ops source target holds S) ↔
      PredicateSubset S (Inv source target holds T) := by
  constructor
  · intro hT I hI op hOp
    exact hT op hOp I hI
  · intro hS op hOp I hI
    exact hS I hI op hOp

/--
A design pattern as a selected operation family and invariant family equipped
with the preservation closure law used by the weak Galois correspondence.

`nonConclusion` records claims intentionally left outside the package, such as
lattice isomorphism, complete classification, or unbounded preservation outside
the selected universe.
-/
structure DesignPattern
    {State : Type u} {Operation : Type v} {Invariant : Type w}
    (source target : Operation -> State)
    (holds : Invariant -> State -> Prop) where
  operationFamily : Operation -> Prop
  invariantFamily : Invariant -> Prop
  operationsPreserveInvariants :
    PredicateSubset operationFamily (Ops source target holds invariantFamily)
  invariantsPreservedByOperations :
    PredicateSubset invariantFamily (Inv source target holds operationFamily)
  nonConclusion : Prop

namespace DesignPattern

variable {State : Type u} {Operation : Type v} {Invariant : Type w}
variable {source target : Operation -> State}
variable {holds : Invariant -> State -> Prop}

/-- A design pattern directly provides the operation-to-invariant closure law. -/
theorem operations_subset_ops
    (P : DesignPattern source target holds) :
    PredicateSubset P.operationFamily
      (Ops source target holds P.invariantFamily) :=
  P.operationsPreserveInvariants

/-- A design pattern directly provides the invariant-to-operation closure law. -/
theorem invariants_subset_inv
    (P : DesignPattern source target holds) :
    PredicateSubset P.invariantFamily
      (Inv source target holds P.operationFamily) :=
  P.invariantsPreservedByOperations

/-- The two closure directions carried by a design pattern are equivalent data. -/
theorem closure_law
    (P : DesignPattern source target holds) :
    PredicateSubset P.operationFamily
      (Ops source target holds P.invariantFamily) ∧
    PredicateSubset P.invariantFamily
      (Inv source target holds P.operationFamily) :=
  ⟨P.operationsPreserveInvariants, P.invariantsPreservedByOperations⟩

/-- Design-pattern theorem packages explicitly record their non-conclusion clause. -/
def RecordsNonConclusions
    (P : DesignPattern source target holds) : Prop :=
  P.nonConclusion

/-- The recorded non-conclusion predicate is exactly the schema field. -/
theorem records_nonConclusions_iff
    (P : DesignPattern source target holds) :
    P.RecordsNonConclusions ↔ P.nonConclusion := by
  rfl

end DesignPattern

end Formal.Arch
