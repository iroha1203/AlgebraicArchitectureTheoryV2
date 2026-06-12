import Formal.AG.Atom.ArchitectureObject

namespace AAT.AG

universe u

/-- I.定義6.1: function-valued invariant on architecture objects. -/
structure FunctionInvariant (U : AtomCarrier.{u}) where
  Value : Type u
  evaluate : ArchitectureObject U -> Value

/-- I.定義6.1: predicate-valued invariant on architecture objects. -/
structure PredicateInvariant (U : AtomCarrier.{u}) where
  holds : ArchitectureObject U -> Prop

/-- I.定義6.1: an invariant is either function-valued or predicate-valued. -/
inductive Invariant (U : AtomCarrier.{u}) where
  | function : FunctionInvariant U -> Invariant U
  | predicate : PredicateInvariant U -> Invariant U

/-- I.定義6.2: a family of invariants to preserve together. -/
structure InvariantFamily (U : AtomCarrier.{u}) where
  Index : Type u
  invariant : Index -> Invariant U

namespace Invariant

/-- I.定義6.3: equality-form preservation `I(A) = I(B)`. -/
def EqualityPreserved {U : AtomCarrier.{u}} (I : FunctionInvariant U)
    (A B : ArchitectureObject U) : Prop :=
  I.evaluate A = I.evaluate B

/-- I.定義6.3: order-form preservation `I(B) <= I(A)`. -/
def OrderPreserved {U : AtomCarrier.{u}} (I : FunctionInvariant U)
    (le : I.Value -> I.Value -> Prop) (A B : ArchitectureObject U) : Prop :=
  le (I.evaluate B) (I.evaluate A)

/-- I.定義6.3: predicate-form preservation from source to target. -/
def PredicatePreserved {U : AtomCarrier.{u}} (P : PredicateInvariant U)
    (A B : ArchitectureObject U) : Prop :=
  P.holds A -> P.holds B

/-- I.定義6.3: equality preservation is exactly equality of invariant values. -/
theorem equalityPreserved_apply {U : AtomCarrier.{u}} {I : FunctionInvariant U}
    {A B : ArchitectureObject U} (h : EqualityPreserved I A B) :
    I.evaluate A = I.evaluate B :=
  h

/-- I.定義6.3: order preservation is exactly the selected order comparison. -/
theorem orderPreserved_apply {U : AtomCarrier.{u}} {I : FunctionInvariant U}
    {le : I.Value -> I.Value -> Prop} {A B : ArchitectureObject U}
    (h : OrderPreserved I le A B) :
    le (I.evaluate B) (I.evaluate A) :=
  h

/-- I.定義6.3: predicate preservation transports a source predicate witness. -/
theorem predicatePreserved_apply {U : AtomCarrier.{u}} {P : PredicateInvariant U}
    {A B : ArchitectureObject U} (h : PredicatePreserved P A B)
    (hA : P.holds A) :
    P.holds B :=
  h hA

end Invariant

namespace InvariantFamily

/-- I.定義6.2: read the invariant indexed by a family member. -/
def get {U : AtomCarrier.{u}} (family : InvariantFamily U)
    (index : family.Index) : Invariant U :=
  family.invariant index

/-- I.定義6.2: the accessor returns the selected invariant. -/
theorem get_eq {U : AtomCarrier.{u}} (family : InvariantFamily U)
    (index : family.Index) :
    family.get index = family.invariant index :=
  rfl

end InvariantFamily

end AAT.AG
