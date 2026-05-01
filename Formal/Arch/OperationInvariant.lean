import Formal.Arch.Operation

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

/-- `Ops` is antitone in the selected invariant family. -/
theorem Ops_antitone
    {State : Type u} {Operation : Type v} {Invariant : Type w}
    (source target : Operation -> State)
    (holds : Invariant -> State -> Prop)
    {S₁ S₂ : Invariant -> Prop}
    (hS : PredicateSubset S₁ S₂) :
    PredicateSubset (Ops source target holds S₂)
      (Ops source target holds S₁) := by
  intro op hOp I hI
  exact hOp I (hS I hI)

/-- `Inv` is antitone in the selected operation family. -/
theorem Inv_antitone
    {State : Type u} {Operation : Type v} {Invariant : Type w}
    (source target : Operation -> State)
    (holds : Invariant -> State -> Prop)
    {T₁ T₂ : Operation -> Prop}
    (hT : PredicateSubset T₁ T₂) :
    PredicateSubset (Inv source target holds T₂)
      (Inv source target holds T₁) := by
  intro I hI op hOp
  exact hI op (hT op hOp)

/-- Every selected invariant is preserved by the operations that preserve all selected invariants. -/
theorem inv_ops_extensive
    {State : Type u} {Operation : Type v} {Invariant : Type w}
    (source target : Operation -> State)
    (holds : Invariant -> State -> Prop)
    (S : Invariant -> Prop) :
    PredicateSubset S (Inv source target holds (Ops source target holds S)) := by
  intro I hI op hOp
  exact hOp I hI

/-- Every selected operation preserves all invariants preserved by the selected operations. -/
theorem ops_inv_extensive
    {State : Type u} {Operation : Type v} {Invariant : Type w}
    (source target : Operation -> State)
    (holds : Invariant -> State -> Prop)
    (T : Operation -> Prop) :
    PredicateSubset T (Ops source target holds (Inv source target holds T)) := by
  intro op hOp I hI
  exact hI op hOp

/-- The invariant closure `Inv ∘ Ops` is monotone. -/
theorem inv_ops_monotone
    {State : Type u} {Operation : Type v} {Invariant : Type w}
    (source target : Operation -> State)
    (holds : Invariant -> State -> Prop)
    {S₁ S₂ : Invariant -> Prop}
    (hS : PredicateSubset S₁ S₂) :
    PredicateSubset
      (Inv source target holds (Ops source target holds S₁))
      (Inv source target holds (Ops source target holds S₂)) := by
  exact Inv_antitone source target holds (Ops_antitone source target holds hS)

/-- The operation closure `Ops ∘ Inv` is monotone. -/
theorem ops_inv_monotone
    {State : Type u} {Operation : Type v} {Invariant : Type w}
    (source target : Operation -> State)
    (holds : Invariant -> State -> Prop)
    {T₁ T₂ : Operation -> Prop}
    (hT : PredicateSubset T₁ T₂) :
    PredicateSubset
      (Ops source target holds (Inv source target holds T₁))
      (Ops source target holds (Inv source target holds T₂)) := by
  exact Ops_antitone source target holds (Inv_antitone source target holds hT)

/-- The invariant closure `Inv ∘ Ops` is idempotent up to predicate extensionality. -/
theorem inv_ops_idempotent
    {State : Type u} {Operation : Type v} {Invariant : Type w}
    (source target : Operation -> State)
    (holds : Invariant -> State -> Prop)
    (S : Invariant -> Prop) :
    Inv source target holds
        (Ops source target holds (Inv source target holds (Ops source target holds S))) =
      Inv source target holds (Ops source target holds S) := by
  funext I
  apply propext
  constructor
  · intro hI op hOp
    exact hI op (ops_inv_extensive source target holds (Ops source target holds S) op hOp)
  · intro hI
    exact inv_ops_extensive source target holds
      (Inv source target holds (Ops source target holds S)) I hI

/-- The operation closure `Ops ∘ Inv` is idempotent up to predicate extensionality. -/
theorem ops_inv_idempotent
    {State : Type u} {Operation : Type v} {Invariant : Type w}
    (source target : Operation -> State)
    (holds : Invariant -> State -> Prop)
    (T : Operation -> Prop) :
    Ops source target holds
        (Inv source target holds (Ops source target holds (Inv source target holds T))) =
      Ops source target holds (Inv source target holds T) := by
  funext op
  apply propext
  constructor
  · intro hOp I hI
    exact hOp I (inv_ops_extensive source target holds (Inv source target holds T) I hI)
  · intro hOp
    exact ops_inv_extensive source target holds
      (Ops source target holds (Inv source target holds T)) op hOp

namespace OperationRoleSchema

variable {State : Type u} {BeforeWitness : Type v} {AfterWitness : Type w}

/--
Source map used when an `OperationRoleSchema` is viewed as an operation in the
operation/invariant Galois package.
-/
def operationInvariantSource
    (R : OperationRoleSchema State BeforeWitness AfterWitness) : State :=
  R.operation.source

/--
Target map used when an `OperationRoleSchema` is viewed as an operation in the
operation/invariant Galois package.
-/
def operationInvariantTarget
    (R : OperationRoleSchema State BeforeWitness AfterWitness) : State :=
  R.operation.target

/-- In this bridge, selected invariants are predicates on the same state universe. -/
def stateInvariantHolds (I : State -> Prop) (state : State) : Prop :=
  I state

/-- The Galois-package source map is exactly the underlying architecture operation source. -/
theorem operationInvariantSource_eq
    (R : OperationRoleSchema State BeforeWitness AfterWitness) :
    operationInvariantSource R = R.operation.source :=
  rfl

/-- The Galois-package target map is exactly the underlying architecture operation target. -/
theorem operationInvariantTarget_eq
    (R : OperationRoleSchema State BeforeWitness AfterWitness) :
    operationInvariantTarget R = R.operation.target :=
  rfl

/--
The bounded conclusion shape required to read a preserve role package as
selected-invariant preservation.

This is an explicit bridge assumption: a preserve role tag by itself still does
not imply preservation.
-/
def RoleConclusionIsSelectedPreservation
    (R : OperationRoleSchema State BeforeWitness AfterWitness) : Prop :=
  R.roleConclusion =
    (R.selectedInvariant R.operation.source ->
      R.selectedInvariant R.operation.target)

/--
A discharged preserve role package whose bounded conclusion is selected
source-to-target preservation yields `PreservesInvariant` for the selected
invariant.
-/
theorem preservesInvariant_of_discharged_preserve
    (R : OperationRoleSchema State BeforeWitness AfterWitness)
    (hRole : R.HasRole ArchitectureOperationRole.preserve)
    (hConclusion : R.RoleConclusionIsSelectedPreservation)
    (hDischarged : R.Discharged)
    (hAssumptions : R.AssumptionsHold) :
    PreservesInvariant operationInvariantSource operationInvariantTarget
      stateInvariantHolds R R.selectedInvariant := by
  have _hRoleBoundary : R.HasRole ArchitectureOperationRole.preserve := hRole
  intro hSource
  have h : R.roleConclusion := hDischarged hAssumptions
  rw [hConclusion] at h
  exact h hSource

/--
A discharged preserve role package is an `Ops` member for the singleton selected
invariant family associated with that package.
-/
theorem ops_mem_selectedInvariant_of_discharged_preserve
    (R : OperationRoleSchema State BeforeWitness AfterWitness)
    (hRole : R.HasRole ArchitectureOperationRole.preserve)
    (hConclusion : R.RoleConclusionIsSelectedPreservation)
    (hDischarged : R.Discharged)
    (hAssumptions : R.AssumptionsHold) :
    Ops operationInvariantSource operationInvariantTarget stateInvariantHolds
      (fun I => I = R.selectedInvariant) R := by
  intro I hI
  rw [hI]
  exact preservesInvariant_of_discharged_preserve R hRole hConclusion
    hDischarged hAssumptions

/--
If every selected operation role package preserves every selected invariant,
then the selected operation family is contained in `Ops(S)`.
-/
theorem operationFamily_subset_ops_of_preserves_selected
    (T : OperationRoleSchema State BeforeWitness AfterWitness -> Prop)
    (S : (State -> Prop) -> Prop)
    (hPreserves :
      ∀ R, T R ->
        ∀ I, S I ->
          PreservesInvariant operationInvariantSource operationInvariantTarget
            stateInvariantHolds R I) :
    PredicateSubset T
      (Ops operationInvariantSource operationInvariantTarget stateInvariantHolds S) := by
  intro R hR I hI
  exact hPreserves R hR I hI

end OperationRoleSchema

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
