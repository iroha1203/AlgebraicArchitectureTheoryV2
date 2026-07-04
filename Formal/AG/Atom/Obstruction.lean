import Formal.AG.Atom.Law

namespace AAT.AG

universe u

/-- I.定義8.1: an obstruction is a selected witness of law failure. -/
structure Obstruction {U : AtomCarrier.{u}} (L : Law U)
    (A : ArchitectureObject U) where
  Witness : Type u
  witness : Witness
  law_failure : ¬ L.holds A

/-- I.定義8.2: an obstruction circuit `O = (F_O, R_O, L)`. -/
structure ObstructionCircuit {U : AtomCarrier.{u}} (L : Law U)
    (A : ArchitectureObject U) where
  family : AtomFamily U
  relation : U.Atom -> U.Atom -> Prop
  relation_supported : ∀ {a b}, relation a b -> family.mem a ∧ family.mem b
  finite : Prop
  finite_holds : finite
  law_failure : ¬ L.holds A

/-- I.定義8.5: value domain for obstruction valuation readings. -/
structure ObstructionValueDomain (Value : Type u) where
  zero : Value
  positive : Value -> Prop
  zero_or_positive : ∀ value, value = zero ∨ positive value
  noCancellationAtZero : ∀ {value}, positive value -> value ≠ zero

/-- I.定義8.5: a law-indexed obstruction valuation `omega_L(A)`. -/
structure ObstructionValuation (U : AtomCarrier.{u}) (Value : Type u) where
  domain : ObstructionValueDomain Value
  omega : Law U -> ArchitectureObject U -> Value

/-- I.定義8.5: zero-reflecting aggregation over a selected law index type. -/
structure ZeroReflectingAggregation (Value : Type u)
    (domain : ObstructionValueDomain Value) (Index : Type u) where
  aggregate : (Index -> Value) -> Value
  zero_reflecting :
    ∀ values, aggregate values = domain.zero ↔ ∀ index, values index = domain.zero

/-- I.定義8.5: finite-list form of zero-reflecting aggregation. -/
structure ZeroReflectingListAggregation (Value : Type u)
    (domain : ObstructionValueDomain Value) where
  aggregate : List Value -> Value
  zero_reflecting :
    ∀ values, aggregate values = domain.zero ↔
      ∀ value, value ∈ values -> value = domain.zero

namespace LawUniverse

/-- I.定義8.5: the selected required-law index type used by aggregate valuation. -/
def RequiredIndex {U : AtomCarrier.{u}} (LU : LawUniverse U) : Type u :=
  { index : LU.Index // LU.Required index }

end LawUniverse

/-- I.定義8.5: a finite enumeration covering a selected index type. -/
structure FiniteIndexEnumeration (Index : Type u) where
  indices : List Index
  covers : ∀ index, index ∈ indices

namespace ZeroReflectingListAggregation

/--
I.定義8.5: lift a zero-reflecting finite-list aggregation to a selected finite
index aggregation using an explicit covering enumeration.
-/
def toIndexed {Value : Type u} {domain : ObstructionValueDomain Value}
    (listAggregation : ZeroReflectingListAggregation Value domain)
    {Index : Type u} (enumeration : FiniteIndexEnumeration Index) :
    ZeroReflectingAggregation Value domain Index where
  aggregate values := listAggregation.aggregate (enumeration.indices.map values)
  zero_reflecting values := by
    constructor
    · intro h index
      exact (listAggregation.zero_reflecting _).mp h (values index)
        (List.mem_map_of_mem (f := values) (enumeration.covers index))
    · intro h
      apply (listAggregation.zero_reflecting _).mpr
      intro value hmem
      rcases List.mem_map.mp hmem with ⟨index, _hindex, hvalue⟩
      rw [← hvalue]
      exact h index

end ZeroReflectingListAggregation

/-- I.定義8.5: aggregate selected per-law obstruction values. -/
def omegaU {U : AtomCarrier.{u}} {Value : Type u}
    (valuation : ObstructionValuation U Value) (LU : LawUniverse U)
    (aggregation :
      ZeroReflectingAggregation Value valuation.domain LU.RequiredIndex)
    (A : ArchitectureObject U) : Value :=
  aggregation.aggregate (fun index => valuation.omega (LU.law index.1) A)

/-- I.定義8.5: `omegaU = 0` is exactly zero on each required law index. -/
theorem omegaU_zero_iff_required {U : AtomCarrier.{u}} {Value : Type u}
    (valuation : ObstructionValuation U Value) (LU : LawUniverse U)
    (aggregation :
      ZeroReflectingAggregation Value valuation.domain LU.RequiredIndex)
    (A : ArchitectureObject U) :
    omegaU valuation LU aggregation A = valuation.domain.zero ↔
      ∀ index : LU.RequiredIndex,
        valuation.omega (LU.law index.1) A = valuation.domain.zero :=
  aggregation.zero_reflecting _

namespace ObstructionCircuit

/--
PRD-R I-3: concrete finite-support reading for an obstruction circuit. New
finite examples should provide this explicit list cover in addition to any
legacy marker required by frozen declarations.
-/
def ListFinite {U : AtomCarrier.{u}} {L : Law U}
    {A : ArchitectureObject U} (O : ObstructionCircuit L A) : Prop :=
  O.family.ListFinite

/-- I.定義8.2: the relation of an obstruction circuit is supported by its family. -/
theorem relation_supported_holds {U : AtomCarrier.{u}} {L : Law U}
    {A : ArchitectureObject U} (O : ObstructionCircuit L A)
    {a b : U.Atom} (h : O.relation a b) :
    O.family.mem a ∧ O.family.mem b :=
  O.relation_supported h

/-- I.定義8.2: the finite marker recorded by an obstruction circuit. -/
theorem finite_marker {U : AtomCarrier.{u}} {L : Law U}
    {A : ArchitectureObject U} (O : ObstructionCircuit L A) :
    O.finite :=
  O.finite_holds

/-- PRD-R I-3: expose the explicit atom cover carried by list-finite evidence. -/
theorem listFinite_has_cover {U : AtomCarrier.{u}} {L : Law U}
    {A : ArchitectureObject U} (O : ObstructionCircuit L A)
    (h : O.ListFinite) :
    ∃ atoms : List U.Atom, ∀ atom, O.family.mem atom -> atom ∈ atoms :=
  h

/-- I.定義8.2: an obstruction circuit records failure of its selected law. -/
theorem law_failure_holds {U : AtomCarrier.{u}} {L : Law U}
    {A : ArchitectureObject U} (O : ObstructionCircuit L A) :
    ¬ L.holds A :=
  O.law_failure

end ObstructionCircuit

namespace ObstructionValueDomain

/-- I.定義8.5: `Nat` as count-valued obstruction readings. -/
def nat : ObstructionValueDomain Nat where
  zero := 0
  positive value := 0 < value
  zero_or_positive value := by
    cases Nat.eq_zero_or_pos value with
    | inl h => exact Or.inl h
    | inr h => exact Or.inr h
  noCancellationAtZero h := by
    exact Nat.ne_of_gt h

/-- I.定義8.5: `Bool` as obstruction-present readings. -/
def bool : ObstructionValueDomain Bool where
  zero := false
  positive value := value = true
  zero_or_positive value := by
    cases value <;> simp
  noCancellationAtZero h := by
    simp [h]

/-- I.定義8.5: a nonnegative weight represented by a natural magnitude. -/
structure NonnegativeWeight where
  value : Nat
  deriving DecidableEq

namespace NonnegativeWeight

/-- The zero nonnegative weight. -/
def zero : NonnegativeWeight :=
  ⟨0⟩

/-- The supremum of two nonnegative weights. -/
def sup (a b : NonnegativeWeight) : NonnegativeWeight :=
  ⟨Nat.max a.value b.value⟩

end NonnegativeWeight

/-- I.定義8.5: nonnegative weights as obstruction-valued readings. -/
def nonnegativeWeight : ObstructionValueDomain NonnegativeWeight where
  zero := NonnegativeWeight.zero
  positive value := 0 < value.value
  zero_or_positive value := by
    cases Nat.eq_zero_or_pos value.value with
    | inl h =>
        left
        cases value
        simp [NonnegativeWeight.zero] at h ⊢
        exact h
    | inr h =>
        exact Or.inr h
  noCancellationAtZero h := by
    intro hzero
    cases hzero
    exact Nat.lt_irrefl 0 h

end ObstructionValueDomain

namespace ObstructionAggregation

/-- I.定義8.5: count aggregation by finite sum. -/
def natSum : List Nat -> Nat
  | [] => 0
  | value :: values => value + natSum values

/-- I.定義8.5: boolean aggregation by finite disjunction. -/
def boolOr : List Bool -> Bool
  | [] => false
  | value :: values => value || boolOr values

/-- I.定義8.5: nonnegative-weight aggregation by finite supremum. -/
def weightSup :
    List ObstructionValueDomain.NonnegativeWeight ->
      ObstructionValueDomain.NonnegativeWeight
  | [] => ObstructionValueDomain.NonnegativeWeight.zero
  | value :: values =>
      ObstructionValueDomain.NonnegativeWeight.sup value (weightSup values)

/-- I.定義8.5: count sums are zero-reflecting. -/
theorem natSum_eq_zero_iff (values : List Nat) :
    natSum values = 0 ↔ ∀ value, value ∈ values -> value = 0 := by
  induction values with
  | nil =>
      simp [natSum]
  | cons value values ih =>
      constructor
      · intro h candidate hmem
        have hpair := Nat.add_eq_zero_iff.mp h
        cases hmem with
        | head =>
            exact hpair.1
        | tail _ htail =>
            exact (ih.mp hpair.2) candidate htail
      · intro h
        have hvalue : value = 0 := h value (by simp)
        have hvalues : natSum values = 0 := by
          apply ih.mpr
          intro candidate hmem
          exact h candidate (by simp [hmem])
        simp [natSum, hvalue, hvalues]

/-- I.定義8.5: boolean disjunction is zero-reflecting. -/
theorem boolOr_eq_false_iff (values : List Bool) :
    boolOr values = false ↔ ∀ value, value ∈ values -> value = false := by
  induction values with
  | nil =>
      simp [boolOr]
  | cons value values ih =>
      cases value <;> simp [boolOr, ih]

/-- I.定義8.5: finite sup of nonnegative weights is zero-reflecting. -/
theorem weightSup_eq_zero_iff
    (values : List ObstructionValueDomain.NonnegativeWeight) :
    weightSup values = ObstructionValueDomain.NonnegativeWeight.zero ↔
      ∀ value, value ∈ values ->
        value = ObstructionValueDomain.NonnegativeWeight.zero := by
  induction values with
  | nil =>
      simp [weightSup]
  | cons value values ih =>
      constructor
      · intro h candidate hmem
        have hmax :
            Nat.max value.value (weightSup values).value = 0 := by
          exact congrArg ObstructionValueDomain.NonnegativeWeight.value h
        have hleft : value.value = 0 := by
          exact Nat.eq_zero_of_le_zero (by
            simpa [hmax] using Nat.le_max_left value.value (weightSup values).value)
        have hright : (weightSup values).value = 0 := by
          exact Nat.eq_zero_of_le_zero (by
            simpa [hmax] using Nat.le_max_right value.value (weightSup values).value)
        cases hmem with
        | head =>
            cases value
            simp [ObstructionValueDomain.NonnegativeWeight.zero] at hleft ⊢
            exact hleft
        | tail _ htail =>
            have hweight :
                weightSup values =
                  ObstructionValueDomain.NonnegativeWeight.zero := by
              cases hws : weightSup values with
              | mk weight =>
                  have hweight_zero : weight = 0 := by
                    simpa [hws] using hright
                  simp [ObstructionValueDomain.NonnegativeWeight.zero,
                    hweight_zero]
            exact (ih.mp hweight) candidate htail
      · intro h
        have hvalue :
            value = ObstructionValueDomain.NonnegativeWeight.zero :=
          h value (by simp)
        have hvalues :
            weightSup values = ObstructionValueDomain.NonnegativeWeight.zero := by
          apply ih.mpr
          intro candidate hmem
          exact h candidate (by simp [hmem])
        have hvalueNat : value.value = 0 := by
          exact congrArg ObstructionValueDomain.NonnegativeWeight.value hvalue
        have hvaluesNat : (weightSup values).value = 0 := by
          exact congrArg ObstructionValueDomain.NonnegativeWeight.value hvalues
        simp [weightSup, ObstructionValueDomain.NonnegativeWeight.zero,
          ObstructionValueDomain.NonnegativeWeight.sup, hvalueNat, hvaluesNat]

/-- I.定義8.5: zero-reflecting list aggregation for counts. -/
def natSumListAggregation :
    ZeroReflectingListAggregation Nat ObstructionValueDomain.nat where
  aggregate := natSum
  zero_reflecting := natSum_eq_zero_iff

/-- I.定義8.5: zero-reflecting list aggregation for booleans. -/
def boolOrListAggregation :
    ZeroReflectingListAggregation Bool ObstructionValueDomain.bool where
  aggregate := boolOr
  zero_reflecting := boolOr_eq_false_iff

/-- I.定義8.5: zero-reflecting list aggregation for nonnegative weights. -/
def weightSupListAggregation :
    ZeroReflectingListAggregation ObstructionValueDomain.NonnegativeWeight
      ObstructionValueDomain.nonnegativeWeight where
  aggregate := weightSup
  zero_reflecting := weightSup_eq_zero_iff

end ObstructionAggregation

end AAT.AG
