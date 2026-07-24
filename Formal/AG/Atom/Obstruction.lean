import Formal.AG.Equation.Basic

namespace AAT.AG

universe u

/--
I.定義8.1: semantic obstruction is failure of the selected equation on the
selected architecture object.
-/
def EquationSemanticObstruction
    {U : AtomCarrier.{u}} {A₀ : ArchitectureObject U}
    {C : Site.ContextPreorderCategory A₀}
    (E : ArchitecturalEquationSystem C) (index : E.Index)
    (A : ArchitectureObject U) : Prop :=
  ¬ E.EquationHolds index A

namespace EquationSemanticObstruction

/-- Semantic obstruction is exactly failure of residual vanishing. -/
theorem iff_not_equationHolds
    {U : AtomCarrier.{u}} {A₀ : ArchitectureObject U}
    {C : Site.ContextPreorderCategory A₀}
    (E : ArchitecturalEquationSystem C) (index : E.Index)
    (A : ArchitectureObject U) :
    EquationSemanticObstruction E index A ↔ ¬ E.EquationHolds index A :=
  Iff.rfl

end EquationSemanticObstruction

/-- SD1: a finite circuit query over Atom-level configuration data. -/
inductive CircuitQuery (U : AtomCarrier.{u}) where
  | atomPresent (a : U.Atom)
  | relationPresent (a b : U.Atom)
  | identificationPresent (a b : U.Atom)

/-- SD1: the semantic reading of a circuit query on an architecture object. -/
def CircuitQuery.Holds {U : AtomCarrier.{u}} (q : CircuitQuery U)
    (A : ArchitectureObject U) : Prop :=
  match q with
  | .atomPresent a => A.configuration.family.mem a
  | .relationPresent a b =>
      A.configuration.family.mem a ∧
      A.configuration.family.mem b ∧
      A.configuration.relation a b
  | .identificationPresent a b =>
      A.configuration.family.mem a ∧
      A.configuration.family.mem b ∧
      A.configuration.identification a b

namespace CircuitQuery

/-- An atom-presence query holds exactly when the atom belongs to the object family. -/
theorem atomPresent_holds_iff {U : AtomCarrier.{u}} (a : U.Atom)
    (A : ArchitectureObject U) :
    (CircuitQuery.atomPresent a).Holds A ↔ A.configuration.family.mem a :=
  Iff.rfl

/-- A relation query exposes its two support memberships and selected relation. -/
theorem relationPresent_holds_iff {U : AtomCarrier.{u}} (a b : U.Atom)
    (A : ArchitectureObject U) :
    (CircuitQuery.relationPresent a b).Holds A ↔
      A.configuration.family.mem a ∧ A.configuration.family.mem b ∧
        A.configuration.relation a b :=
  Iff.rfl

/-- An identification query exposes its support memberships and selected identification. -/
theorem identificationPresent_holds_iff {U : AtomCarrier.{u}} (a b : U.Atom)
    (A : ArchitectureObject U) :
    (CircuitQuery.identificationPresent a b).Holds A ↔
      A.configuration.family.mem a ∧ A.configuration.family.mem b ∧
        A.configuration.identification a b :=
  Iff.rfl

end CircuitQuery

/--
SD1: a finite signed query pattern for an obstruction circuit.

Implementation notes: signed queries are finite data; matching remains a
separate predicate on architecture objects.  Storing an object or a law-failure
proof in the datum was rejected because it would repackage the desired
semantic conclusion.
-/
structure FiniteCircuitDatum (U : AtomCarrier.{u}) where
  /-- The finite list of queries paired with their expected Boolean polarity. -/
  queries : List (CircuitQuery U × Bool)

/-- SD1: every signed query in the datum has the expected reading on the object. -/
def FiniteCircuitDatum.Matches {U : AtomCarrier.{u}}
    (Q : FiniteCircuitDatum U) (A : ArchitectureObject U) : Prop :=
  ∀ query expected, (query, expected) ∈ Q.queries ->
    (query.Holds A ↔ expected = true)

/--
SD1: finite-template detector syntax. Its constructors contain only finite
data, exact templates, and finite disjunction.
-/
inductive CircuitDetectorCode (U : AtomCarrier.{u}) where
  | reject
  | exact (pattern : FiniteCircuitDatum U)
  | any (left right : CircuitDetectorCode U)

/-- SD1: evaluate finite-template detector syntax on a finite circuit datum. -/
noncomputable def CircuitDetectorCode.eval {U : AtomCarrier.{u}}
    (code : CircuitDetectorCode U) (Q : FiniteCircuitDatum U) : Bool := by
  classical
  exact match code with
    | .reject => false
    | .exact pattern => if pattern = Q then true else false
    | .any left right => left.eval Q || right.eval Q

namespace CircuitDetectorCode

/-- The rejecting detector evaluates to false on every finite datum. -/
@[simp]
theorem eval_reject {U : AtomCarrier.{u}} (Q : FiniteCircuitDatum U) :
    (CircuitDetectorCode.reject : CircuitDetectorCode U).eval Q = false := by
  simp [CircuitDetectorCode.eval]

/-- An exact detector accepts precisely its stored finite template. -/
theorem eval_exact_eq_true_iff {U : AtomCarrier.{u}}
    (pattern Q : FiniteCircuitDatum U) :
    (CircuitDetectorCode.exact pattern).eval Q = true ↔ pattern = Q := by
  classical
  simp [CircuitDetectorCode.eval]

/-- Finite disjunction accepts precisely when one of its detector branches accepts. -/
theorem eval_any_eq_true_iff {U : AtomCarrier.{u}}
    (left right : CircuitDetectorCode U) (Q : FiniteCircuitDatum U) :
    (CircuitDetectorCode.any left right).eval Q = true ↔
      left.eval Q = true ∨ right.eval Q = true := by
  simp [CircuitDetectorCode.eval]

end CircuitDetectorCode

/--
Equation-indexed finite detector code.

Implementation notes: this structure carries finite syntax only. Semantic
soundness is the separate predicate `EquationCircuitReading.Sound`, so a
generic core never stores equation failure as a field of its detector data.
-/
structure EquationCircuitReading
    {U : AtomCarrier.{u}} {A₀ : ArchitectureObject U}
    {C : Site.ContextPreorderCategory A₀}
  (E : ArchitecturalEquationSystem C) where
  /-- The finite detector syntax selected for each equation. -/
  code : E.Index -> CircuitDetectorCode U

namespace EquationCircuitReading

variable {U : AtomCarrier.{u}} {A₀ : ArchitectureObject U}
variable {C : Site.ContextPreorderCategory A₀}
variable {E : ArchitecturalEquationSystem C}

/-- Boolean acceptance of a finite datum by the selected equation detector. -/
noncomputable def accepts (R : EquationCircuitReading E)
    (index : E.Index) (datum : FiniteCircuitDatum U) : Bool :=
  (R.code index).eval datum

/-- Accepted matching circuit data for an object and equation index. -/
def Circuit (R : EquationCircuitReading E) (object : ArchitectureObject U)
    (index : E.Index) : Type u :=
  {datum : FiniteCircuitDatum U //
    datum.Matches object ∧ R.accepts index datum = true}

/--
Direction hypothesis for an equation detector: every accepted matching datum
refutes the indexed residual-vanishing equation. Concrete fixtures must prove
this predicate from their residual and query semantics.
-/
def Sound (R : EquationCircuitReading E) : Prop :=
  ∀ (index : E.Index) (object : ArchitectureObject U)
    (datum : FiniteCircuitDatum U),
      datum.Matches object -> (R.code index).eval datum = true ->
        ¬ E.EquationHolds index object

/-- Completeness for required equation failure, kept separate from the reading data. -/
def RequiredComplete (R : EquationCircuitReading E) : Prop :=
  ∀ (object : ArchitectureObject U) (index : E.Index), E.Required index ->
    ¬ E.EquationHolds index object -> Nonempty (R.Circuit object index)

/-- Equation circuit readings agree when their detector families agree. -/
@[ext]
theorem ext {R S : EquationCircuitReading E} (hcode : R.code = S.code) : R = S := by
  cases R
  cases S
  cases hcode
  rfl

/-- Acceptance is evaluation of the selected finite detector code. -/
theorem accepts_eq_eval (R : EquationCircuitReading E) (index : E.Index)
    (datum : FiniteCircuitDatum U) :
    R.accepts index datum = (R.code index).eval datum :=
  rfl

/-- A rejecting equation detector accepts no finite datum. -/
theorem accepts_eq_false_of_code_reject (R : EquationCircuitReading E)
    (index : E.Index) (datum : FiniteCircuitDatum U)
    (hcode : R.code index = .reject) :
    R.accepts index datum = false := by
  rw [accepts_eq_eval, hcode]
  exact CircuitDetectorCode.eval_reject datum

/-- An exact equation detector accepts precisely its selected template. -/
theorem accepts_eq_true_iff_of_code_exact (R : EquationCircuitReading E)
    (index : E.Index) (pattern datum : FiniteCircuitDatum U)
    (hcode : R.code index = .exact pattern) :
    R.accepts index datum = true ↔ pattern = datum := by
  rw [accepts_eq_eval, hcode]
  exact CircuitDetectorCode.eval_exact_eq_true_iff pattern datum

/-- A disjunctive equation detector accepts when either branch accepts. -/
theorem accepts_eq_true_iff_of_code_any (R : EquationCircuitReading E)
    (index : E.Index) (left right : CircuitDetectorCode U)
    (datum : FiniteCircuitDatum U)
    (hcode : R.code index = .any left right) :
    R.accepts index datum = true ↔
      left.eval datum = true ∨ right.eval datum = true := by
  rw [accepts_eq_eval, hcode]
  exact CircuitDetectorCode.eval_any_eq_true_iff left right datum

/-- An accepted matching circuit refutes its indexed equation. -/
theorem circuit_sound (R : EquationCircuitReading E)
    (hSound : R.Sound)
    (object : ArchitectureObject U) (index : E.Index)
    (circuit : R.Circuit object index) :
    ¬ E.EquationHolds index object :=
  hSound index object circuit.1 circuit.2.1 circuit.2.2

end EquationCircuitReading

/--
Core equation reading on the context category selected for one generated
architecture object.
-/
structure EquationReading {U : AtomCarrier.{u}} (object : ArchitectureObject U) where
  /-- The readable context preorder selected for the generated object. -/
  contextPreorder : Site.ContextPreorderCategory object
  /-- The architectural equation system on that context preorder. -/
  equationSystem : ArchitecturalEquationSystem contextPreorder
  /-- Finite obstruction circuits indexed by the same equation system. -/
  circuits : EquationCircuitReading equationSystem
  /-- Admissibility proof that accepted matching circuits refute their equations. -/
  circuitSound : circuits.Sound

namespace FiniteCircuitDatum

/-- Two finite circuit data are equal when their signed query lists are equal. -/
@[ext]
theorem ext {U : AtomCarrier.{u}} {Q R : FiniteCircuitDatum U}
    (hqueries : Q.queries = R.queries) : Q = R := by
  cases Q
  cases R
  cases hqueries
  rfl

/-- A matching datum exposes the expected reading of each query it contains. -/
theorem holds_iff_of_matches {U : AtomCarrier.{u}}
    {Q : FiniteCircuitDatum U} {A : ArchitectureObject U}
    (h : Q.Matches A) {query : CircuitQuery U} {expected : Bool}
    (hquery : (query, expected) ∈ Q.queries) :
    query.Holds A ↔ expected = true :=
  h query expected hquery

end FiniteCircuitDatum

/-- I.定義8.5: value domain for obstruction valuation readings. -/
structure ObstructionValueDomain (Value : Type u) where
  zero : Value
  positive : Value -> Prop
  zero_or_positive : ∀ value, value = zero ∨ positive value
  noCancellationAtZero : ∀ {value}, positive value -> value ≠ zero

/--
I.定義8.5: an equation-indexed obstruction valuation `omega_{E,i}(A)`.

Implementation notes: the valuation receives an equation index from the same
`ArchitecturalEquationSystem` that determines fulfillment.  A predicate-valued
law argument was rejected because it loses the residual and role provenance.
-/
structure EquationObstructionValuation
    {U : AtomCarrier.{u}} {A₀ : ArchitectureObject U}
    {C : Site.ContextPreorderCategory A₀}
    (E : ArchitecturalEquationSystem C) (Value : Type u) where
  domain : ObstructionValueDomain Value
  omega : E.Index -> ArchitectureObject U -> Value

/-- I.定義8.5: zero-reflecting aggregation over a selected index type. -/
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

/-- I.定義8.5: aggregate the obstruction values of all required equations. -/
def omegaE
    {U : AtomCarrier.{u}} {A₀ : ArchitectureObject U}
    {C : Site.ContextPreorderCategory A₀}
    {E : ArchitecturalEquationSystem C} {Value : Type u}
    (valuation : EquationObstructionValuation E Value)
    (aggregation :
      ZeroReflectingAggregation Value valuation.domain E.RequiredIndex)
    (A : ArchitectureObject U) : Value :=
  aggregation.aggregate (fun index => valuation.omega index.1 A)

/-- I.定義8.5: `omegaE = 0` exactly when every required value is zero. -/
theorem omegaE_zero_iff_required
    {U : AtomCarrier.{u}} {A₀ : ArchitectureObject U}
    {C : Site.ContextPreorderCategory A₀}
    {E : ArchitecturalEquationSystem C} {Value : Type u}
    (valuation : EquationObstructionValuation E Value)
    (aggregation :
      ZeroReflectingAggregation Value valuation.domain E.RequiredIndex)
    (A : ArchitectureObject U) :
    omegaE valuation aggregation A = valuation.domain.zero ↔
      ∀ index : E.RequiredIndex,
        valuation.omega index.1 A = valuation.domain.zero :=
  aggregation.zero_reflecting _

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
