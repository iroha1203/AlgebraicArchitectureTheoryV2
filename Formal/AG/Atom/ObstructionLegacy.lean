import Formal.AG.Atom.Obstruction
import Formal.AG.Equation.Legacy

/-!
# One-way legacy circuit displays

This compatibility leaf converts equation-indexed circuit readings into the
older law-indexed display API.  Standard core and site modules depend only on
`EquationCircuitReading` and `EquationReading` from `Atom.Obstruction`.
-/

namespace AAT.AG

universe u

/-- Compatibility semantic obstruction for a predicate-valued law display. -/
def SemanticObstruction {U : AtomCarrier.{u}} (L : Law U)
    (A : ArchitectureObject U) : Prop :=
  ¬ L.holds A

namespace SemanticObstruction

/-- Compatibility characterization of predicate-valued law failure. -/
theorem iff_not_holds {U : AtomCarrier.{u}} (L : Law U)
    (A : ArchitectureObject U) :
    SemanticObstruction L A ↔ ¬ L.holds A :=
  Iff.rfl

end SemanticObstruction

/-- Compatibility law-indexed finite detector code with semantic soundness. -/
structure CircuitReading {U : AtomCarrier.{u}} (LU : LawUniverse U) where
  code : (i : LU.Index) -> CircuitDetectorCode U
  sound : ∀ (i : LU.Index) (A : ArchitectureObject U)
    (Q : FiniteCircuitDatum U),
      Q.Matches A -> (code i).eval Q = true ->
        ¬ (LU.law i).holds A

/-- Compatibility Boolean acceptance of a finite datum. -/
noncomputable def CircuitReading.accepts {U : AtomCarrier.{u}}
    {LU : LawUniverse U} (R : CircuitReading LU)
    (i : LU.Index) (Q : FiniteCircuitDatum U) : Bool :=
  (R.code i).eval Q

/-- Compatibility accepted matching circuit data. -/
def CircuitReading.Circuit {U : AtomCarrier.{u}} {LU : LawUniverse U}
    (R : CircuitReading LU) (A : ArchitectureObject U)
    (i : LU.Index) : Type u :=
  {Q : FiniteCircuitDatum U // Q.Matches A ∧ R.accepts i Q = true}

/-- Compatibility completeness condition for required predicate-valued laws. -/
def CircuitReading.RequiredComplete {U : AtomCarrier.{u}}
    {LU : LawUniverse U} (R : CircuitReading LU) : Prop :=
  ∀ (A : ArchitectureObject U) (i : LU.Index), LU.Required i ->
    ¬ (LU.law i).holds A -> Nonempty (R.Circuit A i)

/-- Compatibility law universe equipped with its finite circuit reading. -/
structure LawReading (U : AtomCarrier.{u}) where
  lawUniverse : LawUniverse U
  circuits : CircuitReading lawUniverse

namespace CircuitReading

/-- Compatibility circuit readings agree when their detector families agree. -/
@[ext]
theorem ext {U : AtomCarrier.{u}} {LU : LawUniverse U}
    {R S : CircuitReading LU} (hcode : R.code = S.code) : R = S := by
  cases R
  cases S
  cases hcode
  rfl

/-- Compatibility acceptance is evaluation of the detector code. -/
theorem accepts_eq_eval {U : AtomCarrier.{u}} {LU : LawUniverse U}
    (R : CircuitReading LU) (i : LU.Index) (Q : FiniteCircuitDatum U) :
    R.accepts i Q = (R.code i).eval Q :=
  rfl

/-- Compatibility acceptance exposes the detector equality. -/
theorem accepts_eq_true_iff_eval {U : AtomCarrier.{u}} {LU : LawUniverse U}
    (R : CircuitReading LU) (i : LU.Index) (Q : FiniteCircuitDatum U) :
    R.accepts i Q = true ↔ (R.code i).eval Q = true :=
  Iff.rfl

/-- A rejecting compatibility detector accepts no finite datum. -/
theorem accepts_eq_false_of_code_reject {U : AtomCarrier.{u}}
    {LU : LawUniverse U} (R : CircuitReading LU) (i : LU.Index)
    (Q : FiniteCircuitDatum U) (hcode : R.code i = .reject) :
    R.accepts i Q = false := by
  rw [accepts_eq_eval, hcode]
  exact CircuitDetectorCode.eval_reject Q

/-- An exact compatibility detector accepts precisely its template. -/
theorem accepts_eq_true_iff_of_code_exact {U : AtomCarrier.{u}}
    {LU : LawUniverse U} (R : CircuitReading LU) (i : LU.Index)
    (pattern Q : FiniteCircuitDatum U) (hcode : R.code i = .exact pattern) :
    R.accepts i Q = true ↔ pattern = Q := by
  rw [accepts_eq_eval, hcode]
  exact CircuitDetectorCode.eval_exact_eq_true_iff pattern Q

/-- A disjunctive compatibility detector accepts when either branch accepts. -/
theorem accepts_eq_true_iff_of_code_any {U : AtomCarrier.{u}}
    {LU : LawUniverse U} (R : CircuitReading LU) (i : LU.Index)
    (left right : CircuitDetectorCode U) (Q : FiniteCircuitDatum U)
    (hcode : R.code i = .any left right) :
    R.accepts i Q = true ↔ left.eval Q = true ∨ right.eval Q = true := by
  rw [accepts_eq_eval, hcode]
  exact CircuitDetectorCode.eval_any_eq_true_iff left right Q

/-- An accepted compatibility circuit refutes its predicate-valued law. -/
theorem circuit_sound {U : AtomCarrier.{u}} {LU : LawUniverse U}
    (R : CircuitReading LU) (A : ArchitectureObject U) (i : LU.Index)
    (c : R.Circuit A i) : ¬ (LU.law i).holds A :=
  R.sound i A c.1 c.2.1 c.2.2

end CircuitReading

namespace LawReading

/-- Compatibility law readings agree when both dependent fields agree. -/
@[ext]
theorem ext {U : AtomCarrier.{u}} {R S : LawReading U}
    (huniverse : R.lawUniverse = S.lawUniverse)
    (hcircuits : HEq R.circuits S.circuits) : R = S := by
  cases R
  cases S
  cases huniverse
  cases hcircuits
  rfl

end LawReading

/-- Compatibility witness package for a predicate-valued law failure. -/
structure Obstruction {U : AtomCarrier.{u}} (L : Law U)
    (A : ArchitectureObject U) where
  Witness : Type u
  witness : Witness
  law_failure : ¬ L.holds A

/-- Compatibility finite-support package carrying predicate-valued law failure. -/
structure ObstructionCircuit {U : AtomCarrier.{u}} (L : Law U)
    (A : ArchitectureObject U) where
  family : AtomFamily U
  relation : U.Atom -> U.Atom -> Prop
  relation_supported : ∀ {a b}, relation a b -> family.mem a ∧ family.mem b
  finite : Prop
  finite_holds : finite
  law_failure : ¬ L.holds A

/-- Compatibility predicate-valued-law obstruction valuation. -/
structure ObstructionValuation (U : AtomCarrier.{u}) (Value : Type u) where
  domain : ObstructionValueDomain Value
  omega : Law U -> ArchitectureObject U -> Value

namespace LawUniverse

/-- Required-law subtype used by the compatibility aggregate valuation. -/
def RequiredIndex {U : AtomCarrier.{u}} (LU : LawUniverse U) : Type u :=
  { index : LU.Index // LU.Required index }

end LawUniverse

/-- Aggregate the compatibility per-law obstruction values. -/
def omegaU {U : AtomCarrier.{u}} {Value : Type u}
    (valuation : ObstructionValuation U Value) (LU : LawUniverse U)
    (aggregation :
      ZeroReflectingAggregation Value valuation.domain LU.RequiredIndex)
    (A : ArchitectureObject U) : Value :=
  aggregation.aggregate (fun index => valuation.omega (LU.law index.1) A)

/-- Compatibility aggregate zero is pointwise zero on every required law. -/
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

/-- Explicit list-finiteness of a compatibility obstruction circuit. -/
def ListFinite {U : AtomCarrier.{u}} {L : Law U}
    {A : ArchitectureObject U} (O : ObstructionCircuit L A) : Prop :=
  O.family.ListFinite

/-- A compatibility circuit relation is supported by its selected family. -/
theorem relation_supported_holds {U : AtomCarrier.{u}} {L : Law U}
    {A : ArchitectureObject U} (O : ObstructionCircuit L A)
    {a b : U.Atom} (h : O.relation a b) :
    O.family.mem a ∧ O.family.mem b :=
  O.relation_supported h

/-- Expose the compatibility circuit's finite marker. -/
theorem finite_marker {U : AtomCarrier.{u}} {L : Law U}
    {A : ArchitectureObject U} (O : ObstructionCircuit L A) :
    O.finite :=
  O.finite_holds

/-- Expose an explicit atom cover from list-finite evidence. -/
theorem listFinite_has_cover {U : AtomCarrier.{u}} {L : Law U}
    {A : ArchitectureObject U} (O : ObstructionCircuit L A)
    (h : O.ListFinite) :
    ∃ atoms : List U.Atom, ∀ atom, O.family.mem atom -> atom ∈ atoms :=
  h

/-- Expose predicate-valued law failure stored by the compatibility circuit. -/
theorem law_failure_holds {U : AtomCarrier.{u}} {L : Law U}
    {A : ArchitectureObject U} (O : ObstructionCircuit L A) :
    ¬ L.holds A :=
  O.law_failure

end ObstructionCircuit

namespace EquationCircuitReading

variable {U : AtomCarrier.{u}} {A₀ : ArchitectureObject U}
variable {C : Site.ContextPreorderCategory A₀}
variable {E : ArchitecturalEquationSystem C}

/--
One-way compatibility conversion of an equation circuit reading, relative to
an explicitly supplied detector-soundness proof.
-/
def toLegacy (R : EquationCircuitReading E) (hSound : R.Sound) :
    CircuitReading E.toLegacyLawUniverse where
  code := R.code
  sound := by
    intro index object datum hmatches haccepts
    exact hSound index object datum hmatches haccepts

end EquationCircuitReading

namespace EquationReading

/--
The one-way legacy display generated by an admissible core equation reading.
-/
def toLegacyLawReading {U : AtomCarrier.{u}} {object : ArchitectureObject U}
    (R : EquationReading object) : LawReading U where
  lawUniverse := R.equationSystem.toLegacyLawUniverse
  circuits := R.circuits.toLegacy R.circuitSound

end EquationReading

end AAT.AG
