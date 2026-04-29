namespace Formal.Arch

universe u v w

/--
Representation map from architecture states to an analytic domain.

The structural and analytic zero/obstruction predicates are kept as explicit
fields so representation strength can be stated without treating metrics alone
as flatness proofs.
-/
structure AnalyticRepresentation
    (State : Type u) (Analytic : Type v) (Witness : Type w) where
  represent : State -> Analytic
  structuralZero : State -> Prop
  analyticZero : Analytic -> Prop
  structuralObstruction : State -> Witness -> Prop
  analyticObstruction : Analytic -> Witness -> Prop
  coverageAssumptions : Prop
  witnessCompleteness : Prop
  semanticContractCoverage : Prop
  nonConclusions : Prop

namespace AnalyticRepresentation

variable {State : Type u} {Analytic : Type v} {Witness : Type w}

/-- The representation sends structural zero states to analytic zero values. -/
def ZeroPreserving (R : AnalyticRepresentation State Analytic Witness) : Prop :=
  ∀ X, R.structuralZero X -> R.analyticZero (R.represent X)

/--
Analytic zero reflects structural zero under the selected coverage and
completeness assumptions.
-/
def ZeroReflecting (R : AnalyticRepresentation State Analytic Witness) : Prop :=
  R.coverageAssumptions ->
  R.witnessCompleteness ->
  R.semanticContractCoverage ->
  ∀ X, R.analyticZero (R.represent X) -> R.structuralZero X

/-- Structural obstruction witnesses are preserved by the analytic representation. -/
def ObstructionPreserving
    (R : AnalyticRepresentation State Analytic Witness) : Prop :=
  ∀ X w, R.structuralObstruction X w ->
    R.analyticObstruction (R.represent X) w

/--
Analytic obstruction witnesses reflect structural witnesses under the selected
coverage and completeness assumptions.
-/
def ObstructionReflecting
    (R : AnalyticRepresentation State Analytic Witness) : Prop :=
  R.coverageAssumptions ->
  R.witnessCompleteness ->
  R.semanticContractCoverage ->
  ∀ X w, R.analyticObstruction (R.represent X) w ->
    R.structuralObstruction X w

/-- The theorem package explicitly records non-conclusions. -/
def RecordsNonConclusions
    (R : AnalyticRepresentation State Analytic Witness) : Prop :=
  R.nonConclusions

theorem analyticZero_of_structuralZero
    (R : AnalyticRepresentation State Analytic Witness)
    (h : ZeroPreserving R)
    {X : State} (hZero : R.structuralZero X) :
    R.analyticZero (R.represent X) :=
  h X hZero

theorem structuralZero_of_analyticZero
    (R : AnalyticRepresentation State Analytic Witness)
    (h : ZeroReflecting R)
    (hCoverage : R.coverageAssumptions)
    (hWitness : R.witnessCompleteness)
    (hSemantic : R.semanticContractCoverage)
    {X : State} (hZero : R.analyticZero (R.represent X)) :
    R.structuralZero X :=
  h hCoverage hWitness hSemantic X hZero

theorem analyticObstruction_of_structuralObstruction
    (R : AnalyticRepresentation State Analytic Witness)
    (h : ObstructionPreserving R)
    {X : State} {w : Witness}
    (hObs : R.structuralObstruction X w) :
    R.analyticObstruction (R.represent X) w :=
  h X w hObs

theorem structuralObstruction_of_analyticObstruction
    (R : AnalyticRepresentation State Analytic Witness)
    (h : ObstructionReflecting R)
    (hCoverage : R.coverageAssumptions)
    (hWitness : R.witnessCompleteness)
    (hSemantic : R.semanticContractCoverage)
    {X : State} {w : Witness}
    (hObs : R.analyticObstruction (R.represent X) w) :
    R.structuralObstruction X w :=
  h hCoverage hWitness hSemantic X w hObs

end AnalyticRepresentation

/--
Abstract obstruction valuation for a selected witness universe.

The valuation is not a flatness predicate by itself.  Its zero-reflection field
is witness-relative and must be combined with coverage before structural
conclusions are drawn.
-/
structure ObstructionValuation (State : Type u) (Witness : Type v) where
  obstruction : State -> Witness -> Prop
  value : State -> Witness -> Nat
  zeroReflectsAbsence :
    ∀ X w, value X w = 0 -> ¬ obstruction X w
  obstructionGivesPositive :
    ∀ X w, obstruction X w -> 0 < value X w
  coverageAssumptions : Prop
  nonConclusions : Prop

namespace ObstructionValuation

variable {State : Type u} {Witness : Type v}

/-- No selected obstruction witness is present at a state. -/
def NoSelectedObstruction
    (V : ObstructionValuation State Witness) (X : State) : Prop :=
  ∀ w, ¬ V.obstruction X w

/-- An aggregate valuation is zero-reflecting for the selected witness universe. -/
def ZeroReflectingSum
    (V : ObstructionValuation State Witness)
    (aggregate : State -> Nat) : Prop :=
  ∀ X, aggregate X = 0 -> NoSelectedObstruction V X

/-- Zero valuation of an individual witness rules out that witness obstruction. -/
theorem no_obstruction_of_value_zero
    (V : ObstructionValuation State Witness)
    {X : State} {w : Witness}
    (hZero : V.value X w = 0) :
    ¬ V.obstruction X w :=
  V.zeroReflectsAbsence X w hZero

/-- Zero-reflecting aggregate values rule out selected obstruction witnesses. -/
theorem noSelectedObstruction_of_zeroReflectingSum
    (V : ObstructionValuation State Witness)
    {aggregate : State -> Nat}
    (hReflects : ZeroReflectingSum V aggregate)
    {X : State} (hZero : aggregate X = 0) :
    NoSelectedObstruction V X :=
  hReflects X hZero

/-- The theorem package explicitly records non-conclusions. -/
def RecordsNonConclusions
    (V : ObstructionValuation State Witness) : Prop :=
  V.nonConclusions

end ObstructionValuation

end Formal.Arch
