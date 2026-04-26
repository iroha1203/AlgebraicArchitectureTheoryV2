import Formal.Arch.Obstruction

namespace Formal.Arch

universe u v w

/--
An abstract family of required laws together with its finite measured witness
universe.

`lawful` is deliberately a separate predicate. The obstruction framework can
prove bridge theorems to it, but the definition itself is not reduced to
`NoRequiredObstruction`.
-/
structure LawFamily (A : Type u) where
  Witness : Type v
  Axis : Type w
  measured : List Witness
  required : Witness -> Prop
  bad : A -> Witness -> Prop
  lawful : A -> Prop
  lawful_iff_no_measured_bad :
    ∀ a, lawful a ↔ ∀ w, w ∈ measured -> ¬ bad a w
  requiredAxis : Axis -> Prop

/-- A signature axis valuation used by abstract law-family bridge theorems. -/
abbrev AxisSignature (Axis : Type u) := Axis -> Option Nat

/--
An optional metric has no measured nonzero value.

This is intentionally weaker than `AvailableAndZero`: `none` satisfies
`MeasuredZero`, because no measured nonzero value is present.
-/
def MeasuredZero (metric : Option Nat) : Prop :=
  ∀ n, metric = some n -> n = 0

/--
An optional metric is present and exactly zero.

This intentionally rejects `none`; required law axes use this stronger
predicate when zero is meant to certify a covered law family.
-/
def AvailableAndZero (metric : Option Nat) : Prop :=
  metric = some 0

/-- A signature axis has no measured nonzero value. -/
def AxisMeasuredZero {Axis : Type u} (sig : AxisSignature Axis)
    (axis : Axis) : Prop :=
  MeasuredZero (sig axis)

/-- A signature axis is present and exactly zero. -/
def AxisAvailableAndZero {Axis : Type u} (sig : AxisSignature Axis)
    (axis : Axis) : Prop :=
  AvailableAndZero (sig axis)

/-- Missing measurements are measured-zero in the weak sense. -/
theorem measuredZero_none : MeasuredZero none := by
  intro n hSome
  cases hSome

/-- Missing measurements are not available-and-zero. -/
theorem not_availableAndZero_none : ¬ AvailableAndZero none := by
  intro hAvailable
  cases hAvailable

/-- A present zero metric is measured-zero. -/
theorem measuredZero_of_availableAndZero {metric : Option Nat}
    (hAvailable : AvailableAndZero metric) :
    MeasuredZero metric := by
  intro n hSome
  rw [hAvailable] at hSome
  cases hSome
  rfl

/-- For present metrics, measured-zero is exactly equality to zero. -/
theorem measuredZero_some_iff {n : Nat} :
    MeasuredZero (some n) ↔ n = 0 := by
  constructor
  · intro hMeasured
    exact hMeasured n rfl
  · intro hZero m hSome
    cases hSome
    exact hZero

/-- For present metrics, available-and-zero is exactly equality to zero. -/
theorem availableAndZero_some_iff {n : Nat} :
    AvailableAndZero (some n) ↔ n = 0 := by
  simp [AvailableAndZero]

/-- A law family is lawful for an architecture according to its independent predicate. -/
def Lawful {A : Type u} (a : A) (L : LawFamily A) : Prop :=
  L.lawful a

/-- No required obstruction witness exists for the law family. -/
def NoRequiredObstruction {A : Type u} (a : A) (L : LawFamily A) : Prop :=
  ∀ w, L.required w -> ¬ L.bad a w

/-- No measured obstruction witness exists for the law family. -/
def NoMeasuredObstruction {A : Type u} (a : A) (L : LawFamily A) : Prop :=
  ∀ w, w ∈ L.measured -> ¬ L.bad a w

/-- The measured witness list contains every required witness. -/
def RequiredWitnessCoverage {A : Type u} (L : LawFamily A) : Prop :=
  CoversWitnesses L.required L.measured

/-- The finite measured witness list is exactly the required witness universe. -/
def CompleteWitnessCoverage {A : Type u} (L : LawFamily A) : Prop :=
  ∀ w, w ∈ L.measured ↔ L.required w

/-- Count measured law-family obstruction witnesses. -/
def lawViolationCount {A : Type u} (a : A) (L : LawFamily A)
    [DecidablePred (L.bad a)] : Nat :=
  violationCount (L.bad a) L.measured

/--
The independent lawfulness predicate is equivalent to absence of measured
obstruction witnesses by the bridge carried by the law family.
-/
theorem lawful_iff_noMeasuredObstruction {A : Type u} {a : A}
    {L : LawFamily A} :
    Lawful a L ↔ NoMeasuredObstruction a L := by
  exact L.lawful_iff_no_measured_bad a

/--
The finite measured violation count is zero exactly when the independent
lawfulness predicate holds.
-/
theorem lawViolationCount_eq_zero_iff_lawful {A : Type u} {a : A}
    {L : LawFamily A} [DecidablePred (L.bad a)] :
    lawViolationCount a L = 0 ↔ Lawful a L := by
  exact Iff.trans violationCount_eq_zero_iff_forall_not_bad
    (Iff.symm lawful_iff_noMeasuredObstruction)

/-- Complete witness coverage includes required-witness coverage. -/
theorem requiredWitnessCoverage_of_completeWitnessCoverage
    {A : Type u} {L : LawFamily A}
    (hCoverage : CompleteWitnessCoverage L) :
    RequiredWitnessCoverage L := by
  intro w hRequired
  exact (hCoverage w).mpr hRequired

/--
Complete witness coverage turns measured obstruction absence into required
obstruction absence.
-/
theorem noRequiredObstruction_of_completeCoverage_and_noMeasuredObstruction
    {A : Type u} {a : A} {L : LawFamily A}
    (hCoverage : CompleteWitnessCoverage L)
    (hNoMeasured : NoMeasuredObstruction a L) :
    NoRequiredObstruction a L := by
  intro w hRequired
  exact hNoMeasured w ((hCoverage w).mpr hRequired)

/--
Required-witness coverage is the precise assumption needed to turn measured
obstruction absence into required obstruction absence.
-/
theorem noRequiredObstruction_of_requiredWitnessCoverage_and_noMeasuredObstruction
    {A : Type u} {a : A} {L : LawFamily A}
    (hCoverage : RequiredWitnessCoverage L)
    (hNoMeasured : NoMeasuredObstruction a L) :
    NoRequiredObstruction a L := by
  intro w hRequired
  exact hNoMeasured w (hCoverage w hRequired)

/--
Under required-witness coverage, zero measured law violations imply absence of
required obstruction witnesses. Without this coverage, measured-zero is only a
statement about the measured list.
-/
theorem noRequiredObstruction_of_requiredWitnessCoverage_and_lawViolationCount_eq_zero
    {A : Type u} {a : A} {L : LawFamily A}
    [DecidablePred (L.bad a)]
    (hCoverage : RequiredWitnessCoverage L)
    (hZero : lawViolationCount a L = 0) :
    NoRequiredObstruction a L := by
  exact noRequiredObstruction_of_requiredWitnessCoverage_and_noMeasuredObstruction
    hCoverage (lawful_iff_noMeasuredObstruction.mp
      (lawViolationCount_eq_zero_iff_lawful.mp hZero))

/--
Complete witness coverage turns required obstruction absence into measured
obstruction absence.
-/
theorem noMeasuredObstruction_of_completeCoverage_and_noRequiredObstruction
    {A : Type u} {a : A} {L : LawFamily A}
    (hCoverage : CompleteWitnessCoverage L)
    (hNoRequired : NoRequiredObstruction a L) :
    NoMeasuredObstruction a L := by
  intro w hMeasured
  exact hNoRequired w ((hCoverage w).mp hMeasured)

/--
Under complete witness coverage, the independent lawfulness predicate is
equivalent to the absence of required obstruction witnesses.
-/
theorem lawful_iff_noRequiredObstruction_of_completeCoverage
    {A : Type u} {a : A} {L : LawFamily A}
    (hCoverage : CompleteWitnessCoverage L) :
    Lawful a L ↔ NoRequiredObstruction a L := by
  constructor
  · intro hLawful
    exact noRequiredObstruction_of_completeCoverage_and_noMeasuredObstruction
      hCoverage (lawful_iff_noMeasuredObstruction.mp hLawful)
  · intro hNoRequired
    exact lawful_iff_noMeasuredObstruction.mpr
      (noMeasuredObstruction_of_completeCoverage_and_noRequiredObstruction
        hCoverage hNoRequired)

/--
Under complete witness coverage, zero measured violations are equivalent to the
absence of required obstruction witnesses.
-/
theorem lawViolationCount_eq_zero_iff_noRequiredObstruction_of_completeCoverage
    {A : Type u} {a : A} {L : LawFamily A}
    [DecidablePred (L.bad a)]
    (hCoverage : CompleteWitnessCoverage L) :
    lawViolationCount a L = 0 ↔ NoRequiredObstruction a L := by
  exact Iff.trans lawViolationCount_eq_zero_iff_lawful
    (lawful_iff_noRequiredObstruction_of_completeCoverage hCoverage)

/--
Every required axis of the law family is present in the signature and measured
as zero.
-/
def RequiredAxesAvailableAndZero {A : Type u} (L : LawFamily A)
    (sig : AxisSignature L.Axis) : Prop :=
  ∀ axis, L.requiredAxis axis -> AxisAvailableAndZero sig axis

/--
Axis-level exactness: one available-and-zero axis is equivalent to absence of
bad witnesses in the witness subfamily represented by that axis.
-/
def AxisExact {A : Type u} (a : A) (L : LawFamily A)
    (sig : AxisSignature L.Axis) (axis : L.Axis)
    (witnessForAxis : L.Witness -> Prop) : Prop :=
  AxisAvailableAndZero sig axis ↔ ∀ w, witnessForAxis w -> ¬ L.bad a w

/-- An axis witness subfamily contains only required witnesses. -/
def AxisCoversOnlyRequired {A : Type u} (L : LawFamily A)
    (witnessForAxis : L.Axis -> L.Witness -> Prop) : Prop :=
  ∀ axis, L.requiredAxis axis -> ∀ w, witnessForAxis axis w -> L.required w

/-- Every required witness is represented by at least one required axis. -/
def RequiredWitnessCoveredByAxis {A : Type u} (L : LawFamily A)
    (witnessForAxis : L.Axis -> L.Witness -> Prop) : Prop :=
  ∀ w, L.required w ->
    ∃ axis, L.requiredAxis axis ∧ witnessForAxis axis w

/-- Every required axis is exact for its represented witness subfamily. -/
def RequiredAxisFamilyExact {A : Type u} (a : A) (L : LawFamily A)
    (sig : AxisSignature L.Axis)
    (witnessForAxis : L.Axis -> L.Witness -> Prop) : Prop :=
  ∀ axis, L.requiredAxis axis -> AxisExact a L sig axis (witnessForAxis axis)

/--
A proof-carrying statement that required zero axes exactly represent absence of
required obstruction witnesses.
-/
def RequiredAxisExact {A : Type u} (a : A) (L : LawFamily A)
    (sig : AxisSignature L.Axis) : Prop :=
  RequiredAxesAvailableAndZero L sig ↔ NoRequiredObstruction a L

/--
Required axis exactness exposes the bridge from signature zeros to required
obstruction absence.
-/
theorem requiredAxesAvailableAndZero_iff_noRequiredObstruction_of_requiredAxisExact
    {A : Type u} {a : A} {L : LawFamily A} {sig : AxisSignature L.Axis}
    (hExact : RequiredAxisExact a L sig) :
    RequiredAxesAvailableAndZero L sig ↔ NoRequiredObstruction a L := by
  exact hExact

/--
Axis-level exactness and a required-axis cover produce the global required-axis
bridge used by the zero-curvature theorem shape.
-/
theorem requiredAxesAvailableAndZero_iff_noRequiredObstruction_of_axisExactFamily
    {A : Type u} {a : A} {L : LawFamily A} {sig : AxisSignature L.Axis}
    {witnessForAxis : L.Axis -> L.Witness -> Prop}
    (hExact : RequiredAxisFamilyExact a L sig witnessForAxis)
    (hOnlyRequired : AxisCoversOnlyRequired L witnessForAxis)
    (hCovered : RequiredWitnessCoveredByAxis L witnessForAxis) :
    RequiredAxesAvailableAndZero L sig ↔ NoRequiredObstruction a L := by
  constructor
  · intro hAxes w hRequired
    rcases hCovered w hRequired with ⟨axis, hRequiredAxis, hWitness⟩
    exact ((hExact axis hRequiredAxis).mp (hAxes axis hRequiredAxis)) w hWitness
  · intro hNoRequired axis hRequiredAxis
    exact (hExact axis hRequiredAxis).mpr (by
      intro w hWitness
      exact hNoRequired w (hOnlyRequired axis hRequiredAxis w hWitness))

/--
Axis-level exactness can be packaged as the whole-family exactness predicate
used by existing bridge theorems.
-/
theorem requiredAxisExact_of_axisExactFamily
    {A : Type u} {a : A} {L : LawFamily A} {sig : AxisSignature L.Axis}
    {witnessForAxis : L.Axis -> L.Witness -> Prop}
    (hExact : RequiredAxisFamilyExact a L sig witnessForAxis)
    (hOnlyRequired : AxisCoversOnlyRequired L witnessForAxis)
    (hCovered : RequiredWitnessCoveredByAxis L witnessForAxis) :
    RequiredAxisExact a L sig := by
  exact requiredAxesAvailableAndZero_iff_noRequiredObstruction_of_axisExactFamily
    hExact hOnlyRequired hCovered

/--
Central zero-curvature theorem shape: with complete witness coverage and an
exact required-axis bridge, independent lawfulness is equivalent to all required
signature axes being available and zero.
-/
theorem lawful_iff_requiredAxesAvailableAndZero_of_completeCoverage_and_requiredAxisExact
    {A : Type u} {a : A} {L : LawFamily A} {sig : AxisSignature L.Axis}
    (hCoverage : CompleteWitnessCoverage L)
    (hExact : RequiredAxisExact a L sig) :
    Lawful a L ↔ RequiredAxesAvailableAndZero L sig := by
  exact Iff.trans
    (lawful_iff_noRequiredObstruction_of_completeCoverage hCoverage)
    (Iff.symm hExact)

end Formal.Arch
