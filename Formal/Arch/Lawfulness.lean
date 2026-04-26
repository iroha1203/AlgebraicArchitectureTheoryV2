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

/-- A law family is lawful for an architecture according to its independent predicate. -/
def Lawful {A : Type u} (a : A) (L : LawFamily A) : Prop :=
  L.lawful a

/-- No required obstruction witness exists for the law family. -/
def NoRequiredObstruction {A : Type u} (a : A) (L : LawFamily A) : Prop :=
  ∀ w, L.required w -> ¬ L.bad a w

/-- No measured obstruction witness exists for the law family. -/
def NoMeasuredObstruction {A : Type u} (a : A) (L : LawFamily A) : Prop :=
  ∀ w, w ∈ L.measured -> ¬ L.bad a w

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
The axis has been measured and is exactly zero. This intentionally rejects
`none`.
-/
def AvailableAndZero {Axis : Type u} (sig : AxisSignature Axis)
    (axis : Axis) : Prop :=
  sig axis = some 0

/--
Every required axis of the law family is present in the signature and measured
as zero.
-/
def RequiredAxesAvailableAndZero {A : Type u} (L : LawFamily A)
    (sig : AxisSignature L.Axis) : Prop :=
  ∀ axis, L.requiredAxis axis -> AvailableAndZero sig axis

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
