import Formal.AG.Atom.ArchitectureObject

namespace AAT.AG

universe u

/-- I.定義7.1: a law is a predicate on architecture objects. -/
structure Law (U : AtomCarrier.{u}) where
  holds : ArchitectureObject U -> Prop

/-- Laws are equal when their predicates agree. -/
@[ext] theorem Law.ext {U : AtomCarrier.{u}} {L₁ L₂ : Law U}
    (hholds : L₁.holds = L₂.holds) : L₁ = L₂ := by
  cases L₁
  cases L₂
  cases hholds
  rfl

/-- I.定義7.2: the role assigned to a law inside a law universe. -/
inductive LawRole where
  | required
  | optional
  | derived
  deriving DecidableEq

/-- I.定義7.2: selected witness family for reading required obstruction absence. -/
structure LawWitnessFamily (U : AtomCarrier.{u}) where
  Witness : Type u
  badWitness : ArchitectureObject U -> Witness -> Prop

/-- I.定義7.2: selected signature axes for zero-axis readings. -/
structure SignatureAxes (U : AtomCarrier.{u}) where
  Axis : Type u
  selected : Axis -> Prop
  zero : ArchitectureObject U -> Axis -> Prop

/--
Legacy display surface for a selected equation family.

Standard AAT construction obtains this structure from an
`ArchitecturalEquationSystem`; it no longer carries untyped coverage or
exactness assumptions. The eventual removal of this compatibility type is
tracked separately from the equation-system migration.
-/
structure LawUniverse (U : AtomCarrier.{u}) where
  Index : Type u
  law : Index -> Law U
  role : Index -> LawRole
  witnessFamily : LawWitnessFamily U
  SelectedReading : Type u
  selectedReading : SelectedReading

namespace LawUniverse

/-- I.定義7.2: required-law membership inside a law universe. -/
def Required {U : AtomCarrier.{u}} (LU : LawUniverse U) (index : LU.Index) :
    Prop :=
  LU.role index = LawRole.required

/-- I.定義7.2: optional-law membership inside a law universe. -/
def Optional {U : AtomCarrier.{u}} (LU : LawUniverse U) (index : LU.Index) :
    Prop :=
  LU.role index = LawRole.optional

/-- I.定義7.2: derived-law membership inside a law universe. -/
def Derived {U : AtomCarrier.{u}} (LU : LawUniverse U) (index : LU.Index) :
    Prop :=
  LU.role index = LawRole.derived

end LawUniverse

/-- I.定義7.3: lawfulness means satisfying every required law in the selected universe. -/
def Lawfulness {U : AtomCarrier.{u}} (A : ArchitectureObject U)
    (LU : LawUniverse U) : Prop :=
  ∀ index : LU.Index, LU.Required index -> (LU.law index).holds A

/-- I.定義7.2: semantic lawfulness in the selected law universe. -/
def SemanticLawful {U : AtomCarrier.{u}} (A : ArchitectureObject U)
    (LU : LawUniverse U) : Prop :=
  Lawfulness A LU

/-- I.定義7.2: no selected required bad witness exists. -/
def NoRequiredObstruction {U : AtomCarrier.{u}} (A : ArchitectureObject U)
    (W : LawWitnessFamily U) : Prop :=
  ∀ witness : W.Witness, ¬ W.badWitness A witness

/-- I.定義7.2: every selected signature axis reads as zero. -/
def RequiredSignatureAxesZero {U : AtomCarrier.{u}} (A : ArchitectureObject U)
    (S : SignatureAxes U) : Prop :=
  ∀ axis : S.Axis, S.selected axis -> S.zero A axis

/-- I.定義7.3: extract a required law proof from lawfulness. -/
theorem lawfulness_required_holds {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {LU : LawUniverse U} {index : LU.Index} (h : Lawfulness A LU)
    (hrequired : LU.Required index) :
    (LU.law index).holds A :=
  h index hrequired

/-- I.定義7.2: semantic lawfulness is the lawfulness predicate by definition. -/
theorem semanticLawful_iff_lawfulness {U : AtomCarrier.{u}}
    {A : ArchitectureObject U} {LU : LawUniverse U} :
    SemanticLawful A LU ↔ Lawfulness A LU :=
  Iff.rfl

/-- I.定義7.2: no-obstruction readings expose absence of each selected witness. -/
theorem noRequiredObstruction_no_bad_witness {U : AtomCarrier.{u}}
    {A : ArchitectureObject U} {W : LawWitnessFamily U}
    (h : NoRequiredObstruction A W) (witness : W.Witness) :
    ¬ W.badWitness A witness :=
  h witness

/-- I.定義7.2: selected zero-axis readings expose zero on each selected axis. -/
theorem requiredSignatureAxesZero_axis {U : AtomCarrier.{u}}
    {A : ArchitectureObject U} {S : SignatureAxes U}
    (h : RequiredSignatureAxesZero A S) {axis : S.Axis}
    (hselected : S.selected axis) :
    S.zero A axis :=
  h axis hselected

end AAT.AG
