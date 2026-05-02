import Formal.Arch.Repair.Repair

namespace Formal.Arch

universe u v r c

/-- A state has no selected obstruction witnesses in the chosen repair universe. -/
def SelectedObstructionsCleared
    {State : Type u} {Witness : Type v}
    (U : SelectedObstructionUniverse State Witness)
    (state : State) : Prop :=
  ∀ w, U.selected w -> ¬ U.witnessAt state w

/--
Bounded finite repair plan schema.

The plan records the finite bound, the selected measure at the target, the
coverage assumption that turns zero selected measure into witness absence, and
explicit non-conclusions.  It does not claim global obstruction removal.
-/
structure BoundedRepairPlan
    {State : Type u} {Witness : Type v} {Rule : Type r}
    (U : SelectedObstructionUniverse State Witness)
    (source target : State) where
  initialMeasure : Nat
  sourceMeasureWithinBound :
    ExtensionObstructionMeasure U source ≤ initialMeasure
  finiteSteps : Nat
  stepsWithinBound : finiteSteps ≤ initialMeasure
  everyStepDecreases : Prop
  targetMeasureZero : ExtensionObstructionMeasure U target = 0
  zeroMeasureClearsSelected :
    ExtensionObstructionMeasure U target = 0 ->
      SelectedObstructionsCleared U target
  nonConclusions : Prop

namespace BoundedRepairPlan

variable {State : Type u} {Witness : Type v} {Rule : Type r}
variable {U : SelectedObstructionUniverse State Witness}
variable {source target : State}

/-- A bounded repair plan exposes the finite number of selected repair steps. -/
theorem finite_steps_within_initial_measure
    (plan : BoundedRepairPlan (Rule := Rule) U source target) :
    plan.finiteSteps ≤ plan.initialMeasure :=
  plan.stepsWithinBound

/-- A bounded repair plan clears the selected obstruction universe at target. -/
theorem selectedObstructionsCleared
    (plan : BoundedRepairPlan (Rule := Rule) U source target) :
    SelectedObstructionsCleared U target :=
  plan.zeroMeasureClearsSelected plan.targetMeasureZero

/-- The theorem package explicitly records non-conclusions. -/
def RecordsNonConclusions
    (plan : BoundedRepairPlan (Rule := Rule) U source target) : Prop :=
  plan.nonConclusions

end BoundedRepairPlan

/--
Finite repair theorem package for the selected obstruction universe.

This packages the bounded plan and its selected-universe conclusion separately
from the local `RepairStepDecreases` theorem.
-/
structure FiniteRepairPackage
    {State : Type u} {Witness : Type v} {Rule : Type r}
    (U : SelectedObstructionUniverse State Witness)
    (source target : State) where
  plan : BoundedRepairPlan (Rule := Rule) U source target
  coverageAssumptions : Prop
  exactnessAssumptions : Prop
  nonConclusions : Prop

namespace FiniteRepairPackage

variable {State : Type u} {Witness : Type v} {Rule : Type r}
variable {U : SelectedObstructionUniverse State Witness}
variable {source target : State}

/-- Finite repair clears the selected obstruction universe at the target. -/
theorem selectedObstructionsCleared
    (pkg : FiniteRepairPackage (Rule := Rule) U source target) :
    SelectedObstructionsCleared U target :=
  pkg.plan.selectedObstructionsCleared

/-- The theorem package explicitly records non-conclusions. -/
def RecordsNonConclusions
    (pkg : FiniteRepairPackage (Rule := Rule) U source target) : Prop :=
  pkg.nonConclusions

end FiniteRepairPackage

/-- Constraint system used by synthesis and no-solution certificate schemas. -/
structure SynthesisConstraintSystem (State : Type u) (Constraint : Type c) where
  required : Constraint -> Prop
  satisfies : State -> Constraint -> Prop

/-- A state satisfies every required constraint in a synthesis system. -/
def ArchitectureSatisfies
    {State : Type u} {Constraint : Type c}
    (C : SynthesisConstraintSystem State Constraint)
    (X : State) : Prop :=
  ∀ constraint, C.required constraint -> C.satisfies X constraint

/-- No architecture state satisfies all required constraints. -/
def NoArchitectureSatisfies
    {State : Type u} {Constraint : Type c}
    (C : SynthesisConstraintSystem State Constraint) : Prop :=
  ∀ X, ¬ ArchitectureSatisfies C X

/--
Sound synthesis package for a produced architecture candidate.

Returning a candidate is separate from proving that `none` means no solution.
-/
structure SynthesisSoundnessPackage
    {State : Type u} {Constraint : Type c}
    (C : SynthesisConstraintSystem State Constraint) where
  candidate : State
  sound : ArchitectureSatisfies C candidate
  coverageAssumptions : Prop
  exactnessAssumptions : Prop
  nonConclusions : Prop

namespace SynthesisSoundnessPackage

variable {State : Type u} {Constraint : Type c}
variable {C : SynthesisConstraintSystem State Constraint}

/-- A sound synthesis package exposes that the produced candidate satisfies C. -/
theorem candidate_satisfies
    (pkg : SynthesisSoundnessPackage C) :
    ArchitectureSatisfies C pkg.candidate :=
  pkg.sound

/-- The theorem package explicitly records non-conclusions. -/
def RecordsNonConclusions
    (pkg : SynthesisSoundnessPackage C) : Prop :=
  pkg.nonConclusions

end SynthesisSoundnessPackage

/--
No-solution certificate package.

The `valid` field is intentionally separate from solver failure.  Only a valid
certificate implies non-existence of a satisfying architecture.
-/
structure NoSolutionCertificate
    {State : Type u} {Constraint : Type c} (Certificate : Type v)
    (C : SynthesisConstraintSystem State Constraint)
    (cert : Certificate) where
  valid : Prop
  sound : valid -> NoArchitectureSatisfies C
  coverageAssumptions : Prop
  exactnessAssumptions : Prop
  nonConclusions : Prop

/-- A certificate is valid when its selected no-solution package says so. -/
def ValidNoSolutionCertificate
    {State : Type u} {Constraint : Type c} {Certificate : Type v}
    {C : SynthesisConstraintSystem State Constraint} {cert : Certificate}
    (pkg : NoSolutionCertificate Certificate C cert) : Prop :=
  pkg.valid

namespace NoSolutionCertificate

variable {State : Type u} {Constraint : Type c} {Certificate : Type v}
variable {C : SynthesisConstraintSystem State Constraint}
variable {cert : Certificate}

/-- Valid no-solution certificates imply that no architecture satisfies C. -/
theorem sound_of_valid
    (pkg : NoSolutionCertificate Certificate C cert)
    (hValid : ValidNoSolutionCertificate pkg) :
    NoArchitectureSatisfies C :=
  pkg.sound hValid

/-- The theorem package explicitly records non-conclusions. -/
def RecordsNonConclusions
    (pkg : NoSolutionCertificate Certificate C cert) : Prop :=
  pkg.nonConclusions

end NoSolutionCertificate

end Formal.Arch
