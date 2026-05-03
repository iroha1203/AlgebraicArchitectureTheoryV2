import Formal.Arch.Repair.RepairSynthesis

namespace Formal.Arch

/-
Small finite examples for the repair, synthesis, and no-solution theorem
packages.  The examples deliberately stay relative to selected finite
universes: they do not claim global obstruction removal, solver completeness,
global flatness preservation, or empirical cost improvement.
-/
namespace RepairSynthesisExamples

inductive SmallRepairState where
  | entangled
  | split
  deriving DecidableEq, Repr

inductive SmallRepairRule where
  | splitFeature
  deriving DecidableEq, Repr

inductive SmallRepairWitness where
  | selectedLeak
  | untrackedRuntime
  deriving DecidableEq, Repr

def smallRepairStates : List SmallRepairState :=
  [.entangled, .split]

def smallRepairWitnesses : List SmallRepairWitness :=
  [.selectedLeak, .untrackedRuntime]

theorem smallRepairStates_complete (s : SmallRepairState) :
    s ∈ smallRepairStates := by
  cases s <;> simp [smallRepairStates]

theorem smallRepairWitnesses_complete (w : SmallRepairWitness) :
    w ∈ smallRepairWitnesses := by
  cases w <;> simp [smallRepairWitnesses]

def selectedLeakWitness (w : SmallRepairWitness) : Prop :=
  w = .selectedLeak

def selectedLeakAt (s : SmallRepairState) (w : SmallRepairWitness) : Prop :=
  s = .entangled ∧ w = .selectedLeak

def selectedLeakUniverse :
    SelectedObstructionUniverse SmallRepairState SmallRepairWitness where
  selected := selectedLeakWitness
  witnessAt := selectedLeakAt
  measure := fun
    | .entangled => 1
    | .split => 0

def splitFeatureStep :
    RepairStep SmallRepairState SmallRepairRule
      .entangled .splitFeature .split where
  applied := True

theorem selectedLeak_nonSplitWitness :
    NonSplitExtensionWitness selectedLeakUniverse
      .entangled .selectedLeak := by
  simp [NonSplitExtensionWitness, selectedLeakUniverse,
    selectedLeakWitness, selectedLeakAt]

theorem splitFeatureStep_decreases :
    RepairStepDecreases selectedLeakUniverse .entangled .split := by
  simp [RepairStepDecreases, ExtensionObstructionMeasure,
    selectedLeakUniverse]

def smallBoundedRepairPlan :
    BoundedRepairPlan (Rule := SmallRepairRule)
      selectedLeakUniverse .entangled .split where
  initialMeasure := 1
  sourceMeasureWithinBound := by
    simp [ExtensionObstructionMeasure, selectedLeakUniverse]
  finiteSteps := 1
  stepsWithinBound := by
    simp
  everyStepDecreases :=
    RepairStepDecreases selectedLeakUniverse .entangled .split
  targetMeasureZero := by
    simp [ExtensionObstructionMeasure, selectedLeakUniverse]
  zeroMeasureClearsSelected := by
    intro _hZero w hSelected hAt
    cases w <;>
      simp [selectedLeakUniverse, selectedLeakWitness, selectedLeakAt]
        at hSelected hAt
  nonConclusions := True

def smallFiniteRepairPackage :
    FiniteRepairPackage (Rule := SmallRepairRule)
      selectedLeakUniverse .entangled .split where
  plan := smallBoundedRepairPlan
  coverageAssumptions :=
    (∀ s : SmallRepairState, s ∈ smallRepairStates) ∧
      (∀ w : SmallRepairWitness, w ∈ smallRepairWitnesses)
  exactnessAssumptions := True
  nonConclusions := True

theorem smallFiniteRepair_selectedObstructionsCleared :
    SelectedObstructionsCleared selectedLeakUniverse .split :=
  FiniteRepairPackage.selectedObstructionsCleared
    smallFiniteRepairPackage

theorem smallFiniteRepair_clears_selectedLeak :
    ¬ selectedLeakUniverse.witnessAt .split .selectedLeak :=
  smallFiniteRepair_selectedObstructionsCleared .selectedLeak
    (by simp [selectedLeakUniverse, selectedLeakWitness])

inductive SmallSynthesisState where
  | candidate
  | rejected
  deriving DecidableEq, Repr

inductive SmallSynthesisConstraint where
  | hasBoundary
  | hasAbstraction
  deriving DecidableEq, Repr

def smallSynthesisStates : List SmallSynthesisState :=
  [.candidate, .rejected]

def smallSynthesisConstraints : List SmallSynthesisConstraint :=
  [.hasBoundary, .hasAbstraction]

theorem smallSynthesisStates_complete (s : SmallSynthesisState) :
    s ∈ smallSynthesisStates := by
  cases s <;> simp [smallSynthesisStates]

theorem smallSynthesisConstraints_complete
    (c : SmallSynthesisConstraint) :
    c ∈ smallSynthesisConstraints := by
  cases c <;> simp [smallSynthesisConstraints]

def smallSynthesisSystem :
    SynthesisConstraintSystem
      SmallSynthesisState SmallSynthesisConstraint where
  required := fun _ => True
  satisfies := fun
    | .candidate, _ => True
    | .rejected, .hasBoundary => False
    | .rejected, .hasAbstraction => True

theorem smallCandidate_satisfies_system :
    ArchitectureSatisfies smallSynthesisSystem
      SmallSynthesisState.candidate := by
  intro constraint _hRequired
  cases constraint <;> simp [smallSynthesisSystem]

def smallSynthesisSoundnessPackage :
    SynthesisSoundnessPackage smallSynthesisSystem where
  candidate := .candidate
  sound := smallCandidate_satisfies_system
  coverageAssumptions :=
    (∀ s : SmallSynthesisState, s ∈ smallSynthesisStates) ∧
      (∀ c : SmallSynthesisConstraint, c ∈ smallSynthesisConstraints)
  exactnessAssumptions := True
  nonConclusions := True

theorem smallSynthesis_candidate_satisfies :
    ArchitectureSatisfies smallSynthesisSystem
      smallSynthesisSoundnessPackage.candidate :=
  SynthesisSoundnessPackage.candidate_satisfies
    smallSynthesisSoundnessPackage

inductive SmallNoSolutionConstraint where
  | mustBeCandidate
  | mustBeRejected
  deriving DecidableEq, Repr

inductive SmallNoSolutionCertificate where
  | conflictingRequirements
  deriving DecidableEq, Repr

def smallNoSolutionConstraints : List SmallNoSolutionConstraint :=
  [.mustBeCandidate, .mustBeRejected]

theorem smallNoSolutionConstraints_complete
    (c : SmallNoSolutionConstraint) :
    c ∈ smallNoSolutionConstraints := by
  cases c <;> simp [smallNoSolutionConstraints]

def conflictingRequirementSystem :
    SynthesisConstraintSystem
      SmallSynthesisState SmallNoSolutionConstraint where
  required := fun _ => True
  satisfies := fun
    | .candidate, .mustBeCandidate => True
    | .candidate, .mustBeRejected => False
    | .rejected, .mustBeCandidate => False
    | .rejected, .mustBeRejected => True

theorem conflictingRequirement_no_architecture :
    NoArchitectureSatisfies conflictingRequirementSystem := by
  intro X hSat
  cases X
  · exact hSat SmallNoSolutionConstraint.mustBeRejected (by
      simp [conflictingRequirementSystem])
  · exact hSat SmallNoSolutionConstraint.mustBeCandidate (by
      simp [conflictingRequirementSystem])

def conflictingRequirementsCertificatePackage :
    NoSolutionCertificate SmallNoSolutionCertificate
      conflictingRequirementSystem
      SmallNoSolutionCertificate.conflictingRequirements where
  valid := True
  sound := by
    intro _hValid
    exact conflictingRequirement_no_architecture
  coverageAssumptions :=
    (∀ s : SmallSynthesisState, s ∈ smallSynthesisStates) ∧
      (∀ c : SmallNoSolutionConstraint, c ∈ smallNoSolutionConstraints)
  exactnessAssumptions := True
  nonConclusions := True

theorem smallNoSolution_from_valid_certificate :
    NoArchitectureSatisfies conflictingRequirementSystem :=
  NoSolutionCertificate.sound_of_valid
    conflictingRequirementsCertificatePackage trivial

theorem smallNoSolution_rejects_candidate :
    ¬ ArchitectureSatisfies conflictingRequirementSystem
      SmallSynthesisState.candidate :=
  smallNoSolution_from_valid_certificate SmallSynthesisState.candidate

end RepairSynthesisExamples

end Formal.Arch
