import Formal.Arch.Obstruction
import Formal.Arch.Repair
import Formal.Arch.ComplexityTransfer

namespace Formal.Arch

/-
A minimal counterexample package showing that a selected repair measure can
decrease while another diagnostic axis gains an obstruction.

The example has two states.  The repair removes the selected static witness
from `entangled`, but the repaired state carries a runtime-axis witness.  This
keeps the repair theorem bounded to the selected obstruction universe and
records that it is not an all-axis monotonicity or global-flatness theorem.
-/
namespace RepairTransferCounterexample

inductive RepairState where
  | entangled
  | repaired
  deriving DecidableEq, Repr

inductive RepairRule where
  | splitStaticLeak
  deriving DecidableEq, Repr

inductive RepairWitness where
  | staticLeak
  | runtimeBackpressure
  deriving DecidableEq, Repr

def selectedStaticWitness (w : RepairWitness) : Prop :=
  w = .staticLeak

def staticWitnessAt (s : RepairState) (w : RepairWitness) : Prop :=
  s = .entangled ∧ w = .staticLeak

def runtimeAxisWitness (w : RepairWitness) : Prop :=
  w = .runtimeBackpressure

def runtimeWitnessAt (s : RepairState) (w : RepairWitness) : Prop :=
  s = .repaired ∧ w = .runtimeBackpressure

def selectedStaticUniverse :
    SelectedObstructionUniverse RepairState RepairWitness where
  selected := selectedStaticWitness
  witnessAt := staticWitnessAt
  measure := fun
    | .entangled => 1
    | .repaired => 0

def runtimeAxisUniverse :
    SelectedObstructionUniverse RepairState RepairWitness where
  selected := runtimeAxisWitness
  witnessAt := runtimeWitnessAt
  measure := fun
    | .entangled => 0
    | .repaired => 1

instance instDecidablePredRuntimeAxisWitnessAt (s : RepairState) :
    DecidablePred (runtimeAxisUniverse.witnessAt s) := by
  intro w
  change Decidable (runtimeWitnessAt s w)
  unfold runtimeWitnessAt
  infer_instance

def staticRepairStep :
    RepairStep RepairState RepairRule
      .entangled .splitStaticLeak .repaired where
  applied := True

theorem staticLeak_nonSplitWitness :
    NonSplitExtensionWitness selectedStaticUniverse
      .entangled .staticLeak := by
  simp [NonSplitExtensionWitness, selectedStaticUniverse,
    selectedStaticWitness, staticWitnessAt]

theorem selectedRepairStep_decreases :
    RepairStepDecreases selectedStaticUniverse .entangled .repaired := by
  simp [RepairStepDecreases, ExtensionObstructionMeasure,
    selectedStaticUniverse]

/--
Bridge to the existing admissible-repair API: any admissible rule for the
selected static witness yields the same selected-measure decrease for this
repair step.
-/
theorem selectedRepairStep_decreases_of_admissible
    (hRule :
      AdmissibleRepairRule selectedStaticUniverse
        RepairRule.splitStaticLeak RepairWitness.staticLeak) :
    RepairStepDecreases selectedStaticUniverse .entangled .repaired :=
  repairStepDecreases_of_admissible
    staticLeak_nonSplitWitness hRule staticRepairStep

theorem runtimeAxisMeasure_increases :
    ExtensionObstructionMeasure runtimeAxisUniverse .entangled <
      ExtensionObstructionMeasure runtimeAxisUniverse .repaired := by
  simp [ExtensionObstructionMeasure, runtimeAxisUniverse]

def runtimeMeasuredWitnesses : List RepairWitness :=
  [.runtimeBackpressure]

theorem runtimeAxis_noMeasuredViolation_before :
    NoMeasuredViolation (runtimeAxisUniverse.witnessAt .entangled)
      runtimeMeasuredWitnesses := by
  intro w hMem hBad
  simp [runtimeMeasuredWitnesses, runtimeAxisUniverse,
    runtimeWitnessAt] at hMem hBad

theorem runtimeAxis_measuredViolation_after :
    MeasuredViolationExists (runtimeAxisUniverse.witnessAt .repaired)
      runtimeMeasuredWitnesses := by
  refine ⟨.runtimeBackpressure, ?_, ?_⟩
  · simp [runtimeMeasuredWitnesses]
  · simp [runtimeAxisUniverse, runtimeWitnessAt]

theorem runtimeAxisViolationCount_before :
    violationCount (runtimeAxisUniverse.witnessAt .entangled)
      runtimeMeasuredWitnesses = 0 := by
  simp [violationCount, violatingWitnesses, runtimeMeasuredWitnesses,
    runtimeAxisUniverse, runtimeWitnessAt]

theorem runtimeAxisViolationCount_after :
    violationCount (runtimeAxisUniverse.witnessAt .repaired)
      runtimeMeasuredWitnesses = 1 := by
  simp [violationCount, violatingWitnesses, runtimeMeasuredWitnesses,
    runtimeAxisUniverse, runtimeWitnessAt]

def AxisMeasureNonincreasing
    (U : SelectedObstructionUniverse RepairState RepairWitness)
    (source target : RepairState) : Prop :=
  ExtensionObstructionMeasure U target <=
    ExtensionObstructionMeasure U source

def SelectedAndRuntimeAxesNonincreasing
    (source target : RepairState) : Prop :=
  AxisMeasureNonincreasing selectedStaticUniverse source target ∧
    AxisMeasureNonincreasing runtimeAxisUniverse source target

theorem selectedRepairStep_not_all_axes_nonincreasing :
    ¬ SelectedAndRuntimeAxesNonincreasing .entangled .repaired := by
  intro hAxes
  exact (by
    simpa [SelectedAndRuntimeAxesNonincreasing,
      AxisMeasureNonincreasing, ExtensionObstructionMeasure,
      runtimeAxisUniverse] using hAxes.2)

inductive RepairTransform where
  | staticSplitRepair
  deriving DecidableEq, Repr

def repairTransform :
    ArchitectureTransform RepairState RepairTransform where
  source := fun
    | .staticSplitRepair => .entangled
  target := fun
    | .staticSplitRepair => .repaired
  boundedUniverse := True
  nonConclusions := True

def selectedStaticComplexity :
    SelectedComplexityMeasure RepairState where
  value := ExtensionObstructionMeasure selectedStaticUniverse
  measuredUniverse := fun _ => True
  bounded := True
  nonConclusions := True

theorem staticSplitRepair_reducesStaticComplexity :
    ReducesStaticComplexity repairTransform
      selectedStaticComplexity .staticSplitRepair := by
  simp [ReducesStaticComplexity, repairTransform,
    selectedStaticComplexity, ExtensionObstructionMeasure,
    selectedStaticUniverse]

def repairTransferWitness
    (target : ComplexityTransferTarget)
    (_ : RepairTransform) (w : RepairWitness) : Prop :=
  target = .runtime ∧ w = .runtimeBackpressure

def repairComplexityTransferSchema :
    ComplexityTransferSchema RepairTransform RepairWitness where
  eliminatedByProof := fun _ => False
  transferWitness := repairTransferWitness
  selectedWitness := runtimeAxisWitness
  coverageAssumptions := True
  exactnessAssumptions := True
  nonConclusions :=
    ¬ SelectedAndRuntimeAxesNonincreasing .entangled .repaired

theorem staticSplitRepair_not_eliminated_by_proof :
    ¬ ComplexityEliminatedByProof
      repairComplexityTransferSchema .staticSplitRepair := by
  simp [ComplexityEliminatedByProof, repairComplexityTransferSchema]

theorem staticSplitRepair_transfers_runtime :
    ComplexityTransferredTo repairComplexityTransferSchema
      .runtime .staticSplitRepair := by
  refine ⟨.runtimeBackpressure, ?_, ?_⟩
  · simp [repairComplexityTransferSchema, runtimeAxisWitness]
  · simp [repairComplexityTransferSchema, repairTransferWitness]

theorem repairComplexityTransfer_records_nonConclusion :
    repairComplexityTransferSchema.nonConclusions :=
  selectedRepairStep_not_all_axes_nonincreasing

structure RepairTransferCounterexamplePackage where
  selectedDecrease :
    RepairStepDecreases selectedStaticUniverse .entangled .repaired
  runtimeMeasureIncrease :
    ExtensionObstructionMeasure runtimeAxisUniverse .entangled <
      ExtensionObstructionMeasure runtimeAxisUniverse .repaired
  runtimeViolationAfter :
    MeasuredViolationExists (runtimeAxisUniverse.witnessAt .repaired)
      runtimeMeasuredWitnesses
  runtimeViolationCountBefore :
    violationCount (runtimeAxisUniverse.witnessAt .entangled)
      runtimeMeasuredWitnesses = 0
  runtimeViolationCountAfter :
    violationCount (runtimeAxisUniverse.witnessAt .repaired)
      runtimeMeasuredWitnesses = 1
  runtimeTransfer :
    ComplexityTransferredTo repairComplexityTransferSchema
      .runtime .staticSplitRepair
  nonConclusion :
    ¬ SelectedAndRuntimeAxesNonincreasing .entangled .repaired

def counterexamplePackage : RepairTransferCounterexamplePackage where
  selectedDecrease := selectedRepairStep_decreases
  runtimeMeasureIncrease := runtimeAxisMeasure_increases
  runtimeViolationAfter := runtimeAxis_measuredViolation_after
  runtimeViolationCountBefore := runtimeAxisViolationCount_before
  runtimeViolationCountAfter := runtimeAxisViolationCount_after
  runtimeTransfer := staticSplitRepair_transfers_runtime
  nonConclusion := selectedRepairStep_not_all_axes_nonincreasing

end RepairTransferCounterexample

end Formal.Arch
