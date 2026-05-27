import Formal.Arch.Repair.AtomRepair
import Formal.Arch.Examples.AtomZeroCurvatureExamples

namespace Formal.Arch.AtomicExamples

inductive AtomRepairState where
  | withForbiddenEdge
  | repaired
  deriving DecidableEq, Repr

inductive AtomRepairRule where
  | removeForbiddenEdge
  deriving DecidableEq, Repr

def targetRepairedMolecules
    (molecule : AtomMolecule Component Edge Diagram) : Prop :=
  molecule = componentMolecule

theorem componentMolecule_not_forbiddenEdgeBad :
    ¬ forbiddenEdgeLaw.Bad componentMolecule := by
  intro hBad
  have hKind : relationAtom.kind = componentAtom.kind := by
    exact congrArg ArchitectureAtom.kind hBad
  simp [relationAtom, componentAtom] at hKind

theorem targetRepairedMolecules_no_forbiddenCircuit
    {molecule : AtomMolecule Component Edge Diagram}
    (hTarget : targetRepairedMolecules molecule) :
    ¬ ObstructionCircuit forbiddenEdgeLaw molecule := by
  intro hCircuit
  rw [hTarget] at hCircuit
  exact componentMolecule_not_forbiddenEdgeBad
    (obstructionCircuit_bad hCircuit)

def targetRepairedLawfulnessBridge :
    AtomLawfulnessBridge forbiddenEdgeLaw targetRepairedMolecules where
  badWitnessComplete := by
    intro molecule hTarget hBad
    exact False.elim
      (componentMolecule_not_forbiddenEdgeBad (by
        rw [hTarget] at hBad
        exact hBad))
  circuitBad := by
    intro molecule _hTarget hCircuit
    exact obstructionCircuit_bad hCircuit
  coverageBoundary := True
  exactnessBoundary := True
  nonConclusions := True

def forbiddenEdgeAtomRepairUniverse :
    AtomRepairUniverse
      forbiddenEdgeLaw targetRepairedMolecules AtomRepairState where
  witnessAt := fun
    | .withForbiddenEdge, _ => True
    | .repaired, _ => False
  measure := fun
    | .withForbiddenEdge => 1
    | .repaired => 0
  stateBoundary := True
  witnessBoundary := True
  measureBoundary := True
  nonConclusions := True

def forbiddenEdgeAtomRepairPlan :
    BoundedRepairPlan (Rule := AtomRepairRule)
      forbiddenEdgeAtomRepairUniverse.selectedObstructionUniverse
      AtomRepairState.withForbiddenEdge AtomRepairState.repaired where
  initialMeasure := 1
  sourceMeasureWithinBound := by
    simp [ExtensionObstructionMeasure,
      AtomRepairUniverse.selectedObstructionUniverse,
      forbiddenEdgeAtomRepairUniverse]
  finiteSteps := 1
  stepsWithinBound := by
    simp
  everyStepDecreases :=
    RepairStepDecreases
      forbiddenEdgeAtomRepairUniverse.selectedObstructionUniverse
      AtomRepairState.withForbiddenEdge AtomRepairState.repaired
  targetMeasureZero := by
    simp [ExtensionObstructionMeasure,
      AtomRepairUniverse.selectedObstructionUniverse,
      forbiddenEdgeAtomRepairUniverse]
  zeroMeasureClearsSelected := by
    intro _hZero witness _hSelected hAt
    exact hAt
  nonConclusions := True

def forbiddenEdgeFiniteRepairPackage :
    FiniteRepairPackage (Rule := AtomRepairRule)
      forbiddenEdgeAtomRepairUniverse.selectedObstructionUniverse
      AtomRepairState.withForbiddenEdge AtomRepairState.repaired where
  plan := forbiddenEdgeAtomRepairPlan
  coverageAssumptions := True
  exactnessAssumptions := True
  nonConclusions := True

def forbiddenEdgeAtomFiniteRepairPackage :
    AtomFiniteRepairPackage
      forbiddenEdgeLaw targetRepairedMolecules
      AtomRepairState AtomRepairRule
      AtomRepairState.withForbiddenEdge AtomRepairState.repaired where
  repairUniverse := forbiddenEdgeAtomRepairUniverse
  repair := forbiddenEdgeFiniteRepairPackage
  targetCircuitWitnessComplete := by
    intro molecule hTarget hCircuit
    exact False.elim
      (targetRepairedMolecules_no_forbiddenCircuit hTarget hCircuit)
  repairBoundary := True
  exactnessBoundary := True
  nonConclusions := True

def forbiddenEdgeAtomRepairTransitionPackage :
    AtomRepairTransitionPackage
      forbiddenEdgeLaw
      selectedForbiddenEdgeUniverse.selected
      targetRepairedMolecules
      AtomRepairState AtomRepairRule
      AtomRepairState.withForbiddenEdge AtomRepairState.repaired where
  sourceCircuitExists :=
    ⟨forbiddenEdgeMolecule, Or.inl rfl,
      singletonForbiddenMolecule_obstruction⟩
  repair := forbiddenEdgeAtomFiniteRepairPackage
  transitionBoundary := True
  nonConclusions := True

theorem forbiddenEdgeAtomRepair_source_has_circuit :
    ∃ molecule,
      selectedForbiddenEdgeUniverse.selected molecule ∧
        ObstructionCircuit forbiddenEdgeLaw molecule := by
  exact
    AtomRepairTransitionPackage.source_has_obstructionCircuit
      forbiddenEdgeAtomRepairTransitionPackage

theorem forbiddenEdgeAtomRepair_source_not_lawful :
    ¬ LawfulWithinAtomConfiguration
      forbiddenEdgeLaw selectedForbiddenEdgeUniverse.selected := by
  exact
    AtomRepairTransitionPackage.source_not_lawful_of_circuitBad
      forbiddenEdgeAtomRepairTransitionPackage
      (by
        intro molecule _hRequired hCircuit
        exact obstructionCircuit_bad hCircuit)

theorem forbiddenEdgeAtomRepair_target_noRequiredCircuit :
    NoRequiredObstructionCircuit
      forbiddenEdgeLaw targetRepairedMolecules := by
  exact
    AtomRepairTransitionPackage.target_noRequiredObstructionCircuit
      forbiddenEdgeAtomRepairTransitionPackage

theorem forbiddenEdgeAtomRepair_target_lawful :
    LawfulWithinAtomConfiguration
      forbiddenEdgeLaw targetRepairedMolecules := by
  exact
    AtomRepairTransitionPackage.target_lawful_of_bridge
      forbiddenEdgeAtomRepairTransitionPackage
      targetRepairedLawfulnessBridge

def noBadAtomRepairUniverse :
    AtomRepairUniverse
      noBadAtomLaw allSelectedMolecules AtomRepairState where
  witnessAt := fun
    | .withForbiddenEdge, _ => True
    | .repaired, _ => False
  measure := fun
    | .withForbiddenEdge => 1
    | .repaired => 0
  stateBoundary := True
  witnessBoundary := True
  measureBoundary := True
  nonConclusions := True

def noBadAtomRepairPlan :
    BoundedRepairPlan (Rule := AtomRepairRule)
      noBadAtomRepairUniverse.selectedObstructionUniverse
      AtomRepairState.withForbiddenEdge AtomRepairState.repaired where
  initialMeasure := 1
  sourceMeasureWithinBound := by
    simp [ExtensionObstructionMeasure,
      AtomRepairUniverse.selectedObstructionUniverse,
      noBadAtomRepairUniverse]
  finiteSteps := 1
  stepsWithinBound := by
    simp
  everyStepDecreases :=
    RepairStepDecreases
      noBadAtomRepairUniverse.selectedObstructionUniverse
      AtomRepairState.withForbiddenEdge AtomRepairState.repaired
  targetMeasureZero := by
    simp [ExtensionObstructionMeasure,
      AtomRepairUniverse.selectedObstructionUniverse,
      noBadAtomRepairUniverse]
  zeroMeasureClearsSelected := by
    intro _hZero witness _hSelected hAt
    exact hAt
  nonConclusions := True

def noBadFiniteRepairPackage :
    FiniteRepairPackage (Rule := AtomRepairRule)
      noBadAtomRepairUniverse.selectedObstructionUniverse
      AtomRepairState.withForbiddenEdge AtomRepairState.repaired where
  plan := noBadAtomRepairPlan
  coverageAssumptions := True
  exactnessAssumptions := True
  nonConclusions := True

def noBadAtomFiniteRepairPackage :
    AtomFiniteRepairPackage
      noBadAtomLaw allSelectedMolecules
      AtomRepairState AtomRepairRule
      AtomRepairState.withForbiddenEdge AtomRepairState.repaired where
  repairUniverse := noBadAtomRepairUniverse
  repair := noBadFiniteRepairPackage
  targetCircuitWitnessComplete := by
    intro molecule _hRequired hCircuit
    exact False.elim (obstructionCircuit_bad hCircuit)
  repairBoundary := True
  exactnessBoundary := True
  nonConclusions := True

def noEdgePureAtomRepairPackage :
    AtomAxiomatizedPureRepairPackage
      noEdgePureAtomAxiomatizedAATCore
      AtomRepairState AtomRepairRule
      AtomRepairState.withForbiddenEdge AtomRepairState.repaired where
  law := noBadAtomLaw
  requiredMolecule := allSelectedMolecules
  lawOnSurface := rfl
  requiredMoleculesOnSurface := by
    intro molecule _hRequired
    trivial
  repair := noBadAtomFiniteRepairPackage
  lawfulnessBridge := noBadAtomLawfulnessBridge
  noArchitectureSignatureDependency := True
  noArchitectureSignatureDependencyEvidence := trivial
  repairAxiomBoundary := True
  theoremPackageBoundary := True
  nonConclusions := True

theorem noEdgePureAtomRepair_independent_of_signature :
    noEdgePureAtomRepairPackage.noArchitectureSignatureDependency := by
  exact
    AtomAxiomatizedPureRepairPackage.independent_of_architecture_signature
      noEdgePureAtomRepairPackage

theorem noEdgePureAtomRepair_target_noRequiredCircuit :
    NoRequiredObstructionCircuit noBadAtomLaw allSelectedMolecules := by
  exact
    AtomAxiomatizedPureRepairPackage.target_noRequiredObstructionCircuit
      noEdgePureAtomRepairPackage

theorem noEdgePureAtomRepair_target_atomZeroCurvature :
    AtomZeroCurvature noBadAtomLaw allSelectedMolecules := by
  exact
    AtomAxiomatizedPureRepairPackage.target_atomZeroCurvature
      noEdgePureAtomRepairPackage

def noEdgePureAtomRepairZeroCurvatureTheoremPackage :
    AtomZeroCurvatureTheoremPackage noEdgePureAtomAxiomatizedAATCore :=
  AtomAxiomatizedPureRepairPackage.atomZeroCurvatureTheoremPackage
    noEdgePureAtomRepairPackage

theorem noEdgePureAtomRepair_target_atomLawful :
    LawfulWithinAtomConfiguration noBadAtomLaw allSelectedMolecules := by
  exact
    AtomAxiomatizedPureRepairPackage.target_atomLawful
      noEdgePureAtomRepairPackage

theorem noEdgePureAtomRepair_law_does_not_create_atoms :
    (noEdgePureAtomAxiomatizedAATCore.lawSeparation noBadAtomLaw rfl).lawDoesNotCreateAtoms := by
  exact
    AtomAxiomatizedPureRepairPackage.law_does_not_create_atoms
      noEdgePureAtomRepairPackage

def noEdgeAtomAxiomatizedRepairPackage :
    AtomAxiomatizedRepairPackage
      noEdgeArchitectureLawModel Edge Diagram
      AtomRepairState AtomRepairRule
      AtomRepairState.withForbiddenEdge AtomRepairState.repaired where
  aat := noEdgeAtomAxiomatizedAAT
  repair := noBadAtomFiniteRepairPackage
  repairAxiomBoundary := True
  theoremPackageBoundary := True
  nonConclusions := True

theorem noEdgeAtomRepair_target_atomLawful :
    LawfulWithinAtomConfiguration
      noEdgeAtomAxiomatizedAAT.zeroCurvature.law
      noEdgeAtomAxiomatizedAAT.zeroCurvature.requiredMolecule := by
  exact
    AtomAxiomatizedRepairPackage.target_atomLawful
      noEdgeAtomAxiomatizedRepairPackage

theorem noEdgeAtomRepair_architectureLawful :
    ArchitectureSignature.ArchitectureLawful
      noEdgeArchitectureLawModel := by
  exact
    AtomAxiomatizedRepairPackage.architectureLawful_of_repair
      noEdgeAtomAxiomatizedRepairPackage

theorem noEdgeAtomRepair_requiredSignatureAxesZero :
    ArchitectureSignature.RequiredSignatureAxesZero
      (ArchitectureSignature.ArchitectureLawModel.signatureOf
        noEdgeArchitectureLawModel) := by
  exact
    AtomAxiomatizedRepairPackage.requiredSignatureAxesZero_of_repair
      noEdgeAtomAxiomatizedRepairPackage

theorem noEdgeAtomRepair_zeroCurvatureTheoremPackage :
    ArchitectureSignature.ArchitectureZeroCurvatureTheoremPackage
      noEdgeArchitectureLawModel := by
  exact
    AtomAxiomatizedRepairPackage.architectureZeroCurvatureTheoremPackage_of_repair
      noEdgeAtomAxiomatizedRepairPackage

end Formal.Arch.AtomicExamples
