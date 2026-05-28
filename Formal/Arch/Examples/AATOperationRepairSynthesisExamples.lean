import Formal.Arch.AAT.Operation
import Formal.Arch.AAT.Repair
import Formal.Arch.AAT.Synthesis
import Formal.Arch.Examples.AATZeroCurvatureExamples

namespace Formal.Arch.AATOperationRepairSynthesisExamples

open Formal.Arch.AtomFoundationExamples
open Formal.Arch.AATMoleculeLawExamples
open Formal.Arch.AATZeroCurvatureExamples

/-- Identity operation preservation over the no-bad pure AAT core. -/
def identityOperationPackage :
    AAT.OperationPreservationPackage noBadCore noBadCore where
  selectedMolecule := requiredApiMolecule
  selectedLaw := fun law => law = noBadLaw
  preservesMolecule := by
    intro _molecule _hSelected hSource
    exact hSource
  preservesLaw := by
    intro _law _hSelected hSource
    exact hSource
  operationDoesNotCreateAtomsEvidence :=
    exampleAtomAxiomSystem.tool_output_does_not_create_atoms
  operationBoundary := True
  theoremPackageBoundary := True
  nonConclusions := True

theorem identityOperation_target_molecule :
    noBadCore.molecules apiMolecule := by
  exact identityOperationPackage.target_molecule rfl rfl

theorem identityOperation_target_law :
    noBadCore.laws noBadLaw := by
  exact identityOperationPackage.target_law rfl rfl

theorem identityOperation_does_not_create_atoms :
    exampleAtomAxiomSystem.noToolOutputCreatesAtoms := by
  exact identityOperationPackage.operation_does_not_create_atoms

/-- Repair clearing package over the no-bad pure AAT core. -/
def noBadRepairClearingPackage :
    AAT.RepairClearingPackage noBadCore Unit Unit () () where
  law := noBadLaw
  requiredMolecule := requiredApiMolecule
  lawOnCore := rfl
  requiredMoleculesOnCore := by
    intro molecule hRequired
    exact hRequired
  requiredCircuitsOnCore := by
    intro molecule hRequired hCircuit
    exact noBadCore.circuit_on_surface rfl hRequired hCircuit
  lawfulnessBridge := noBadLawfulnessBridge
  targetNoRequiredObstructionCircuit := noBadZeroCurvature
  repairDoesNotCreateAtomsEvidence :=
    exampleAtomAxiomSystem.tool_output_does_not_create_atoms
  repairBoundary := True
  exactnessBoundary := True
  nonConclusions := True

theorem noBadRepair_target_noRequiredObstructionCircuit :
    AAT.NoRequiredObstructionCircuit noBadLaw requiredApiMolecule := by
  exact noBadRepairClearingPackage.target_noRequiredObstructionCircuit

theorem noBadRepair_target_lawful :
    AAT.LawfulWithinMoleculeConfiguration noBadLaw requiredApiMolecule := by
  exact noBadRepairClearingPackage.target_lawfulWithinMoleculeConfiguration

theorem noBadRepair_does_not_create_atoms :
    exampleAtomAxiomSystem.noToolOutputCreatesAtoms := by
  exact noBadRepairClearingPackage.repair_does_not_create_atoms

/-- Synthesis soundness package over the no-bad pure AAT core. -/
def noBadSynthesisSoundnessPackage :
    AAT.SynthesisSoundnessPackage noBadCore Unit where
  law := noBadLaw
  requiredMolecule := requiredApiMolecule
  lawOnCore := rfl
  requiredMoleculesOnCore := by
    intro molecule hRequired
    exact hRequired
  requiredCircuitsOnCore := by
    intro molecule hRequired hCircuit
    exact noBadCore.circuit_on_surface rfl hRequired hCircuit
  lawfulnessBridge := noBadLawfulnessBridge
  candidate := ()
  candidateNoRequiredObstructionCircuit := noBadZeroCurvature
  synthesisDoesNotCreateAtomsEvidence :=
    exampleAtomAxiomSystem.tool_output_does_not_create_atoms
  coverageBoundary := True
  exactnessBoundary := True
  synthesisBoundary := True
  nonConclusions := True

theorem noBadSynthesis_candidate_noRequiredObstructionCircuit :
    AAT.NoRequiredObstructionCircuit noBadLaw requiredApiMolecule := by
  exact noBadSynthesisSoundnessPackage.candidate_noRequiredObstructionCircuit

theorem noBadSynthesis_candidate_lawful :
    AAT.LawfulWithinMoleculeConfiguration noBadLaw requiredApiMolecule := by
  exact noBadSynthesisSoundnessPackage.candidate_lawfulWithinMoleculeConfiguration

theorem noBadSynthesis_does_not_create_atoms :
    exampleAtomAxiomSystem.noToolOutputCreatesAtoms := by
  exact noBadSynthesisSoundnessPackage.synthesis_does_not_create_atoms

end Formal.Arch.AATOperationRepairSynthesisExamples
