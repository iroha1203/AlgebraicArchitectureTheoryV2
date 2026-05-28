import Formal.Arch.AAT.ZeroCurvature
import Formal.Arch.Examples.AATMoleculeLawExamples

namespace Formal.Arch.AATZeroCurvatureExamples

open Formal.Arch.AtomFoundationExamples
open Formal.Arch.AATMoleculeLawExamples

/-- A no-bad law over the example atom system. -/
def noBadLaw : AAT.DesignLaw exampleAtomAxiomSystem where
  Bad := fun _ => False
  evaluationBoundary := True
  nonConclusions := True

/-- The singleton molecule is the selected required molecule family. -/
def requiredApiMolecule :
    AAT.Molecule exampleAtomAxiomSystem -> Prop :=
  fun molecule => molecule = apiMolecule

/-- A pure AAT core over the example atom axiom system and no-bad law. -/
def noBadCore : AAT.AATCore exampleAtomAxiomSystem where
  molecules := fun molecule => molecule = apiMolecule
  moleculeAtomsPrimitive := by
    intro molecule _hMolecule atom _hAtom
    exact exampleAtomAxiomSystem.primitive atom
  laws := fun law => law = noBadLaw
  circuits := fun _hLaw _hMolecule _hCircuit => False
  circuitEvidence := by
    intro law _molecule hLaw _hMolecule hCircuit
    subst hLaw
    exact AAT.obstructionCircuit_bad hCircuit
  noObservationDependency := True
  noObservationDependencyEvidence := trivial
  noLawCreatesAtomsEvidence :=
    exampleAtomAxiomSystem.law_does_not_create_atoms
  moleculeBoundary := True
  lawBoundary := True
  circuitBoundary := True
  nonConclusions := True

/-- No-bad lawfulness bridge for the singleton required molecule family. -/
def noBadLawfulnessBridge :
    AAT.LawfulnessBridge noBadLaw requiredApiMolecule where
  badWitnessComplete := by
    intro _molecule _hRequired hBad
    cases hBad
  circuitBad := by
    intro _molecule _hRequired hCircuit
    exact AAT.obstructionCircuit_bad hCircuit
  coverageBoundary := True
  exactnessBoundary := True
  nonConclusions := True

/-- No required obstruction circuit exists for the no-bad law. -/
theorem noBadZeroCurvature :
    AAT.ZeroCurvature noBadLaw requiredApiMolecule := by
  intro _molecule _hRequired hCircuit
  exact AAT.obstructionCircuit_bad hCircuit

/-- Pure Atom-AAT zero-curvature theorem package over the example core. -/
def noBadZeroCurvaturePackage :
    AAT.ZeroCurvaturePackage noBadCore where
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
  zeroCurvature := noBadZeroCurvature
  coverageBoundary := True
  exactnessBoundary := True
  theoremPackageBoundary := True
  nonConclusions := True

/-- The package exposes the no-required-circuit theorem. -/
theorem noBadPackage_noRequiredObstructionCircuit :
    AAT.NoRequiredObstructionCircuit noBadLaw requiredApiMolecule := by
  exact noBadZeroCurvaturePackage.noRequiredObstructionCircuit

/-- The package derives lawfulness inside the selected molecule family. -/
theorem noBadPackage_lawfulWithinMoleculeConfiguration :
    AAT.LawfulWithinMoleculeConfiguration noBadLaw requiredApiMolecule := by
  exact noBadZeroCurvaturePackage.lawfulWithinMoleculeConfiguration

/-- The package derives lawfulness inside the selected pure AAT core. -/
theorem noBadPackage_lawfulWithinAATCore :
    AAT.LawfulWithinAATCore noBadCore noBadLaw requiredApiMolecule := by
  exact noBadZeroCurvaturePackage.lawfulWithinAATCore

/-- Required molecules selected by the package are selected by the core. -/
theorem noBadPackage_requiredMolecule_on_core :
    noBadCore.molecules apiMolecule := by
  exact noBadZeroCurvaturePackage.requiredMolecule_on_core rfl

/-- Atoms in required molecules remain primitive root atoms. -/
theorem noBadPackage_atom_of_requiredMolecule :
    exampleAtomAxiomSystem.Primitive ExampleAtom.apiComponent := by
  exact noBadZeroCurvaturePackage.atom_of_requiredMolecule
    (molecule := apiMolecule) rfl (by rfl)

/-- The zero-curvature package remains independent of observation boundaries. -/
theorem noBadPackage_core_independent_of_observation :
    noBadCore.noObservationDependency := by
  exact noBadZeroCurvaturePackage.core_independent_of_observation

/-- The selected law does not create atom existence. -/
theorem noBadPackage_law_does_not_create_atoms :
    exampleAtomAxiomSystem.noLawCreatesAtoms := by
  exact noBadZeroCurvaturePackage.law_does_not_create_atoms

end Formal.Arch.AATZeroCurvatureExamples
