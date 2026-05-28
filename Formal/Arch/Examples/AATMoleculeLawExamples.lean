import Formal.Arch.AAT.Core
import Formal.Arch.Examples.AtomFoundationExamples

namespace Formal.Arch.AATMoleculeLawExamples

open Formal.Arch.AtomFoundationExamples

/-- A singleton molecule over the pure atom axiom example. -/
def apiMolecule : AAT.Molecule exampleAtomAxiomSystem where
  atoms := fun atom => atom = ExampleAtom.apiComponent
  finiteConfiguration := True
  nonConclusions := True

/-- The singleton molecule contains only primitive atoms from the root system. -/
theorem apiMolecule_atom_primitive :
    exampleAtomAxiomSystem.Primitive ExampleAtom.apiComponent := by
  exact apiMolecule.atom_primitive (by rfl)

/-- A law that marks exactly the singleton molecule as bad. -/
def singletonBadLaw : AAT.DesignLaw exampleAtomAxiomSystem where
  Bad := fun molecule => molecule = apiMolecule
  evaluationBoundary := True
  nonConclusions := True

/-- Pure design laws do not create atoms in the underlying axiom system. -/
theorem singletonBadLaw_does_not_create_atoms :
    exampleAtomAxiomSystem.noLawCreatesAtoms := by
  exact singletonBadLaw.does_not_create_atoms

/-- The singleton molecule is a law-relative minimal bad molecule. -/
theorem singletonBadLaw_obstruction :
    AAT.ObstructionCircuit singletonBadLaw apiMolecule := by
  constructor
  · rfl
  · intro N hProper hBad
    change N = apiMolecule at hBad
    rw [hBad] at hProper
    exact hProper.2 (AAT.MoleculeSubset.refl apiMolecule)

/-- Minimal pure AAT surface over the example atom axiom system. -/
def examplePureTheory : AAT.PureTheory exampleAtomAxiomSystem where
  molecules := fun molecule => molecule = apiMolecule
  moleculeAtomsPrimitive := by
    intro molecule _hMolecule atom _hAtom
    exact exampleAtomAxiomSystem.primitive atom
  laws := fun law => law = singletonBadLaw
  circuits := fun _hLaw _hMolecule _hCircuit => True
  circuitEvidence := by
    intro _law _molecule _hLaw _hMolecule _hCircuit
    trivial
  noObservationDependency := True
  noObservationDependencyEvidence := trivial
  noLawCreatesAtomsEvidence :=
    exampleAtomAxiomSystem.law_does_not_create_atoms
  moleculeBoundary := True
  lawBoundary := True
  circuitBoundary := True
  nonConclusions := True

/-- The pure AAT surface keeps its observation independence accessor. -/
theorem examplePureTheory_independent_of_observation :
    examplePureTheory.noObservationDependency := by
  exact examplePureTheory.independent_of_observation

/-- The pure AAT surface inherits law independence from the root atom system. -/
theorem examplePureTheory_laws_do_not_create_atoms :
    exampleAtomAxiomSystem.noLawCreatesAtoms := by
  exact examplePureTheory.laws_do_not_create_atoms

/-- The selected obstruction circuit is carried by the pure theory surface. -/
theorem examplePureTheory_circuit_on_surface :
    examplePureTheory.circuits
      (by rfl : examplePureTheory.laws singletonBadLaw)
      (by rfl : examplePureTheory.molecules apiMolecule)
      singletonBadLaw_obstruction := by
  exact examplePureTheory.circuit_on_surface
    (by rfl) (by rfl) singletonBadLaw_obstruction

end Formal.Arch.AATMoleculeLawExamples
