import Formal.Arch.AAT.Circuit

namespace Formal.Arch
namespace AAT

universe u v

/--
Pure AAT surface generated from an atom axiom system.

This is the boundary-free AAT reading: atoms come from `system`, molecules are
finite configurations over `system.Atom`, laws evaluate those molecules, and
obstruction circuits are law-relative minimal bad molecules.
-/
structure PureTheory (system : AtomAxiomSystem.{u, v}) where
  molecules : Molecule system -> Prop
  moleculeAtomsPrimitive :
    ∀ molecule, molecules molecule ->
      ∀ atom, molecule.atoms atom -> system.Primitive atom
  laws : DesignLaw system -> Prop
  circuits :
    ∀ {law : DesignLaw system} {molecule : Molecule system},
      laws law -> molecules molecule -> ObstructionCircuit law molecule -> Prop
  circuitEvidence :
    ∀ {law : DesignLaw system} {molecule : Molecule system}
      (hLaw : laws law)
      (hMolecule : molecules molecule)
      (hCircuit : ObstructionCircuit law molecule),
        circuits hLaw hMolecule hCircuit
  noObservationDependency : Prop
  noObservationDependencyEvidence : noObservationDependency
  noLawCreatesAtomsEvidence : system.noLawCreatesAtoms
  moleculeBoundary : Prop
  lawBoundary : Prop
  circuitBoundary : Prop
  nonConclusions : Prop

namespace PureTheory

/-- A selected molecule contains only primitive atoms from the root system. -/
theorem atom_of_selected_molecule {system : AtomAxiomSystem.{u, v}}
    (theory : PureTheory system)
    {molecule : Molecule system}
    (hMolecule : theory.molecules molecule)
    {atom : system.Atom}
    (hAtom : molecule.atoms atom) :
    system.Primitive atom :=
  theory.moleculeAtomsPrimitive molecule hMolecule atom hAtom

/-- Pure AAT is independent of observation boundaries. -/
theorem independent_of_observation {system : AtomAxiomSystem.{u, v}}
    (theory : PureTheory system) :
    theory.noObservationDependency :=
  theory.noObservationDependencyEvidence

/-- Pure AAT laws do not create atom existence. -/
theorem laws_do_not_create_atoms {system : AtomAxiomSystem.{u, v}}
    (theory : PureTheory system) :
    system.noLawCreatesAtoms :=
  theory.noLawCreatesAtomsEvidence

/-- Selected obstruction circuits are carried by the pure theory surface. -/
theorem circuit_on_surface {system : AtomAxiomSystem.{u, v}}
    (theory : PureTheory system)
    {law : DesignLaw system} {molecule : Molecule system}
    (hLaw : theory.laws law)
    (hMolecule : theory.molecules molecule)
    (hCircuit : ObstructionCircuit law molecule) :
    theory.circuits hLaw hMolecule hCircuit :=
  theory.circuitEvidence hLaw hMolecule hCircuit

end PureTheory

end AAT
end Formal.Arch
