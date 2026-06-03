import Formal.Arch.AAT.Molecule
import Formal.Arch.AAT.AtomComposition

namespace Formal.Arch
namespace AAT

universe u v

/--
Every required port of every selected atom is matched by a compatible selected
neighboring atom.
-/
def RequiredPortsMatched {system : AtomAxiomSystem.{u, v}}
    (presentation : AtomShapePresentation system)
    (atoms : system.Atom -> Prop) : Prop :=
  ∀ {atom port},
    atoms atom ->
    (AtomShapeOf presentation atom).valence.requiredPort port ->
      ∃ other otherPort,
        atoms other ∧
        other ≠ atom ∧
        (AtomShapeOf presentation other).valence.ports otherPort ∧
        PortCompatible port otherPort

/--
Atom-generated molecule.

This is the first molecule notion that satisfies the reconstruction plan:
selected atoms are primitive, finite, pairwise compatible through their shapes,
and required ports must be matched inside the selected configuration.
-/
structure GeneratedMolecule {system : AtomAxiomSystem.{u, v}}
    (presentation : AtomShapePresentation system) where
  atoms : system.Atom -> Prop
  finiteConfiguration : Prop
  atomsPrimitive :
    ∀ atom, atoms atom -> system.Primitive atom
  compositionGraph : CompositionGraph presentation atoms
  requiredPortsMatched :
    RequiredPortsMatched presentation atoms
  notArbitrarySet : Prop
  notArbitrarySetEvidence : notArbitrarySet

namespace GeneratedMolecule

/-- Forget only the compatibility evidence and recover the legacy molecule carrier. -/
def toMolecule {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    (molecule : GeneratedMolecule presentation) : Molecule system where
  atoms := molecule.atoms
  finiteConfiguration := molecule.finiteConfiguration
  nonConclusions := True

/-- Generated molecules contain only primitive atoms from the root system. -/
theorem atoms_primitive {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    (molecule : GeneratedMolecule presentation)
    {atom : system.Atom}
    (hAtom : molecule.atoms atom) :
    system.Primitive atom :=
  molecule.atomsPrimitive atom hAtom

/-- Distinct atoms in a generated molecule compose through their shapes. -/
def compatible_pairs {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    (molecule : GeneratedMolecule presentation)
    {left right : system.Atom}
    (hLeft : molecule.atoms left)
    (hRight : molecule.atoms right)
    (hDistinct : left ≠ right) :
    CompatibleComposition
      (AtomShapeOf presentation left)
      (AtomShapeOf presentation right) :=
  molecule.compositionGraph.compatible_pairs hLeft hRight hDistinct

/-- Generated molecules are explicitly not arbitrary atom sets. -/
theorem not_arbitrary_set {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    (molecule : GeneratedMolecule presentation) :
    molecule.notArbitrarySet :=
  molecule.notArbitrarySetEvidence

/-- Incompatible selected atom pairs cannot inhabit a generated molecule. -/
theorem incompatible_slots_not_generatedMolecule
    {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    (molecule : GeneratedMolecule presentation)
    {left right : system.Atom}
    (hLeft : molecule.atoms left)
    (hRight : molecule.atoms right)
    (hDistinct : left ≠ right)
    (hIncompatible :
      CompatibleComposition
        (AtomShapeOf presentation left)
        (AtomShapeOf presentation right) -> False) :
    False :=
  hIncompatible
    (molecule.compatible_pairs hLeft hRight hDistinct)

/-- Missing required port matches cannot inhabit a generated molecule. -/
theorem missing_required_port_not_generatedMolecule
    {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    (molecule : GeneratedMolecule presentation)
    {atom : system.Atom}
    {port : AtomPort}
    (hAtom : molecule.atoms atom)
    (hRequired :
      (AtomShapeOf presentation atom).valence.requiredPort port)
    (hMissing :
      ¬ ∃ other otherPort,
        molecule.atoms other ∧
        other ≠ atom ∧
        (AtomShapeOf presentation other).valence.ports otherPort ∧
        PortCompatible port otherPort) :
    False :=
  hMissing (molecule.requiredPortsMatched hAtom hRequired)

end GeneratedMolecule

end AAT
end Formal.Arch
