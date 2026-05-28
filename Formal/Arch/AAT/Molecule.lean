import Formal.Arch.Atom.Foundation

namespace Formal.Arch
namespace AAT

universe u v q

/--
A pure AAT molecule over a fixed atom axiom system.

The molecule is a finite configuration of already-existing atoms.  It is not an
observation artifact, a role, a pattern, or a new atom family.
-/
structure Molecule (system : AtomAxiomSystem.{u, v}) where
  atoms : system.Atom -> Prop
  finiteConfiguration : Prop
  nonConclusions : Prop

namespace Molecule

/-- Membership predicate for atoms in a pure molecule. -/
def Contains {system : AtomAxiomSystem.{u, v}} (M : Molecule system)
    (atom : system.Atom) : Prop :=
  M.atoms atom

/-- Every atom in a pure molecule is still a primitive atom of the root system. -/
theorem atom_primitive {system : AtomAxiomSystem.{u, v}}
    (M : Molecule system) {atom : system.Atom} (_hAtom : M.Contains atom) :
    system.Primitive atom :=
  system.primitive atom

/--
Atom membership in a molecule does not make atom existence depend on
observation boundaries.
-/
theorem atom_boundary_independent {system : AtomAxiomSystem.{u, v}}
    (M : Molecule system) {atom : system.Atom} (_hAtom : M.Contains atom) :
    system.boundaryIndependent atom :=
  system.boundary_independent atom

/--
Atom membership in a molecule does not make atom existence depend on selected
design laws.
-/
theorem atom_law_independent {system : AtomAxiomSystem.{u, v}}
    (M : Molecule system) {atom : system.Atom} (_hAtom : M.Contains atom) :
    system.lawIndependent atom :=
  system.law_independent atom

end Molecule

/-- Inclusion of pure AAT molecules. -/
def MoleculeSubset {system : AtomAxiomSystem.{u, v}}
    (M N : Molecule system) : Prop :=
  ∀ atom, M.atoms atom -> N.atoms atom

namespace MoleculeSubset

theorem refl {system : AtomAxiomSystem.{u, v}} (M : Molecule system) :
    MoleculeSubset M M := by
  intro atom hAtom
  exact hAtom

theorem trans {system : AtomAxiomSystem.{u, v}}
    {M N P : Molecule system}
    (hMN : MoleculeSubset M N)
    (hNP : MoleculeSubset N P) :
    MoleculeSubset M P := by
  intro atom hAtom
  exact hNP atom (hMN atom hAtom)

end MoleculeSubset

/-- Proper molecule inclusion. -/
def ProperSubmolecule {system : AtomAxiomSystem.{u, v}}
    (M N : Molecule system) : Prop :=
  MoleculeSubset M N ∧ ¬ MoleculeSubset N M

/--
A role is an interpretation of a molecule, not a primitive atom.
-/
structure RoleInterpretation (system : AtomAxiomSystem.{u, v})
    (Role : Type q) where
  molecule : Molecule system
  role : Role
  interprets : Prop
  interpretationBoundary : Prop
  nonConclusions : Prop

namespace RoleInterpretation

/-- Forget the role interpretation and return its underlying molecule. -/
def toMolecule {system : AtomAxiomSystem.{u, v}} {Role : Type q}
    (interpretation : RoleInterpretation system Role) : Molecule system :=
  interpretation.molecule

/-- Role interpretation does not create atoms in the root axiom system. -/
theorem does_not_create_atoms {system : AtomAxiomSystem.{u, v}} {Role : Type q}
    (_interpretation : RoleInterpretation system Role) :
    system.noLawCreatesAtoms :=
  system.law_does_not_create_atoms

end RoleInterpretation

/--
A design pattern is an interpretation of a molecule configuration, not a
primitive atom.
-/
structure PatternInterpretation (system : AtomAxiomSystem.{u, v})
    (Pattern : Type q) where
  molecule : Molecule system
  pattern : Pattern
  interprets : Prop
  interpretationBoundary : Prop
  nonConclusions : Prop

namespace PatternInterpretation

/-- Forget the pattern interpretation and return its underlying molecule. -/
def toMolecule {system : AtomAxiomSystem.{u, v}} {Pattern : Type q}
    (interpretation : PatternInterpretation system Pattern) : Molecule system :=
  interpretation.molecule

/-- Pattern interpretation does not create atoms in the root axiom system. -/
theorem does_not_create_atoms {system : AtomAxiomSystem.{u, v}}
    {Pattern : Type q}
    (_interpretation : PatternInterpretation system Pattern) :
    system.noLawCreatesAtoms :=
  system.law_does_not_create_atoms

end PatternInterpretation

end AAT
end Formal.Arch
