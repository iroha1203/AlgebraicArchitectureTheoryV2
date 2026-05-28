import Formal.Arch.AAT.Molecule

namespace Formal.Arch
namespace AAT

universe u v

/--
A pure AAT design law over a fixed atom axiom system.

The law evaluates atom molecules by marking selected configurations as bad.  It
does not create atom existence and is not part of the atom ontology.
-/
structure DesignLaw (system : AtomAxiomSystem.{u, v}) where
  Bad : Molecule system -> Prop
  evaluationBoundary : Prop
  nonConclusions : Prop

namespace DesignLaw

/-- A molecule is lawful for a design law when it is not marked bad. -/
def Lawful {system : AtomAxiomSystem.{u, v}} (law : DesignLaw system)
    (M : Molecule system) : Prop :=
  ¬ law.Bad M

/-- Design laws evaluate existing atoms; they do not create atoms. -/
theorem does_not_create_atoms {system : AtomAxiomSystem.{u, v}}
    (_law : DesignLaw system) :
    system.noLawCreatesAtoms :=
  system.law_does_not_create_atoms

/-- Design laws do not change atom-level law independence. -/
theorem atom_law_independent {system : AtomAxiomSystem.{u, v}}
    (_law : DesignLaw system) (atom : system.Atom) :
    system.lawIndependent atom :=
  system.law_independent atom

end DesignLaw

end AAT
end Formal.Arch
