import Formal.Arch.AAT.Core

namespace Formal.Arch
namespace AAT

universe u v

/--
Lawfulness inside a selected Atom-generated AAT core.

This packages the core membership assumptions together with lawfulness over the
selected required molecule family.
-/
structure LawfulWithinAATCore {system : AtomAxiomSystem.{u, v}}
    (core : AATCore system)
    (law : DesignLaw system)
    (requiredMolecule : Molecule system -> Prop) where
  lawOnCore : core.laws law
  requiredMoleculesOnCore :
    ∀ molecule, requiredMolecule molecule -> core.molecules molecule
  lawful : LawfulWithinMoleculeConfiguration law requiredMolecule

/--
Atom-generated zero curvature.

At pure AAT level, zero curvature is the absence of required law-relative
obstruction circuits.  Signature axes, ArchMap observations, and SFT forecasts
are later readings, not definition conditions.
-/
def ZeroCurvature {system : AtomAxiomSystem.{u, v}}
    (law : DesignLaw system)
    (requiredMolecule : Molecule system -> Prop) : Prop :=
  NoRequiredObstructionCircuit law requiredMolecule

theorem zeroCurvature_iff_noRequiredObstructionCircuit
    {system : AtomAxiomSystem.{u, v}}
    {law : DesignLaw system}
    {requiredMolecule : Molecule system -> Prop} :
    ZeroCurvature law requiredMolecule ↔
      NoRequiredObstructionCircuit law requiredMolecule := by
  rfl

/--
Pure Atom-AAT zero-curvature theorem package.

The package starts from an `AATCore system`, a selected design law, selected
required molecules, and explicit coverage / exactness bridge assumptions.  It
derives lawfulness inside the same Atom-generated core without importing
observation, Signature, or forecast premises.
-/
structure ZeroCurvaturePackage {system : AtomAxiomSystem.{u, v}}
    (core : AATCore system) where
  law : DesignLaw system
  requiredMolecule : Molecule system -> Prop
  lawOnCore : core.laws law
  requiredMoleculesOnCore :
    ∀ molecule, requiredMolecule molecule -> core.molecules molecule
  requiredCircuitsOnCore :
    ∀ {molecule},
      (hRequired : requiredMolecule molecule) ->
      (hCircuit : ObstructionCircuit law molecule) ->
        core.circuits lawOnCore
          (requiredMoleculesOnCore molecule hRequired) hCircuit
  lawfulnessBridge : LawfulnessBridge law requiredMolecule
  zeroCurvature : ZeroCurvature law requiredMolecule
  coverageBoundary : Prop
  exactnessBoundary : Prop
  theoremPackageBoundary : Prop
  nonConclusions : Prop

namespace ZeroCurvaturePackage

/-- The package exposes no required obstruction circuit directly. -/
theorem noRequiredObstructionCircuit {system : AtomAxiomSystem.{u, v}}
    {core : AATCore system}
    (pkg : ZeroCurvaturePackage core) :
    NoRequiredObstructionCircuit pkg.law pkg.requiredMolecule :=
  zeroCurvature_iff_noRequiredObstructionCircuit.mp pkg.zeroCurvature

/-- Zero curvature gives lawfulness over the selected molecule family. -/
theorem lawfulWithinMoleculeConfiguration
    {system : AtomAxiomSystem.{u, v}}
    {core : AATCore system}
    (pkg : ZeroCurvaturePackage core) :
    LawfulWithinMoleculeConfiguration pkg.law pkg.requiredMolecule :=
  (LawfulnessBridge.lawful_iff_no_obstructionCircuit
    pkg.lawfulnessBridge).mpr
    pkg.noRequiredObstructionCircuit

/-- Zero curvature gives lawfulness inside the same selected AAT core. -/
def lawfulWithinAATCore {system : AtomAxiomSystem.{u, v}}
    {core : AATCore system}
    (pkg : ZeroCurvaturePackage core) :
    LawfulWithinAATCore core pkg.law pkg.requiredMolecule where
  lawOnCore := pkg.lawOnCore
  requiredMoleculesOnCore := pkg.requiredMoleculesOnCore
  lawful := pkg.lawfulWithinMoleculeConfiguration

/-- Required molecules are selected by the core carried by the package. -/
theorem requiredMolecule_on_core {system : AtomAxiomSystem.{u, v}}
    {core : AATCore system}
    (pkg : ZeroCurvaturePackage core)
    {molecule : Molecule system}
    (hRequired : pkg.requiredMolecule molecule) :
    core.molecules molecule :=
  pkg.requiredMoleculesOnCore molecule hRequired

/-- Required obstruction circuits, if assumed, are selected by the same core. -/
theorem requiredCircuit_on_core {system : AtomAxiomSystem.{u, v}}
    {core : AATCore system}
    (pkg : ZeroCurvaturePackage core)
    {molecule : Molecule system}
    (hRequired : pkg.requiredMolecule molecule)
    (hCircuit : ObstructionCircuit pkg.law molecule) :
    core.circuits pkg.lawOnCore
      (pkg.requiredMoleculesOnCore molecule hRequired) hCircuit :=
  pkg.requiredCircuitsOnCore hRequired hCircuit

/-- Atoms in required molecules are primitive atoms of the root system. -/
theorem atom_of_requiredMolecule {system : AtomAxiomSystem.{u, v}}
    {core : AATCore system}
    (pkg : ZeroCurvaturePackage core)
    {molecule : Molecule system}
    (hRequired : pkg.requiredMolecule molecule)
    {atom : system.Atom}
    (hAtom : molecule.atoms atom) :
    system.Primitive atom :=
  core.atom_of_selected_molecule
    (pkg.requiredMolecule_on_core hRequired) hAtom

/-- The package inherits observation independence from the core. -/
theorem core_independent_of_observation
    {system : AtomAxiomSystem.{u, v}}
    {core : AATCore system}
    (_pkg : ZeroCurvaturePackage core) :
    core.noObservationDependency :=
  core.independent_of_observation

/-- The selected law does not create atoms. -/
theorem law_does_not_create_atoms
    {system : AtomAxiomSystem.{u, v}}
    {core : AATCore system}
    (pkg : ZeroCurvaturePackage core) :
    system.noLawCreatesAtoms :=
  pkg.law.does_not_create_atoms

end ZeroCurvaturePackage

end AAT
end Formal.Arch
