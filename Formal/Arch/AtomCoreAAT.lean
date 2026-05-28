import Formal.Arch.AAT.Core
import Formal.Arch.Atomization

namespace Formal.Arch

universe u v w

/--
Boundary-free pure AAT core generated directly from an `AtomAxiomSystem`.

This is the new source-of-truth surface for Atom-first AAT.  The
`AtomAxiomatizedPureAAT` structures below remain as compatibility bridges until
the dependent zero-curvature, operation, repair, synthesis, and Signature
layers are migrated and the obsolete Lean code is deleted.
-/
abbrev AtomAxiomSystemPureAAT (system : AtomAxiomSystem.{u, v}) :=
  AAT.PureTheory system

/--
Pure Atom-axiomatized AAT core.

This is the Lean entrypoint for reading AAT as a theory generated from Atom
Core facts alone.  It has no `ArchitectureSignature`, ArchSig observation, or
SFT forecasting field.  Laws and obstruction circuits are selected over an
already-selected atom surface, while `AtomLawSeparation` records that laws
evaluate existing atoms instead of creating atom existence.
-/
structure AtomAxiomatizedPureAAT (C : Type u) (E : Type v) (D : Type w) where
  surface : AATPureTheorySurface C E D
  lawSeparation :
    ∀ law, surface.laws law -> AtomLawSeparation C E D
  lawSeparationMatches :
    ∀ law hLaw, (lawSeparation law hLaw).law = law
  lawEvaluatesSurfaceMolecules :
    ∀ law hLaw molecule,
      surface.molecules molecule ->
        (lawSeparation law hLaw).selectedMolecule molecule
  circuitClosure :
    ∀ {law : DesignLaw C E D} {molecule : AtomMolecule C E D}
      (hLaw : surface.laws law)
      (hMolecule : surface.molecules molecule)
      (hCircuit : ObstructionCircuit law molecule),
        surface.circuits hLaw hMolecule hCircuit
  noArchitectureSignatureDependency : Prop
  noArchitectureSignatureDependencyEvidence :
    noArchitectureSignatureDependency
  atomAxiomBoundary : Prop
  moleculeAxiomBoundary : Prop
  lawAxiomBoundary : Prop
  circuitAxiomBoundary : Prop
  pureTheoryBoundary : Prop
  nonConclusions : Prop

namespace AtomAxiomatizedPureAAT

/-- The pure Atom-AAT core is independent of observation tooling. -/
theorem independent_of_observation
    {C : Type u} {E : Type v} {D : Type w}
    (core : AtomAxiomatizedPureAAT C E D) :
    core.surface.noObservationDependency :=
  core.surface.independent_of_observation

/-- The pure Atom-AAT core is independent of SFT forecasting. -/
theorem independent_of_sft
    {C : Type u} {E : Type v} {D : Type w}
    (core : AtomAxiomatizedPureAAT C E D) :
    core.surface.noSFTDependency :=
  core.surface.independent_of_sft

/-- The pure Atom-AAT core is independent of ArchitectureSignature packages. -/
theorem independent_of_architecture_signature
    {C : Type u} {E : Type v} {D : Type w}
    (core : AtomAxiomatizedPureAAT C E D) :
    core.noArchitectureSignatureDependency :=
  core.noArchitectureSignatureDependencyEvidence

/-- Selected atoms are primitive atom-kind facts in the current Atom Core grammar. -/
theorem selected_atom_is_primitive
    {C : Type u} {E : Type v} {D : Type w}
    (core : AtomAxiomatizedPureAAT C E D)
    {atom : ArchitectureAtom C E D}
    (_hAtom : core.surface.atoms atom) :
    atom.kind.IsPrimitive :=
  AtomKind.isPrimitive atom.kind

/-- A selected law separation belongs to the law selected by the surface. -/
theorem selected_law_matches
    {C : Type u} {E : Type v} {D : Type w}
    (core : AtomAxiomatizedPureAAT C E D)
    {law : DesignLaw C E D}
    (hLaw : core.surface.laws law) :
    (core.lawSeparation law hLaw).law = law :=
  core.lawSeparationMatches law hLaw

/-- Selected laws evaluate already-selected surface molecules. -/
theorem selected_law_evaluates_surface_molecule
    {C : Type u} {E : Type v} {D : Type w}
    (core : AtomAxiomatizedPureAAT C E D)
    {law : DesignLaw C E D}
    (hLaw : core.surface.laws law)
    {molecule : AtomMolecule C E D}
    (hMolecule : core.surface.molecules molecule) :
    (core.lawSeparation law hLaw).selectedMolecule molecule :=
  core.lawEvaluatesSurfaceMolecules law hLaw molecule hMolecule

/-- Selected molecules are made only from selected atoms on the pure surface. -/
theorem selected_molecule_atom_on_surface
    {C : Type u} {E : Type v} {D : Type w}
    (core : AtomAxiomatizedPureAAT C E D)
    {molecule : AtomMolecule C E D}
    (hMolecule : core.surface.molecules molecule)
    {atom : ArchitectureAtom C E D}
    (hAtom : molecule.atoms atom) :
    core.surface.atoms atom :=
  core.surface.atom_of_selected_molecule hMolecule hAtom

/-- Selected molecules are supported by the pure core's selected atom universe. -/
theorem selected_molecule_supportedBy_surface_atoms
    {C : Type u} {E : Type v} {D : Type w}
    (core : AtomAxiomatizedPureAAT C E D)
    {molecule : AtomMolecule C E D}
    (hMolecule : core.surface.molecules molecule) :
    AtomMoleculeSupportedBy core.surface.selectedAtomUniverse molecule :=
  core.surface.selected_molecule_supportedBy_selected_atoms hMolecule

/--
Every atom occurring in a selected molecule is still a primitive Atom Core
fact.
-/
theorem selected_molecule_atom_is_primitive
    {C : Type u} {E : Type v} {D : Type w}
    (core : AtomAxiomatizedPureAAT C E D)
    {molecule : AtomMolecule C E D}
    (hMolecule : core.surface.molecules molecule)
    {atom : ArchitectureAtom C E D}
    (hAtom : molecule.atoms atom) :
    PrimitiveArchitectureAtom atom :=
  have _hSelected : core.surface.atoms atom :=
    core.selected_molecule_atom_on_surface hMolecule hAtom
  primitiveArchitectureAtom_constructive atom

/--
Atoms in a selected semantic molecule are both selected by the pure Atom-AAT
surface and semantic/interpretation atoms.
-/
theorem selected_semantic_molecule_atom_on_surface_and_semantic
    {C : Type u} {E : Type v} {D : Type w}
    (core : AtomAxiomatizedPureAAT C E D)
    {molecule : AtomMolecule C E D}
    (hSemanticMolecule :
      core.surface.SemanticMoleculeOnSurface molecule)
    {atom : ArchitectureAtom C E D}
    (hAtom : molecule.atoms atom) :
    core.surface.atoms atom ∧ atom.IsSemanticInterpretation :=
  core.surface.semantic_atom_of_selected_semantic_molecule
    hSemanticMolecule hAtom

/-- Selected laws do not create primitive atom existence. -/
theorem selected_law_does_not_create_atoms
    {C : Type u} {E : Type v} {D : Type w}
    (core : AtomAxiomatizedPureAAT C E D)
    {law : DesignLaw C E D}
    (hLaw : core.surface.laws law) :
    (core.lawSeparation law hLaw).lawDoesNotCreateAtoms :=
  (core.lawSeparation law hLaw).law_does_not_create_atoms

/-- Selected laws do not change primitive atom existence. -/
theorem selected_law_does_not_change_atom_existence
    {C : Type u} {E : Type v} {D : Type w}
    (core : AtomAxiomatizedPureAAT C E D)
    {law : DesignLaw C E D}
    (hLaw : core.surface.laws law) :
    (core.lawSeparation law hLaw).lawDoesNotChangeAtomExistence :=
  (core.lawSeparation law hLaw).law_does_not_change_atom_existence

/-- Selected laws evaluate atoms that already exist before law selection. -/
theorem selected_law_atoms_exist_before_law
    {C : Type u} {E : Type v} {D : Type w}
    (core : AtomAxiomatizedPureAAT C E D)
    {law : DesignLaw C E D}
    (hLaw : core.surface.laws law) :
    (core.lawSeparation law hLaw).atomsExistBeforeLaw :=
  (core.lawSeparation law hLaw).atoms_exist_before_law

/--
Every selected law/molecule obstruction circuit is selected by the pure atom
surface.
-/
theorem circuit_on_surface
    {C : Type u} {E : Type v} {D : Type w}
    (core : AtomAxiomatizedPureAAT C E D)
    {law : DesignLaw C E D} {molecule : AtomMolecule C E D}
    (hLaw : core.surface.laws law)
    (hMolecule : core.surface.molecules molecule)
    (hCircuit : ObstructionCircuit law molecule) :
    core.surface.circuits hLaw hMolecule hCircuit :=
  core.circuitClosure hLaw hMolecule hCircuit

end AtomAxiomatizedPureAAT

/--
Atom-level zero curvature.

At the pure Atom-AAT level, zero curvature means that no required
law-relative obstruction circuit remains in the selected atom-molecule
boundary.
-/
def AtomZeroCurvature
    {C : Type u} {E : Type v} {D : Type w}
    (law : DesignLaw C E D)
    (requiredMolecule : AtomMolecule C E D -> Prop) : Prop :=
  NoRequiredObstructionCircuit law requiredMolecule

theorem atomZeroCurvature_iff_noRequiredObstructionCircuit
    {C : Type u} {E : Type v} {D : Type w}
    {law : DesignLaw C E D}
    {requiredMolecule : AtomMolecule C E D -> Prop} :
    AtomZeroCurvature law requiredMolecule ↔
      NoRequiredObstructionCircuit law requiredMolecule := by
  rfl

/--
Pure Atom-AAT zero-curvature theorem package.

This package is the atom-only theorem layer: it starts from a pure atom core,
a selected design law, selected required molecules, and a lawfulness bridge,
then derives atom-configuration lawfulness from atom-level zero curvature.
Signature-level zero-curvature packages can consume this result, but do not
define it.
-/
structure AtomZeroCurvatureTheoremPackage
    {C : Type u} {E : Type v} {D : Type w}
    (core : AtomAxiomatizedPureAAT C E D) where
  law : DesignLaw C E D
  requiredMolecule : AtomMolecule C E D -> Prop
  lawOnSurface : core.surface.laws law
  requiredMoleculesOnSurface :
    ∀ molecule, requiredMolecule molecule -> core.surface.molecules molecule
  requiredCircuitsOnSurface :
    ∀ {molecule},
      (hRequired : requiredMolecule molecule) ->
      (hCircuit : ObstructionCircuit law molecule) ->
        core.surface.circuits lawOnSurface
          (requiredMoleculesOnSurface molecule hRequired) hCircuit
  lawfulnessBridge : AtomLawfulnessBridge law requiredMolecule
  atomZeroCurvature : AtomZeroCurvature law requiredMolecule
  atomZeroCurvatureBoundary : Prop
  theoremPackageBoundary : Prop
  nonConclusions : Prop

namespace AtomZeroCurvatureTheoremPackage

/-- Atom zero curvature is the absence of required atom obstruction circuits. -/
theorem noRequiredObstructionCircuit
    {C : Type u} {E : Type v} {D : Type w}
    {core : AtomAxiomatizedPureAAT C E D}
    (pkg : AtomZeroCurvatureTheoremPackage core) :
    NoRequiredObstructionCircuit pkg.law pkg.requiredMolecule :=
  atomZeroCurvature_iff_noRequiredObstructionCircuit.mp
    pkg.atomZeroCurvature

/-- Pure atom zero curvature gives selected atom-configuration lawfulness. -/
theorem atomLawful
    {C : Type u} {E : Type v} {D : Type w}
    {core : AtomAxiomatizedPureAAT C E D}
    (pkg : AtomZeroCurvatureTheoremPackage core) :
    LawfulWithinAtomConfiguration pkg.law pkg.requiredMolecule := by
  exact
    (AtomLawfulnessBridge.lawful_iff_no_obstructionCircuit
      pkg.lawfulnessBridge).mpr
      pkg.noRequiredObstructionCircuit

/-- Required molecules selected by the zero-curvature package are on the pure surface. -/
theorem requiredMolecule_on_surface
    {C : Type u} {E : Type v} {D : Type w}
    {core : AtomAxiomatizedPureAAT C E D}
    (pkg : AtomZeroCurvatureTheoremPackage core)
    {molecule : AtomMolecule C E D}
    (hRequired : pkg.requiredMolecule molecule) :
    core.surface.molecules molecule :=
  pkg.requiredMoleculesOnSurface molecule hRequired

/--
Atoms occurring in required zero-curvature molecules are selected by the same
pure surface.
-/
theorem atom_of_requiredMolecule
    {C : Type u} {E : Type v} {D : Type w}
    {core : AtomAxiomatizedPureAAT C E D}
    (pkg : AtomZeroCurvatureTheoremPackage core)
    {molecule : AtomMolecule C E D}
    (hRequired : pkg.requiredMolecule molecule)
    {atom : ArchitectureAtom C E D}
    (hAtom : molecule.atoms atom) :
    core.surface.atoms atom :=
  core.surface.atom_of_selected_molecule
    (pkg.requiredMolecule_on_surface hRequired) hAtom

/-- Required zero-curvature molecules are supported by the pure surface atoms. -/
theorem requiredMolecule_supportedBy_surface_atoms
    {C : Type u} {E : Type v} {D : Type w}
    {core : AtomAxiomatizedPureAAT C E D}
    (pkg : AtomZeroCurvatureTheoremPackage core)
    {molecule : AtomMolecule C E D}
    (hRequired : pkg.requiredMolecule molecule) :
    AtomMoleculeSupportedBy core.surface.selectedAtomUniverse molecule :=
  core.surface.selected_molecule_supportedBy_selected_atoms
    (pkg.requiredMolecule_on_surface hRequired)

/-- Atoms in required zero-curvature molecules are primitive Atom Core facts. -/
theorem requiredMolecule_atom_is_primitive
    {C : Type u} {E : Type v} {D : Type w}
    {core : AtomAxiomatizedPureAAT C E D}
    (pkg : AtomZeroCurvatureTheoremPackage core)
    {molecule : AtomMolecule C E D}
    (hRequired : pkg.requiredMolecule molecule)
    {atom : ArchitectureAtom C E D}
    (hAtom : molecule.atoms atom) :
    PrimitiveArchitectureAtom atom :=
  AtomAxiomatizedPureAAT.selected_molecule_atom_is_primitive
    core (pkg.requiredMolecule_on_surface hRequired) hAtom

/-- Required atom obstruction circuits are selected by the pure atom surface. -/
theorem requiredCircuit_on_surface
    {C : Type u} {E : Type v} {D : Type w}
    {core : AtomAxiomatizedPureAAT C E D}
    (pkg : AtomZeroCurvatureTheoremPackage core)
    {molecule : AtomMolecule C E D}
    (hRequired : pkg.requiredMolecule molecule)
    (hCircuit : ObstructionCircuit pkg.law molecule) :
    core.surface.circuits pkg.lawOnSurface
      (pkg.requiredMoleculesOnSurface molecule hRequired) hCircuit :=
  pkg.requiredCircuitsOnSurface hRequired hCircuit

/-- The selected zero-curvature law does not create primitive atom existence. -/
theorem law_does_not_create_atoms
    {C : Type u} {E : Type v} {D : Type w}
    {core : AtomAxiomatizedPureAAT C E D}
    (pkg : AtomZeroCurvatureTheoremPackage core) :
    (core.lawSeparation pkg.law pkg.lawOnSurface).lawDoesNotCreateAtoms :=
  AtomAxiomatizedPureAAT.selected_law_does_not_create_atoms
    core pkg.lawOnSurface

/-- The selected zero-curvature law does not change primitive atom existence. -/
theorem law_does_not_change_atom_existence
    {C : Type u} {E : Type v} {D : Type w}
    {core : AtomAxiomatizedPureAAT C E D}
    (pkg : AtomZeroCurvatureTheoremPackage core) :
    (core.lawSeparation pkg.law pkg.lawOnSurface).lawDoesNotChangeAtomExistence :=
  AtomAxiomatizedPureAAT.selected_law_does_not_change_atom_existence
    core pkg.lawOnSurface

/-- The selected zero-curvature law evaluates atoms that already exist. -/
theorem law_atoms_exist_before_law
    {C : Type u} {E : Type v} {D : Type w}
    {core : AtomAxiomatizedPureAAT C E D}
    (pkg : AtomZeroCurvatureTheoremPackage core) :
    (core.lawSeparation pkg.law pkg.lawOnSurface).atomsExistBeforeLaw :=
  AtomAxiomatizedPureAAT.selected_law_atoms_exist_before_law
    core pkg.lawOnSurface

end AtomZeroCurvatureTheoremPackage

end Formal.Arch
