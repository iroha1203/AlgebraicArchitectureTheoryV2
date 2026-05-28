import Formal.Arch.AAT.ZeroCurvature

namespace Formal.Arch
namespace AAT

universe u v

/--
Operation preservation over Atom-generated AAT cores.

The package records preservation between selected source and target cores.  It
does not define atoms, observe atoms, or create atom existence.
-/
structure OperationPreservationPackage {system : AtomAxiomSystem.{u, v}}
    (source target : AATCore system) where
  selectedMolecule : Molecule system -> Prop
  selectedLaw : DesignLaw system -> Prop
  preservesMolecule :
    ∀ molecule,
      selectedMolecule molecule ->
      source.molecules molecule ->
        target.molecules molecule
  preservesLaw :
    ∀ law,
      selectedLaw law ->
      source.laws law ->
        target.laws law
  operationDoesNotCreateAtomsEvidence :
    system.noToolOutputCreatesAtoms
  operationBoundary : Prop
  theoremPackageBoundary : Prop
  nonConclusions : Prop

namespace OperationPreservationPackage

/-- A selected molecule preserved by the operation is selected in the target core. -/
theorem target_molecule {system : AtomAxiomSystem.{u, v}}
    {source target : AATCore system}
    (pkg : OperationPreservationPackage source target)
    {molecule : Molecule system}
    (hSelected : pkg.selectedMolecule molecule)
    (hSource : source.molecules molecule) :
    target.molecules molecule :=
  pkg.preservesMolecule molecule hSelected hSource

/-- A selected law preserved by the operation is selected in the target core. -/
theorem target_law {system : AtomAxiomSystem.{u, v}}
    {source target : AATCore system}
    (pkg : OperationPreservationPackage source target)
    {law : DesignLaw system}
    (hSelected : pkg.selectedLaw law)
    (hSource : source.laws law) :
    target.laws law :=
  pkg.preservesLaw law hSelected hSource

/-- Pure AAT operation packages do not create atom existence. -/
theorem operation_does_not_create_atoms
    {system : AtomAxiomSystem.{u, v}}
    {source target : AATCore system}
    (pkg : OperationPreservationPackage source target) :
    system.noToolOutputCreatesAtoms :=
  pkg.operationDoesNotCreateAtomsEvidence

end OperationPreservationPackage

end AAT
end Formal.Arch
