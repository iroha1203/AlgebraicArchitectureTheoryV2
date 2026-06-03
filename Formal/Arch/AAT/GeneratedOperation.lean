import Formal.Arch.AAT.GeneratedFlatness
import Formal.Arch.AAT.Operation

namespace Formal.Arch
namespace AAT

universe u v

/-- Shape transformation relation used by generated operations. -/
abbrev AtomShapeTransform := AtomShape -> AtomShape -> Prop

/--
Generated operation between generated architecture objects.

The operation maps selected source atoms to selected target atoms and records
the AtomShape transformation it performs. It does not create atom existence.
-/
structure GeneratedOperation {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    (source target : GeneratedArchitectureObject presentation) where
  atomMap : GeneratedCarrier source -> GeneratedCarrier target
  shapeTransform : AtomShapeTransform
  transformsAtomShape :
    ∀ carrier,
      shapeTransform
        (AtomShapeOf presentation carrier.val)
        (AtomShapeOf presentation (atomMap carrier).val)
  preservesPrimitive :
    ∀ carrier, system.Primitive (atomMap carrier).val
  operationDoesNotCreateAtomsEvidence :
    system.noToolOutputCreatesAtoms
  operationBoundary : Prop

namespace GeneratedOperation

/-- Generated operations expose their AtomShape transformation on each mapped atom. -/
theorem atomShape_transformed
    {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    {source target : GeneratedArchitectureObject presentation}
    (operation : GeneratedOperation source target)
    (carrier : GeneratedCarrier source) :
    operation.shapeTransform
      (AtomShapeOf presentation carrier.val)
      (AtomShapeOf presentation (operation.atomMap carrier).val) :=
  operation.transformsAtomShape carrier

/-- Operation targets remain primitive atoms in the same root system. -/
theorem target_atom_primitive
    {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    {source target : GeneratedArchitectureObject presentation}
    (operation : GeneratedOperation source target)
    (carrier : GeneratedCarrier source) :
    system.Primitive (operation.atomMap carrier).val :=
  operation.preservesPrimitive carrier

/-- Generated operations do not create atom existence. -/
theorem operation_does_not_create_atoms
    {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    {source target : GeneratedArchitectureObject presentation}
    (operation : GeneratedOperation source target) :
    system.noToolOutputCreatesAtoms :=
  operation.operationDoesNotCreateAtomsEvidence

/--
Generated operations induce pure AAT operation transport between the generated
AAT cores of their source and target law models.
-/
def toOperationTransportPackage
    {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    {source target : GeneratedArchitectureObject presentation}
    (operation : GeneratedOperation source target)
    (sourceModel : GeneratedArchitectureLawModel source)
    (targetModel : GeneratedArchitectureLawModel target) :
    OperationTransportPackage
      sourceModel.generatedAATCore
      targetModel.generatedAATCore where
  selectedSourceMolecule := sourceModel.requiredGeneratedMolecule
  selectedTargetMolecule := targetModel.requiredGeneratedMolecule
  selectedSourceLaw := fun law => law = sourceModel.generatedDesignLaw
  selectedTargetLaw := fun law => law = targetModel.generatedDesignLaw
  transportsMolecule := by
    intro _molecule _hSelected _hSource
    exact ⟨target.molecule.toMolecule, rfl, rfl⟩
  transportsLaw := by
    intro _law _hSelected _hSource
    exact ⟨targetModel.generatedDesignLaw, rfl, targetModel.generated_law_on_core⟩
  operationDoesNotCreateAtomsEvidence :=
    operation.operation_does_not_create_atoms
  operationBoundary := operation.operationBoundary
  theoremPackageBoundary := operation.operationBoundary
  nonConclusions := True

end GeneratedOperation

end AAT
end Formal.Arch
