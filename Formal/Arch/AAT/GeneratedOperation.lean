import Formal.Arch.AAT.GeneratedDistance
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
the AtomShape transformation it performs. Atom non-creation is derived from the
root `AtomAxiomSystem`, not supplied as an operation-specific field.
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
  operationBoundary : Prop

namespace GeneratedOperation

/-- AtomShape-coordinate distance between a source carrier and its mapped target carrier. -/
def mappedCarrierShapeDistance
    {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    {source target : GeneratedArchitectureObject presentation}
    (operation : GeneratedOperation source target)
    (carrier : GeneratedCarrier source) : Nat :=
  GeneratedAtomShapeCoordinate.mismatchCount
    (GeneratedAtomShapeCoordinate.ofShape
      (AtomShapeOf presentation carrier.val))
    (GeneratedAtomShapeCoordinate.ofShape
      (AtomShapeOf presentation (operation.atomMap carrier).val))

/--
Target carriers outside the source atom map are still target generated carriers,
not atoms created by the operation.
-/
def TargetCarrierUnmapped
    {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    {source target : GeneratedArchitectureObject presentation}
    (operation : GeneratedOperation source target)
    (targetCarrier : GeneratedCarrier target) : Prop :=
  ∀ sourceCarrier : GeneratedCarrier source,
    operation.atomMap sourceCarrier ≠ targetCarrier

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

/-- Operation mapped distance unfolds to generated AtomShape coordinate mismatch count. -/
theorem mappedCarrierShapeDistance_eq_coordinate_mismatchCount
    {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    {source target : GeneratedArchitectureObject presentation}
    (operation : GeneratedOperation source target)
    (carrier : GeneratedCarrier source) :
    operation.mappedCarrierShapeDistance carrier =
      GeneratedAtomShapeCoordinate.mismatchCount
        (GeneratedAtomShapeCoordinate.ofShape
          (AtomShapeOf presentation carrier.val))
        (GeneratedAtomShapeCoordinate.ofShape
          (AtomShapeOf presentation (operation.atomMap carrier).val)) := by
  rfl

/-- Zero mapped distance is exactly equality of source and mapped target coordinates. -/
theorem mappedCarrierShapeDistance_eq_zero_iff_coordinate_eq
    {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    {source target : GeneratedArchitectureObject presentation}
    (operation : GeneratedOperation source target)
    (carrier : GeneratedCarrier source) :
    operation.mappedCarrierShapeDistance carrier = 0 ↔
      GeneratedAtomShapeCoordinate.ofShape
          (AtomShapeOf presentation carrier.val) =
        GeneratedAtomShapeCoordinate.ofShape
          (AtomShapeOf presentation (operation.atomMap carrier).val) := by
  exact GeneratedAtomShapeCoordinate.mismatchCount_eq_zero_iff

/-- Operation targets remain primitive atoms in the same root system. -/
theorem target_atom_primitive
    {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    {source target : GeneratedArchitectureObject presentation}
    (operation : GeneratedOperation source target)
    (carrier : GeneratedCarrier source) :
    system.Primitive (operation.atomMap carrier).val :=
  target.carrier_atom_primitive (operation.atomMap carrier)

/-- Unmapped target carriers remain primitive atoms in the same root system. -/
theorem unmapped_target_atom_primitive
    {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    {source target : GeneratedArchitectureObject presentation}
    (operation : GeneratedOperation source target)
    (targetCarrier : GeneratedCarrier target)
    (_hUnmapped : operation.TargetCarrierUnmapped targetCarrier) :
    system.Primitive targetCarrier.val :=
  target.carrier_atom_primitive targetCarrier

/-- Generated operations do not create atom existence. -/
theorem operation_does_not_create_atoms
    {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    {source target : GeneratedArchitectureObject presentation}
    (_operation : GeneratedOperation source target) :
    system.noToolOutputCreatesAtoms :=
  system.tool_output_does_not_create_atoms

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
