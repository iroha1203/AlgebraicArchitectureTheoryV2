import Formal.Arch.AAT.GeneratedOperation

namespace Formal.Arch
namespace AAT

universe u v

/-- Shape-level generated repair targets. -/
inductive GeneratedRepairTarget {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    (object : GeneratedArchitectureObject presentation) where
  | missingRequiredPort
      (carrier : GeneratedCarrier object)
      (port : AtomPort)
      (required :
        (AtomShapeOf presentation carrier.val).valence.requiredPort port)
  | incompatibleAtomPair
      (left right : GeneratedCarrier object)
      (distinct : left.val ≠ right.val)
      (incompatible :
        CompatibleComposition
          (AtomShapeOf presentation left.val)
          (AtomShapeOf presentation right.val) -> False)

namespace GeneratedRepairTarget

/-- Repair targets are port / slot / valence level targets, not free-form recommendations. -/
def shapeLevel {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    {object : GeneratedArchitectureObject presentation}
    (_target : GeneratedRepairTarget object) : Prop :=
  True

/-- Every generated repair target is shape-level by construction. -/
theorem is_shapeLevel {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    {object : GeneratedArchitectureObject presentation}
    (target : GeneratedRepairTarget object) :
    target.shapeLevel := by
  trivial

end GeneratedRepairTarget

/-- A target is cleared in the target object of a generated operation. -/
inductive GeneratedRepairTargetCleared {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    {source target : GeneratedArchitectureObject presentation}
    (operation : GeneratedOperation source target)
    : GeneratedRepairTarget source -> Type (max u v) where
  | missingRequiredPortCleared
      {carrier : GeneratedCarrier source}
      {port : AtomPort}
      {required :
        (AtomShapeOf presentation carrier.val).valence.requiredPort port}
      (other : system.Atom)
      (otherPort : AtomPort)
      (clears :
        target.molecule.atoms other ∧
        other ≠ (operation.atomMap carrier).val ∧
        (AtomShapeOf presentation other).valence.ports otherPort ∧
        PortCompatible port otherPort) :
      GeneratedRepairTargetCleared operation
        (.missingRequiredPort carrier port required)
  | incompatibleAtomPairCleared
      {left right : GeneratedCarrier source}
      {distinct : left.val ≠ right.val}
      {incompatible :
        CompatibleComposition
          (AtomShapeOf presentation left.val)
          (AtomShapeOf presentation right.val) -> False}
      (composition :
        CompatibleComposition
        (AtomShapeOf presentation (operation.atomMap left).val)
        (AtomShapeOf presentation (operation.atomMap right).val)) :
      GeneratedRepairTargetCleared operation
        (.incompatibleAtomPair left right distinct incompatible)

/--
Generated repair package.

The repair clears a selected shape-level target by applying a generated
operation. It does not introduce a free-form recommendation boundary.
-/
structure GeneratedRepair {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    (source target : GeneratedArchitectureObject presentation) where
  operation : GeneratedOperation source target
  repairTarget : GeneratedRepairTarget source
  clearsTarget : GeneratedRepairTargetCleared operation repairTarget
  repairBoundary : Prop

namespace GeneratedRepair

/-- Generated repairs clear their selected shape-level target. -/
def clears_selected_target
    {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    {source target : GeneratedArchitectureObject presentation}
    (repair : GeneratedRepair source target) :
    GeneratedRepairTargetCleared repair.operation repair.repairTarget :=
  repair.clearsTarget

/-- Generated repair targets are shape-level targets. -/
theorem target_shapeLevel
    {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    {source target : GeneratedArchitectureObject presentation}
    (repair : GeneratedRepair source target) :
    repair.repairTarget.shapeLevel :=
  repair.repairTarget.is_shapeLevel

/-- Generated repairs do not create atom existence. -/
theorem repair_does_not_create_atoms
    {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    {source target : GeneratedArchitectureObject presentation}
    (repair : GeneratedRepair source target) :
    system.noToolOutputCreatesAtoms :=
  repair.operation.operation_does_not_create_atoms

end GeneratedRepair

end AAT
end Formal.Arch
