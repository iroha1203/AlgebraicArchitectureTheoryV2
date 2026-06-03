import Formal.Arch.AAT.GeneratedOperation
import Formal.Arch.AAT.Repair

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

/--
Generated repairs induce the existing pure AAT repair-clearing package at the
generated target object.
-/
def toRepairClearingPackage
    {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    {source target : GeneratedArchitectureObject presentation}
    (repair : GeneratedRepair source target)
    (targetModel : GeneratedArchitectureLawModel target) :
    RepairClearingPackage
      targetModel.generatedAATCore
      (GeneratedArchitectureObject presentation)
      Unit
      source
      target where
  law := targetModel.generatedDesignLaw
  requiredMolecule := targetModel.requiredGeneratedMolecule
  lawOnCore := targetModel.generated_law_on_core
  requiredMoleculesOnCore := by
    intro molecule hRequired
    exact hRequired
  requiredCircuitsOnCore := by
    intro _molecule _hRequired _hCircuit
    trivial
  lawfulnessBridge := targetModel.generatedLawfulnessBridge
  targetNoRequiredObstructionCircuit :=
    targetModel.generated_noRequiredObstructionCircuit
  repairDoesNotCreateAtomsEvidence :=
    repair.repair_does_not_create_atoms
  repairBoundary := repair.repairBoundary
  exactnessBoundary := targetModel.lawModelBoundary
  nonConclusions := True

end GeneratedRepair

/--
Finite selected atom configuration before it is known to satisfy the generated
molecule compatibility conditions.

This is the repair/synthesis boundary required by the atom reconstruction plan:
a broken atom configuration is not promoted to `GeneratedMolecule`; instead its
shape-level failure is repaired into a generated target object.
-/
structure GeneratedRepairProblemConfiguration {system : AtomAxiomSystem.{u, v}}
    (presentation : AtomShapePresentation system) where
  atoms : system.Atom -> Prop
  finiteConfiguration : Prop
  atomsPrimitive :
    ∀ atom, atoms atom -> system.Primitive atom
  problemBoundary : Prop

/-- Carrier of a pre-molecule repair problem configuration. -/
abbrev GeneratedRepairProblemCarrier {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    (configuration : GeneratedRepairProblemConfiguration presentation) :=
  { atom : system.Atom // configuration.atoms atom }

namespace GeneratedRepairProblemConfiguration

/-- A repair problem configuration can be forgotten to the legacy molecule shape only. -/
def toMolecule {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    (configuration : GeneratedRepairProblemConfiguration presentation) :
    Molecule system where
  atoms := configuration.atoms
  finiteConfiguration := configuration.finiteConfiguration
  nonConclusions := True

/-- Problem configurations still contain only primitive root atoms. -/
theorem atoms_primitive {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    (configuration : GeneratedRepairProblemConfiguration presentation)
    {atom : system.Atom}
    (hAtom : configuration.atoms atom) :
    system.Primitive atom :=
  configuration.atomsPrimitive atom hAtom

end GeneratedRepairProblemConfiguration

/--
Shape-level failure that prevents a selected atom configuration from being a
generated molecule.
-/
inductive GeneratedRepairProblem {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    (configuration : GeneratedRepairProblemConfiguration presentation)
    : Type (max u v) where
  | missingRequiredPort
      (atom : GeneratedRepairProblemCarrier configuration)
      (port : AtomPort)
      (required :
        (AtomShapeOf presentation atom.val).valence.requiredPort port)
      (missing :
        ¬ ∃ other otherPort,
          configuration.atoms other ∧
          other ≠ atom.val ∧
          (AtomShapeOf presentation other).valence.ports otherPort ∧
          PortCompatible port otherPort)
  | incompatibleAtomPair
      (left right : GeneratedRepairProblemCarrier configuration)
      (distinct : left.val ≠ right.val)
      (incompatible :
        CompatibleComposition
          (AtomShapeOf presentation left.val)
          (AtomShapeOf presentation right.val) -> False)

namespace GeneratedRepairProblem

/-- Generated repair problems are defined at port / slot / valence level. -/
def shapeLevel {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    {configuration : GeneratedRepairProblemConfiguration presentation}
    (_problem : GeneratedRepairProblem configuration) : Prop :=
  True

/-- Every generated repair problem is shape-level by construction. -/
theorem is_shapeLevel {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    {configuration : GeneratedRepairProblemConfiguration presentation}
    (problem : GeneratedRepairProblem configuration) :
    problem.shapeLevel := by
  trivial

end GeneratedRepairProblem

/--
Generated operation from a pre-molecule repair problem configuration into a
valid generated target object.
-/
structure GeneratedRepairProblemOperation {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    (configuration : GeneratedRepairProblemConfiguration presentation)
    (target : GeneratedArchitectureObject presentation) where
  atomMap : GeneratedRepairProblemCarrier configuration -> GeneratedCarrier target
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

namespace GeneratedRepairProblemOperation

/-- Problem repair operations expose their AtomShape transformation. -/
theorem atomShape_transformed
    {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    {configuration : GeneratedRepairProblemConfiguration presentation}
    {target : GeneratedArchitectureObject presentation}
    (operation : GeneratedRepairProblemOperation configuration target)
    (carrier : GeneratedRepairProblemCarrier configuration) :
    operation.shapeTransform
      (AtomShapeOf presentation carrier.val)
      (AtomShapeOf presentation (operation.atomMap carrier).val) :=
  operation.transformsAtomShape carrier

/-- Problem repair operations map selected source atoms to primitive target atoms. -/
theorem target_atom_primitive
    {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    {configuration : GeneratedRepairProblemConfiguration presentation}
    {target : GeneratedArchitectureObject presentation}
    (operation : GeneratedRepairProblemOperation configuration target)
    (carrier : GeneratedRepairProblemCarrier configuration) :
    system.Primitive (operation.atomMap carrier).val :=
  operation.preservesPrimitive carrier

/-- Problem repair operations do not create atom existence. -/
theorem operation_does_not_create_atoms
    {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    {configuration : GeneratedRepairProblemConfiguration presentation}
    {target : GeneratedArchitectureObject presentation}
    (operation : GeneratedRepairProblemOperation configuration target) :
    system.noToolOutputCreatesAtoms :=
  operation.operationDoesNotCreateAtomsEvidence

end GeneratedRepairProblemOperation

/-- A selected repair problem is cleared by the generated target object. -/
inductive GeneratedRepairProblemCleared {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    {configuration : GeneratedRepairProblemConfiguration presentation}
    {target : GeneratedArchitectureObject presentation}
    (operation : GeneratedRepairProblemOperation configuration target)
    : GeneratedRepairProblem configuration -> Type (max u v) where
  | missingRequiredPortCleared
      {atom : GeneratedRepairProblemCarrier configuration}
      {port : AtomPort}
      {required :
        (AtomShapeOf presentation atom.val).valence.requiredPort port}
      {missing :
        ¬ ∃ other otherPort,
          configuration.atoms other ∧
          other ≠ atom.val ∧
          (AtomShapeOf presentation other).valence.ports otherPort ∧
          PortCompatible port otherPort}
      (other : system.Atom)
      (otherPort : AtomPort)
      (clears :
        target.molecule.atoms other ∧
        other ≠ (operation.atomMap atom).val ∧
        (AtomShapeOf presentation other).valence.ports otherPort ∧
        PortCompatible port otherPort) :
      GeneratedRepairProblemCleared operation
        (.missingRequiredPort atom port required missing)
  | incompatibleAtomPairCleared
      {left right : GeneratedRepairProblemCarrier configuration}
      {distinct : left.val ≠ right.val}
      {incompatible :
        CompatibleComposition
          (AtomShapeOf presentation left.val)
          (AtomShapeOf presentation right.val) -> False}
      (composition :
        CompatibleComposition
          (AtomShapeOf presentation (operation.atomMap left).val)
          (AtomShapeOf presentation (operation.atomMap right).val)) :
      GeneratedRepairProblemCleared operation
        (.incompatibleAtomPair left right distinct incompatible)

/--
Generated repair from a failed atom configuration to a valid generated object.

The source is not assumed to be a `GeneratedMolecule`; the target is.
-/
structure GeneratedRepairFromProblem {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    (configuration : GeneratedRepairProblemConfiguration presentation)
    (target : GeneratedArchitectureObject presentation) where
  operation : GeneratedRepairProblemOperation configuration target
  repairProblem : GeneratedRepairProblem configuration
  clearsProblem : GeneratedRepairProblemCleared operation repairProblem
  repairBoundary : Prop

namespace GeneratedRepairFromProblem

/-- The selected problem is cleared by the generated target object. -/
def clears_selected_problem
    {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    {configuration : GeneratedRepairProblemConfiguration presentation}
    {target : GeneratedArchitectureObject presentation}
    (repair : GeneratedRepairFromProblem configuration target) :
    GeneratedRepairProblemCleared repair.operation repair.repairProblem :=
  repair.clearsProblem

/-- The repair target is a valid generated molecule. -/
def target_generated_molecule
    {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    {configuration : GeneratedRepairProblemConfiguration presentation}
    {target : GeneratedArchitectureObject presentation}
    (_repair : GeneratedRepairFromProblem configuration target) :
    GeneratedMolecule presentation :=
  target.molecule

/-- Problem repairs operate on shape-level repair problems. -/
theorem problem_shapeLevel
    {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    {configuration : GeneratedRepairProblemConfiguration presentation}
    {target : GeneratedArchitectureObject presentation}
    (repair : GeneratedRepairFromProblem configuration target) :
    repair.repairProblem.shapeLevel :=
  repair.repairProblem.is_shapeLevel

/-- Problem repairs do not create atom existence. -/
theorem repair_problem_does_not_create_atoms
    {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    {configuration : GeneratedRepairProblemConfiguration presentation}
    {target : GeneratedArchitectureObject presentation}
    (repair : GeneratedRepairFromProblem configuration target) :
    system.noToolOutputCreatesAtoms :=
  repair.operation.operation_does_not_create_atoms

/--
Generated repair from a failed pre-molecule configuration induces the existing
pure AAT repair-clearing package at the generated target object.
-/
def toRepairClearingPackage
    {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    {configuration : GeneratedRepairProblemConfiguration presentation}
    {target : GeneratedArchitectureObject presentation}
    (repair : GeneratedRepairFromProblem configuration target)
    (targetModel : GeneratedArchitectureLawModel target) :
    RepairClearingPackage
      targetModel.generatedAATCore
      (Sum
        (GeneratedRepairProblemConfiguration presentation)
        (GeneratedArchitectureObject presentation))
      Unit
      (Sum.inl configuration)
      (Sum.inr target) where
  law := targetModel.generatedDesignLaw
  requiredMolecule := targetModel.requiredGeneratedMolecule
  lawOnCore := targetModel.generated_law_on_core
  requiredMoleculesOnCore := by
    intro molecule hRequired
    exact hRequired
  requiredCircuitsOnCore := by
    intro _molecule _hRequired _hCircuit
    trivial
  lawfulnessBridge := targetModel.generatedLawfulnessBridge
  targetNoRequiredObstructionCircuit :=
    targetModel.generated_noRequiredObstructionCircuit
  repairDoesNotCreateAtomsEvidence :=
    repair.repair_problem_does_not_create_atoms
  repairBoundary := repair.repairBoundary
  exactnessBoundary := targetModel.lawModelBoundary
  nonConclusions := True

end GeneratedRepairFromProblem

end AAT
end Formal.Arch
