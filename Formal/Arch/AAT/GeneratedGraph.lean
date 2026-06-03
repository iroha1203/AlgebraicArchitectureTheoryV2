import Formal.Arch.AAT.GeneratedObject
import Formal.Arch.Core.Graph

namespace Formal.Arch
namespace AAT

universe u v

/--
A relation atom generates an oriented edge when it is selected by the generated
object and composes with the source through `relationSource` ports and with the
target through `relationTarget` ports.
-/
structure GeneratedRelationAtom {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    (object : GeneratedArchitectureObject presentation)
    (relation source target : GeneratedCarrier object) : Prop where
  relationFamily :
    (AtomShapeOf presentation relation.val).family = AtomKind.relation
  relationSourceDistinct : relation.val ≠ source.val
  relationTargetDistinct : relation.val ≠ target.val
  endpointsDistinct : source.val ≠ target.val
  sourceCompositionUsesRelationSource :
    let composition :=
      object.molecule.compatible_pairs
        relation.property source.property relationSourceDistinct
    composition.leftPort.kind = AtomPortKind.relationSource ∧
      composition.rightPort.kind = AtomPortKind.relationSource
  targetCompositionUsesRelationTarget :
    let composition :=
      object.molecule.compatible_pairs
        relation.property target.property relationTargetDistinct
    composition.leftPort.kind = AtomPortKind.relationTarget ∧
      composition.rightPort.kind = AtomPortKind.relationTarget

/-- Generated graph relation induced by selected relation atoms. -/
def GeneratedRelation {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    (object : GeneratedArchitectureObject presentation)
    (source target : GeneratedCarrier object) : Prop :=
  ∃ relation : GeneratedCarrier object,
    GeneratedRelationAtom object relation source target

/-- The dependency graph projected from a generated architecture object. -/
def GeneratedArchGraph {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    (object : GeneratedArchitectureObject presentation) :
    ArchGraph (GeneratedCarrier object) where
  edge := GeneratedRelation object

/--
A runtime-interaction atom generates an oriented runtime edge when it composes
with the source through `runtimeSource` ports and with the target through
`runtimeTarget` ports.
-/
structure GeneratedRuntimeRelationAtom {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    (object : GeneratedArchitectureObject presentation)
    (interaction source target : GeneratedCarrier object) : Prop where
  interactionFamily :
    (AtomShapeOf presentation interaction.val).family =
      AtomKind.runtimeInteraction
  interactionSourceDistinct : interaction.val ≠ source.val
  interactionTargetDistinct : interaction.val ≠ target.val
  endpointsDistinct : source.val ≠ target.val
  sourceCompositionUsesRuntimeSource :
    let composition :=
      object.molecule.compatible_pairs
        interaction.property source.property interactionSourceDistinct
    composition.leftPort.kind = AtomPortKind.runtimeSource ∧
      composition.rightPort.kind = AtomPortKind.runtimeSource
  targetCompositionUsesRuntimeTarget :
    let composition :=
      object.molecule.compatible_pairs
        interaction.property target.property interactionTargetDistinct
    composition.leftPort.kind = AtomPortKind.runtimeTarget ∧
      composition.rightPort.kind = AtomPortKind.runtimeTarget

/-- Runtime relation induced by selected runtime-interaction atoms. -/
def GeneratedRuntimeRelation {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    (object : GeneratedArchitectureObject presentation)
    (source target : GeneratedCarrier object) : Prop :=
  ∃ interaction : GeneratedCarrier object,
    GeneratedRuntimeRelationAtom object interaction source target

/-- Runtime graph projected from runtime-interaction atoms in a generated object. -/
def GeneratedRuntimeGraph {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    (object : GeneratedArchitectureObject presentation) :
    RuntimeDependencyGraph (GeneratedCarrier object) where
  edge := GeneratedRuntimeRelation object

namespace GeneratedArchitectureObject

/-- Runtime policy generated from the runtime-interaction surface. -/
def generatedRuntimeAllowed {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    (object : GeneratedArchitectureObject presentation)
    (source target : GeneratedCarrier object) : Prop :=
  GeneratedRuntimeRelation object source target

end GeneratedArchitectureObject

/- Edge materialization witness for generated relation atoms. -/
structure GeneratedRelationEdgeWitness {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    (object : GeneratedArchitectureObject presentation)
    (source target : GeneratedCarrier object) where
  relation : GeneratedCarrier object
  relationAtom : GeneratedRelationAtom object relation source target
  relationSourceComposition :
    CompatibleComposition
      (AtomShapeOf presentation relation.val)
      (AtomShapeOf presentation source.val)
  relationTargetComposition :
    CompatibleComposition
      (AtomShapeOf presentation relation.val)
      (AtomShapeOf presentation target.val)

/- Edge materialization witness for generated runtime-interaction atoms. -/
structure GeneratedRuntimeEdgeWitness {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    (object : GeneratedArchitectureObject presentation)
    (source target : GeneratedCarrier object) where
  interaction : GeneratedCarrier object
  interactionAtom : GeneratedRuntimeRelationAtom object interaction source target
  interactionSourceComposition :
    CompatibleComposition
      (AtomShapeOf presentation interaction.val)
      (AtomShapeOf presentation source.val)
  interactionTargetComposition :
    CompatibleComposition
      (AtomShapeOf presentation interaction.val)
      (AtomShapeOf presentation target.val)

namespace GeneratedArchGraph

/--
Generated relation atom witnesses inherit compatible composition with both
endpoints from the generated molecule.
-/
def generated_relation_atom_witness
    {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    (object : GeneratedArchitectureObject presentation)
    {relation source target : GeneratedCarrier object}
    (hRelation : GeneratedRelationAtom object relation source target) :
    GeneratedRelationEdgeWitness object source target where
  relation := relation
  relationAtom := hRelation
  relationSourceComposition :=
    object.molecule.compatible_pairs
      relation.property source.property
      hRelation.relationSourceDistinct
  relationTargetComposition :=
    object.molecule.compatible_pairs
      relation.property target.property
      hRelation.relationTargetDistinct

/-- Generated graph edges are exactly backed by selected relation atoms. -/
theorem generated_graph_edges_from_relation_atoms
    {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    (object : GeneratedArchitectureObject presentation)
    {source target : GeneratedCarrier object}
    (hEdge : (GeneratedArchGraph object).edge source target) :
    ∃ relation : GeneratedCarrier object,
      GeneratedRelationAtom object relation source target :=
  hEdge

/-- Generated graph edges require two distinct selected endpoint atoms. -/
theorem generated_graph_edge_requires_distinct_endpoints
    {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    (object : GeneratedArchitectureObject presentation)
    {source target : GeneratedCarrier object}
    (hEdge : (GeneratedArchGraph object).edge source target) :
    source.val ≠ target.val := by
  rcases hEdge with ⟨_relation, hRelation⟩
  exact hRelation.endpointsDistinct

end GeneratedArchGraph

namespace GeneratedRuntimeGraph

/--
Generated runtime-interaction atom witnesses inherit compatible composition
with both endpoints from the generated molecule.
-/
def generated_runtime_atom_witness
    {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    (object : GeneratedArchitectureObject presentation)
    {interaction source target : GeneratedCarrier object}
    (hInteraction :
      GeneratedRuntimeRelationAtom object interaction source target) :
    GeneratedRuntimeEdgeWitness object source target where
  interaction := interaction
  interactionAtom := hInteraction
  interactionSourceComposition :=
    object.molecule.compatible_pairs
      interaction.property source.property
      hInteraction.interactionSourceDistinct
  interactionTargetComposition :=
    object.molecule.compatible_pairs
      interaction.property target.property
      hInteraction.interactionTargetDistinct

/-- Generated runtime graph edges are exactly backed by runtime-interaction atoms. -/
theorem generated_runtime_edges_from_interaction_atoms
    {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    (object : GeneratedArchitectureObject presentation)
    {source target : GeneratedCarrier object}
    (hEdge : (GeneratedRuntimeGraph object).edge source target) :
    ∃ interaction : GeneratedCarrier object,
      GeneratedRuntimeRelationAtom object interaction source target :=
  hEdge

/-- Generated runtime graph edges require two distinct selected endpoint atoms. -/
theorem generated_runtime_edge_requires_distinct_endpoints
    {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    (object : GeneratedArchitectureObject presentation)
    {source target : GeneratedCarrier object}
    (hEdge : (GeneratedRuntimeGraph object).edge source target) :
    source.val ≠ target.val := by
  rcases hEdge with ⟨_interaction, hInteraction⟩
  exact hInteraction.endpointsDistinct

end GeneratedRuntimeGraph

end AAT
end Formal.Arch
