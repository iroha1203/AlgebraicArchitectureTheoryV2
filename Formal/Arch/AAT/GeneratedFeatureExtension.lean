import Formal.Arch.AAT.GeneratedFlatness

namespace Formal.Arch
namespace AAT

universe u v

namespace GeneratedArchitectureObject

/--
Identity feature extension generated from a generated architecture object.

The static graph is the generated graph of the object, not a hand-authored
representation.
-/
def generatedIdentityFeatureExtension {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    (object : GeneratedArchitectureObject presentation) :
    FeatureExtension (GeneratedCarrier object) PEmpty.{u+1}
      (GeneratedCarrier object) (GeneratedCarrier object) :=
  identityFeatureExtension (GeneratedArchGraph object)

/--
Identity static split extension generated from a generated architecture object.

The selected static policy is the generated boundary policy, which is generated
from the same relation-atom surface as the generated graph.
-/
def generatedIdentityStaticSplitFeatureExtension
    {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    (object : GeneratedArchitectureObject presentation) :
    StaticSplitFeatureExtension (GeneratedCarrier object) PEmpty.{u+1}
      (GeneratedCarrier object) (GeneratedCarrier object) :=
  identityStaticSplitFeatureExtension
    (GeneratedArchGraph object)
    object.generatedBoundaryAllowed
    (by
      intro _src _dst hEdge
      exact hEdge)

/-- Generated identity split extensions satisfy selected static split. -/
theorem generated_selectedStaticSplitFeatureExtension
    {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    (object : GeneratedArchitectureObject presentation) :
    SelectedStaticSplitExtension
      object.generatedIdentityStaticSplitFeatureExtension.extension
      object.generatedIdentityStaticSplitFeatureExtension.declaredInterface
      object.generatedIdentityStaticSplitFeatureExtension.coreAllowedStaticEdge
      object.generatedIdentityStaticSplitFeatureExtension.extendedAllowedStaticEdge :=
  selectedStaticSplitExtension_of_staticSplitFeatureExtension
    object.generatedIdentityStaticSplitFeatureExtension

/-- Component universe for the generated identity feature extension. -/
def generatedIdentityExtensionComponentUniverse
    {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    (object : GeneratedArchitectureObject presentation) :
    ComponentUniverse
      object.generatedIdentityStaticSplitFeatureExtension.extension.extended where
  components := object.carrierList
  nodup := object.carrierListNodup
  covers := object.carrierListCovers
  edgeClosed := by
    intro source target _hEdge
    exact ⟨object.carrierListCovers source,
      object.carrierListCovers target⟩

/--
Generated identity feature extensions are covered by the generated component
universe.
-/
theorem generatedIdentityExtensionCoverageComplete
    {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    (object : GeneratedArchitectureObject presentation) :
    StaticSplitExtensionCoverageComplete
      object.generatedIdentityStaticSplitFeatureExtension
      object.generatedIdentityExtensionComponentUniverse := by
  exact
    ⟨(by
        intro carrier
        exact object.generatedIdentityExtensionComponentUniverse.covers carrier),
      (by
        intro feature
        cases feature),
      (by
        intro _source _target hEdge
        exact object.generatedIdentityExtensionComponentUniverse.edgeClosed hEdge),
      trivial⟩

/-- Flatness model induced by the generated identity feature extension. -/
def generatedIdentityExtensionFlatnessModel
    {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    (object : GeneratedArchitectureObject presentation) :
    ArchitectureFlatnessModel
      (GeneratedCarrier object)
      (GeneratedCarrier object)
      GeneratedObservationCoordinate
      (GeneratedSemanticExpr object)
      GeneratedObservationCoordinate :=
  LawfulExtensionFlatnessModel
    object.generatedIdentityStaticSplitFeatureExtension
    (GeneratedRuntimeGraph object)
    object.generatedProjection
    object.generatedAbstractGraph
    object.generatedObservation
    object.generatedBoundaryAllowed
    object.generatedAbstractionAllowed
    object.generatedRuntimeAllowed
    object.generatedSemanticSemantics
    (RequiredDiagramsByList object.generatedSemanticDiagrams)
    object.generatedSemanticDiagrams

/--
Runtime / semantic split preservation for the generated identity feature
extension follows from generated runtime and semantic surfaces.
-/
theorem generatedIdentityRuntimeSemanticSplitPreservation
    {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    (object : GeneratedArchitectureObject presentation) :
    RuntimeSemanticSplitPreservation
      object.generatedIdentityExtensionFlatnessModel
      object.generatedIdentityExtensionComponentUniverse := by
  exact
    ⟨(by
        intro _source _target hEdge _hSource _hTarget
        exact hEdge),
      (by
        intro diagram hMeasured
        exact object.generatedSemanticFlatWithin diagram hMeasured)⟩

end GeneratedArchitectureObject

namespace GeneratedArchitectureLawModel

/--
Generated law models induce bounded split feature extension packages.

This connects `FeatureExtension` / `SplitFeatureExtensionWithin` to generated
objects instead of leaving feature extension theorem packages as only
representation-level entrypoints.
-/
def generatedSplitFeatureExtensionWithin
    {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    {object : GeneratedArchitectureObject presentation}
    (model : GeneratedArchitectureLawModel object) :
    SplitFeatureExtensionWithin
      object.generatedIdentityStaticSplitFeatureExtension
      (GeneratedRuntimeGraph object)
      object.generatedProjection
      object.generatedAbstractGraph
      object.generatedObservation
      object.generatedBoundaryAllowed
      object.generatedAbstractionAllowed
      object.generatedRuntimeAllowed
      object.generatedSemanticSemantics
      (RequiredDiagramsByList object.generatedSemanticDiagrams)
      object.generatedSemanticDiagrams
      object.generatedIdentityExtensionComponentUniverse where
  extensionCoverage :=
    object.generatedIdentityExtensionCoverageComplete
  boundaryPolicyCompatible := by
    intro _source _target hAllowed
    exact hAllowed
  abstractionPolicyCompatible := by
    intro _source _target hAllowed
    exact hAllowed
  walkAcyclic := model.generatedWalkAcyclic
  projectionSound := by
    intro _source _target hEdge
    exact hEdge
  lspCompatible := by
    intro x y hSame
    cases hSame
    rfl
  runtimeCoverage := by
    intro source target _hEdge
    exact ⟨object.generatedIdentityExtensionComponentUniverse.covers source,
      object.generatedIdentityExtensionComponentUniverse.covers target⟩
  semanticCoverage := object.generatedSemanticCoverageComplete
  runtimeSemanticPreservation :=
    object.generatedIdentityRuntimeSemanticSplitPreservation
  recordsNonConclusions := trivial

/--
The existing split feature extension flatness theorem fires on generated
identity feature extensions.
-/
theorem generatedFeatureExtension_architectureFlatWithin
    {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    {object : GeneratedArchitectureObject presentation}
    (model : GeneratedArchitectureLawModel object) :
    ArchitectureFlatWithin
      object.generatedIdentityExtensionFlatnessModel
      object.generatedIdentityExtensionComponentUniverse :=
  architectureFlatWithin_of_splitFeatureExtensionWithin
    model.generatedSplitFeatureExtensionWithin

/-- Generated split feature extension packages record their non-conclusions. -/
theorem generatedSplitFeatureExtension_recordsNonConclusions
    {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    {object : GeneratedArchitectureObject presentation}
    (model : GeneratedArchitectureLawModel object) :
    SplitFeatureExtensionWithinNonConclusions
      object.generatedIdentityStaticSplitFeatureExtension
      object.generatedIdentityExtensionComponentUniverse :=
  splitFeatureExtensionWithin_recordsNonConclusions
    model.generatedSplitFeatureExtensionWithin

end GeneratedArchitectureLawModel

end AAT
end Formal.Arch
