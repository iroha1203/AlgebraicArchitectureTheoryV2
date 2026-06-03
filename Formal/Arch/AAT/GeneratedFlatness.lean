import Formal.Arch.AAT.GeneratedLawModel
import Formal.Arch.Extension.Flatness

namespace Formal.Arch
namespace AAT

universe u v

namespace GeneratedArchitectureObject

/-- Semantic expression family generated from object carriers. -/
abbrev GeneratedSemanticExpr {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    (object : GeneratedArchitectureObject presentation) :=
  GeneratedCarrier object

/-- Generated semantic semantics read the same shape coordinate as observations. -/
def generatedSemanticSemantics {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    (object : GeneratedArchitectureObject presentation) :
    Semantics (GeneratedSemanticExpr object)
      GeneratedObservationCoordinate where
  eval := fun carrier => object.generatedObservation.observe carrier

/-- Reflexive semantic diagram generated for a selected carrier. -/
def generatedSemanticDiagram {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    (object : GeneratedArchitectureObject presentation)
    (carrier : GeneratedCarrier object) :
    RequiredDiagram (GeneratedSemanticExpr object) where
  lhs := carrier
  rhs := carrier

/-- Finite semantic diagram family generated from the selected carrier list. -/
def generatedSemanticDiagrams {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    (object : GeneratedArchitectureObject presentation) :
    List (RequiredDiagram (GeneratedSemanticExpr object)) :=
  object.carrierList.map (fun carrier =>
    object.generatedSemanticDiagram carrier)

/-- Generated semantic diagrams cover exactly the finite required list they define. -/
theorem generatedSemanticCoverageComplete
    {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    (object : GeneratedArchitectureObject presentation) :
    CoversRequired
      (RequiredDiagramsByList object.generatedSemanticDiagrams)
      object.generatedSemanticDiagrams :=
  coversRequired_requiredDiagramsByList_self object.generatedSemanticDiagrams

/-- Generated reflexive semantic diagrams commute by construction. -/
theorem generatedSemanticFlatWithin
    {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    (object : GeneratedArchitectureObject presentation) :
    DiagramLawfulByList object.generatedSemanticSemantics
      object.generatedSemanticDiagrams := by
  intro diagram hMeasured
  rcases List.mem_map.mp hMeasured with ⟨carrier, _hCarrier, hEq⟩
  cases hEq
  rfl

/-- Flatness model constructed from generated static, runtime, and semantic surfaces. -/
def generatedFlatnessModel {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    (object : GeneratedArchitectureObject presentation) :
    ArchitectureFlatnessModel
      (GeneratedCarrier object)
      (GeneratedCarrier object)
      GeneratedObservationCoordinate
      (GeneratedSemanticExpr object)
      GeneratedObservationCoordinate where
  static := GeneratedArchGraph object
  runtime := GeneratedRuntimeGraph object
  projection := object.generatedProjection
  abstractStatic := object.generatedAbstractGraph
  staticObservation := object.generatedObservation
  boundaryAllowed := object.generatedBoundaryAllowed
  abstractionAllowed := object.generatedAbstractionAllowed
  runtimeAllowed := object.generatedRuntimeAllowed
  semantic := object.generatedSemanticSemantics
  requiredSemantic := RequiredDiagramsByList object.generatedSemanticDiagrams
  measuredSemantic := object.generatedSemanticDiagrams

end GeneratedArchitectureObject

namespace GeneratedArchitectureLawModel

/-- Static flatness follows from the generated Signature law model. -/
theorem generated_staticFlatWithin
    {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    {object : GeneratedArchitectureObject presentation}
    (model : GeneratedArchitectureLawModel object) :
    StaticFlatWithin object.generatedFlatnessModel
      object.generatedComponentUniverse := by
  exact model.generatedArchitectureLawful

/-- Runtime coverage follows from the generated object's carrier universe. -/
theorem generated_runtimeCoverageComplete
    {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    {object : GeneratedArchitectureObject presentation}
    (_model : GeneratedArchitectureLawModel object) :
    RuntimeCoverageComplete object.generatedFlatnessModel
      object.generatedComponentUniverse := by
  intro source target _hEdge
  exact ⟨object.carrierListCovers source,
    object.carrierListCovers target⟩

/-- Generated runtime flatness follows because runtime policy is generated from runtime edges. -/
theorem generated_runtimeFlatWithin
    {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    {object : GeneratedArchitectureObject presentation}
    (_model : GeneratedArchitectureLawModel object) :
    RuntimeFlatWithin object.generatedFlatnessModel
      object.generatedComponentUniverse := by
  intro _source _target _hSource _hTarget hEdge
  exact hEdge

/-- Generated semantic flatness follows from the generated reflexive diagram family. -/
theorem generated_semanticFlatWithin
    {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    {object : GeneratedArchitectureObject presentation}
    (_model : GeneratedArchitectureLawModel object) :
    SemanticFlatWithin object.generatedFlatnessModel :=
  object.generatedSemanticFlatWithin

/-- Generated flatness has no unmeasured required axis within its generated universe. -/
theorem generated_noUnmeasuredRequiredAxis
    {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    {object : GeneratedArchitectureObject presentation}
    (model : GeneratedArchitectureLawModel object) :
    NoUnmeasuredRequiredAxis object.generatedFlatnessModel
      object.generatedComponentUniverse := by
  exact
    ⟨staticCoverageComplete_of_componentUniverse
        object.generatedFlatnessModel object.generatedComponentUniverse,
      model.generated_runtimeCoverageComplete,
      object.generatedSemanticCoverageComplete⟩

/-- Generated law models discharge bounded architecture flatness. -/
theorem generatedArchitectureFlatWithin
    {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    {object : GeneratedArchitectureObject presentation}
    (model : GeneratedArchitectureLawModel object) :
    ArchitectureFlatWithin object.generatedFlatnessModel
      object.generatedComponentUniverse := by
  exact
    ⟨model.generated_noUnmeasuredRequiredAxis,
      model.generated_staticFlatWithin,
      model.generated_runtimeFlatWithin,
      model.generated_semanticFlatWithin⟩

/-- Generated bounded flatness can be promoted with its explicit generated coverage certificate. -/
theorem generatedArchitectureFlat
    {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    {object : GeneratedArchitectureObject presentation}
    (model : GeneratedArchitectureLawModel object) :
    ArchitectureFlat object.generatedFlatnessModel :=
  globalFlat_of_within_exhaustive
    model.generatedArchitectureFlatWithin
    model.generated_noUnmeasuredRequiredAxis
    (exactFlatnessObservation_of_exhaustiveCoverage
      model.generated_noUnmeasuredRequiredAxis)
    True.intro

end GeneratedArchitectureLawModel

end AAT
end Formal.Arch
