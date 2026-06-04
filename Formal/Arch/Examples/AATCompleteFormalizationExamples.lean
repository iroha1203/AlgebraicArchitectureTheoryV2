import Formal.Arch.AAT.CompleteFormalization
import Formal.Arch.Examples.AtomGeneratedMoleculeExamples

namespace Formal.Arch.AATCompleteFormalizationExamples

open Formal.Arch.AtomGeneratedMoleculeExamples

/-- Concrete generated world used to test the complete-formalization skeleton. -/
def generatedComponentWorld : AAT.AtomGeneratedAATWorld where
  system := componentSystem
  presentation := componentShapePresentation
  object := generatedComponentObject
  lawModel := generatedComponentLawModel
  atomDecidable := inferInstance
  relationDecidable := inferInstance

/-- The first suite is inhabited by the existing generated component model. -/
def generatedComponentTheoremSuite :
    AAT.AATTheoremSuite generatedComponentWorld :=
  AAT.initialTheoremSuite generatedComponentWorld

theorem generatedComponentTheoremSuite_has_required_axes_zero :
    generatedComponentWorld.RequiredSignatureAxesZero := by
  exact generatedComponentTheoremSuite.generatedSignatureAxesZero

theorem generatedComponentTheoremSuite_has_static_structural_core :
    generatedComponentWorld.StaticStructuralCore := by
  exact generatedComponentTheoremSuite.generatedStaticStructuralCore

theorem generatedComponentTheoremSuite_has_generated_aat_core_bridge_fields :
    generatedComponentWorld.GeneratedAATCoreNoObservationDependency ∧
      generatedComponentWorld.GeneratedAATCoreCircuitBoundary := by
  exact
    ⟨generatedComponentTheoremSuite.generatedAATCoreNoObservationDependency,
      generatedComponentTheoremSuite.generatedAATCoreCircuitBoundary⟩

theorem generatedComponentTheoremSuite_has_generated_object_fields :
    (∀ carrier : AAT.GeneratedCarrier generatedComponentWorld.object,
      generatedComponentWorld.system.Primitive carrier.val) ∧
      AAT.ArchMapGeneratedObjectHandoff generatedComponentWorld := by
  exact
    ⟨generatedComponentTheoremSuite
        |>.generatedMoleculeObject
        |>.objectCarrierAtomPrimitive,
      generatedComponentTheoremSuite
        |>.generatedMoleculeObject
        |>.archMapHandoffToGeneratedObject⟩

theorem generatedComponentTheoremSuite_registry_has_no_bridge_assumed_rows :
    AATReconstructionClassification.TheoremPackageClass.bridgeAssumed ∉
      AATReconstructionClassification.allClassificationClasses := by
  exact
    generatedComponentTheoremSuite
      |>.classificationRegistryHasNoBridgeAssumedRows

/--
The complete-formalization coordination artifact covers every current theorem
family before sub-agent proof filling begins.
-/
def generatedComponentCompleteFormalization :
    AAT.AATCompleteFormalization :=
  AAT.initialCompleteFormalization generatedComponentWorld

theorem generatedComponentCompleteFormalization_frontier_covers_all_families :
    generatedComponentCompleteFormalization.implementationFrontier.map
        (fun row => row.family) =
      AAT.allAATTheoremFamilies := by
  exact generatedComponentCompleteFormalization.frontierCoversFamilies

theorem generatedComponentCompleteFormalization_parallel_rows_are_safe :
    generatedComponentCompleteFormalization.implementationFrontier.all
      (fun row =>
        if row.parallelAllowed = true then
          decide (row.coordinationRequired = false)
        else
          true) = true := by
  simpa [generatedComponentCompleteFormalization,
    AAT.initialCompleteFormalization]
    using AAT.parallel_frontier_rows_are_not_core_coordination

end Formal.Arch.AATCompleteFormalizationExamples
