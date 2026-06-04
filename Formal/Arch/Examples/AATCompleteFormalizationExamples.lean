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
  runtimeGraphRank := generatedComponentRuntimeGraphRank
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

theorem generatedComponentTheoremSuite_has_graph_rank_fields :
    generatedComponentTheoremSuite.generatedGraphRank.relationGraphRank =
        generatedComponentGraphRank ∧
      generatedComponentTheoremSuite.generatedGraphRank.runtimeGraphRank =
        generatedComponentRuntimeGraphRank ∧
      WalkAcyclic (AAT.GeneratedArchGraph generatedComponentWorld.object) ∧
      WalkAcyclic (AAT.GeneratedRuntimeGraph generatedComponentWorld.object) := by
  exact
    ⟨rfl, rfl,
      generatedComponentTheoremSuite
        |>.generatedGraphRank
        |>.relationGraphRankWalkAcyclic,
      generatedComponentTheoremSuite
        |>.generatedGraphRank
        |>.runtimeGraphRankWalkAcyclic⟩

theorem generatedComponentTheoremSuite_has_flatness_curvature_fields :
    ArchitectureFlat generatedComponentObject.generatedFlatnessModel ∧
      totalCurvature AAT.generatedAtomShapeCoordinateDistance
        generatedComponentObject.generatedAtomShapeCoordinateSemantics
        generatedComponentObject.generatedSemanticDiagrams = 0 := by
  exact
    ⟨generatedComponentTheoremSuite
        |>.generatedFlatnessCurvature
        |>.architectureFlat,
      generatedComponentTheoremSuite
        |>.generatedFlatnessCurvature
        |>.shapeCoordinateTotalCurvature_eq_zero⟩

theorem generatedComponentTheoremSuite_has_operation_repair_synthesis_fields :
    (∀ {target : AAT.GeneratedArchitectureObject generatedComponentWorld.presentation}
      (_operation : AAT.GeneratedOperation generatedComponentWorld.object target),
        generatedComponentWorld.system.noToolOutputCreatesAtoms) ∧
    (∀ {configuration :
        AAT.GeneratedRepairProblemConfiguration generatedComponentWorld.presentation}
      {target : AAT.GeneratedArchitectureObject generatedComponentWorld.presentation}
      (_repair : AAT.GeneratedRepairFromProblem configuration target)
      (targetModel : AAT.GeneratedArchitectureLawModel target),
        Nonempty (AAT.RepairClearingPackage
          targetModel.generatedAATCore
          (Sum
            (AAT.GeneratedRepairProblemConfiguration
              generatedComponentWorld.presentation)
            (AAT.GeneratedArchitectureObject generatedComponentWorld.presentation))
          Unit
          (Sum.inl configuration)
          (Sum.inr target))) ∧
    (∀ {object : AAT.GeneratedArchitectureObject generatedComponentWorld.presentation}
      (candidate : AAT.GeneratedSynthesisCandidate object),
        Nonempty (AAT.SynthesisSoundnessPackage
          candidate.lawModel.generatedAATCore
          (AAT.GeneratedSynthesisCandidate object))) := by
  exact
    ⟨by
      intro _target operation
      exact
        generatedComponentTheoremSuite
          |>.generatedOperationRepairSynthesis
          |>.operationDoesNotCreateAtoms operation,
    by
      constructor
      · intro _configuration _target repair targetModel
        exact ⟨
          generatedComponentTheoremSuite
            |>.generatedOperationRepairSynthesis
            |>.repairToRepairClearingPackage repair targetModel⟩
      · intro _object candidate
        exact ⟨
          generatedComponentTheoremSuite
            |>.generatedOperationRepairSynthesis
            |>.synthesisToSynthesisSoundnessPackage candidate⟩⟩

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
