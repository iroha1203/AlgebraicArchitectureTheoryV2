import Formal.Arch.AAT.CompleteFormalization
import Formal.Arch.Examples.AtomGeneratedMoleculeExamples
import Formal.Arch.Examples.AtomGeneratedSignatureExamples

namespace Formal.Arch.AATCompleteFormalizationExamples

open Formal.Arch.AtomGeneratedMoleculeExamples
open Formal.Arch.AtomGeneratedSignatureExamples

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
noncomputable def generatedComponentTheoremSuite :
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

theorem generatedComponentTheoremSuite_has_analytic_representation_fields :
    (generatedComponentTheoremSuite
        |>.generatedAnalyticRepresentation
        |>.analyticRepresentation
        |>.coverageAssumptions) ∧
      (generatedComponentTheoremSuite
        |>.generatedAnalyticRepresentation
        |>.requiredSignatureObstructionValuation
        |>.coverageAssumptions) ∧
      (generatedComponentTheoremSuite
        |>.generatedAnalyticRepresentation
        |>.identityAnalyticExtensionFormulaPackage
        |>.FormulaEquation) := by
  exact
    ⟨generatedComponentTheoremSuite
        |>.generatedAnalyticRepresentation
        |>.analyticRepresentationCoverage,
      generatedComponentTheoremSuite
        |>.generatedAnalyticRepresentation
        |>.obstructionValuationCoverage,
      generatedComponentTheoremSuite
        |>.generatedAnalyticRepresentation
        |>.identityFormulaHolds⟩

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

theorem generatedComponentTheoremSuite_has_path_diagram_fields
    (carrier : AAT.GeneratedCarrier generatedComponentObject) :
    AAT.GeneratedDiagramFiller
      (object := generatedComponentObject)
      (fun _ _ _ _ _ _ _ _ => False)
      (fun _ _ _ _ => False)
      (fun _ _ _ _ => False)
      (generatedComponentNilDiagram carrier) := by
  exact
    generatedComponentTheoremSuite
      |>.generatedPathDiagram
      |>.reflexiveDiagramFiller
        (generatedComponentNilPath carrier)

theorem generatedComponentTheoremSuite_has_feature_extension_fields :
    AAT.GeneratedFeatureExtensionFields generatedComponentWorld := by
  exact generatedComponentTheoremSuite.generatedFeatureExtension

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

theorem generatedComponentTheoremSuite_has_sft_archsig_fieldsig_fields :
    (generatedComponentTheoremSuite
      |>.generatedSFTArchSigFieldSig
      |>.sftInputToLocalAlgebra
        atomGeneratedSignature_sftInput).usedAsLocalAlgebra ∧
      ArchitectureSignature.ArchitectureLawful
        generatedComponentWorld.lawModel.toArchitectureLawModel ∧
      atomGeneratedSignature_generatedArchSigTransition.fieldSigAnalysisBoundary ∧
      atomGeneratedSignature_sftForecastStatus.RecordsForecastBoundary := by
  let sourceBridge :=
    generatedComponentTheoremSuite
      |>.generatedSFTArchSigFieldSig
      |>.archsigTransitionSourceBridge
        atomGeneratedSignature_generatedArchSigTransition
  exact
    ⟨generatedComponentTheoremSuite
        |>.generatedSFTArchSigFieldSig
        |>.sftInputLocalAlgebraReadsGenerated
          atomGeneratedSignature_sftInput,
      ArchitectureSignature.AATCoreSignatureLawfulnessBridge.architectureLawful
        sourceBridge,
      generatedComponentTheoremSuite
        |>.generatedSFTArchSigFieldSig
        |>.fieldSigReadsArchSigTransitionAsSFTAnalysis
          atomGeneratedSignature_generatedFieldSigAnalysis,
      generatedComponentTheoremSuite
        |>.generatedSFTArchSigFieldSig
        |>.fieldSigForecastCorrectnessRemainsBoundary
          atomGeneratedSignature_generatedFieldSigAnalysis⟩

theorem generatedComponentTheoremSuite_registry_has_no_bridge_assumed_rows :
    AATReconstructionClassification.TheoremPackageClass.bridgeAssumed ∉
      AATReconstructionClassification.allClassificationClasses := by
  exact
    generatedComponentTheoremSuite
      |>.classificationRegistryHasNoBridgeAssumedRows

theorem generatedComponentTheoremSuite_registry_has_no_rewrite_targets :
    AATReconstructionClassification.ReconstructionAction.rewriteTarget ∉
      AATReconstructionClassification.allClassificationActions := by
  exact
    generatedComponentTheoremSuite
      |>.classificationRegistryHasNoRewriteTargets

theorem generatedComponentTheoremSuite_registry_source_rows_are_atom_generated :
    ∀ classAction ∈
      AATReconstructionClassification.allClassificationClassActions,
      classAction.2 =
        AATReconstructionClassification.ReconstructionAction.aatSourceOfTruth ->
        classAction.1 =
          AATReconstructionClassification.TheoremPackageClass.atomGenerated := by
  exact
    generatedComponentTheoremSuite
      |>.classificationRegistrySourceRowsAreAtomGenerated

theorem generatedComponentTheoremSuite_registry_representation_rows_are_downstream :
    ∀ classAction ∈
      AATReconstructionClassification.allClassificationClassActions,
      classAction.1 =
        AATReconstructionClassification.TheoremPackageClass.representationLevel ->
        classAction.2 =
          AATReconstructionClassification.ReconstructionAction.downstreamLibrary := by
  exact
    generatedComponentTheoremSuite
      |>.classificationRegistryRepresentationRowsAreDownstream

/--
The complete-formalization coordination artifact covers every current theorem
family before sub-agent proof filling begins.
-/
noncomputable def generatedComponentCompleteFormalization :
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

theorem generatedComponentCompleteFormalization_is_complete :
    generatedComponentCompleteFormalization.IsComplete := by
  exact AAT.initialCompleteFormalization_is_complete generatedComponentWorld

end Formal.Arch.AATCompleteFormalizationExamples
