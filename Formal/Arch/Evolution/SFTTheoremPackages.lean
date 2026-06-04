import Formal.Arch.Evolution.SFTField
import Formal.Arch.Evolution.SFTForecastCone
import Formal.Arch.Evolution.SFTConeProjection
import Formal.Arch.Evolution.SFTSupportSafety
import Formal.Arch.Evolution.SFTArtifactAction
import Formal.Arch.Evolution.SFTPolicy
import Formal.Arch.Evolution.SFTReachability
import Formal.Arch.Evolution.SFTFieldUpdate
import Formal.Arch.AAT.GeneratedSFT
import Formal.Arch.Evolution.SFTEnvelope
import Formal.Arch.Evolution.SFTInterfaceBoundary
import Formal.Arch.Evolution.SFTArchSigBoundary
import Formal.Arch.Evolution.SFTCounterexamples
import Formal.Arch.Evolution.SFTClockedCone
import Formal.Arch.Evolution.SFTFieldCover
import Formal.Arch.Evolution.SFTDescent
import Formal.Arch.Evolution.SFTFiniteCover
import Formal.Arch.Evolution.SFTFiniteExactModel
import Formal.Arch.Evolution.SFTCechCohomology
import Formal.Arch.Evolution.SFTDescentObstruction
import Formal.Arch.Evolution.SFTTheoremRoadmap
import Formal.Arch.Evolution.SFTAgenticConfluence
import Formal.Arch.Evolution.SFTFundamentalModularity
import Formal.Arch.Evolution.SFTAATFundamentalModularity
import Formal.Arch.Evolution.SFTAATFundamentalModularityExamples
import Formal.Arch.Evolution.SFTArtifactBoundaryBridge
import Formal.Arch.Evolution.SFTAATArtifactBoundaryExamples

/-!
Documentation-facing entrypoints for the SFT Lean theorem packages.

This module is intentionally thin. Importing it exposes the SFT formal surface
implemented across the first `ForecastCone` wave and the remaining SFT boundary
issues without adding forecast correctness, calibration, extractor completeness,
or global future-safety claims.
-/

namespace Formal.Arch

namespace SFTTheoremPackages

/--
A stable documentation-facing mapping from SFT schematic statements to the Lean
declarations that currently carry the corresponding bounded package.
-/
structure SchematicCorrespondence where
  schematic : String
  leanDeclarations : List String
  reading : String
  status : String
  deriving Repr

/-- SFT theorem-package groups used by docs and website-facing status tables. -/
inductive Candidate where
  | softwareFieldProjection
  | forecastConeCore
  | coneProjection
  | artifactAction
  | operationPolicyGovernance
  | stableRegionReachability
  | supportSafety
  | fieldUpdate
  | consequenceEnvelope
  | aatInterfaceBoundary
  | archSigReportBoundary
  | counterexamplePackage
  | theoremRoadmap
  | finiteExactModel
  | aatSupportedFundamentalModularity
  deriving DecidableEq, Repr

namespace Candidate

/-- SFT source section that the candidate primarily indexes. -/
def sftSection : Candidate -> String
  | softwareFieldProjection => "Part III / 8"
  | forecastConeCore => "Part III / 12"
  | coneProjection => "Part III / 12"
  | artifactAction => "Part III / 9"
  | operationPolicyGovernance => "Part III / 10 and 13"
  | stableRegionReachability => "Part IV / 19"
  | supportSafety => "Part III / 12"
  | fieldUpdate => "Part III / 14"
  | consequenceEnvelope => "Part III / 12"
  | aatInterfaceBoundary => "AAT / SFT interface"
  | archSigReportBoundary => "AAT / SFT interface"
  | counterexamplePackage => "AAT / SFT forbidden readings"
  | theoremRoadmap => "SFT theorem roadmap"
  | finiteExactModel => "SFT theorem roadmap"
  | aatSupportedFundamentalModularity => "AAT / SFT interface"

/-- Stable schematic name used by documentation and status tables. -/
def schematicName : Candidate -> String
  | softwareFieldProjection => "SoftwareField projection boundary"
  | forecastConeCore => "ForecastCone core"
  | coneProjection => "ForecastCone projection and monotonicity"
  | artifactAction => "Artifact-mediated candidate update"
  | operationPolicyGovernance => "OperationPolicy and GovernanceIntervention"
  | stableRegionReachability => "Stable-region reachability"
  | supportSafety => "SFT support safety"
  | fieldUpdate => "FieldUpdate record preservation"
  | consequenceEnvelope => "ConsequenceEnvelope projection"
  | aatInterfaceBoundary => "AAT theorem-status interface boundary"
  | archSigReportBoundary => "ArchSig-SFT report boundary"
  | counterexamplePackage => "SFT-native counterexample package"
  | theoremRoadmap => "SFT theorem roadmap theorem packages"
  | finiteExactModel => "Finite exact SFT model"
  | aatSupportedFundamentalModularity =>
      "AAT-supported finite selected Fundamental Modularity"

/-- Representative Lean declarations that serve as public entrypoints. -/
def representativeDeclarations : Candidate -> List String
  | softwareFieldProjection =>
      ["SoftwareField",
       "SoftwareFieldEstimate",
       "ArchitectureProjectionBoundary",
       "ArchitectureProjectionBoundary.projection_records_nonConclusions",
       "AtomGeneratedSignatureExamples.atomGeneratedSignature_generatedSoftwareField",
       "AtomGeneratedSignatureExamples.atomGeneratedSignature_generatedSoftwareFieldEstimate",
       "AtomGeneratedSignatureExamples.atomGeneratedSignature_generatedArchitectureProjectionBoundary",
       "AtomGeneratedSignatureExamples.atomGeneratedSignature_generatedSoftwareField_projects_to_generated",
       "AtomGeneratedSignatureExamples.atomGeneratedSignature_generatedSoftwareField_records_nonConclusions"]
  | forecastConeCore =>
      ["OperationSupport",
       "StepRelation",
       "FieldPath",
       "ForecastCone",
       "ForecastCone.monotone_horizon",
       "AtomGeneratedSignatureExamples.atomGeneratedSignature_sftSupportSafetyPackage",
       "AtomGeneratedSignatureExamples.atomGeneratedSignature_generatedForecastCone_mem",
       "AtomGeneratedSignatureExamples.atomGeneratedSignature_generatedForecastCone_length_le_horizon",
       "AtomGeneratedSignatureExamples.atomGeneratedSignature_generatedForecastCone_monotone_succ"]
  | coneProjection =>
      ["PointwiseSupportInclusion",
       "StepSimulation",
       "ForecastConeProjection.forecastCone_projects_of_supportInclusion_and_stepSimulation",
       "ForecastConeProjection.forecastCone_projects_of_supportInclusion_and_horizon_le",
       "AtomGeneratedSignatureExamples.atomGeneratedSignature_supportSelfInclusion",
       "AtomGeneratedSignatureExamples.atomGeneratedSignature_generatedForecastCone_projects_self",
       "AtomGeneratedSignatureExamples.atomGeneratedSignature_exists_projected_generatedForecastCone",
       "AtomGeneratedSignatureExamples.atomGeneratedSignature_generatedForecastCone_projects_horizon_succ"]
  | artifactAction =>
      ["CandidateUpdateRelation",
       "ArtifactAction",
       "DeterministicArtifactAction",
       "ForecastConeFamilyAfterAction",
       "AtomGeneratedSignatureExamples.atomGeneratedSignature_artifactAction",
       "AtomGeneratedSignatureExamples.atomGeneratedSignature_deterministicArtifactAction",
       "AtomGeneratedSignatureExamples.atomGeneratedSignature_forecastConeAfterArtifact",
       "AtomGeneratedSignatureExamples.atomGeneratedSignature_forecastConeAfterArtifact_candidate_member",
       "AtomGeneratedSignatureExamples.atomGeneratedSignature_forecastConeAfterArtifact_length_le_horizon"]
  | operationPolicyGovernance =>
      ["OperationPolicy",
       "SupportTransformation",
       "GovernanceIntervention",
       "GovernanceIntervention.restrictive_forecastCone_projects",
       "AtomGeneratedSignatureExamples.atomGeneratedSignature_generatedOperationPolicy",
       "AtomGeneratedSignatureExamples.atomGeneratedSignature_generatedGovernanceIntervention",
       "AtomGeneratedSignatureExamples.atomGeneratedSignature_generatedGovernance_restrictive",
       "AtomGeneratedSignatureExamples.atomGeneratedSignature_generatedGovernance_projects_forecastCone",
       "AtomGeneratedSignatureExamples.atomGeneratedSignature_generatedGovernance_keeps_nonConclusion"]
  | stableRegionReachability =>
      ["FieldRegion",
       "MayReach",
       "MustReach",
       "StableRegion",
       "ReachablePreimage",
       "AtomGeneratedSignatureExamples.atomGeneratedSignature_generatedFieldRegion",
       "AtomGeneratedSignatureExamples.atomGeneratedSignature_generatedStableRegion",
       "AtomGeneratedSignatureExamples.atomGeneratedSignature_generatedMayReach",
       "AtomGeneratedSignatureExamples.atomGeneratedSignature_generatedMustReach",
       "AtomGeneratedSignatureExamples.atomGeneratedSignature_generatedReachablePreimage"]
  | supportSafety =>
      ["SFTSupportSafetyPackage",
       "SFTSupportSafetyPackage.operationSupport",
       "SFTSupportSafetyPackage.stepRelation",
       "SFTSupportSafetyPackage.AcceptedSupportedTrajectory.forecastCone_and_supportSafety",
       "AtomGeneratedSignatureExamples.atomGeneratedSignature_sftSupportSafetyPackage",
       "AtomGeneratedSignatureExamples.atomGeneratedSignature_acceptedSupportedTrajectory",
       "AtomGeneratedSignatureExamples.atomGeneratedSignature_supportSafety_forecastCone_and_safety"]
  | fieldUpdate =>
      ["ForecastRecord",
       "ObservedOutcome",
       "PosteriorFieldRecord",
       "FieldUpdate",
       "FieldUpdate.UpdateSound.fieldUpdate_records_nonConclusions"]
  | consequenceEnvelope =>
      ["ConeFamily",
       "ObservationBoundary",
       "ConsequenceEnvelope",
       "EnvelopeProjection.envelope_does_not_strengthen_forecast_claim",
       "GeneratedAATConsequenceEnvelope",
       "GeneratedAATConsequenceEnvelope.theorem_status_from_generated",
       "GeneratedAATConsequenceEnvelope.records_transition_boundaries",
       "GeneratedAATConsequenceEnvelope.forecast_correctness_remains_boundary",
       "AATCorePremisedConsequenceEnvelope",
       "AATCorePremisedConsequenceEnvelope.aatcore_premise_does_not_prove_forecast_correctness"]
  | aatInterfaceBoundary =>
      ["AATTheoremStatus",
       "SFTForecastStatus",
       "AAT.GeneratedArchitectureLawModel.generatedAATTheoremStatusForSFT",
       "AAT.GeneratedArchitectureLawModel.generatedAATTheoremStatusForSFT_recordsTheoremPackage",
       "AAT.GeneratedArchitectureLawModel.generatedAATTheoremStatusForSFT_recordsMeasuredZeroEvidence",
       "AAT.GeneratedSFTInput",
       "AAT.GeneratedSFTInput.theoremStatus",
       "AAT.GeneratedSFTInput.theoremStatusFromGenerated",
       "AAT.GeneratedSFTInput.measured_zero_from_generated",
       "AAT.GeneratedSFTInput.reads_generated_aat_as_sft_local_premise",
       "AAT.GeneratedSFTInput.sft_event_does_not_create_atoms",
       "AAT.GeneratedArchitectureLawModel.generatedIdentityAATCoreCircuitDelta",
       "AAT.GeneratedArchitectureLawModel.generatedIdentityAATCoreCircuitDelta_circuitBoundary",
       "AAT.GeneratedArchitectureLawModel.generatedIdentityAATCoreCircuitDelta_doesNotCreateAtoms",
       "AATCoreLocalAlgebraForSFT",
       "AATCoreTransition",
       "AATCoreTransportTransition",
       "AATCoreTransportCircuitDelta",
       "AATToSFTInterfaceBoundary",
       "AATToSFTInterfaceBoundary.aat_lawfulness_alone_does_not_discharge_trajectory_safety_boundary"]
  | archSigReportBoundary =>
      ["ArchSigSFTReport",
       "ArchSigSFTReportEstimateBoundary",
       "ArchSigAATCoreTransition",
       "FieldSigAATCoreTransitionAnalysis",
       "GeneratedArchSigAATCoreTransition",
       "GeneratedFieldSigAATCoreTransitionAnalysis",
       "GeneratedArchSigAATCoreTransition.ofTransition",
       "GeneratedArchSigAATCoreTransition.generatedArchSigDoesNotDefineAAT_recorded",
       "GeneratedArchSigAATCoreTransition.generatedFieldSigAnalysisBoundary_recorded",
       "GeneratedArchSigAATCoreTransition.generatedUnknownRejectedUnmeasuredSeparated_recorded",
       "GeneratedArchSigAATCoreTransition.sourceBridge",
       "GeneratedArchSigAATCoreTransition.targetBridge",
       "GeneratedArchSigAATCoreTransition.source_bridge_architectureLawful",
       "GeneratedFieldSigAATCoreTransitionAnalysis.fieldsig_reads_generated_archsig_transition_as_sft_analysis",
       "GeneratedArchSigAATCoreTransportTransition",
       "GeneratedFieldSigAATCoreTransportTransitionAnalysis",
       "GeneratedArchSigAATCoreTransportTransition.ofTransportTransition",
       "GeneratedArchSigAATCoreTransportTransition.generatedArchSigDoesNotDefineAAT_recorded",
       "GeneratedArchSigAATCoreTransportTransition.generatedFieldSigAnalysisBoundary_recorded",
       "GeneratedArchSigAATCoreTransportTransition.generatedUnknownRejectedUnmeasuredSeparated_recorded",
       "GeneratedArchSigAATCoreTransportTransition.sourceBridge",
       "GeneratedArchSigAATCoreTransportTransition.targetBridge",
       "GeneratedArchSigAATCoreTransportTransition.source_bridge_architectureLawful",
       "GeneratedFieldSigAATCoreTransportTransitionAnalysis.fieldsig_reads_generated_archsig_transport_transition_as_sft_analysis",
       "ArchSigSFTReportEstimateBoundary.report_existence_does_not_promote_aat_theorem_status",
       "ArchSigSFTReportEstimateBoundary.report_existence_does_not_promote_calibrated_forecast"]
  | counterexamplePackage =>
      ["SFTCounterexampleKind",
       "SFTCounterexamples.Package",
       "SFTCounterexamples.canonicalPackage",
       "SFTCounterexamples.records_nonConclusions"]
  | theoremRoadmap =>
      ["ClockedForecastCone",
       "BoundedClockedForecastCone",
       "ClockedForecastCone.length_eq_horizon",
       "clockedForecastCone_of_forecastCone",
       "BinaryFieldCover",
       "BinarySFTModel",
       "CompatibleLocalClockedStep",
       "CompatibleLocalClockedPath",
       "BinaryClockedStepGluingData",
       "glueCompatibleBinaryClockedConeFamily",
       "BinaryProjectionGluingLaws",
       "GlobalConePointPathEquivalenceData",
       "LocalFamilyPathEquivalenceData",
       "BinaryProjectionGluingPathLaws",
       "BinaryProjectionGluingPathLaws.toEndpointLaws",
       "BinaryProjectionGluingPathLaws.glue_project_after_projection_endpoint",
       "BinaryProjectionGluingPathLaws.project_after_glue_endpoint",
       "UniformFiniteFieldCover",
       "Cech0Simplex",
       "Cech1Simplex",
       "Cech2Simplex",
       "FiniteSFTModel",
       "FiniteLocalClockedConeFamily",
       "FiniteClockedGluingData",
       "FiniteProjectionGluingLaws",
       "forecastCone_descent_finite_of_laws",
       "FiniteSelectedForecastConeDescentPackage.ofLaws",
       "finiteForecastConeDescentPackage_of_laws",
       "finiteCoverOfBinaryCover",
       "FiniteCechDescentCohomologyBridge",
       "SFTTheoremRoadmap.finiteForecastConeDescent_of_laws",
       "FiniteDescentFailureKind",
       "FiniteDescentFailure",
       "FiniteObstructionClass",
       "FiniteDescentObstructionPayload",
       "FiniteTypedObstructionWitness.payload_failureKind_eq",
       "FiniteDescentObstructionClassifier",
       "FiniteDescentObstructionClassifier.classified_failureKind_eq",
       "FiniteDescentObstructionClassifier.classified_payload_failureKind_eq",
       "FiniteDescentObstructionClassifier.classified_payload_matches_witness_kind",
       "finite_descent_obstruction_of_classified_failure_sound",
       "finite_descent_obstruction_of_classified_failure_sound_complete",
       "FiniteDescentObstructionPackage",
       "finite_descent_obstruction_of_failure",
       "finite_descent_obstruction_of_failure_sound",
       "FiniteExactFailureClassifierCompleteness",
       "finiteExact_failure_classifier_complete",
       "CechCocycleObstruction",
       "FiniteCechTypedObstructionBridge",
       "cech_obstruction_of_typed_witness",
       "typed_obstruction_of_cech_cocycle_obstruction",
       "FiniteCechObstructionBridge",
       "FiniteObstructionReviewProjection",
       "FiniteGovernanceCutTarget",
       "FiniteGovernanceCuttingPackage",
       "finite_governance_cuts_bad_obstruction",
       "finite_governance_preserves_desired_family",
       "FiniteObstructionGovernancePackage",
       "governance_cuts_obstruction_of_finite_failure",
       "FiniteExactGovernanceCuttingSoundness",
       "finiteExact_governance_cuts_bad_failure",
       "finiteExact_governance_preserves_desired_family",
       "finiteExact_governance_cutting_sound",
       "SFTTheoremRoadmap.FiniteGovernanceSynthesisBridge",
       "SFTTheoremRoadmap.FiniteGovernanceSynthesisBridge.synthesized_intervention_of_guard_family",
       "SFTTheoremRoadmap.FiniteGovernanceSynthesisBridge.guard_family_hits_and_misses",
       "SFTTheoremRoadmap.FiniteGovernanceSynthesisBridge.guard_family_hits_selected_bad",
       "SFTTheoremRoadmap.FiniteGovernanceSynthesisBridge.governanceCuttingPackage",
       "SFTTheoremRoadmap.FiniteGovernanceSynthesisBridge.governanceCuttingPackage_cuts_bad",
       "SFTTheoremRoadmap.FiniteGovernanceSynthesisBridge.governanceCuttingPackage_preserves_desired",
       "SFTTheoremRoadmap.FiniteGovernanceSynthesisBridge.obstructionGovernancePackage",
       "SFTTheoremRoadmap.finite_governance_cuts_obstruction_of_failure",
       "BinaryProjectionGluingEquivalenceLaws.ofEndpointLaws",
       "BinaryDescentAssumptions.ofStepGluing",
       "BinaryDescentAssumptions.ofEndpointLaws",
       "forecastCone_descent_binary_of_endpoint_laws",
       "forecastCone_descent_binary_of_path_laws",
       "binaryForecastConeDescentPackage_of_path_laws",
       "forecastCone_descent_binary",
       "SFTTheoremRoadmap.ClockedForecastConeDescentPackage.forecastCone_descent",
       "SFTTheoremRoadmap.ModularityRepresentationPackage.modularity_representation",
       "SFTTheoremRoadmap.DescentObstructionPackage.descent_obstruction_of_surjectivity_failure",
       "SFTTheoremRoadmap.ConeCohomologyPackage.h1_zero_iff_local_futures_glue",
       "SFTTheoremRoadmap.ObstructionAwareReviewEquivalence",
       "SFTTheoremRoadmap.decisionSoundProjection_of_obstructionAware",
       "SFTTheoremRoadmap.FundamentalModularityTheoremPackage.bounded_evolution_governed_or_typed_witness",
       "SFTFundamentalModularity.FundamentalEvolutionOutcome",
       "SFTFundamentalModularity.FundamentalBoundaryFailureKind",
       "SFTFundamentalModularity.TypedComputationBoundaryFailure",
       "SFTFundamentalModularity.ComputablyGoverned",
       "SFTFundamentalModularity.FundamentalDescentComponent",
       "SFTFundamentalModularity.FundamentalObstructionComponent",
       "SFTFundamentalModularity.FundamentalReviewComponent",
       "SFTFundamentalModularity.FundamentalGovernanceComponent",
       "SFTFundamentalModularity.FundamentalCalibrationComponent",
       "SFTFundamentalModularity.FundamentalAgenticComponent",
       "SFTFundamentalModularity.FundamentalModularityHypotheses",
       "SFTFundamentalModularity.roadmapConclusion_of_hypotheses",
       "SFTFundamentalModularity.roadmapPackage_of_hypotheses",
       "SFTFundamentalModularity.fundamental_modularity_final_assembly",
       "SFTFundamentalModularity.final_bounded_evolution_governed_or_typed_failure",
       "SFTFundamentalModularity.final_agentic_confluence",
       "SFTFundamentalModularity.final_governed_agenticConfluenceAvailable",
       "SFTFundamentalModularity.final_modularity_iff_forecastConeDescent",
       "SFTFundamentalModularity.FiniteSelectedFundamentalModularityTheorem",
       "SFTFundamentalModularity.FiniteSelectedFundamentalModularityTheorem.finiteSelected_fundamental_modularity",
       "SFTFundamentalModularity.FiniteSelectedFundamentalModularityTheorem.governed_or_typed_failure",
       "SFTFundamentalModularity.FiniteSelectedFundamentalModularityTheorem.modularity_iff_forecastConeDescent",
       "SFTFundamentalModularity.governanceComponent_of_finiteObstructionGovernance",
       "SFTFundamentalModularity.governanceComponent_of_finiteExactGovernanceSoundness",
       "SFTFundamentalModularity.governanceComponent_records_finiteExact_cut",
       "SFTFundamentalModularity.governanceComponent_records_finiteExact_desired_preservation",
       "SFTFundamentalModularity.governanceComponent_of_finiteGovernanceSynthesisBridge",
       "SFTFundamentalModularity.governanceComponent_records_synthesis_cut",
       "SFTFundamentalModularity.governanceComponent_records_synthesis_desired_preservation",
       "SFTFundamentalModularity.governanceComponent_records_synthesis_guard_family",
       "SFTFundamentalModularity.reviewComponent_of_minimalEnvelopePackage",
       "SFTFundamentalModularity.reviewComponent_records_minimalEnvelope",
       "SFTFundamentalModularity.reviewComponent_records_minimalEnvelope_boundary",
       "SFTFundamentalModularity.reviewComponent_records_minimalEnvelope_nonConclusions",
       "SFTFundamentalModularity.FiniteObstructionAwareReviewEnvelopeBridge",
       "SFTFundamentalModularity.FiniteObstructionAwareReviewEnvelopeBridge.obstructionDecision_factors",
       "SFTFundamentalModularity.reviewComponent_of_obstructionAwareEnvelopeBridge",
       "SFTFundamentalModularity.reviewComponent_records_obstructionAware_minimalEnvelope",
       "SFTFundamentalModularity.reviewComponent_records_obstructionAware_boundary",
       "SFTFundamentalModularity.reviewComponent_records_obstructionAware_nonConclusions",
       "SFTFundamentalModularity.calibrationComponent_of_closedLoopPackage",
       "SFTFundamentalModularity.calibrationComponent_records_boundaryExplicit",
       "SFTFundamentalModularity.calibrationComponent_records_fixedPointOrBoundary",
       "SFTFundamentalModularity.calibrationComponent_records_closedLoop_nonConclusions",
       "SFTTheoremRoadmap.FiniteHeightClosedLoopCalibrationBridge",
       "SFTTheoremRoadmap.FiniteHeightClosedLoopCalibrationBridge.closedLoopPackage",
       "SFTTheoremRoadmap.FiniteHeightClosedLoopCalibrationBridge.finiteHeight_closedLoopCalibration_fixedPoint_or_boundary",
       "SFTTheoremRoadmap.FiniteHeightClosedLoopCalibrationBridge.RecordsCalibrationBoundary",
       "SFTTheoremRoadmap.FiniteHeightClosedLoopCalibrationBridge.RecordsNonConclusions",
       "SFTFundamentalModularity.calibrationComponent_of_finiteHeightClosedLoopBridge",
       "SFTFundamentalModularity.calibrationComponent_records_finiteHeight_fixedPointOrBoundary",
       "SFTFundamentalModularity.calibrationComponent_records_finiteHeight_boundary",
       "SFTFundamentalModularity.calibrationComponent_records_finiteHeight_boundaryExplicit",
       "SFTFundamentalModularity.calibrationComponent_records_finiteHeight_nonConclusions",
       "SFTFundamentalModularity.agenticComponent_of_agenticConfluencePackage",
       "SFTFundamentalModularity.agenticComponent_records_agenticConfluence",
       "SFTFundamentalModularity.agenticComponent_records_confluence",
       "SFTFundamentalModularity.agenticComponent_records_agentBoundary",
       "SFTFundamentalModularity.agenticComponent_records_nonConclusions",
       "SFTFundamentalModularity.agenticComponent_governedAvailability",
       "SFTAgenticConfluence.ReductionReaches",
       "SFTAgenticConfluence.NewmanStyleConfluenceKernel",
       "SFTAgenticConfluence.NewmanStyleConfluenceKernel.newmanStyle_fairInterleavingsConverge",
       "SFTAgenticConfluence.NewmanStyleConfluenceKernel.agenticPackage",
       "SFTAgenticConfluence.NewmanStyleConfluenceKernel.agenticPackage_records_newmanStyle_confluence",
       "SFTAgenticConfluence.NewmanStyleConfluenceKernel.RecordsNonConclusions",
       "SFTFundamentalModularity.agenticComponent_of_newmanStyleConfluenceKernel",
       "SFTFundamentalModularity.agenticComponent_records_newmanStyle_confluence",
       "SFTFundamentalModularity.agenticComponent_records_newmanStyle_nonConclusions"]
  | finiteExactModel =>
      ["FiniteExactSFTModel",
       "FiniteExactSFTModel.exactCover",
       "FiniteExactSFTModel.descentModel",
       "FiniteExactSFTModel.RecordsSelectedUniverseBoundary",
       "FiniteExactSFTModel.RecordsExactCoverBoundary",
       "FiniteExactSFTModel.RecordsOperationBoundary",
       "FiniteExactSFTModel.RecordsFiniteModelBoundary",
       "FiniteExactSFTModel.RecordsObservationBoundary",
       "FiniteExactSFTModel.RecordsGovernanceBasisBoundary",
       "FiniteExactSFTModel.RecordsExtractorEmpiricalBoundary",
       "FiniteExactSFTModel.RecordsNonConclusions",
       "FiniteExactDescentAssumptions",
       "FiniteExactDescentAssumptions.descentPackage",
       "finiteExactForecastConeDescentPackage_of_assumptions",
       "CechCone0",
       "CechCone1",
       "IsCechConeCocycle",
       "CechConeCoboundary",
       "IsCechConeCoboundary",
       "cechConeCocycle_of_finiteLocalFamily",
       "CechConeH1Vanishes",
       "CechConeH1Vanishes.cocycle_is_coboundary",
       "CechH1FiniteDescentAssumptions",
       "h1_vanishes_implies_finite_descent"]
  | aatSupportedFundamentalModularity =>
      ["SFTAATFundamentalModularity.AATSelectedArchitectureSlice",
       "SFTAATFundamentalModularity.AATSelectedArchitectureSlice.ArchMapDerivedAATSliceBoundary",
       "SFTAATFundamentalModularity.AATSelectedArchitectureSlice.ofArchMapObservationBoundary",
       "SFTAATFundamentalModularity.AATSelectedArchitectureSlice.archMap_records_selectedArchitecture",
       "SFTAATFundamentalModularity.AATSelectedArchitectureSlice.archMap_preserves_nonConclusions",
       "SFTAATFundamentalModularity.ArchSigDerivedSFTReportBoundary",
       "SFTAATFundamentalModularity.ArchSigDerivedSFTReportBoundary.report_boundary_does_not_strengthen_theorem_status",
       "SFTAATFundamentalModularity.ArchSigDerivedSFTReportBoundary.report_boundary_does_not_calibrate_forecast",
       "SFTAATFundamentalModularity.AATSelectedArchitectureSlice.RecordsProjectionBoundary",
       "SFTAATFundamentalModularity.AATSupportedSFTBoundary",
       "SFTAATFundamentalModularity.AATSupportedSFTBoundary.ofSelectedSliceAndFiniteExactModel",
       "SFTAATFundamentalModularity.AATSupportedSFTBoundary.ofGeneratedSFTInput",
       "SFTAATFundamentalModularity.AATSupportedSFTBoundary.ofGeneratedSFTInput_aatStatus_eq_generated",
       "SFTAATFundamentalModularity.AATSupportedSFTBoundary.ofGeneratedSFTInput_reads_generated_status_as_local_premise",
       "SFTAATFundamentalModularity.AATSupportedSFTBoundary.ofGeneratedSFTInputAndArchSigTransition",
       "SFTAATFundamentalModularity.AATSupportedSFTBoundary.ofGeneratedSFTInputAndArchSigTransition_aatStatus_eq_generated",
       "SFTAATFundamentalModularity.AATSupportedSFTBoundary.ofGeneratedSFTInputAndArchSigTransition_records_archsig_boundary",
       "SFTAATFundamentalModularity.AATSupportedSFTBoundary.ofGeneratedSFTInputAndArchSigTransition_records_theorem_boundary",
       "SFTAATFundamentalModularity.AATSupportedSFTBoundary.ofGeneratedSFTInputAndArchSigTransition_records_typed_failure_boundary",
       "SFTAATFundamentalModularity.AATSupportedSFTBoundary.ofGeneratedSFTInputAndArchSigTransition_records_nonConclusions",
       "SFTAATFundamentalModularity.AATSupportedSFTBoundary.ofArchMapAndArchSigBoundaries",
       "SFTAATFundamentalModularity.AATSupportedSFTBoundary.artifact_constructor_records_archMap_boundaries",
       "SFTAATFundamentalModularity.AATSupportedSFTBoundary.artifact_constructor_preserves_nonConclusions",
       "SFTAATFundamentalModularity.AATSupportedSFTBoundary.aat_status_as_sft_local_premise",
       "SFTAATFundamentalModularity.AATSupportedSFTBoundary.records_projection_observation_reconstruction_missingEvidence",
       "SFTAATFundamentalModularity.AATSupportedSFTBoundary.records_selected_finite_source_horizon",
       "SFTAATFundamentalModularity.AATSupportedSFTBoundary.records_selected_source_boundary",
       "SFTAATFundamentalModularity.AATSupportedSFTBoundary.records_selected_horizon_boundary",
       "SFTAATFundamentalModularity.AATSupportedSFTBoundary.records_aat_projection_boundary",
       "SFTAATFundamentalModularity.AATSupportedSFTBoundary.records_aat_observation_boundary",
       "SFTAATFundamentalModularity.AATSupportedSFTBoundary.records_aat_reconstruction_boundary",
       "SFTAATFundamentalModularity.AATSupportedSFTBoundary.records_aat_missingEvidence_boundary",
       "SFTAATFundamentalModularity.AATSupportedSFTBoundary.preserves_nonConclusions",
       "SFTAATFundamentalModularity.AATSupportedSFTBoundary.records_report_and_theorem_status_boundaries",
       "SFTAATFundamentalModularity.AATSupportedSFTBoundary.constructor_preserves_nonConclusions",
       "SFTAATFundamentalModularity.AATSFTBoundaryFailure",
       "SFTAATFundamentalModularity.AATSFTBoundaryFailure.toTypedComputationBoundaryFailure",
       "SFTAATFundamentalModularity.AATSFTBoundaryFailure.toAATTypedComputationBoundaryFailure",
       "SFTAATFundamentalModularity.AATSupportedFundamentalModularityPackage",
       "SFTAATFundamentalModularity.AATSupportedFundamentalModularityPackage.ofBoundaryAndFiniteSelectedHypotheses",
       "SFTAATFundamentalModularity.AATSupportedFundamentalModularityPackage.ExplicitAssumptionLedger",
       "SFTAATFundamentalModularity.AATSupportedFundamentalModularityPackage.explicitAssumptionLedger",
       "SFTAATFundamentalModularity.AATSupportedFundamentalModularityPackage.explicitAssumptionLedger_supports_final_typed_conclusion",
       "SFTAATFundamentalModularity.AATSupportedFundamentalModularityPackage.explicitAssumptionLedger_supports_nonConclusion_boundary",
       "SFTAATFundamentalModularity.AATSupportedFundamentalModularityPackage.finiteSelected_fundamental_modularity",
       "SFTAATFundamentalModularity.AATSupportedFundamentalModularityPackage.governed_or_typed_boundary_failure",
       "SFTAATFundamentalModularity.AATSupportedFundamentalModularityPackage.finite_failure_enters_final_typed_conclusion",
       "SFTAATFundamentalModularity.AATSupportedFundamentalModularityPackage.final_typed_conclusion_records_finite_or_aat_failure_taxonomy",
       "SFTAATFundamentalModularity.AATSupportedFundamentalModularityPackage.governed_or_finite_failure_or_aat_boundary_failure",
       "SFTAATFundamentalModularity.AATSupportedFundamentalModularityPackage.aat_boundary_failure_enters_final_typed_conclusion",
       "SFTAATFundamentalModularity.AATSupportedFundamentalModularityPackage.final_failure_taxonomy_preserves_nonConclusions",
       "SFTAATFundamentalModularity.AATSupportedFundamentalModularityPackage.modularity_iff_forecastConeDescent",
       "SFTAATFundamentalModularity.AATSupportedFundamentalModularityPackage.does_not_promote_to_unconditional_claim",
       "SFTAATFundamentalModularity.AATSupportedFundamentalModularityPackage.LifecycleTypedFailureSidecar",
       "SFTAATFundamentalModularity.AATSupportedFundamentalModularityPackage.lifecycleTypedFailureSidecar_of_threshold",
       "SFTAATFundamentalModularity.AATSupportedFundamentalModularityPackage.AllowedGrandTheoremTransformation",
       "SFTAATFundamentalModularity.AATSupportedFundamentalModularityPackage.EvolutionaryConclusionPreservation",
       "SFTAATFundamentalModularity.AATSupportedFundamentalModularityPackage.evolutionaryConclusionPreservation_of_allowedTransformation",
       "SFTAATFundamentalModularity.Examples.canonicalFiniteSelectedDescentPackage",
       "SFTAATFundamentalModularity.Examples.canonicalDescentComponent",
       "SFTAATFundamentalModularity.Examples.canonicalObstructionPackage",
       "SFTAATFundamentalModularity.Examples.canonicalObstructionComponent",
       "SFTAATFundamentalModularity.Examples.canonicalObstructionGovernancePackage",
       "SFTAATFundamentalModularity.Examples.canonicalGovernanceComponent",
       "SFTAATFundamentalModularity.Examples.canonicalAATSupportedBoundary",
       "SFTAATFundamentalModularity.Examples.canonicalGeneratedAATSupportedBoundary",
       "SFTAATFundamentalModularity.Examples.canonicalGeneratedAATSupportedBoundary_aatStatus_eq_generated",
       "SFTAATFundamentalModularity.Examples.canonicalGeneratedAATSupportedBoundary_reads_generated_status_as_local_premise",
       "SFTAATFundamentalModularity.Examples.artifactDerivedReportBoundary",
       "SFTAATFundamentalModularity.Examples.canonicalArtifactSupportedBoundary",
       "SFTAATFundamentalModularity.Examples.canonicalArtifactSupportedFundamentalModularityPackage",
       "SFTAATFundamentalModularity.Examples.canonicalArtifactSupported_final_typed_conclusion",
       "SFTAATFundamentalModularity.Examples.canonicalArtifactSupported_preserves_nonConclusions",
       "SFTAATFundamentalModularity.Examples.canonicalAATSupportedFundamentalModularityPackage",
       "SFTAATFundamentalModularity.Examples.canonicalGeneratedAATSupportedFundamentalModularityPackage",
       "SFTAATFundamentalModularity.Examples.canonicalGeneratedAATSupported_final_typed_conclusion",
       "SFTAATFundamentalModularity.Examples.canonicalGeneratedAATSupported_preserves_nonConclusions",
       "SFTAATFundamentalModularity.Examples.canonicalAATSupported_fundamental_modularity",
       "SFTAATFundamentalModularity.Examples.canonicalAATSupported_governed_or_typed_boundary_failure",
       "SFTAATFundamentalModularity.Examples.canonicalAATSupported_final_typed_conclusion",
       "SFTAATFundamentalModularity.Examples.canonicalAATSupported_preserves_nonConclusions",
       "SFTAATFundamentalModularity.Examples.nonSingletonExactModel",
       "SFTAATFundamentalModularity.Examples.nonSingletonExactModel_has_two_global_points",
       "SFTAATFundamentalModularity.Examples.nonSingletonAATSupportedFundamentalModularityPackage",
       "SFTAATFundamentalModularity.Examples.nonSingletonAATSupported_final_typed_conclusion",
       "SFTAATFundamentalModularity.Examples.nonSingletonAATSupported_preserves_nonConclusions"]

/--
Schematic-name to Lean-API correspondences for SFT Part III / IV.

These rows are metadata only. They stabilize how SFT statements are read
against existing bounded Lean APIs without turning empirical or tooling claims
into Lean theorem claims.
-/
def schematicCorrespondences : Candidate -> List SchematicCorrespondence
  | softwareFieldProjection =>
      [{ schematic := "SoftwareField -> ArchitectureObject projection",
         leanDeclarations :=
          ["SoftwareField.arch",
           "SoftwareFieldEstimate.arch",
           "ArchitectureProjectionBoundary.projection_eq_selected_arch"],
         reading :=
          "selected field estimate has a one-way architecture projection boundary",
         status := "defined only / proved accessors" },
       { schematic :=
          "GeneratedArchitectureObject -> SoftwareFieldEstimate projection",
         leanDeclarations :=
          ["AtomGeneratedSignatureExamples.atomGeneratedSignature_generatedSoftwareField",
           "AtomGeneratedSignatureExamples.atomGeneratedSignature_generatedSoftwareFieldEstimate",
           "AtomGeneratedSignatureExamples.atomGeneratedSignature_generatedArchitectureProjectionBoundary",
           "AtomGeneratedSignatureExamples.atomGeneratedSignature_generatedSoftwareField_projects_to_generated",
           "AtomGeneratedSignatureExamples.atomGeneratedSignature_generatedSoftwareField_records_nonConclusions"],
         reading :=
          "Atom-generated carriers instantiate the selected SoftwareField and SoftwareFieldEstimate projection boundary to the generated flatness model while retaining field/non-conclusion boundaries",
         status := "proved acceptance" }]
  | forecastConeCore =>
      [{ schematic := "ForecastCone support relation source horizon target path",
         leanDeclarations :=
          ["ForecastCone",
           "ForecastCone.length_le_horizon",
           "ForecastCone.nil_mem",
           "ForecastCone.monotone_horizon"],
         reading :=
          "bounded finite field-path membership under selected support and step relation",
         status := "defined only / proved accessors" },
       { schematic :=
          "GeneratedArchitectureObject support package -> ForecastCone witness",
         leanDeclarations :=
          ["AtomGeneratedSignatureExamples.atomGeneratedSignature_sftSupportSafetyPackage",
           "AtomGeneratedSignatureExamples.atomGeneratedSignature_generatedForecastCone_mem",
           "AtomGeneratedSignatureExamples.atomGeneratedSignature_generatedForecastCone_length_le_horizon",
           "AtomGeneratedSignatureExamples.atomGeneratedSignature_generatedForecastCone_monotone_succ"],
         reading :=
          "the Atom-generated support-safety package yields a concrete generated carrier field path with a bounded ForecastCone witness and monotone horizon theorem",
         status := "proved acceptance" }]
  | coneProjection =>
      [{ schematic := "support inclusion projects cone membership",
         leanDeclarations :=
          ["ForecastConeProjection.forecastCone_projects_of_supportInclusion",
           "ForecastConeProjection.exists_projected_forecastCone_of_supportInclusion",
           "ForecastConeProjection.forecastCone_projects_of_supportInclusion_and_horizon_le"],
         reading :=
          "same-relation support monotonicity with projected finite path witness",
         status := "proved" },
       { schematic :=
          "Generated ForecastCone witness projects through generated support inclusion",
         leanDeclarations :=
          ["AtomGeneratedSignatureExamples.atomGeneratedSignature_supportSelfInclusion",
           "AtomGeneratedSignatureExamples.atomGeneratedSignature_generatedForecastCone_projects_self",
           "AtomGeneratedSignatureExamples.atomGeneratedSignature_exists_projected_generatedForecastCone",
           "AtomGeneratedSignatureExamples.atomGeneratedSignature_generatedForecastCone_projects_horizon_succ"],
         reading :=
          "the generated carrier ForecastCone witness is projected through generated self-inclusion with the projected path and horizon-extension evidence exposed",
         status := "proved acceptance" }]
  | artifactAction =>
      [{ schematic := "artifact action induces candidate update and after-action cone",
         leanDeclarations :=
          ["ArtifactAction.CandidateUpdate",
           "ArtifactAction.AppliesTo",
           "ForecastConeFamilyAfterAction.candidate_member",
           "ForecastConeFamilyAfterAction.applies_to_updatedField"],
         reading :=
          "artifact-mediated change records candidate and applied target boundaries",
         status := "defined only / proved accessors" },
       { schematic :=
          "GeneratedSFTInput -> ArtifactAction after-action cone",
         leanDeclarations :=
          ["AtomGeneratedSignatureExamples.atomGeneratedSignature_artifactAction",
           "AtomGeneratedSignatureExamples.atomGeneratedSignature_deterministicArtifactAction",
           "AtomGeneratedSignatureExamples.atomGeneratedSignature_forecastConeAfterArtifact",
           "AtomGeneratedSignatureExamples.atomGeneratedSignature_forecastConeAfterArtifact_candidate_member",
           "AtomGeneratedSignatureExamples.atomGeneratedSignature_forecastConeAfterArtifact_length_le_horizon"],
         reading :=
          "the Atom-generated SFT input acts as a generated artifact whose deterministic keep-carrier update preserves the generated ForecastCone witness after the action",
         status := "proved acceptance" }]
  | operationPolicyGovernance =>
      [{ schematic := "restrictive governance narrows support",
         leanDeclarations :=
          ["GovernanceIntervention.restrictive_supportInclusion",
           "GovernanceIntervention.restrictive_forecastCone_projects",
           "GovernanceIntervention.policy_pass_does_not_discharge_lawfulness"],
         reading :=
          "restrictive support transformation preserves projected cone membership but not lawfulness",
         status := "proved accessors" },
       { schematic :=
          "Generated support policy/governance projects generated ForecastCone",
         leanDeclarations :=
          ["AtomGeneratedSignatureExamples.atomGeneratedSignature_generatedOperationPolicy",
           "AtomGeneratedSignatureExamples.atomGeneratedSignature_generatedGovernanceIntervention",
           "AtomGeneratedSignatureExamples.atomGeneratedSignature_generatedGovernance_restrictive",
           "AtomGeneratedSignatureExamples.atomGeneratedSignature_generatedGovernance_projects_forecastCone",
           "AtomGeneratedSignatureExamples.atomGeneratedSignature_generatedGovernance_keeps_nonConclusion"],
         reading :=
          "the Atom-generated support package instantiates before/after policies and a restrictive governance intervention whose cone projection and policy-pass non-conclusion are proved",
         status := "proved acceptance" }]
  | stableRegionReachability =>
      [{ schematic := "MayReach / MustReach / StableRegion / ReachablePreimage",
         leanDeclarations :=
          ["MayReach.of_forecastCone",
           "MustReach.mayReach",
           "StableRegion.forecastCone_target",
           "ReachablePreimage.iff_mayReach"],
         reading :=
          "selected finite-cone reachability and stable-region closure vocabulary",
         status := "defined only / proved accessors" },
       { schematic :=
          "Generated ForecastCone witness -> generated reachability region",
         leanDeclarations :=
          ["AtomGeneratedSignatureExamples.atomGeneratedSignature_generatedFieldRegion",
           "AtomGeneratedSignatureExamples.atomGeneratedSignature_generatedStableRegion",
           "AtomGeneratedSignatureExamples.atomGeneratedSignature_generatedMayReach",
           "AtomGeneratedSignatureExamples.atomGeneratedSignature_generatedMustReach",
           "AtomGeneratedSignatureExamples.atomGeneratedSignature_generatedReachablePreimage"],
         reading :=
          "the Atom-generated support-safety ForecastCone witness instantiates selected may-reach, must-reach, stable-region, and reachable-preimage accessors over generated carriers",
         status := "proved acceptance" }]
  | supportSafety =>
      [{ schematic := "supported accepted trajectory stays in selected safe region",
         leanDeclarations :=
          ["SFTSupportSafetyPackage.AcceptedSupportedTrajectory.mem_forecastCone",
           "SFTSupportSafetyPackage.AcceptedSupportedTrajectory.supportSafety_preserves_forecastTrajectory",
           "SFTSupportSafetyPackage.AcceptedSupportedTrajectory.forecastCone_and_supportSafety"],
         reading :=
          "support-preservation premise yields selected trajectory safety and cone membership",
         status := "proved under package assumptions" },
       { schematic :=
          "GeneratedArchitectureObject -> SFTSupportSafetyPackage",
         leanDeclarations :=
          ["AtomGeneratedSignatureExamples.atomGeneratedSignature_sftSupportSafetyPackage",
           "AtomGeneratedSignatureExamples.atomGeneratedSignature_acceptedSupportedTrajectory",
           "AtomGeneratedSignatureExamples.atomGeneratedSignature_supportSafety_forecastCone_and_safety"],
         reading :=
          "Atom-generated carriers instantiate the selected support-safety package with a generated identity support operation and a finite accepted supported trajectory",
         status := "proved acceptance" }]
  | fieldUpdate =>
      [{ schematic := "observed feedback is preserved into posterior field record",
         leanDeclarations :=
          ["FieldUpdate.UpdateSound.fieldUpdate_preserves_forecastError_and_missingEvidence",
           "FieldUpdate.UpdateSound.fieldUpdate_preserves_unexpectedWitness_and_policyDrift",
           "FieldUpdate.UpdateSound.fieldUpdate_records_calibrationBoundary"],
         reading :=
          "selected update soundness preserves recorded feedback without claiming accuracy improvement",
         status := "proved accessors" }]
  | consequenceEnvelope =>
      [{ schematic := "cone family projects to consequence envelope",
         leanDeclarations :=
          ["EnvelopeProjection.envelope_records_selectedConeCount",
           "EnvelopeProjection.envelope_preserves_missingBoundary",
           "EnvelopeProjection.envelope_preserves_theoremBoundary",
           "EnvelopeProjection.envelope_does_not_strengthen_forecast_claim",
           "GeneratedAATConsequenceEnvelope",
           "GeneratedAATConsequenceEnvelope.to_premisedEnvelope",
           "GeneratedAATConsequenceEnvelope.theorem_status_from_generated",
           "GeneratedAATConsequenceEnvelope.records_transition_boundaries",
           "GeneratedAATConsequenceEnvelope.forecast_correctness_remains_boundary",
           "GeneratedAATConsequenceEnvelope.records_envelope_boundaries",
           "AATCorePremisedConsequenceEnvelope.records_envelope_boundaries",
           "AATCorePremisedConsequenceEnvelope.aatcore_premise_does_not_prove_forecast_correctness"],
         reading :=
          "loss-aware report projection preserving missing/theorem/forecast boundaries and generated AAT transition premises",
         status := "proved accessors" }]
  | aatInterfaceBoundary =>
      [{ schematic := "AAT theorem status is only an SFT local premise",
         leanDeclarations :=
          ["AAT.GeneratedSFTInput.theoremStatus",
           "AAT.GeneratedSFTInput.theoremStatusFromGenerated",
           "AAT.GeneratedSFTInput.measured_zero_from_generated",
           "AAT.GeneratedSFTInput.reads_generated_aat_as_sft_local_premise",
           "AAT.GeneratedSFTInput.sft_event_does_not_create_atoms",
           "AAT.GeneratedArchitectureLawModel.generatedIdentityAATCoreCircuitDelta",
           "AAT.GeneratedArchitectureLawModel.generatedIdentityAATCoreCircuitDelta_circuitBoundary",
           "AAT.GeneratedArchitectureLawModel.generatedIdentityAATCoreCircuitDelta_doesNotCreateAtoms",
           "AATToSFTInterfaceBoundary.aat_theorem_status_as_local_premise",
           "AATToSFTInterfaceBoundary.aat_lawfulness_alone_does_not_discharge_trajectory_safety_boundary",
           "AATToSFTInterfaceBoundary.measured_zero_does_not_discharge_unmeasured_axis_safety_boundary",
           "AATCoreLocalAlgebraForSFT.reads_aatcore_as_local_algebra",
           "AATCoreTransition.operation_does_not_create_atoms",
           "AATCoreTransportTransition.operation_does_not_create_atoms",
           "AATCoreTransportCircuitDelta.transport_circuit_delta_does_not_create_atoms"],
         reading :=
          "Atom-generated theorem status and generated AATCore circuit delta evidence are read as local algebra or local premise; transport circuit deltas keep source and target law/molecule selections separate and do not automatically promote to forecast safety",
         status := "proved accessors" }]
  | archSigReportBoundary =>
      [{ schematic := "ArchSig report reads as SFT estimate/status boundary",
         leanDeclarations :=
          ["ArchSigSFTReportEstimateBoundary.estimate_eq_report_estimate",
           "ArchSigSFTReportEstimateBoundary.report_preserves_theoremBoundary",
           "ArchSigSFTReportEstimateBoundary.report_preserves_forecastBoundary",
           "ArchSigSFTReportEstimateBoundary.report_preserves_nonConclusions",
           "FieldSigAATCoreTransitionAnalysis.fieldsig_reads_archsig_transition_as_sft_analysis",
           "FieldSigAATCoreTransitionAnalysis.forecast_correctness_remains_boundary",
           "GeneratedArchSigAATCoreTransition.ofTransition",
           "GeneratedArchSigAATCoreTransition.generatedArchSigDoesNotDefineAAT_recorded",
           "GeneratedArchSigAATCoreTransition.generatedFieldSigAnalysisBoundary_recorded",
           "GeneratedArchSigAATCoreTransition.generatedUnknownRejectedUnmeasuredSeparated_recorded",
           "GeneratedArchSigAATCoreTransition.source_bridge_architectureLawful",
           "GeneratedArchSigAATCoreTransition.target_bridge_architectureLawful",
           "GeneratedFieldSigAATCoreTransitionAnalysis.fieldsig_reads_generated_archsig_transition_as_sft_analysis",
           "GeneratedFieldSigAATCoreTransitionAnalysis.forecast_correctness_remains_boundary",
           "GeneratedArchSigAATCoreTransportTransition.ofTransportTransition",
           "GeneratedArchSigAATCoreTransportTransition.generatedArchSigDoesNotDefineAAT_recorded",
           "GeneratedArchSigAATCoreTransportTransition.generatedFieldSigAnalysisBoundary_recorded",
           "GeneratedArchSigAATCoreTransportTransition.generatedUnknownRejectedUnmeasuredSeparated_recorded",
           "GeneratedArchSigAATCoreTransportTransition.source_bridge_architectureLawful",
           "GeneratedArchSigAATCoreTransportTransition.target_bridge_architectureLawful",
           "GeneratedFieldSigAATCoreTransportTransitionAnalysis.fieldsig_reads_generated_archsig_transport_transition_as_sft_analysis",
           "GeneratedFieldSigAATCoreTransportTransitionAnalysis.forecast_correctness_remains_boundary",
           "AtomGeneratedSignatureExamples.atomGeneratedSignature_transport_target_molecule_is_distinct"],
         reading :=
          "tool report output and generated AATCore preservation / non-identity transport transition analysis preserve selected SFT boundaries without caller-supplied Signature bridge or generated handoff boundary fields, and without forecast claim promotion",
         status := "proved accessors" }]
  | counterexamplePackage =>
      [{ schematic := "SFT forbidden readings have canonical counterexample entrypoints",
         leanDeclarations :=
          ["SFTCounterexamples.endpoint_safe_zero_delta_not_path_safe",
           "SFTCounterexamples.accepted_preservation_not_support_preservation",
           "SFTCounterexamples.same_observed_signature_different_future_trajectory",
           "SFTCounterexamples.coarse_safe_not_refined_hidden_axis_safe"],
         reading :=
          "existing finite counterexamples indexed as SFT-native non-conclusion witnesses",
         status := "proved wrappers" }]
  | theoremRoadmap =>
      [{ schematic := "ForecastCone Descent / Modularity / Grand SFT roadmap",
         leanDeclarations :=
          ["ClockedForecastCone",
           "BoundedClockedForecastCone",
           "ClockedForecastCone.length_eq_horizon",
           "clockedForecastCone_of_forecastCone",
           "BinaryFieldCover",
           "BinarySFTModel.projectClockedForecastCone_left",
           "BinarySFTModel.projectClockedForecastCone_right",
           "BinarySFTModel.projectClockedStepPairCompatible",
           "BinarySFTModel.projectedClockedPaths_tickwiseCompatible",
           "CompatibleBinaryClockedConeFamily",
           "BinaryClockedStepGluingData",
           "glueCompatibleLocalClockedPath",
           "glueCompatibleBinaryClockedConeFamily",
           "BinaryProjectionGluingLaws",
           "projected_glued_target_related",
           "glued_projected_target_related",
           "GlobalConePointPathEquivalenceData",
           "LocalFamilyPathEquivalenceData",
           "BinaryProjectionGluingPathLaws",
           "BinaryProjectionGluingPathLaws.toEndpointLaws",
           "BinaryProjectionGluingPathLaws.glue_project_after_projection_endpoint",
           "BinaryProjectionGluingPathLaws.project_after_glue_endpoint",
           "UniformFiniteFieldCover",
           "Cech0Simplex",
           "Cech1Simplex",
           "Cech2Simplex",
           "FiniteSFTModel",
           "FiniteLocalClockedConeFamily",
           "FiniteClockedGluingData",
           "FiniteProjectionGluingLaws",
           "forecastCone_descent_finite_of_laws",
           "FiniteSelectedForecastConeDescentPackage.ofLaws",
           "finiteForecastConeDescentPackage_of_laws",
           "finiteCoverOfBinaryCover",
           "FiniteCechDescentCohomologyBridge",
           "SFTTheoremRoadmap.finiteForecastConeDescent_of_laws",
           "FiniteDescentFailureKind",
           "FiniteDescentFailure",
           "FiniteObstructionClass",
           "FiniteDescentObstructionPayload",
           "FiniteDescentObstructionClassifier",
           "FiniteDescentObstructionClassifier.classified_failureKind_eq",
           "FiniteDescentObstructionClassifier.classified_payload_failureKind_eq",
           "finite_descent_obstruction_of_classified_failure_sound",
           "FiniteDescentObstructionPackage",
           "finite_descent_obstruction_of_failure",
           "finite_descent_obstruction_of_failure_sound",
           "FiniteExactFailureClassifierCompleteness",
           "finiteExact_failure_classifier_complete",
           "CechCocycleObstruction",
           "FiniteCechTypedObstructionBridge",
           "typed_obstruction_of_cech_cocycle_obstruction",
           "FiniteCechObstructionBridge",
           "FiniteObstructionReviewProjection",
           "FiniteGovernanceCutTarget",
           "FiniteGovernanceCuttingPackage",
           "finite_governance_cuts_bad_obstruction",
           "finite_governance_preserves_desired_family",
           "FiniteObstructionGovernancePackage",
           "governance_cuts_obstruction_of_finite_failure",
           "SFTTheoremRoadmap.finite_governance_cuts_obstruction_of_failure",
           "BinaryProjectionGluingEquivalenceLaws",
           "BinaryProjectionGluingEquivalenceLaws.ofEndpointLaws",
           "BinaryDescentAssumptions.ofStepGluing",
           "BinaryDescentAssumptions.ofEndpointLaws",
           "forecastCone_descent_binary_of_endpoint_laws",
           "binaryForecastConeDescentPackage_of_endpoint_laws",
           "forecastCone_descent_binary_of_path_laws",
           "BinarySelectedForecastConeDescentPackage.ofPathLaws",
           "binaryForecastConeDescentPackage_of_path_laws",
           "forecastCone_descent_binary",
           "binaryForecastConeDescentPackage_of_assumptions",
           "SFTTheoremRoadmap.binaryForecastConeDescent_of_path_laws",
           "SFTTheoremRoadmap.ClockedForecastConeDescentPackage.forecastCone_descent",
           "SFTTheoremRoadmap.BinaryForecastConeDescentPackage.forecastCone_binary_descent",
           "SFTTheoremRoadmap.ModularityRepresentationPackage.modularity_representation",
           "SFTTheoremRoadmap.FundamentalModularityTheoremPackage.fundamental_modularity"],
         reading :=
          "roadmap-scale SFT theorems are implemented as explicit theorem-package surfaces over exact shared-clock cones; binary local-to-global path gluing is constructed from step gluing data, selected inverse laws can be instantiated from endpoint projection/glue laws or selected path-level inverse laws, finite-cover descent has a Cech-style selected skeleton under explicit gluing laws, and selected finite descent failures can be bridged to typed obstruction witnesses and governance cutting assumptions",
         status := "defined only / proved accessors under package assumptions" },
       { schematic := "Descent obstruction / cohomology / normal form / observation / envelope",
         leanDeclarations :=
          ["SFTTheoremRoadmap.DescentFailureKind",
           "SFTTheoremRoadmap.DescentObstructionWitness",
           "SFTTheoremRoadmap.DescentObstructionPackage.descent_obstruction_of_injectivity_failure",
           "SFTTheoremRoadmap.ConeCohomologyPackage.h1_zero_iff_local_futures_glue",
           "SFTTheoremRoadmap.EvolutionaryNormalFormPackage.evolutionary_normal_form",
           "SFTTheoremRoadmap.not_coneConservative_of_observationCollapse",
           "SFTTheoremRoadmap.MinimalConsequenceEnvelopePackage.minimal_consequenceEnvelope_factors",
           "SFTTheoremRoadmap.minimalConsequenceEnvelopePackageOfDecisionEquivalence",
           "SFTTheoremRoadmap.MinimalConsequenceEnvelopePackage.minimal_consequenceEnvelope_factor_unique_on_image",
           "SFTTheoremRoadmap.ObstructionAwareReviewEquivalence",
           "SFTFundamentalModularity.reviewComponent_records_obstructionAware_minimalEnvelope"],
         reading :=
          "local-to-global failure, cohomology, normal forms, observation adequacy, and minimal envelopes are recorded as bounded theorem surfaces",
         status := "defined only / proved accessors under package assumptions" },
       { schematic := "Modular attractor / governance / calibration / Yoneda / confluence / lifecycle / fixed point / invariance",
         leanDeclarations :=
          ["SFTTheoremRoadmap.ModularAttractorPackage.modular_attractor",
           "SFTTheoremRoadmap.GovernanceSynthesisPackage.governance_synthesis",
           "SFTTheoremRoadmap.FiniteGovernanceSynthesisBridge.obstructionGovernancePackage",
           "SFTFundamentalModularity.governanceComponent_records_synthesis_cut",
           "SFTTheoremRoadmap.FiniteHeightClosedLoopCalibrationBridge.finiteHeight_closedLoopCalibration_fixedPoint_or_boundary",
           "SFTFundamentalModularity.calibrationComponent_records_finiteHeight_fixedPointOrBoundary",
           "SFTTheoremRoadmap.ClosedLoopCalibrationPackage.closedLoop_calibration_fixedPoint_or_boundary",
           "SFTTheoremRoadmap.ArtifactYonedaPackage.artifact_yoneda",
           "SFTTheoremRoadmap.AgenticConfluencePackage.agentic_confluence",
           "SFTAgenticConfluence.NewmanStyleConfluenceKernel.newmanStyle_fairInterleavingsConverge",
           "SFTFundamentalModularity.agenticComponent_records_newmanStyle_confluence",
           "SFTFundamentalModularity.agenticComponent_records_finiteTeam_confluence",
           "SFTTheoremRoadmap.LifecycleBifurcationPackage.lifecycle_bifurcation_above_threshold",
           "SFTTheoremRoadmap.FieldShapingFixedPointPackage.fieldShaping_fixedPoints",
           "SFTAATFundamentalModularity.AATSupportedFundamentalModularityPackage.FieldShapingConclusionSidecar",
           "SFTTheoremRoadmap.EvolutionaryInvariancePackage.evolutionary_invariance"],
         reading :=
          "engineering-surface and closed-loop roadmap theorem families are available as checked theorem-package entrypoints",
         status := "defined only / proved accessors under package assumptions" }]
  | finiteExactModel =>
      [{ schematic := "FiniteExactSFTModel selected finite proof universe",
         leanDeclarations :=
          ["FiniteExactSFTModel",
           "FiniteExactSFTModel.exactCover",
           "FiniteExactSFTModel.descentModel",
           "FiniteExactSFTModel.RecordsExactCoverBoundary",
           "FiniteExactSFTModel.RecordsFiniteModelBoundary",
           "FiniteExactSFTModel.RecordsExtractorEmpiricalBoundary",
           "FiniteExactSFTModel.RecordsNonConclusions",
           "FiniteExactDescentAssumptions",
           "finiteExactForecastConeDescentPackage_of_assumptions",
           "CechCone0",
           "CechCone1",
           "IsCechConeCocycle",
           "IsCechConeCoboundary",
           "cechConeCocycle_of_finiteLocalFamily",
           "CechConeH1Vanishes",
           "h1_vanishes_implies_finite_descent",
           "h1_vanishes_selected_finite_descent_bridge"],
         reading :=
         "selected finite universe, exact cover, operation support, observation boundary, and governance basis are packaged for downstream assumption-discharge theorems; explicit gluing laws yield a selected finite descent package; concrete Cech cone cochains connect the finite simplex skeleton to cocycle/coboundary predicates and selected H1 vanishing implies selected finite descent under explicit finite exact assumptions",
         status := "defined only / proved accessor under explicit assumptions" }]
  | aatSupportedFundamentalModularity =>
      [{ schematic := "AAT-supported finite selected Fundamental Modularity",
         leanDeclarations :=
         ["SFTAATFundamentalModularity.AATSupportedSFTBoundary",
           "SFTAATFundamentalModularity.AATSelectedArchitectureSlice.ArchMapDerivedAATSliceBoundary",
           "SFTAATFundamentalModularity.AATSelectedArchitectureSlice.ofArchMapObservationBoundary",
           "SFTAATFundamentalModularity.ArchSigDerivedSFTReportBoundary",
           "SFTAATFundamentalModularity.AATSupportedSFTBoundary.ofSelectedSliceAndFiniteExactModel",
           "SFTAATFundamentalModularity.AATSupportedSFTBoundary.ofGeneratedSFTInputAndArchSigTransition",
           "SFTAATFundamentalModularity.AATSupportedSFTBoundary.ofArchMapAndArchSigBoundaries",
           "SFTAATFundamentalModularity.AATSupportedSFTBoundary.aat_status_as_sft_local_premise",
           "SFTAATFundamentalModularity.AATSupportedSFTBoundary.ofGeneratedSFTInputAndArchSigTransition_records_archsig_boundary",
           "SFTAATFundamentalModularity.AATSupportedSFTBoundary.ofGeneratedSFTInputAndArchSigTransition_records_theorem_boundary",
           "SFTAATFundamentalModularity.AATSupportedSFTBoundary.ofGeneratedSFTInputAndArchSigTransition_records_typed_failure_boundary",
           "SFTAATFundamentalModularity.AATSupportedSFTBoundary.records_report_and_theorem_status_boundaries",
           "SFTAATFundamentalModularity.AATSupportedSFTBoundary.constructor_preserves_nonConclusions",
           "SFTAATFundamentalModularity.AATSFTBoundaryFailure.ofKind",
           "SFTAATFundamentalModularity.AATSFTBoundaryFailure.toTypedComputationBoundaryFailure",
           "SFTAATFundamentalModularity.AATSFTBoundaryFailure.toAATTypedComputationBoundaryFailure",
           "SFTFundamentalModularity.FiniteExactQuantifiedFundamentalModularityTheorem",
           "SFTFundamentalModularity.FiniteExactQuantifiedFundamentalModularityTheorem.selected_fundamental_modularity",
           "SFTAATFundamentalModularity.AATSupportedFundamentalModularityPackage.ofBoundaryAndFiniteSelectedHypotheses",
           "SFTAATFundamentalModularity.AATSupportedFundamentalModularityPackage.governed_or_typed_boundary_failure",
           "SFTAATFundamentalModularity.AATSupportedFundamentalModularityPackage.governed_or_finite_failure_or_aat_boundary_failure",
           "SFTAATFundamentalModularity.AATSupportedFundamentalModularityPackage.aat_boundary_failure_enters_final_typed_conclusion",
           "SFTAATFundamentalModularity.AATSupportedFundamentalModularityPackage.modularity_iff_forecastConeDescent",
           "SFTAATFundamentalModularity.AATSupportedFundamentalModularityPackage.does_not_promote_to_unconditional_claim",
           "SFTAATFundamentalModularity.Examples.canonicalFiniteSelectedDescentPackage",
           "SFTAATFundamentalModularity.Examples.canonicalObstructionPackage",
           "SFTAATFundamentalModularity.Examples.canonicalObstructionGovernancePackage",
           "SFTAATFundamentalModularity.Examples.canonicalAATSupportedFundamentalModularityPackage",
           "SFTAATFundamentalModularity.Examples.canonicalArtifactSupportedFundamentalModularityPackage",
           "SFTAATFundamentalModularity.Examples.canonicalAATSupportedBoundary_reads_aat_status_as_local_premise",
           "SFTAATFundamentalModularity.Examples.canonicalGeneratedAATSupportedBoundary_records_archsig_transition_boundary",
           "SFTAATFundamentalModularity.Examples.canonicalGeneratedAATSupportedBoundary_records_generated_theorem_boundary",
           "SFTAATFundamentalModularity.Examples.canonicalGeneratedAATSupportedBoundary_records_typed_failure_boundary",
           "SFTAATFundamentalModularity.Examples.canonicalAATSupported_final_typed_conclusion",
           "SFTAATFundamentalModularity.Examples.canonicalArtifactSupported_final_typed_conclusion",
           "SFTAATFundamentalModularity.Examples.canonicalAATSupported_preserves_nonConclusions"],
         reading :=
          "AAT theorem status, selected architecture slice, finite exact model, selected source, and selected horizon are carried as explicit premises for the finite selected final assembly; generated SFT input plus generated ArchSig transition evidence can supply the AAT status, report boundary, theorem boundary, typed-failure boundary, and non-conclusion boundary without caller-filled report propositions; ArchMap preservation packages can be read as selected AAT slices and ArchSig report boundaries can be read as SFT report/forecast boundaries before constructing the AAT-supported boundary; singleton canonical examples instantiate generated, direct, and artifact-boundary AAT-supported packages end to end with descent, obstruction, and governance components routed through existing helper packages",
         status := "proved accessors and canonical example under explicit AAT/SFT boundary assumptions" }]

/-- Boundary reminder for reading each SFT candidate as a bounded package. -/
def nonConclusionBoundary : Candidate -> String
  | softwareFieldProjection =>
      "selected projection only; no full field model, reconstruction completeness, or extractor completeness"
  | forecastConeCore =>
      "bounded finite path membership only; no probability, calibration, causal proof, or global safety"
  | coneProjection =>
      "same-field support inclusion projection only; no risk-reduction or transition-kernel theorem"
  | artifactAction =>
      "candidate updates and after-action cones only; no unique future, market success, or intention model"
  | operationPolicyGovernance =>
      "selected support/policy transformation only; no lawfulness, governance effectiveness, or risk reduction"
  | stableRegionReachability =>
      "selected finite-cone reachability only; no global basin, convergence, recurrence, or calibrated prediction"
  | supportSafety =>
      "selected supported trajectory safety only; accepted evidence is not support preservation"
  | fieldUpdate =>
      "record preservation only; no posterior accuracy improvement or empirical calibration theorem"
  | consequenceEnvelope =>
      "loss-aware report projection only; no invertible cone reconstruction or forecast correctness"
  | aatInterfaceBoundary =>
      "AAT theorem status is a local premise only; no automatic SFT trajectory-safety promotion"
  | archSigReportBoundary =>
      "report-to-estimate boundary only; no ground-truth architecture, theorem package, or calibrated forecast"
  | counterexamplePackage =>
      "finite non-conclusion witnesses only; no empirical degradation, incident risk, or global forecast claim"
  | theoremRoadmap =>
      "roadmap theorem packages only; no unconditional global descent, calibration, governance effectiveness, AI safety, or extractor completeness"
  | finiteExactModel =>
      "selected finite proof universe only; no extractor completeness, empirical correctness, all-covers descent, or full Fundamental Modularity theorem"
  | aatSupportedFundamentalModularity =>
      "AAT-supported selected slice only; no assumption-free Grand Theorem, empirical correctness, operational effectiveness, global AI safety, or extractor completeness"

end Candidate

end SFTTheoremPackages

end Formal.Arch
