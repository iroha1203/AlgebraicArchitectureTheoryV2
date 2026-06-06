use serde::{Deserialize, Serialize};

use super::validation::ValidationCheck;

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct ArchSigAnalysisPacketV0 {
    pub schema_version: String,
    pub analysis_id: String,
    pub generated_at: String,
    pub arch_map_ref: ArchSigAnalysisArtifactRefV0,
    pub interpretation_profile_ref: ArchSigAnalysisArtifactRefV0,
    pub selected_law_policy_ref: ArchSigAnalysisArtifactRefV0,
    pub arch_map_store_refs: ArchSigArchMapStoreRefsV0,
    pub architecture_state: ArchSigArchitectureStateV0,
    pub design_pressure: Vec<ArchSigDesignPressureReadingV0>,
    pub change_impact: ArchSigChangeImpactReadingV0,
    pub aat_concept_surfaces: Vec<ArchSigAatConceptSurfaceV0>,
    pub atom_configuration_summary: ArchSigAtomConfigurationSummaryV0,
    pub architecture_object_projections: Vec<ArchSigArchitectureObjectProjectionV0>,
    pub invariant_family_readings: Vec<ArchSigInvariantFamilyReadingV0>,
    pub law_universe_reading: ArchSigLawUniverseReadingV0,
    pub molecule_readings: Vec<ArchSigMoleculeReadingV0>,
    #[serde(default)]
    pub generated_atom_shapes: Vec<ArchSigGeneratedAtomShapeV0>,
    #[serde(default)]
    pub generated_molecules: Vec<ArchSigGeneratedMoleculeV0>,
    #[serde(default)]
    pub generated_law_inputs: Vec<ArchSigGeneratedLawInputV0>,
    #[serde(default)]
    pub generated_obstructions: Vec<ArchSigGeneratedObstructionV0>,
    #[serde(default)]
    pub generated_repair_targets: Vec<ArchSigGeneratedRepairTargetV0>,
    #[serde(default)]
    pub viewer_distance_inputs: Vec<ArchSigViewerDistanceInputV0>,
    #[serde(default)]
    pub part4_distance_foundation: ArchSigPart4DistanceFoundationV0,
    #[serde(default)]
    pub atom_distance_readings: Vec<ArchSigAtomDistanceReadingV0>,
    #[serde(default)]
    pub configuration_distance_readings: Vec<ArchSigConfigurationDistanceReadingV0>,
    #[serde(default)]
    pub signature_distance_readings: Vec<ArchSigSignatureDistanceReadingV0>,
    #[serde(default)]
    pub operation_distance_readings: Vec<ArchSigOperationDistanceReadingV0>,
    #[serde(default)]
    pub obstruction_measure_readings: Vec<ArchSigObstructionMeasureReadingV0>,
    #[serde(default)]
    pub curvature_mass_readings: Vec<ArchSigCurvatureMassReadingV0>,
    pub obstruction_circuits: Vec<ArchSigObstructionCircuitV0>,
    pub signature_axes: Vec<ArchSigSignatureAxisReadingV0>,
    pub analytic_representations: Vec<ArchSigAnalyticRepresentationV0>,
    pub coupling_cohesion_readings: Vec<ArchSigCouplingCohesionReadingV0>,
    pub spectral_analysis_readings: Vec<ArchSigSpectralAnalysisReadingV0>,
    pub spectral_mode_readings: Vec<ArchSigSpectralModeReadingV0>,
    pub spectral_drilldown_readings: Vec<ArchSigSpectralDrilldownReadingV0>,
    #[serde(default)]
    pub curvature_support_readings: Vec<ArchSigCurvatureSupportReadingV0>,
    #[serde(default)]
    pub curvature_transfer_readings: Vec<ArchSigCurvatureTransferReadingV0>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub architecture_spectrum_report: Option<ArchSigArchitectureSpectrumReportV0>,
    pub transfer_bridge_readings: Vec<ArchSigTransferBridgeReadingV0>,
    #[serde(default)]
    pub atom_support_axis_readings: Vec<ArchSigAtomSupportAxisReadingV0>,
    #[serde(default)]
    pub atom_compatibility_readings: Vec<ArchSigAtomCompatibilityReadingV0>,
    #[serde(default)]
    pub law_universe_coverage_readings: Vec<ArchSigLawUniverseCoverageReadingV0>,
    #[serde(default)]
    pub feature_extension_formula_readings: Vec<ArchSigFeatureExtensionFormulaReadingV0>,
    #[serde(default)]
    pub operation_calculus_law_readings: Vec<ArchSigOperationCalculusLawReadingV0>,
    #[serde(default)]
    pub path_signature_trajectory_readings: Vec<ArchSigPathSignatureTrajectoryReadingV0>,
    #[serde(default)]
    pub homotopy_order_sensitivity_readings: Vec<ArchSigHomotopyOrderSensitivityReadingV0>,
    #[serde(default)]
    pub diagram_fillability_readings: Vec<ArchSigDiagramFillabilityReadingV0>,
    #[serde(default)]
    pub axis_forgetting_risk_readings: Vec<ArchSigAxisForgettingRiskReadingV0>,
    #[serde(default)]
    pub observation_projection_fidelity_readings:
        Vec<ArchSigObservationProjectionFidelityReadingV0>,
    #[serde(default)]
    pub atom_origin_closure_debt_readings: Vec<ArchSigAtomOriginClosureDebtReadingV0>,
    #[serde(default)]
    pub effect_relation_algebra_readings: Vec<ArchSigEffectRelationAlgebraReadingV0>,
    #[serde(default)]
    pub synthesis_blockage_readings: Vec<ArchSigSynthesisBlockageReadingV0>,
    #[serde(default)]
    pub operation_precondition_readiness_readings:
        Vec<ArchSigOperationPreconditionReadinessReadingV0>,
    #[serde(default)]
    pub path_multiplicity_loss_readings: Vec<ArchSigPathMultiplicityLossReadingV0>,
    #[serde(default)]
    pub signature_trajectory_homotopy_refutation_readings:
        Vec<ArchSigSignatureTrajectoryHomotopyRefutationReadingV0>,
    #[serde(default)]
    pub bridge_split_obstruction_transfer_readings:
        Vec<ArchSigBridgeSplitObstructionTransferReadingV0>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub homotopy_complex_summary: Option<ArchSigHomotopyComplexSummaryV0>,
    #[serde(default)]
    pub path_pair_candidates: Vec<ArchSigPathPairCandidateV0>,
    #[serde(default)]
    pub loop_candidates: Vec<ArchSigLoopCandidateV0>,
    #[serde(default)]
    pub filler_candidate_readings: Vec<ArchSigFillerCandidateReadingV0>,
    #[serde(default)]
    pub architectural_hole_readings: Vec<ArchSigArchitecturalHoleReadingV0>,
    #[serde(default)]
    pub homotopy_holonomy_readings: Vec<ArchSigHomotopyHolonomyReadingV0>,
    #[serde(default)]
    pub stokes_style_readings: Vec<ArchSigStokesStyleReadingV0>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub architecture_homotopy_report: Option<ArchSigArchitectureHomotopyReportV0>,
    #[serde(default)]
    pub homotopy_distance_readings: Vec<ArchSigHomotopyDistanceReadingV0>,
    pub operation_square_candidates: Vec<ArchSigOperationSquareCandidateV0>,
    pub path_continuation_traces: Vec<ArchSigPathContinuationTraceV0>,
    pub axis_wise_monodromy_defects: Vec<ArchSigAxisWiseMonodromyDefectV0>,
    pub ami_aggregate_readings: Vec<ArchSigAmiAggregateReadingV0>,
    pub nonzero_monodromy_witnesses: Vec<ArchSigNonzeroMonodromyWitnessV0>,
    pub feature_boundary_residual_readings: Vec<ArchSigFeatureBoundaryResidualReadingV0>,
    pub feature_extension_diagnosis_readings: Vec<ArchSigFeatureExtensionDiagnosisReadingV0>,
    pub monodromy_reading_family: ArchSigMonodromyReadingFamilyV0,
    pub boundary_holonomy_reading_family: ArchSigBoundaryHolonomyReadingFamilyV0,
    pub representation_strength_readings: Vec<ArchSigRepresentationStrengthReadingV0>,
    #[serde(default)]
    pub representation_metric_readings: Vec<ArchSigRepresentationMetricReadingV0>,
    pub local_curvature_diagram_readings: Vec<ArchSigLocalCurvatureDiagramReadingV0>,
    pub three_layer_flatness_readings: Vec<ArchSigThreeLayerFlatnessReadingV0>,
    pub observation_projection_readings: Vec<ArchSigObservationProjectionReadingV0>,
    pub state_transition_algebra_readings: Vec<ArchSigStateTransitionAlgebraReadingV0>,
    pub operation_invariant_galois_readings: Vec<ArchSigOperationInvariantGaloisReadingV0>,
    pub split_readiness_readings: Vec<ArchSigSplitReadinessReadingV0>,
    pub structural_reading_review_surface: ArchSigStructuralReadingReviewSurfaceV0,
    pub current_state_evolution_boundary: ArchSigCurrentStateEvolutionBoundaryV0,
    pub design_principle_readings: Vec<ArchSigDesignPrincipleReadingV0>,
    pub flatness_reading: ArchSigFlatnessReadingV0,
    pub static_runtime_semantic_layer_split: ArchSigLayerSplitV0,
    pub repair_operation_candidates: Vec<ArchSigRepairOperationCandidateV0>,
    pub operation_deltas: Vec<ArchSigOperationDeltaReadingV0>,
    pub path_homotopy_diagram_readings: Vec<ArchSigPathHomotopyDiagramReadingV0>,
    pub bounded_judgements: Vec<ArchSigBoundedJudgementV0>,
    #[serde(rename = "llmInterpretationPacket")]
    pub llm_interpretation_packet: ArchSigLlmInterpretationPacketV0,
    pub evidence_boundary: String,
    #[serde(rename = "interpretationNotesForLLM")]
    pub interpretation_notes_for_llm: Vec<String>,
    #[serde(default)]
    pub excluded_readings: Vec<String>,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigOperationSquareCandidateV0 {
    pub candidate_id: String,
    pub candidate_source: String,
    pub supplied_pair_ref: Option<String>,
    pub candidate_basis: Vec<String>,
    #[serde(default)]
    pub candidate_basis_refs: Vec<String>,
    pub left_operation_ref: String,
    pub right_operation_ref: String,
    pub p_path_ref: String,
    pub q_path_ref: String,
    #[serde(default)]
    pub p_operation_sequence: Vec<String>,
    #[serde(default)]
    pub q_operation_sequence: Vec<String>,
    #[serde(default)]
    pub endpoint_object_refs: Vec<String>,
    #[serde(default)]
    pub generator_candidate_refs: Vec<String>,
    pub shared_atom_support_refs: Vec<String>,
    pub state_refs: Vec<String>,
    pub effect_refs: Vec<String>,
    pub contract_refs: Vec<String>,
    pub semantic_refs: Vec<String>,
    pub authority_refs: Vec<String>,
    pub runtime_refs: Vec<String>,
    pub projection_refs: Vec<String>,
    pub source_refs: Vec<String>,
    pub observation_refs: Vec<String>,
    pub missing_refs: Vec<String>,
    pub evidence_boundary: String,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigPathContinuationTraceV0 {
    pub trace_id: String,
    pub candidate_ref: String,
    pub path_ref: String,
    pub path_role: String,
    pub path_expression: String,
    #[serde(default)]
    pub operation_sequence: Vec<String>,
    #[serde(default)]
    pub endpoint_object_refs: Vec<String>,
    #[serde(default)]
    pub continuation_step_refs: Vec<String>,
    pub axis_traces: Vec<ArchSigAxisContinuationTraceV0>,
    pub observation_refs: Vec<String>,
    pub source_refs: Vec<String>,
    pub missing_refs: Vec<String>,
    pub evidence_boundary: String,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigAxisContinuationTraceV0 {
    pub axis_family: String,
    pub axis_ref: String,
    pub trace_status: String,
    #[serde(default)]
    pub distance_evaluator_kind: String,
    pub continuation_summary: String,
    #[serde(default)]
    pub continuation_states: Vec<String>,
    #[serde(default)]
    pub comparable_continuation_values: Vec<String>,
    #[serde(default)]
    pub distance_input_refs: Vec<String>,
    pub observation_refs: Vec<String>,
    pub source_refs: Vec<String>,
    pub missing_refs: Vec<String>,
    pub unmeasured_boundary: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigAxisWiseMonodromyDefectV0 {
    pub defect_id: String,
    pub candidate_ref: String,
    pub axis_family: String,
    pub axis_ref: String,
    pub distance_kind: String,
    #[serde(default)]
    pub p_continuation_ref: String,
    #[serde(default)]
    pub q_continuation_ref: String,
    #[serde(default)]
    pub distance_input_refs: Vec<String>,
    #[serde(default)]
    pub positive_witness_boundary: String,
    #[serde(default)]
    pub weight: i64,
    pub measurement_status: String,
    pub distance_value: Option<i64>,
    pub measured_support_refs: Vec<String>,
    pub witness_refs: Vec<String>,
    pub source_refs: Vec<String>,
    pub observation_refs: Vec<String>,
    pub missing_refs: Vec<String>,
    pub coverage_boundary: String,
    pub exactness_assumption_status: Vec<String>,
    pub zero_reflection_assumptions: Vec<String>,
    pub cancellation_boundary: String,
    pub evidence_boundary: String,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigAmiAggregateReadingV0 {
    pub aggregate_id: String,
    pub selected_square_family: String,
    pub selected_axis_family: Vec<String>,
    #[serde(default)]
    pub selected_measured_square_refs: Vec<String>,
    pub weight_policy: String,
    pub distance_kind: String,
    pub measurement_status: String,
    pub aggregate_value: i64,
    pub measured_defect_refs: Vec<String>,
    pub unmeasured_defect_refs: Vec<String>,
    #[serde(default)]
    pub positive_weight_defect_refs: Vec<String>,
    #[serde(default)]
    pub zero_weight_defect_refs: Vec<String>,
    pub top_contributors: Vec<ArchSigAmiTopContributorV0>,
    pub zero_reflection_assumptions: Vec<String>,
    pub cancellation_boundary: String,
    pub aggregate_to_local_reading_boundary: String,
    pub review_priority: String,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigAmiTopContributorV0 {
    pub defect_ref: String,
    pub candidate_ref: String,
    pub axis_family: String,
    pub contribution_weight: i64,
    pub contribution_value: Option<i64>,
    pub review_focus: String,
    pub witness_refs: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigNonzeroMonodromyWitnessV0 {
    pub witness_id: String,
    pub defect_ref: String,
    pub candidate_ref: String,
    pub operation_pair: Vec<String>,
    pub path_pair: Vec<String>,
    pub axis_family: String,
    pub axis_ref: String,
    pub defect_value: i64,
    pub compared_trace_summary: Vec<String>,
    pub affected_atom_refs: Vec<String>,
    pub law_refs: Vec<String>,
    pub signature_axis_refs: Vec<String>,
    pub source_refs: Vec<String>,
    pub observation_refs: Vec<String>,
    pub missing_evidence: Vec<String>,
    pub coverage_boundary: String,
    pub suggested_filler_evidence: Vec<String>,
    pub suggested_lifting_evidence: Vec<String>,
    pub suggested_boundary_evidence: Vec<String>,
    pub recommended_review_focus: Vec<String>,
    pub evidence_boundary: String,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigFeatureBoundaryResidualReadingV0 {
    pub reading_id: String,
    pub boundary_ref: String,
    pub feature_extension_ref: String,
    pub status: String,
    pub core_scope_ref: String,
    pub feature_scope_ref: String,
    pub mixed_subconfiguration_refs: Vec<String>,
    pub core_local_reading_refs: Vec<String>,
    pub feature_local_reading_refs: Vec<String>,
    pub boundary_support_refs: Vec<String>,
    pub holonomy_axes: Vec<ArchSigBoundaryHolonomyAxisResidualV0>,
    pub residual_obstruction_refs: Vec<String>,
    pub support_separation_policy: String,
    pub coverage_assumptions: Vec<String>,
    pub exactness_assumptions: Vec<String>,
    pub attribution_policy: String,
    pub coverage_boundary: String,
    pub exactness_boundary: String,
    pub evidence_boundary: String,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigBoundaryHolonomyAxisResidualV0 {
    pub holonomy_axis_ref: String,
    pub axis_family: String,
    pub status: String,
    pub residual_value: i64,
    pub measured_defect_refs: Vec<String>,
    pub support_refs: Vec<String>,
    pub missing_evidence: Vec<String>,
    pub reading: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigFeatureExtensionDiagnosisReadingV0 {
    pub diagnosis_id: String,
    pub feature_extension_ref: String,
    pub boundary_residual_ref: String,
    pub status: String,
    pub classifier_version: String,
    pub classification_summary: Vec<ArchSigFeatureExtensionAxisSummaryV0>,
    pub attribution_records: Vec<ArchSigFeatureExtensionWitnessAttributionV0>,
    pub residual_coverage_gap_refs: Vec<String>,
    pub lifting_failure_refs: Vec<String>,
    pub filling_failure_refs: Vec<String>,
    pub complexity_transfer_refs: Vec<String>,
    pub classification_boundary: String,
    pub fieldsig_boundary: String,
    pub evidence_boundary: String,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigFeatureExtensionWitnessAttributionV0 {
    pub witness_ref: String,
    pub labels: Vec<String>,
    #[serde(default)]
    pub observation_refs: Vec<String>,
    #[serde(default)]
    pub source_refs: Vec<String>,
    pub inherited_core_refs: Vec<String>,
    pub feature_local_refs: Vec<String>,
    pub boundary_holonomy_refs: Vec<String>,
    pub lifting_failure_refs: Vec<String>,
    pub filling_failure_refs: Vec<String>,
    pub complexity_transfer_refs: Vec<String>,
    pub residual_coverage_gap_refs: Vec<String>,
    pub reading: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigArchMapStoreRefsV0 {
    pub ref_set_id: String,
    pub arch_map_ref: String,
    pub delta_ref: ArchSigAnalysisArtifactRefV0,
    pub commit_ref: ArchSigAnalysisArtifactRefV0,
    pub snapshot_ref: ArchSigAnalysisArtifactRefV0,
    pub index_ref: ArchSigAnalysisArtifactRefV0,
    pub raw_diff_boundary: String,
    pub compaction_boundary: String,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigMonodromyReadingFamilyV0 {
    pub reading_family_id: String,
    pub status: String,
    #[serde(default)]
    pub measured_axis_count: usize,
    #[serde(default)]
    pub unmeasured_axis_count: usize,
    #[serde(default)]
    pub positive_witness_count: usize,
    #[serde(default)]
    pub coverage_blocker_count: usize,
    pub arch_map_store_ref_set_ref: String,
    pub selected_axis_refs: Vec<String>,
    pub distance_kind: String,
    pub weight_policy: String,
    pub coverage_policy: String,
    pub operation_square_candidate_refs: Vec<String>,
    pub path_continuation_trace_refs: Vec<String>,
    pub axis_wise_defect_refs: Vec<String>,
    pub ami_aggregate_reading_refs: Vec<String>,
    pub aggregate_reading_kind: String,
    pub reading_boundary: String,
    pub evidence_boundary: String,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigBoundaryHolonomyReadingFamilyV0 {
    pub reading_family_id: String,
    pub status: String,
    #[serde(default)]
    pub measured_axis_count: usize,
    #[serde(default)]
    pub unmeasured_axis_count: usize,
    #[serde(default)]
    pub positive_witness_count: usize,
    #[serde(default)]
    pub coverage_blocker_count: usize,
    pub arch_map_store_ref_set_ref: String,
    pub selected_axis_refs: Vec<String>,
    pub distance_kind: String,
    pub weight_policy: String,
    pub coverage_policy: String,
    pub nonzero_monodromy_witness_refs: Vec<String>,
    pub feature_boundary_residual_refs: Vec<String>,
    pub extension_diagnosis_refs: Vec<String>,
    pub attribution_boundary: String,
    pub reading_boundary: String,
    pub evidence_boundary: String,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigAnalysisArtifactRefV0 {
    pub artifact_id: String,
    pub artifact_kind: String,
    pub schema_version: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub path: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub content_hash: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigArchitectureStateV0 {
    pub state_id: String,
    pub reading: String,
    pub atom_family_refs: Vec<String>,
    pub molecule_refs: Vec<String>,
    pub workflow_refs: Vec<String>,
    pub boundary_refs: Vec<String>,
    pub invariant_refs: Vec<String>,
    pub signature_axis_refs: Vec<String>,
    pub coverage_boundary: String,
    pub recommended_next_action: String,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigDesignPressureReadingV0 {
    pub pressure_id: String,
    pub status: String,
    pub reading: String,
    pub atom_configuration_refs: Vec<String>,
    pub obstruction_refs: Vec<String>,
    pub signature_axis_refs: Vec<String>,
    pub coverage_boundary: String,
    pub recommended_next_action: String,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigChangeImpactReadingV0 {
    pub impact_id: String,
    pub operation_scope: String,
    pub signature_delta_summary: Vec<String>,
    pub affected_boundaries: Vec<String>,
    pub complexity_transfer_notes: Vec<String>,
    pub coverage_boundary: String,
    pub recommended_next_action: String,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigAatConceptSurfaceV0 {
    pub concept: String,
    pub status: String,
    pub reading: String,
    pub evidence_refs: Vec<String>,
    pub coverage_boundary: String,
    pub exactness_boundary: String,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigAtomConfigurationSummaryV0 {
    pub atom_observation_count: usize,
    pub molecule_observation_count: usize,
    pub semantic_observation_count: usize,
    pub observation_gap_count: usize,
    pub concern_hint_count: usize,
    pub configuration_boundary: String,
    pub coverage_summary: Vec<String>,
    pub source_refs: Vec<String>,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigArchitectureObjectProjectionV0 {
    pub projection_id: String,
    pub projection_family: String,
    pub atom_refs: Vec<String>,
    pub molecule_refs: Vec<String>,
    pub semantic_refs: Vec<String>,
    pub reading: String,
    pub projection_boundary: String,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigInvariantFamilyReadingV0 {
    pub invariant_id: String,
    pub invariant_family: String,
    pub status: String,
    pub law_refs: Vec<String>,
    pub atom_refs: Vec<String>,
    pub obstruction_refs: Vec<String>,
    pub reading: String,
    pub evidence_boundary: String,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigLawUniverseReadingV0 {
    pub law_universe_id: String,
    pub profile_ref: String,
    pub selected_law_refs: Vec<String>,
    pub witness_rule_refs: Vec<String>,
    pub signature_axis_refs: Vec<String>,
    pub exactness_assumptions: Vec<String>,
    pub coverage_requirements: Vec<String>,
    pub reading: String,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigMoleculeReadingV0 {
    pub molecule_reading_id: String,
    pub molecule_observation_ref: String,
    pub law_refs: Vec<String>,
    pub atom_observation_refs: Vec<String>,
    #[serde(default)]
    pub configuration_graph_refs: Vec<String>,
    pub reading: String,
    pub evidence_summary: String,
    pub evidence_boundary: String,
    pub source_refs: Vec<String>,
    #[serde(rename = "interpretationNotesForLLM")]
    pub interpretation_notes_for_llm: Vec<String>,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigGeneratedAtomShapeV0 {
    pub atom_shape_id: String,
    pub atom_observation_ref: String,
    pub family: String,
    pub axis: String,
    pub subject_ref: String,
    pub predicate: String,
    pub object_slots: Vec<String>,
    pub payload_slots: Vec<String>,
    pub direction: String,
    pub arity: usize,
    pub ports: Vec<String>,
    pub valence_summary: String,
    pub evidence_boundary: String,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigGeneratedMoleculeV0 {
    pub generated_molecule_id: String,
    pub source_molecule_observation_ref: String,
    pub generation_status: String,
    pub atom_observation_refs: Vec<String>,
    pub atom_shape_refs: Vec<String>,
    pub compatible_pair_count: usize,
    pub required_port_status: String,
    pub not_arbitrary_set_boundary: String,
    pub evidence_boundary: String,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigGeneratedLawInputV0 {
    pub generated_law_input_id: String,
    pub generated_molecule_ref: String,
    pub source_molecule_reading_ref: String,
    pub law_refs: Vec<String>,
    pub signature_axis_refs: Vec<String>,
    #[serde(default)]
    pub applicable_law_axes: Vec<String>,
    pub atom_shape_refs: Vec<String>,
    pub law_input_kind: String,
    pub evaluation_status: String,
    #[serde(default)]
    pub local_statuses: Vec<String>,
    pub coverage_boundary: String,
    pub evidence_boundary: String,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigGeneratedObstructionV0 {
    pub generated_obstruction_id: String,
    pub obstruction_circuit_ref: String,
    pub generated_law_input_refs: Vec<String>,
    pub generated_molecule_refs: Vec<String>,
    pub atom_shape_refs: Vec<String>,
    pub obstruction_kind: String,
    #[serde(default)]
    pub local_status: String,
    pub measurement_status: String,
    #[serde(default)]
    pub blocker_status: String,
    pub evidence_boundary: String,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigGeneratedRepairTargetV0 {
    pub repair_target_id: String,
    pub target_kind: String,
    pub source_repair_candidate_ref: String,
    pub generated_obstruction_refs: Vec<String>,
    pub generated_molecule_refs: Vec<String>,
    pub atom_shape_refs: Vec<String>,
    pub blocked_by_gap_refs: Vec<String>,
    pub required_port_or_slot: String,
    pub recommended_operation_kind: String,
    pub evidence_boundary: String,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigViewerDistanceInputV0 {
    pub distance_input_id: String,
    pub distance_kind: String,
    pub source_ref: String,
    pub target_ref: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub generated_molecule_ref: Option<String>,
    pub atom_shape_refs: Vec<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub distance_value: Option<i64>,
    pub coordinate_components: Vec<String>,
    pub evidence_boundary: String,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigPart4DistanceFoundationV0 {
    pub foundation_id: String,
    pub profile: ArchSigDistanceProfileV0,
    pub diagnostic_scope: ArchSigDiagnosticScopeV0,
    pub supporting_distances: Vec<ArchSigSupportingDistanceV0>,
    pub status_summary: ArchSigDistanceStatusSummaryV0,
    pub measurement_boundary: String,
    pub proxy_guardrails: Vec<String>,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigDistanceProfileV0 {
    pub profile_id: String,
    pub profile_source_ref: String,
    pub atom_weights: Vec<ArchSigDistanceProfileWeightV0>,
    pub signature_weights: Vec<ArchSigDistanceProfileWeightV0>,
    pub operation_costs: Vec<ArchSigDistanceOperationCostV0>,
    pub aggregation_policy: String,
    pub unmeasured_policy: String,
    pub law_overlay_policy: String,
    pub coverage_policy_refs: Vec<String>,
    pub evidence_boundary: String,
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigDistanceProfileWeightV0 {
    pub axis_ref: String,
    pub weight: i64,
    pub source_ref: String,
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigDistanceOperationCostV0 {
    pub operation_kind: String,
    pub cost: i64,
    pub source_ref: String,
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigDiagnosticScopeV0 {
    pub scope_id: String,
    pub observed_atom_refs: Vec<String>,
    pub configuration_refs: Vec<String>,
    pub law_universe_ref: String,
    pub distance_profile_ref: String,
    pub measured_axis_refs: Vec<String>,
    pub unmeasured_axis_refs: Vec<String>,
    pub coverage_policy_refs: Vec<String>,
    pub blocker_refs: Vec<String>,
    pub evidence_boundary: String,
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigSupportingDistanceV0 {
    pub distance_id: String,
    pub distance_family: String,
    pub distance_kind: String,
    pub source_ref: String,
    pub target_ref: String,
    pub value: ArchSigDistanceValueV0,
    pub profile_ref: String,
    pub diagnostic_scope_ref: String,
    pub evidence_boundary: String,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigDistanceValueV0 {
    pub status: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub measured_value: Option<i64>,
    pub unit: String,
    pub provenance_refs: Vec<String>,
    pub evaluator_basis_refs: Vec<String>,
    pub coverage_refs: Vec<String>,
    pub blocker_refs: Vec<String>,
    pub reading: String,
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigDistanceStatusSummaryV0 {
    pub measured_count: usize,
    pub zero_count: usize,
    pub unmeasured_count: usize,
    pub unavailable_count: usize,
    pub incomparable_count: usize,
    pub infinite_count: usize,
    pub blocked_count: usize,
    pub schema_foundation_only_count: usize,
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigAtomDistanceReadingV0 {
    pub atom_distance_reading_id: String,
    pub source_atom_ref: String,
    pub target_atom_ref: String,
    pub molecule_refs: Vec<String>,
    pub distance_profile_ref: String,
    pub diagnostic_scope_ref: String,
    pub fiber_distance: ArchSigDistanceValueV0,
    pub carrier_distance: ArchSigDistanceValueV0,
    pub valence_distance: ArchSigDistanceValueV0,
    pub semantic_anchor_distance: ArchSigDistanceValueV0,
    pub atom_layout_distance_bundle: ArchSigDistanceValueV0,
    pub component_distances: Vec<ArchSigAtomDistanceComponentV0>,
    pub high_distance_reasons: Vec<String>,
    pub viewer_distance_input_refs: Vec<String>,
    pub evidence_boundary: String,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigAtomDistanceComponentV0 {
    pub component_kind: String,
    pub weight: i64,
    pub value: ArchSigDistanceValueV0,
    pub evaluator_basis_refs: Vec<String>,
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigConfigurationDistanceReadingV0 {
    pub configuration_distance_reading_id: String,
    pub source_atom_ref: String,
    pub target_atom_ref: String,
    pub configuration_ref: String,
    pub molecule_refs: Vec<String>,
    pub distance_profile_ref: String,
    pub diagnostic_scope_ref: String,
    pub hypergraph_ref: String,
    pub typed_hyperedges: Vec<ArchSigConfigurationHyperedgeV0>,
    pub shortest_path_atom_refs: Vec<String>,
    pub shortest_path_hyperedge_refs: Vec<String>,
    pub configuration_indexed_distance: ArchSigDistanceValueV0,
    pub context_distance: ArchSigDistanceValueV0,
    pub small_molecule_weight_milli: i64,
    pub configuration_distance_bundle: ArchSigDistanceValueV0,
    pub high_context_overlap: bool,
    pub unreachable_pair_refs: Vec<String>,
    pub evidence_boundary: String,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigConfigurationHyperedgeV0 {
    pub hyperedge_id: String,
    pub hyperedge_kind: String,
    pub atom_refs: Vec<String>,
    pub source_refs: Vec<String>,
    pub evidence_boundary: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigObstructionCircuitV0 {
    pub obstruction_circuit_id: String,
    pub law_ref: String,
    pub witness_rule_ref: String,
    pub circuit_kind: String,
    pub atom_observation_refs: Vec<String>,
    pub molecule_reading_refs: Vec<String>,
    #[serde(default)]
    pub concern_hint_refs: Vec<String>,
    pub signature_axis_refs: Vec<String>,
    pub minimality_reading: String,
    pub evidence_summary: String,
    pub evidence_boundary: String,
    #[serde(default)]
    pub missing_evidence: Vec<String>,
    #[serde(default)]
    pub excluded_readings: Vec<String>,
    #[serde(rename = "interpretationNotesForLLM")]
    pub interpretation_notes_for_llm: Vec<String>,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigSignatureAxisReadingV0 {
    pub signature_axis_id: String,
    pub law_ref: String,
    pub axis_ref: String,
    pub value_type: String,
    pub value: i64,
    #[serde(default)]
    pub signature_distance_reading_refs: Vec<String>,
    pub zero_reading: String,
    pub coverage_status: String,
    pub exactness_assumptions: Vec<String>,
    pub evidence_summary: String,
    pub source_refs: Vec<String>,
    #[serde(default)]
    pub missing_evidence: Vec<String>,
    #[serde(default)]
    pub excluded_readings: Vec<String>,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigSignatureDistanceReadingV0 {
    pub signature_distance_reading_id: String,
    pub distance_profile_ref: String,
    pub diagnostic_scope_ref: String,
    pub axis_distances: Vec<ArchSigSignatureAxisDistanceV0>,
    pub total_measured_distance: ArchSigDistanceValueV0,
    pub measured_axis_refs: Vec<String>,
    pub unmeasured_axis_refs: Vec<String>,
    pub incomparable_axis_refs: Vec<String>,
    pub safe_region_status: String,
    pub safe_region_margin: ArchSigDistanceValueV0,
    pub path_drift: ArchSigDistanceValueV0,
    pub endpoint_distance: ArchSigDistanceValueV0,
    pub hidden_excursion_status: String,
    pub coverage_refs: Vec<String>,
    pub confidence: String,
    pub evidence_boundary: String,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigSignatureAxisDistanceV0 {
    pub signature_axis_ref: String,
    pub law_ref: String,
    pub axis_ref: String,
    pub rho_i: ArchSigDistanceValueV0,
    pub axis_distance: ArchSigDistanceValueV0,
    pub coverage_status: String,
    pub source_refs: Vec<String>,
    pub blocker_refs: Vec<String>,
    pub evidence_boundary: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigAnalyticRepresentationV0 {
    pub representation_id: String,
    pub representation_family: String,
    pub status: String,
    pub value_type: String,
    pub value: String,
    #[serde(default)]
    pub selected_graph_nodes: Vec<String>,
    #[serde(default)]
    pub selected_graph_edges: Vec<ArchSigAnalyticGraphEdgeV0>,
    #[serde(default)]
    pub sparse_matrix_entries: Vec<ArchSigAnalyticMatrixEntryV0>,
    #[serde(default)]
    pub walk_witness_refs: Vec<String>,
    pub graph_scope_refs: Vec<String>,
    pub axis_refs: Vec<String>,
    pub reading: String,
    pub coverage_boundary: String,
    pub zero_reflecting_boundary: String,
    #[serde(default)]
    pub part4_distance_refs: Vec<String>,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigAnalyticGraphEdgeV0 {
    pub edge_ref: String,
    pub source_ref: String,
    pub target_ref: String,
    pub weight: i64,
    pub relation_atom_ref: String,
    pub source_refs: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigAnalyticMatrixEntryV0 {
    pub row_ref: String,
    pub column_ref: String,
    pub value: i64,
    pub evidence_refs: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigCouplingCohesionReadingV0 {
    pub reading_id: String,
    pub axis: String,
    pub status: String,
    pub value_type: String,
    pub value: String,
    pub supporting_refs: Vec<String>,
    pub stressed_refs: Vec<String>,
    pub reading: String,
    pub coverage_boundary: String,
    pub recommended_next_action: String,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigSpectralAnalysisReadingV0 {
    pub spectral_reading_id: String,
    pub representation_family: String,
    pub status: String,
    pub matrix_shape: ArchSigSpectralMatrixShapeV0,
    pub entry_rule: String,
    pub value_type: String,
    pub values: Vec<ArchSigSpectralValueV0>,
    pub dominant_components: Vec<ArchSigSpectralDominantComponentV0>,
    pub support_refs: Vec<String>,
    pub reading: String,
    pub coverage_boundary: String,
    pub zero_reflecting_boundary: String,
    pub recommended_next_action: String,
    #[serde(default)]
    pub part4_distance_refs: Vec<String>,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigSpectralMatrixShapeV0 {
    pub row_domain: String,
    pub column_domain: String,
    pub row_count: usize,
    pub column_count: usize,
    pub nonzero_entry_count: usize,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigSpectralValueV0 {
    pub name: String,
    pub value: String,
    pub interpretation: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigSpectralDominantComponentV0 {
    pub component_ref: String,
    pub component_kind: String,
    pub value: String,
    pub reading: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigMeasurementReadingBoundaryV0 {
    #[serde(default)]
    pub reading_strength: String,
    #[serde(default)]
    pub zero_reflection_assumptions: Vec<String>,
    #[serde(default)]
    pub obstruction_reflection_assumptions: Vec<String>,
    #[serde(default)]
    pub coverage_requirement_refs: Vec<String>,
    #[serde(default)]
    pub witness_completeness_boundary: String,
}

impl Default for ArchSigMeasurementReadingBoundaryV0 {
    fn default() -> Self {
        Self {
            reading_strength: String::new(),
            zero_reflection_assumptions: Vec::new(),
            obstruction_reflection_assumptions: Vec::new(),
            coverage_requirement_refs: Vec::new(),
            witness_completeness_boundary: String::new(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigCurvatureSupportReadingV0 {
    pub reading_id: String,
    pub profile_ref: String,
    pub status: String,
    #[serde(default)]
    pub measurement_status: String,
    #[serde(default)]
    pub reading_boundary: ArchSigMeasurementReadingBoundaryV0,
    pub measured_axis_refs: Vec<String>,
    pub unmeasured_axis_refs: Vec<String>,
    pub witness_supports: Vec<ArchSigCurvatureWitnessSupportV0>,
    pub top_curvature_modes: Vec<ArchSigCurvatureTopModeV0>,
    pub witness_clusters: Vec<ArchSigCurvatureWitnessClusterV0>,
    pub coverage_boundary: String,
    pub exactness_assumption_refs: Vec<String>,
    pub measurement_boundary: String,
    pub missing_evidence: Vec<String>,
    #[serde(default)]
    pub part4_distance_refs: Vec<String>,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigCurvatureWitnessSupportV0 {
    pub witness_support_id: String,
    pub witness_rule_ref: String,
    pub selected_axis_ref: String,
    pub signature_axis_ref: String,
    #[serde(default)]
    pub measurement_status: String,
    #[serde(default)]
    pub reading_boundary: ArchSigMeasurementReadingBoundaryV0,
    #[serde(default)]
    pub local_curvature_ref: String,
    #[serde(default)]
    pub diagram_ref: String,
    #[serde(default)]
    pub lhs_observation_refs: Vec<String>,
    #[serde(default)]
    pub rhs_observation_refs: Vec<String>,
    #[serde(default)]
    pub distance_kind: String,
    #[serde(default)]
    pub distance_input_refs: Vec<String>,
    #[serde(default)]
    pub soundness_boundary: String,
    #[serde(default)]
    pub coverage_status: String,
    pub curvature_value: i64,
    pub weight: i64,
    pub support_refs: Vec<String>,
    pub source_refs: Vec<String>,
    pub observation_refs: Vec<String>,
    pub missing_evidence: Vec<String>,
    #[serde(default)]
    pub obstruction_measure_reading_refs: Vec<String>,
    pub reading: String,
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigObstructionMeasureReadingV0 {
    pub obstruction_measure_reading_id: String,
    pub profile_ref: String,
    pub obstruction_circuit_ref: String,
    pub witness_support_ref: String,
    pub witness_rule_ref: String,
    pub selected_axis_ref: String,
    pub signature_axis_ref: String,
    pub distance_profile_ref: String,
    pub diagnostic_scope_ref: String,
    pub witness_value: ArchSigDistanceValueV0,
    pub measure_value: ArchSigDistanceValueV0,
    pub support_refs: Vec<String>,
    pub source_refs: Vec<String>,
    pub observation_refs: Vec<String>,
    pub missing_evidence: Vec<String>,
    pub measurement_status: String,
    pub evidence_boundary: String,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigCurvatureMassReadingV0 {
    pub curvature_mass_reading_id: String,
    pub profile_ref: String,
    pub support_reading_ref: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub transfer_reading_ref: Option<String>,
    pub distance_profile_ref: String,
    pub diagnostic_scope_ref: String,
    pub obstruction_measure_reading_refs: Vec<String>,
    pub measured_axis_refs: Vec<String>,
    pub unmeasured_axis_refs: Vec<String>,
    pub curvature_mass: ArchSigDistanceValueV0,
    pub before_operation_mass: ArchSigDistanceValueV0,
    pub after_operation_mass: ArchSigDistanceValueV0,
    pub target_axis_decrease: ArchSigDistanceValueV0,
    pub protected_axis_movement: ArchSigDistanceValueV0,
    pub transport_distance: ArchSigDistanceValueV0,
    pub transferred_obstruction_refs: Vec<String>,
    pub complexity_transfer_distance_refs: Vec<String>,
    pub evidence_refs: Vec<String>,
    pub evidence_boundary: String,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigCurvatureTopModeV0 {
    pub mode_id: String,
    pub rank: usize,
    #[serde(default)]
    pub mode_kind: String,
    pub axis_ref: String,
    pub curvature_value: i64,
    #[serde(default)]
    pub operator_component_refs: Vec<String>,
    #[serde(default)]
    pub localization: String,
    #[serde(default)]
    pub source_refs: Vec<String>,
    #[serde(default)]
    pub recommended_review_target: String,
    pub witness_refs: Vec<String>,
    pub support_refs: Vec<String>,
    pub reading: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigCurvatureWitnessClusterV0 {
    pub cluster_id: String,
    pub cluster_kind: String,
    #[serde(default)]
    pub cluster_basis: Vec<String>,
    pub axis_refs: Vec<String>,
    pub witness_refs: Vec<String>,
    pub support_refs: Vec<String>,
    #[serde(default)]
    pub source_refs: Vec<String>,
    #[serde(default)]
    pub transfer_edge_refs: Vec<String>,
    pub cluster_weight: i64,
    pub reading: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigCurvatureTransferReadingV0 {
    pub reading_id: String,
    pub profile_ref: String,
    pub status: String,
    #[serde(default)]
    pub measurement_status: String,
    #[serde(default)]
    pub reading_boundary: ArchSigMeasurementReadingBoundaryV0,
    pub transfer_operator: ArchSigCurvatureTransferOperatorV0,
    pub transfer_edges: Vec<ArchSigCurvatureTransferEdgeV0>,
    pub recurrent_obstruction_modes: Vec<ArchSigRecurrentObstructionModeV0>,
    pub spectral_radius_reading: ArchSigSpectralValueV0,
    pub coverage_boundary: String,
    pub evidence_boundary: String,
    #[serde(default)]
    pub part4_distance_refs: Vec<String>,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigCurvatureTransferOperatorV0 {
    pub operator_id: String,
    pub row_domain: String,
    pub column_domain: String,
    #[serde(default)]
    pub row_support_refs: Vec<String>,
    #[serde(default)]
    pub column_support_refs: Vec<String>,
    #[serde(default)]
    pub sparse_entries: Vec<ArchSigCurvatureTransferMatrixEntryV0>,
    pub row_count: usize,
    pub column_count: usize,
    pub nonzero_edge_count: usize,
    pub entry_rule: String,
    #[serde(default)]
    pub spectral_radius_kind: String,
    pub reading: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigCurvatureTransferMatrixEntryV0 {
    pub row_support_ref: String,
    pub column_support_ref: String,
    pub weight: i64,
    pub edge_ref: String,
    pub evidence_refs: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigCurvatureTransferEdgeV0 {
    pub edge_id: String,
    pub source_support_ref: String,
    pub source_axis_ref: String,
    pub target_support_ref: String,
    pub target_axis_ref: String,
    pub witness_refs: Vec<String>,
    pub defect_value: i64,
    pub weight: i64,
    pub source_refs: Vec<String>,
    #[serde(default)]
    pub evidence_refs: Vec<String>,
    #[serde(default)]
    pub extraction_rule: String,
    #[serde(default)]
    pub closed_walk_kind: String,
    #[serde(default)]
    pub part4_distance_refs: Vec<String>,
    pub reading: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigRecurrentObstructionModeV0 {
    pub mode_id: String,
    #[serde(default)]
    pub recurrence_kind: String,
    pub transfer_edge_refs: Vec<String>,
    pub support_refs: Vec<String>,
    pub witness_refs: Vec<String>,
    #[serde(default)]
    pub cycle_weight: i64,
    pub spectral_radius_reading: String,
    pub recurrent_obstruction_reading: String,
    pub review_focus: Vec<String>,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigArchitectureSpectrumReportV0 {
    pub report_id: String,
    pub profile_ref: String,
    pub status: String,
    #[serde(default)]
    pub measurement_status: String,
    #[serde(default)]
    pub reading_boundary: ArchSigMeasurementReadingBoundaryV0,
    pub top_hotspots: Vec<ArchSigArchitectureSpectrumHotspotV0>,
    pub top_eigenmodes: Vec<ArchSigArchitectureSpectrumModeV0>,
    pub top_witness_clusters: Vec<ArchSigArchitectureSpectrumWitnessClusterV0>,
    pub recurrent_obstructions: Vec<ArchSigArchitectureSpectrumRecurrentObstructionV0>,
    pub coverage_gaps: Vec<String>,
    #[serde(default)]
    pub curvature_mass_reading_refs: Vec<String>,
    pub measured_boundary: String,
    pub recommended_review_focus: Vec<String>,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigArchitectureSpectrumHotspotV0 {
    pub hotspot_id: String,
    pub axis_ref: String,
    pub curvature_value: i64,
    pub support_refs: Vec<String>,
    pub witness_refs: Vec<String>,
    pub coverage_gap_refs: Vec<String>,
    pub recommended_next_action: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigArchitectureSpectrumModeV0 {
    pub mode_ref: String,
    pub rank: usize,
    #[serde(default)]
    pub mode_kind: String,
    pub axis_ref: String,
    pub curvature_value: i64,
    #[serde(default)]
    pub operator_component_refs: Vec<String>,
    #[serde(default)]
    pub localization: String,
    #[serde(default)]
    pub source_refs: Vec<String>,
    #[serde(default)]
    pub recommended_review_target: String,
    pub support_refs: Vec<String>,
    pub witness_refs: Vec<String>,
    pub reading: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigArchitectureSpectrumWitnessClusterV0 {
    pub cluster_ref: String,
    #[serde(default)]
    pub cluster_basis: Vec<String>,
    pub axis_refs: Vec<String>,
    pub witness_refs: Vec<String>,
    pub support_refs: Vec<String>,
    #[serde(default)]
    pub source_refs: Vec<String>,
    #[serde(default)]
    pub transfer_edge_refs: Vec<String>,
    pub cluster_weight: i64,
    pub reading: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigArchitectureSpectrumRecurrentObstructionV0 {
    pub mode_ref: String,
    pub spectral_radius_reading: String,
    pub transfer_edge_refs: Vec<String>,
    pub support_refs: Vec<String>,
    pub witness_refs: Vec<String>,
    pub reading: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigSpectralModeReadingV0 {
    pub spectral_mode_id: String,
    pub source_spectral_reading_ref: String,
    pub representation_family: String,
    pub status: String,
    pub mode_kind: String,
    pub mode_components: Vec<ArchSigSpectralModeComponentV0>,
    pub spectral_gap_proxy: ArchSigSpectralValueV0,
    pub localization_index: ArchSigSpectralValueV0,
    pub matrix_density: ArchSigSpectralValueV0,
    pub decomposability_reading: String,
    pub repair_perturbation_reading: String,
    pub evidence_boundary: String,
    pub recommended_next_action: String,
    #[serde(default)]
    pub part4_distance_refs: Vec<String>,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigSpectralModeComponentV0 {
    pub component_ref: String,
    pub component_kind: String,
    pub weight: String,
    pub role: String,
    pub reading: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigSpectralDrilldownReadingV0 {
    pub drilldown_id: String,
    pub status: String,
    pub source_spectral_mode_refs: Vec<String>,
    pub dominant_atom_family_composition: Vec<ArchSigDominantAtomFamilyCompositionV0>,
    pub high_overlap_molecule_pairs: Vec<ArchSigHighOverlapMoleculePairV0>,
    pub repair_axis_delta_readings: Vec<ArchSigRepairAxisDeltaReadingV0>,
    pub reading: String,
    pub evidence_boundary: String,
    pub recommended_next_action: String,
    #[serde(default)]
    pub part4_distance_refs: Vec<String>,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigDominantAtomFamilyCompositionV0 {
    pub source_component_ref: String,
    pub source_component_kind: String,
    pub atom_family: String,
    pub count: usize,
    pub atom_observation_refs: Vec<String>,
    pub reading: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigHighOverlapMoleculePairV0 {
    pub pair_id: String,
    pub left_molecule_ref: String,
    pub right_molecule_ref: String,
    pub overlap_score: i64,
    pub shared_atom_families: Vec<String>,
    pub shared_atom_refs: Vec<String>,
    pub boundary_advice: String,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigRepairAxisDeltaReadingV0 {
    pub operation_delta_ref: String,
    pub operation_kind: String,
    pub positive_delta_axes: Vec<String>,
    pub negative_delta_axes: Vec<String>,
    pub neutral_or_unknown_axes: Vec<String>,
    pub transfer_risk_refs: Vec<String>,
    pub reading: String,
    pub evidence_boundary: String,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigTransferBridgeReadingV0 {
    pub transfer_bridge_id: String,
    pub status: String,
    pub transfer_matrix_entries: Vec<ArchSigTransferMatrixEntryV0>,
    pub bridge_atom_families: Vec<ArchSigBridgeAtomFamilyReadingV0>,
    pub evolution_risk_ranking: ArchSigEvolutionRiskRankingV0,
    pub reading: String,
    pub evidence_boundary: String,
    pub recommended_next_action: String,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigTransferMatrixEntryV0 {
    pub operation_delta_ref: String,
    pub transferred_axis_ref: String,
    pub transfer_weight: i64,
    pub transfer_kind: String,
    pub reading: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigBridgeAtomFamilyReadingV0 {
    pub bridge_id: String,
    pub source_hub_molecule_ref: String,
    pub target_hub_molecule_ref: String,
    pub intermediate_molecule_refs: Vec<String>,
    pub bridge_atom_families: Vec<String>,
    pub bridge_score: i64,
    pub path_pair_refs: Vec<String>,
    pub edge_breakdowns: Vec<ArchSigBridgeEdgeBreakdownV0>,
    pub shared_axis_refs: Vec<String>,
    pub review_risk: String,
    pub recommended_boundary_preparation: String,
    pub evidence_boundary: String,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigBridgeEdgeBreakdownV0 {
    pub edge_id: String,
    pub source_molecule_ref: String,
    pub target_molecule_ref: String,
    pub pair_ref: String,
    pub overlap_score: i64,
    pub shared_atom_families: Vec<String>,
    pub shared_atom_refs: Vec<String>,
    pub family_supporting_atom_refs: Vec<String>,
    pub source_refs: Vec<String>,
    pub source_ref_rationale: String,
    pub dependency_kind: String,
    pub dependency_reading: String,
    pub review_focus: Vec<String>,
    pub recommended_cut_kind: String,
    pub cut_rationale: String,
    #[serde(rename = "llmReviewSummary")]
    pub llm_review_summary: String,
    pub evidence_boundary: String,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigEvolutionRiskRankingV0 {
    pub repair_transfer_risk_ranking: Vec<ArchSigRepairTransferRiskRankV0>,
    pub boundary_preparation_ranking: Vec<ArchSigBoundaryPreparationRankV0>,
    pub reading: String,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigRepairTransferRiskRankV0 {
    pub rank: usize,
    pub operation_delta_ref: String,
    pub positive_axis_count: usize,
    pub transferred_axis_count: usize,
    pub transfer_weight: i64,
    pub reading: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigBoundaryPreparationRankV0 {
    pub rank: usize,
    pub pair_ref: String,
    pub left_molecule_ref: String,
    pub right_molecule_ref: String,
    pub overlap_score: i64,
    pub shared_atom_families: Vec<String>,
    pub reading: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigAtomSupportAxisReadingV0 {
    pub reading_id: String,
    pub scope_ref: String,
    pub scope_kind: String,
    pub support_size: usize,
    pub subject_family_spread: Vec<ArchSigSubjectFamilySpreadV0>,
    pub axis_restriction_counts: Vec<ArchSigAxisRestrictionCountV0>,
    pub axis_concentration: String,
    pub mixed_axis_molecule_pressure: String,
    pub high_support_refs: Vec<String>,
    pub source_refs: Vec<String>,
    pub coverage_boundary: String,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigSubjectFamilySpreadV0 {
    pub subject_ref: String,
    pub atom_count: usize,
    pub atom_families: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigAxisRestrictionCountV0 {
    pub axis: String,
    pub atom_count: usize,
    pub atom_observation_refs: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigAtomCompatibilityReadingV0 {
    pub reading_id: String,
    pub status: String,
    pub same_slot_conflict_count: usize,
    pub conflicts: Vec<ArchSigAtomCompatibilityConflictV0>,
    pub conflicting_atom_observation_refs: Vec<String>,
    pub conflicting_semantic_observation_refs: Vec<String>,
    pub payload_inconsistency_kinds: Vec<String>,
    #[serde(default)]
    pub payload_comparison_policy: Vec<String>,
    pub confidence_boundary: String,
    pub uncertainty: Vec<String>,
    pub evidence_boundary: String,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigAtomCompatibilityConflictV0 {
    pub slot_ref: String,
    pub subject_ref: String,
    pub predicate: String,
    pub atom_observation_refs: Vec<String>,
    pub semantic_observation_refs: Vec<String>,
    pub inconsistency_kind: String,
    #[serde(default)]
    pub payload_comparison_policy: String,
    #[serde(default)]
    pub compared_payload_refs: Vec<String>,
    #[serde(default)]
    pub source_refs: Vec<String>,
    #[serde(default)]
    pub confidence_refs: Vec<String>,
    #[serde(default)]
    pub uncertainty_refs: Vec<String>,
    #[serde(default)]
    pub semantic_conflict_relation_refs: Vec<String>,
    pub reading: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigLawUniverseCoverageReadingV0 {
    pub reading_id: String,
    pub law_universe_ref: String,
    pub required_law_coverage: Vec<ArchSigCoverageStatusV0>,
    pub optional_law_coverage: Vec<ArchSigCoverageStatusV0>,
    pub witness_family_coverage: Vec<ArchSigCoverageStatusV0>,
    pub signature_axis_coverage: Vec<ArchSigCoverageStatusV0>,
    #[serde(default)]
    pub coverage_requirement_status: Vec<ArchSigCoverageStatusV0>,
    pub exactness_assumption_status: Vec<ArchSigCoverageStatusV0>,
    #[serde(default)]
    pub law_witness_axis_evaluations: Vec<ArchSigLawWitnessAxisAlignmentEvaluationV0>,
    pub unmeasured_required_law_count: usize,
    pub blocked_witness_refs: Vec<String>,
    pub law_witness_axis_alignment: String,
    pub coverage_boundary: String,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigCoverageStatusV0 {
    pub ref_id: String,
    pub status: String,
    pub evidence_refs: Vec<String>,
    pub blocker_refs: Vec<String>,
    pub reading: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigLawWitnessAxisAlignmentEvaluationV0 {
    pub evaluation_id: String,
    pub law_ref: String,
    pub alignment_status: String,
    pub coverage_status: String,
    pub exactness_status: String,
    pub required_witness_refs: Vec<String>,
    pub observed_witness_refs: Vec<String>,
    pub missing_witness_refs: Vec<String>,
    pub required_axis_refs: Vec<String>,
    pub observed_axis_refs: Vec<String>,
    pub missing_axis_refs: Vec<String>,
    pub coverage_requirement_refs: Vec<String>,
    pub exactness_assumption_refs: Vec<String>,
    pub source_backed_evidence_refs: Vec<String>,
    pub blocker_refs: Vec<String>,
    pub evaluator: String,
    pub reading: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigFeatureExtensionFormulaReadingV0 {
    pub reading_id: String,
    pub scope_ref: String,
    pub status: String,
    pub inherited_core_obstruction_refs: Vec<String>,
    pub feature_local_obstruction_refs: Vec<String>,
    pub interaction_obstruction_refs: Vec<String>,
    pub lifting_failure_refs: Vec<String>,
    pub filling_failure_refs: Vec<String>,
    pub complexity_transfer_refs: Vec<String>,
    pub residual_coverage_gap_refs: Vec<String>,
    #[serde(default)]
    pub witness_basis: Vec<ArchSigFeatureExtensionWitnessBasisV0>,
    pub classification_summary: Vec<ArchSigFeatureExtensionAxisSummaryV0>,
    pub evidence_boundary: String,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigFeatureExtensionWitnessBasisV0 {
    pub witness_ref: String,
    pub labels: Vec<String>,
    pub observation_refs: Vec<String>,
    pub source_refs: Vec<String>,
    pub basis_boundary: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigFeatureExtensionAxisSummaryV0 {
    pub axis: String,
    pub status: String,
    pub refs: Vec<String>,
    pub reading: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigOperationCalculusLawReadingV0 {
    pub reading_id: String,
    pub operation_ref: String,
    pub operation_kind: String,
    pub composition_status: String,
    pub associativity_under_observation_status: String,
    pub refinement_abstraction_compatibility: String,
    pub replacement_equivalence: String,
    pub protection_idempotence: String,
    pub runtime_localization: String,
    pub migration_compatibility: String,
    pub reverse_involution: String,
    pub repair_monotonicity: String,
    pub synthesis_no_solution_boundary: String,
    pub precondition_refs: Vec<String>,
    pub evidence_refs: Vec<String>,
    #[serde(default)]
    pub law_evidence: Vec<ArchSigOperationLawEvidenceV0>,
    pub evidence_boundary: String,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigOperationLawEvidenceV0 {
    pub law_axis: String,
    pub status: String,
    pub required_evidence_refs: Vec<String>,
    pub observed_evidence_refs: Vec<String>,
    pub blocked_reason_refs: Vec<String>,
    pub exactness_assumption_refs: Vec<String>,
    pub reading: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigPathSignatureTrajectoryReadingV0 {
    pub reading_id: String,
    pub path_ref: String,
    pub status: String,
    pub endpoint_signature_delta: Vec<String>,
    pub max_axis_excursion: Vec<ArchSigAxisExcursionV0>,
    pub non_monotone_axis_refs: Vec<String>,
    pub path_cost_proxy: String,
    pub preserved_invariant_trajectory: Vec<String>,
    pub introduced_obstruction_trajectory: Vec<String>,
    pub trajectory_coverage_boundary: String,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigAxisExcursionV0 {
    pub axis_ref: String,
    pub max_value: i64,
    pub evidence_refs: Vec<String>,
    pub reading: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigHomotopyOrderSensitivityReadingV0 {
    pub reading_id: String,
    pub status: String,
    pub independent_square_candidate_refs: Vec<String>,
    pub same_contract_replacement_refs: Vec<String>,
    pub repair_filler_refs: Vec<String>,
    pub operation_order_sensitivity: String,
    pub homotopy_blocker_refs: Vec<String>,
    pub selected_observation_preservation_status: String,
    pub evidence_boundary: String,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigDiagramFillabilityReadingV0 {
    pub reading_id: String,
    pub diagram_ref: String,
    pub diagram_family: String,
    pub status: String,
    pub missing_filler_kind: String,
    pub filler_candidate_refs: Vec<String>,
    pub non_fillability_witness_refs: Vec<String>,
    pub filling_blocker_refs: Vec<String>,
    pub obstruction_refs: Vec<String>,
    pub feature_extension_refs: Vec<String>,
    pub evidence_boundary: String,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigAxisForgettingRiskReadingV0 {
    pub reading_id: String,
    pub source_projection_ref: String,
    pub source_atom_support_refs: Vec<String>,
    pub forgotten_axis_refs: Vec<String>,
    #[serde(default)]
    pub selected_signature_axis_refs: Vec<String>,
    #[serde(default)]
    pub blocked_signature_axis_refs: Vec<String>,
    pub mixed_axis_scope_refs: Vec<String>,
    pub reflection_loss_kind: String,
    pub zero_reflection_status: String,
    pub obstruction_reflection_status: String,
    pub required_assumptions: Vec<String>,
    pub coverage_boundary: String,
    pub evidence_boundary: String,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigObservationProjectionFidelityReadingV0 {
    pub reading_id: String,
    pub source_projection_ref: String,
    pub source_axis_forgetting_ref: String,
    pub fidelity_status: String,
    pub observed_atom_family_count: usize,
    pub forgotten_coordinate_count: usize,
    pub observation_collision_count: usize,
    pub collapsed_atom_family_candidate_count: usize,
    pub hidden_atom_family_hint_count: usize,
    pub projection_lost_atom_family_refs: Vec<String>,
    pub projection_loss_axes: Vec<String>,
    #[serde(default)]
    pub reconstruction_blocker_refs: Vec<String>,
    pub reflection_status: String,
    pub measurement_boundary: String,
    pub recommended_next_action: String,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigAtomOriginClosureDebtReadingV0 {
    pub reading_id: String,
    pub source_backed_atom_count: usize,
    pub derived_or_inferred_atom_count: usize,
    pub expected_missing_atom_count: usize,
    pub source_backed_atom_family_refs: Vec<String>,
    pub derived_or_inferred_refs: Vec<String>,
    pub missing_expected_atom_refs: Vec<String>,
    pub closure_status: String,
    pub weakens_zero_or_repair_claims: Vec<String>,
    pub evidence_boundary: String,
    pub recommended_next_action: String,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigEffectRelationAlgebraReadingV0 {
    pub reading_id: String,
    pub generator_refs: Vec<String>,
    pub effect_atom_refs: Vec<String>,
    pub relation_atom_refs: Vec<String>,
    pub external_boundary_refs: Vec<String>,
    pub required_effect_relations: Vec<String>,
    pub relation_inputs: Vec<ArchSigEffectRelationInputV0>,
    pub relation_evaluations: Vec<ArchSigEffectRelationLawEvaluationV0>,
    pub relation_evaluator_status: String,
    pub unresolved_effect_relations: Vec<String>,
    pub effect_ordering_pressure: String,
    pub state_transition_ref: String,
    pub evidence_boundary: String,
    pub recommended_next_action: String,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigEffectRelationInputV0 {
    pub relation_input_id: String,
    pub relation_kind: String,
    pub ordering_refs: Vec<String>,
    pub replay_or_idempotency_refs: Vec<String>,
    pub compensation_or_finalization_refs: Vec<String>,
    pub authority_requirement_refs: Vec<String>,
    pub effect_refs: Vec<String>,
    pub runtime_or_trace_refs: Vec<String>,
    pub source_refs: Vec<String>,
    pub reading: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigEffectRelationLawEvaluationV0 {
    pub law_axis: String,
    pub status: String,
    pub required_input_refs: Vec<String>,
    pub observed_input_refs: Vec<String>,
    pub blocked_reason_refs: Vec<String>,
    pub evaluator: String,
    pub reading: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigSynthesisBlockageReadingV0 {
    pub reading_id: String,
    pub target_construction_refs: Vec<String>,
    pub required_atom_refs: Vec<String>,
    pub constraint_refs: Vec<String>,
    pub missing_evidence_refs: Vec<String>,
    pub decision_boundary_refs: Vec<String>,
    pub candidate_solution_refs: Vec<String>,
    pub blockage_status: String,
    pub no_solution_certificate_status: String,
    pub synthesis_boundary: String,
    pub recommended_next_action: String,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigOperationPreconditionReadinessReadingV0 {
    pub reading_id: String,
    pub operation_ref: String,
    pub operation_kind: String,
    pub readiness_status: String,
    pub precondition_refs: Vec<String>,
    pub missing_precondition_refs: Vec<String>,
    pub coverage_gap_refs: Vec<String>,
    pub exactness_gap_refs: Vec<String>,
    pub witness_gap_refs: Vec<String>,
    pub candidate_boundary: String,
    pub recommended_next_action: String,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigPathMultiplicityLossReadingV0 {
    pub reading_id: String,
    pub scope_ref: String,
    pub path_reading_refs: Vec<String>,
    pub observed_path_count: usize,
    pub alternate_path_pressure: usize,
    pub max_walk_length_proxy: usize,
    pub reachability_forgotten_refs: Vec<String>,
    pub fan_in_boundary_refs: Vec<String>,
    pub multiplicity_loss_status: String,
    pub homotopy_boundary: String,
    pub evidence_boundary: String,
    pub recommended_next_action: String,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigSignatureTrajectoryHomotopyRefutationReadingV0 {
    pub reading_id: String,
    pub selected_homotopy_ref: String,
    pub trajectory_reading_refs: Vec<String>,
    pub path_refs: Vec<String>,
    pub trajectory_disagreement_refs: Vec<String>,
    pub trajectory_equivalence_status: String,
    pub homotopy_refutation_status: String,
    pub selected_equivalence_boundary: String,
    pub evidence_boundary: String,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigBridgeSplitObstructionTransferReadingV0 {
    pub reading_id: String,
    pub split_readiness_ref: String,
    pub bridge_edge_refs: Vec<String>,
    pub molecule_refs: Vec<String>,
    pub obstruction_refs: Vec<String>,
    pub required_boundary_operations: Vec<String>,
    pub filler_evidence_status: String,
    pub lifting_evidence_status: String,
    pub transfer_risk_status: String,
    pub evidence_boundary: String,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigHomotopyComplexSummaryV0 {
    pub complex_id: String,
    pub profile_ref: String,
    pub status: String,
    #[serde(default)]
    pub measurement_status: String,
    #[serde(default)]
    pub reading_boundary: ArchSigMeasurementReadingBoundaryV0,
    pub selected_axis_refs: Vec<String>,
    pub zero_cells: Vec<ArchSigHomotopyCellSummaryV0>,
    pub one_cells: Vec<ArchSigHomotopyCellSummaryV0>,
    pub two_cells: Vec<ArchSigHomotopyCellSummaryV0>,
    pub source_refs: Vec<String>,
    pub coverage_boundary: String,
    pub exactness_assumptions: Vec<String>,
    pub evidence_boundary: String,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigHomotopyCellSummaryV0 {
    pub cell_id: String,
    pub cell_dimension: u8,
    pub cell_kind: String,
    pub status: String,
    pub observation_refs: Vec<String>,
    pub source_refs: Vec<String>,
    pub reading: String,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigPathPairCandidateV0 {
    pub candidate_id: String,
    pub candidate_source: String,
    pub status: String,
    #[serde(default)]
    pub measurement_status: String,
    #[serde(default)]
    pub reading_boundary: ArchSigMeasurementReadingBoundaryV0,
    pub p_path_ref: String,
    pub q_path_ref: String,
    #[serde(default)]
    pub p_operation_sequence: Vec<String>,
    #[serde(default)]
    pub q_operation_sequence: Vec<String>,
    #[serde(default)]
    pub endpoint_object_refs: Vec<String>,
    #[serde(default)]
    pub generator_candidate_refs: Vec<String>,
    pub shared_endpoint_refs: Vec<String>,
    pub selected_axis_refs: Vec<String>,
    pub source_refs: Vec<String>,
    pub observation_refs: Vec<String>,
    pub coverage_boundary: String,
    pub evidence_boundary: String,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigLoopCandidateV0 {
    pub loop_id: String,
    pub path_pair_ref: String,
    pub candidate_source: String,
    pub status: String,
    #[serde(default)]
    pub measurement_status: String,
    #[serde(default)]
    pub reading_boundary: ArchSigMeasurementReadingBoundaryV0,
    pub path_refs: Vec<String>,
    #[serde(default)]
    pub endpoint_object_refs: Vec<String>,
    pub filler_candidate_refs: Vec<String>,
    pub missing_filler_evidence: Vec<String>,
    pub selected_axis_refs: Vec<String>,
    pub source_refs: Vec<String>,
    #[serde(default)]
    pub part4_distance_refs: Vec<String>,
    pub coverage_boundary: String,
    pub evidence_boundary: String,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigFillerCandidateReadingV0 {
    pub reading_id: String,
    pub loop_ref: String,
    pub filler_rule_ref: String,
    pub filler_kind: String,
    pub status: String,
    #[serde(default)]
    pub measurement_status: String,
    #[serde(default)]
    pub reading_boundary: ArchSigMeasurementReadingBoundaryV0,
    #[serde(default)]
    pub evidence_status: String,
    #[serde(default)]
    pub measured_filler_evidence_refs: Vec<String>,
    #[serde(default)]
    pub missing_filler_evidence: Vec<String>,
    #[serde(default)]
    pub filling_condition_refs: Vec<String>,
    pub source_refs: Vec<String>,
    pub docs_refs: Vec<String>,
    pub runtime_refs: Vec<String>,
    pub next_check_refs: Vec<String>,
    #[serde(default)]
    pub part4_distance_refs: Vec<String>,
    pub evidence_boundary: String,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigArchitecturalHoleReadingV0 {
    pub reading_id: String,
    pub loop_ref: String,
    pub status: String,
    #[serde(default)]
    pub measurement_status: String,
    #[serde(default)]
    pub reading_boundary: ArchSigMeasurementReadingBoundaryV0,
    #[serde(default)]
    pub selected_diagram_refs: Vec<String>,
    #[serde(default)]
    pub non_fillability_witness_refs: Vec<String>,
    pub missing_filler_evidence: Vec<String>,
    pub next_check_refs: Vec<String>,
    pub source_refs: Vec<String>,
    #[serde(default)]
    pub part4_distance_refs: Vec<String>,
    pub coverage_boundary: String,
    pub evidence_boundary: String,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigHomotopyHolonomyReadingV0 {
    pub reading_id: String,
    pub path_pair_ref: String,
    pub loop_ref: String,
    pub axis_ref: String,
    #[serde(default)]
    pub measurement_status: String,
    #[serde(default)]
    pub reading_boundary: ArchSigMeasurementReadingBoundaryV0,
    pub distance_kind: String,
    pub value: i64,
    pub compared_continuation_summary: String,
    #[serde(default)]
    pub compared_continuation_refs: Vec<String>,
    #[serde(default)]
    pub distance_input_refs: Vec<String>,
    #[serde(default)]
    pub mu_defect_refs: Vec<String>,
    pub source_refs: Vec<String>,
    pub observation_refs: Vec<String>,
    pub filler_refs: Vec<String>,
    pub missing_filler_refs: Vec<String>,
    #[serde(default)]
    pub part4_distance_refs: Vec<String>,
    pub coverage_boundary: String,
    pub exactness_assumption_status: String,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigStokesStyleReadingV0 {
    pub reading_id: String,
    pub loop_ref: String,
    pub status: String,
    #[serde(default)]
    pub measurement_status: String,
    #[serde(default)]
    pub reading_boundary: ArchSigMeasurementReadingBoundaryV0,
    pub holonomy_reading_refs: Vec<String>,
    #[serde(default)]
    pub filling_evidence_refs: Vec<String>,
    #[serde(default)]
    pub non_fillability_witness_refs: Vec<String>,
    #[serde(default)]
    pub local_curvature_condition: String,
    pub local_curvature_cell_candidates: Vec<String>,
    pub review_queue_refs: Vec<String>,
    #[serde(default)]
    pub part4_distance_refs: Vec<String>,
    pub coverage_boundary: String,
    pub evidence_boundary: String,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigArchitectureHomotopyReportV0 {
    pub report_id: String,
    pub profile_ref: String,
    pub status: String,
    #[serde(default)]
    pub measurement_status: String,
    #[serde(default)]
    pub reading_boundary: ArchSigMeasurementReadingBoundaryV0,
    pub filled_loops: Vec<String>,
    pub unfilled_loops: Vec<String>,
    pub nonzero_holonomy_loops: Vec<String>,
    pub top_local_curvature_cells: Vec<String>,
    pub aggregate_readings: Vec<ArchSigHomotopyAggregateReadingV0>,
    pub coverage_gaps: Vec<String>,
    #[serde(default)]
    pub part4_distance_refs: Vec<String>,
    pub measured_boundary: String,
    pub recommended_review_focus: Vec<String>,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigHomotopyAggregateReadingV0 {
    pub aggregate_id: String,
    pub value: i64,
    pub reading: String,
    pub boundary: String,
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigHomotopyDistanceReadingV0 {
    pub homotopy_distance_reading_id: String,
    pub profile_ref: String,
    pub loop_ref: String,
    pub path_pair_ref: String,
    pub distance_profile_ref: String,
    pub diagnostic_scope_ref: String,
    pub homotopy_distance: ArchSigDistanceValueV0,
    pub filling_cost: ArchSigDistanceValueV0,
    pub observation_gap_lower_bound: ArchSigDistanceValueV0,
    pub selected_dehn_area: ArchSigDistanceValueV0,
    pub filler_candidate_refs: Vec<String>,
    pub measured_filler_refs: Vec<String>,
    pub missing_filler_refs: Vec<String>,
    pub holonomy_reading_refs: Vec<String>,
    pub non_fillability_witness_refs: Vec<String>,
    pub evidence_refs: Vec<String>,
    pub lipschitz_assumption_refs: Vec<String>,
    pub evidence_boundary: String,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigRepresentationStrengthReadingV0 {
    pub reading_id: String,
    pub source_reading_ref: String,
    pub representation_family: String,
    pub zero_preserving: String,
    pub zero_reflecting: String,
    pub obstruction_preserving: String,
    pub obstruction_reflecting: String,
    #[serde(default)]
    pub aggregate_zero_safety: String,
    #[serde(default)]
    pub cancellation_risk: String,
    pub required_assumptions: Vec<String>,
    pub blocked_by: Vec<String>,
    #[serde(default)]
    pub blocked_reflection_or_preservation_reasons: Vec<String>,
    pub reading: String,
    pub evidence_boundary: String,
    #[serde(default)]
    pub part4_distance_refs: Vec<String>,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigRepresentationMetricReadingV0 {
    pub representation_metric_reading_id: String,
    pub representation_ref: String,
    pub representation_family: String,
    pub source_reading_refs: Vec<String>,
    pub distance_profile_ref: String,
    pub diagnostic_scope_ref: String,
    pub structural_distance: ArchSigDistanceValueV0,
    pub analytic_distance: ArchSigDistanceValueV0,
    pub lipschitz_stability: ArchSigDistanceValueV0,
    pub bi_lipschitz_faithfulness: ArchSigDistanceValueV0,
    pub coverage_blocker_refs: Vec<String>,
    pub witness_completeness_blocker_refs: Vec<String>,
    pub analytic_representation_refs: Vec<String>,
    pub spectral_reading_refs: Vec<String>,
    pub spectral_mode_refs: Vec<String>,
    pub spectral_drilldown_refs: Vec<String>,
    pub representation_strength_refs: Vec<String>,
    pub evidence_refs: Vec<String>,
    pub evidence_boundary: String,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigLocalCurvatureDiagramReadingV0 {
    pub diagram_id: String,
    pub law_ref: String,
    pub obstruction_ref: String,
    pub signature_axis_refs: Vec<String>,
    pub molecule_refs: Vec<String>,
    pub lhs_path_refs: Vec<String>,
    pub rhs_path_refs: Vec<String>,
    pub curvature_value: i64,
    pub curvature_status: String,
    pub diagram_reading: String,
    pub filling_boundary: String,
    pub source_refs: Vec<String>,
    pub evidence_boundary: String,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigThreeLayerFlatnessReadingV0 {
    pub reading_id: String,
    pub static_status: String,
    pub runtime_status: String,
    pub semantic_status: String,
    pub static_observation_refs: Vec<String>,
    pub runtime_observation_refs: Vec<String>,
    pub semantic_observation_refs: Vec<String>,
    pub cross_layer_atom_refs: Vec<String>,
    pub non_implication_reading: String,
    pub evidence_boundary: String,
    pub recommended_next_action: String,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigObservationProjectionReadingV0 {
    pub reading_id: String,
    pub observed_atom_families: Vec<String>,
    pub observed_atom_family_count: usize,
    #[serde(default)]
    pub source_coordinates: Vec<ArchSigProjectionCoordinateV0>,
    #[serde(default)]
    pub observed_coordinates: Vec<ArchSigProjectionCoordinateV0>,
    pub forgotten_coordinates: Vec<String>,
    #[serde(default)]
    pub forgotten_coordinate_evidence: Vec<ArchSigProjectionCoordinateV0>,
    #[serde(default)]
    pub non_injectivity_candidates: Vec<ArchSigProjectionNonInjectivityCandidateV0>,
    #[serde(default)]
    pub reconstruction_blocker_evidence: Vec<ArchSigProjectionReconstructionBlockerV0>,
    #[serde(default)]
    pub observation_collision_pairs: Vec<String>,
    #[serde(default)]
    pub collapsed_atom_family_candidates: Vec<String>,
    #[serde(default)]
    pub hidden_atom_family_hints: Vec<String>,
    #[serde(default)]
    pub reconstruction_risk: String,
    pub coarse_projection_risks: Vec<String>,
    pub reconstruction_blockers: Vec<String>,
    pub source_refs: Vec<String>,
    pub reading: String,
    pub evidence_boundary: String,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigProjectionCoordinateV0 {
    pub coordinate_id: String,
    pub coordinate_kind: String,
    pub atom_family: String,
    pub subject_ref: String,
    pub predicate: String,
    pub atom_observation_refs: Vec<String>,
    pub source_refs: Vec<String>,
    pub status: String,
    pub reading: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigProjectionNonInjectivityCandidateV0 {
    pub candidate_id: String,
    pub candidate_kind: String,
    pub coordinate_refs: Vec<String>,
    pub atom_observation_refs: Vec<String>,
    pub evidence_refs: Vec<String>,
    pub reading: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigProjectionReconstructionBlockerV0 {
    pub blocker_id: String,
    pub blocker_kind: String,
    pub coordinate_refs: Vec<String>,
    pub gap_refs: Vec<String>,
    pub expected_atom_families: Vec<String>,
    pub source_refs: Vec<String>,
    pub blocked_axis_refs: Vec<String>,
    pub evidence_refs: Vec<String>,
    pub reading: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigStateTransitionAlgebraReadingV0 {
    pub reading_id: String,
    pub generator_refs: Vec<String>,
    pub state_atom_refs: Vec<String>,
    pub effect_atom_refs: Vec<String>,
    pub runtime_atom_refs: Vec<String>,
    pub required_relations: Vec<String>,
    pub transition_relation_inputs: Vec<ArchSigStateTransitionRelationInputV0>,
    pub law_evaluations: Vec<ArchSigStateTransitionLawEvaluationV0>,
    pub law_evaluator_status: String,
    pub unresolved_relations: Vec<String>,
    pub obstruction_refs: Vec<String>,
    pub reading: String,
    pub evidence_boundary: String,
    pub recommended_next_action: String,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigStateTransitionRelationInputV0 {
    pub transition_input_id: String,
    pub from_refs: Vec<String>,
    pub event_refs: Vec<String>,
    pub to_refs: Vec<String>,
    pub operation_refs: Vec<String>,
    pub invariant_refs: Vec<String>,
    pub runtime_or_trace_refs: Vec<String>,
    pub source_refs: Vec<String>,
    pub reading: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigStateTransitionLawEvaluationV0 {
    pub law_axis: String,
    pub status: String,
    pub required_input_refs: Vec<String>,
    pub observed_input_refs: Vec<String>,
    pub blocked_reason_refs: Vec<String>,
    pub evaluator: String,
    pub reading: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigOperationInvariantGaloisReadingV0 {
    pub reading_id: String,
    pub invariant_family_refs: Vec<String>,
    pub operation_family_refs: Vec<String>,
    pub ops_of_invariants: Vec<String>,
    pub inv_of_operations: Vec<String>,
    pub preserved_invariant_refs: Vec<String>,
    pub blocked_operation_refs: Vec<String>,
    pub reading: String,
    pub evidence_boundary: String,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigSplitReadinessReadingV0 {
    pub reading_id: String,
    pub molecule_ref: String,
    pub status: String,
    pub readiness_score: i64,
    pub core_embedding_status: String,
    pub feature_view_section_status: String,
    pub lifting_evidence_status: String,
    pub interaction_obstruction_refs: Vec<String>,
    pub bridge_edge_refs: Vec<String>,
    pub recommended_boundary_operation: String,
    pub reading: String,
    pub evidence_boundary: String,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigStructuralReadingReviewSurfaceV0 {
    pub surface_id: String,
    pub status: String,
    pub current_state_reading: String,
    pub connected_reading_refs: Vec<String>,
    pub review_focus: Vec<String>,
    pub evidence_boundary: String,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigCurrentStateEvolutionBoundaryV0 {
    pub boundary_id: String,
    pub archsig_current_state_scope: String,
    pub fieldsig_evolution_scope: String,
    pub handoff_artifact_ref: String,
    pub forbidden_readings: Vec<String>,
    pub evidence_boundary: String,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigDesignPrincipleReadingV0 {
    pub principle_id: String,
    pub principle: String,
    pub status: String,
    #[serde(default)]
    pub witness_rule_ref: String,
    #[serde(default)]
    pub witness_status: String,
    #[serde(default)]
    pub witness_evidence_refs: Vec<String>,
    pub aat_reading: String,
    pub invariant_refs: Vec<String>,
    pub obstruction_refs: Vec<String>,
    pub operation_refs: Vec<String>,
    pub evidence_refs: Vec<String>,
    #[serde(default)]
    pub source_refs: Vec<String>,
    pub confidence: String,
    pub coverage_boundary: String,
    pub exactness_blockers: Vec<String>,
    pub recommended_next_action: String,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigFlatnessReadingV0 {
    pub reading_id: String,
    pub selected_law_policy_ref: String,
    pub status: String,
    pub zero_signature_axis_refs: Vec<String>,
    pub nonzero_signature_axis_refs: Vec<String>,
    pub blocked_by_coverage_gaps: Vec<String>,
    pub evidence_boundary: String,
    #[serde(rename = "interpretationNotesForLLM")]
    pub interpretation_notes_for_llm: Vec<String>,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigLayerSplitV0 {
    pub static_observation_refs: Vec<String>,
    pub runtime_observation_refs: Vec<String>,
    pub semantic_observation_refs: Vec<String>,
    pub split_boundary: String,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigRepairOperationCandidateV0 {
    pub repair_operation_candidate_id: String,
    pub operation_kind: String,
    pub target_obstruction_refs: Vec<String>,
    pub preserved_invariants: Vec<String>,
    pub preconditions: Vec<String>,
    pub expected_signature_axis_effects: Vec<String>,
    pub transfer_risks: Vec<String>,
    #[serde(default)]
    pub part4_distance_refs: Vec<String>,
    pub evidence_boundary: String,
    #[serde(default)]
    pub missing_evidence: Vec<String>,
    #[serde(default)]
    pub excluded_readings: Vec<String>,
    #[serde(rename = "interpretationNotesForLLM")]
    pub interpretation_notes_for_llm: Vec<String>,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigOperationDeltaReadingV0 {
    pub operation_delta_id: String,
    pub operation_kind: String,
    pub support_refs: Vec<String>,
    pub preconditions: Vec<String>,
    pub atom_transformations: Vec<String>,
    pub transition_relation: String,
    pub invariant_preservation_claims: Vec<String>,
    pub obstruction_transport: Vec<String>,
    pub signature_delta: Vec<String>,
    pub decreased_axes: Vec<String>,
    pub transferred_obstructions: Vec<String>,
    #[serde(default)]
    pub part4_distance_refs: Vec<String>,
    pub excluded_readings: Vec<String>,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigOperationDistanceReadingV0 {
    pub operation_distance_reading_id: String,
    pub operation_delta_ref: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub repair_candidate_ref: Option<String>,
    pub operation_kind: String,
    pub distance_profile_ref: String,
    pub diagnostic_scope_ref: String,
    pub operation_cost: ArchSigDistanceValueV0,
    pub target_distance_decrease: ArchSigDistanceValueV0,
    pub protected_axis_movement: ArchSigDistanceValueV0,
    pub distance_to_selected_flat: ArchSigDistanceValueV0,
    pub side_effect_bound: ArchSigDistanceValueV0,
    pub transfer_risk_refs: Vec<String>,
    pub unmeasured_axis_refs: Vec<String>,
    pub evidence_refs: Vec<String>,
    pub repair_route_status: String,
    pub evidence_boundary: String,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigPathHomotopyDiagramReadingV0 {
    pub reading_id: String,
    pub surface: String,
    pub status: String,
    pub path_refs: Vec<String>,
    pub homotopy_refs: Vec<String>,
    pub diagram_refs: Vec<String>,
    pub filling_boundary: String,
    pub reading: String,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigBoundedJudgementV0 {
    pub judgement_id: String,
    pub status: String,
    pub aat_concept: String,
    pub reading: String,
    pub evidence_refs: Vec<String>,
    pub confidence: String,
    pub uncertainty: Vec<String>,
    pub coverage_boundary: String,
    pub exactness_boundary: String,
    pub recommended_next_action: String,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigLlmInterpretationPacketV0 {
    pub packet_id: String,
    pub short_diagnosis: String,
    pub aat_concept_map: Vec<String>,
    pub observed_atoms_summary: Vec<String>,
    pub obstruction_summary: Vec<String>,
    pub signature_axes_summary: Vec<String>,
    #[serde(default)]
    pub distance_diagnosis_summary: Vec<String>,
    pub analytic_readings_summary: Vec<String>,
    pub spectral_readings_summary: Vec<String>,
    pub spectral_mode_summary: Vec<String>,
    pub spectral_drilldown_summary: Vec<String>,
    #[serde(default)]
    pub representation_metric_summary: Vec<String>,
    #[serde(default)]
    pub curvature_support_summary: Vec<String>,
    #[serde(default)]
    pub curvature_transfer_summary: Vec<String>,
    #[serde(default)]
    pub architecture_spectrum_report_summary: Vec<String>,
    pub transfer_bridge_summary: Vec<String>,
    pub transfer_bridge_edge_summary: Vec<String>,
    #[serde(default)]
    pub measurement_expansion_summary: Vec<String>,
    #[serde(default)]
    pub atom_support_axis_summary: Vec<String>,
    #[serde(default)]
    pub atom_compatibility_summary: Vec<String>,
    #[serde(default)]
    pub law_universe_coverage_summary: Vec<String>,
    #[serde(default)]
    pub feature_extension_formula_summary: Vec<String>,
    #[serde(default)]
    pub operation_calculus_law_summary: Vec<String>,
    #[serde(default)]
    pub path_signature_trajectory_summary: Vec<String>,
    #[serde(default)]
    pub homotopy_order_sensitivity_summary: Vec<String>,
    #[serde(default)]
    pub diagram_fillability_summary: Vec<String>,
    #[serde(default)]
    pub axis_forgetting_risk_summary: Vec<String>,
    #[serde(default)]
    pub observation_projection_fidelity_summary: Vec<String>,
    #[serde(default)]
    pub atom_origin_closure_debt_summary: Vec<String>,
    #[serde(default)]
    pub effect_relation_algebra_summary: Vec<String>,
    #[serde(default)]
    pub synthesis_blockage_summary: Vec<String>,
    #[serde(default)]
    pub operation_precondition_readiness_summary: Vec<String>,
    #[serde(default)]
    pub path_multiplicity_loss_summary: Vec<String>,
    #[serde(default)]
    pub signature_trajectory_homotopy_refutation_summary: Vec<String>,
    #[serde(default)]
    pub bridge_split_obstruction_transfer_summary: Vec<String>,
    #[serde(default)]
    pub nonzero_monodromy_witness_summary: Vec<String>,
    #[serde(default)]
    pub feature_boundary_residual_summary: Vec<String>,
    #[serde(default)]
    pub feature_extension_diagnosis_summary: Vec<String>,
    pub representation_strength_summary: Vec<String>,
    pub local_curvature_diagram_summary: Vec<String>,
    pub three_layer_flatness_summary: Vec<String>,
    pub observation_projection_summary: Vec<String>,
    pub state_transition_algebra_summary: Vec<String>,
    pub operation_invariant_galois_summary: Vec<String>,
    pub split_readiness_summary: Vec<String>,
    pub structural_reading_review_summary: Vec<String>,
    pub current_state_evolution_boundary_summary: Vec<String>,
    pub repair_operation_summary: Vec<String>,
    pub complexity_transfer_notes: Vec<String>,
    pub coverage_gaps_and_exactness_blockers: Vec<String>,
    pub non_conclusions: Vec<String>,
    pub recommended_human_review_focus: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigAnalysisPacketValidationReportV0 {
    pub schema_version: String,
    pub input: ArchSigAnalysisPacketValidationInputV0,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub packet: Option<ArchSigAnalysisPacketV0>,
    pub summary: ArchSigAnalysisPacketValidationSummaryV0,
    pub checks: Vec<ValidationCheck>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigAnalysisPacketValidationInputV0 {
    pub schema_version: String,
    pub path: String,
    pub analysis_id: String,
    pub arch_map_ref: String,
    pub selected_law_policy_ref: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigAnalysisPacketValidationSummaryV0 {
    pub result: String,
    pub aat_concept_surface_count: usize,
    pub molecule_reading_count: usize,
    pub generated_atom_shape_count: usize,
    pub generated_molecule_count: usize,
    pub generated_law_input_count: usize,
    pub generated_obstruction_count: usize,
    pub generated_repair_target_count: usize,
    pub viewer_distance_input_count: usize,
    #[serde(default)]
    pub part4_supporting_distance_count: usize,
    #[serde(default)]
    pub atom_distance_reading_count: usize,
    #[serde(default)]
    pub configuration_distance_reading_count: usize,
    #[serde(default)]
    pub signature_distance_reading_count: usize,
    #[serde(default)]
    pub operation_distance_reading_count: usize,
    #[serde(default)]
    pub obstruction_measure_reading_count: usize,
    #[serde(default)]
    pub curvature_mass_reading_count: usize,
    pub obstruction_circuit_count: usize,
    pub signature_axis_count: usize,
    pub analytic_representation_count: usize,
    pub coupling_cohesion_reading_count: usize,
    pub spectral_analysis_reading_count: usize,
    pub spectral_mode_reading_count: usize,
    pub spectral_drilldown_reading_count: usize,
    pub curvature_support_reading_count: usize,
    pub curvature_transfer_reading_count: usize,
    pub transfer_bridge_reading_count: usize,
    pub atom_support_axis_reading_count: usize,
    pub atom_compatibility_reading_count: usize,
    pub law_universe_coverage_reading_count: usize,
    pub feature_extension_formula_reading_count: usize,
    pub operation_calculus_law_reading_count: usize,
    pub path_signature_trajectory_reading_count: usize,
    pub homotopy_order_sensitivity_reading_count: usize,
    pub diagram_fillability_reading_count: usize,
    pub axis_forgetting_risk_reading_count: usize,
    pub observation_projection_fidelity_reading_count: usize,
    pub atom_origin_closure_debt_reading_count: usize,
    pub effect_relation_algebra_reading_count: usize,
    pub synthesis_blockage_reading_count: usize,
    pub operation_precondition_readiness_reading_count: usize,
    pub path_multiplicity_loss_reading_count: usize,
    pub signature_trajectory_homotopy_refutation_reading_count: usize,
    #[serde(default)]
    pub homotopy_distance_reading_count: usize,
    pub bridge_split_obstruction_transfer_reading_count: usize,
    pub representation_strength_reading_count: usize,
    #[serde(default)]
    pub representation_metric_reading_count: usize,
    pub local_curvature_diagram_reading_count: usize,
    pub three_layer_flatness_reading_count: usize,
    pub observation_projection_reading_count: usize,
    pub state_transition_algebra_reading_count: usize,
    pub operation_invariant_galois_reading_count: usize,
    pub split_readiness_reading_count: usize,
    pub design_principle_reading_count: usize,
    pub repair_operation_candidate_count: usize,
    pub operation_delta_count: usize,
    pub bounded_judgement_count: usize,
    pub surface_check_count: usize,
    pub measurement_depth_check_count: usize,
    pub proxy_regression_check_count: usize,
    pub failed_check_count: usize,
    pub warning_check_count: usize,
}
