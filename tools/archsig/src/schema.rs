use serde::{Deserialize, Serialize};

pub const ARCHMAP_SCHEMA_VERSION: &str = "archmap-observation-map-v0";
pub const ARCHMAP_SOURCE_INVENTORY_SCHEMA_VERSION: &str = "archmap-source-inventory-v0";
pub const ARCHMAP_VALIDATION_REPORT_SCHEMA_VERSION: &str = "archmap-validation-report-v0";
pub const LAW_POLICY_SCHEMA_VERSION: &str = "law-policy-v0";
pub const LAW_POLICY_VALIDATION_REPORT_SCHEMA_VERSION: &str = "law-policy-validation-report-v0";
pub const ARCHSIG_ANALYSIS_PACKET_SCHEMA_VERSION: &str = "archsig-analysis-packet-v0";
pub const ARCHSIG_ANALYSIS_PACKET_VALIDATION_REPORT_SCHEMA_VERSION: &str =
    "archsig-analysis-packet-validation-report-v0";
pub const SCHEMA_VERSION_CATALOG_SCHEMA_VERSION: &str = "schema-version-catalog-v0";
pub const SCHEMA_COMPATIBILITY_POLICY_SCHEMA_VERSION: &str = "schema-compatibility-policy-v0";

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct SchemaVersionCatalogV0 {
    pub schema_version: String,
    pub catalog_id: String,
    pub catalog_version: String,
    pub phase: String,
    pub artifacts: Vec<SchemaVersionCatalogEntryV0>,
    pub compatibility_policy: SchemaCompatibilityPolicyV0,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct SchemaVersionCatalogEntryV0 {
    pub artifact_id: String,
    pub artifact_name: String,
    pub schema_version_name: String,
    pub artifact_role: String,
    pub owner_phase: String,
    pub status: String,
    pub primary_docs: Vec<String>,
    pub downstream_issues: Vec<String>,
    pub compatibility_boundary: SchemaCompatibilityBoundaryV0,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct SchemaCompatibilityBoundaryV0 {
    pub field_mapping_policy: String,
    pub deprecated_fields: Vec<String>,
    pub new_required_assumptions: Vec<String>,
    pub coverage_exactness_boundary: Vec<String>,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct SchemaCompatibilityPolicyV0 {
    pub schema_version: String,
    pub policy_id: String,
    pub policy_version: String,
    pub applies_to_catalog_version: String,
    pub dimensions: Vec<SchemaCompatibilityDimensionV0>,
    pub required_checks: Vec<String>,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct SchemaCompatibilityDimensionV0 {
    pub dimension: String,
    pub required_metadata: Vec<String>,
    pub checker_boundary: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ValidationCheck {
    pub id: String,
    pub title: String,
    pub result: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub reason: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub count: Option<usize>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub examples: Vec<ValidationExample>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub metric: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub lean_boundary: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ValidationExample {
    #[serde(skip_serializing_if = "Option::is_none")]
    pub component_id: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub path: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub source: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub target: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub evidence: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct ArchMapDocumentV0 {
    pub schema_version: String,
    pub map_id: String,
    pub architecture_id: String,
    pub generated_at: String,
    pub generator: ArchMapGenerator,
    #[serde(default)]
    pub prompt_refs: Vec<ArchMapArtifactRef>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub source_inventory_ref: Option<ArchMapArtifactRef>,
    pub generation_boundary: ArchMapGenerationBoundary,
    pub source_universe: ArchMapSourceUniverse,
    #[serde(default)]
    pub provenance: ArchMapProvenanceV0,
    #[serde(default)]
    pub atom_observations: Vec<ArchMapAtomObservationV0>,
    #[serde(default)]
    pub molecule_observations: Vec<ArchMapMoleculeObservationV0>,
    #[serde(default)]
    pub semantic_observations: Vec<ArchMapSemanticObservationV0>,
    #[serde(default)]
    pub observation_gaps: Vec<ArchMapObservationGapV0>,
    #[serde(default)]
    pub projection_info: Vec<ArchMapProjectionInfoV0>,
    #[serde(default)]
    pub concern_hints: Vec<ArchMapConcernHintV0>,
    #[serde(default)]
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchMapGenerator {
    pub kind: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub tool: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub provider: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub model_id: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchMapArtifactRef {
    pub artifact_id: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub kind: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub path: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub content_hash: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchMapGenerationBoundary {
    #[serde(skip_serializing_if = "Option::is_none")]
    pub token_budget: Option<String>,
    #[serde(default)]
    pub scope: Vec<String>,
    #[serde(default)]
    pub excluded_refs: Vec<ArchMapSourceRef>,
    #[serde(default)]
    pub private_refs: Vec<ArchMapSourceRef>,
    #[serde(default)]
    pub unavailable_refs: Vec<ArchMapSourceRef>,
    #[serde(default)]
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchMapSourceUniverse {
    pub root: String,
    #[serde(default)]
    pub included_refs: Vec<ArchMapSourceRef>,
    #[serde(default)]
    pub excluded_refs: Vec<ArchMapSourceRef>,
    #[serde(default)]
    pub unavailable_refs: Vec<ArchMapSourceRef>,
    #[serde(default)]
    pub private_refs: Vec<ArchMapSourceRef>,
    #[serde(default)]
    pub hashes: Vec<ArchMapArtifactRef>,
    #[serde(default)]
    pub known_blind_spots: Vec<String>,
    pub selection_boundary: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchMapSourceInventoryV0 {
    pub schema_version: String,
    pub inventory_id: String,
    pub root: String,
    #[serde(default)]
    pub included_refs: Vec<ArchMapSourceRef>,
    #[serde(default)]
    pub excluded_refs: Vec<ArchMapSourceRef>,
    #[serde(default)]
    pub unavailable_refs: Vec<ArchMapSourceRef>,
    #[serde(default)]
    pub private_refs: Vec<ArchMapSourceRef>,
    #[serde(default)]
    pub hashes: Vec<ArchMapArtifactRef>,
    #[serde(default)]
    pub known_blind_spots: Vec<String>,
    pub selection_boundary: String,
    #[serde(default)]
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchMapSourceRef {
    #[serde(skip_serializing_if = "Option::is_none")]
    pub artifact_id: Option<String>,
    pub kind: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub path: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub symbol: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub line: Option<usize>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub section: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchMapProvenanceV0 {
    pub observer: String,
    pub observation_method: String,
    pub source_root: String,
    pub observation_boundary: String,
    #[serde(default)]
    pub reviewed_refs: Vec<ArchMapSourceRef>,
    #[serde(default)]
    pub excluded_readings: Vec<String>,
    #[serde(default)]
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchMapAtomObservationV0 {
    pub atom_observation_id: String,
    pub atom_family: String,
    pub predicate: String,
    pub subject_ref: String,
    #[serde(default)]
    pub object_refs: Vec<String>,
    #[serde(default)]
    pub source_refs: Vec<ArchMapSourceRef>,
    pub observation_status: String,
    pub evidence_boundary: String,
    pub confidence: String,
    #[serde(default)]
    pub uncertainty: Vec<String>,
    #[serde(default)]
    pub projection_refs: Vec<String>,
    #[serde(default)]
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchMapMoleculeObservationV0 {
    pub molecule_observation_id: String,
    pub molecule_family: String,
    pub role_name: String,
    #[serde(default)]
    pub atom_observation_refs: Vec<String>,
    #[serde(default)]
    pub source_refs: Vec<ArchMapSourceRef>,
    pub observation_status: String,
    pub evidence_boundary: String,
    pub confidence: String,
    #[serde(default)]
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchMapSemanticObservationV0 {
    pub semantic_observation_id: String,
    pub semantic_family: String,
    pub subject_ref: String,
    pub predicate: String,
    #[serde(default)]
    pub atom_observation_refs: Vec<String>,
    #[serde(default)]
    pub molecule_observation_refs: Vec<String>,
    #[serde(default)]
    pub source_refs: Vec<ArchMapSourceRef>,
    pub observation_status: String,
    pub evidence_boundary: String,
    #[serde(default)]
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchMapProjectionInfoV0 {
    pub projection_id: String,
    pub projection_family: String,
    pub source_observation_ref: String,
    pub target_surface: String,
    pub reading: String,
    pub projection_boundary: String,
    #[serde(default)]
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchMapConcernHintV0 {
    pub concern_hint_id: String,
    pub concern_family: String,
    pub subject_ref: String,
    #[serde(default)]
    pub atom_observation_refs: Vec<String>,
    #[serde(default)]
    pub molecule_observation_refs: Vec<String>,
    #[serde(default)]
    pub semantic_observation_refs: Vec<String>,
    #[serde(default)]
    pub source_refs: Vec<ArchMapSourceRef>,
    pub evidence_boundary: String,
    pub analysis_boundary: String,
    #[serde(default)]
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchMapObservationGapV0 {
    pub gap_id: String,
    pub gap_kind: String,
    pub subject_ref: String,
    pub evidence_status: String,
    pub reason: String,
    #[serde(default)]
    pub expected_atom_families: Vec<String>,
    #[serde(default)]
    pub source_refs: Vec<ArchMapSourceRef>,
    #[serde(default)]
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchMapValidationReportV0 {
    pub schema_version: String,
    pub archmap_ref: String,
    pub lean_preservation_vocabulary: Vec<ArchMapLeanPreservationVocabularyEntry>,
    pub lean_preservation_precondition_checklist: Vec<ArchMapLeanPreservationChecklistEntry>,
    pub source_inventory_checks: Vec<ValidationCheck>,
    pub source_ref_checks: Vec<ValidationCheck>,
    pub claim_boundary_checks: Vec<ValidationCheck>,
    pub semantic_coverage_checks: Vec<ValidationCheck>,
    pub formal_promotion_guardrail_checks: Vec<ValidationCheck>,
    pub atomic_observation_checks: Vec<ValidationCheck>,
    pub atomic_observation_summary: ArchMapAtomicObservationSummary,
    pub responsibility_checks: Vec<ValidationCheck>,
    pub summary: ArchMapValidationSummary,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchMapAtomicObservationSummary {
    pub atom_observation_count: usize,
    pub observed_atom_count: usize,
    pub promotable_atom_observation_count: usize,
    pub rejected_or_uncertain_observation_count: usize,
    pub molecule_observation_count: usize,
    pub observed_molecule_count: usize,
    pub semantic_observation_count: usize,
    pub concern_hint_count: usize,
    pub observation_gap_count: usize,
    pub lean_presentation_candidate_count: usize,
    pub sft_handoff_ref_count: usize,
    pub zero_curvature_reading: String,
    pub promotion_boundary: String,
    pub boundary: String,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchMapValidationSummary {
    pub result: String,
    pub atom_observation_count: usize,
    pub molecule_observation_count: usize,
    pub semantic_observation_count: usize,
    pub observation_gap_count: usize,
    pub failed_check_count: usize,
    pub warning_check_count: usize,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchMapLeanPreservationVocabularyEntry {
    pub vocabulary_id: String,
    pub archmap_selector: String,
    pub lean_package_field: String,
    pub preservation_role: String,
    pub report_boundary: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchMapLeanPreservationChecklistEntry {
    pub checklist_id: String,
    pub lean_package_field: String,
    pub status: String,
    pub candidate_sources: Vec<String>,
    pub blocking_reasons: Vec<String>,
    pub missing_evidence: Vec<String>,
    pub coverage_boundary: String,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct LawPolicyDocumentV0 {
    pub schema_version: String,
    pub law_policy_id: String,
    pub policy_version: String,
    pub scope: String,
    pub archmap_schema_ref: String,
    pub selected_laws: Vec<LawPolicySelectedLawV0>,
    pub required_zero_axes: Vec<LawPolicyAxisDefinitionV0>,
    #[serde(default)]
    pub optional_axes: Vec<LawPolicyAxisDefinitionV0>,
    pub witness_rules: Vec<LawPolicyWitnessRuleV0>,
    #[serde(default)]
    pub molecule_patterns: Vec<LawPolicyMoleculePatternV0>,
    pub obstruction_circuit_definitions: Vec<LawPolicyObstructionCircuitDefinitionV0>,
    pub signature_axis_definitions: Vec<LawPolicySignatureAxisDefinitionV0>,
    pub exactness_assumptions: Vec<String>,
    pub coverage_requirements: Vec<LawPolicyCoverageRequirementV0>,
    #[serde(default)]
    pub excluded_readings: Vec<String>,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct LawPolicySelectedLawV0 {
    pub law_id: String,
    pub law_family: String,
    pub description: String,
    pub enforcement_boundary: String,
    #[serde(default)]
    pub applies_to_atom_families: Vec<String>,
    #[serde(default)]
    pub required_witness_refs: Vec<String>,
    #[serde(default)]
    pub required_axis_refs: Vec<String>,
    #[serde(default)]
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct LawPolicyAxisDefinitionV0 {
    pub axis_id: String,
    pub axis_family: String,
    pub value_type: String,
    pub zero_reading: String,
    pub measurement_boundary: String,
    #[serde(default)]
    pub evidence_requirements: Vec<String>,
    #[serde(default)]
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct LawPolicyWitnessRuleV0 {
    pub witness_rule_id: String,
    pub law_ref: String,
    pub witness_kind: String,
    #[serde(default)]
    pub atom_observation_refs: Vec<String>,
    #[serde(default)]
    pub required_atom_families: Vec<String>,
    #[serde(default)]
    pub molecule_pattern_refs: Vec<String>,
    pub evidence_boundary: String,
    #[serde(default)]
    pub missing_evidence_behavior: String,
    #[serde(default)]
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct LawPolicyMoleculePatternV0 {
    pub molecule_pattern_id: String,
    pub role_name: String,
    #[serde(default)]
    pub required_atom_families: Vec<String>,
    #[serde(default)]
    pub optional_atom_families: Vec<String>,
    pub interpretation_boundary: String,
    #[serde(default)]
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct LawPolicyObstructionCircuitDefinitionV0 {
    pub obstruction_circuit_id: String,
    pub law_ref: String,
    pub witness_rule_ref: String,
    pub circuit_kind: String,
    pub minimality_reading: String,
    pub evidence_boundary: String,
    #[serde(default)]
    pub signature_axis_refs: Vec<String>,
    #[serde(default)]
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct LawPolicySignatureAxisDefinitionV0 {
    pub signature_axis_id: String,
    pub law_ref: String,
    pub axis_ref: String,
    pub valuation_rule: String,
    pub value_type: String,
    pub zero_reading: String,
    pub coverage_boundary: String,
    #[serde(default)]
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct LawPolicyCoverageRequirementV0 {
    pub coverage_requirement_id: String,
    #[serde(default)]
    pub applies_to_law_refs: Vec<String>,
    #[serde(default)]
    pub required_atom_families: Vec<String>,
    #[serde(default)]
    pub required_source_ref_kinds: Vec<String>,
    pub missing_coverage_behavior: String,
    #[serde(default)]
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct LawPolicyValidationReportV0 {
    pub schema_version: String,
    pub input: LawPolicyValidationInputV0,
    pub policy: LawPolicyDocumentV0,
    pub summary: LawPolicyValidationSummaryV0,
    pub checks: Vec<ValidationCheck>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct LawPolicyValidationInputV0 {
    pub schema_version: String,
    pub path: String,
    pub law_policy_id: String,
    pub policy_version: String,
    pub archmap_schema_ref: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct LawPolicyValidationSummaryV0 {
    pub result: String,
    pub selected_law_count: usize,
    pub required_zero_axis_count: usize,
    pub witness_rule_count: usize,
    pub obstruction_circuit_definition_count: usize,
    pub signature_axis_definition_count: usize,
    pub coverage_requirement_count: usize,
    pub failed_check_count: usize,
    pub warning_check_count: usize,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigAnalysisPacketV0 {
    pub schema_version: String,
    pub analysis_id: String,
    pub generated_at: String,
    pub arch_map_ref: ArchSigAnalysisArtifactRefV0,
    pub interpretation_profile_ref: ArchSigAnalysisArtifactRefV0,
    pub selected_law_policy_ref: ArchSigAnalysisArtifactRefV0,
    pub architecture_state: ArchSigArchitectureStateV0,
    pub design_pressure: Vec<ArchSigDesignPressureReadingV0>,
    pub change_impact: ArchSigChangeImpactReadingV0,
    pub aat_concept_surfaces: Vec<ArchSigAatConceptSurfaceV0>,
    pub atom_configuration_summary: ArchSigAtomConfigurationSummaryV0,
    pub architecture_object_projections: Vec<ArchSigArchitectureObjectProjectionV0>,
    pub invariant_family_readings: Vec<ArchSigInvariantFamilyReadingV0>,
    pub law_universe_reading: ArchSigLawUniverseReadingV0,
    pub molecule_readings: Vec<ArchSigMoleculeReadingV0>,
    pub obstruction_circuits: Vec<ArchSigObstructionCircuitV0>,
    pub signature_axes: Vec<ArchSigSignatureAxisReadingV0>,
    pub analytic_representations: Vec<ArchSigAnalyticRepresentationV0>,
    pub coupling_cohesion_readings: Vec<ArchSigCouplingCohesionReadingV0>,
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

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigAnalyticRepresentationV0 {
    pub representation_id: String,
    pub representation_family: String,
    pub status: String,
    pub value_type: String,
    pub value: String,
    pub graph_scope_refs: Vec<String>,
    pub axis_refs: Vec<String>,
    pub reading: String,
    pub coverage_boundary: String,
    pub zero_reflecting_boundary: String,
    pub non_conclusions: Vec<String>,
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
pub struct ArchSigDesignPrincipleReadingV0 {
    pub principle_id: String,
    pub principle: String,
    pub status: String,
    pub aat_reading: String,
    pub invariant_refs: Vec<String>,
    pub obstruction_refs: Vec<String>,
    pub operation_refs: Vec<String>,
    pub evidence_refs: Vec<String>,
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
    pub excluded_readings: Vec<String>,
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
    pub analytic_readings_summary: Vec<String>,
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
    pub packet: ArchSigAnalysisPacketV0,
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
    pub obstruction_circuit_count: usize,
    pub signature_axis_count: usize,
    pub analytic_representation_count: usize,
    pub coupling_cohesion_reading_count: usize,
    pub design_principle_reading_count: usize,
    pub repair_operation_candidate_count: usize,
    pub operation_delta_count: usize,
    pub bounded_judgement_count: usize,
    pub failed_check_count: usize,
    pub warning_check_count: usize,
}
