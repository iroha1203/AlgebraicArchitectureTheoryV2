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
    pub operation_square_evidence: Vec<ArchMapOperationSquareEvidenceV0>,
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
pub struct ArchMapOperationSquareEvidenceV0 {
    pub operation_square_evidence_id: String,
    pub evidence_kind: String,
    pub left_operation_ref: String,
    pub right_operation_ref: String,
    #[serde(default)]
    pub p_operation_sequence: Vec<String>,
    #[serde(default)]
    pub q_operation_sequence: Vec<String>,
    #[serde(default)]
    pub endpoint_object_refs: Vec<String>,
    #[serde(default)]
    pub generator_candidate_refs: Vec<String>,
    #[serde(default)]
    pub shared_endpoint_refs: Vec<String>,
    #[serde(default)]
    pub atom_observation_refs: Vec<String>,
    #[serde(default)]
    pub molecule_observation_refs: Vec<String>,
    #[serde(default)]
    pub semantic_observation_refs: Vec<String>,
    #[serde(default)]
    pub projection_refs: Vec<String>,
    #[serde(default)]
    pub source_refs: Vec<ArchMapSourceRef>,
    pub observation_status: String,
    pub evidence_boundary: String,
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
#[serde(rename_all = "camelCase", deny_unknown_fields)]
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
    pub measurement_policy: LawPolicyMeasurementPolicyV0,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub spectrum_measurement_profile: Option<LawPolicySpectrumMeasurementProfileV0>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub homotopy_measurement_profile: Option<LawPolicyHomotopyMeasurementProfileV0>,
    pub exactness_assumptions: Vec<String>,
    pub coverage_requirements: Vec<LawPolicyCoverageRequirementV0>,
    #[serde(default)]
    pub excluded_readings: Vec<String>,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct LawPolicyMeasurementPolicyV0 {
    pub policy_id: String,
    #[serde(default)]
    pub selected_axis_refs: Vec<String>,
    pub distance_kind: String,
    pub weight_policy: String,
    pub coverage_policy: String,
    #[serde(default)]
    pub arch_map_store_ref_kinds: Vec<String>,
    pub measurement_boundary: String,
    #[serde(default)]
    pub exactness_assumption_refs: Vec<String>,
    #[serde(default)]
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct LawPolicySpectrumMeasurementProfileV0 {
    pub profile_id: String,
    #[serde(default)]
    pub reading_boundary: LawPolicyReadingBoundaryV0,
    #[serde(default)]
    pub selected_axis_refs: Vec<String>,
    #[serde(default)]
    pub measured_witness_rule_refs: Vec<String>,
    #[serde(default)]
    pub distance_kinds: Vec<LawPolicySpectrumDistanceKindV0>,
    pub weight_policy: String,
    pub support_projection_rule: String,
    pub transfer_edge_rule: String,
    #[serde(default)]
    pub clustering_ranking_options: Vec<String>,
    #[serde(default)]
    pub report_focus_options: Vec<String>,
    #[serde(default)]
    pub coverage_requirement_refs: Vec<String>,
    pub coverage_boundary: String,
    #[serde(default)]
    pub exactness_assumption_refs: Vec<String>,
    pub measurement_boundary: String,
    #[serde(default)]
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct LawPolicySpectrumDistanceKindV0 {
    pub axis_ref: String,
    pub distance_kind: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct LawPolicyHomotopyMeasurementProfileV0 {
    pub profile_id: String,
    #[serde(default)]
    pub reading_boundary: LawPolicyReadingBoundaryV0,
    #[serde(default)]
    pub selected_axis_refs: Vec<String>,
    #[serde(default)]
    pub path_discovery_rules: Vec<LawPolicyHomotopyPathDiscoveryRuleV0>,
    #[serde(default)]
    pub filler_rules: Vec<LawPolicyHomotopyFillerRuleV0>,
    pub loop_measurement_policy: LawPolicyHomotopyLoopMeasurementPolicyV0,
    pub continuation_policy: String,
    pub distance_policy: String,
    #[serde(default)]
    pub coverage_requirement_refs: Vec<String>,
    pub coverage_boundary: String,
    #[serde(default)]
    pub exactness_assumption_refs: Vec<String>,
    pub measurement_boundary: String,
    #[serde(default)]
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct LawPolicyReadingBoundaryV0 {
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

impl Default for LawPolicyReadingBoundaryV0 {
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
pub struct LawPolicyHomotopyPathDiscoveryRuleV0 {
    pub rule_id: String,
    pub path_source_kind: String,
    pub endpoint_policy: String,
    pub candidate_source: String,
    pub evidence_boundary: String,
    #[serde(default)]
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct LawPolicyHomotopyFillerRuleV0 {
    pub rule_id: String,
    pub filler_kind: String,
    #[serde(default)]
    pub required_source_ref_kinds: Vec<String>,
    pub missing_filler_behavior: String,
    pub evidence_boundary: String,
    #[serde(default)]
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct LawPolicyHomotopyLoopMeasurementPolicyV0 {
    pub policy_id: String,
    #[serde(default)]
    pub loop_candidate_sources: Vec<String>,
    pub filled_loop_reading: String,
    pub unfilled_loop_reading: String,
    pub holonomy_distance_kind: String,
    pub local_curvature_reading_boundary: String,
    #[serde(default)]
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
    pub obstruction_circuits: Vec<ArchSigObstructionCircuitV0>,
    pub signature_axes: Vec<ArchSigSignatureAxisReadingV0>,
    pub analytic_representations: Vec<ArchSigAnalyticRepresentationV0>,
    pub coupling_cohesion_readings: Vec<ArchSigCouplingCohesionReadingV0>,
    pub workflow_risk_readings: Vec<ArchSigWorkflowRiskReadingV0>,
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
pub struct ArchSigWorkflowRiskReadingV0 {
    pub workflow_risk_id: String,
    pub molecule_observation_ref: String,
    pub molecule_family: String,
    pub role_name: String,
    pub status: String,
    pub risk_score: i64,
    pub risk_tier: String,
    pub atom_count: usize,
    pub atom_family_counts: Vec<ArchSigWorkflowAtomFamilyCountV0>,
    pub semantic_refs: Vec<String>,
    pub concern_refs: Vec<String>,
    pub top_axes: Vec<ArchSigWorkflowRiskAxisReadingV0>,
    pub review_focus: Vec<String>,
    pub coverage_gap_refs: Vec<String>,
    pub evidence_boundary: String,
    pub recommended_next_action: String,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigWorkflowAtomFamilyCountV0 {
    pub atom_family: String,
    pub count: usize,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchSigWorkflowRiskAxisReadingV0 {
    pub axis: String,
    pub status: String,
    pub score: i64,
    pub family_score: i64,
    pub keyword_hits: Vec<String>,
    pub concern_refs: Vec<String>,
    pub coverage_gap_refs: Vec<String>,
    pub reading: String,
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
    pub reading: String,
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
    pub exactness_assumption_status: Vec<ArchSigCoverageStatusV0>,
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
    pub evidence_boundary: String,
    pub non_conclusions: Vec<String>,
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
    pub unresolved_effect_relations: Vec<String>,
    pub effect_ordering_pressure: String,
    pub state_transition_ref: String,
    pub evidence_boundary: String,
    pub recommended_next_action: String,
    pub non_conclusions: Vec<String>,
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
    pub forgotten_coordinates: Vec<String>,
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
pub struct ArchSigStateTransitionAlgebraReadingV0 {
    pub reading_id: String,
    pub generator_refs: Vec<String>,
    pub state_atom_refs: Vec<String>,
    pub effect_atom_refs: Vec<String>,
    pub runtime_atom_refs: Vec<String>,
    pub required_relations: Vec<String>,
    pub unresolved_relations: Vec<String>,
    pub obstruction_refs: Vec<String>,
    pub reading: String,
    pub evidence_boundary: String,
    pub recommended_next_action: String,
    pub non_conclusions: Vec<String>,
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
    pub spectral_readings_summary: Vec<String>,
    pub spectral_mode_summary: Vec<String>,
    pub spectral_drilldown_summary: Vec<String>,
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
    pub workflow_risk_reading_count: usize,
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
    pub bridge_split_obstruction_transfer_reading_count: usize,
    pub representation_strength_reading_count: usize,
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
    pub failed_check_count: usize,
    pub warning_check_count: usize,
}
