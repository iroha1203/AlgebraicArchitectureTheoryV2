use std::collections::BTreeMap;

use serde::{Deserialize, Serialize};

pub const SCHEMA_VERSION: &str = "archsig-sig0-v0";
pub const COMPONENT_KIND: &str = "lean-module";
pub const PYTHON_COMPONENT_KIND: &str = "python-module";
pub const PYTHON_IMPORT_RULE_VERSION: &str = "python-import-graph-v0";
pub const VALIDATION_REPORT_SCHEMA_VERSION: &str = "component-universe-validation-report-v0";
pub const EMPIRICAL_DATASET_SCHEMA_VERSION: &str = "empirical-signature-dataset-v0";
pub const SIGNATURE_SNAPSHOT_STORE_SCHEMA_VERSION: &str = "signature-snapshot-store-v0";
pub const SIGNATURE_DIFF_REPORT_SCHEMA_VERSION: &str = "signature-diff-report-v0";
pub const AIR_SCHEMA_VERSION: &str = "aat-air-v0";
pub const AIR_VALIDATION_REPORT_SCHEMA_VERSION: &str = "aat-air-validation-report-v0";
pub const ARCHMAP_SCHEMA_VERSION: &str = "archmap-observation-map-v0";
pub const ARCHMAP_SOURCE_INVENTORY_SCHEMA_VERSION: &str = "archmap-source-inventory-v0";
pub const ARCHMAP_VALIDATION_REPORT_SCHEMA_VERSION: &str = "archmap-validation-report-v0";
pub const FEATURE_EXTENSION_REPORT_SCHEMA_VERSION: &str = "feature-extension-report-v0";
pub const OBSTRUCTION_WITNESS_SCHEMA_VERSION: &str = "obstruction-witness-v0";
pub const ARCHITECTURE_DRIFT_LEDGER_SCHEMA_VERSION: &str = "architecture-drift-ledger-v0";
pub const DETECTABLE_VALUES_REPORTED_AXES_CATALOG_SCHEMA_VERSION: &str =
    "detectable-values-reported-axes-catalog-v0";
pub const SCHEMA_VERSION_CATALOG_SCHEMA_VERSION: &str = "schema-version-catalog-v0";
pub const SCHEMA_COMPATIBILITY_POLICY_SCHEMA_VERSION: &str = "schema-compatibility-policy-v0";
pub const SCHEMA_COMPATIBILITY_CHECK_REPORT_SCHEMA_VERSION: &str =
    "schema-compatibility-check-report-v0";
pub const THEOREM_PRECONDITION_CHECK_REPORT_SCHEMA_VERSION: &str =
    "theorem-precondition-check-report-v0";
pub const REPAIR_RULE_REGISTRY_SCHEMA_VERSION: &str = "repair-rule-registry-v0";
pub const REPAIR_RULE_REGISTRY_VALIDATION_REPORT_SCHEMA_VERSION: &str =
    "repair-rule-registry-validation-report-v0";
pub const SYNTHESIS_CONSTRAINT_ARTIFACT_SCHEMA_VERSION: &str = "synthesis-constraint-artifact-v0";
pub const SYNTHESIS_CONSTRAINT_VALIDATION_REPORT_SCHEMA_VERSION: &str =
    "synthesis-constraint-validation-report-v0";
pub const NO_SOLUTION_CERTIFICATE_SCHEMA_VERSION: &str = "no-solution-certificate-v0";
pub const NO_SOLUTION_CERTIFICATE_VALIDATION_REPORT_SCHEMA_VERSION: &str =
    "no-solution-certificate-validation-report-v0";
pub const ORGANIZATION_POLICY_SCHEMA_VERSION: &str = "organization-policy-v0";
pub const ORGANIZATION_POLICY_VALIDATION_REPORT_SCHEMA_VERSION: &str =
    "organization-policy-validation-report-v0";
pub const LAW_POLICY_SCHEMA_VERSION: &str = "law-policy-v0";
pub const LAW_POLICY_VALIDATION_REPORT_SCHEMA_VERSION: &str = "law-policy-validation-report-v0";
pub const ARCHSIG_ANALYSIS_PACKET_SCHEMA_VERSION: &str = "archsig-analysis-packet-v0";
pub const ARCHSIG_ANALYSIS_PACKET_VALIDATION_REPORT_SCHEMA_VERSION: &str =
    "archsig-analysis-packet-validation-report-v0";
pub const LAW_POLICY_TEMPLATE_REGISTRY_SCHEMA_VERSION: &str = "law-policy-template-registry-v0";
pub const LAW_POLICY_TEMPLATE_REGISTRY_VALIDATION_REPORT_SCHEMA_VERSION: &str =
    "law-policy-template-registry-validation-report-v0";
pub const ARCHITECTURE_POLICY_SCHEMA_VERSION: &str = "architecture-policy-v0";
pub const ARCHITECTURE_POLICY_VALIDATION_REPORT_SCHEMA_VERSION: &str =
    "architecture-policy-validation-report-v0";
pub const LAW_VIOLATION_REPORT_SCHEMA_VERSION: &str = "law-violation-report-v0";
pub const CUSTOM_RULE_PLUGIN_REGISTRY_SCHEMA_VERSION: &str = "custom-rule-plugin-registry-v0";
pub const CUSTOM_RULE_PLUGIN_REGISTRY_VALIDATION_REPORT_SCHEMA_VERSION: &str =
    "custom-rule-plugin-registry-validation-report-v0";
pub const MEASUREMENT_UNIT_REGISTRY_SCHEMA_VERSION: &str = "measurement-unit-registry-v0";
pub const MEASUREMENT_UNIT_REGISTRY_VALIDATION_REPORT_SCHEMA_VERSION: &str =
    "measurement-unit-registry-validation-report-v0";
pub const POLICY_DECISION_REPORT_SCHEMA_VERSION: &str = "policy-decision-report-v0";
pub const REPORT_ARTIFACT_RETENTION_MANIFEST_SCHEMA_VERSION: &str =
    "report-artifact-retention-manifest-v0";
pub const REPORT_ARTIFACT_RETENTION_VALIDATION_REPORT_SCHEMA_VERSION: &str =
    "report-artifact-retention-validation-report-v0";
pub const PR_COMMENT_SUMMARY_SCHEMA_VERSION: &str = "pr-comment-summary-v0";
pub const BASELINE_SUPPRESSION_REPORT_SCHEMA_VERSION: &str = "baseline-suppression-report-v0";
pub const PR_QUALITY_ANALYSIS_REPORT_SCHEMA_VERSION: &str = "pr-quality-analysis-report-v0";
pub const PR_QUALITY_ANALYSIS_VALIDATION_REPORT_SCHEMA_VERSION: &str =
    "pr-quality-analysis-validation-report-v0";
pub const AAT_OBSERVABLE_BUNDLE_SCHEMA_VERSION: &str = "aat-observable-bundle-v0";
pub const AAT_OBSERVABLE_BUNDLE_VALIDATION_REPORT_SCHEMA_VERSION: &str =
    "aat-observable-bundle-validation-report-v0";
pub const RUNTIME_EDGE_EVIDENCE_SCHEMA_VERSION: &str = "runtime-edge-evidence-v0";
pub const RUNTIME_PROJECTION_RULE_VERSION: &str = "runtime-edge-projection-v0";
pub const FRAMEWORK_ADAPTER_EVIDENCE_SCHEMA_VERSION: &str = "framework-adapter-evidence-v0";
pub const RELATION_COMPLEXITY_CANDIDATE_SCHEMA_VERSION: &str = "relation-complexity-candidates/v0";
pub const RELATION_COMPLEXITY_OBSERVATION_SCHEMA_VERSION: &str =
    "relation-complexity-observation/v0";
pub const RELATION_COMPLEXITY_RULE_SET_VERSION: &str = "relation-complexity-rules/v0";
pub const EXTRACTOR_NAME: &str = "archsig";
pub const EXTRACTOR_VERSION: &str = env!("CARGO_PKG_VERSION");
pub const RULE_SET_VERSION: &str = "sig0-v0";
pub const DEFAULT_UNIVERSE_MODE: &str = "local-only";

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
pub struct SchemaArtifactCompatibilityV0 {
    pub artifact_id: String,
    pub schema_version_name: String,
    pub compatibility_policy_ref: String,
    pub field_mappings: Vec<SchemaFieldMappingV0>,
    pub deprecated_fields: Vec<SchemaDeprecatedFieldV0>,
    pub required_assumptions: Vec<SchemaRequiredAssumptionV0>,
    pub coverage_exactness_boundaries: Vec<SchemaCoverageExactnessBoundaryV0>,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct DetectableValuesReportedAxesCatalogV0 {
    pub schema_version: String,
    pub catalog_id: String,
    pub catalog_version: String,
    pub benchmark_suite_version: String,
    pub frozen_fixtures: Vec<BenchmarkSuiteFixtureV0>,
    pub update_rules: Vec<BenchmarkSuiteUpdateRuleV0>,
    pub axes: Vec<ReportedAxisCatalogEntryV0>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub schema_compatibility: Option<SchemaArtifactCompatibilityV0>,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct BenchmarkSuiteFixtureV0 {
    pub fixture_id: String,
    pub path: String,
    pub artifact_kind: String,
    pub frozen_for: Vec<String>,
    pub expected_boundaries: Vec<String>,
    pub update_rule_refs: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct BenchmarkSuiteUpdateRuleV0 {
    pub rule_id: String,
    pub applies_to: String,
    pub required_review: String,
    pub compatibility_check: String,
    pub non_conclusion: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ReportedAxisCatalogEntryV0 {
    pub axis_id: String,
    pub layer: String,
    pub value_type: String,
    pub reported_in: Vec<String>,
    pub allowed_measurement_boundaries: Vec<String>,
    pub default_measurement_boundary: String,
    pub evidence_requirements: Vec<String>,
    pub theorem_refs: Vec<String>,
    pub compatibility_notes: Vec<String>,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct SchemaFieldMappingV0 {
    pub source_field: String,
    pub target_field: String,
    pub mapping_kind: String,
    pub required_review: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct SchemaDeprecatedFieldV0 {
    pub field: String,
    pub replacement: Option<String>,
    pub removal_phase: String,
    pub reader_behavior: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct SchemaRequiredAssumptionV0 {
    pub assumption_id: String,
    pub applies_to: String,
    pub required_for: String,
    pub fallback_when_missing: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct SchemaCoverageExactnessBoundaryV0 {
    pub axis_or_layer: String,
    pub measurement_boundary: String,
    pub coverage_assumptions: Vec<String>,
    pub exactness_assumptions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct SchemaCompatibilityCheckReportV0 {
    pub schema_version: String,
    pub checker_id: String,
    pub compatibility_policy_ref: String,
    pub before: SchemaCompatibilityArtifactRefV0,
    pub after: SchemaCompatibilityArtifactRefV0,
    pub summary: SchemaCompatibilityCheckSummaryV0,
    pub checks: Vec<SchemaCompatibilityCheckV0>,
    pub field_mappings: Vec<SchemaFieldMappingV0>,
    pub deprecated_fields: Vec<SchemaDeprecatedFieldV0>,
    pub new_required_assumptions: Vec<SchemaRequiredAssumptionV0>,
    pub coverage_exactness_boundaries: Vec<SchemaCoverageExactnessBoundaryV0>,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct SchemaCompatibilityArtifactRefV0 {
    pub path: String,
    pub artifact_id: Option<String>,
    pub schema_version_name: Option<String>,
    pub catalog_status: String,
    pub has_schema_compatibility_metadata: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct SchemaCompatibilityCheckSummaryV0 {
    pub result: String,
    pub compatible_diff_count: usize,
    pub migration_required_count: usize,
    pub blocked_formal_claim_promotion_count: usize,
    pub warning_count: usize,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct SchemaCompatibilityCheckV0 {
    pub id: String,
    pub dimension: String,
    pub result: String,
    pub severity: String,
    pub message: String,
    pub required_action: Option<String>,
    pub non_conclusion: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct Sig0Document {
    pub schema_version: String,
    pub root: String,
    pub component_kind: String,
    pub components: Vec<Component>,
    pub edges: Vec<Edge>,
    pub policies: Policies,
    pub signature: Signature,
    pub metric_status: BTreeMap<String, MetricStatus>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub policy_violations: Vec<PolicyViolation>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub runtime_edge_evidence: Vec<RuntimeEdgeEvidence>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub runtime_dependency_graph: Option<RuntimeDependencyGraphProjection>,
    pub coverage_boundary: String,
    #[serde(default)]
    pub unsupported_constructs: Vec<UnsupportedConstruct>,
    #[serde(default)]
    pub missing_evidence: Vec<String>,
    #[serde(default)]
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Component {
    pub id: String,
    pub path: String,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct Edge {
    pub source: String,
    pub target: String,
    pub kind: String,
    pub evidence: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct Policies {
    pub boundary_allowed: Vec<String>,
    pub abstraction_allowed: Vec<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub policy_id: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub schema_version: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub boundary_group_count: Option<usize>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub abstraction_relation_count: Option<usize>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct Signature {
    pub has_cycle: usize,
    pub scc_max_size: usize,
    pub max_depth: usize,
    pub fanout_risk: usize,
    pub boundary_violation_count: usize,
    pub abstraction_violation_count: usize,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct MetricStatus {
    pub measured: bool,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub reason: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub source: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct PolicyViolation {
    pub axis: String,
    pub source: String,
    pub target: String,
    pub evidence: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub source_group: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub target_group: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub relation_ids: Option<Vec<String>>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct RuntimeEdgeEvidence {
    pub source: String,
    pub target: String,
    pub label: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub failure_mode: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub timeout_budget: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub retry_policy: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub circuit_breaker_coverage: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub confidence: Option<String>,
    pub evidence_location: RuntimeEvidenceLocation,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct RuntimeEvidenceLocation {
    pub path: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub line: Option<usize>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub symbol: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct RuntimeDependencyGraphProjection {
    pub projection_rule: String,
    pub edge_kind: String,
    pub edges: Vec<Edge>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct FrameworkAdapterEvidenceV0 {
    pub schema_version: String,
    pub adapter_id: String,
    pub framework: String,
    pub source_language: String,
    pub component_id_kind: String,
    pub projection_rule: String,
    pub routes: Vec<FrameworkRouteEvidenceV0>,
    pub coverage_assumptions: Vec<String>,
    pub exactness_assumptions: Vec<String>,
    pub unsupported_constructs: Vec<FrameworkUnsupportedConstructV0>,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct FrameworkRouteEvidenceV0 {
    pub route_id: String,
    pub source: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub target: Option<String>,
    pub method: String,
    pub route_path: String,
    pub relation_kind: String,
    pub confidence: String,
    pub evidence_location: RuntimeEvidenceLocation,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct FrameworkUnsupportedConstructV0 {
    pub kind: String,
    pub path: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub line: Option<usize>,
    pub reason: String,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct UnsupportedConstruct {
    pub kind: String,
    pub path: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub line: Option<usize>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub evidence: Option<String>,
    pub reason: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ComponentUniverseValidationReport {
    pub schema_version: String,
    pub input: ValidationInput,
    pub universe_mode: String,
    pub summary: ValidationSummary,
    pub checks: Vec<ValidationCheck>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub warnings: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ValidationInput {
    pub schema_version: String,
    pub path: String,
    pub root: String,
    pub component_kind: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ValidationSummary {
    pub result: String,
    pub component_count: usize,
    pub local_edge_count: usize,
    pub external_edge_count: usize,
    pub failed_check_count: usize,
    pub warning_check_count: usize,
    pub not_measured_check_count: usize,
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

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct EmpiricalDatasetInput {
    pub repository: RepositoryRef,
    pub pull_request: PullRequestRef,
    pub pr_metrics: PullRequestMetrics,
    #[serde(default)]
    pub issue_incident_links: Vec<IssueIncidentLink>,
    #[serde(default)]
    pub analysis_metadata: AnalysisMetadata,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct EmpiricalSignatureDatasetV0 {
    pub schema_version: String,
    pub repository: RepositoryRef,
    pub pull_request: PullRequestRef,
    pub signature_before: SignatureSnapshot,
    pub signature_after: SignatureSnapshot,
    pub delta_signature_signed: NullableSignatureIntVector,
    pub metric_delta_status: BTreeMap<String, MetricDeltaStatus>,
    pub pr_metrics: PullRequestMetrics,
    pub issue_incident_links: Vec<IssueIncidentLink>,
    pub analysis_metadata: AnalysisMetadata,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct RepositoryRef {
    pub owner: String,
    pub name: String,
    pub default_branch: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct PullRequestRef {
    pub number: usize,
    pub author: String,
    pub created_at: String,
    pub merged_at: Option<String>,
    pub base_commit: String,
    pub head_commit: String,
    pub merge_commit: Option<String>,
    pub labels: Vec<String>,
    pub is_bot_generated: bool,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct PullRequestMetrics {
    pub changed_files: usize,
    pub changed_lines_added: usize,
    pub changed_lines_deleted: usize,
    pub changed_components: Vec<String>,
    pub review_comment_count: usize,
    pub review_thread_count: usize,
    pub review_round_count: usize,
    pub first_review_latency_hours: Option<f64>,
    pub approval_latency_hours: Option<f64>,
    pub merge_latency_hours: Option<f64>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct IssueIncidentLink {
    pub kind: String,
    pub id: String,
    pub url: Option<String>,
    pub severity: Option<String>,
    pub labels: Vec<String>,
    pub opened_at: Option<String>,
    pub closed_at: Option<String>,
    pub affected_components: Vec<String>,
    pub rollback: Option<bool>,
    pub reopened: Option<bool>,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct AnalysisMetadata {
    pub signature_after_commit_role: String,
    pub excluded_from_primary_analysis: bool,
    pub exclusion_reasons: Vec<String>,
    pub primary_cost_record: Option<String>,
    pub relation_complexity_components: Option<RelationComplexityComponents>,
    pub runtime_metrics: Option<RuntimeMetrics>,
    pub alternate_signature_after: Option<Box<SignatureSnapshot>>,
}

impl Default for AnalysisMetadata {
    fn default() -> Self {
        Self {
            signature_after_commit_role: "head".to_string(),
            excluded_from_primary_analysis: false,
            exclusion_reasons: Vec::new(),
            primary_cost_record: None,
            relation_complexity_components: None,
            runtime_metrics: None,
            alternate_signature_after: None,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct RuntimeMetrics {
    pub runtime_graph_measured: bool,
    pub runtime_edge_evidence_count: Option<usize>,
    pub runtime_pair_count: Option<usize>,
    pub runtime_fanout: Option<usize>,
    pub unprotected_runtime_propagation_radius: Option<usize>,
    pub circuit_breaker_coverage_ratio: Option<f64>,
    pub protected_pair_count: Option<usize>,
    pub partial_pair_count: Option<usize>,
    pub unprotected_pair_count: Option<usize>,
    pub unknown_coverage_pair_count: Option<usize>,
    pub failure_mode_taxonomy_version: Option<String>,
    pub coverage_policy_version: Option<String>,
    pub confidence_threshold: Option<f64>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct RelationComplexityComponents {
    pub constraints: usize,
    pub compensations: usize,
    pub projections: usize,
    pub failure_transitions: usize,
    pub idempotency_requirements: usize,
}

impl RelationComplexityComponents {
    pub(crate) fn relation_complexity(&self) -> usize {
        self.constraints
            + self.compensations
            + self.projections
            + self.failure_transitions
            + self.idempotency_requirements
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct RelationComplexityCandidateFile {
    pub schema_version: String,
    pub repository: String,
    pub revision: String,
    pub measurement_universe: RelationComplexityMeasurementUniverse,
    pub workflow: RelationComplexityWorkflow,
    #[serde(default)]
    pub evidence: Vec<RelationComplexityEvidence>,
    #[serde(default)]
    pub evidence_candidates: Vec<RelationComplexityEvidence>,
    #[serde(default)]
    pub excluded_evidence: Vec<RelationComplexityExcludedEvidence>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct RelationComplexityObservation {
    pub schema_version: String,
    pub repository: String,
    pub revision: String,
    pub measurement_universe: RelationComplexityMeasurementUniverse,
    pub workflow: RelationComplexityWorkflow,
    pub counts: RelationComplexityComponents,
    pub relation_complexity: usize,
    pub evidence: Vec<RelationComplexityEvidence>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub excluded_evidence: Vec<RelationComplexityExcludedEvidence>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct RelationComplexityMeasurementUniverse {
    pub root: String,
    pub languages: Vec<String>,
    pub frameworks: Vec<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub rule_set_version: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct RelationComplexityWorkflow {
    pub id: String,
    pub name: String,
    pub component: String,
    pub entrypoints: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct RelationComplexityEvidence {
    pub id: String,
    pub path: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub symbol: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub line: Option<usize>,
    pub tags: Vec<String>,
    pub ownership: String,
    pub review_status: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub notes: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct RelationComplexityExcludedEvidence {
    pub path: String,
    pub reason: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub symbol: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub line: Option<usize>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct GitCommitRef {
    pub sha: String,
    pub role: String,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct SignatureSnapshot {
    pub commit: GitCommitRef,
    pub extractor: ExtractorRef,
    pub signature: ArchitectureSignatureV1DatasetShape,
    pub metric_status: BTreeMap<String, MetricStatus>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ExtractorRef {
    pub name: String,
    pub version: String,
    pub rule_set_version: String,
    pub policy_version: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchitectureSignatureV1DatasetShape {
    pub has_cycle: usize,
    pub scc_max_size: usize,
    pub max_depth: usize,
    pub fanout_risk: usize,
    pub boundary_violation_count: usize,
    pub abstraction_violation_count: usize,
    pub scc_excess_size: usize,
    pub max_fanout: usize,
    pub reachable_cone_size: usize,
    pub weighted_scc_risk: Option<usize>,
    pub projection_soundness_violation: Option<usize>,
    pub lsp_violation_count: Option<usize>,
    pub nilpotency_index: Option<usize>,
    pub runtime_propagation: Option<usize>,
    pub relation_complexity: Option<usize>,
    pub empirical_change_cost: Option<usize>,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct SignatureSnapshotStoreRecordV0 {
    pub schema_version: String,
    pub repository: SnapshotRepositoryRef,
    pub revision: RepositoryRevisionRef,
    pub scan: ScanMetadata,
    pub extractor: SnapshotExtractorMetadata,
    pub policy: SnapshotPolicyMetadata,
    pub signature: ArchitectureSignatureV1DatasetShape,
    pub metric_status: BTreeMap<String, MetricStatus>,
    pub validation_summary: SnapshotValidationSummary,
    pub artifacts: SnapshotArtifacts,
    pub analysis_metadata: SnapshotAnalysisMetadata,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct SnapshotRepositoryRef {
    pub owner: String,
    pub name: String,
    pub default_branch: String,
    pub remote_url: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct RepositoryRevisionRef {
    pub sha: String,
    #[serde(rename = "ref")]
    pub ref_name: Option<String>,
    pub branch: Option<String>,
    pub committed_at: Option<String>,
    pub parent_shas: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ScanMetadata {
    pub scanned_at: String,
    pub scanner_id: Option<String>,
    pub trigger: String,
    pub root: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct SnapshotExtractorMetadata {
    pub name: String,
    pub version: String,
    pub rule_set_version: String,
    pub input_schema_version: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct SnapshotPolicyMetadata {
    pub policy_id: Option<String>,
    pub schema_version: Option<String>,
    pub version: Option<String>,
    pub source_path: Option<String>,
    pub content_hash: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct SnapshotValidationSummary {
    pub schema_version: Option<String>,
    pub result: String,
    pub universe_mode: Option<String>,
    pub failed_check_count: Option<usize>,
    pub warning_check_count: Option<usize>,
    pub not_measured_check_count: Option<usize>,
    pub report_path: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct SnapshotArtifacts {
    pub extractor_output_path: Option<String>,
    pub validation_report_path: Option<String>,
    pub policy_path: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct SnapshotAnalysisMetadata {
    pub excluded_from_primary_diff: bool,
    pub exclusion_reasons: Vec<String>,
    pub tags: Vec<String>,
    pub notes: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SnapshotRecordInput {
    pub repository: SnapshotRepositoryRef,
    pub revision: RepositoryRevisionRef,
    pub scan: ScanMetadata,
    pub policy_version: Option<String>,
    pub policy_source_path: Option<String>,
    pub policy_content_hash: Option<String>,
    pub extractor_output_path: Option<String>,
    pub validation_report_path: Option<String>,
    pub tags: Vec<String>,
    pub notes: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct SignatureDiffReportV0 {
    pub schema_version: String,
    pub before: SnapshotDiffEndpoint,
    pub after: SnapshotDiffEndpoint,
    pub comparison_status: SnapshotComparisonStatus,
    pub delta_signature_signed: NullableSignatureIntVector,
    pub metric_delta_status: BTreeMap<String, MetricDeltaStatus>,
    pub worsened_axes: Vec<SignatureAxisChange>,
    pub improved_axes: Vec<SignatureAxisChange>,
    pub unchanged_axes: Vec<SignatureAxisChange>,
    pub unmeasured_axes: Vec<UnmeasuredAxisDelta>,
    pub evidence_diff: SnapshotEvidenceDiff,
    pub attribution: SnapshotDiffAttribution,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct AirDocumentV0 {
    pub schema_version: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub schema_compatibility: Option<SchemaArtifactCompatibilityV0>,
    pub architecture_id: String,
    pub ids: AirIdPolicies,
    pub revision: AirRevision,
    pub feature: AirFeature,
    pub artifacts: Vec<AirArtifact>,
    pub evidence: Vec<AirEvidence>,
    pub components: Vec<AirComponent>,
    pub relations: Vec<AirRelation>,
    pub policies: AirPolicies,
    pub semantic_diagrams: Vec<AirSemanticDiagram>,
    pub architecture_paths: Vec<AirArchitecturePath>,
    pub homotopy_generators: Vec<AirHomotopyGenerator>,
    pub nonfillability_witnesses: Vec<AirNonfillabilityWitness>,
    pub signature: AirSignature,
    pub coverage: AirCoverage,
    pub claims: Vec<AirClaim>,
    pub operation_trace: AirOperationTrace,
    pub extension: AirExtension,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct AirIdPolicies {
    pub component_id_policy: String,
    pub relation_id_policy: String,
    pub evidence_id_policy: String,
    pub claim_id_policy: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct AirRevision {
    pub before: Option<String>,
    pub after: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct AirFeature {
    pub feature_id: Option<String>,
    pub title: Option<String>,
    pub description: Option<String>,
    pub source: String,
    pub ai_session: Option<AirAiSession>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct AirAiSession {
    pub provider: Option<String>,
    pub model: Option<String>,
    pub prompt_ref: Option<String>,
    pub generated_patch: Option<bool>,
    pub human_reviewed: Option<bool>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct AirArtifact {
    pub artifact_id: String,
    pub kind: String,
    pub schema_version: Option<String>,
    pub path: Option<String>,
    pub content_hash: Option<String>,
    pub produced_by: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct AirEvidence {
    pub evidence_id: String,
    pub kind: String,
    pub artifact_ref: Option<String>,
    pub path: Option<String>,
    pub symbol: Option<String>,
    pub line: Option<usize>,
    pub rule_id: Option<String>,
    pub confidence: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct AirComponent {
    pub id: String,
    pub kind: String,
    pub lifecycle: String,
    pub owner: Option<String>,
    pub evidence_refs: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct AirRelation {
    pub id: String,
    pub layer: String,
    #[serde(rename = "from")]
    pub from_component: Option<String>,
    #[serde(rename = "to")]
    pub to_component: Option<String>,
    pub kind: String,
    pub lifecycle: String,
    pub protected_by: Option<String>,
    pub extraction_rule: Option<String>,
    pub evidence_refs: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct AirPolicies {
    pub laws: Vec<String>,
    pub boundaries: Vec<String>,
    pub allowed_edges: Vec<String>,
    pub forbidden_edges: Vec<String>,
    pub abstraction_rules: Vec<String>,
    pub protection_rules: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct AirSemanticDiagram {
    pub id: String,
    pub lhs_path_ref: String,
    pub rhs_path_ref: String,
    pub equivalence: String,
    pub filler_claim_ref: Option<String>,
    pub nonfillability_witness_refs: Vec<String>,
    pub observation_refs: Vec<String>,
    pub lifecycle: String,
    pub evidence_refs: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct AirArchitecturePath {
    pub path_id: String,
    pub source_state: String,
    pub target_state: String,
    pub steps: Vec<String>,
    pub lifecycle: String,
    pub evidence_refs: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct AirHomotopyGenerator {
    pub generator_id: String,
    pub kind: String,
    pub diagram_refs: Vec<String>,
    pub preserves_observation_claim_refs: Vec<String>,
    pub evidence_refs: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct AirNonfillabilityWitness {
    pub witness_id: String,
    pub diagram_ref: String,
    pub witness_kind: String,
    pub claim_ref: String,
    pub evidence_refs: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct AirSignature {
    pub axes: Vec<AirSignatureAxis>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct AirSignatureAxis {
    pub axis: String,
    pub value: Option<i64>,
    pub measured: bool,
    pub measurement_boundary: String,
    pub source: Option<String>,
    pub reason: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct AirCoverage {
    pub layers: Vec<AirCoverageLayer>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct AirCoverageLayer {
    pub layer: String,
    pub measurement_boundary: String,
    pub universe_refs: Vec<String>,
    pub measured_axes: Vec<String>,
    pub unmeasured_axes: Vec<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub projection_rule: Option<String>,
    pub extraction_scope: Vec<String>,
    pub exactness_assumptions: Vec<String>,
    pub unsupported_constructs: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct AirClaim {
    pub claim_id: String,
    pub subject_ref: String,
    pub predicate: String,
    pub claim_level: String,
    pub claim_classification: String,
    pub measurement_boundary: String,
    pub theorem_refs: Vec<String>,
    pub evidence_refs: Vec<String>,
    pub required_assumptions: Vec<String>,
    pub coverage_assumptions: Vec<String>,
    pub exactness_assumptions: Vec<String>,
    pub missing_preconditions: Vec<String>,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct AirOperationTrace {
    pub operations: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
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
    #[serde(default, skip_serializing_if = "ArchMapTargetUniverse::is_empty")]
    pub target_universe: ArchMapTargetUniverse,
    #[serde(default, skip_serializing_if = "ArchMapHomomorphismV0::is_empty")]
    pub homomorphism: ArchMapHomomorphismV0,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub atom_candidates: Vec<ArchMapAtomCandidateV0>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub molecule_candidates: Vec<ArchMapMoleculeCandidateV0>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub obstruction_circuit_candidates: Vec<ArchMapObstructionCircuitCandidateV0>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub map_items: Vec<ArchMapMapItem>,
    #[serde(default, skip_serializing_if = "ArchMapCoverage::is_empty")]
    pub coverage: ArchMapCoverage,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub conflicts: Vec<ArchMapConflict>,
    #[serde(default)]
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchMapHomomorphismV0 {
    #[serde(default)]
    pub reading: String,
    #[serde(default)]
    pub domain: ArchMapHomomorphismUniverseV0,
    #[serde(default)]
    pub codomain: ArchMapHomomorphismUniverseV0,
    #[serde(default)]
    pub object_map: Vec<ArchMapHomomorphismMapEntryV0>,
    #[serde(default)]
    pub relation_map: Vec<ArchMapHomomorphismMapEntryV0>,
    #[serde(default)]
    pub law_map: Vec<ArchMapHomomorphismMapEntryV0>,
    #[serde(default)]
    pub obstruction_map: Vec<ArchMapHomomorphismMapEntryV0>,
    #[serde(default)]
    pub signature_axis_map: Vec<ArchMapHomomorphismMapEntryV0>,
    #[serde(default)]
    pub preservation_claims: Vec<ArchMapHomomorphismPreservationClaimV0>,
    #[serde(default)]
    pub forgetful_boundary: Vec<String>,
    #[serde(default)]
    pub unmeasured_boundary: Vec<String>,
    #[serde(default)]
    pub unsupported_boundary: Vec<String>,
    #[serde(default)]
    pub non_conclusions: Vec<String>,
}

impl ArchMapHomomorphismV0 {
    pub fn is_empty(&self) -> bool {
        self.reading.is_empty()
            && self.object_map.is_empty()
            && self.relation_map.is_empty()
            && self.law_map.is_empty()
            && self.obstruction_map.is_empty()
            && self.signature_axis_map.is_empty()
            && self.preservation_claims.is_empty()
            && self.forgetful_boundary.is_empty()
            && self.unmeasured_boundary.is_empty()
            && self.unsupported_boundary.is_empty()
            && self.non_conclusions.is_empty()
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchMapHomomorphismUniverseV0 {
    #[serde(default)]
    pub universe_id: String,
    #[serde(default)]
    pub description: String,
    #[serde(default)]
    pub refs: Vec<String>,
    #[serde(default)]
    pub boundary: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchMapHomomorphismMapEntryV0 {
    pub map_entry_id: String,
    pub map_family: String,
    pub source_ref: String,
    pub target_ref: String,
    #[serde(default)]
    pub preserves: Vec<String>,
    #[serde(default)]
    pub forgets: Vec<String>,
    pub measurement_boundary: String,
    pub claim_classification: String,
    #[serde(default)]
    pub evidence_refs: Vec<String>,
    #[serde(default)]
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchMapHomomorphismPreservationClaimV0 {
    pub claim_id: String,
    pub map_entry_ref: String,
    pub preserved_structure: String,
    pub status: String,
    pub boundary: String,
    #[serde(default)]
    pub missing_evidence: Vec<String>,
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
pub struct ArchMapTargetUniverse {
    #[serde(default)]
    pub representation: String,
    #[serde(default)]
    pub selected_layers: Vec<String>,
}

impl ArchMapTargetUniverse {
    pub fn is_empty(&self) -> bool {
        self.representation.is_empty() && self.selected_layers.is_empty()
    }
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
pub struct ArchMapMapItem {
    pub map_item_id: String,
    pub mapping_kind: String,
    #[serde(default)]
    pub source_refs: Vec<ArchMapSourceRef>,
    pub target_ref: ArchMapTargetRef,
    #[serde(default)]
    pub preserves: Vec<String>,
    #[serde(default)]
    pub forgets: Vec<String>,
    pub claim_classification: String,
    pub measurement_boundary: String,
    pub confidence: String,
    #[serde(default)]
    pub evidence_refs: Vec<String>,
    #[serde(default)]
    pub theorem_refs: Vec<String>,
    #[serde(default)]
    pub required_assumptions: Vec<String>,
    #[serde(default)]
    pub missing_evidence: Vec<String>,
    #[serde(default)]
    pub non_conclusions: Vec<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub conflict_category: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub semantic_role: Option<String>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub responsibility_regions: Vec<String>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub reason_to_change: Vec<String>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub actor_refs: Vec<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub allowed_role: Option<String>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub law_refs: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchMapAtomCandidateV0 {
    pub atom_candidate_id: String,
    pub atom_family: String,
    pub predicate: String,
    pub subject_ref: String,
    #[serde(default)]
    pub object_refs: Vec<String>,
    #[serde(default)]
    pub source_refs: Vec<ArchMapSourceRef>,
    pub observation_status: String,
    pub measurement_boundary: String,
    pub confidence: String,
    #[serde(default)]
    pub uncertainty: Vec<String>,
    #[serde(default)]
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchMapMoleculeCandidateV0 {
    pub molecule_candidate_id: String,
    pub molecule_kind: String,
    pub role_name: String,
    #[serde(default)]
    pub atom_candidate_refs: Vec<String>,
    #[serde(default)]
    pub source_refs: Vec<ArchMapSourceRef>,
    pub observation_status: String,
    pub confidence: String,
    #[serde(default)]
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchMapObstructionCircuitCandidateV0 {
    pub circuit_candidate_id: String,
    pub circuit_kind: String,
    pub law_ref: String,
    #[serde(default)]
    pub atom_candidate_refs: Vec<String>,
    #[serde(default)]
    pub molecule_candidate_refs: Vec<String>,
    #[serde(default)]
    pub source_refs: Vec<ArchMapSourceRef>,
    pub observation_status: String,
    pub measurement_boundary: String,
    pub claim_boundary: String,
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

#[derive(Debug, Clone, PartialEq, Eq, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchMapTargetRef {
    pub kind: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub layer: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub id: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub from: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub to: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub subject_ref: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub predicate: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub lhs_path_ref: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub rhs_path_ref: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub equivalence: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchMapCoverage {
    #[serde(default)]
    pub measured_layers: Vec<String>,
    #[serde(default)]
    pub unmeasured_layers: Vec<String>,
    #[serde(default)]
    pub assumed_layers: Vec<String>,
    #[serde(default)]
    pub unsupported_constructs: Vec<String>,
}

impl ArchMapCoverage {
    pub fn is_empty(&self) -> bool {
        self.measured_layers.is_empty()
            && self.unmeasured_layers.is_empty()
            && self.assumed_layers.is_empty()
            && self.unsupported_constructs.is_empty()
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchMapConflict {
    pub conflict_id: String,
    pub category: String,
    pub subject_ref: String,
    pub description: String,
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
    pub conflict_checks: Vec<ValidationCheck>,
    pub formal_promotion_guardrail_checks: Vec<ValidationCheck>,
    pub homomorphism_diagnostics: ArchMapHomomorphismDiagnosticsV0,
    #[serde(default)]
    pub atomic_observation_checks: Vec<ValidationCheck>,
    #[serde(default)]
    pub atomic_observation_summary: ArchMapAtomicObservationSummary,
    #[serde(default)]
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
pub struct ArchMapHomomorphismDiagnosticsV0 {
    pub classification: String,
    pub reading: String,
    pub domain_ref: String,
    pub codomain_ref: String,
    pub map_family_summaries: Vec<ArchMapHomomorphismFamilySummaryV0>,
    pub preservation_failures: Vec<String>,
    pub forgetful_boundaries: Vec<String>,
    pub unmeasured_boundaries: Vec<String>,
    pub unsupported_boundaries: Vec<String>,
    pub obstruction_refs: Vec<String>,
    pub signature_axis_refs: Vec<String>,
    pub next_evidence: Vec<String>,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchMapHomomorphismFamilySummaryV0 {
    pub map_family: String,
    pub entry_count: usize,
    pub measured_count: usize,
    pub unmeasured_count: usize,
    pub assumed_count: usize,
    pub lossy_count: usize,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchMapValidationSummary {
    pub result: String,
    pub map_item_count: usize,
    pub homomorphism_classification: String,
    pub conflict_count: usize,
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
    #[serde(skip_serializing_if = "Option::is_none")]
    pub map_item_id: Option<String>,
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
pub struct AirExtension {
    pub embedding_claim_ref: Option<String>,
    pub feature_view_claim_ref: Option<String>,
    pub interaction_claim_refs: Vec<String>,
    pub split_claim_ref: Option<String>,
    pub split_status: String,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AirDocumentInput {
    pub sig0_path: String,
    pub validation_path: Option<String>,
    pub diff_path: Option<String>,
    pub pr_metadata_path: Option<String>,
    pub law_policy_path: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct AirValidationReport {
    pub schema_version: String,
    pub input: AirValidationInput,
    pub summary: AirValidationSummary,
    pub checks: Vec<ValidationCheck>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub warnings: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct AirValidationInput {
    pub schema_version: String,
    pub path: String,
    pub architecture_id: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct AirValidationSummary {
    pub result: String,
    pub component_count: usize,
    pub relation_count: usize,
    pub evidence_count: usize,
    pub claim_count: usize,
    pub failed_check_count: usize,
    pub warning_check_count: usize,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct FeatureExtensionReportV0 {
    pub schema_version: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub schema_compatibility: Option<SchemaArtifactCompatibilityV0>,
    pub input: FeatureReportInput,
    pub architecture_id: String,
    pub revision: AirRevision,
    pub feature: AirFeature,
    pub review_summary: FeatureReportReviewSummary,
    pub architecture_summary: FeatureReportArchitectureSummary,
    pub homomorphism_summary: FeatureReportHomomorphismSummary,
    #[serde(default)]
    pub runtime_summary: FeatureReportRuntimeSummary,
    pub interpreted_extension: FeatureReportInterpretedExtension,
    pub generated_patch_summary: FeatureReportGeneratedPatchSummary,
    pub split_status: String,
    pub preserved_invariants: Vec<FeatureReportInvariant>,
    pub changed_invariants: Vec<FeatureReportInvariant>,
    pub introduced_obstruction_witnesses: Vec<FeatureReportObstructionWitness>,
    pub eliminated_obstruction_witnesses: Vec<FeatureReportObstructionWitness>,
    pub complexity_transfer_candidates: Vec<String>,
    pub semantic_path_summary: FeatureReportSemanticPathSummary,
    pub theorem_package_refs: Vec<String>,
    pub theorem_precondition_summary: TheoremPreconditionCheckSummary,
    pub theorem_precondition_checks: Vec<TheoremPreconditionCheck>,
    pub discharged_assumptions: Vec<String>,
    pub undischarged_assumptions: Vec<String>,
    pub coverage_gaps: Vec<FeatureReportCoverageGap>,
    pub unsupported_constructs: Vec<String>,
    pub repair_suggestions: Vec<FeatureReportRepairSuggestion>,
    pub empirical_annotations: Vec<String>,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct FeatureReportHomomorphismSummary {
    pub classification: String,
    pub domain: String,
    pub codomain: String,
    pub map_families: Vec<FeatureReportHomomorphismFamily>,
    pub preserved_structure_refs: Vec<String>,
    pub obstruction_refs: Vec<String>,
    pub forgetful_boundaries: Vec<String>,
    pub unmeasured_boundaries: Vec<String>,
    pub unsupported_boundaries: Vec<String>,
    pub next_evidence: Vec<String>,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct FeatureReportHomomorphismFamily {
    pub map_family: String,
    pub entry_count: usize,
    pub measured_count: usize,
    pub unmeasured_count: usize,
    pub lossy_count: usize,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct FeatureReportInput {
    pub schema_version: String,
    pub path: String,
    pub architecture_id: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct FeatureReportReviewSummary {
    pub split_status: String,
    pub claim_classification: String,
    pub top_witnesses: Vec<String>,
    pub required_action: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct FeatureReportArchitectureSummary {
    pub component_count: usize,
    pub relation_count: usize,
    pub static_relation_count: usize,
    pub runtime_relation_count: usize,
    pub policy_relation_count: usize,
    pub semantic_diagram_count: usize,
    pub measured_axes: Vec<String>,
    pub unmeasured_axes: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct FeatureReportRuntimeSummary {
    pub relation_count: usize,
    pub measurement_boundary: String,
    pub runtime_propagation: Option<i64>,
    pub interpretation: String,
    pub measured_axes: Vec<String>,
    pub unmeasured_axes: Vec<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub projection_rule: Option<String>,
    pub extraction_scope: Vec<String>,
    pub exactness_assumptions: Vec<String>,
    pub coverage_gaps: Vec<String>,
    pub claim_refs: Vec<String>,
    pub claim_classifications: Vec<String>,
    pub non_conclusions: Vec<String>,
}

impl Default for FeatureReportRuntimeSummary {
    fn default() -> Self {
        Self {
            relation_count: 0,
            measurement_boundary: "unmeasured".to_string(),
            runtime_propagation: None,
            interpretation: "runtimePropagation is unmeasured".to_string(),
            measured_axes: Vec::new(),
            unmeasured_axes: Vec::new(),
            projection_rule: None,
            extraction_scope: Vec::new(),
            exactness_assumptions: Vec::new(),
            coverage_gaps: Vec::new(),
            claim_refs: Vec::new(),
            claim_classifications: Vec::new(),
            non_conclusions: vec!["runtime risk zero is not concluded".to_string()],
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct FeatureReportInterpretedExtension {
    pub embedding_claim_ref: Option<String>,
    pub feature_view_claim_ref: Option<String>,
    pub interaction_claim_refs: Vec<String>,
    pub split_claim_ref: Option<String>,
    pub added_components: Vec<String>,
    pub changed_components: Vec<String>,
    pub added_relations: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct FeatureReportGeneratedPatchSummary {
    pub is_ai_session: bool,
    pub generated_patch: bool,
    pub human_reviewed: Option<bool>,
    pub provider: Option<String>,
    pub model: Option<String>,
    pub prompt_ref: Option<String>,
    pub artifact_refs: Vec<String>,
    pub evidence: Vec<FeatureReportEvidenceRef>,
    pub operations: Vec<FeatureReportGeneratedPatchOperation>,
    #[serde(default)]
    pub review_warnings: Vec<FeatureReportGeneratedPatchReviewWarning>,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct FeatureReportGeneratedPatchOperation {
    pub operation_ref: String,
    pub added_components: Vec<String>,
    pub added_relations: Vec<FeatureReportEdgeRef>,
    pub policy_touches: Vec<String>,
    pub evidence: Vec<FeatureReportEvidenceRef>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct FeatureReportGeneratedPatchReviewWarning {
    pub warning_id: String,
    pub warning_kind: String,
    pub classification: String,
    pub review_signal: String,
    pub measurement_boundary: String,
    pub components: Vec<String>,
    pub relations: Vec<FeatureReportEdgeRef>,
    pub operation_refs: Vec<String>,
    pub evidence: Vec<FeatureReportEvidenceRef>,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct FeatureReportInvariant {
    pub invariant: String,
    pub axis: String,
    pub value: Option<i64>,
    pub measurement_boundary: String,
    pub evidence_refs: Vec<String>,
    pub claim_refs: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct FeatureReportObstructionWitness {
    pub witness_id: String,
    pub layer: String,
    pub kind: String,
    pub extension_role: Vec<String>,
    pub extension_classification: Vec<String>,
    pub components: Vec<String>,
    pub edges: Vec<FeatureReportEdgeRef>,
    pub paths: Vec<String>,
    pub diagrams: Vec<String>,
    pub nonfillability_witness_ref: Option<String>,
    pub operation: Option<String>,
    pub evidence: Vec<FeatureReportEvidenceRef>,
    pub theorem_reference: Vec<String>,
    pub claim_level: String,
    pub claim_classification: String,
    pub measurement_boundary: String,
    pub non_conclusions: Vec<String>,
    pub repair_candidates: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ObstructionWitnessArtifactV0 {
    pub schema_version: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub schema_compatibility: Option<SchemaArtifactCompatibilityV0>,
    pub witness: FeatureReportObstructionWitness,
    pub versioning: ObstructionWitnessVersioningV0,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ObstructionWitnessVersioningV0 {
    pub target_fields: Vec<String>,
    pub compatibility_boundaries: Vec<String>,
    pub evidence_state_policy: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct FeatureReportRepairSuggestion {
    pub suggestion_id: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub repair_rule_id: Option<String>,
    pub source_witness_refs: Vec<String>,
    pub source_coverage_gap_refs: Vec<String>,
    pub target_witness_kind: String,
    pub proposed_operation: String,
    pub required_preconditions: Vec<String>,
    pub expected_effect: String,
    pub preserved_invariants: Vec<String>,
    pub possible_side_effects: Vec<String>,
    pub proof_obligation_refs: Vec<String>,
    pub patch_strategy: String,
    pub confidence: String,
    pub traceability: Vec<String>,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct FeatureReportEdgeRef {
    pub relation_id: String,
    pub from: Option<String>,
    pub to: Option<String>,
    pub kind: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct FeatureReportEvidenceRef {
    pub evidence_ref: String,
    pub kind: Option<String>,
    pub artifact_ref: Option<String>,
    pub path: Option<String>,
    pub symbol: Option<String>,
    pub rule_id: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchitectureDriftLedgerV0 {
    pub schema_version: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub schema_compatibility: Option<SchemaArtifactCompatibilityV0>,
    pub ledger_id: String,
    pub generated_at: String,
    pub baseline_ref: Option<String>,
    pub retention_manifest_ref: Option<String>,
    pub suppression_workflow_refs: Vec<String>,
    pub entries: Vec<ArchitectureDriftLedgerEntryV0>,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchitectureDriftLedgerEntryV0 {
    pub ledger_entry_id: String,
    pub observed_at: String,
    pub architecture_id: String,
    pub revision_ref: Option<String>,
    pub subject_ref: String,
    pub witness_fingerprint: Option<String>,
    pub policy_ref: Option<String>,
    pub aggregation_window: DriftLedgerAggregationWindowV0,
    pub source: DriftLedgerSourceV0,
    pub metric_id: String,
    pub layer: String,
    pub measured_value: Option<serde_json::Value>,
    pub measurement_boundary: String,
    pub evidence_refs: Vec<String>,
    pub confidence: String,
    pub introduced_by_pr: Option<String>,
    pub first_seen_at: Option<String>,
    pub last_seen_at: Option<String>,
    pub owner: Option<String>,
    pub status: String,
    pub suppression: Option<DriftLedgerSuppressionV0>,
    pub repair_candidates: Vec<String>,
    pub linked_witness_refs: Vec<String>,
    pub linked_claim_refs: Vec<String>,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct DriftLedgerAggregationWindowV0 {
    pub window_start: Option<String>,
    pub window_end: Option<String>,
    pub window_kind: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct DriftLedgerSourceV0 {
    pub kind: String,
    #[serde(rename = "ref")]
    pub reference: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct DriftLedgerSuppressionV0 {
    pub reason: Option<String>,
    pub approved_by: Option<String>,
    pub approved_at: Option<String>,
    pub expires_at: Option<String>,
    pub scope: Option<String>,
    pub policy_ref: Option<String>,
    pub witness_ref: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct FeatureReportSemanticPathSummary {
    pub path_count: usize,
    pub diagram_count: usize,
    pub nonfillability_witness_count: usize,
    pub representative_path_ids: Vec<String>,
    pub representative_diagram_ids: Vec<String>,
    pub representative_nonfillability_witness_ids: Vec<String>,
    pub measurement_boundary: String,
    pub measured_axes: Vec<String>,
    pub unmeasured_axes: Vec<String>,
    pub evidence_kinds: Vec<String>,
    pub diagrams: Vec<FeatureReportSemanticDiagramSummary>,
    pub nonfillability_witnesses: Vec<FeatureReportSemanticNonfillabilityWitnessSummary>,
    pub extraction_scope: Vec<String>,
    pub exactness_assumptions: Vec<String>,
    pub unsupported_constructs: Vec<String>,
    pub missing_preconditions: Vec<String>,
    pub coverage_gaps: Vec<String>,
    pub claim_refs: Vec<String>,
    pub claim_classifications: Vec<String>,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct FeatureReportSemanticDiagramSummary {
    pub diagram_id: String,
    pub lhs_path_ref: String,
    pub rhs_path_ref: String,
    pub equivalence: String,
    pub filler_claim_ref: Option<String>,
    pub nonfillability_witness_refs: Vec<String>,
    pub observation_refs: Vec<String>,
    pub evidence: Vec<FeatureReportEvidenceRef>,
    pub claim_refs: Vec<String>,
    pub claim_classifications: Vec<String>,
    pub theorem_reference: Vec<String>,
    pub missing_preconditions: Vec<String>,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct FeatureReportSemanticNonfillabilityWitnessSummary {
    pub witness_id: String,
    pub diagram_ref: String,
    pub witness_kind: String,
    pub claim_ref: String,
    pub evidence: Vec<FeatureReportEvidenceRef>,
    pub theorem_reference: Vec<String>,
    pub claim_level: String,
    pub claim_classification: String,
    pub measurement_boundary: String,
    pub missing_preconditions: Vec<String>,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct FeatureReportCoverageGap {
    pub layer: String,
    pub measurement_boundary: String,
    pub unmeasured_axes: Vec<String>,
    pub unsupported_constructs: Vec<String>,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct TheoremPreconditionCheckReportV0 {
    pub schema_version: String,
    pub input: TheoremPreconditionCheckInput,
    pub registry: TheoremPackageRegistryV0,
    pub summary: TheoremPreconditionCheckSummary,
    pub archmap_preservation_precondition_checklist: Vec<ArchMapLeanPreservationChecklistEntry>,
    pub checks: Vec<TheoremPreconditionCheck>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct TheoremPreconditionCheckInput {
    pub schema_version: String,
    pub path: String,
    pub architecture_id: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct TheoremPackageRegistryV0 {
    pub schema_version: String,
    pub scope: String,
    pub packages: Vec<TheoremPackageMetadataV0>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct TheoremPackageMetadataV0 {
    pub package_id: String,
    pub lean_entrypoint: String,
    pub theorem_refs: Vec<String>,
    pub supported_subject_refs: Vec<String>,
    pub supported_axes: Vec<String>,
    pub claim_level: String,
    pub claim_classification: String,
    pub measurement_boundary: String,
    pub required_assumptions: Vec<String>,
    pub coverage_assumptions: Vec<String>,
    pub exactness_assumptions: Vec<String>,
    pub missing_preconditions: Vec<String>,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct TheoremPreconditionCheckSummary {
    pub result: String,
    pub checked_claim_count: usize,
    pub applicable_claim_count: usize,
    pub formal_proved_claim_count: usize,
    pub measured_witness_count: usize,
    pub blocked_claim_count: usize,
    pub unmeasured_claim_count: usize,
    pub unknown_theorem_ref_count: usize,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct TheoremPreconditionCheck {
    pub claim_id: String,
    pub subject_ref: String,
    pub applicable_package_refs: Vec<String>,
    pub theorem_refs: Vec<String>,
    pub unknown_theorem_refs: Vec<String>,
    pub claim_level: String,
    pub input_claim_classification: String,
    pub resolved_claim_classification: String,
    pub measurement_boundary: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub projection_rule: Option<String>,
    pub required_assumptions: Vec<String>,
    pub coverage_assumptions: Vec<String>,
    pub exactness_assumptions: Vec<String>,
    pub missing_preconditions: Vec<String>,
    pub non_conclusions: Vec<String>,
    pub result: String,
    pub reason: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct RepairRuleRegistryV0 {
    pub schema_version: String,
    pub scope: String,
    pub selected_obstruction_universe: String,
    pub explicit_assumptions: Vec<String>,
    pub rules: Vec<RepairRuleV0>,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct RepairRuleV0 {
    pub repair_rule_id: String,
    pub target_witness_kind: String,
    pub proposed_operation: String,
    pub required_preconditions: Vec<String>,
    pub expected_effect: String,
    pub preserved_invariants: Vec<String>,
    pub possible_side_effects: Vec<String>,
    pub proof_obligation_refs: Vec<String>,
    pub patch_strategy: String,
    pub confidence: String,
    pub relative_to: RepairRuleRelativeScopeV0,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct RepairRuleRelativeScopeV0 {
    pub selected_obstruction_universe: String,
    pub explicit_assumptions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct RepairRuleRegistryValidationReportV0 {
    pub schema_version: String,
    pub input: RepairRuleRegistryValidationInput,
    pub registry: RepairRuleRegistryV0,
    pub summary: RepairRuleRegistryValidationSummary,
    pub checks: Vec<ValidationCheck>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct RepairRuleRegistryValidationInput {
    pub schema_version: String,
    pub path: String,
    pub scope: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct RepairRuleRegistryValidationSummary {
    pub result: String,
    pub rule_count: usize,
    pub failed_check_count: usize,
    pub warning_check_count: usize,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct SynthesisConstraintArtifactV0 {
    pub schema_version: String,
    pub scope: String,
    pub constraint_refs: Vec<String>,
    pub candidate_refs: Vec<String>,
    pub required_assumptions: Vec<String>,
    pub coverage_assumptions: Vec<String>,
    pub exactness_assumptions: Vec<String>,
    pub unsupported_constructs: Vec<String>,
    pub constraints: Vec<SynthesisConstraintV0>,
    pub candidates: Vec<SynthesisCandidateV0>,
    pub no_solution_boundary: SynthesisNoSolutionBoundaryV0,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct SynthesisConstraintV0 {
    pub constraint_id: String,
    pub kind: String,
    pub subject_ref: String,
    pub predicate: String,
    pub evidence_refs: Vec<String>,
    pub theorem_precondition_refs: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct SynthesisCandidateV0 {
    pub candidate_id: String,
    pub produced_by: String,
    pub operation_refs: Vec<String>,
    pub constraint_refs: Vec<String>,
    pub soundness_package_refs: Vec<String>,
    pub required_assumptions: Vec<String>,
    pub coverage_assumptions: Vec<String>,
    pub exactness_assumptions: Vec<String>,
    pub unsupported_constructs: Vec<String>,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct SynthesisNoSolutionBoundaryV0 {
    pub solver_status: String,
    pub candidate_refs: Vec<String>,
    pub no_solution_certificate_ref: Option<String>,
    pub valid_certificate_claim_ref: Option<String>,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct SynthesisConstraintValidationReportV0 {
    pub schema_version: String,
    pub input: SynthesisConstraintValidationInput,
    pub artifact: SynthesisConstraintArtifactV0,
    pub summary: SynthesisConstraintValidationSummary,
    pub checks: Vec<ValidationCheck>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct SynthesisConstraintValidationInput {
    pub schema_version: String,
    pub path: String,
    pub scope: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct SynthesisConstraintValidationSummary {
    pub result: String,
    pub constraint_count: usize,
    pub candidate_count: usize,
    pub failed_check_count: usize,
    pub warning_check_count: usize,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct NoSolutionCertificateV0 {
    pub schema_version: String,
    pub certificate_id: String,
    pub scope: String,
    pub constraint_refs: Vec<String>,
    pub refuted_candidate_refs: Vec<String>,
    pub obstruction_witness_refs: Vec<String>,
    pub required_assumptions: Vec<String>,
    pub coverage_assumptions: Vec<String>,
    pub exactness_assumptions: Vec<String>,
    pub unsupported_constructs: Vec<String>,
    pub proof_obligation_refs: Vec<String>,
    pub valid_certificate_claim_ref: Option<String>,
    pub cases: Vec<NoSolutionCertificateCaseV0>,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct NoSolutionCertificateCaseV0 {
    pub case_id: String,
    pub constraint_refs: Vec<String>,
    pub refuted_candidate_ref: Option<String>,
    pub evidence_refs: Vec<String>,
    pub theorem_precondition_refs: Vec<String>,
    pub reason: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct NoSolutionCertificateValidationReportV0 {
    pub schema_version: String,
    pub input: NoSolutionCertificateValidationInput,
    pub certificate: NoSolutionCertificateV0,
    pub summary: NoSolutionCertificateValidationSummary,
    pub checks: Vec<ValidationCheck>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct NoSolutionCertificateValidationInput {
    pub schema_version: String,
    pub path: String,
    pub certificate_id: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct NoSolutionCertificateValidationSummary {
    pub result: String,
    pub case_count: usize,
    pub refuted_candidate_count: usize,
    pub failed_check_count: usize,
    pub warning_check_count: usize,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct OrganizationPolicyV0 {
    pub schema_version: String,
    pub policy_id: String,
    pub policy_version: String,
    pub scope: String,
    pub required_axes: Vec<OrganizationRequiredAxisV0>,
    pub allowed_unmeasured_gaps: Vec<OrganizationAllowedUnmeasuredGapV0>,
    pub required_theorem_preconditions: Vec<OrganizationRequiredTheoremPreconditionV0>,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct OrganizationRequiredAxisV0 {
    pub axis: String,
    pub claim_level: String,
    pub measurement_boundary: String,
    pub max_allowed_value: Option<i64>,
    pub required_preconditions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct OrganizationAllowedUnmeasuredGapV0 {
    pub axis: String,
    pub claim_level: String,
    pub layer: String,
    pub scope: String,
    pub reason: String,
    pub expires_at: Option<String>,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct OrganizationRequiredTheoremPreconditionV0 {
    pub subject_ref: String,
    pub claim_level: String,
    pub theorem_refs: Vec<String>,
    pub required_preconditions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct OrganizationPolicyValidationReportV0 {
    pub schema_version: String,
    pub input: OrganizationPolicyValidationInput,
    pub policy: OrganizationPolicyV0,
    pub summary: OrganizationPolicyValidationSummary,
    pub checks: Vec<ValidationCheck>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct OrganizationPolicyValidationInput {
    pub schema_version: String,
    pub path: String,
    pub policy_id: String,
    pub policy_version: String,
    pub scope: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct OrganizationPolicyValidationSummary {
    pub result: String,
    pub required_axis_count: usize,
    pub allowed_unmeasured_gap_count: usize,
    pub required_theorem_precondition_count: usize,
    pub failed_check_count: usize,
    pub warning_check_count: usize,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct LawPolicyTemplateRegistryV0 {
    pub schema_version: String,
    pub registry_id: String,
    pub scope: String,
    pub templates: Vec<LawPolicyTemplateV0>,
    pub explicit_assumptions: Vec<String>,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct LawPolicyTemplateV0 {
    pub template_id: String,
    pub target_component_kind: String,
    pub law_policy_family: String,
    pub selector_semantics: String,
    pub selector_assumptions: Vec<String>,
    pub required_evidence_kinds: Vec<String>,
    pub default_required_axes: Vec<String>,
    pub policy_output_artifacts: Vec<String>,
    pub theorem_bridge_preconditions: Vec<String>,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct LawPolicyTemplateRegistryValidationReportV0 {
    pub schema_version: String,
    pub input: LawPolicyTemplateRegistryValidationInput,
    pub registry: LawPolicyTemplateRegistryV0,
    pub summary: LawPolicyTemplateRegistryValidationSummary,
    pub checks: Vec<ValidationCheck>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct LawPolicyTemplateRegistryValidationInput {
    pub schema_version: String,
    pub path: String,
    pub registry_id: String,
    pub scope: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct LawPolicyTemplateRegistryValidationSummary {
    pub result: String,
    pub template_count: usize,
    pub failed_check_count: usize,
    pub warning_check_count: usize,
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
    pub selected_law_policy_ref: ArchSigAnalysisArtifactRefV0,
    pub atom_configuration_summary: ArchSigAtomConfigurationSummaryV0,
    pub molecule_readings: Vec<ArchSigMoleculeReadingV0>,
    pub obstruction_circuits: Vec<ArchSigObstructionCircuitV0>,
    pub signature_axes: Vec<ArchSigSignatureAxisReadingV0>,
    pub flatness_reading: ArchSigFlatnessReadingV0,
    pub static_runtime_semantic_layer_split: ArchSigLayerSplitV0,
    pub repair_operation_candidates: Vec<ArchSigRepairOperationCandidateV0>,
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
    #[serde(rename = "interpretationNotesForLLM")]
    pub interpretation_notes_for_llm: Vec<String>,
    pub non_conclusions: Vec<String>,
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
    pub molecule_reading_count: usize,
    pub obstruction_circuit_count: usize,
    pub signature_axis_count: usize,
    pub repair_operation_candidate_count: usize,
    pub failed_check_count: usize,
    pub warning_check_count: usize,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchitecturePolicyV0 {
    pub schema_version: String,
    pub policy_id: String,
    pub policy_version: String,
    pub component_id_kind: String,
    pub selector_semantics: String,
    pub adopted_laws: Vec<ArchitectureAdoptedLawV0>,
    pub layers: Vec<ArchitecturePolicyLayerV0>,
    #[serde(default)]
    pub allowed_dependencies: Vec<ArchitecturePolicyDependencyRuleV0>,
    #[serde(default)]
    pub forbidden_dependencies: Vec<ArchitecturePolicyDependencyRuleV0>,
    #[serde(default)]
    pub exceptions: Vec<ArchitecturePolicyExceptionV0>,
    pub srp: ArchitecturePolicySrpV0,
    #[serde(default)]
    pub sft_governance: ArchitecturePolicySftGovernanceV0,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchitectureAdoptedLawV0 {
    pub law_id: String,
    pub law_kind: String,
    pub enforcement: String,
    pub review_level: String,
    pub evidence_boundary: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchitecturePolicyLayerV0 {
    pub layer_id: String,
    pub selectors: Vec<String>,
    pub responsibility: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchitecturePolicyDependencyRuleV0 {
    pub rule_id: String,
    pub law_ref: String,
    pub source_layer: String,
    pub target_layer: String,
    pub severity: String,
    pub review_action: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchitecturePolicyExceptionV0 {
    pub exception_id: String,
    pub law_ref: String,
    pub source_selector: String,
    pub target_selector: String,
    pub reason: String,
    pub expires_at: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchitecturePolicySrpV0 {
    pub responsibility_taxonomy: Vec<String>,
    pub reason_to_change_categories: Vec<String>,
    pub allowed_orchestrator_roles: Vec<String>,
    pub required_evidence_fields: Vec<String>,
    pub judgment_boundary: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize, Default)]
#[serde(rename_all = "camelCase")]
pub struct ArchitecturePolicySftGovernanceV0 {
    #[serde(default)]
    pub adopted_invariant_refs: Vec<String>,
    #[serde(default)]
    pub allowed_operation_families: Vec<ArchitecturePolicyFutureRuleV0>,
    #[serde(default)]
    pub conditionally_allowed_support: Vec<ArchitecturePolicyFutureRuleV0>,
    #[serde(default)]
    pub forbidden_future_path_classes: Vec<ArchitecturePolicyFutureRuleV0>,
    #[serde(default)]
    pub required_governance_interventions: Vec<ArchitecturePolicyGovernanceInterventionV0>,
    #[serde(default)]
    pub selected_horizon_refs: Vec<String>,
    #[serde(default)]
    pub observation_boundary_refs: Vec<String>,
    #[serde(default)]
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize, Default)]
#[serde(rename_all = "camelCase")]
pub struct ArchitecturePolicyFutureRuleV0 {
    pub rule_id: String,
    pub applies_to: Vec<String>,
    pub disposition: String,
    pub reason: String,
    pub evidence_refs: Vec<String>,
    pub reviewer_action: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize, Default)]
#[serde(rename_all = "camelCase")]
pub struct ArchitecturePolicyGovernanceInterventionV0 {
    pub intervention_id: String,
    pub intervention_kind: String,
    pub applies_to: Vec<String>,
    pub required_before: String,
    pub preservation_boundary: String,
    pub evidence_refs: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchitecturePolicyValidationReportV0 {
    pub schema_version: String,
    pub input: ArchitecturePolicyValidationInputV0,
    pub policy: ArchitecturePolicyV0,
    pub summary: ArchitecturePolicyValidationSummaryV0,
    pub checks: Vec<ValidationCheck>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchitecturePolicyValidationInputV0 {
    pub schema_version: String,
    pub path: String,
    pub policy_id: String,
    pub policy_version: String,
    pub component_id_kind: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchitecturePolicyValidationSummaryV0 {
    pub result: String,
    pub adopted_law_count: usize,
    pub layer_count: usize,
    pub forbidden_dependency_count: usize,
    pub exception_count: usize,
    pub failed_check_count: usize,
    pub warning_check_count: usize,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct LawViolationReportV0 {
    pub schema_version: String,
    pub report_id: String,
    pub policy_ref: LawViolationPolicyRefV0,
    pub sig0_ref: LawViolationSig0RefV0,
    pub summary: LawViolationSummaryV0,
    pub deterministic_violations: Vec<LawViolationFindingV0>,
    pub allowed_exceptions: Vec<LawViolationExceptionFindingV0>,
    pub srp_cues: Vec<SrpReviewCueV0>,
    pub unmeasured: Vec<LawViolationUnmeasuredV0>,
    pub review_actions: Vec<String>,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct LawViolationPolicyRefV0 {
    pub policy_id: String,
    pub policy_version: String,
    pub path: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct LawViolationSig0RefV0 {
    pub root: String,
    pub component_kind: String,
    pub path: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct LawViolationSummaryV0 {
    pub result: String,
    pub deterministic_violation_count: usize,
    pub allowed_exception_count: usize,
    pub srp_cue_count: usize,
    pub unmeasured_count: usize,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct LawViolationFindingV0 {
    pub finding_id: String,
    pub law_ref: String,
    pub law_kind: String,
    pub source: String,
    pub target: String,
    pub source_layer: String,
    pub target_layer: String,
    pub rule_id: String,
    pub severity: String,
    pub evidence: String,
    pub review_action: String,
    pub evidence_boundary: String,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct LawViolationExceptionFindingV0 {
    pub exception_id: String,
    pub law_ref: String,
    pub source: String,
    pub target: String,
    pub reason: String,
    pub review_action: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct SrpReviewCueV0 {
    pub cue_id: String,
    pub subject_ref: String,
    pub semantic_role: Option<String>,
    pub responsibility_regions: Vec<String>,
    pub reason_to_change: Vec<String>,
    pub actor_refs: Vec<String>,
    pub allowed_role: Option<String>,
    pub law_refs: Vec<String>,
    pub judgment_taxonomy: Vec<String>,
    pub evidence_refs: Vec<String>,
    pub policy_refs: Vec<String>,
    pub missing_evidence: Vec<String>,
    pub review_level: String,
    pub review_action: String,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct LawViolationUnmeasuredV0 {
    pub item_id: String,
    pub category: String,
    pub subject_ref: String,
    pub reason: String,
    pub review_action: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct CustomRulePluginRegistryV0 {
    pub schema_version: String,
    pub registry_id: String,
    pub scope: String,
    pub plugins: Vec<CustomRulePluginV0>,
    pub explicit_assumptions: Vec<String>,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct CustomRulePluginV0 {
    pub plugin_id: String,
    pub rule_id: String,
    pub plugin_kind: String,
    pub evidence_kind: String,
    pub confidence: String,
    pub input_contract: Vec<String>,
    pub output_contract: Vec<String>,
    pub coverage_assumptions: Vec<String>,
    pub permitted_claim_levels: Vec<String>,
    pub formal_claim_promotion: String,
    pub theorem_precondition_refs: Vec<String>,
    pub required_theorem_preconditions: Vec<String>,
    pub output_artifacts: Vec<String>,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct CustomRulePluginRegistryValidationReportV0 {
    pub schema_version: String,
    pub input: CustomRulePluginRegistryValidationInput,
    pub registry: CustomRulePluginRegistryV0,
    pub summary: CustomRulePluginRegistryValidationSummary,
    pub checks: Vec<ValidationCheck>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct CustomRulePluginRegistryValidationInput {
    pub schema_version: String,
    pub path: String,
    pub registry_id: String,
    pub scope: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct CustomRulePluginRegistryValidationSummary {
    pub result: String,
    pub plugin_count: usize,
    pub failed_check_count: usize,
    pub warning_check_count: usize,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct MeasurementUnitRegistryV0 {
    pub schema_version: String,
    pub registry_id: String,
    pub scope: String,
    pub units: Vec<MeasurementUnitV0>,
    pub evidence_adapters: Vec<MeasurementEvidenceAdapterBoundaryV0>,
    pub explicit_assumptions: Vec<String>,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct MeasurementUnitV0 {
    pub unit_id: String,
    pub unit_kind: String,
    pub repository_root: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub service_root: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub deployment_unit: Option<String>,
    pub component_id_kind: String,
    pub selected_component_refs: Vec<String>,
    pub runtime_evidence_sources: Vec<MeasurementEvidenceSourceV0>,
    pub semantic_workflow_sources: Vec<MeasurementEvidenceSourceV0>,
    pub coverage_assumptions: Vec<String>,
    pub unsupported_constructs: Vec<String>,
    pub output_artifacts: Vec<String>,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct MeasurementEvidenceSourceV0 {
    pub source_id: String,
    pub source_kind: String,
    pub owner_unit_ref: String,
    pub path: String,
    pub privacy_boundary: String,
    pub coverage_assumptions: Vec<String>,
    pub unsupported_constructs: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct MeasurementEvidenceAdapterBoundaryV0 {
    pub adapter_id: String,
    pub adapter_kind: String,
    pub measurement_unit_refs: Vec<String>,
    pub measured_layers: Vec<String>,
    pub evidence_kinds: Vec<String>,
    pub projection_rule: String,
    pub coverage_assumptions: Vec<String>,
    pub exactness_assumptions: Vec<String>,
    pub unsupported_constructs: Vec<String>,
    pub output_artifacts: Vec<String>,
    pub theorem_bridge_preconditions: Vec<String>,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct MeasurementUnitRegistryValidationReportV0 {
    pub schema_version: String,
    pub input: MeasurementUnitRegistryValidationInput,
    pub registry: MeasurementUnitRegistryV0,
    pub summary: MeasurementUnitRegistryValidationSummary,
    pub checks: Vec<ValidationCheck>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct MeasurementUnitRegistryValidationInput {
    pub schema_version: String,
    pub path: String,
    pub registry_id: String,
    pub scope: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct MeasurementUnitRegistryValidationSummary {
    pub result: String,
    pub unit_count: usize,
    pub evidence_adapter_count: usize,
    pub failed_check_count: usize,
    pub warning_check_count: usize,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct AatObservableBundleV0 {
    pub schema_version: String,
    pub bundle_id: String,
    pub architecture_id: String,
    pub source_refs: Vec<AatObservableSourceRefV0>,
    pub selected_universe: AatSelectedUniverseV0,
    pub concept_mappings: Vec<AatConceptMappingV0>,
    pub observed_axes: Vec<AatObservedAxisV0>,
    pub coverage_boundaries: Vec<AatCoverageBoundaryV0>,
    pub witness_catalog: Vec<AatWitnessCatalogEntryV0>,
    pub operation_candidates: Vec<AatOperationCandidateV0>,
    pub projection_observation_evidence: Vec<AatProjectionObservationEvidenceV0>,
    pub feature_extension_evidence: Vec<AatFeatureExtensionEvidenceV0>,
    pub semantic_diagram_evidence: Vec<AatSemanticDiagramEvidenceV0>,
    pub state_effect_law_evidence: Vec<AatStateEffectLawEvidenceV0>,
    pub repair_synthesis_evidence: Vec<AatRepairSynthesisEvidenceV0>,
    pub analytic_axes: Vec<AatAnalyticAxisV0>,
    pub theorem_boundaries: Vec<AatTheoremBoundaryV0>,
    pub review_actions: Vec<AatReviewActionV0>,
    pub llm_review_surface: AatLlmReviewSurfaceV0,
    pub responsibility_boundary: AatResponsibilityBoundaryV0,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct AatObservableSourceRefV0 {
    pub source_ref_id: String,
    pub artifact_kind: String,
    pub schema_version: String,
    pub path: String,
    pub retained_fields: Vec<String>,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct AatSelectedUniverseV0 {
    pub universe_id: String,
    pub included_refs: Vec<String>,
    pub excluded_refs: Vec<String>,
    pub private_refs: Vec<String>,
    pub unavailable_refs: Vec<String>,
    pub unsupported_refs: Vec<String>,
    pub dynamic_boundary_refs: Vec<String>,
    pub exactness_assumptions: Vec<String>,
    pub measurement_status: String,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct AatConceptMappingV0 {
    pub concept_id: String,
    pub aat_concept: String,
    pub artifact_refs: Vec<String>,
    pub report_refs: Vec<String>,
    pub skill_refs: Vec<String>,
    pub expressibility: String,
    pub retention_status: String,
    pub review_status: String,
    pub measurement_status: String,
    pub responsibility: String,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct AatObservedAxisV0 {
    pub axis_id: String,
    pub concept_refs: Vec<String>,
    pub artifact_refs: Vec<String>,
    pub measurement_status: String,
    pub value: Option<i64>,
    pub boundary: String,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct AatCoverageBoundaryV0 {
    pub boundary_id: String,
    pub boundary_kind: String,
    pub affected_refs: Vec<String>,
    pub measurement_status: String,
    pub review_action_ref: Option<String>,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct AatWitnessCatalogEntryV0 {
    pub witness_ref: String,
    pub witness_kind: String,
    pub law_refs: Vec<String>,
    pub source_refs: Vec<String>,
    pub measurement_status: String,
    pub severity: String,
    pub review_action_ref: String,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct AatOperationCandidateV0 {
    pub operation_ref: String,
    pub operation_kind: String,
    pub role: String,
    pub confidence: String,
    pub deterministic_cues: Vec<String>,
    pub llm_judgment_needed: Vec<String>,
    pub evidence_refs: Vec<String>,
    pub preserved_invariant_refs: Vec<String>,
    pub possible_transferred_obstruction_refs: Vec<String>,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct AatProjectionObservationEvidenceV0 {
    pub evidence_ref: String,
    pub evidence_kind: String,
    pub source_ref: String,
    pub target_ref: String,
    pub local_contract_boundary: String,
    pub global_layering_boundary: String,
    pub witness_refs: Vec<String>,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct AatFeatureExtensionEvidenceV0 {
    pub evidence_ref: String,
    pub feature_ref: String,
    pub operation_ref: String,
    pub obstruction_classifications: Vec<String>,
    pub source_refs: Vec<String>,
    pub witness_refs: Vec<String>,
    pub missing_evidence_refs: Vec<String>,
    pub static_boundary: String,
    pub runtime_boundary: String,
    pub semantic_boundary: String,
    pub coverage_boundary: String,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct AatSemanticDiagramEvidenceV0 {
    pub evidence_ref: String,
    pub path_refs: Vec<String>,
    pub homotopy_refs: Vec<String>,
    pub diagram_refs: Vec<String>,
    pub filler_status: String,
    pub nonfillability_witness_refs: Vec<String>,
    pub observation_refs: Vec<String>,
    pub measurement_status: String,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct AatStateEffectLawEvidenceV0 {
    pub evidence_ref: String,
    pub law_kind: String,
    pub law_case_refs: Vec<String>,
    pub measurement_status: String,
    pub witness_refs: Vec<String>,
    pub unmeasured_law_families: Vec<String>,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct AatRepairSynthesisEvidenceV0 {
    pub evidence_ref: String,
    pub repair_step_refs: Vec<String>,
    pub synthesis_candidate_refs: Vec<String>,
    pub no_solution_certificate_refs: Vec<String>,
    pub selected_obstruction_decrease_refs: Vec<String>,
    pub transferred_risk_refs: Vec<String>,
    pub solver_status: String,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct AatAnalyticAxisV0 {
    pub axis_id: String,
    pub metric_ref: String,
    pub representation_strength: Vec<String>,
    pub selected_witness_universe: Vec<String>,
    pub aggregate_zero_reflection: String,
    pub coverage_assumptions: Vec<String>,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct AatTheoremBoundaryV0 {
    pub boundary_ref: String,
    pub claim_ref: String,
    pub claim_level: String,
    pub claim_classification: String,
    pub missing_preconditions: Vec<String>,
    pub measured_violation_refs: Vec<String>,
    pub review_action_ref: String,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct AatReviewActionV0 {
    pub review_action_id: String,
    pub category: String,
    pub source_refs: Vec<String>,
    pub action: String,
    pub next_evidence: Vec<String>,
    pub owner: String,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct AatLlmReviewSurfaceV0 {
    pub skill_ref: String,
    pub input_artifact_refs: Vec<String>,
    pub review_questions: Vec<String>,
    pub output_categories: Vec<String>,
    pub deterministic_inputs: Vec<String>,
    pub llm_judgment_boundaries: Vec<String>,
    pub human_review_boundaries: Vec<String>,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct AatResponsibilityBoundaryV0 {
    pub deterministic_tool: Vec<String>,
    pub llm_review: Vec<String>,
    pub human_review: Vec<String>,
    pub formal_proof: Vec<String>,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct AatObservableBundleValidationReportV0 {
    pub schema_version: String,
    pub input: AatObservableBundleValidationInputV0,
    pub bundle: AatObservableBundleV0,
    pub summary: AatObservableBundleValidationSummaryV0,
    pub checks: Vec<ValidationCheck>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct AatObservableBundleValidationInputV0 {
    pub schema_version: String,
    pub path: String,
    pub bundle_id: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct AatObservableBundleValidationSummaryV0 {
    pub result: String,
    pub concept_count: usize,
    pub witness_count: usize,
    pub operation_candidate_count: usize,
    pub review_action_count: usize,
    pub failed_check_count: usize,
    pub warning_check_count: usize,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct PrQualityAnalysisReportV0 {
    pub schema_version: String,
    pub report_id: String,
    pub archmap_ref: PrQualityArchMapArtifactRefV0,
    pub air_ref: Option<PrQualityArtifactRefV0>,
    pub theorem_check_ref: Option<PrQualityArtifactRefV0>,
    pub feature_report_ref: Option<PrQualityArtifactRefV0>,
    pub policy_decision_ref: Option<PrQualityArtifactRefV0>,
    pub cues: Vec<PrQualityCueV0>,
    pub missing_evidence: Vec<PrQualityMissingEvidenceV0>,
    pub review_summary: PrQualityReviewSummaryV0,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct PrQualityArchMapArtifactRefV0 {
    pub artifact_id: String,
    pub artifact_kind: String,
    pub path: String,
    pub schema_version: Option<String>,
    pub selected_map_item_ids: Vec<String>,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct PrQualityArtifactRefV0 {
    pub artifact_id: String,
    pub artifact_kind: String,
    pub path: String,
    pub schema_version: Option<String>,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct PrQualityCueV0 {
    pub cue_id: String,
    pub cue_kind: String,
    pub source_refs: Vec<String>,
    pub severity: String,
    pub review_focus: String,
    pub evidence_boundary: String,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct PrQualityReviewSummaryV0 {
    pub summary_id: String,
    pub cue_count: usize,
    pub missing_evidence_count: usize,
    pub reviewer_notes: Vec<String>,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct PrQualityMissingEvidenceV0 {
    pub boundary_id: String,
    pub boundary_kind: String,
    pub source_refs: Vec<String>,
    pub reason: String,
    pub treatment: String,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct PrQualityAnalysisValidationReportV0 {
    pub schema_version: String,
    pub input: PrQualityAnalysisValidationInput,
    pub report: PrQualityAnalysisReportV0,
    pub summary: PrQualityAnalysisValidationSummary,
    pub checks: Vec<ValidationCheck>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct PrQualityAnalysisValidationInput {
    pub schema_version: String,
    pub path: String,
    pub report_id: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct PrQualityAnalysisValidationSummary {
    pub result: String,
    pub cue_count: usize,
    pub missing_evidence_count: usize,
    pub failed_check_count: usize,
    pub warning_check_count: usize,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct PolicyDecisionReportV0 {
    pub schema_version: String,
    pub input: PolicyDecisionInput,
    pub summary: PolicyDecisionSummary,
    pub required_axis_decisions: Vec<RequiredAxisPolicyDecisionV0>,
    pub missing_precondition_decisions: Vec<MissingPreconditionPolicyDecisionV0>,
    pub coverage_gap_decisions: Vec<CoverageGapPolicyDecisionV0>,
    pub witness_decisions: Vec<WitnessPolicyDecisionV0>,
    pub checks: Vec<ValidationCheck>,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct PolicyDecisionInput {
    pub feature_report_schema_version: String,
    pub feature_report_path: String,
    pub organization_policy_schema_version: String,
    pub organization_policy_path: String,
    pub policy_id: String,
    pub policy_version: String,
    pub scope: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct PolicyDecisionSummary {
    pub decision: String,
    pub fail_count: usize,
    pub warn_count: usize,
    pub advisory_count: usize,
    pub required_axis_count: usize,
    pub allowed_unmeasured_gap_count: usize,
    pub missing_precondition_count: usize,
    pub measured_nonzero_witness_count: usize,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct RequiredAxisPolicyDecisionV0 {
    pub axis: String,
    pub status: String,
    pub claim_level: String,
    pub expected_measurement_boundary: String,
    pub actual_measurement_boundary: String,
    pub value: Option<i64>,
    pub max_allowed_value: Option<i64>,
    pub reason: String,
    pub required_preconditions: Vec<String>,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct MissingPreconditionPolicyDecisionV0 {
    pub subject_ref: String,
    pub claim_id: String,
    pub status: String,
    pub missing_preconditions: Vec<String>,
    pub theorem_refs: Vec<String>,
    pub reason: String,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct CoverageGapPolicyDecisionV0 {
    pub layer: String,
    pub axis: String,
    pub status: String,
    pub allowed_by_policy: bool,
    pub measurement_boundary: String,
    pub reason: String,
    pub policy_scope: Option<String>,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct WitnessPolicyDecisionV0 {
    pub witness_id: String,
    pub status: String,
    pub layer: String,
    pub kind: String,
    pub claim_level: String,
    pub claim_classification: String,
    pub measurement_boundary: String,
    pub reason: String,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ReportArtifactRetentionManifestV0 {
    pub schema_version: String,
    pub retention_id: String,
    pub repository: RepositoryRef,
    pub pull_request: ReportArtifactPullRequestRef,
    pub commit_sha: String,
    pub policy: ReportArtifactPolicyRef,
    pub generated_at: String,
    pub retention_scope: String,
    pub artifacts: Vec<RetainedReportArtifactRefV0>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub missing_or_private_artifacts: Vec<MissingReportArtifactRefV0>,
    pub traceability: ReportArtifactTraceabilityV0,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ReportArtifactPullRequestRef {
    pub number: usize,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub url: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ReportArtifactPolicyRef {
    #[serde(skip_serializing_if = "Option::is_none")]
    pub policy_id: Option<String>,
    pub policy_version: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub schema_version: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct RetainedReportArtifactRefV0 {
    pub artifact_id: String,
    pub kind: String,
    pub path: String,
    pub repository: RepositoryRef,
    pub pull_request_number: usize,
    pub commit_sha: String,
    pub schema_version: String,
    pub policy_version: String,
    pub generated_at: String,
    pub retention_scope: String,
    pub visibility: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub content_hash: Option<String>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct MissingReportArtifactRefV0 {
    pub kind: String,
    pub reason: String,
    pub visibility: String,
    pub repository: RepositoryRef,
    pub pull_request_number: usize,
    pub commit_sha: String,
    pub schema_version: String,
    pub policy_version: String,
    pub generated_at: String,
    pub retention_scope: String,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ReportArtifactTraceabilityV0 {
    pub baseline_comparison_refs: Vec<String>,
    pub suppression_workflow_refs: Vec<String>,
    pub drift_ledger_refs: Vec<String>,
    pub reviewer_output_refs: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ReportArtifactRetentionValidationReportV0 {
    pub schema_version: String,
    pub input: ReportArtifactRetentionValidationInput,
    pub manifest: ReportArtifactRetentionManifestV0,
    pub summary: ReportArtifactRetentionValidationSummary,
    pub checks: Vec<ValidationCheck>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ReportArtifactRetentionValidationInput {
    pub schema_version: String,
    pub path: String,
    pub retention_id: String,
    pub repository: RepositoryRef,
    pub pull_request_number: usize,
    pub commit_sha: String,
    pub policy_version: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ReportArtifactRetentionValidationSummary {
    pub result: String,
    pub artifact_count: usize,
    pub missing_or_private_artifact_count: usize,
    pub failed_check_count: usize,
    pub warning_check_count: usize,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct BaselineSuppressionReportV0 {
    pub schema_version: String,
    pub input: BaselineSuppressionInput,
    pub summary: BaselineSuppressionSummary,
    pub witness_delta: WitnessDeltaV0,
    pub coverage_gap_delta: CoverageGapDeltaV0,
    pub required_axis_delta: RequiredAxisDeltaV0,
    pub policy_decision_delta: PolicyDecisionDeltaV0,
    pub suppressions: Vec<RiskDispositionV0>,
    pub accepted_risks: Vec<RiskDispositionV0>,
    pub checks: Vec<ValidationCheck>,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct BaselineSuppressionInput {
    pub baseline_feature_report_schema_version: String,
    pub baseline_feature_report_path: String,
    pub current_feature_report_schema_version: String,
    pub current_feature_report_path: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub baseline_policy_decision_path: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub current_policy_decision_path: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub retention_manifest_ref: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct BaselineSuppressionSummary {
    pub result: String,
    pub newly_introduced_witness_count: usize,
    pub eliminated_witness_count: usize,
    pub new_coverage_gap_count: usize,
    pub eliminated_coverage_gap_count: usize,
    pub required_axis_status_change_count: usize,
    pub policy_decision_before: Option<String>,
    pub policy_decision_after: Option<String>,
    pub suppressed_count: usize,
    pub accepted_risk_count: usize,
    pub unresolved_current_witness_count: usize,
    pub failed_check_count: usize,
    pub warning_check_count: usize,
    pub advisory_check_count: usize,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct WitnessDeltaV0 {
    pub newly_introduced: Vec<WitnessDeltaEntryV0>,
    pub eliminated: Vec<WitnessDeltaEntryV0>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct WitnessDeltaEntryV0 {
    pub witness_id: String,
    pub layer: String,
    pub kind: String,
    pub status: String,
    pub measurement_boundary: String,
    pub claim_classification: String,
    pub reason: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct CoverageGapDeltaV0 {
    pub newly_introduced: Vec<CoverageGapDeltaEntryV0>,
    pub eliminated: Vec<CoverageGapDeltaEntryV0>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct CoverageGapDeltaEntryV0 {
    pub gap_ref: String,
    pub layer: String,
    pub axis: String,
    pub status: String,
    pub measurement_boundary: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub allowed_by_policy: Option<bool>,
    pub reason: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct RequiredAxisDeltaV0 {
    pub changes: Vec<RequiredAxisDeltaEntryV0>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct RequiredAxisDeltaEntryV0 {
    pub axis: String,
    pub before_status: Option<String>,
    pub after_status: String,
    pub before_measurement_boundary: Option<String>,
    pub after_measurement_boundary: String,
    pub before_value: Option<i64>,
    pub after_value: Option<i64>,
    pub reason: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct PolicyDecisionDeltaV0 {
    pub baseline_decision: Option<String>,
    pub current_decision: Option<String>,
    pub fail_delta: i64,
    pub warn_delta: i64,
    pub advisory_delta: i64,
    pub required_action: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct RiskDispositionV0 {
    pub disposition_id: String,
    pub kind: String,
    pub status: String,
    pub reason: String,
    pub approved_by: String,
    pub approved_at: String,
    pub expires_at: String,
    pub scope: String,
    pub policy_ref: String,
    pub witness_ref: String,
    pub applies_to_current_witness: bool,
    pub reviewer_status: String,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct SnapshotDiffEndpoint {
    pub repository: SnapshotRepositoryRef,
    pub revision: RepositoryRevisionRef,
    pub validation_result: String,
    pub extractor_version: String,
    pub rule_set_version: String,
    pub policy_id: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct SnapshotComparisonStatus {
    pub primary_diff_eligible: bool,
    pub reasons: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct SignatureAxisChange {
    pub axis: String,
    pub before: i64,
    pub after: i64,
    pub delta: i64,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct UnmeasuredAxisDelta {
    pub axis: String,
    pub reason: String,
    pub before_measured: bool,
    pub after_measured: bool,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct SnapshotEvidenceDiff {
    pub available: bool,
    pub unavailable_reason: Option<String>,
    pub component_delta: Option<ComponentSetDelta>,
    pub edge_delta: Option<EdgeSetDelta>,
    pub policy_violation_delta: Option<PolicyViolationSetDelta>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ComponentSetDelta {
    pub before_count: usize,
    pub after_count: usize,
    pub delta: i64,
    pub added: Vec<String>,
    pub removed: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct EdgeSetDelta {
    pub before_count: usize,
    pub after_count: usize,
    pub delta: i64,
    pub added: Vec<Edge>,
    pub removed: Vec<Edge>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct PolicyViolationSetDelta {
    pub before_count: usize,
    pub after_count: usize,
    pub delta: i64,
    pub added: Vec<PolicyViolation>,
    pub removed: Vec<PolicyViolation>,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct SnapshotDiffAttribution {
    pub method: String,
    pub shared_worsened_axes: Vec<String>,
    pub candidates: Vec<AttributionCandidate>,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct AttributionCandidate {
    pub kind: String,
    pub id: String,
    pub confidence: f64,
    pub confidence_level: String,
    pub reasons: Vec<String>,
    pub changed_components: Vec<String>,
    pub matched_components: Vec<String>,
    pub matched_edges: Vec<Edge>,
    pub matched_policy_violations: Vec<PolicyViolation>,
    pub affected_axes: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct NullableSignatureIntVector {
    pub has_cycle: Option<i64>,
    pub scc_max_size: Option<i64>,
    pub max_depth: Option<i64>,
    pub fanout_risk: Option<i64>,
    pub boundary_violation_count: Option<i64>,
    pub abstraction_violation_count: Option<i64>,
    pub scc_excess_size: Option<i64>,
    pub max_fanout: Option<i64>,
    pub reachable_cone_size: Option<i64>,
    pub weighted_scc_risk: Option<i64>,
    pub projection_soundness_violation: Option<i64>,
    pub lsp_violation_count: Option<i64>,
    pub nilpotency_index: Option<i64>,
    pub runtime_propagation: Option<i64>,
    pub relation_complexity: Option<i64>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct MetricDeltaStatus {
    pub comparable: bool,
    pub reason: String,
    pub before_measured: bool,
    pub after_measured: bool,
}
