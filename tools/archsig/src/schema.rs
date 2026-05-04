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
pub const FEATURE_EXTENSION_REPORT_SCHEMA_VERSION: &str = "feature-extension-report-v0";
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
pub const LAW_POLICY_TEMPLATE_REGISTRY_SCHEMA_VERSION: &str = "law-policy-template-registry-v0";
pub const LAW_POLICY_TEMPLATE_REGISTRY_VALIDATION_REPORT_SCHEMA_VERSION: &str =
    "law-policy-template-registry-validation-report-v0";
pub const POLICY_DECISION_REPORT_SCHEMA_VERSION: &str = "policy-decision-report-v0";
pub const REPORT_ARTIFACT_RETENTION_MANIFEST_SCHEMA_VERSION: &str =
    "report-artifact-retention-manifest-v0";
pub const REPORT_ARTIFACT_RETENTION_VALIDATION_REPORT_SCHEMA_VERSION: &str =
    "report-artifact-retention-validation-report-v0";
pub const PR_COMMENT_SUMMARY_SCHEMA_VERSION: &str = "pr-comment-summary-v0";
pub const BASELINE_SUPPRESSION_REPORT_SCHEMA_VERSION: &str = "baseline-suppression-report-v0";
pub const PR_HISTORY_DATASET_SCHEMA_VERSION: &str = "pr-history-dataset-v0";
pub const FEATURE_EXTENSION_DATASET_SCHEMA_VERSION: &str = "feature-extension-dataset-v0";
pub const OUTCOME_LINKAGE_DATASET_SCHEMA_VERSION: &str = "outcome-linkage-dataset-v0";
pub const RUNTIME_EDGE_EVIDENCE_SCHEMA_VERSION: &str = "runtime-edge-evidence-v0";
pub const RUNTIME_PROJECTION_RULE_VERSION: &str = "runtime-edge-projection-v0";
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
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub unsupported_constructs: Vec<UnsupportedConstruct>,
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
pub struct PrHistoryDatasetV0 {
    pub schema_version: String,
    pub repository: RepositoryRef,
    pub records: Vec<PrHistoryRecordV0>,
    pub analysis_metadata: PrHistoryAnalysisMetadata,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct PrHistoryRecordV0 {
    pub pull_request: PullRequestRef,
    pub changed_file_summary: ChangedFileSummary,
    pub review_metadata: ReviewMetadata,
    pub artifact_refs: PrHistoryArtifactRefs,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ChangedFileSummary {
    pub changed_files: usize,
    pub additions: usize,
    pub deletions: usize,
    pub changed_components: Vec<String>,
    pub files: Vec<ChangedFileEntry>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ChangedFileEntry {
    pub path: String,
    pub additions: Option<usize>,
    pub deletions: Option<usize>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub status: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ReviewMetadata {
    pub review_comment_count: usize,
    pub review_thread_count: usize,
    pub review_round_count: usize,
    pub reviewer_count: usize,
    pub reviewers: Vec<String>,
    pub review_states: Vec<String>,
    pub first_review_latency_hours: Option<f64>,
    pub approval_latency_hours: Option<f64>,
    pub merge_latency_hours: Option<f64>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct PrHistoryArtifactRefs {
    pub signature_artifacts: Vec<PrHistoryArtifactRef>,
    pub feature_extension_reports: Vec<PrHistoryArtifactRef>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct PrHistoryArtifactRef {
    pub kind: String,
    pub path: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub commit_role: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub schema_version: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct PrHistoryAnalysisMetadata {
    pub lean_status: String,
    pub measurement_boundary: String,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct FeatureExtensionDatasetV0 {
    pub schema_version: String,
    pub repository: RepositoryRef,
    pub records: Vec<FeatureExtensionDatasetRecordV0>,
    pub analysis_metadata: FeatureExtensionDatasetAnalysisMetadata,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct FeatureExtensionDatasetRecordV0 {
    pub pull_request: PullRequestRef,
    pub pr_history_record_ref: FeatureExtensionPrHistoryRecordRef,
    pub changed_components: Vec<String>,
    pub feature_report_ref: PrHistoryArtifactRef,
    pub architecture_id: String,
    pub feature: AirFeature,
    pub split_status: String,
    pub claim_classification: String,
    pub obstruction_witness_taxonomy: Vec<FeatureExtensionObstructionTaxon>,
    pub coverage_gaps: Vec<FeatureExtensionDatasetCoverageGap>,
    pub repair_suggestion_adoption_candidates:
        Vec<FeatureExtensionRepairSuggestionAdoptionCandidate>,
    pub theorem_precondition_boundary: FeatureExtensionTheoremPreconditionBoundary,
    pub artifact_refs: FeatureExtensionDatasetArtifactRefs,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct FeatureExtensionPrHistoryRecordRef {
    pub pr_number: usize,
    pub base_commit: String,
    pub head_commit: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct FeatureExtensionObstructionTaxon {
    pub kind: String,
    pub layer: String,
    pub claim_level: String,
    pub claim_classification: String,
    pub measurement_boundary: String,
    pub witness_count: usize,
    pub witness_refs: Vec<String>,
    pub components: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct FeatureExtensionDatasetCoverageGap {
    pub layer: String,
    pub measurement_boundary: String,
    pub unmeasured_axes: Vec<String>,
    pub unsupported_constructs: Vec<String>,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct FeatureExtensionRepairSuggestionAdoptionCandidate {
    pub suggestion_id: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub repair_rule_id: Option<String>,
    pub target_witness_kind: String,
    pub proposed_operation: String,
    pub source_witness_refs: Vec<String>,
    pub source_coverage_gap_refs: Vec<String>,
    pub adoption_status: String,
    pub required_preconditions: Vec<String>,
    pub traceability: Vec<String>,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct FeatureExtensionTheoremPreconditionBoundary {
    pub summary: TheoremPreconditionCheckSummary,
    pub missing_preconditions: Vec<String>,
    pub blocked_claim_refs: Vec<String>,
    pub measured_witness_count: usize,
    pub formal_proved_claim_count: usize,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct FeatureExtensionDatasetArtifactRefs {
    pub signature_artifacts: Vec<PrHistoryArtifactRef>,
    pub feature_extension_report: PrHistoryArtifactRef,
    pub theorem_precondition_reports: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct FeatureExtensionDatasetAnalysisMetadata {
    pub lean_status: String,
    pub measurement_boundary: String,
    pub join_keys: Vec<String>,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct OutcomeLinkageInputV0 {
    pub schema_version: String,
    pub repository: RepositoryRef,
    pub records: Vec<OutcomeObservationV0>,
    pub analysis_metadata: OutcomeLinkageAnalysisMetadata,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct OutcomeLinkageDatasetV0 {
    pub schema_version: String,
    pub repository: RepositoryRef,
    pub records: Vec<OutcomeLinkageDatasetRecordV0>,
    pub analysis_metadata: OutcomeLinkageAnalysisMetadata,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct OutcomeLinkageDatasetRecordV0 {
    pub pull_request: PullRequestRef,
    pub feature_dataset_record_ref: OutcomeFeatureDatasetRecordRef,
    pub changed_components: Vec<String>,
    pub split_status: String,
    pub claim_classification: String,
    pub obstruction_witness_taxonomy: Vec<FeatureExtensionObstructionTaxon>,
    pub outcome_observation: OutcomeObservationV0,
    pub correlation_inputs: OutcomeCorrelationInputs,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct OutcomeFeatureDatasetRecordRef {
    pub pr_number: usize,
    pub base_commit: String,
    pub head_commit: String,
    pub feature_report_path: String,
    pub architecture_id: String,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct OutcomeObservationV0 {
    pub pr_number: usize,
    pub review_cost: ReviewCostOutcome,
    pub follow_up_fix_count: OutcomeMetric<usize>,
    pub rollback: OutcomeMetric<bool>,
    pub incident_affected_component_count: OutcomeMetric<usize>,
    pub mttr_hours: OutcomeMetric<f64>,
    pub traceability: OutcomeTraceabilityRefs,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ReviewCostOutcome {
    pub review_comment_count: OutcomeMetric<usize>,
    pub review_thread_count: OutcomeMetric<usize>,
    pub review_round_count: OutcomeMetric<usize>,
    pub reviewer_count: OutcomeMetric<usize>,
    pub first_review_latency_hours: OutcomeMetric<f64>,
    pub approval_latency_hours: OutcomeMetric<f64>,
    pub merge_latency_hours: OutcomeMetric<f64>,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct OutcomeMetric<T> {
    pub boundary: String,
    pub value: Option<T>,
    pub reason: Option<String>,
    pub source_refs: Vec<String>,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct OutcomeTraceabilityRefs {
    pub pr_refs: Vec<OutcomeExternalRef>,
    pub issue_refs: Vec<OutcomeExternalRef>,
    pub incident_refs: Vec<OutcomeExternalRef>,
    pub artifact_refs: Vec<PrHistoryArtifactRef>,
    pub missing_or_private_data: Vec<String>,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct OutcomeExternalRef {
    pub kind: String,
    pub id: String,
    pub url: Option<String>,
    pub visibility: Option<String>,
    pub labels: Vec<String>,
    pub affected_components: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct OutcomeCorrelationInputs {
    pub obstruction_witness_refs: Vec<String>,
    pub obstruction_witness_kinds: Vec<String>,
    pub outcome_metric_refs: Vec<String>,
    pub measurement_boundary: String,
    pub non_conclusions: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct OutcomeLinkageAnalysisMetadata {
    pub lean_status: String,
    pub measurement_boundary: String,
    pub join_keys: Vec<String>,
    pub non_conclusions: Vec<String>,
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
    pub input: FeatureReportInput,
    pub architecture_id: String,
    pub revision: AirRevision,
    pub feature: AirFeature,
    pub review_summary: FeatureReportReviewSummary,
    pub architecture_summary: FeatureReportArchitectureSummary,
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
