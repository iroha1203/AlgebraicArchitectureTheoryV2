use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::error::Error;
use std::ffi::OsStr;
use std::fs;
use std::path::{Component as PathComponent, Path, PathBuf};

use serde::{Deserialize, Serialize};
use serde_json::Value;
use walkdir::{DirEntry, WalkDir};

pub const SCHEMA_VERSION: &str = "archsig-sig0-v0";
pub const COMPONENT_KIND: &str = "lean-module";
pub const VALIDATION_REPORT_SCHEMA_VERSION: &str = "component-universe-validation-report-v0";
pub const EMPIRICAL_DATASET_SCHEMA_VERSION: &str = "empirical-signature-dataset-v0";
pub const SIGNATURE_SNAPSHOT_STORE_SCHEMA_VERSION: &str = "signature-snapshot-store-v0";
pub const SIGNATURE_DIFF_REPORT_SCHEMA_VERSION: &str = "signature-diff-report-v0";
pub const AIR_SCHEMA_VERSION: &str = "aat-air-v0";
pub const AIR_VALIDATION_REPORT_SCHEMA_VERSION: &str = "aat-air-validation-report-v0";
pub const FEATURE_EXTENSION_REPORT_SCHEMA_VERSION: &str = "feature-extension-report-v0";
pub const THEOREM_PRECONDITION_CHECK_REPORT_SCHEMA_VERSION: &str =
    "theorem-precondition-check-report-v0";
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

const DATASET_SIGNATURE_AXES: [&str; 16] = [
    "hasCycle",
    "sccMaxSize",
    "maxDepth",
    "fanoutRisk",
    "boundaryViolationCount",
    "abstractionViolationCount",
    "sccExcessSize",
    "maxFanout",
    "reachableConeSize",
    "weightedSccRisk",
    "projectionSoundnessViolation",
    "lspViolationCount",
    "nilpotencyIndex",
    "runtimePropagation",
    "relationComplexity",
    "empiricalChangeCost",
];

const DATASET_DELTA_AXES: [&str; 15] = [
    "hasCycle",
    "sccMaxSize",
    "maxDepth",
    "fanoutRisk",
    "boundaryViolationCount",
    "abstractionViolationCount",
    "sccExcessSize",
    "maxFanout",
    "reachableConeSize",
    "weightedSccRisk",
    "projectionSoundnessViolation",
    "lspViolationCount",
    "nilpotencyIndex",
    "runtimePropagation",
    "relationComplexity",
];

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
    fn relation_complexity(&self) -> usize {
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
    pub interpreted_extension: FeatureReportInterpretedExtension,
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
    pub repair_suggestions: Vec<String>,
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

#[derive(Debug, Clone, PartialEq, Eq)]
struct ImportEdge {
    source: String,
    target: String,
    evidence: String,
}

pub fn extract_sig0(root: &Path) -> Result<Sig0Document, Box<dyn Error>> {
    extract_sig0_with_policy(root, None)
}

pub fn extract_sig0_with_policy(
    root: &Path,
    policy_path: Option<&Path>,
) -> Result<Sig0Document, Box<dyn Error>> {
    extract_sig0_with_runtime(root, policy_path, None)
}

pub fn extract_sig0_with_runtime(
    root: &Path,
    policy_path: Option<&Path>,
    runtime_edges_path: Option<&Path>,
) -> Result<Sig0Document, Box<dyn Error>> {
    let root = root.to_path_buf();
    let mut components = Vec::new();
    let mut import_edges = Vec::new();

    for path in lean_files(&root)? {
        let relative_path = normalize_relative_path(&root, &path)?;
        let module_id = module_id_from_relative_path(&relative_path)?;
        components.push(Component {
            id: module_id.clone(),
            path: relative_path,
        });

        let source = fs::read_to_string(&path)?;
        for parsed_import in parse_imports(&source) {
            import_edges.push(ImportEdge {
                source: module_id.clone(),
                target: parsed_import.module,
                evidence: parsed_import.evidence,
            });
        }
    }

    components.sort_by(|a, b| a.id.cmp(&b.id).then(a.path.cmp(&b.path)));

    let edges = dedup_edges(import_edges);
    let mut signature = compute_signature(&components, &edges);

    let mut metric_status = BTreeMap::new();
    for axis in ["hasCycle", "sccMaxSize", "maxDepth", "fanoutRisk"] {
        metric_status.insert(axis.to_string(), measured_status("archsig:import-graph"));
    }
    metric_status.insert(
        "boundaryViolationCount".to_string(),
        MetricStatus {
            measured: false,
            reason: Some("policy file not provided".to_string()),
            source: None,
        },
    );
    metric_status.insert(
        "abstractionViolationCount".to_string(),
        MetricStatus {
            measured: false,
            reason: Some("policy file not provided".to_string()),
            source: None,
        },
    );
    let mut policies = Policies {
        boundary_allowed: Vec::new(),
        abstraction_allowed: Vec::new(),
        policy_id: None,
        schema_version: None,
        boundary_group_count: None,
        abstraction_relation_count: None,
    };
    let mut policy_violations = Vec::new();

    if let Some(policy_path) = policy_path {
        let policy = PolicyFile::read(policy_path)?;
        policies = Policies {
            boundary_allowed: Vec::new(),
            abstraction_allowed: Vec::new(),
            policy_id: Some(policy.policy_id.clone()),
            schema_version: Some(policy.schema_version.clone()),
            boundary_group_count: policy
                .boundary
                .as_ref()
                .map(|boundary| boundary.groups.len()),
            abstraction_relation_count: policy
                .abstraction
                .as_ref()
                .map(|abstraction| abstraction.relations.len()),
        };
        let policy_source = format!("policy:{}", policy.policy_id);

        match policy.boundary.as_ref() {
            Some(boundary) => match measure_boundary(boundary, &components, &edges) {
                Ok((count, violations)) => {
                    signature.boundary_violation_count = count;
                    metric_status.insert(
                        "boundaryViolationCount".to_string(),
                        measured_status(&policy_source),
                    );
                    policy_violations.extend(violations);
                }
                Err(reason) => {
                    signature.boundary_violation_count = 0;
                    metric_status.insert(
                        "boundaryViolationCount".to_string(),
                        unmeasured_status(reason),
                    );
                }
            },
            None => {
                signature.boundary_violation_count = 0;
                metric_status.insert(
                    "boundaryViolationCount".to_string(),
                    unmeasured_status("boundary policy not provided".to_string()),
                );
            }
        }

        match policy.abstraction.as_ref() {
            Some(abstraction) => match measure_abstraction(abstraction, &components, &edges) {
                Ok((count, violations)) => {
                    signature.abstraction_violation_count = count;
                    metric_status.insert(
                        "abstractionViolationCount".to_string(),
                        measured_status(&policy_source),
                    );
                    policy_violations.extend(violations);
                }
                Err(reason) => {
                    signature.abstraction_violation_count = 0;
                    metric_status.insert(
                        "abstractionViolationCount".to_string(),
                        unmeasured_status(reason),
                    );
                }
            },
            None => {
                signature.abstraction_violation_count = 0;
                metric_status.insert(
                    "abstractionViolationCount".to_string(),
                    unmeasured_status("abstraction policy not provided".to_string()),
                );
            }
        }
    }

    let (runtime_edge_evidence, runtime_dependency_graph) =
        if let Some(runtime_edges_path) = runtime_edges_path {
            let evidence = RuntimeEdgeEvidenceFile::read(runtime_edges_path, &components)?;
            let projection = project_runtime_dependency_graph(&evidence);
            metric_status.insert(
                "runtimePropagation".to_string(),
                measured_status(RUNTIME_PROJECTION_RULE_VERSION),
            );
            (evidence, Some(projection))
        } else {
            (Vec::new(), None)
        };

    Ok(Sig0Document {
        schema_version: SCHEMA_VERSION.to_string(),
        root: root.display().to_string(),
        component_kind: COMPONENT_KIND.to_string(),
        components,
        edges,
        policies,
        signature,
        metric_status,
        policy_violations,
        runtime_edge_evidence,
        runtime_dependency_graph,
    })
}

pub fn validate_component_universe_report(
    document: &Sig0Document,
    input_path: &str,
    universe_mode: &str,
) -> Result<ComponentUniverseValidationReport, Box<dyn Error>> {
    if !matches!(universe_mode, "local-only" | "closed-with-external") {
        return Err(format!("unsupported universe mode: {universe_mode}").into());
    }

    let component_ids: BTreeSet<String> = document
        .components
        .iter()
        .map(|component| component.id.clone())
        .collect();
    let local_roots = component_roots(&component_ids);
    let external_edges = external_edges(document, &component_ids, &local_roots);
    let local_edge_count = document
        .edges
        .iter()
        .filter(|edge| component_ids.contains(&edge.source) && component_ids.contains(&edge.target))
        .count();

    let mut checks = Vec::new();

    checks.push(check_schema_version(&document.schema_version));
    checks.push(check_component_id_nodup(&document.components));
    checks.push(check_component_path_nodup(&document.components));
    checks.push(check_edge_endpoint_resolved(
        &document.edges,
        &component_ids,
        &local_roots,
    ));
    checks.push(check_edge_closure_local(
        &document.edges,
        &component_ids,
        &local_roots,
    ));
    checks.push(check_external_edge_targets(&external_edges, universe_mode));
    checks.push(check_metric_status_complete(&document.metric_status));
    checks.push(check_metric_measured(
        "boundary-policy-status",
        "boundary violation metric is measured",
        "boundaryViolationCount",
        &document.metric_status,
    ));
    checks.push(check_metric_measured(
        "abstraction-policy-status",
        "abstraction violation metric is measured",
        "abstractionViolationCount",
        &document.metric_status,
    ));
    checks.push(validation_check(
        "extractor-warning-status",
        "extractor output has no warnings",
        "pass",
    ));

    let failed_check_count = count_checks(&checks, "fail");
    let warning_check_count = count_checks(&checks, "warn");
    let not_measured_check_count = count_checks(&checks, "not_measured");
    let result = if failed_check_count > 0 {
        "fail"
    } else if warning_check_count > 0 || not_measured_check_count > 0 {
        "warn"
    } else {
        "pass"
    };

    let mut warnings = Vec::new();
    if universe_mode == "local-only" && !external_edges.is_empty() {
        warnings
            .push("local-only universe excludes external or synthetic import targets".to_string());
    }

    Ok(ComponentUniverseValidationReport {
        schema_version: VALIDATION_REPORT_SCHEMA_VERSION.to_string(),
        input: ValidationInput {
            schema_version: document.schema_version.clone(),
            path: input_path.to_string(),
            root: document.root.clone(),
            component_kind: document.component_kind.clone(),
        },
        universe_mode: universe_mode.to_string(),
        summary: ValidationSummary {
            result: result.to_string(),
            component_count: document.components.len(),
            local_edge_count,
            external_edge_count: external_edges.len(),
            failed_check_count,
            warning_check_count,
            not_measured_check_count,
        },
        checks,
        warnings,
    })
}

pub fn validate_air_document_report(
    document: &AirDocumentV0,
    input_path: &str,
    strict_measured_evidence: bool,
) -> AirValidationReport {
    let mut checks = Vec::new();

    checks.push(check_air_schema_version(&document.schema_version));
    checks.push(check_air_unique_ids(document));
    checks.push(check_air_artifact_refs(document));
    checks.push(check_air_component_refs(document));
    checks.push(check_air_evidence_refs(document));
    checks.push(check_air_claim_refs(document));
    checks.push(check_air_path_and_witness_refs(document));
    checks.push(check_air_coverage_universe_refs(document));
    checks.push(check_air_signature_measurement_boundary(document));
    checks.push(check_air_claim_measurement_boundary(document));
    checks.push(check_air_measured_claim_evidence(
        document,
        strict_measured_evidence,
    ));

    let failed_check_count = count_checks(&checks, "fail");
    let warning_check_count = count_checks(&checks, "warn");
    let result = if failed_check_count > 0 {
        "fail"
    } else if warning_check_count > 0 {
        "warn"
    } else {
        "pass"
    };
    let warnings = checks
        .iter()
        .filter(|check| check.result == "warn")
        .filter_map(|check| check.reason.clone())
        .collect();

    AirValidationReport {
        schema_version: AIR_VALIDATION_REPORT_SCHEMA_VERSION.to_string(),
        input: AirValidationInput {
            schema_version: document.schema_version.clone(),
            path: input_path.to_string(),
            architecture_id: document.architecture_id.clone(),
        },
        summary: AirValidationSummary {
            result: result.to_string(),
            component_count: document.components.len(),
            relation_count: document.relations.len(),
            evidence_count: document.evidence.len(),
            claim_count: document.claims.len(),
            failed_check_count,
            warning_check_count,
        },
        checks,
        warnings,
    }
}

pub fn static_theorem_package_registry() -> TheoremPackageRegistryV0 {
    TheoremPackageRegistryV0 {
        schema_version: THEOREM_PRECONDITION_CHECK_REPORT_SCHEMA_VERSION.to_string(),
        scope: "static theorem package v0".to_string(),
        packages: vec![TheoremPackageMetadataV0 {
            package_id: "static-theorem-package-v0".to_string(),
            lean_entrypoint: "SelectedStaticSplitExtension".to_string(),
            theorem_refs: vec![
                "SelectedStaticSplitExtension".to_string(),
                "CoreEdgesPreserved".to_string(),
                "DeclaredInterfaceFactorization".to_string(),
                "NoNewForbiddenStaticEdge".to_string(),
                "EmbeddingPolicyPreserved".to_string(),
            ],
            supported_subject_refs: vec![
                "extension.embedding".to_string(),
                "extension.feature".to_string(),
                "extension.split".to_string(),
                "signature.hasCycle".to_string(),
                "signature.projectionSoundnessViolation".to_string(),
                "signature.lspViolationCount".to_string(),
                "signature.boundaryViolationCount".to_string(),
                "signature.abstractionViolationCount".to_string(),
            ],
            supported_axes: vec![
                "hasCycle".to_string(),
                "projectionSoundnessViolation".to_string(),
                "lspViolationCount".to_string(),
                "boundaryViolationCount".to_string(),
                "abstractionViolationCount".to_string(),
            ],
            claim_level: "formal".to_string(),
            claim_classification: "proved".to_string(),
            measurement_boundary: "measuredZero".to_string(),
            required_assumptions: vec![
                "core edges are preserved".to_string(),
                "feature/core interactions factor through a declared interface".to_string(),
                "no new forbidden static edge is introduced".to_string(),
                "embedding policy is preserved".to_string(),
            ],
            coverage_assumptions: vec![
                "static dependency graph is inside the measured universe".to_string(),
                "policy selector covers the checked static edges".to_string(),
            ],
            exactness_assumptions: vec![
                "AIR component and relation identifiers match the Lean package parameters"
                    .to_string(),
            ],
            missing_preconditions: Vec::new(),
            non_conclusions: vec![
                "static theorem package does not conclude runtime flatness".to_string(),
                "static theorem package does not conclude semantic flatness".to_string(),
                "static theorem package does not prove extractor completeness".to_string(),
            ],
        }],
    }
}

pub fn build_theorem_precondition_check_report(
    document: &AirDocumentV0,
    input_path: &str,
) -> TheoremPreconditionCheckReportV0 {
    let registry = static_theorem_package_registry();
    let checks = theorem_precondition_checks(document, &registry);
    let summary = theorem_precondition_check_summary(&checks, document.claims.len());

    TheoremPreconditionCheckReportV0 {
        schema_version: THEOREM_PRECONDITION_CHECK_REPORT_SCHEMA_VERSION.to_string(),
        input: TheoremPreconditionCheckInput {
            schema_version: document.schema_version.clone(),
            path: input_path.to_string(),
            architecture_id: document.architecture_id.clone(),
        },
        registry,
        summary,
        checks,
    }
}

pub fn build_feature_extension_report(
    document: &AirDocumentV0,
    input_path: &str,
) -> FeatureExtensionReportV0 {
    let claim_by_id: BTreeMap<String, &AirClaim> = document
        .claims
        .iter()
        .map(|claim| (claim.claim_id.clone(), claim))
        .collect();
    let evidence_by_id: BTreeMap<String, &AirEvidence> = document
        .evidence
        .iter()
        .map(|evidence| (evidence.evidence_id.clone(), evidence))
        .collect();

    let preserved_invariants = feature_report_preserved_invariants(document);
    let changed_invariants = feature_report_changed_invariants(document);
    let introduced_obstruction_witnesses =
        feature_report_obstruction_witnesses(document, &claim_by_id, &evidence_by_id);
    let coverage_gaps = feature_report_coverage_gaps(document);
    let split_status = feature_report_split_status(
        document,
        &preserved_invariants,
        &changed_invariants,
        &introduced_obstruction_witnesses,
    );
    let theorem_package_refs = feature_report_theorem_package_refs(document);
    let theorem_precondition_report = build_theorem_precondition_check_report(document, input_path);
    let discharged_assumptions = feature_report_discharged_assumptions(document);
    let undischarged_assumptions = feature_report_undischarged_assumptions(document);
    let unsupported_constructs = feature_report_unsupported_constructs(&coverage_gaps);
    let repair_suggestions =
        feature_report_repair_suggestions(&introduced_obstruction_witnesses, &coverage_gaps);
    let non_conclusions = feature_report_non_conclusions(document, &split_status, &coverage_gaps);
    let measured_axes = document
        .signature
        .axes
        .iter()
        .filter(|axis| axis.measured)
        .map(|axis| axis.axis.clone())
        .collect();
    let unmeasured_axes = document
        .signature
        .axes
        .iter()
        .filter(|axis| !axis.measured)
        .map(|axis| axis.axis.clone())
        .collect();

    FeatureExtensionReportV0 {
        schema_version: FEATURE_EXTENSION_REPORT_SCHEMA_VERSION.to_string(),
        input: FeatureReportInput {
            schema_version: document.schema_version.clone(),
            path: input_path.to_string(),
            architecture_id: document.architecture_id.clone(),
        },
        architecture_id: document.architecture_id.clone(),
        revision: document.revision.clone(),
        feature: document.feature.clone(),
        review_summary: FeatureReportReviewSummary {
            split_status: split_status.clone(),
            claim_classification: feature_report_claim_classification(&split_status),
            top_witnesses: introduced_obstruction_witnesses
                .iter()
                .take(3)
                .map(|witness| witness.kind.clone())
                .collect(),
            required_action: feature_report_required_action(
                &split_status,
                &introduced_obstruction_witnesses,
                &coverage_gaps,
            ),
        },
        architecture_summary: FeatureReportArchitectureSummary {
            component_count: document.components.len(),
            relation_count: document.relations.len(),
            static_relation_count: count_air_relations(document, "static"),
            runtime_relation_count: count_air_relations(document, "runtime"),
            policy_relation_count: count_air_relations(document, "policy"),
            semantic_diagram_count: document.semantic_diagrams.len(),
            measured_axes,
            unmeasured_axes,
        },
        interpreted_extension: FeatureReportInterpretedExtension {
            embedding_claim_ref: document.extension.embedding_claim_ref.clone(),
            feature_view_claim_ref: document.extension.feature_view_claim_ref.clone(),
            interaction_claim_refs: document.extension.interaction_claim_refs.clone(),
            split_claim_ref: document.extension.split_claim_ref.clone(),
            added_components: document
                .components
                .iter()
                .filter(|component| component.lifecycle == "added")
                .map(|component| component.id.clone())
                .collect(),
            changed_components: document
                .components
                .iter()
                .filter(|component| component.lifecycle == "changed")
                .map(|component| component.id.clone())
                .collect(),
            added_relations: document
                .relations
                .iter()
                .filter(|relation| relation.lifecycle == "added")
                .map(|relation| relation.id.clone())
                .collect(),
        },
        split_status,
        preserved_invariants,
        changed_invariants,
        introduced_obstruction_witnesses,
        eliminated_obstruction_witnesses: Vec::new(),
        complexity_transfer_candidates: Vec::new(),
        semantic_path_summary: FeatureReportSemanticPathSummary {
            path_count: document.architecture_paths.len(),
            diagram_count: document.semantic_diagrams.len(),
            nonfillability_witness_count: document.nonfillability_witnesses.len(),
        },
        theorem_package_refs,
        theorem_precondition_summary: theorem_precondition_report.summary,
        theorem_precondition_checks: theorem_precondition_report.checks,
        discharged_assumptions,
        undischarged_assumptions,
        coverage_gaps,
        unsupported_constructs,
        repair_suggestions,
        empirical_annotations: vec![
            "Feature Extension Report v0 is a static tooling report".to_string(),
            "Runtime and semantic conclusions require separate evidence".to_string(),
        ],
        non_conclusions,
    }
}

pub fn build_empirical_dataset(
    before: &Sig0Document,
    after: &Sig0Document,
    mut input: EmpiricalDatasetInput,
    after_commit_role: &str,
) -> Result<EmpiricalSignatureDatasetV0, Box<dyn Error>> {
    if !matches!(after_commit_role, "head" | "merge") {
        return Err(format!("unsupported after commit role: {after_commit_role}").into());
    }

    let before_snapshot = signature_snapshot(
        before,
        GitCommitRef {
            sha: input.pull_request.base_commit.clone(),
            role: "base".to_string(),
        },
    );
    let after_sha = match after_commit_role {
        "head" => input.pull_request.head_commit.clone(),
        "merge" => input
            .pull_request
            .merge_commit
            .clone()
            .ok_or("after commit role merge requires pullRequest.mergeCommit")?,
        _ => unreachable!("after commit role is checked above"),
    };
    let after_snapshot = signature_snapshot(
        after,
        GitCommitRef {
            sha: after_sha,
            role: after_commit_role.to_string(),
        },
    );
    let delta_signature_signed = delta_signature_signed(&before_snapshot, &after_snapshot);
    let metric_delta_status = metric_delta_status(&before_snapshot, &after_snapshot);

    input.analysis_metadata.signature_after_commit_role = after_commit_role.to_string();

    Ok(EmpiricalSignatureDatasetV0 {
        schema_version: EMPIRICAL_DATASET_SCHEMA_VERSION.to_string(),
        repository: input.repository,
        pull_request: input.pull_request,
        signature_before: before_snapshot,
        signature_after: after_snapshot,
        delta_signature_signed,
        metric_delta_status,
        pr_metrics: input.pr_metrics,
        issue_incident_links: input.issue_incident_links,
        analysis_metadata: input.analysis_metadata,
    })
}

pub fn build_signature_snapshot_record(
    document: &Sig0Document,
    validation_report: Option<&ComponentUniverseValidationReport>,
    input: SnapshotRecordInput,
) -> SignatureSnapshotStoreRecordV0 {
    let validation_summary =
        snapshot_validation_summary(validation_report, input.validation_report_path.clone());
    let mut exclusion_reasons = Vec::new();
    match validation_summary.result.as_str() {
        "fail" => exclusion_reasons.push("validationSummary.result = fail".to_string()),
        "not_run" => exclusion_reasons.push("validationSummary.result = not_run".to_string()),
        _ => {}
    }

    SignatureSnapshotStoreRecordV0 {
        schema_version: SIGNATURE_SNAPSHOT_STORE_SCHEMA_VERSION.to_string(),
        repository: input.repository,
        revision: input.revision,
        scan: input.scan,
        extractor: SnapshotExtractorMetadata {
            name: EXTRACTOR_NAME.to_string(),
            version: EXTRACTOR_VERSION.to_string(),
            rule_set_version: RULE_SET_VERSION.to_string(),
            input_schema_version: document.schema_version.clone(),
        },
        policy: SnapshotPolicyMetadata {
            policy_id: document.policies.policy_id.clone(),
            schema_version: document.policies.schema_version.clone(),
            version: input.policy_version,
            source_path: input.policy_source_path.clone(),
            content_hash: input.policy_content_hash,
        },
        signature: dataset_signature_shape(document),
        metric_status: dataset_metric_status(document),
        validation_summary,
        artifacts: SnapshotArtifacts {
            extractor_output_path: input.extractor_output_path,
            validation_report_path: input.validation_report_path,
            policy_path: input.policy_source_path,
        },
        analysis_metadata: SnapshotAnalysisMetadata {
            excluded_from_primary_diff: !exclusion_reasons.is_empty(),
            exclusion_reasons,
            tags: input.tags,
            notes: input.notes,
        },
    }
}

pub fn build_signature_diff_report(
    before: &SignatureSnapshotStoreRecordV0,
    after: &SignatureSnapshotStoreRecordV0,
    before_document: Option<&Sig0Document>,
    after_document: Option<&Sig0Document>,
    pr_metadata: &[EmpiricalDatasetInput],
) -> SignatureDiffReportV0 {
    let before_snapshot = store_record_signature_snapshot(before, "before");
    let after_snapshot = store_record_signature_snapshot(after, "after");
    let delta_signature_signed = delta_signature_signed(&before_snapshot, &after_snapshot);
    let metric_delta_status = metric_delta_status(&before_snapshot, &after_snapshot);
    let (worsened_axes, improved_axes, unchanged_axes, unmeasured_axes) =
        classify_axis_deltas(before, after, &metric_delta_status);
    let evidence_diff = snapshot_evidence_diff(before_document, after_document);
    let attribution = snapshot_diff_attribution(after, &evidence_diff, &worsened_axes, pr_metadata);

    SignatureDiffReportV0 {
        schema_version: SIGNATURE_DIFF_REPORT_SCHEMA_VERSION.to_string(),
        before: snapshot_diff_endpoint(before),
        after: snapshot_diff_endpoint(after),
        comparison_status: snapshot_comparison_status(before, after),
        delta_signature_signed,
        metric_delta_status,
        worsened_axes,
        improved_axes,
        unchanged_axes,
        unmeasured_axes,
        evidence_diff,
        attribution,
    }
}

pub fn build_air_document(
    sig0: &Sig0Document,
    validation: Option<&ComponentUniverseValidationReport>,
    diff: Option<&SignatureDiffReportV0>,
    pr_metadata: Option<&EmpiricalDatasetInput>,
    input: AirDocumentInput,
) -> AirDocumentV0 {
    let signature = dataset_signature_shape(sig0);
    let metric_status = dataset_metric_status(sig0);
    let signature_axes = air_signature_axes(&signature, &metric_status);
    let component_lifecycle = air_component_lifecycle(diff);

    let mut artifacts = vec![AirArtifact {
        artifact_id: "artifact-sig0".to_string(),
        kind: "sig0".to_string(),
        schema_version: Some(sig0.schema_version.clone()),
        path: Some(input.sig0_path),
        content_hash: None,
        produced_by: Some(EXTRACTOR_NAME.to_string()),
    }];
    if let (Some(report), Some(path)) = (validation, input.validation_path) {
        artifacts.push(AirArtifact {
            artifact_id: "artifact-validation".to_string(),
            kind: "validation".to_string(),
            schema_version: Some(report.schema_version.clone()),
            path: Some(path),
            content_hash: None,
            produced_by: Some(EXTRACTOR_NAME.to_string()),
        });
    }
    if let (Some(report), Some(path)) = (diff, input.diff_path) {
        artifacts.push(AirArtifact {
            artifact_id: "artifact-diff".to_string(),
            kind: "diff".to_string(),
            schema_version: Some(report.schema_version.clone()),
            path: Some(path),
            content_hash: None,
            produced_by: Some(EXTRACTOR_NAME.to_string()),
        });
    }
    if input.pr_metadata_path.is_some() {
        artifacts.push(AirArtifact {
            artifact_id: "artifact-pr-metadata".to_string(),
            kind: "pr_metadata".to_string(),
            schema_version: Some(EMPIRICAL_DATASET_SCHEMA_VERSION.to_string()),
            path: input.pr_metadata_path,
            content_hash: None,
            produced_by: Some(EXTRACTOR_NAME.to_string()),
        });
    }
    if input.law_policy_path.is_some() {
        artifacts.push(AirArtifact {
            artifact_id: "artifact-law-policy".to_string(),
            kind: "policy".to_string(),
            schema_version: sig0.policies.schema_version.clone(),
            path: input.law_policy_path,
            content_hash: None,
            produced_by: None,
        });
    }

    let mut evidence: Vec<AirEvidence> = artifacts
        .iter()
        .map(|artifact| AirEvidence {
            evidence_id: format!("evidence-{}-artifact", artifact.kind.replace('_', "-")),
            kind: artifact_evidence_kind(&artifact.kind),
            artifact_ref: Some(artifact.artifact_id.clone()),
            path: artifact.path.clone(),
            symbol: None,
            line: None,
            rule_id: artifact.schema_version.clone(),
            confidence: Some("high".to_string()),
        })
        .collect();
    let mut relations = Vec::new();
    let component_paths: BTreeMap<String, String> = sig0
        .components
        .iter()
        .map(|component| (component.id.clone(), component.path.clone()))
        .collect();
    for (index, edge) in sig0.edges.iter().enumerate() {
        let evidence_id = numbered_id("evidence-static", index);
        evidence.push(AirEvidence {
            evidence_id: evidence_id.clone(),
            kind: "source_location".to_string(),
            artifact_ref: Some("artifact-sig0".to_string()),
            path: component_paths.get(&edge.source).cloned(),
            symbol: Some(edge.source.clone()),
            line: None,
            rule_id: Some(edge.evidence.clone()),
            confidence: Some("high".to_string()),
        });
        relations.push(AirRelation {
            id: numbered_id("relation-static", index),
            layer: "static".to_string(),
            from_component: Some(edge.source.clone()),
            to_component: Some(edge.target.clone()),
            kind: edge.kind.clone(),
            lifecycle: relation_lifecycle(edge, diff),
            protected_by: None,
            extraction_rule: Some("lean-import".to_string()),
            evidence_refs: vec![evidence_id],
        });
    }
    for (index, runtime) in sig0.runtime_edge_evidence.iter().enumerate() {
        let evidence_id = numbered_id("evidence-runtime", index);
        evidence.push(AirEvidence {
            evidence_id: evidence_id.clone(),
            kind: "runtime_trace".to_string(),
            artifact_ref: Some("artifact-sig0".to_string()),
            path: Some(runtime.evidence_location.path.clone()),
            symbol: runtime.evidence_location.symbol.clone(),
            line: runtime.evidence_location.line,
            rule_id: Some(runtime.label.clone()),
            confidence: runtime.confidence.clone(),
        });
        relations.push(AirRelation {
            id: numbered_id("relation-runtime", index),
            layer: "runtime".to_string(),
            from_component: Some(runtime.source.clone()),
            to_component: Some(runtime.target.clone()),
            kind: runtime_relation_kind(&runtime.label),
            lifecycle: "after".to_string(),
            protected_by: runtime.circuit_breaker_coverage.clone(),
            extraction_rule: Some(RUNTIME_PROJECTION_RULE_VERSION.to_string()),
            evidence_refs: vec![evidence_id],
        });
    }
    for (index, violation) in sig0.policy_violations.iter().enumerate() {
        let evidence_id = numbered_id("evidence-policy", index);
        evidence.push(AirEvidence {
            evidence_id: evidence_id.clone(),
            kind: "policy_rule".to_string(),
            artifact_ref: Some("artifact-sig0".to_string()),
            path: None,
            symbol: None,
            line: None,
            rule_id: violation.relation_ids.as_ref().map(|ids| ids.join(",")),
            confidence: Some("high".to_string()),
        });
        relations.push(AirRelation {
            id: numbered_id("relation-policy", index),
            layer: "policy".to_string(),
            from_component: Some(violation.source.clone()),
            to_component: Some(violation.target.clone()),
            kind: "policy_rule".to_string(),
            lifecycle: "after".to_string(),
            protected_by: None,
            extraction_rule: Some(violation.axis.clone()),
            evidence_refs: vec![evidence_id],
        });
    }

    let components = sig0
        .components
        .iter()
        .map(|component| AirComponent {
            id: component.id.clone(),
            kind: "module".to_string(),
            lifecycle: component_lifecycle
                .get(&component.id)
                .cloned()
                .unwrap_or_else(|| "after".to_string()),
            owner: None,
            evidence_refs: Vec::new(),
        })
        .collect();
    let claims = air_claims(&signature_axes);
    let interaction_claim_refs = air_interaction_claim_refs(&claims);
    let revision = air_revision(diff, pr_metadata);
    let feature = air_feature(pr_metadata);

    AirDocumentV0 {
        schema_version: AIR_SCHEMA_VERSION.to_string(),
        architecture_id: sig0.root.clone(),
        ids: AirIdPolicies {
            component_id_policy: "sig0 component id".to_string(),
            relation_id_policy: "layer-prefixed stable ordinal".to_string(),
            evidence_id_policy: "layer-prefixed stable ordinal".to_string(),
            claim_id_policy: "axis-prefixed stable id".to_string(),
        },
        revision,
        feature,
        artifacts,
        evidence,
        components,
        relations,
        policies: AirPolicies {
            laws: sig0
                .policies
                .policy_id
                .iter()
                .map(|policy_id| format!("policy:{policy_id}"))
                .collect(),
            boundaries: sig0
                .policies
                .boundary_group_count
                .map(|count| vec![format!("boundary groups: {count}")])
                .unwrap_or_default(),
            allowed_edges: sig0.policies.boundary_allowed.clone(),
            forbidden_edges: sig0
                .policy_violations
                .iter()
                .map(|violation| {
                    format!(
                        "{}:{}->{}",
                        violation.axis, violation.source, violation.target
                    )
                })
                .collect(),
            abstraction_rules: sig0.policies.abstraction_allowed.clone(),
            protection_rules: Vec::new(),
        },
        semantic_diagrams: Vec::new(),
        architecture_paths: Vec::new(),
        homotopy_generators: Vec::new(),
        nonfillability_witnesses: Vec::new(),
        signature: AirSignature {
            axes: signature_axes.clone(),
        },
        coverage: AirCoverage {
            layers: air_coverage_layers(&signature_axes),
        },
        claims,
        operation_trace: AirOperationTrace {
            operations: Vec::new(),
        },
        extension: AirExtension {
            embedding_claim_ref: Some("claim-extension-embedding".to_string()),
            feature_view_claim_ref: Some("claim-extension-feature-view".to_string()),
            interaction_claim_refs,
            split_claim_ref: None,
            split_status: "unmeasured".to_string(),
        },
    }
}

pub fn build_pr_metadata_from_github_files(
    pull_request_path: &Path,
    files_path: &Path,
    reviews_path: Option<&Path>,
    review_threads_path: Option<&Path>,
) -> Result<EmpiricalDatasetInput, Box<dyn Error>> {
    let pull_request: Value = serde_json::from_str(&fs::read_to_string(pull_request_path)?)?;
    let files: Value = serde_json::from_str(&fs::read_to_string(files_path)?)?;
    let reviews = match reviews_path {
        Some(path) => Some(serde_json::from_str(&fs::read_to_string(path)?)?),
        None => None,
    };
    let review_threads = match review_threads_path {
        Some(path) => Some(serde_json::from_str(&fs::read_to_string(path)?)?),
        None => None,
    };

    build_pr_metadata_from_github_values(
        &pull_request,
        &files,
        reviews.as_ref(),
        review_threads.as_ref(),
    )
}

pub fn build_pr_metadata_from_github_values(
    pull_request: &Value,
    files: &Value,
    reviews: Option<&Value>,
    review_threads: Option<&Value>,
) -> Result<EmpiricalDatasetInput, Box<dyn Error>> {
    let file_items = json_items(
        files,
        &["data", "repository", "pullRequest", "files", "nodes"],
    );
    let changed_files =
        optional_usize(pull_request, &["changed_files"]).unwrap_or(file_items.len());
    let changed_lines_added = optional_usize(pull_request, &["additions"])
        .unwrap_or_else(|| sum_usize_field(&file_items, &["additions"]));
    let changed_lines_deleted = optional_usize(pull_request, &["deletions"])
        .unwrap_or_else(|| sum_usize_field(&file_items, &["deletions"]));

    let review_items = reviews
        .map(|reviews| {
            json_items(
                reviews,
                &["data", "repository", "pullRequest", "reviews", "nodes"],
            )
        })
        .unwrap_or_default();
    let thread_items = review_threads
        .map(|threads| {
            json_items(
                threads,
                &[
                    "data",
                    "repository",
                    "pullRequest",
                    "reviewThreads",
                    "nodes",
                ],
            )
        })
        .unwrap_or_default();

    let created_at = required_string(pull_request, &["created_at"])?;
    let merged_at = optional_string(pull_request, &["merged_at"]);

    Ok(EmpiricalDatasetInput {
        repository: RepositoryRef {
            owner: required_string(pull_request, &["base", "repo", "owner", "login"])?,
            name: required_string(pull_request, &["base", "repo", "name"])?,
            default_branch: required_string(pull_request, &["base", "repo", "default_branch"])?,
        },
        pull_request: PullRequestRef {
            number: required_usize(pull_request, &["number"])?,
            author: required_string(pull_request, &["user", "login"])?,
            created_at: created_at.clone(),
            merged_at: merged_at.clone(),
            base_commit: required_string(pull_request, &["base", "sha"])?,
            head_commit: required_string(pull_request, &["head", "sha"])?,
            merge_commit: optional_string(pull_request, &["merge_commit_sha"]),
            labels: pull_request_labels(pull_request),
            is_bot_generated: is_bot_generated_pull_request(pull_request),
        },
        pr_metrics: PullRequestMetrics {
            changed_files,
            changed_lines_added,
            changed_lines_deleted,
            changed_components: changed_components_from_github_files(&file_items),
            review_comment_count: optional_usize(pull_request, &["review_comments"]).unwrap_or(0),
            review_thread_count: thread_items.len(),
            review_round_count: review_items
                .iter()
                .filter(|review| review_timestamp(review).is_some())
                .count(),
            first_review_latency_hours: first_review_latency_hours(&created_at, &review_items),
            approval_latency_hours: approval_latency_hours(&created_at, &review_items),
            merge_latency_hours: merged_at
                .as_deref()
                .and_then(|merged_at| hours_between(&created_at, merged_at)),
        },
        issue_incident_links: Vec::new(),
        analysis_metadata: AnalysisMetadata::default(),
    })
}

pub fn extract_relation_complexity_observation_from_file(
    path: &Path,
) -> Result<RelationComplexityObservation, Box<dyn Error>> {
    let source = fs::read_to_string(path)?;
    let input: RelationComplexityCandidateFile = serde_json::from_str(&source)?;
    extract_relation_complexity_observation(input)
}

pub fn extract_relation_complexity_observation(
    mut input: RelationComplexityCandidateFile,
) -> Result<RelationComplexityObservation, Box<dyn Error>> {
    if input.schema_version != RELATION_COMPLEXITY_CANDIDATE_SCHEMA_VERSION {
        return Err(format!(
            "unsupported relation complexity candidate schemaVersion: {}",
            input.schema_version
        )
        .into());
    }

    input.measurement_universe.rule_set_version =
        Some(RELATION_COMPLEXITY_RULE_SET_VERSION.to_string());

    let mut excluded_evidence = input.excluded_evidence;
    let mut included_by_id: BTreeMap<String, RelationComplexityEvidence> = BTreeMap::new();
    let unsupported_frameworks =
        unsupported_relation_complexity_frameworks(&input.measurement_universe.frameworks);
    let framework_supported = input.measurement_universe.frameworks.is_empty()
        || input
            .measurement_universe
            .frameworks
            .iter()
            .any(|framework| relation_complexity_framework_supported(framework));
    let unsupported_reason = (!unsupported_frameworks.is_empty())
        .then(|| format!("unsupported-framework:{}", unsupported_frameworks.join(",")));

    let candidates = input
        .evidence
        .into_iter()
        .chain(input.evidence_candidates)
        .collect::<Vec<_>>();
    for mut candidate in candidates {
        validate_relation_complexity_candidate_shape(&candidate)?;

        if !framework_supported {
            excluded_evidence.push(excluded_relation_complexity_evidence(
                &candidate,
                unsupported_reason
                    .as_deref()
                    .expect("unsupported reason exists"),
            ));
            continue;
        }

        let ownership = candidate.ownership.as_str();
        if !matches!(ownership, "application-owned" | "application-configured") {
            excluded_evidence.push(excluded_relation_complexity_evidence(
                &candidate,
                &format!("ownership-not-counted:{ownership}"),
            ));
            continue;
        }

        if matches!(
            candidate.review_status.as_str(),
            "excluded" | "false-positive" | "rejected"
        ) {
            excluded_evidence.push(excluded_relation_complexity_evidence(
                &candidate,
                &format!("review-status-not-counted:{}", candidate.review_status),
            ));
            continue;
        }

        let mut unsupported_tags = Vec::new();
        candidate.tags = relation_complexity_tags(candidate.tags, &mut unsupported_tags);
        if !unsupported_tags.is_empty() {
            excluded_evidence.push(excluded_relation_complexity_evidence(
                &candidate,
                &format!("unsupported-tags:{}", unsupported_tags.join(",")),
            ));
        }
        if candidate.tags.is_empty() {
            excluded_evidence.push(excluded_relation_complexity_evidence(
                &candidate,
                "no-counted-relation-complexity-tags",
            ));
            continue;
        }

        included_by_id
            .entry(candidate.id.clone())
            .and_modify(|existing| {
                existing.tags = relation_complexity_tags(
                    existing
                        .tags
                        .iter()
                        .cloned()
                        .chain(candidate.tags.iter().cloned())
                        .collect(),
                    &mut Vec::new(),
                );
            })
            .or_insert(candidate);
    }

    let evidence: Vec<RelationComplexityEvidence> = included_by_id.into_values().collect();
    let counts = relation_complexity_counts(&evidence);
    let relation_complexity = counts.relation_complexity();

    Ok(RelationComplexityObservation {
        schema_version: RELATION_COMPLEXITY_OBSERVATION_SCHEMA_VERSION.to_string(),
        repository: input.repository,
        revision: input.revision,
        measurement_universe: input.measurement_universe,
        workflow: input.workflow,
        counts,
        relation_complexity,
        evidence,
        excluded_evidence,
    })
}

fn validate_relation_complexity_candidate_shape(
    candidate: &RelationComplexityEvidence,
) -> Result<(), String> {
    if candidate.id.is_empty() {
        return Err("relation complexity evidence id must not be empty".to_string());
    }
    if candidate.path.is_empty() {
        return Err(format!(
            "relation complexity evidence path must not be empty for {}",
            candidate.id
        ));
    }
    if candidate.ownership.is_empty() {
        return Err(format!(
            "relation complexity evidence ownership must not be empty for {}",
            candidate.id
        ));
    }
    if candidate.review_status.is_empty() {
        return Err(format!(
            "relation complexity evidence reviewStatus must not be empty for {}",
            candidate.id
        ));
    }
    Ok(())
}

fn relation_complexity_tags(tags: Vec<String>, unsupported_tags: &mut Vec<String>) -> Vec<String> {
    let mut supported = BTreeSet::new();
    let mut unsupported = BTreeSet::new();
    for tag in tags {
        if relation_complexity_tag_rank(&tag).is_some() {
            supported.insert(tag);
        } else {
            unsupported.insert(tag);
        }
    }
    unsupported_tags.extend(unsupported);

    let mut tags: Vec<String> = supported.into_iter().collect();
    tags.sort_by_key(|tag| relation_complexity_tag_rank(tag).expect("supported tag"));
    tags
}

fn relation_complexity_tag_rank(tag: &str) -> Option<usize> {
    match tag {
        "constraints" => Some(0),
        "compensations" => Some(1),
        "projections" => Some(2),
        "failureTransitions" => Some(3),
        "idempotencyRequirements" => Some(4),
        _ => None,
    }
}

fn relation_complexity_counts(
    evidence: &[RelationComplexityEvidence],
) -> RelationComplexityComponents {
    let mut counts = RelationComplexityComponents {
        constraints: 0,
        compensations: 0,
        projections: 0,
        failure_transitions: 0,
        idempotency_requirements: 0,
    };

    for item in evidence {
        let tags: BTreeSet<&str> = item.tags.iter().map(String::as_str).collect();
        for tag in tags {
            match tag {
                "constraints" => counts.constraints += 1,
                "compensations" => counts.compensations += 1,
                "projections" => counts.projections += 1,
                "failureTransitions" => counts.failure_transitions += 1,
                "idempotencyRequirements" => counts.idempotency_requirements += 1,
                _ => {}
            }
        }
    }

    counts
}

fn unsupported_relation_complexity_frameworks(frameworks: &[String]) -> Vec<String> {
    frameworks
        .iter()
        .filter(|framework| !relation_complexity_framework_supported(framework))
        .cloned()
        .collect()
}

fn relation_complexity_framework_supported(framework: &str) -> bool {
    matches!(
        framework,
        "generic-workflow" | "event-sourcing" | "saga" | "crud" | "lean-fixture"
    )
}

fn excluded_relation_complexity_evidence(
    evidence: &RelationComplexityEvidence,
    reason: &str,
) -> RelationComplexityExcludedEvidence {
    RelationComplexityExcludedEvidence {
        path: evidence.path.clone(),
        reason: reason.to_string(),
        symbol: evidence.symbol.clone(),
        line: evidence.line,
    }
}

fn json_field<'a>(value: &'a Value, path: &[&str]) -> Option<&'a Value> {
    path.iter()
        .try_fold(value, |current, key| current.get(*key))
}

fn required_string(value: &Value, path: &[&str]) -> Result<String, Box<dyn Error>> {
    optional_string(value, path)
        .ok_or_else(|| format!("missing or non-string GitHub field: {}", path.join(".")).into())
}

fn optional_string(value: &Value, path: &[&str]) -> Option<String> {
    match json_field(value, path)? {
        Value::String(text) => Some(text.clone()),
        Value::Null => None,
        _ => None,
    }
}

fn required_usize(value: &Value, path: &[&str]) -> Result<usize, Box<dyn Error>> {
    optional_usize(value, path)
        .ok_or_else(|| format!("missing or non-integer GitHub field: {}", path.join(".")).into())
}

fn optional_usize(value: &Value, path: &[&str]) -> Option<usize> {
    json_field(value, path)?
        .as_u64()
        .and_then(|value| usize::try_from(value).ok())
}

fn json_items<'a>(value: &'a Value, graph_ql_nodes_path: &[&str]) -> Vec<&'a Value> {
    if let Some(items) = value.as_array() {
        return items.iter().collect();
    }
    if let Some(items) = json_field(value, &["nodes"]).and_then(Value::as_array) {
        return items.iter().collect();
    }
    if let Some(items) = json_field(value, graph_ql_nodes_path).and_then(Value::as_array) {
        return items.iter().collect();
    }
    Vec::new()
}

fn sum_usize_field(items: &[&Value], path: &[&str]) -> usize {
    items
        .iter()
        .filter_map(|item| optional_usize(item, path))
        .sum()
}

fn pull_request_labels(pull_request: &Value) -> Vec<String> {
    let mut labels: Vec<String> = json_field(pull_request, &["labels"])
        .and_then(Value::as_array)
        .into_iter()
        .flatten()
        .filter_map(|label| optional_string(label, &["name"]))
        .collect();
    labels.sort();
    labels.dedup();
    labels
}

fn is_bot_generated_pull_request(pull_request: &Value) -> bool {
    let user = match json_field(pull_request, &["user"]) {
        Some(user) => user,
        None => return false,
    };
    let login = optional_string(user, &["login"]).unwrap_or_default();
    let user_type = optional_string(user, &["type"]).unwrap_or_default();
    user_type == "Bot" || login.ends_with("[bot]") || login.ends_with("-bot")
}

fn changed_components_from_github_files(files: &[&Value]) -> Vec<String> {
    let components: BTreeSet<String> = files
        .iter()
        .filter_map(|file| {
            optional_string(file, &["filename"])
                .or_else(|| optional_string(file, &["path"]))
                .or_else(|| optional_string(file, &["name"]))
        })
        .filter_map(|path| lean_module_id_from_path(&path))
        .collect();
    components.into_iter().collect()
}

fn lean_module_id_from_path(path: &str) -> Option<String> {
    let path = path.trim_start_matches("./");
    let module_path = path.strip_suffix(".lean")?;
    let module_id = module_path.replace(['/', '\\'], ".");
    (!module_id.is_empty()).then_some(module_id)
}

fn review_timestamp(review: &Value) -> Option<String> {
    optional_string(review, &["submitted_at"]).or_else(|| optional_string(review, &["submittedAt"]))
}

fn review_state(review: &Value) -> Option<String> {
    optional_string(review, &["state"]).map(|state| state.to_ascii_uppercase())
}

fn first_review_latency_hours(created_at: &str, reviews: &[&Value]) -> Option<f64> {
    reviews
        .iter()
        .filter_map(|review| review_timestamp(review))
        .filter_map(|submitted_at| seconds_between(created_at, &submitted_at))
        .min()
        .map(hours_from_seconds)
}

fn approval_latency_hours(created_at: &str, reviews: &[&Value]) -> Option<f64> {
    reviews
        .iter()
        .filter(|review| review_state(review).as_deref() == Some("APPROVED"))
        .filter_map(|review| review_timestamp(review))
        .filter_map(|submitted_at| seconds_between(created_at, &submitted_at))
        .min()
        .map(hours_from_seconds)
}

fn hours_between(start: &str, end: &str) -> Option<f64> {
    seconds_between(start, end).map(hours_from_seconds)
}

fn seconds_between(start: &str, end: &str) -> Option<i64> {
    let start = parse_github_timestamp(start)?;
    let end = parse_github_timestamp(end)?;
    (end >= start).then_some(end - start)
}

fn hours_from_seconds(seconds: i64) -> f64 {
    seconds as f64 / 3600.0
}

fn parse_github_timestamp(timestamp: &str) -> Option<i64> {
    let timestamp = timestamp.strip_suffix('Z')?;
    let (date, time) = timestamp.split_once('T')?;
    let mut date_parts = date.split('-');
    let year: i64 = date_parts.next()?.parse().ok()?;
    let month: i64 = date_parts.next()?.parse().ok()?;
    let day: i64 = date_parts.next()?.parse().ok()?;
    if date_parts.next().is_some() {
        return None;
    }

    let time = time.split_once('.').map_or(time, |(whole, _)| whole);
    let mut time_parts = time.split(':');
    let hour: i64 = time_parts.next()?.parse().ok()?;
    let minute: i64 = time_parts.next()?.parse().ok()?;
    let second: i64 = time_parts.next()?.parse().ok()?;
    if time_parts.next().is_some()
        || !(1..=12).contains(&month)
        || !(1..=31).contains(&day)
        || !(0..=23).contains(&hour)
        || !(0..=59).contains(&minute)
        || !(0..=60).contains(&second)
    {
        return None;
    }

    Some(days_from_civil(year, month, day) * 86_400 + hour * 3_600 + minute * 60 + second)
}

fn days_from_civil(year: i64, month: i64, day: i64) -> i64 {
    let year = year - i64::from(month <= 2);
    let era = if year >= 0 { year } else { year - 399 } / 400;
    let year_of_era = year - era * 400;
    let month_prime = month + if month > 2 { -3 } else { 9 };
    let day_of_year = (153 * month_prime + 2) / 5 + day - 1;
    let day_of_era = year_of_era * 365 + year_of_era / 4 - year_of_era / 100 + day_of_year;
    era * 146_097 + day_of_era - 719_468
}

fn signature_snapshot(document: &Sig0Document, commit: GitCommitRef) -> SignatureSnapshot {
    let signature = dataset_signature_shape(document);
    SignatureSnapshot {
        commit,
        extractor: ExtractorRef {
            name: EXTRACTOR_NAME.to_string(),
            version: EXTRACTOR_VERSION.to_string(),
            rule_set_version: RULE_SET_VERSION.to_string(),
            policy_version: document.policies.policy_id.clone(),
        },
        metric_status: dataset_metric_status(document),
        signature,
    }
}

fn dataset_signature_shape(document: &Sig0Document) -> ArchitectureSignatureV1DatasetShape {
    let graph = Graph::from_components_and_edges(&document.components, &document.edges);
    let runtime_propagation = document
        .runtime_dependency_graph
        .as_ref()
        .map(|projection| {
            Graph::from_components_and_edges(&document.components, &projection.edges)
                .reachable_cone_size()
        });

    ArchitectureSignatureV1DatasetShape {
        has_cycle: document.signature.has_cycle,
        scc_max_size: document.signature.scc_max_size,
        max_depth: document.signature.max_depth,
        fanout_risk: document.signature.fanout_risk,
        boundary_violation_count: document.signature.boundary_violation_count,
        abstraction_violation_count: document.signature.abstraction_violation_count,
        scc_excess_size: document.signature.scc_max_size.saturating_sub(1),
        max_fanout: graph.max_fanout(),
        reachable_cone_size: graph.reachable_cone_size(),
        weighted_scc_risk: None,
        projection_soundness_violation: None,
        lsp_violation_count: None,
        nilpotency_index: None,
        runtime_propagation,
        relation_complexity: None,
        empirical_change_cost: None,
    }
}

fn dataset_metric_status(document: &Sig0Document) -> BTreeMap<String, MetricStatus> {
    let mut status = BTreeMap::new();
    for axis in DATASET_SIGNATURE_AXES {
        let axis_status = match axis {
            "hasCycle"
            | "sccMaxSize"
            | "maxDepth"
            | "fanoutRisk"
            | "boundaryViolationCount"
            | "abstractionViolationCount" => document
                .metric_status
                .get(axis)
                .cloned()
                .unwrap_or_else(|| {
                    unmeasured_status(format!("legacy data without metricStatus entry for {axis}"))
                }),
            "sccExcessSize" => measured_status("archsig:derived-scc-excess"),
            "maxFanout" => measured_status("archsig:import-graph"),
            "reachableConeSize" => measured_status("archsig:import-graph"),
            "weightedSccRisk" => unmeasured_status("weight rule set not provided".to_string()),
            "projectionSoundnessViolation" => {
                unmeasured_status("projection rule set not provided".to_string())
            }
            "lspViolationCount" => {
                unmeasured_status("observation rule set not provided".to_string())
            }
            "nilpotencyIndex" => unmeasured_status("matrix bridge output not provided".to_string()),
            "runtimePropagation" => {
                document
                    .metric_status
                    .get(axis)
                    .cloned()
                    .unwrap_or_else(|| {
                        unmeasured_status("runtime dependency graph not provided".to_string())
                    })
            }
            "relationComplexity" => {
                unmeasured_status("relation complexity observation not provided".to_string())
            }
            "empiricalChangeCost" => {
                unmeasured_status("empirical target variable not provided".to_string())
            }
            _ => unreachable!("all dataset axes are covered"),
        };
        status.insert(axis.to_string(), axis_status);
    }
    status
}

fn air_signature_axes(
    signature: &ArchitectureSignatureV1DatasetShape,
    metric_status: &BTreeMap<String, MetricStatus>,
) -> Vec<AirSignatureAxis> {
    DATASET_SIGNATURE_AXES
        .iter()
        .map(|axis| {
            let value = signature_axis_value(signature, axis).map(|value| value as i64);
            let status = metric_status.get(*axis).cloned().unwrap_or_else(|| {
                unmeasured_status(format!("missing metricStatus entry for {axis}"))
            });
            AirSignatureAxis {
                axis: (*axis).to_string(),
                value,
                measured: status.measured,
                measurement_boundary: measurement_boundary(&status, value),
                source: status.source,
                reason: status.reason,
            }
        })
        .collect()
}

fn signature_axis_value(
    signature: &ArchitectureSignatureV1DatasetShape,
    axis: &str,
) -> Option<usize> {
    match axis {
        "hasCycle" => Some(signature.has_cycle),
        "sccMaxSize" => Some(signature.scc_max_size),
        "maxDepth" => Some(signature.max_depth),
        "fanoutRisk" => Some(signature.fanout_risk),
        "boundaryViolationCount" => Some(signature.boundary_violation_count),
        "abstractionViolationCount" => Some(signature.abstraction_violation_count),
        "sccExcessSize" => Some(signature.scc_excess_size),
        "maxFanout" => Some(signature.max_fanout),
        "reachableConeSize" => Some(signature.reachable_cone_size),
        "weightedSccRisk" => signature.weighted_scc_risk,
        "projectionSoundnessViolation" => signature.projection_soundness_violation,
        "lspViolationCount" => signature.lsp_violation_count,
        "nilpotencyIndex" => signature.nilpotency_index,
        "runtimePropagation" => signature.runtime_propagation,
        "relationComplexity" => signature.relation_complexity,
        "empiricalChangeCost" => signature.empirical_change_cost,
        _ => None,
    }
}

fn measurement_boundary(status: &MetricStatus, value: Option<i64>) -> String {
    if !status.measured {
        return "unmeasured".to_string();
    }
    match value {
        Some(0) => "measuredZero".to_string(),
        Some(_) => "measuredNonzero".to_string(),
        None => "unmeasured".to_string(),
    }
}

fn numbered_id(prefix: &str, index: usize) -> String {
    format!("{prefix}-{:04}", index + 1)
}

fn runtime_relation_kind(label: &str) -> String {
    match label {
        "http" | "grpc" | "queue" | "db" | "event" | "batch" => label.to_string(),
        label if label.contains("queue") => "queue".to_string(),
        label if label.contains("event") => "event".to_string(),
        label if label.contains("rpc") => "grpc".to_string(),
        label if label.contains("db") => "db".to_string(),
        _ => "call".to_string(),
    }
}

fn artifact_evidence_kind(kind: &str) -> String {
    match kind {
        "policy" => "policy_rule",
        "pr_metadata" => "pr_file",
        "diff" | "validation" | "sig0" => "observation_result",
        _ => "manual_annotation",
    }
    .to_string()
}

fn relation_lifecycle(edge: &Edge, diff: Option<&SignatureDiffReportV0>) -> String {
    let Some(diff) = diff else {
        return "after".to_string();
    };
    let Some(edge_delta) = &diff.evidence_diff.edge_delta else {
        return "after".to_string();
    };
    if edge_delta.added.iter().any(|added| added == edge) {
        "added".to_string()
    } else if edge_delta.removed.iter().any(|removed| removed == edge) {
        "removed".to_string()
    } else {
        "unchanged".to_string()
    }
}

fn air_component_lifecycle(diff: Option<&SignatureDiffReportV0>) -> BTreeMap<String, String> {
    let mut lifecycle = BTreeMap::new();
    if let Some(component_delta) =
        diff.and_then(|report| report.evidence_diff.component_delta.as_ref())
    {
        for component in &component_delta.added {
            lifecycle.insert(component.clone(), "added".to_string());
        }
        for component in &component_delta.removed {
            lifecycle.insert(component.clone(), "removed".to_string());
        }
    }
    lifecycle
}

fn air_revision(
    diff: Option<&SignatureDiffReportV0>,
    pr_metadata: Option<&EmpiricalDatasetInput>,
) -> AirRevision {
    if let Some(diff) = diff {
        return AirRevision {
            before: Some(diff.before.revision.sha.clone()),
            after: diff.after.revision.sha.clone(),
        };
    }
    if let Some(pr_metadata) = pr_metadata {
        return AirRevision {
            before: Some(pr_metadata.pull_request.base_commit.clone()),
            after: pr_metadata.pull_request.head_commit.clone(),
        };
    }
    AirRevision {
        before: None,
        after: "unknown".to_string(),
    }
}

fn air_feature(pr_metadata: Option<&EmpiricalDatasetInput>) -> AirFeature {
    if let Some(pr_metadata) = pr_metadata {
        AirFeature {
            feature_id: Some(format!("#{}", pr_metadata.pull_request.number)),
            title: None,
            description: Some(format!(
                "pull request by {} with {} changed files",
                pr_metadata.pull_request.author, pr_metadata.pr_metrics.changed_files
            )),
            source: "pr".to_string(),
            ai_session: None,
        }
    } else {
        AirFeature {
            feature_id: None,
            title: None,
            description: None,
            source: "unknown".to_string(),
            ai_session: None,
        }
    }
}

fn air_claims(signature_axes: &[AirSignatureAxis]) -> Vec<AirClaim> {
    let mut claims: Vec<AirClaim> = signature_axes
        .iter()
        .map(|axis| {
            let measured = axis.measured && axis.value.is_some();
            let mut missing_preconditions = Vec::new();
            let mut non_conclusions = vec![
                "tooling measurement is not a Lean proof".to_string(),
                "extractor output is not a complete ComponentUniverse proof".to_string(),
            ];
            if !measured {
                missing_preconditions.push(format!("{} is unmeasured", axis.axis));
                non_conclusions.push("placeholder zero is not measured zero".to_string());
            }
            AirClaim {
                claim_id: format!("claim-axis-{}", stable_id_fragment(&axis.axis)),
                subject_ref: format!("signature.{}", axis.axis),
                predicate: if measured {
                    "axis value measured by tooling".to_string()
                } else {
                    "axis is outside the current measurement boundary".to_string()
                },
                claim_level: "tooling".to_string(),
                claim_classification: if measured {
                    "measured".to_string()
                } else {
                    "unmeasured".to_string()
                },
                measurement_boundary: axis.measurement_boundary.clone(),
                theorem_refs: Vec::new(),
                evidence_refs: vec!["evidence-sig0-artifact".to_string()],
                required_assumptions: Vec::new(),
                coverage_assumptions: Vec::new(),
                exactness_assumptions: Vec::new(),
                missing_preconditions,
                non_conclusions,
            }
        })
        .collect();
    claims.push(AirClaim {
        claim_id: "claim-extension-embedding".to_string(),
        subject_ref: "extension.embedding".to_string(),
        predicate: "before architecture is embedded into after architecture only if diff evidence and theorem preconditions are discharged".to_string(),
        claim_level: "tooling".to_string(),
        claim_classification: "unmeasured".to_string(),
        measurement_boundary: "unmeasured".to_string(),
        theorem_refs: Vec::new(),
        evidence_refs: Vec::new(),
        required_assumptions: vec!["before/after component correspondence".to_string()],
        coverage_assumptions: vec!["static diff coverage".to_string()],
        exactness_assumptions: Vec::new(),
        missing_preconditions: vec!["theorem precondition checker has not run".to_string()],
        non_conclusions: vec!["split extension is not concluded".to_string()],
    });
    claims.push(AirClaim {
        claim_id: "claim-extension-feature-view".to_string(),
        subject_ref: "extension.feature".to_string(),
        predicate: "feature-owned delta can be interpreted from PR metadata and diff evidence"
            .to_string(),
        claim_level: "tooling".to_string(),
        claim_classification: "unmeasured".to_string(),
        measurement_boundary: "unmeasured".to_string(),
        theorem_refs: Vec::new(),
        evidence_refs: Vec::new(),
        required_assumptions: vec!["PR-to-component attribution".to_string()],
        coverage_assumptions: vec!["diff evidence coverage".to_string()],
        exactness_assumptions: Vec::new(),
        missing_preconditions: vec!["feature extension report has not run".to_string()],
        non_conclusions: vec!["feature quotient is not constructed".to_string()],
    });
    claims
}

fn air_interaction_claim_refs(claims: &[AirClaim]) -> Vec<String> {
    claims
        .iter()
        .filter(|claim| {
            claim.subject_ref == "signature.boundaryViolationCount"
                || claim.subject_ref == "signature.abstractionViolationCount"
                || claim.subject_ref == "signature.runtimePropagation"
        })
        .map(|claim| claim.claim_id.clone())
        .collect()
}

fn feature_report_preserved_invariants(document: &AirDocumentV0) -> Vec<FeatureReportInvariant> {
    document
        .signature
        .axes
        .iter()
        .filter(|axis| {
            axis.measured
                && axis.value == Some(0)
                && axis.measurement_boundary == "measuredZero"
                && static_report_axis(&axis.axis)
        })
        .map(|axis| FeatureReportInvariant {
            invariant: format!("{} preserved", axis.axis),
            axis: axis.axis.clone(),
            value: axis.value,
            measurement_boundary: axis.measurement_boundary.clone(),
            evidence_refs: feature_report_axis_evidence_refs(document, &axis.axis),
            claim_refs: feature_report_axis_claim_refs(document, &axis.axis),
        })
        .collect()
}

fn feature_report_changed_invariants(document: &AirDocumentV0) -> Vec<FeatureReportInvariant> {
    document
        .signature
        .axes
        .iter()
        .filter(|axis| {
            axis.measured && axis.value.unwrap_or_default() != 0 && static_report_axis(&axis.axis)
        })
        .map(|axis| FeatureReportInvariant {
            invariant: format!("{} changed", axis.axis),
            axis: axis.axis.clone(),
            value: axis.value,
            measurement_boundary: axis.measurement_boundary.clone(),
            evidence_refs: feature_report_axis_evidence_refs(document, &axis.axis),
            claim_refs: feature_report_axis_claim_refs(document, &axis.axis),
        })
        .collect()
}

fn feature_report_obstruction_witnesses(
    document: &AirDocumentV0,
    claim_by_id: &BTreeMap<String, &AirClaim>,
    evidence_by_id: &BTreeMap<String, &AirEvidence>,
) -> Vec<FeatureReportObstructionWitness> {
    let mut witnesses = Vec::new();
    for relation in &document.relations {
        if !feature_report_obstructing_relation(document, relation) {
            continue;
        }
        let claim = feature_report_relation_claim(document, relation);
        let kind = feature_report_relation_witness_kind(document, relation);
        witnesses.push(FeatureReportObstructionWitness {
            witness_id: format!("witness-{}", stable_id_fragment(&relation.id)),
            layer: relation.layer.clone(),
            kind: kind.clone(),
            extension_role: feature_report_witness_roles(&kind),
            extension_classification: feature_report_witness_classification(&kind),
            components: relation
                .from_component
                .iter()
                .chain(relation.to_component.iter())
                .cloned()
                .collect(),
            edges: vec![FeatureReportEdgeRef {
                relation_id: relation.id.clone(),
                from: relation.from_component.clone(),
                to: relation.to_component.clone(),
                kind: relation.kind.clone(),
            }],
            paths: Vec::new(),
            diagrams: Vec::new(),
            nonfillability_witness_ref: None,
            operation: Some("feature_addition".to_string()),
            evidence: feature_report_evidence_refs(&relation.evidence_refs, evidence_by_id),
            theorem_reference: claim
                .map(|claim| claim.theorem_refs.clone())
                .unwrap_or_default(),
            claim_level: claim
                .map(|claim| claim.claim_level.clone())
                .unwrap_or_else(|| "tooling".to_string()),
            claim_classification: claim
                .map(|claim| claim.claim_classification.clone())
                .unwrap_or_else(|| "measured".to_string()),
            measurement_boundary: claim
                .map(|claim| claim.measurement_boundary.clone())
                .unwrap_or_else(|| "measuredNonzero".to_string()),
            non_conclusions: feature_report_claim_non_conclusions(claim),
            repair_candidates: feature_report_witness_repairs(&kind),
        });
    }

    for witness in &document.nonfillability_witnesses {
        let claim = claim_by_id.get(&witness.claim_ref).copied();
        witnesses.push(FeatureReportObstructionWitness {
            witness_id: witness.witness_id.clone(),
            layer: "semantic".to_string(),
            kind: witness.witness_kind.clone(),
            extension_role: vec!["invariant_not_preserved".to_string()],
            extension_classification: vec!["fillingFailure".to_string()],
            components: Vec::new(),
            edges: Vec::new(),
            paths: Vec::new(),
            diagrams: vec![witness.diagram_ref.clone()],
            nonfillability_witness_ref: Some(witness.witness_id.clone()),
            operation: Some("feature_addition".to_string()),
            evidence: feature_report_evidence_refs(&witness.evidence_refs, evidence_by_id),
            theorem_reference: claim
                .map(|claim| claim.theorem_refs.clone())
                .unwrap_or_default(),
            claim_level: claim
                .map(|claim| claim.claim_level.clone())
                .unwrap_or_else(|| "tooling".to_string()),
            claim_classification: claim
                .map(|claim| claim.claim_classification.clone())
                .unwrap_or_else(|| "measured".to_string()),
            measurement_boundary: claim
                .map(|claim| claim.measurement_boundary.clone())
                .unwrap_or_else(|| "measuredNonzero".to_string()),
            non_conclusions: feature_report_claim_non_conclusions(claim),
            repair_candidates: vec![
                "add or repair semantic diagram evidence".to_string(),
                "choose an explicit contract for the non-commuting paths".to_string(),
            ],
        });
    }

    witnesses
}

fn feature_report_coverage_gaps(document: &AirDocumentV0) -> Vec<FeatureReportCoverageGap> {
    document
        .coverage
        .layers
        .iter()
        .filter(|layer| {
            layer.measurement_boundary == "unmeasured"
                || !layer.unmeasured_axes.is_empty()
                || !layer.unsupported_constructs.is_empty()
        })
        .map(|layer| FeatureReportCoverageGap {
            layer: layer.layer.clone(),
            measurement_boundary: if layer.measurement_boundary == "unmeasured" {
                "UNMEASURED".to_string()
            } else {
                layer.measurement_boundary.clone()
            },
            unmeasured_axes: layer.unmeasured_axes.clone(),
            unsupported_constructs: layer.unsupported_constructs.clone(),
            non_conclusions: vec![format!("{} layer is not concluded", layer.layer)],
        })
        .collect()
}

fn feature_report_split_status(
    document: &AirDocumentV0,
    preserved_invariants: &[FeatureReportInvariant],
    changed_invariants: &[FeatureReportInvariant],
    introduced_obstruction_witnesses: &[FeatureReportObstructionWitness],
) -> String {
    if !introduced_obstruction_witnesses.is_empty() || !changed_invariants.is_empty() {
        return "non_split".to_string();
    }
    if !preserved_invariants.is_empty() || feature_report_has_static_measurement(document) {
        return "split".to_string();
    }
    if document
        .coverage
        .layers
        .iter()
        .any(|layer| matches!(layer.layer.as_str(), "static" | "policy"))
    {
        "unknown".to_string()
    } else {
        "unmeasured".to_string()
    }
}

fn feature_report_theorem_package_refs(document: &AirDocumentV0) -> Vec<String> {
    let mut refs = BTreeSet::new();
    for claim in &document.claims {
        for theorem_ref in &claim.theorem_refs {
            refs.insert(theorem_ref.clone());
        }
    }
    refs.into_iter().collect()
}

fn feature_report_discharged_assumptions(document: &AirDocumentV0) -> Vec<String> {
    let mut assumptions = BTreeSet::new();
    for claim in &document.claims {
        if claim.missing_preconditions.is_empty()
            && matches!(
                claim.claim_classification.as_str(),
                "measured" | "proved" | "assumed"
            )
        {
            for assumption in claim
                .required_assumptions
                .iter()
                .chain(claim.coverage_assumptions.iter())
                .chain(claim.exactness_assumptions.iter())
            {
                assumptions.insert(assumption.clone());
            }
        }
    }
    assumptions.into_iter().collect()
}

fn feature_report_undischarged_assumptions(document: &AirDocumentV0) -> Vec<String> {
    let mut assumptions = BTreeSet::new();
    for claim in &document.claims {
        for assumption in claim
            .missing_preconditions
            .iter()
            .chain(claim.required_assumptions.iter())
            .chain(claim.coverage_assumptions.iter())
            .chain(claim.exactness_assumptions.iter())
        {
            if !claim.missing_preconditions.is_empty() || claim.claim_classification == "unmeasured"
            {
                assumptions.insert(assumption.clone());
            }
        }
    }
    assumptions.into_iter().collect()
}

fn feature_report_unsupported_constructs(
    coverage_gaps: &[FeatureReportCoverageGap],
) -> Vec<String> {
    let mut unsupported = BTreeSet::new();
    for gap in coverage_gaps {
        for construct in &gap.unsupported_constructs {
            unsupported.insert(format!("{}: {}", gap.layer, construct));
        }
    }
    unsupported.into_iter().collect()
}

fn feature_report_repair_suggestions(
    witnesses: &[FeatureReportObstructionWitness],
    coverage_gaps: &[FeatureReportCoverageGap],
) -> Vec<String> {
    let mut suggestions = BTreeSet::new();
    for witness in witnesses {
        for repair in &witness.repair_candidates {
            suggestions.insert(repair.clone());
        }
    }
    for gap in coverage_gaps {
        if gap.measurement_boundary == "UNMEASURED" {
            suggestions.insert(format!(
                "add {} layer evidence before drawing global conclusions",
                gap.layer
            ));
        }
    }
    suggestions.into_iter().collect()
}

fn feature_report_non_conclusions(
    document: &AirDocumentV0,
    split_status: &str,
    coverage_gaps: &[FeatureReportCoverageGap],
) -> Vec<String> {
    let mut non_conclusions = BTreeSet::new();
    non_conclusions.insert("tooling report is not a Lean proof".to_string());
    non_conclusions.insert("absence of unmeasured witnesses is not concluded".to_string());
    if split_status == "split" {
        non_conclusions.insert("static split does not conclude runtime flatness".to_string());
        non_conclusions.insert("static split does not conclude semantic flatness".to_string());
    }
    for gap in coverage_gaps {
        non_conclusions.insert(format!(
            "{} layer is {}",
            gap.layer, gap.measurement_boundary
        ));
        for conclusion in &gap.non_conclusions {
            non_conclusions.insert(conclusion.clone());
        }
    }
    for claim in &document.claims {
        for conclusion in &claim.non_conclusions {
            non_conclusions.insert(conclusion.clone());
        }
    }
    non_conclusions.into_iter().collect()
}

fn feature_report_required_action(
    split_status: &str,
    witnesses: &[FeatureReportObstructionWitness],
    coverage_gaps: &[FeatureReportCoverageGap],
) -> String {
    match split_status {
        "non_split" if !witnesses.is_empty() => {
            "review introduced obstruction witnesses before treating the feature as split"
                .to_string()
        }
        "split" if !coverage_gaps.is_empty() => {
            "review static split together with UNMEASURED coverage gaps".to_string()
        }
        "split" => "review preserved static invariants".to_string(),
        "unmeasured" => {
            "add static or policy evidence before classifying the extension".to_string()
        }
        _ => {
            "review coverage and theorem preconditions before classifying the extension".to_string()
        }
    }
}

fn feature_report_claim_classification(split_status: &str) -> String {
    match split_status {
        "split" | "non_split" => "MEASURED".to_string(),
        "unmeasured" => "UNMEASURED".to_string(),
        _ => "UNKNOWN".to_string(),
    }
}

fn theorem_precondition_checks(
    document: &AirDocumentV0,
    registry: &TheoremPackageRegistryV0,
) -> Vec<TheoremPreconditionCheck> {
    document
        .claims
        .iter()
        .map(|claim| theorem_precondition_check(claim, registry))
        .collect()
}

fn theorem_precondition_check(
    claim: &AirClaim,
    registry: &TheoremPackageRegistryV0,
) -> TheoremPreconditionCheck {
    let applicable_packages: Vec<&TheoremPackageMetadataV0> = registry
        .packages
        .iter()
        .filter(|package| theorem_package_applies_to_claim(package, claim))
        .collect();
    let known_refs: BTreeSet<String> = registry
        .packages
        .iter()
        .flat_map(|package| package.theorem_refs.iter().cloned())
        .collect();
    let unknown_theorem_refs: Vec<String> = claim
        .theorem_refs
        .iter()
        .filter(|theorem_ref| !known_refs.contains(theorem_ref.as_str()))
        .cloned()
        .collect();
    let applicable_package_refs = applicable_packages
        .iter()
        .map(|package| package.package_id.clone())
        .collect();

    let (resolved_claim_classification, result, reason) = if !unknown_theorem_refs.is_empty() {
        (
            "UNKNOWN_THEOREM_REF".to_string(),
            "warn".to_string(),
            "claim cites theorem refs outside the static theorem package registry".to_string(),
        )
    } else if claim.claim_classification == "measured" {
        (
            "MEASURED_WITNESS".to_string(),
            "pass".to_string(),
            "tooling measurement remains a measured witness, not a formal proved claim".to_string(),
        )
    } else if claim.claim_level == "formal"
        && claim.claim_classification == "proved"
        && !claim.missing_preconditions.is_empty()
    {
        (
            "BLOCKED_FORMAL_CLAIM".to_string(),
            "warn".to_string(),
            "missing preconditions block formal proved classification".to_string(),
        )
    } else if claim.claim_level == "formal"
        && claim.claim_classification == "proved"
        && !claim.theorem_refs.is_empty()
        && !applicable_packages.is_empty()
    {
        (
            "FORMAL_PROVED".to_string(),
            "pass".to_string(),
            "theorem refs are registered and missing preconditions are empty".to_string(),
        )
    } else if claim.claim_level == "formal" && claim.claim_classification == "proved" {
        (
            "BLOCKED_FORMAL_CLAIM".to_string(),
            "warn".to_string(),
            "formal proved claim needs registered theorem refs".to_string(),
        )
    } else if claim.claim_classification == "unmeasured" || !claim.missing_preconditions.is_empty()
    {
        (
            "UNMEASURED".to_string(),
            "warn".to_string(),
            "claim remains outside the measured theorem boundary".to_string(),
        )
    } else if applicable_packages.is_empty() && !claim.theorem_refs.is_empty() {
        (
            "UNKNOWN_THEOREM_REF".to_string(),
            "warn".to_string(),
            "claim has theorem refs but no applicable static theorem package".to_string(),
        )
    } else {
        (
            "TOOLING_CLAIM".to_string(),
            "pass".to_string(),
            "claim is reported at tooling level".to_string(),
        )
    };

    TheoremPreconditionCheck {
        claim_id: claim.claim_id.clone(),
        subject_ref: claim.subject_ref.clone(),
        applicable_package_refs,
        theorem_refs: claim.theorem_refs.clone(),
        unknown_theorem_refs,
        claim_level: claim.claim_level.clone(),
        input_claim_classification: claim.claim_classification.clone(),
        resolved_claim_classification,
        measurement_boundary: claim.measurement_boundary.clone(),
        required_assumptions: claim.required_assumptions.clone(),
        coverage_assumptions: claim.coverage_assumptions.clone(),
        exactness_assumptions: claim.exactness_assumptions.clone(),
        missing_preconditions: claim.missing_preconditions.clone(),
        non_conclusions: claim.non_conclusions.clone(),
        result,
        reason,
    }
}

fn theorem_precondition_check_summary(
    checks: &[TheoremPreconditionCheck],
    checked_claim_count: usize,
) -> TheoremPreconditionCheckSummary {
    let blocked_claim_count = checks
        .iter()
        .filter(|check| check.resolved_claim_classification == "BLOCKED_FORMAL_CLAIM")
        .count();
    let unknown_theorem_ref_count = checks
        .iter()
        .map(|check| check.unknown_theorem_refs.len())
        .sum();
    let result = if checks.iter().any(|check| check.result == "warn") {
        "warn"
    } else {
        "pass"
    };

    TheoremPreconditionCheckSummary {
        result: result.to_string(),
        checked_claim_count,
        applicable_claim_count: checks
            .iter()
            .filter(|check| !check.applicable_package_refs.is_empty())
            .count(),
        formal_proved_claim_count: checks
            .iter()
            .filter(|check| check.resolved_claim_classification == "FORMAL_PROVED")
            .count(),
        measured_witness_count: checks
            .iter()
            .filter(|check| check.resolved_claim_classification == "MEASURED_WITNESS")
            .count(),
        blocked_claim_count,
        unmeasured_claim_count: checks
            .iter()
            .filter(|check| check.resolved_claim_classification == "UNMEASURED")
            .count(),
        unknown_theorem_ref_count,
    }
}

fn theorem_package_applies_to_claim(package: &TheoremPackageMetadataV0, claim: &AirClaim) -> bool {
    let theorem_ref_matches = claim
        .theorem_refs
        .iter()
        .any(|theorem_ref| package.theorem_refs.contains(theorem_ref));
    let subject_matches = package
        .supported_subject_refs
        .iter()
        .any(|subject_ref| subject_ref == &claim.subject_ref);

    theorem_ref_matches || subject_matches
}

fn feature_report_obstructing_relation(document: &AirDocumentV0, relation: &AirRelation) -> bool {
    let extraction_rule = relation.extraction_rule.as_deref().unwrap_or_default();
    relation.layer == "policy"
        || extraction_rule.contains("hidden")
        || relation.kind.contains("hidden")
        || document.policies.forbidden_edges.iter().any(|edge| {
            relation
                .from_component
                .as_ref()
                .zip(relation.to_component.as_ref())
                .map(|(from, to)| edge.contains(from) && edge.contains(to))
                .unwrap_or(false)
        })
}

fn feature_report_relation_witness_kind(
    document: &AirDocumentV0,
    relation: &AirRelation,
) -> String {
    let extraction_rule = relation.extraction_rule.as_deref().unwrap_or_default();
    if extraction_rule.contains("hidden")
        || relation.kind.contains("hidden")
        || document
            .policies
            .forbidden_edges
            .iter()
            .any(|edge| edge.contains("hiddenInteraction"))
    {
        "hidden_interaction".to_string()
    } else if relation.layer == "policy" {
        "policy_violation".to_string()
    } else {
        "invariant_not_preserved".to_string()
    }
}

fn feature_report_witness_roles(kind: &str) -> Vec<String> {
    match kind {
        "hidden_interaction" => vec![
            "hidden_interaction".to_string(),
            "invariant_not_preserved".to_string(),
        ],
        "policy_violation" => vec![
            "embedding_broken".to_string(),
            "invariant_not_preserved".to_string(),
        ],
        _ => vec!["invariant_not_preserved".to_string()],
    }
}

fn feature_report_witness_classification(kind: &str) -> Vec<String> {
    match kind {
        "hidden_interaction" => vec!["interaction".to_string()],
        "policy_violation" => vec!["liftingFailure".to_string()],
        _ => vec!["residualCoverageGap".to_string()],
    }
}

fn feature_report_witness_repairs(kind: &str) -> Vec<String> {
    match kind {
        "hidden_interaction" => vec![
            "route the dependency through a declared interface".to_string(),
            "move direct internal-state access behind a feature port".to_string(),
        ],
        "policy_violation" => vec![
            "move the dependency behind an allowed boundary".to_string(),
            "update policy only if the architecture law intentionally changed".to_string(),
        ],
        _ => vec!["add evidence or refactor the obstructing relation".to_string()],
    }
}

fn feature_report_relation_claim<'a>(
    document: &'a AirDocumentV0,
    relation: &AirRelation,
) -> Option<&'a AirClaim> {
    document
        .claims
        .iter()
        .find(|claim| claim.subject_ref == relation.id)
        .or_else(|| {
            document.claims.iter().find(|claim| {
                !claim.evidence_refs.is_empty()
                    && claim
                        .evidence_refs
                        .iter()
                        .any(|evidence_ref| relation.evidence_refs.contains(evidence_ref))
            })
        })
}

fn feature_report_claim_non_conclusions(claim: Option<&AirClaim>) -> Vec<String> {
    let mut non_conclusions = claim
        .map(|claim| claim.non_conclusions.clone())
        .unwrap_or_default();
    non_conclusions.push("witness is not a formal theorem claim".to_string());
    non_conclusions
}

fn feature_report_evidence_refs(
    refs: &[String],
    evidence_by_id: &BTreeMap<String, &AirEvidence>,
) -> Vec<FeatureReportEvidenceRef> {
    refs.iter()
        .map(|evidence_ref| {
            let evidence = evidence_by_id.get(evidence_ref).copied();
            FeatureReportEvidenceRef {
                evidence_ref: evidence_ref.clone(),
                kind: evidence.map(|evidence| evidence.kind.clone()),
                artifact_ref: evidence.and_then(|evidence| evidence.artifact_ref.clone()),
                path: evidence.and_then(|evidence| evidence.path.clone()),
                symbol: evidence.and_then(|evidence| evidence.symbol.clone()),
                rule_id: evidence.and_then(|evidence| evidence.rule_id.clone()),
            }
        })
        .collect()
}

fn feature_report_axis_evidence_refs(document: &AirDocumentV0, axis: &str) -> Vec<String> {
    let mut refs = BTreeSet::new();
    for claim in &document.claims {
        if claim.subject_ref == format!("signature.{axis}") {
            for evidence_ref in &claim.evidence_refs {
                refs.insert(evidence_ref.clone());
            }
        }
    }
    refs.into_iter().collect()
}

fn feature_report_axis_claim_refs(document: &AirDocumentV0, axis: &str) -> Vec<String> {
    document
        .claims
        .iter()
        .filter(|claim| claim.subject_ref == format!("signature.{axis}"))
        .map(|claim| claim.claim_id.clone())
        .collect()
}

fn feature_report_has_static_measurement(document: &AirDocumentV0) -> bool {
    document.coverage.layers.iter().any(|layer| {
        matches!(layer.layer.as_str(), "static" | "policy")
            && layer.measurement_boundary != "unmeasured"
    }) || document
        .signature
        .axes
        .iter()
        .any(|axis| axis.measured && static_report_axis(&axis.axis))
}

fn static_report_axis(axis: &str) -> bool {
    matches!(
        axis,
        "boundaryViolationCount"
            | "abstractionViolationCount"
            | "projectionSoundnessViolation"
            | "lspViolationCount"
            | "hasCycle"
            | "sccMaxSize"
            | "maxDepth"
            | "fanoutRisk"
            | "sccExcessSize"
            | "maxFanout"
            | "reachableConeSize"
            | "weightedSccRisk"
    )
}

fn count_air_relations(document: &AirDocumentV0, layer: &str) -> usize {
    document
        .relations
        .iter()
        .filter(|relation| relation.layer == layer)
        .count()
}

fn stable_id_fragment(value: &str) -> String {
    value
        .chars()
        .map(|character| {
            if character.is_ascii_alphanumeric() {
                character.to_ascii_lowercase()
            } else {
                '-'
            }
        })
        .collect()
}

fn air_coverage_layers(signature_axes: &[AirSignatureAxis]) -> Vec<AirCoverageLayer> {
    vec![
        air_coverage_layer(
            "static",
            signature_axes,
            &[
                "hasCycle",
                "sccMaxSize",
                "maxDepth",
                "fanoutRisk",
                "sccExcessSize",
                "maxFanout",
                "reachableConeSize",
            ],
            vec!["Lean import graph".to_string()],
            Vec::new(),
        ),
        air_coverage_layer(
            "policy",
            signature_axes,
            &["boundaryViolationCount", "abstractionViolationCount"],
            vec!["policy file".to_string()],
            vec!["policy coverage depends on selector completeness".to_string()],
        ),
        air_coverage_layer(
            "runtime",
            signature_axes,
            &["runtimePropagation"],
            vec!["runtime edge evidence JSON".to_string()],
            vec![
                "runtime projection is a tooling observation, not telemetry completeness"
                    .to_string(),
            ],
        ),
        air_unmeasured_coverage_layer(
            "semantic",
            vec![
                "lspViolationCount".to_string(),
                "projectionSoundnessViolation".to_string(),
            ],
        ),
        air_unmeasured_coverage_layer(
            "operation",
            vec![
                "relationComplexity".to_string(),
                "empiricalChangeCost".to_string(),
            ],
        ),
    ]
}

fn air_coverage_layer(
    layer: &str,
    signature_axes: &[AirSignatureAxis],
    axes: &[&str],
    extraction_scope: Vec<String>,
    exactness_assumptions: Vec<String>,
) -> AirCoverageLayer {
    let mut measured_axes = Vec::new();
    let mut unmeasured_axes = Vec::new();
    let mut boundaries = Vec::new();
    for axis in axes {
        if let Some(signature_axis) = signature_axes
            .iter()
            .find(|signature_axis| signature_axis.axis == *axis)
        {
            boundaries.push(signature_axis.measurement_boundary.clone());
            if signature_axis.measured {
                measured_axes.push((*axis).to_string());
            } else {
                unmeasured_axes.push((*axis).to_string());
            }
        }
    }
    AirCoverageLayer {
        layer: layer.to_string(),
        measurement_boundary: combined_measurement_boundary(&boundaries),
        universe_refs: vec!["artifact-sig0".to_string()],
        measured_axes,
        unmeasured_axes,
        extraction_scope,
        exactness_assumptions,
        unsupported_constructs: Vec::new(),
    }
}

fn air_unmeasured_coverage_layer(layer: &str, unmeasured_axes: Vec<String>) -> AirCoverageLayer {
    AirCoverageLayer {
        layer: layer.to_string(),
        measurement_boundary: "unmeasured".to_string(),
        universe_refs: Vec::new(),
        measured_axes: Vec::new(),
        unmeasured_axes,
        extraction_scope: Vec::new(),
        exactness_assumptions: Vec::new(),
        unsupported_constructs: vec!["extractor not implemented for this layer".to_string()],
    }
}

fn combined_measurement_boundary(boundaries: &[String]) -> String {
    if boundaries.is_empty() || boundaries.iter().any(|boundary| boundary == "unmeasured") {
        "unmeasured".to_string()
    } else if boundaries
        .iter()
        .any(|boundary| boundary == "measuredNonzero")
    {
        "measuredNonzero".to_string()
    } else {
        "measuredZero".to_string()
    }
}

fn delta_signature_signed(
    before: &SignatureSnapshot,
    after: &SignatureSnapshot,
) -> NullableSignatureIntVector {
    NullableSignatureIntVector {
        has_cycle: signed_delta("hasCycle", before, after),
        scc_max_size: signed_delta("sccMaxSize", before, after),
        max_depth: signed_delta("maxDepth", before, after),
        fanout_risk: signed_delta("fanoutRisk", before, after),
        boundary_violation_count: signed_delta("boundaryViolationCount", before, after),
        abstraction_violation_count: signed_delta("abstractionViolationCount", before, after),
        scc_excess_size: signed_delta("sccExcessSize", before, after),
        max_fanout: signed_delta("maxFanout", before, after),
        reachable_cone_size: signed_delta("reachableConeSize", before, after),
        weighted_scc_risk: signed_delta("weightedSccRisk", before, after),
        projection_soundness_violation: signed_delta("projectionSoundnessViolation", before, after),
        lsp_violation_count: signed_delta("lspViolationCount", before, after),
        nilpotency_index: signed_delta("nilpotencyIndex", before, after),
        runtime_propagation: signed_delta("runtimePropagation", before, after),
        relation_complexity: signed_delta("relationComplexity", before, after),
    }
}

fn metric_delta_status(
    before: &SignatureSnapshot,
    after: &SignatureSnapshot,
) -> BTreeMap<String, MetricDeltaStatus> {
    DATASET_DELTA_AXES
        .iter()
        .map(|axis| ((*axis).to_string(), delta_status(axis, before, after)))
        .collect()
}

fn signed_delta(axis: &str, before: &SignatureSnapshot, after: &SignatureSnapshot) -> Option<i64> {
    let before_measured = is_measured(axis, &before.metric_status);
    let after_measured = is_measured(axis, &after.metric_status);
    if !before_measured || !after_measured {
        return None;
    }

    Some(signature_value(axis, &after.signature)? - signature_value(axis, &before.signature)?)
}

fn delta_status(
    axis: &str,
    before: &SignatureSnapshot,
    after: &SignatureSnapshot,
) -> MetricDeltaStatus {
    let before_measured = is_measured(axis, &before.metric_status);
    let after_measured = is_measured(axis, &after.metric_status);
    let before_value = signature_value(axis, &before.signature);
    let after_value = signature_value(axis, &after.signature);
    let comparable =
        before_measured && after_measured && before_value.is_some() && after_value.is_some();
    let reason = if comparable {
        "measured before and after".to_string()
    } else {
        delta_unavailable_reason(
            axis,
            before_measured,
            after_measured,
            before_value.is_some(),
            after_value.is_some(),
            &before.metric_status,
            &after.metric_status,
        )
    };

    MetricDeltaStatus {
        comparable,
        reason,
        before_measured,
        after_measured,
    }
}

fn is_measured(axis: &str, metric_status: &BTreeMap<String, MetricStatus>) -> bool {
    metric_status
        .get(axis)
        .is_some_and(|status| status.measured)
}

fn signature_value(axis: &str, signature: &ArchitectureSignatureV1DatasetShape) -> Option<i64> {
    let value = match axis {
        "hasCycle" => Some(signature.has_cycle),
        "sccMaxSize" => Some(signature.scc_max_size),
        "maxDepth" => Some(signature.max_depth),
        "fanoutRisk" => Some(signature.fanout_risk),
        "boundaryViolationCount" => Some(signature.boundary_violation_count),
        "abstractionViolationCount" => Some(signature.abstraction_violation_count),
        "sccExcessSize" => Some(signature.scc_excess_size),
        "maxFanout" => Some(signature.max_fanout),
        "reachableConeSize" => Some(signature.reachable_cone_size),
        "weightedSccRisk" => signature.weighted_scc_risk,
        "projectionSoundnessViolation" => signature.projection_soundness_violation,
        "lspViolationCount" => signature.lsp_violation_count,
        "nilpotencyIndex" => signature.nilpotency_index,
        "runtimePropagation" => signature.runtime_propagation,
        "relationComplexity" => signature.relation_complexity,
        _ => None,
    };
    value.map(|value| value as i64)
}

fn delta_unavailable_reason(
    axis: &str,
    before_measured: bool,
    after_measured: bool,
    before_value_present: bool,
    after_value_present: bool,
    before_status: &BTreeMap<String, MetricStatus>,
    after_status: &BTreeMap<String, MetricStatus>,
) -> String {
    let mut reasons = Vec::new();
    if !before_measured {
        reasons.push(format!(
            "before: {}",
            metric_status_reason(axis, before_status)
        ));
    }
    if !after_measured {
        reasons.push(format!(
            "after: {}",
            metric_status_reason(axis, after_status)
        ));
    }
    if before_measured && !before_value_present {
        reasons.push("before signature value is null".to_string());
    }
    if after_measured && !after_value_present {
        reasons.push("after signature value is null".to_string());
    }
    reasons.join("; ")
}

fn metric_status_reason(axis: &str, metric_status: &BTreeMap<String, MetricStatus>) -> String {
    metric_status
        .get(axis)
        .and_then(|status| status.reason.clone())
        .unwrap_or_else(|| "metricStatus entry is missing".to_string())
}

fn snapshot_validation_summary(
    report: Option<&ComponentUniverseValidationReport>,
    report_path: Option<String>,
) -> SnapshotValidationSummary {
    match report {
        Some(report) => SnapshotValidationSummary {
            schema_version: Some(report.schema_version.clone()),
            result: report.summary.result.clone(),
            universe_mode: Some(report.universe_mode.clone()),
            failed_check_count: Some(report.summary.failed_check_count),
            warning_check_count: Some(report.summary.warning_check_count),
            not_measured_check_count: Some(report.summary.not_measured_check_count),
            report_path,
        },
        None => SnapshotValidationSummary {
            schema_version: None,
            result: "not_run".to_string(),
            universe_mode: None,
            failed_check_count: None,
            warning_check_count: None,
            not_measured_check_count: None,
            report_path: None,
        },
    }
}

fn store_record_signature_snapshot(
    record: &SignatureSnapshotStoreRecordV0,
    role: &str,
) -> SignatureSnapshot {
    SignatureSnapshot {
        commit: GitCommitRef {
            sha: record.revision.sha.clone(),
            role: role.to_string(),
        },
        extractor: ExtractorRef {
            name: record.extractor.name.clone(),
            version: record.extractor.version.clone(),
            rule_set_version: record.extractor.rule_set_version.clone(),
            policy_version: record.policy.policy_id.clone(),
        },
        signature: record.signature.clone(),
        metric_status: record.metric_status.clone(),
    }
}

fn snapshot_diff_endpoint(record: &SignatureSnapshotStoreRecordV0) -> SnapshotDiffEndpoint {
    SnapshotDiffEndpoint {
        repository: record.repository.clone(),
        revision: record.revision.clone(),
        validation_result: record.validation_summary.result.clone(),
        extractor_version: record.extractor.version.clone(),
        rule_set_version: record.extractor.rule_set_version.clone(),
        policy_id: record.policy.policy_id.clone(),
    }
}

fn snapshot_comparison_status(
    before: &SignatureSnapshotStoreRecordV0,
    after: &SignatureSnapshotStoreRecordV0,
) -> SnapshotComparisonStatus {
    let mut reasons = Vec::new();
    if !matches!(before.validation_summary.result.as_str(), "pass" | "warn") {
        reasons.push(format!(
            "before validationSummary.result = {}",
            before.validation_summary.result
        ));
    }
    if !matches!(after.validation_summary.result.as_str(), "pass" | "warn") {
        reasons.push(format!(
            "after validationSummary.result = {}",
            after.validation_summary.result
        ));
    }
    if before.extractor.name != after.extractor.name {
        reasons.push("extractor.name differs".to_string());
    }
    if before.extractor.version != after.extractor.version {
        reasons.push("extractor.version differs".to_string());
    }
    if before.extractor.rule_set_version != after.extractor.rule_set_version {
        reasons.push("extractor.ruleSetVersion differs".to_string());
    }
    if before.policy.policy_id != after.policy.policy_id {
        reasons.push("policy.policyId differs".to_string());
    }
    if before.policy.version != after.policy.version {
        reasons.push("policy.version differs".to_string());
    }

    SnapshotComparisonStatus {
        primary_diff_eligible: reasons.is_empty(),
        reasons,
    }
}

fn classify_axis_deltas(
    before: &SignatureSnapshotStoreRecordV0,
    after: &SignatureSnapshotStoreRecordV0,
    status: &BTreeMap<String, MetricDeltaStatus>,
) -> (
    Vec<SignatureAxisChange>,
    Vec<SignatureAxisChange>,
    Vec<SignatureAxisChange>,
    Vec<UnmeasuredAxisDelta>,
) {
    let mut worsened = Vec::new();
    let mut improved = Vec::new();
    let mut unchanged = Vec::new();
    let mut unmeasured = Vec::new();

    for axis in DATASET_DELTA_AXES {
        let axis_status = status
            .get(axis)
            .expect("metric delta status exists for every dataset delta axis");
        let before_value = signature_value(axis, &before.signature);
        let after_value = signature_value(axis, &after.signature);
        if !axis_status.comparable {
            unmeasured.push(UnmeasuredAxisDelta {
                axis: axis.to_string(),
                reason: axis_status.reason.clone(),
                before_measured: axis_status.before_measured,
                after_measured: axis_status.after_measured,
            });
            continue;
        }

        let before_value = before_value.expect("comparable before value exists");
        let after_value = after_value.expect("comparable after value exists");
        let change = SignatureAxisChange {
            axis: axis.to_string(),
            before: before_value,
            after: after_value,
            delta: after_value - before_value,
        };
        match change.delta.cmp(&0) {
            std::cmp::Ordering::Greater => worsened.push(change),
            std::cmp::Ordering::Less => improved.push(change),
            std::cmp::Ordering::Equal => unchanged.push(change),
        }
    }

    (worsened, improved, unchanged, unmeasured)
}

fn snapshot_evidence_diff(
    before: Option<&Sig0Document>,
    after: Option<&Sig0Document>,
) -> SnapshotEvidenceDiff {
    let (before, after) = match (before, after) {
        (Some(before), Some(after)) => (before, after),
        _ => {
            return SnapshotEvidenceDiff {
                available: false,
                unavailable_reason: Some(
                    "before and after ArchSig JSON are required for component / edge evidence diff"
                        .to_string(),
                ),
                component_delta: None,
                edge_delta: None,
                policy_violation_delta: None,
            };
        }
    };

    let before_components = before
        .components
        .iter()
        .map(|component| component.id.clone())
        .collect::<BTreeSet<_>>();
    let after_components = after
        .components
        .iter()
        .map(|component| component.id.clone())
        .collect::<BTreeSet<_>>();
    let before_edges = before.edges.iter().cloned().collect::<BTreeSet<_>>();
    let after_edges = after.edges.iter().cloned().collect::<BTreeSet<_>>();
    let before_policy_violations = before
        .policy_violations
        .iter()
        .cloned()
        .collect::<BTreeSet<_>>();
    let after_policy_violations = after
        .policy_violations
        .iter()
        .cloned()
        .collect::<BTreeSet<_>>();

    SnapshotEvidenceDiff {
        available: true,
        unavailable_reason: None,
        component_delta: Some(ComponentSetDelta {
            before_count: before_components.len(),
            after_count: after_components.len(),
            delta: after_components.len() as i64 - before_components.len() as i64,
            added: set_added(&before_components, &after_components),
            removed: set_removed(&before_components, &after_components),
        }),
        edge_delta: Some(EdgeSetDelta {
            before_count: before_edges.len(),
            after_count: after_edges.len(),
            delta: after_edges.len() as i64 - before_edges.len() as i64,
            added: set_added(&before_edges, &after_edges),
            removed: set_removed(&before_edges, &after_edges),
        }),
        policy_violation_delta: Some(PolicyViolationSetDelta {
            before_count: before_policy_violations.len(),
            after_count: after_policy_violations.len(),
            delta: after_policy_violations.len() as i64 - before_policy_violations.len() as i64,
            added: set_added(&before_policy_violations, &after_policy_violations),
            removed: set_removed(&before_policy_violations, &after_policy_violations),
        }),
    }
}

fn set_added<T: Ord + Clone>(before: &BTreeSet<T>, after: &BTreeSet<T>) -> Vec<T> {
    after.difference(before).cloned().collect()
}

fn set_removed<T: Ord + Clone>(before: &BTreeSet<T>, after: &BTreeSet<T>) -> Vec<T> {
    before.difference(after).cloned().collect()
}

fn snapshot_diff_attribution(
    after: &SignatureSnapshotStoreRecordV0,
    evidence_diff: &SnapshotEvidenceDiff,
    worsened_axes: &[SignatureAxisChange],
    pr_metadata: &[EmpiricalDatasetInput],
) -> SnapshotDiffAttribution {
    let touched_components = touched_components_from_evidence_diff(evidence_diff);
    let worsened_axis_names = worsened_axes
        .iter()
        .map(|axis| axis.axis.clone())
        .collect::<Vec<_>>();
    let mut candidates = pr_metadata
        .iter()
        .map(|metadata| {
            attribution_candidate(
                after,
                evidence_diff,
                &touched_components,
                &worsened_axis_names,
                metadata,
            )
        })
        .collect::<Vec<_>>();
    candidates.sort_by(|left, right| {
        right
            .confidence
            .partial_cmp(&left.confidence)
            .unwrap_or(std::cmp::Ordering::Equal)
            .then(left.id.cmp(&right.id))
    });

    let method = if pr_metadata.is_empty() {
        "none: PR metadata not provided".to_string()
    } else if touched_components.is_empty() {
        "pr-metadata: commit match and changed components; raw evidence diff unavailable or empty"
            .to_string()
    } else {
        "pr-metadata: commit match and changed-component overlap with added/removed evidence"
            .to_string()
    };

    let shared_worsened_axes = if candidates
        .iter()
        .filter(|candidate| candidate.confidence_level != "unknown")
        .count()
        > 1
    {
        worsened_axis_names
    } else {
        Vec::new()
    };

    SnapshotDiffAttribution {
        method,
        shared_worsened_axes,
        candidates,
    }
}

fn touched_components_from_evidence_diff(evidence_diff: &SnapshotEvidenceDiff) -> BTreeSet<String> {
    let mut components = BTreeSet::new();
    if let Some(component_delta) = &evidence_diff.component_delta {
        components.extend(component_delta.added.iter().cloned());
        components.extend(component_delta.removed.iter().cloned());
    }
    if let Some(edge_delta) = &evidence_diff.edge_delta {
        for edge in edge_delta.added.iter().chain(edge_delta.removed.iter()) {
            components.insert(edge.source.clone());
            components.insert(edge.target.clone());
        }
    }
    if let Some(policy_delta) = &evidence_diff.policy_violation_delta {
        for violation in policy_delta.added.iter().chain(policy_delta.removed.iter()) {
            components.insert(violation.source.clone());
            components.insert(violation.target.clone());
        }
    }
    components
}

fn attribution_candidate(
    after: &SignatureSnapshotStoreRecordV0,
    evidence_diff: &SnapshotEvidenceDiff,
    touched_components: &BTreeSet<String>,
    worsened_axes: &[String],
    metadata: &EmpiricalDatasetInput,
) -> AttributionCandidate {
    let changed_components = metadata.pr_metrics.changed_components.clone();
    let changed_set = changed_components.iter().cloned().collect::<BTreeSet<_>>();
    let overlap = changed_set
        .intersection(touched_components)
        .cloned()
        .collect::<Vec<_>>();
    let matched_edges = matched_edges_from_evidence_diff(evidence_diff, &changed_set);
    let matched_policy_violations =
        matched_policy_violations_from_evidence_diff(evidence_diff, &changed_set);
    let mut matched_components = overlap;
    matched_components.sort();
    matched_components.dedup();
    let mut confidence = 0.0;
    let mut reasons = Vec::new();

    if after.revision.sha == metadata.pull_request.head_commit {
        confidence += 0.35;
        reasons.push("after revision matches pullRequest.headCommit".to_string());
    }
    if metadata
        .pull_request
        .merge_commit
        .as_ref()
        .is_some_and(|merge_commit| after.revision.sha == *merge_commit)
    {
        confidence += 0.35;
        reasons.push("after revision matches pullRequest.mergeCommit".to_string());
    }
    if !matched_components.is_empty() {
        let denominator = touched_components.len().max(1) as f64;
        confidence += 0.35 * (matched_components.len() as f64 / denominator).min(1.0);
        reasons.push(format!(
            "changed components overlap with evidence diff: {}",
            matched_components.join(", ")
        ));
    }
    if !matched_edges.is_empty() {
        confidence += 0.15;
        reasons.push(format!(
            "changed components touch added/removed edges: {}",
            edge_labels(&matched_edges).join(", ")
        ));
    }
    if !matched_policy_violations.is_empty() {
        confidence += 0.15;
        reasons.push(format!(
            "changed components touch added/removed policy violations: {}",
            policy_violation_labels(&matched_policy_violations).join(", ")
        ));
    }
    if !worsened_axes.is_empty() && confidence > 0.0 {
        confidence += 0.10;
        reasons.push(format!(
            "signature worsened on axes: {}",
            worsened_axes.join(", ")
        ));
    }
    if reasons.is_empty() {
        reasons.push(
            "weak candidate: PR metadata provided but no commit or evidence overlap".to_string(),
        );
    }
    let confidence = round_confidence(confidence.min(0.95));

    AttributionCandidate {
        kind: "pullRequest".to_string(),
        id: format!("#{}", metadata.pull_request.number),
        confidence,
        confidence_level: confidence_level(confidence).to_string(),
        reasons,
        changed_components,
        matched_components,
        matched_edges,
        matched_policy_violations,
        affected_axes: if confidence > 0.0 {
            worsened_axes.to_vec()
        } else {
            Vec::new()
        },
    }
}

fn matched_edges_from_evidence_diff(
    evidence_diff: &SnapshotEvidenceDiff,
    changed_components: &BTreeSet<String>,
) -> Vec<Edge> {
    let Some(edge_delta) = &evidence_diff.edge_delta else {
        return Vec::new();
    };
    edge_delta
        .added
        .iter()
        .chain(edge_delta.removed.iter())
        .filter(|edge| {
            changed_components.contains(&edge.source) || changed_components.contains(&edge.target)
        })
        .cloned()
        .collect()
}

fn matched_policy_violations_from_evidence_diff(
    evidence_diff: &SnapshotEvidenceDiff,
    changed_components: &BTreeSet<String>,
) -> Vec<PolicyViolation> {
    let Some(policy_delta) = &evidence_diff.policy_violation_delta else {
        return Vec::new();
    };
    policy_delta
        .added
        .iter()
        .chain(policy_delta.removed.iter())
        .filter(|violation| {
            changed_components.contains(&violation.source)
                || changed_components.contains(&violation.target)
        })
        .cloned()
        .collect()
}

fn edge_labels(edges: &[Edge]) -> Vec<String> {
    edges
        .iter()
        .map(|edge| format!("{} -> {}", edge.source, edge.target))
        .collect()
}

fn policy_violation_labels(violations: &[PolicyViolation]) -> Vec<String> {
    violations
        .iter()
        .map(|violation| {
            format!(
                "{}:{} -> {}",
                violation.axis, violation.source, violation.target
            )
        })
        .collect()
}

fn confidence_level(confidence: f64) -> &'static str {
    if confidence >= 0.80 {
        "high"
    } else if confidence >= 0.50 {
        "medium"
    } else if confidence > 0.0 {
        "low"
    } else {
        "unknown"
    }
}

fn round_confidence(value: f64) -> f64 {
    (value * 100.0).round() / 100.0
}

fn count_checks(checks: &[ValidationCheck], result: &str) -> usize {
    checks.iter().filter(|check| check.result == result).count()
}

fn validation_check(id: &str, title: &str, result: &str) -> ValidationCheck {
    ValidationCheck {
        id: id.to_string(),
        title: title.to_string(),
        result: result.to_string(),
        reason: None,
        count: None,
        examples: Vec::new(),
        metric: None,
        lean_boundary: None,
    }
}

fn check_schema_version(schema_version: &str) -> ValidationCheck {
    let mut check = validation_check(
        "schema-version-supported",
        "input schema version is supported",
        if schema_version == SCHEMA_VERSION {
            "pass"
        } else {
            "fail"
        },
    );
    if check.result == "fail" {
        check.reason = Some(format!("unsupported schemaVersion: {schema_version}"));
    }
    check
}

fn check_component_id_nodup(components: &[Component]) -> ValidationCheck {
    let duplicate_ids = duplicates(components.iter().map(|component| component.id.as_str()));
    let mut check = validation_check(
        "component-id-nodup",
        "component ids are duplicate-free",
        if duplicate_ids.is_empty() {
            "pass"
        } else {
            "fail"
        },
    );
    check.lean_boundary = Some("Nodup-like JSON evidence only".to_string());
    if !duplicate_ids.is_empty() {
        check.reason = Some("duplicate component ids found".to_string());
        check.count = Some(duplicate_ids.len());
        check.examples = duplicate_ids
            .into_iter()
            .take(5)
            .map(|component_id| ValidationExample {
                component_id: Some(component_id),
                path: None,
                source: None,
                target: None,
                evidence: None,
            })
            .collect();
    }
    check
}

fn check_component_path_nodup(components: &[Component]) -> ValidationCheck {
    let duplicate_paths = duplicates(components.iter().map(|component| component.path.as_str()));
    let mut check = validation_check(
        "component-path-nodup",
        "component paths are duplicate-free",
        if duplicate_paths.is_empty() {
            "pass"
        } else {
            "fail"
        },
    );
    if !duplicate_paths.is_empty() {
        check.reason = Some("duplicate component paths found".to_string());
        check.count = Some(duplicate_paths.len());
        check.examples = duplicate_paths
            .into_iter()
            .take(5)
            .map(|path| ValidationExample {
                component_id: None,
                path: Some(path),
                source: None,
                target: None,
                evidence: None,
            })
            .collect();
    }
    check
}

fn check_edge_endpoint_resolved(
    edges: &[Edge],
    component_ids: &BTreeSet<String>,
    local_roots: &BTreeSet<String>,
) -> ValidationCheck {
    let unresolved = unresolved_edges(edges, component_ids, local_roots);
    let mut check = validation_check(
        "edge-endpoint-resolved",
        "edge endpoints are local components or external nodes",
        if unresolved.is_empty() {
            "pass"
        } else {
            "fail"
        },
    );
    if !unresolved.is_empty() {
        check.reason = Some("edge endpoint is not covered by the selected universe".to_string());
        check.count = Some(unresolved.len());
        check.examples = unresolved.into_iter().take(5).collect();
    }
    check
}

fn check_edge_closure_local(
    edges: &[Edge],
    component_ids: &BTreeSet<String>,
    local_roots: &BTreeSet<String>,
) -> ValidationCheck {
    let open_edges: Vec<ValidationExample> = edges
        .iter()
        .filter(|edge| {
            component_ids.contains(&edge.source)
                && is_local_like(&edge.target, local_roots)
                && !component_ids.contains(&edge.target)
                && !is_module_root_target(&edge.target, component_ids, local_roots)
        })
        .map(edge_example)
        .collect();
    let mut check = validation_check(
        "edge-closure-local",
        "local dependency edges are closed over selected universe",
        if open_edges.is_empty() {
            "pass"
        } else {
            "fail"
        },
    );
    check.lean_boundary = Some("edge-closedness candidate for local-only projection".to_string());
    if !open_edges.is_empty() {
        check.reason = Some("local-like dependency target is missing from components".to_string());
        check.count = Some(open_edges.len());
        check.examples = open_edges.into_iter().take(5).collect();
    }
    check
}

fn check_external_edge_targets(
    external_edges: &[ValidationExample],
    universe_mode: &str,
) -> ValidationCheck {
    let has_external_edges = !external_edges.is_empty();
    let result = if universe_mode == "local-only" && has_external_edges {
        "warn"
    } else {
        "pass"
    };
    let mut check = validation_check(
        "external-edge-targets",
        "external import targets are outside selected universe",
        result,
    );
    check.lean_boundary =
        Some("not a ComponentUniverse witness for the full import graph".to_string());
    if has_external_edges {
        check.count = Some(external_edges.len());
        check.examples = external_edges.iter().take(5).cloned().collect();
    }
    check
}

fn check_metric_status_complete(metric_status: &BTreeMap<String, MetricStatus>) -> ValidationCheck {
    let expected_axes = [
        "hasCycle",
        "sccMaxSize",
        "maxDepth",
        "fanoutRisk",
        "boundaryViolationCount",
        "abstractionViolationCount",
    ];
    let missing: Vec<&str> = expected_axes
        .iter()
        .copied()
        .filter(|axis| !metric_status.contains_key(*axis))
        .collect();
    let mut check = validation_check(
        "metric-status-complete",
        "signature axes have metric status entries",
        if missing.is_empty() { "pass" } else { "warn" },
    );
    if !missing.is_empty() {
        check.reason = Some(format!(
            "missing metricStatus entries: {}",
            missing.join(", ")
        ));
        check.count = Some(missing.len());
    }
    check
}

fn check_metric_measured(
    id: &str,
    title: &str,
    metric: &str,
    metric_status: &BTreeMap<String, MetricStatus>,
) -> ValidationCheck {
    let status = metric_status.get(metric);
    let measured = status.is_some_and(|status| status.measured);
    let mut check = validation_check(id, title, if measured { "pass" } else { "not_measured" });
    check.metric = Some(metric.to_string());
    if !measured {
        check.reason = Some(
            status
                .and_then(|status| status.reason.clone())
                .unwrap_or_else(|| "metricStatus entry is missing".to_string()),
        );
    }
    check
}

fn check_air_schema_version(schema_version: &str) -> ValidationCheck {
    let mut check = validation_check(
        "air-schema-version-supported",
        "AIR schema version is supported",
        if schema_version == AIR_SCHEMA_VERSION {
            "pass"
        } else {
            "fail"
        },
    );
    if check.result == "fail" {
        check.reason = Some(format!("unsupported schemaVersion: {schema_version}"));
    }
    check
}

fn check_air_unique_ids(document: &AirDocumentV0) -> ValidationCheck {
    let duplicate_examples: Vec<ValidationExample> = [
        (
            "artifact",
            duplicates(
                document
                    .artifacts
                    .iter()
                    .map(|artifact| artifact.artifact_id.as_str()),
            ),
        ),
        (
            "evidence",
            duplicates(
                document
                    .evidence
                    .iter()
                    .map(|evidence| evidence.evidence_id.as_str()),
            ),
        ),
        (
            "component",
            duplicates(
                document
                    .components
                    .iter()
                    .map(|component| component.id.as_str()),
            ),
        ),
        (
            "relation",
            duplicates(
                document
                    .relations
                    .iter()
                    .map(|relation| relation.id.as_str()),
            ),
        ),
        (
            "claim",
            duplicates(document.claims.iter().map(|claim| claim.claim_id.as_str())),
        ),
    ]
    .into_iter()
    .flat_map(|(kind, ids)| {
        ids.into_iter()
            .map(move |id| generic_validation_example(kind, &id, "duplicate id"))
    })
    .collect();

    let mut check = validation_check(
        "air-id-nodup",
        "AIR ids are duplicate-free within each reference namespace",
        if duplicate_examples.is_empty() {
            "pass"
        } else {
            "fail"
        },
    );
    if !duplicate_examples.is_empty() {
        check.reason = Some("duplicate AIR ids found".to_string());
        check.count = Some(duplicate_examples.len());
        check.examples = duplicate_examples.into_iter().take(5).collect();
    }
    check
}

fn check_air_artifact_refs(document: &AirDocumentV0) -> ValidationCheck {
    let artifact_ids = air_artifact_ids(document);
    let unresolved: Vec<ValidationExample> = document
        .evidence
        .iter()
        .filter_map(|evidence| {
            let artifact_ref = evidence.artifact_ref.as_ref()?;
            (!artifact_ids.contains(artifact_ref)).then(|| {
                generic_validation_example(
                    &evidence.evidence_id,
                    artifact_ref,
                    "dangling artifact_ref",
                )
            })
        })
        .collect();

    air_ref_check(
        "air-artifact-refs-resolved",
        "evidence artifact refs resolve to AIR artifacts",
        unresolved,
    )
}

fn check_air_component_refs(document: &AirDocumentV0) -> ValidationCheck {
    let component_ids = air_component_ids(document);
    let mut unresolved = Vec::new();
    for relation in &document.relations {
        if let Some(component_ref) = &relation.from_component {
            if !component_ids.contains(component_ref) {
                unresolved.push(generic_validation_example(
                    &relation.id,
                    component_ref,
                    "dangling relation.from",
                ));
            }
        }
        if let Some(component_ref) = &relation.to_component {
            if !component_ids.contains(component_ref) {
                unresolved.push(generic_validation_example(
                    &relation.id,
                    component_ref,
                    "dangling relation.to",
                ));
            }
        }
    }

    air_ref_check(
        "air-component-refs-resolved",
        "relation component refs resolve to AIR components",
        unresolved,
    )
}

fn check_air_evidence_refs(document: &AirDocumentV0) -> ValidationCheck {
    let evidence_ids = air_evidence_ids(document);
    let mut unresolved = Vec::new();

    for component in &document.components {
        unresolved.extend(unresolved_refs(
            &component.id,
            "dangling component.evidence_refs",
            &component.evidence_refs,
            &evidence_ids,
        ));
    }
    for relation in &document.relations {
        unresolved.extend(unresolved_refs(
            &relation.id,
            "dangling relation.evidence_refs",
            &relation.evidence_refs,
            &evidence_ids,
        ));
    }
    for diagram in &document.semantic_diagrams {
        unresolved.extend(unresolved_refs(
            &diagram.id,
            "dangling semantic_diagram.evidence_refs",
            &diagram.evidence_refs,
            &evidence_ids,
        ));
    }
    for path in &document.architecture_paths {
        unresolved.extend(unresolved_refs(
            &path.path_id,
            "dangling architecture_path.evidence_refs",
            &path.evidence_refs,
            &evidence_ids,
        ));
    }
    for generator in &document.homotopy_generators {
        unresolved.extend(unresolved_refs(
            &generator.generator_id,
            "dangling homotopy_generator.evidence_refs",
            &generator.evidence_refs,
            &evidence_ids,
        ));
    }
    for witness in &document.nonfillability_witnesses {
        unresolved.extend(unresolved_refs(
            &witness.witness_id,
            "dangling nonfillability_witness.evidence_refs",
            &witness.evidence_refs,
            &evidence_ids,
        ));
    }
    for claim in &document.claims {
        unresolved.extend(unresolved_refs(
            &claim.claim_id,
            "dangling claim.evidence_refs",
            &claim.evidence_refs,
            &evidence_ids,
        ));
    }

    air_ref_check(
        "air-evidence-refs-resolved",
        "AIR evidence refs resolve to evidence objects",
        unresolved,
    )
}

fn check_air_claim_refs(document: &AirDocumentV0) -> ValidationCheck {
    let claim_ids = air_claim_ids(document);
    let mut unresolved = Vec::new();

    for diagram in &document.semantic_diagrams {
        if let Some(claim_ref) = &diagram.filler_claim_ref {
            if !claim_ids.contains(claim_ref) {
                unresolved.push(generic_validation_example(
                    &diagram.id,
                    claim_ref,
                    "dangling semantic_diagram.filler_claim_ref",
                ));
            }
        }
    }
    for generator in &document.homotopy_generators {
        unresolved.extend(unresolved_refs(
            &generator.generator_id,
            "dangling homotopy_generator.preserves_observation_claim_refs",
            &generator.preserves_observation_claim_refs,
            &claim_ids,
        ));
    }
    for witness in &document.nonfillability_witnesses {
        if !claim_ids.contains(&witness.claim_ref) {
            unresolved.push(generic_validation_example(
                &witness.witness_id,
                &witness.claim_ref,
                "dangling nonfillability_witness.claim_ref",
            ));
        }
    }
    unresolved.extend(optional_unresolved_ref(
        "extension.embedding_claim_ref",
        document.extension.embedding_claim_ref.as_ref(),
        &claim_ids,
    ));
    unresolved.extend(optional_unresolved_ref(
        "extension.feature_view_claim_ref",
        document.extension.feature_view_claim_ref.as_ref(),
        &claim_ids,
    ));
    unresolved.extend(optional_unresolved_ref(
        "extension.split_claim_ref",
        document.extension.split_claim_ref.as_ref(),
        &claim_ids,
    ));
    unresolved.extend(unresolved_refs(
        "extension.interaction_claim_refs",
        "dangling extension.interaction_claim_refs",
        &document.extension.interaction_claim_refs,
        &claim_ids,
    ));

    air_ref_check(
        "air-claim-refs-resolved",
        "AIR claim refs resolve to claim objects",
        unresolved,
    )
}

fn check_air_path_and_witness_refs(document: &AirDocumentV0) -> ValidationCheck {
    let path_ids: BTreeSet<String> = document
        .architecture_paths
        .iter()
        .map(|path| path.path_id.clone())
        .collect();
    let diagram_ids: BTreeSet<String> = document
        .semantic_diagrams
        .iter()
        .map(|diagram| diagram.id.clone())
        .collect();
    let witness_ids: BTreeSet<String> = document
        .nonfillability_witnesses
        .iter()
        .map(|witness| witness.witness_id.clone())
        .collect();
    let mut unresolved = Vec::new();

    for diagram in &document.semantic_diagrams {
        if !path_ids.contains(&diagram.lhs_path_ref) {
            unresolved.push(generic_validation_example(
                &diagram.id,
                &diagram.lhs_path_ref,
                "dangling semantic_diagram.lhs_path_ref",
            ));
        }
        if !path_ids.contains(&diagram.rhs_path_ref) {
            unresolved.push(generic_validation_example(
                &diagram.id,
                &diagram.rhs_path_ref,
                "dangling semantic_diagram.rhs_path_ref",
            ));
        }
        unresolved.extend(unresolved_refs(
            &diagram.id,
            "dangling semantic_diagram.nonfillability_witness_refs",
            &diagram.nonfillability_witness_refs,
            &witness_ids,
        ));
    }
    for generator in &document.homotopy_generators {
        unresolved.extend(unresolved_refs(
            &generator.generator_id,
            "dangling homotopy_generator.diagram_refs",
            &generator.diagram_refs,
            &diagram_ids,
        ));
    }
    for witness in &document.nonfillability_witnesses {
        if !diagram_ids.contains(&witness.diagram_ref) {
            unresolved.push(generic_validation_example(
                &witness.witness_id,
                &witness.diagram_ref,
                "dangling nonfillability_witness.diagram_ref",
            ));
        }
    }

    air_ref_check(
        "air-path-witness-refs-resolved",
        "AIR path, diagram, and witness refs resolve",
        unresolved,
    )
}

fn check_air_coverage_universe_refs(document: &AirDocumentV0) -> ValidationCheck {
    let artifact_ids = air_artifact_ids(document);
    let unresolved: Vec<ValidationExample> = document
        .coverage
        .layers
        .iter()
        .flat_map(|layer| {
            unresolved_refs(
                &layer.layer,
                "dangling coverage.layers.universe_refs",
                &layer.universe_refs,
                &artifact_ids,
            )
        })
        .collect();
    air_ref_check(
        "air-coverage-universe-refs-resolved",
        "coverage universe refs resolve to artifacts",
        unresolved,
    )
}

fn check_air_signature_measurement_boundary(document: &AirDocumentV0) -> ValidationCheck {
    let valid_boundaries = [
        "measuredZero",
        "measuredNonzero",
        "unmeasured",
        "outOfScope",
    ];
    let mut invalid = Vec::new();

    for axis in &document.signature.axes {
        if !valid_boundaries.contains(&axis.measurement_boundary.as_str()) {
            invalid.push(generic_validation_example(
                &axis.axis,
                &axis.measurement_boundary,
                "unsupported signature measurement_boundary",
            ));
            continue;
        }
        if !axis.measured {
            if !matches!(
                axis.measurement_boundary.as_str(),
                "unmeasured" | "outOfScope"
            ) {
                invalid.push(generic_validation_example(
                    &axis.axis,
                    &axis.measurement_boundary,
                    "unmeasured axis must use unmeasured or outOfScope boundary",
                ));
            }
            continue;
        }
        match axis.value {
            Some(0) => {
                if axis.measurement_boundary != "measuredZero" {
                    invalid.push(generic_validation_example(
                        &axis.axis,
                        &axis.measurement_boundary,
                        "zero measured axis must use measuredZero boundary",
                    ));
                }
            }
            Some(_) => {
                if axis.measurement_boundary != "measuredNonzero" {
                    invalid.push(generic_validation_example(
                        &axis.axis,
                        &axis.measurement_boundary,
                        "nonzero measured axis must use measuredNonzero boundary",
                    ));
                }
            }
            None => {
                invalid.push(generic_validation_example(
                    &axis.axis,
                    &axis.measurement_boundary,
                    "measured axis must carry a value",
                ));
            }
        }
    }

    for layer in &document.coverage.layers {
        if !valid_boundaries.contains(&layer.measurement_boundary.as_str()) {
            invalid.push(generic_validation_example(
                &layer.layer,
                &layer.measurement_boundary,
                "unsupported coverage measurement_boundary",
            ));
        }
    }

    air_ref_check(
        "air-signature-boundary-compatible",
        "signature and coverage measurement boundaries are internally consistent",
        invalid,
    )
}

fn check_air_claim_measurement_boundary(document: &AirDocumentV0) -> ValidationCheck {
    let valid_boundaries = [
        "measuredZero",
        "measuredNonzero",
        "unmeasured",
        "outOfScope",
    ];
    let valid_classifications = [
        "proved",
        "measured",
        "assumed",
        "empirical",
        "unmeasured",
        "out_of_scope",
    ];
    let mut invalid = Vec::new();

    for claim in &document.claims {
        if !valid_boundaries.contains(&claim.measurement_boundary.as_str()) {
            invalid.push(generic_validation_example(
                &claim.claim_id,
                &claim.measurement_boundary,
                "unsupported measurement_boundary",
            ));
        }
        if !valid_classifications.contains(&claim.claim_classification.as_str()) {
            invalid.push(generic_validation_example(
                &claim.claim_id,
                &claim.claim_classification,
                "unsupported claim_classification",
            ));
        }
        if claim.claim_classification == "measured"
            && !matches!(
                claim.measurement_boundary.as_str(),
                "measuredZero" | "measuredNonzero"
            )
        {
            invalid.push(generic_validation_example(
                &claim.claim_id,
                &claim.measurement_boundary,
                "measured claim must use a measured boundary",
            ));
        }
        if matches!(
            claim.measurement_boundary.as_str(),
            "measuredZero" | "measuredNonzero"
        ) && claim.claim_classification == "unmeasured"
        {
            invalid.push(generic_validation_example(
                &claim.claim_id,
                &claim.claim_classification,
                "measured boundary cannot be classified as unmeasured",
            ));
        }
        if claim.claim_classification == "proved" && claim.claim_level != "formal" {
            invalid.push(generic_validation_example(
                &claim.claim_id,
                &claim.claim_level,
                "proved claim must be claim_level formal",
            ));
        }
        if claim.claim_classification == "proved" && !claim.missing_preconditions.is_empty() {
            invalid.push(generic_validation_example(
                &claim.claim_id,
                &claim.missing_preconditions.join(", "),
                "proved claim has missing preconditions",
            ));
        }
    }

    air_ref_check(
        "air-claim-boundary-compatible",
        "claim classification is compatible with measurement boundary",
        invalid,
    )
}

fn check_air_measured_claim_evidence(
    document: &AirDocumentV0,
    strict_measured_evidence: bool,
) -> ValidationCheck {
    let missing_evidence: Vec<ValidationExample> = document
        .claims
        .iter()
        .filter(|claim| claim.claim_classification == "measured" && claim.evidence_refs.is_empty())
        .map(|claim| {
            generic_validation_example(
                &claim.claim_id,
                &claim.subject_ref,
                "measured claim has no evidence_refs",
            )
        })
        .collect();
    let mut check = validation_check(
        "air-measured-claims-have-evidence",
        "measured tooling claims are traceable to evidence",
        if missing_evidence.is_empty() {
            "pass"
        } else if strict_measured_evidence {
            "fail"
        } else {
            "warn"
        },
    );
    if !missing_evidence.is_empty() {
        check.reason = Some("measured claims without evidence refs found".to_string());
        check.count = Some(missing_evidence.len());
        check.examples = missing_evidence.into_iter().take(5).collect();
    }
    check
}

fn air_ref_check(id: &str, title: &str, unresolved: Vec<ValidationExample>) -> ValidationCheck {
    let mut check = validation_check(
        id,
        title,
        if unresolved.is_empty() {
            "pass"
        } else {
            "fail"
        },
    );
    if !unresolved.is_empty() {
        check.reason = Some("dangling or invalid AIR references found".to_string());
        check.count = Some(unresolved.len());
        check.examples = unresolved.into_iter().take(5).collect();
    }
    check
}

fn unresolved_refs(
    owner: &str,
    reason: &str,
    refs: &[String],
    valid_refs: &BTreeSet<String>,
) -> Vec<ValidationExample> {
    refs.iter()
        .filter(|value| !valid_refs.contains(*value))
        .map(|value| generic_validation_example(owner, value, reason))
        .collect()
}

fn optional_unresolved_ref(
    owner: &str,
    value: Option<&String>,
    valid_refs: &BTreeSet<String>,
) -> Vec<ValidationExample> {
    value
        .filter(|value| !valid_refs.contains(*value))
        .map(|value| generic_validation_example(owner, value, "dangling optional claim ref"))
        .into_iter()
        .collect()
}

fn air_artifact_ids(document: &AirDocumentV0) -> BTreeSet<String> {
    document
        .artifacts
        .iter()
        .map(|artifact| artifact.artifact_id.clone())
        .collect()
}

fn air_evidence_ids(document: &AirDocumentV0) -> BTreeSet<String> {
    document
        .evidence
        .iter()
        .map(|evidence| evidence.evidence_id.clone())
        .collect()
}

fn air_component_ids(document: &AirDocumentV0) -> BTreeSet<String> {
    document
        .components
        .iter()
        .map(|component| component.id.clone())
        .collect()
}

fn air_claim_ids(document: &AirDocumentV0) -> BTreeSet<String> {
    document
        .claims
        .iter()
        .map(|claim| claim.claim_id.clone())
        .collect()
}

fn generic_validation_example(source: &str, target: &str, evidence: &str) -> ValidationExample {
    ValidationExample {
        component_id: None,
        path: None,
        source: Some(source.to_string()),
        target: Some(target.to_string()),
        evidence: Some(evidence.to_string()),
    }
}

fn duplicates<'a>(values: impl Iterator<Item = &'a str>) -> Vec<String> {
    let mut counts: BTreeMap<&str, usize> = BTreeMap::new();
    for value in values {
        *counts.entry(value).or_default() += 1;
    }
    counts
        .into_iter()
        .filter_map(|(value, count)| (count > 1).then(|| value.to_string()))
        .collect()
}

fn component_roots(component_ids: &BTreeSet<String>) -> BTreeSet<String> {
    component_ids
        .iter()
        .filter_map(|id| id.split('.').next())
        .filter(|root| !root.is_empty())
        .map(str::to_string)
        .collect()
}

fn unresolved_edges(
    edges: &[Edge],
    component_ids: &BTreeSet<String>,
    local_roots: &BTreeSet<String>,
) -> Vec<ValidationExample> {
    edges
        .iter()
        .filter(|edge| {
            edge.source.is_empty()
                || edge.target.is_empty()
                || (!component_ids.contains(&edge.source)
                    && is_local_like(&edge.source, local_roots)
                    && !is_module_root_target(&edge.source, component_ids, local_roots))
                || (!component_ids.contains(&edge.target)
                    && is_local_like(&edge.target, local_roots)
                    && !is_module_root_target(&edge.target, component_ids, local_roots))
        })
        .map(edge_example)
        .collect()
}

fn external_edges(
    document: &Sig0Document,
    component_ids: &BTreeSet<String>,
    local_roots: &BTreeSet<String>,
) -> Vec<ValidationExample> {
    document
        .edges
        .iter()
        .filter(|edge| {
            (!component_ids.contains(&edge.source) && !is_local_like(&edge.source, local_roots))
                || is_module_root_target(&edge.source, component_ids, local_roots)
                || (!component_ids.contains(&edge.target)
                    && !is_local_like(&edge.target, local_roots))
                || is_module_root_target(&edge.target, component_ids, local_roots)
        })
        .map(edge_example)
        .collect()
}

fn is_local_like(component_id: &str, local_roots: &BTreeSet<String>) -> bool {
    component_id
        .split('.')
        .next()
        .is_some_and(|root| local_roots.contains(root))
}

fn is_module_root_target(
    component_id: &str,
    component_ids: &BTreeSet<String>,
    local_roots: &BTreeSet<String>,
) -> bool {
    local_roots.contains(component_id)
        && !component_ids.contains(component_id)
        && component_ids.iter().any(|id| {
            id.strip_prefix(component_id)
                .is_some_and(|rest| rest.starts_with('.'))
        })
}

fn edge_example(edge: &Edge) -> ValidationExample {
    ValidationExample {
        component_id: None,
        path: None,
        source: Some(edge.source.clone()),
        target: Some(edge.target.clone()),
        evidence: Some(edge.evidence.clone()),
    }
}

fn measured_status(source: &str) -> MetricStatus {
    MetricStatus {
        measured: true,
        reason: None,
        source: Some(source.to_string()),
    }
}

fn unmeasured_status(reason: String) -> MetricStatus {
    MetricStatus {
        measured: false,
        reason: Some(reason),
        source: None,
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
#[serde(rename_all = "camelCase")]
struct PolicyFile {
    schema_version: String,
    policy_id: String,
    component_id_kind: String,
    selector_semantics: String,
    boundary: Option<BoundaryPolicy>,
    abstraction: Option<AbstractionPolicy>,
}

#[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
#[serde(rename_all = "camelCase")]
struct RuntimeEdgeEvidenceFile {
    schema_version: String,
    component_id_kind: String,
    edges: Vec<RuntimeEdgeEvidence>,
}

impl RuntimeEdgeEvidenceFile {
    fn read(
        path: &Path,
        components: &[Component],
    ) -> Result<Vec<RuntimeEdgeEvidence>, Box<dyn Error>> {
        let source = fs::read_to_string(path)?;
        let file: RuntimeEdgeEvidenceFile = serde_json::from_str(&source)?;
        if file.schema_version != RUNTIME_EDGE_EVIDENCE_SCHEMA_VERSION {
            return Err(format!(
                "unsupported runtime edge evidence schemaVersion: {}",
                file.schema_version
            )
            .into());
        }
        if file.component_id_kind != COMPONENT_KIND {
            return Err(format!(
                "unsupported runtime edge evidence componentIdKind: {}",
                file.component_id_kind
            )
            .into());
        }

        let component_ids = local_component_ids(components);
        let mut edges = file.edges;
        for edge in &edges {
            validate_runtime_edge_evidence(edge, &component_ids)?;
        }
        edges.sort_by(|a, b| {
            a.source
                .cmp(&b.source)
                .then(a.target.cmp(&b.target))
                .then(a.label.cmp(&b.label))
                .then(a.evidence_location.path.cmp(&b.evidence_location.path))
                .then(a.evidence_location.line.cmp(&b.evidence_location.line))
                .then(a.evidence_location.symbol.cmp(&b.evidence_location.symbol))
        });
        Ok(edges)
    }
}

fn validate_runtime_edge_evidence(
    edge: &RuntimeEdgeEvidence,
    component_ids: &BTreeSet<String>,
) -> Result<(), String> {
    if edge.source.is_empty() {
        return Err("runtime edge source must not be empty".to_string());
    }
    if edge.target.is_empty() {
        return Err("runtime edge target must not be empty".to_string());
    }
    if edge.label.is_empty() {
        return Err("runtime edge label must not be empty".to_string());
    }
    if edge.evidence_location.path.is_empty() {
        return Err("runtime edge evidenceLocation.path must not be empty".to_string());
    }
    if !component_ids.contains(&edge.source) {
        return Err(format!(
            "runtime edge source is outside component universe: {}",
            edge.source
        ));
    }
    if !component_ids.contains(&edge.target) {
        return Err(format!(
            "runtime edge target is outside component universe: {}",
            edge.target
        ));
    }
    Ok(())
}

fn project_runtime_dependency_graph(
    evidence: &[RuntimeEdgeEvidence],
) -> RuntimeDependencyGraphProjection {
    let mut by_pair: BTreeMap<(String, String), usize> = BTreeMap::new();
    for item in evidence {
        *by_pair
            .entry((item.source.clone(), item.target.clone()))
            .or_default() += 1;
    }

    let edges = by_pair
        .into_iter()
        .map(|((source, target), count)| Edge {
            source,
            target,
            kind: "runtime".to_string(),
            evidence: format!("runtime edge evidence count: {count}"),
        })
        .collect();

    RuntimeDependencyGraphProjection {
        projection_rule: RUNTIME_PROJECTION_RULE_VERSION.to_string(),
        edge_kind: "runtime".to_string(),
        edges,
    }
}

impl PolicyFile {
    fn read(path: &Path) -> Result<Self, Box<dyn Error>> {
        let source = fs::read_to_string(path)?;
        let policy: PolicyFile = serde_json::from_str(&source)?;
        if policy.schema_version != "signature-policy-v0" {
            return Err(format!(
                "unsupported policy schemaVersion: {}",
                policy.schema_version
            )
            .into());
        }
        if policy.component_id_kind != COMPONENT_KIND {
            return Err(format!(
                "unsupported policy componentIdKind: {}",
                policy.component_id_kind
            )
            .into());
        }
        if policy.selector_semantics != "exact-or-prefix-star" {
            return Err(format!(
                "unsupported policy selectorSemantics: {}",
                policy.selector_semantics
            )
            .into());
        }
        Ok(policy)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
#[serde(rename_all = "camelCase")]
struct BoundaryPolicy {
    groups: Vec<BoundaryGroup>,
    allowed_dependencies: Vec<AllowedDependency>,
    unmatched_component: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
struct BoundaryGroup {
    id: String,
    components: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
#[serde(rename_all = "camelCase")]
struct AllowedDependency {
    source_group: String,
    target_group: String,
    #[allow(dead_code)]
    reason: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
#[serde(rename_all = "camelCase")]
struct AbstractionPolicy {
    relations: Vec<AbstractionRelation>,
    #[allow(dead_code)]
    unmatched_component: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
#[serde(rename_all = "camelCase")]
struct AbstractionRelation {
    id: String,
    abstraction: String,
    clients: Vec<String>,
    implementations: Vec<String>,
    #[serde(default)]
    allowed_direct_implementation_dependencies: Vec<String>,
}

fn measure_boundary(
    boundary: &BoundaryPolicy,
    components: &[Component],
    edges: &[Edge],
) -> Result<(usize, Vec<PolicyViolation>), String> {
    if boundary.unmatched_component.as_deref() != Some("not-measured") {
        return Err("boundary.unmatchedComponent must be not-measured".to_string());
    }

    let component_ids = local_component_ids(components);
    let mut membership: BTreeMap<String, BTreeSet<String>> = component_ids
        .iter()
        .map(|id| (id.clone(), BTreeSet::new()))
        .collect();

    for group in &boundary.groups {
        if group.id.is_empty() {
            return Err("boundary group id must not be empty".to_string());
        }
        if group.components.is_empty() {
            return Err(format!(
                "boundary group {} has no component selectors",
                group.id
            ));
        }

        for selector in &group.components {
            let matches = resolve_selector(selector, &component_ids)?;
            if matches.is_empty() {
                return Err(format!(
                    "boundary selector did not match component: {selector}"
                ));
            }
            for component in matches {
                membership
                    .get_mut(&component)
                    .expect("component id came from local set")
                    .insert(group.id.clone());
            }
        }
    }

    let mut group_by_component = BTreeMap::new();
    for (component, groups) in membership {
        if groups.len() != 1 {
            return Err(format!(
                "boundary group membership is not unique for {component}"
            ));
        }
        group_by_component.insert(
            component,
            groups
                .into_iter()
                .next()
                .expect("exactly one boundary group"),
        );
    }

    let allowed: BTreeSet<(String, String)> = boundary
        .allowed_dependencies
        .iter()
        .map(|dependency| {
            (
                dependency.source_group.clone(),
                dependency.target_group.clone(),
            )
        })
        .collect();

    let mut violations = Vec::new();
    for edge in edges {
        if !component_ids.contains(&edge.source) || !component_ids.contains(&edge.target) {
            continue;
        }

        let source_group = group_by_component
            .get(&edge.source)
            .expect("local component has boundary group");
        let target_group = group_by_component
            .get(&edge.target)
            .expect("local component has boundary group");
        if allowed.contains(&(source_group.clone(), target_group.clone())) {
            continue;
        }

        violations.push(PolicyViolation {
            axis: "boundaryViolationCount".to_string(),
            source: edge.source.clone(),
            target: edge.target.clone(),
            evidence: edge.evidence.clone(),
            source_group: Some(source_group.clone()),
            target_group: Some(target_group.clone()),
            relation_ids: None,
        });
    }

    Ok((violations.len(), violations))
}

fn measure_abstraction(
    abstraction: &AbstractionPolicy,
    components: &[Component],
    edges: &[Edge],
) -> Result<(usize, Vec<PolicyViolation>), String> {
    if abstraction.relations.is_empty() {
        return Err("abstraction.relations must not be empty".to_string());
    }

    let component_ids = local_component_ids(components);
    let mut relation_components = Vec::new();
    for relation in &abstraction.relations {
        if relation.id.is_empty() {
            return Err("abstraction relation id must not be empty".to_string());
        }
        let clients = resolve_nonempty_selectors(
            &relation.clients,
            &component_ids,
            &format!("abstraction relation {} clients", relation.id),
        )?;
        let abstractions = resolve_selector(&relation.abstraction, &component_ids)?;
        if abstractions.is_empty() {
            return Err(format!(
                "abstraction relation {} abstraction selector did not match component: {}",
                relation.id, relation.abstraction
            ));
        }
        let implementations = resolve_nonempty_selectors(
            &relation.implementations,
            &component_ids,
            &format!("abstraction relation {} implementations", relation.id),
        )?;
        let allowed_direct = resolve_optional_selectors(
            &relation.allowed_direct_implementation_dependencies,
            &component_ids,
        )?;

        relation_components.push(ResolvedAbstractionRelation {
            id: relation.id.clone(),
            clients,
            implementations,
            allowed_direct,
        });
    }

    let mut violations = Vec::new();
    for edge in edges {
        if !component_ids.contains(&edge.source) || !component_ids.contains(&edge.target) {
            continue;
        }

        let relation_ids: Vec<String> = relation_components
            .iter()
            .filter(|relation| {
                relation.clients.contains(&edge.source)
                    && relation.implementations.contains(&edge.target)
                    && !relation.allowed_direct.contains(&edge.target)
            })
            .map(|relation| relation.id.clone())
            .collect();

        if relation_ids.is_empty() {
            continue;
        }

        violations.push(PolicyViolation {
            axis: "abstractionViolationCount".to_string(),
            source: edge.source.clone(),
            target: edge.target.clone(),
            evidence: edge.evidence.clone(),
            source_group: None,
            target_group: None,
            relation_ids: Some(relation_ids),
        });
    }

    Ok((violations.len(), violations))
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct ResolvedAbstractionRelation {
    id: String,
    clients: BTreeSet<String>,
    implementations: BTreeSet<String>,
    allowed_direct: BTreeSet<String>,
}

fn local_component_ids(components: &[Component]) -> BTreeSet<String> {
    components
        .iter()
        .map(|component| component.id.clone())
        .collect()
}

fn resolve_nonempty_selectors(
    selectors: &[String],
    component_ids: &BTreeSet<String>,
    label: &str,
) -> Result<BTreeSet<String>, String> {
    if selectors.is_empty() {
        return Err(format!("{label} selectors must not be empty"));
    }
    let resolved = resolve_optional_selectors(selectors, component_ids)?;
    if resolved.is_empty() {
        return Err(format!("{label} selectors did not match any component"));
    }
    Ok(resolved)
}

fn resolve_optional_selectors(
    selectors: &[String],
    component_ids: &BTreeSet<String>,
) -> Result<BTreeSet<String>, String> {
    let mut resolved = BTreeSet::new();
    for selector in selectors {
        let matches = resolve_selector(selector, component_ids)?;
        if matches.is_empty() {
            return Err(format!("selector did not match component: {selector}"));
        }
        resolved.extend(matches);
    }
    Ok(resolved)
}

fn resolve_selector(
    selector: &str,
    component_ids: &BTreeSet<String>,
) -> Result<BTreeSet<String>, String> {
    validate_selector(selector)?;
    if let Some(prefix) = selector.strip_suffix('*') {
        return Ok(component_ids
            .iter()
            .filter(|component| component.starts_with(prefix))
            .cloned()
            .collect());
    }

    Ok(component_ids
        .iter()
        .filter(|component| component.as_str() == selector)
        .cloned()
        .collect())
}

fn validate_selector(selector: &str) -> Result<(), String> {
    if selector.is_empty() {
        return Err("selector must not be empty".to_string());
    }

    let star_count = selector.chars().filter(|ch| *ch == '*').count();
    if star_count > 1 || (star_count == 1 && !selector.ends_with('*')) {
        return Err(format!("unsupported selector: {selector}"));
    }

    Ok(())
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct ParsedImport {
    module: String,
    evidence: String,
}

fn parse_imports(source: &str) -> Vec<ParsedImport> {
    let mut imports = Vec::new();

    for line in source.lines() {
        let trimmed = line.trim();
        if trimmed.is_empty() || trimmed.starts_with("--") {
            continue;
        }

        let Some(rest) = trimmed.strip_prefix("import") else {
            break;
        };
        if !rest.starts_with(char::is_whitespace) {
            break;
        }

        let evidence = trimmed
            .split_once("--")
            .map(|(before_comment, _)| before_comment.trim())
            .unwrap_or(trimmed)
            .to_string();
        let import_body = evidence
            .strip_prefix("import")
            .map(str::trim)
            .unwrap_or_default();

        for module in import_body.split_whitespace() {
            imports.push(ParsedImport {
                module: module.to_string(),
                evidence: evidence.clone(),
            });
        }
    }

    imports
}

fn lean_files(root: &Path) -> Result<Vec<PathBuf>, Box<dyn Error>> {
    let mut files = Vec::new();
    for entry in WalkDir::new(root)
        .sort_by_file_name()
        .into_iter()
        .filter_entry(|entry| !is_skipped_entry(root, entry))
    {
        let entry = entry?;
        if entry.file_type().is_file() && entry.path().extension() == Some(OsStr::new("lean")) {
            files.push(entry.into_path());
        }
    }
    Ok(files)
}

fn is_skipped_entry(root: &Path, entry: &DirEntry) -> bool {
    let name = entry.file_name().to_string_lossy();
    if entry.file_type().is_file() {
        return name == "lakefile.lean";
    }

    if !entry.file_type().is_dir() {
        return false;
    }

    if matches!(name.as_ref(), ".git" | ".lake" | ".elan" | "target") {
        return true;
    }

    entry.path().parent() == Some(root) && name == "tools"
}

fn normalize_relative_path(root: &Path, path: &Path) -> Result<String, Box<dyn Error>> {
    let relative = path.strip_prefix(root)?;
    let mut parts = Vec::new();
    for component in relative.components() {
        match component {
            PathComponent::Normal(part) => parts.push(part.to_string_lossy().into_owned()),
            _ => return Err(format!("unsupported path component in {}", path.display()).into()),
        }
    }
    Ok(parts.join("/"))
}

fn module_id_from_relative_path(relative_path: &str) -> Result<String, Box<dyn Error>> {
    let Some(without_ext) = relative_path.strip_suffix(".lean") else {
        return Err(format!("Lean path does not end with .lean: {relative_path}").into());
    };
    Ok(without_ext.replace('/', "."))
}

fn dedup_edges(import_edges: Vec<ImportEdge>) -> Vec<Edge> {
    let mut by_pair: BTreeMap<(String, String), String> = BTreeMap::new();
    for edge in import_edges {
        by_pair
            .entry((edge.source, edge.target))
            .or_insert(edge.evidence);
    }

    by_pair
        .into_iter()
        .map(|((source, target), evidence)| Edge {
            source,
            target,
            kind: "import".to_string(),
            evidence,
        })
        .collect()
}

fn compute_signature(components: &[Component], edges: &[Edge]) -> Signature {
    let graph = Graph::from_components_and_edges(components, edges);
    let sccs = graph.strongly_connected_components();
    let has_cycle = sccs.iter().any(|scc| {
        scc.len() > 1
            || scc
                .first()
                .is_some_and(|node| graph.neighbors(node).iter().any(|target| target == node))
    });

    Signature {
        has_cycle: usize::from(has_cycle),
        scc_max_size: sccs.iter().map(Vec::len).max().unwrap_or(0),
        max_depth: graph.max_bounded_depth(),
        fanout_risk: graph.unique_edge_count(),
        boundary_violation_count: 0,
        abstraction_violation_count: 0,
    }
}

#[derive(Debug, Clone)]
struct Graph {
    nodes: BTreeSet<String>,
    adjacency: BTreeMap<String, BTreeSet<String>>,
}

impl Graph {
    fn from_components_and_edges(components: &[Component], edges: &[Edge]) -> Self {
        let mut nodes = BTreeSet::new();
        let mut adjacency: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();

        for component in components {
            nodes.insert(component.id.clone());
        }

        for edge in edges {
            nodes.insert(edge.source.clone());
            nodes.insert(edge.target.clone());
            adjacency
                .entry(edge.source.clone())
                .or_default()
                .insert(edge.target.clone());
        }

        for node in &nodes {
            adjacency.entry(node.clone()).or_default();
        }

        Self { nodes, adjacency }
    }

    fn neighbors(&self, node: &str) -> Vec<String> {
        self.adjacency
            .get(node)
            .map(|neighbors| neighbors.iter().cloned().collect())
            .unwrap_or_default()
    }

    fn unique_edge_count(&self) -> usize {
        self.adjacency.values().map(BTreeSet::len).sum()
    }

    fn max_fanout(&self) -> usize {
        self.adjacency
            .values()
            .map(BTreeSet::len)
            .max()
            .unwrap_or(0)
    }

    fn reachable_cone_size(&self) -> usize {
        self.nodes
            .iter()
            .map(|node| self.reachable_from(node).len())
            .max()
            .unwrap_or(0)
    }

    fn reachable_from(&self, source: &str) -> BTreeSet<String> {
        let mut visited = BTreeSet::new();
        let mut stack = self.neighbors(source);
        while let Some(node) = stack.pop() {
            if node == source || !visited.insert(node.clone()) {
                continue;
            }
            stack.extend(self.neighbors(&node));
        }
        visited
    }

    fn strongly_connected_components(&self) -> Vec<Vec<String>> {
        let mut visited = HashSet::new();
        let mut order = Vec::new();
        for node in &self.nodes {
            self.dfs_order(node, &mut visited, &mut order);
        }

        let reversed = self.reversed();
        let mut visited = HashSet::new();
        let mut sccs = Vec::new();
        for node in order.iter().rev() {
            if visited.contains(node) {
                continue;
            }
            let mut scc = Vec::new();
            reversed.dfs_collect(node, &mut visited, &mut scc);
            scc.sort();
            sccs.push(scc);
        }
        sccs
    }

    fn dfs_order(&self, node: &str, visited: &mut HashSet<String>, order: &mut Vec<String>) {
        if !visited.insert(node.to_string()) {
            return;
        }

        for neighbor in self.neighbors(node) {
            self.dfs_order(&neighbor, visited, order);
        }
        order.push(node.to_string());
    }

    fn dfs_collect(&self, node: &str, visited: &mut HashSet<String>, scc: &mut Vec<String>) {
        if !visited.insert(node.to_string()) {
            return;
        }

        scc.push(node.to_string());
        for neighbor in self.neighbors(node) {
            self.dfs_collect(&neighbor, visited, scc);
        }
    }

    fn reversed(&self) -> Self {
        let mut adjacency: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
        for node in &self.nodes {
            adjacency.entry(node.clone()).or_default();
        }

        for (source, targets) in &self.adjacency {
            for target in targets {
                adjacency
                    .entry(target.clone())
                    .or_default()
                    .insert(source.clone());
            }
        }

        Self {
            nodes: self.nodes.clone(),
            adjacency,
        }
    }

    fn max_bounded_depth(&self) -> usize {
        let fuel = self.nodes.len();
        let mut memo = HashMap::new();
        self.nodes
            .iter()
            .map(|node| self.bounded_depth_from(node, fuel, &mut memo))
            .max()
            .unwrap_or(0)
    }

    fn bounded_depth_from(
        &self,
        node: &str,
        fuel: usize,
        memo: &mut HashMap<(String, usize), usize>,
    ) -> usize {
        if fuel == 0 {
            return 0;
        }

        let key = (node.to_string(), fuel);
        if let Some(depth) = memo.get(&key) {
            return *depth;
        }

        let depth = self
            .neighbors(node)
            .iter()
            .map(|target| self.bounded_depth_from(target, fuel - 1, memo) + 1)
            .max()
            .unwrap_or(0);
        memo.insert(key, depth);
        depth
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_leading_imports_only() {
        let source = r#"
-- comment
import Formal.Arch.Graph
import Formal.Arch.Signature -- inline comment

def x := 1
import Should.Not.Appear
"#;

        let imports = parse_imports(source);

        assert_eq!(
            imports,
            vec![
                ParsedImport {
                    module: "Formal.Arch.Graph".to_string(),
                    evidence: "import Formal.Arch.Graph".to_string(),
                },
                ParsedImport {
                    module: "Formal.Arch.Signature".to_string(),
                    evidence: "import Formal.Arch.Signature".to_string(),
                },
            ]
        );
    }

    #[test]
    fn theorem_check_keeps_measured_witness_out_of_formal_proved_claims() {
        let document = air_fixture_document("good_extension.json");
        let report = build_theorem_precondition_check_report(&document, "good_extension.json");

        assert_eq!(
            report.schema_version,
            THEOREM_PRECONDITION_CHECK_REPORT_SCHEMA_VERSION
        );
        assert_eq!(report.registry.scope, "static theorem package v0");
        assert!(report.registry.packages.iter().any(|package| {
            package.theorem_refs
                == vec![
                    "SelectedStaticSplitExtension".to_string(),
                    "CoreEdgesPreserved".to_string(),
                    "DeclaredInterfaceFactorization".to_string(),
                    "NoNewForbiddenStaticEdge".to_string(),
                    "EmbeddingPolicyPreserved".to_string(),
                ]
        }));

        let boundary_check = report
            .checks
            .iter()
            .find(|check| check.claim_id == "claim-boundary-zero")
            .expect("boundary claim is checked");
        assert_eq!(
            boundary_check.resolved_claim_classification,
            "MEASURED_WITNESS"
        );
        assert_eq!(report.summary.formal_proved_claim_count, 0);
        assert!(report.summary.measured_witness_count > 0);
    }

    #[test]
    fn theorem_check_blocks_formal_claims_with_missing_preconditions() {
        let mut document = air_fixture_document("good_extension.json");
        document.claims.push(AirClaim {
            claim_id: "claim-static-split-blocked".to_string(),
            subject_ref: "extension.split".to_string(),
            predicate: "selected static split theorem package applies".to_string(),
            claim_level: "formal".to_string(),
            claim_classification: "proved".to_string(),
            measurement_boundary: "measuredZero".to_string(),
            theorem_refs: vec!["SelectedStaticSplitExtension".to_string()],
            evidence_refs: Vec::new(),
            required_assumptions: vec!["core edges are preserved".to_string()],
            coverage_assumptions: vec!["static graph coverage".to_string()],
            exactness_assumptions: vec!["AIR ids match Lean parameters".to_string()],
            missing_preconditions: vec![
                "declared interface factorization not discharged".to_string(),
            ],
            non_conclusions: vec!["runtime flatness is not concluded".to_string()],
        });

        let report = build_theorem_precondition_check_report(&document, "good_extension.json");
        let check = report
            .checks
            .iter()
            .find(|check| check.claim_id == "claim-static-split-blocked")
            .expect("formal split claim is checked");

        assert_eq!(check.resolved_claim_classification, "BLOCKED_FORMAL_CLAIM");
        assert_eq!(check.result, "warn");
        assert_eq!(report.summary.blocked_claim_count, 1);
        assert_eq!(report.summary.formal_proved_claim_count, 0);
    }

    #[test]
    fn theorem_check_accepts_registered_formal_claim_without_missing_preconditions() {
        let mut document = air_fixture_document("good_extension.json");
        document.claims.push(AirClaim {
            claim_id: "claim-static-split-proved".to_string(),
            subject_ref: "extension.split".to_string(),
            predicate: "selected static split theorem package applies".to_string(),
            claim_level: "formal".to_string(),
            claim_classification: "proved".to_string(),
            measurement_boundary: "measuredZero".to_string(),
            theorem_refs: vec![
                "SelectedStaticSplitExtension".to_string(),
                "CoreEdgesPreserved".to_string(),
                "DeclaredInterfaceFactorization".to_string(),
                "NoNewForbiddenStaticEdge".to_string(),
                "EmbeddingPolicyPreserved".to_string(),
            ],
            evidence_refs: Vec::new(),
            required_assumptions: vec!["core edges are preserved".to_string()],
            coverage_assumptions: vec!["static graph coverage".to_string()],
            exactness_assumptions: vec!["AIR ids match Lean parameters".to_string()],
            missing_preconditions: Vec::new(),
            non_conclusions: vec!["runtime flatness is not concluded".to_string()],
        });

        let report = build_theorem_precondition_check_report(&document, "good_extension.json");
        let check = report
            .checks
            .iter()
            .find(|check| check.claim_id == "claim-static-split-proved")
            .expect("formal split claim is checked");

        assert_eq!(check.resolved_claim_classification, "FORMAL_PROVED");
        assert_eq!(check.result, "pass");
        assert_eq!(report.summary.formal_proved_claim_count, 1);
    }

    #[test]
    fn extracts_minimal_fixture() {
        let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/minimal");
        let document = extract_sig0(&root).expect("fixture extracts");

        assert_eq!(document.schema_version, SCHEMA_VERSION);
        assert_eq!(document.component_kind, COMPONENT_KIND);
        assert!(document.components.iter().any(|c| c.id == "Formal"));
        assert!(document.components.iter().any(|c| c.id == "Formal.Arch.B"));
        assert!(!document.components.iter().any(|c| c.id == "lakefile"));
        assert!(document.edges.iter().any(|edge| {
            edge.source == "Formal.Arch.B"
                && edge.target == "Formal.Arch.A"
                && edge.kind == "import"
                && edge.evidence == "import Formal.Arch.A"
        }));
        assert_eq!(document.signature.has_cycle, 0);
        assert_eq!(document.signature.scc_max_size, 1);
        assert_eq!(document.signature.fanout_risk, 3);
        assert_eq!(document.signature.boundary_violation_count, 0);
        assert_eq!(document.signature.abstraction_violation_count, 0);
        assert!(
            document
                .metric_status
                .get("hasCycle")
                .expect("hasCycle status")
                .measured
        );
        assert!(
            !document
                .metric_status
                .get("boundaryViolationCount")
                .expect("boundary status")
                .measured
        );
        assert_eq!(
            document
                .metric_status
                .get("boundaryViolationCount")
                .expect("boundary status")
                .reason
                .as_deref(),
            Some("policy file not provided")
        );
        assert!(document.policy_violations.is_empty());
        assert!(document.runtime_edge_evidence.is_empty());
        assert!(document.runtime_dependency_graph.is_none());
    }

    #[test]
    fn projects_runtime_edge_evidence_to_runtime_dependency_graph() {
        let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/minimal");
        let runtime_edges = root.join("runtime_edges.json");
        let document =
            extract_sig0_with_runtime(&root, None, Some(&runtime_edges)).expect("fixture extracts");

        assert_eq!(document.runtime_edge_evidence.len(), 2);
        assert!(document.runtime_edge_evidence.iter().any(|edge| {
            edge.source == "Formal"
                && edge.target == "Formal.Arch.A"
                && edge.label == "rpc"
                && edge.failure_mode.as_deref() == Some("timeout")
                && edge.timeout_budget.as_deref() == Some("250ms")
                && edge.retry_policy.as_deref() == Some("bounded-retry")
                && edge.circuit_breaker_coverage.as_deref() == Some("covered")
                && edge.confidence.as_deref() == Some("fixture")
                && edge.evidence_location.path == "runtime/routes.json"
        }));

        let projection = document
            .runtime_dependency_graph
            .as_ref()
            .expect("runtime projection");
        assert_eq!(projection.projection_rule, RUNTIME_PROJECTION_RULE_VERSION);
        assert_eq!(projection.edge_kind, "runtime");
        assert_eq!(projection.edges.len(), 2);
        assert!(projection.edges.iter().any(|edge| {
            edge.source == "Formal"
                && edge.target == "Formal.Arch.A"
                && edge.kind == "runtime"
                && edge.evidence == "runtime edge evidence count: 1"
        }));
        assert!(
            document
                .metric_status
                .get("runtimePropagation")
                .expect("runtime status")
                .measured
        );

        let dataset = build_empirical_dataset(&document, &document, dataset_input(), "head")
            .expect("dataset builds");
        assert_eq!(
            dataset.signature_after.signature.runtime_propagation,
            Some(2)
        );
        assert_eq!(dataset.delta_signature_signed.runtime_propagation, Some(0));
        assert!(
            dataset
                .signature_after
                .metric_status
                .get("runtimePropagation")
                .expect("runtime dataset status")
                .measured
        );
    }

    #[test]
    fn builds_relation_complexity_observation_from_candidate_fixture() {
        let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/minimal");
        let observation = extract_relation_complexity_observation_from_file(
            &root.join("relation_complexity_candidates.json"),
        )
        .expect("relation complexity fixture extracts");

        assert_eq!(
            observation.schema_version,
            RELATION_COMPLEXITY_OBSERVATION_SCHEMA_VERSION
        );
        assert_eq!(
            observation.measurement_universe.rule_set_version.as_deref(),
            Some(RELATION_COMPLEXITY_RULE_SET_VERSION)
        );
        assert_eq!(observation.workflow.id, "checkout-payment");
        assert_eq!(observation.counts.constraints, 1);
        assert_eq!(observation.counts.compensations, 1);
        assert_eq!(observation.counts.projections, 0);
        assert_eq!(observation.counts.failure_transitions, 1);
        assert_eq!(observation.counts.idempotency_requirements, 0);
        assert_eq!(observation.relation_complexity, 3);
        assert_eq!(observation.evidence.len(), 2);
        assert!(observation.evidence.iter().any(|evidence| {
            evidence.id == "constraint-1"
                && evidence.path == "src/billing/checkout.rs"
                && evidence.symbol.as_deref() == Some("CheckoutWorkflow::validate")
                && evidence.line == Some(42)
                && evidence.tags == vec!["constraints".to_string()]
                && evidence.ownership == "application-owned"
                && evidence.review_status == "candidate"
        }));
        assert!(observation.evidence.iter().any(|evidence| {
            evidence.id == "compensate-timeout"
                && evidence.tags
                    == vec![
                        "compensations".to_string(),
                        "failureTransitions".to_string(),
                    ]
                && evidence.ownership == "application-configured"
        }));
        assert!(observation.excluded_evidence.iter().any(|evidence| {
            evidence.path == "src/framework/generated.rs"
                && evidence.reason == "ownership-not-counted:framework-generated"
        }));
        assert!(observation.excluded_evidence.iter().any(|evidence| {
            evidence.path == "src/billing/checkout.rs"
                && evidence.reason == "unsupported-tags:notATag"
        }));
        assert!(observation.excluded_evidence.iter().any(|evidence| {
            evidence.path == "src/billing/checkout_test.rs" && evidence.reason == "test-fixture"
        }));
    }

    #[test]
    fn relation_complexity_fixture_excludes_unsupported_framework() {
        let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/minimal");
        let observation = extract_relation_complexity_observation_from_file(
            &root.join("relation_complexity_unsupported_framework.json"),
        )
        .expect("relation complexity fixture extracts");

        assert_eq!(observation.relation_complexity, 0);
        assert!(observation.evidence.is_empty());
        assert!(observation.excluded_evidence.iter().any(|evidence| {
            evidence.path == "src/billing/unsupported.rs"
                && evidence.reason == "unsupported-framework:unsupported-framework"
        }));
    }

    #[test]
    fn applies_policy_with_measured_zero_counts() {
        let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/minimal");
        let policy = root.join("policy_measured_zero.json");
        let document = extract_sig0_with_policy(&root, Some(&policy)).expect("fixture extracts");

        assert_eq!(
            document.policies.policy_id.as_deref(),
            Some("minimal-measured-zero")
        );
        assert_eq!(document.policies.boundary_group_count, Some(2));
        assert_eq!(document.policies.abstraction_relation_count, Some(1));
        assert_eq!(document.signature.boundary_violation_count, 0);
        assert_eq!(document.signature.abstraction_violation_count, 0);
        assert!(
            document
                .metric_status
                .get("boundaryViolationCount")
                .expect("boundary status")
                .measured
        );
        assert_eq!(
            document
                .metric_status
                .get("boundaryViolationCount")
                .expect("boundary status")
                .source
                .as_deref(),
            Some("policy:minimal-measured-zero")
        );
        assert!(document.policy_violations.is_empty());
    }

    #[test]
    fn counts_policy_violations_by_unique_dependency_edge() {
        let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/minimal");
        let policy = root.join("policy_violations.json");
        let document = extract_sig0_with_policy(&root, Some(&policy)).expect("fixture extracts");

        assert_eq!(document.signature.boundary_violation_count, 2);
        assert_eq!(document.signature.abstraction_violation_count, 1);
        assert!(
            document
                .policy_violations
                .iter()
                .any(|violation| violation.axis == "boundaryViolationCount"
                    && violation.source == "Formal"
                    && violation.target == "Formal.Arch.A")
        );
        assert!(document.policy_violations.iter().any(|violation| {
            violation.axis == "abstractionViolationCount"
                && violation.source == "Formal"
                && violation.target == "Formal.Arch.B"
                && violation
                    .relation_ids
                    .as_ref()
                    .is_some_and(|relations| relations == &vec!["formal-api".to_string()])
        }));
    }

    #[test]
    fn validates_minimal_fixture_with_tooling_boundary_warnings() {
        let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/minimal");
        let policy = root.join("policy_measured_zero.json");
        let document = extract_sig0_with_policy(&root, Some(&policy)).expect("fixture extracts");

        let report =
            validate_component_universe_report(&document, ".lake/sig0.json", DEFAULT_UNIVERSE_MODE)
                .expect("report validates");

        assert_eq!(report.schema_version, VALIDATION_REPORT_SCHEMA_VERSION);
        assert_eq!(report.universe_mode, DEFAULT_UNIVERSE_MODE);
        assert_eq!(report.summary.component_count, 3);
        assert_eq!(report.summary.local_edge_count, 3);
        assert_eq!(report.summary.external_edge_count, 0);
        assert_eq!(report.summary.failed_check_count, 0);
        assert_eq!(report.summary.warning_check_count, 0);
        assert_eq!(report.summary.not_measured_check_count, 0);
        assert_eq!(report.summary.result, "pass");
        assert!(
            report
                .checks
                .iter()
                .any(|check| { check.id == "metric-status-complete" && check.result == "pass" })
        );
        assert!(
            report
                .checks
                .iter()
                .any(|check| { check.id == "boundary-policy-status" && check.result == "pass" })
        );
        assert!(report.warnings.is_empty());
    }

    #[test]
    fn validation_report_detects_duplicate_and_uncovered_local_target() {
        let mut metric_status = BTreeMap::new();
        metric_status.insert(
            "boundaryViolationCount".to_string(),
            unmeasured_status("policy file not provided".to_string()),
        );
        metric_status.insert(
            "abstractionViolationCount".to_string(),
            unmeasured_status("policy file not provided".to_string()),
        );
        let document = Sig0Document {
            schema_version: SCHEMA_VERSION.to_string(),
            root: ".".to_string(),
            component_kind: COMPONENT_KIND.to_string(),
            components: vec![
                Component {
                    id: "Formal".to_string(),
                    path: "Formal.lean".to_string(),
                },
                Component {
                    id: "Formal".to_string(),
                    path: "FormalDuplicate.lean".to_string(),
                },
            ],
            edges: vec![Edge {
                source: "Formal".to_string(),
                target: "Formal.Arch.Missing".to_string(),
                kind: "import".to_string(),
                evidence: "import Formal.Arch.Missing".to_string(),
            }],
            policies: Policies {
                boundary_allowed: Vec::new(),
                abstraction_allowed: Vec::new(),
                policy_id: None,
                schema_version: None,
                boundary_group_count: None,
                abstraction_relation_count: None,
            },
            signature: Signature {
                has_cycle: 0,
                scc_max_size: 1,
                max_depth: 1,
                fanout_risk: 1,
                boundary_violation_count: 0,
                abstraction_violation_count: 0,
            },
            metric_status,
            policy_violations: Vec::new(),
            runtime_edge_evidence: Vec::new(),
            runtime_dependency_graph: None,
        };

        let report =
            validate_component_universe_report(&document, ".lake/sig0.json", DEFAULT_UNIVERSE_MODE)
                .expect("report validates");

        assert_eq!(report.summary.result, "fail");
        assert_eq!(report.summary.failed_check_count, 3);
        assert!(report.checks.iter().any(|check| {
            check.id == "component-id-nodup" && check.result == "fail" && check.count == Some(1)
        }));
        assert!(report.checks.iter().any(|check| {
            check.id == "edge-endpoint-resolved" && check.result == "fail" && check.count == Some(1)
        }));
        assert!(report.checks.iter().any(|check| {
            check.id == "edge-closure-local" && check.result == "fail" && check.count == Some(1)
        }));
    }

    #[test]
    fn validation_report_warns_about_external_targets_in_local_only_mode() {
        let mut document = extract_sig0(
            Path::new(env!("CARGO_MANIFEST_DIR"))
                .join("tests/fixtures/minimal")
                .as_path(),
        )
        .expect("fixture extracts");
        document.edges.push(Edge {
            source: "Formal".to_string(),
            target: "Mathlib.Data.List.Basic".to_string(),
            kind: "import".to_string(),
            evidence: "import Mathlib.Data.List.Basic".to_string(),
        });

        let report =
            validate_component_universe_report(&document, ".lake/sig0.json", DEFAULT_UNIVERSE_MODE)
                .expect("report validates");

        assert_eq!(report.summary.external_edge_count, 1);
        assert!(report.checks.iter().any(|check| {
            check.id == "external-edge-targets" && check.result == "warn" && check.count == Some(1)
        }));
        assert_eq!(
            report.warnings,
            vec!["local-only universe excludes external or synthetic import targets".to_string()]
        );
    }

    #[test]
    fn builds_empirical_dataset_with_comparable_and_unmeasured_deltas() {
        let before = sig0_document_for_edges(
            vec![
                ("A", "A.lean"),
                ("B", "B.lean"),
                ("C", "C.lean"),
                ("D", "D.lean"),
            ],
            vec![("A", "B")],
        );
        let after = sig0_document_for_edges(
            vec![
                ("A", "A.lean"),
                ("B", "B.lean"),
                ("C", "C.lean"),
                ("D", "D.lean"),
            ],
            vec![("A", "B"), ("A", "C"), ("C", "D")],
        );

        let dataset = build_empirical_dataset(&before, &after, dataset_input(), "head")
            .expect("dataset builds");

        assert_eq!(dataset.schema_version, EMPIRICAL_DATASET_SCHEMA_VERSION);
        assert_eq!(dataset.signature_before.commit.sha, "base-sha");
        assert_eq!(dataset.signature_after.commit.role, "head");
        assert_eq!(dataset.delta_signature_signed.fanout_risk, Some(2));
        assert_eq!(dataset.delta_signature_signed.max_fanout, Some(1));
        assert_eq!(dataset.delta_signature_signed.reachable_cone_size, Some(2));
        assert_eq!(
            dataset.delta_signature_signed.boundary_violation_count,
            None
        );
        assert_eq!(dataset.signature_after.signature.weighted_scc_risk, None);
        assert!(
            !dataset
                .signature_after
                .metric_status
                .get("weightedSccRisk")
                .expect("weighted status")
                .measured
        );
        assert_eq!(dataset.signature_after.signature.runtime_propagation, None);
        assert!(
            !dataset
                .signature_after
                .metric_status
                .get("runtimePropagation")
                .expect("runtime status")
                .measured
        );

        let fanout_status = dataset
            .metric_delta_status
            .get("fanoutRisk")
            .expect("fanout delta status");
        assert!(fanout_status.comparable);
        assert!(fanout_status.before_measured);
        assert!(fanout_status.after_measured);

        let boundary_status = dataset
            .metric_delta_status
            .get("boundaryViolationCount")
            .expect("boundary delta status");
        assert!(!boundary_status.comparable);
        assert!(!boundary_status.before_measured);
        assert!(!boundary_status.after_measured);
        assert!(
            boundary_status
                .reason
                .contains("policy file not provided before")
                || boundary_status.reason.contains("policy file not provided")
        );
    }

    #[test]
    fn dataset_merge_role_uses_merge_commit() {
        let document = sig0_document_for_edges(vec![("A", "A.lean")], Vec::new());
        let dataset = build_empirical_dataset(&document, &document, dataset_input(), "merge")
            .expect("dataset builds");

        assert_eq!(dataset.signature_after.commit.sha, "merge-sha");
        assert_eq!(
            dataset.analysis_metadata.signature_after_commit_role,
            "merge"
        );
    }

    #[test]
    fn detects_cycle_fixture_metrics() {
        let components = vec![
            Component {
                id: "A".to_string(),
                path: "A.lean".to_string(),
            },
            Component {
                id: "B".to_string(),
                path: "B.lean".to_string(),
            },
        ];
        let edges = vec![
            Edge {
                source: "A".to_string(),
                target: "B".to_string(),
                kind: "import".to_string(),
                evidence: "import B".to_string(),
            },
            Edge {
                source: "B".to_string(),
                target: "A".to_string(),
                kind: "import".to_string(),
                evidence: "import A".to_string(),
            },
        ];

        let signature = compute_signature(&components, &edges);

        assert_eq!(signature.has_cycle, 1);
        assert_eq!(signature.scc_max_size, 2);
        assert_eq!(signature.fanout_risk, 2);
    }

    fn sig0_document_for_edges(
        components: Vec<(&str, &str)>,
        edge_pairs: Vec<(&str, &str)>,
    ) -> Sig0Document {
        let components: Vec<Component> = components
            .into_iter()
            .map(|(id, path)| Component {
                id: id.to_string(),
                path: path.to_string(),
            })
            .collect();
        let edges: Vec<Edge> = edge_pairs
            .into_iter()
            .map(|(source, target)| Edge {
                source: source.to_string(),
                target: target.to_string(),
                kind: "import".to_string(),
                evidence: format!("import {target}"),
            })
            .collect();
        let signature = compute_signature(&components, &edges);
        let mut metric_status = BTreeMap::new();
        for axis in ["hasCycle", "sccMaxSize", "maxDepth", "fanoutRisk"] {
            metric_status.insert(axis.to_string(), measured_status("archsig:import-graph"));
        }
        metric_status.insert(
            "boundaryViolationCount".to_string(),
            unmeasured_status("policy file not provided".to_string()),
        );
        metric_status.insert(
            "abstractionViolationCount".to_string(),
            unmeasured_status("policy file not provided".to_string()),
        );

        Sig0Document {
            schema_version: SCHEMA_VERSION.to_string(),
            root: ".".to_string(),
            component_kind: COMPONENT_KIND.to_string(),
            components,
            edges,
            policies: Policies {
                boundary_allowed: Vec::new(),
                abstraction_allowed: Vec::new(),
                policy_id: None,
                schema_version: None,
                boundary_group_count: None,
                abstraction_relation_count: None,
            },
            signature,
            metric_status,
            policy_violations: Vec::new(),
            runtime_edge_evidence: Vec::new(),
            runtime_dependency_graph: None,
        }
    }

    fn air_fixture_document(fixture: &str) -> AirDocumentV0 {
        let path = Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("tests/fixtures/air")
            .join(fixture);
        let contents = std::fs::read_to_string(&path).expect("AIR fixture is readable");
        serde_json::from_str(&contents).expect("AIR fixture parses")
    }

    fn dataset_input() -> EmpiricalDatasetInput {
        EmpiricalDatasetInput {
            repository: RepositoryRef {
                owner: "example".to_string(),
                name: "service".to_string(),
                default_branch: "main".to_string(),
            },
            pull_request: PullRequestRef {
                number: 42,
                author: "alice".to_string(),
                created_at: "2026-04-01T00:00:00Z".to_string(),
                merged_at: Some("2026-04-02T00:00:00Z".to_string()),
                base_commit: "base-sha".to_string(),
                head_commit: "head-sha".to_string(),
                merge_commit: Some("merge-sha".to_string()),
                labels: vec!["feature".to_string()],
                is_bot_generated: false,
            },
            pr_metrics: PullRequestMetrics {
                changed_files: 2,
                changed_lines_added: 20,
                changed_lines_deleted: 5,
                changed_components: vec!["A".to_string(), "C".to_string()],
                review_comment_count: 1,
                review_thread_count: 1,
                review_round_count: 1,
                first_review_latency_hours: Some(2.0),
                approval_latency_hours: Some(6.0),
                merge_latency_hours: Some(12.0),
            },
            issue_incident_links: Vec::new(),
            analysis_metadata: AnalysisMetadata::default(),
        }
    }
}
