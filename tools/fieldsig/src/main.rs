use std::error::Error;
use std::fs::File;
use std::io::{self, Write};
use std::path::{Path, PathBuf};
use std::process::ExitCode;

use clap::{Parser, Subcommand};
use fieldsig::{
    AatObservableBundleV0, AatObservableBundleValidationReportV0, AiProposalGovernanceV0,
    AiProposalGovernanceValidationReportV0, AirDocumentInput, AirDocumentV0, AirValidationReport,
    ArchMapDocumentV0, ArchMapSourceInventoryInput, ArchMapSourceInventoryV0,
    ArchMapValidationReportV0, ArchitectureDynamicsMetricsReportV0,
    ArchitectureDynamicsMetricsReportValidationReportV0, ArchitectureFieldSnapshotV0,
    ArchitectureFieldSnapshotValidationReportV0, ArchitecturePolicyV0,
    ArchitecturePolicyValidationReportV0, ArtifactDescriptorV0,
    ArtifactDescriptorValidationReportV0, CalibrationReviewRecordV0,
    ComponentUniverseValidationReport, ConsequenceEnvelopeReportV0,
    ConsequenceEnvelopeValidationReportV0, CustomRulePluginRegistryV0,
    CustomRulePluginRegistryValidationReportV0, DEFAULT_UNIVERSE_MODE,
    DetectableValuesReportedAxesCatalogV0, DriftLedgerAggregationWindowV0,
    DynamicsMeasurementContractV0, DynamicsMeasurementContractValidationReportV0,
    EmpiricalDatasetInput, FeatureExtensionReportV0, FieldSigRunManifestV0,
    FieldSigRunManifestValidationReportV0, ForecastCalibrationHookV0,
    ForecastCalibrationHookValidationReportV0, ForecastConeSkeletonV0,
    ForecastConeSkeletonValidationReportV0, FrameworkAdapterEvidenceV0, HypothesisRefreshCycleV0,
    IncidentCorrelationMonitorV0, IntentArchMapAlignmentV0,
    IntentArchMapAlignmentValidationReportV0, IntentCalibrationRecordV0,
    IntentCalibrationValidationReportV0, IntentMapV0, IntentMapValidationReportV0,
    LawPolicyTemplateRegistryV0, LawPolicyTemplateRegistryValidationReportV0, LawViolationReportV0,
    MeasurementUnitRegistryV0, MeasurementUnitRegistryValidationReportV0, NoSolutionCertificateV0,
    NoSolutionCertificateValidationReportV0, OperationProposalLogV0,
    OperationProposalLogValidationReportV0, OperationSupportEstimateV0,
    OperationSupportEstimateValidationReportV0, OrganizationPolicyV0,
    OrganizationPolicyValidationReportV0, OwnershipBoundaryMonitorV0, PolicyDecisionReportV0,
    PrForceReportV0, PrForceReportValidationReportV0, PrQualityAnalysisReportV0,
    PrQualityAnalysisValidationReportV0, RepairAdoptionRecordV0, RepairRuleRegistryV0,
    RepairRuleRegistryValidationReportV0, ReportArtifactRetentionManifestV0,
    ReportArtifactRetentionValidationReportV0, ReportOutcomeDailyLedgerInput,
    RepositoryRevisionRef, RiskDispositionV0, ScanMetadata, SchemaCompatibilityCheckReportV0,
    SchemaVersionCatalogV0, SftReviewSummaryV0, SftReviewSummaryValidationReportV0, Sig0Document,
    SignatureDiffReportV0, SignatureSnapshotStoreRecordV0, SignatureTrajectoryReportV0,
    SignatureTrajectoryReportValidationReportV0, SnapshotRecordInput, SnapshotRepositoryRef,
    SoftwareFieldMeasurementV0, SoftwareFieldMeasurementValidationReportV0,
    SynthesisConstraintArtifactV0, SynthesisConstraintValidationReportV0, TeamThresholdPolicyV0,
    TheoremPreconditionCheckReportV0, apply_architecture_policy_to_sig0,
    attach_framework_adapter_evidence, build_ai_proposal_governance_from_descriptor,
    build_air_document, build_air_from_archmap, build_artifact_descriptor_from_ai_proposal_json,
    build_artifact_descriptor_from_github_issue_json, build_artifact_descriptor_from_markdown,
    build_baseline_suppression_report, build_consequence_envelope_from_forecast_cone,
    build_empirical_dataset, build_feature_extension_dataset_from_files,
    build_feature_extension_report, build_forecast_cone_skeleton_from_operation_support,
    build_law_violation_report, build_operation_support_estimate_from_archmap,
    build_operation_support_estimate_from_archsig_analysis_packet,
    build_operation_support_estimate_from_descriptor,
    build_operation_support_estimate_from_intent_alignment,
    build_outcome_linkage_dataset_from_files, build_policy_decision_report,
    build_pr_history_dataset_from_github_files, build_pr_metadata_from_github_files,
    build_report_outcome_daily_ledger_from_files, build_schema_compatibility_check_report,
    build_sft_review_summary_from_consequence_envelope, build_signature_diff_report,
    build_signature_snapshot_record, build_theorem_precondition_check_report, extract_python_sig0,
    extract_relation_complexity_observation_from_file, extract_sig0_with_runtime,
    read_architecture_policy, render_pr_comment_markdown, static_aat_observable_bundle,
    static_ai_proposal_governance, static_architecture_dynamics_metrics_report,
    static_architecture_field_snapshot, static_artifact_descriptor,
    static_calibration_review_record, static_consequence_envelope_report,
    static_custom_rule_plugin_registry, static_detectable_values_reported_axes_catalog,
    static_dynamics_measurement_contract, static_fieldsig_run_manifest,
    static_forecast_calibration_hook, static_forecast_cone_skeleton,
    static_hypothesis_refresh_cycle, static_incident_correlation_monitor,
    static_intent_archmap_alignment, static_intent_calibration_record, static_intent_map,
    static_law_policy_template_registry, static_measurement_unit_registry,
    static_no_solution_certificate, static_operation_proposal_log,
    static_operation_support_estimate, static_organization_policy,
    static_ownership_boundary_monitor, static_pr_force_report, static_pr_quality_analysis_report,
    static_repair_adoption_record, static_repair_rule_registry,
    static_report_artifact_retention_manifest, static_schema_version_catalog,
    static_sft_review_summary, static_signature_trajectory_report,
    static_software_field_measurement, static_synthesis_constraint_artifact,
    static_team_threshold_policy, validate_aat_observable_bundle, validate_ai_proposal_governance,
    validate_air_document_report, validate_architecture_dynamics_metrics_report,
    validate_architecture_field_snapshot, validate_architecture_policy_report,
    validate_archmap_report, validate_artifact_descriptor_report,
    validate_component_universe_report, validate_consequence_envelope_report,
    validate_custom_rule_plugin_registry_report, validate_dynamics_measurement_contract_report,
    validate_fieldsig_run_manifest, validate_forecast_calibration_hook,
    validate_forecast_cone_skeleton, validate_intent_archmap_alignment,
    validate_intent_calibration_record, validate_intent_map,
    validate_law_policy_template_registry_report, validate_measurement_unit_registry_report,
    validate_no_solution_certificate_report, validate_operation_proposal_log,
    validate_operation_support_estimate, validate_organization_policy_report,
    validate_pr_force_report, validate_pr_quality_analysis_report,
    validate_repair_rule_registry_report, validate_report_artifact_retention_report,
    validate_sft_review_summary, validate_signature_trajectory_report,
    validate_software_field_measurement, validate_synthesis_constraint_artifact_report,
};

#[derive(Debug, Parser)]
#[command(
    version,
    about = "Build FieldSig software evolution measurement artifacts"
)]
struct Args {
    #[command(subcommand)]
    command: Option<Command>,

    /// Repository root to scan.
    #[arg(long, default_value = ".")]
    root: PathBuf,

    /// Output JSON path. If omitted, JSON is written to stdout.
    #[arg(long)]
    out: Option<PathBuf>,

    /// Optional boundary / abstraction policy JSON file.
    #[arg(long)]
    policy: Option<PathBuf>,

    /// Optional runtime edge evidence JSON file.
    #[arg(long = "runtime-edges")]
    runtime_edges: Option<PathBuf>,

    /// Source language to scan.
    #[arg(long, default_value = "lean", value_parser = ["lean", "python"])]
    language: String,

    /// Python source root relative to --root. Repeat for multiple roots.
    #[arg(long = "source-root")]
    source_roots: Vec<PathBuf>,

    /// Python package root relative to --root. Repeat for multiple roots.
    #[arg(long = "package-root")]
    package_roots: Vec<PathBuf>,
}

#[derive(Debug, Subcommand)]
enum Command {
    /// Validate an existing ArchSig JSON document.
    Validate {
        /// Input ArchSig JSON path.
        #[arg(long)]
        input: PathBuf,

        /// Output validation report JSON path. If omitted, JSON is written to stdout.
        #[arg(long)]
        out: Option<PathBuf>,

        /// Universe mode for edge closure checks.
        #[arg(long, default_value = DEFAULT_UNIVERSE_MODE)]
        universe_mode: String,
    },

    /// Build an empirical dataset v0 record from before / after signatures and PR metadata.
    Dataset {
        /// Input ArchSig JSON for the PR base commit.
        #[arg(long)]
        before: PathBuf,

        /// Input ArchSig JSON for the PR head or merge commit.
        #[arg(long)]
        after: PathBuf,

        /// PR metadata JSON path.
        #[arg(long = "pr-metadata")]
        pr_metadata: PathBuf,

        /// Commit role used for the after signature: head or merge.
        #[arg(long, default_value = "head")]
        after_role: String,

        /// Output dataset JSON path. If omitted, JSON is written to stdout.
        #[arg(long)]
        out: Option<PathBuf>,
    },

    /// Build dataset input PR metadata from GitHub API JSON.
    PrMetadata {
        /// GitHub REST pull request JSON path.
        #[arg(long = "pull-request")]
        pull_request: PathBuf,

        /// GitHub pull request files JSON path.
        #[arg(long)]
        files: PathBuf,

        /// Optional GitHub pull request reviews JSON path.
        #[arg(long)]
        reviews: Option<PathBuf>,

        /// Optional GitHub GraphQL reviewThreads JSON path.
        #[arg(long = "review-threads")]
        review_threads: Option<PathBuf>,

        /// Output PR metadata JSON path. If omitted, JSON is written to stdout.
        #[arg(long)]
        out: Option<PathBuf>,
    },

    /// Build a PR history dataset v0 record from GitHub API JSON and artifact refs.
    PrHistoryDataset {
        /// GitHub REST pull request JSON path.
        #[arg(long = "pull-request")]
        pull_request: PathBuf,

        /// GitHub pull request files JSON path.
        #[arg(long)]
        files: PathBuf,

        /// Optional GitHub pull request reviews JSON path.
        #[arg(long)]
        reviews: Option<PathBuf>,

        /// Optional GitHub GraphQL reviewThreads JSON path.
        #[arg(long = "review-threads")]
        review_threads: Option<PathBuf>,

        /// Signature artifact path. Optional role prefix can be used, e.g. base=before.json.
        #[arg(long = "signature-artifact")]
        signature_artifact: Vec<String>,

        /// Feature Extension Report artifact path.
        #[arg(long = "feature-report-artifact")]
        feature_report_artifact: Vec<String>,

        /// Output PR history dataset JSON path. If omitted, JSON is written to stdout.
        #[arg(long)]
        out: Option<PathBuf>,
    },

    /// Build a feature extension dataset v0 by joining PR history and Feature Extension Reports.
    FeatureExtensionDataset {
        /// Input PR history dataset JSON path.
        #[arg(long = "pr-history")]
        pr_history: PathBuf,

        /// Feature Extension Report JSON path. Repeat for multiple PR records.
        #[arg(long = "feature-report")]
        feature_report: Vec<PathBuf>,

        /// Optional theorem precondition check report JSON path. Repeat for multiple reports.
        #[arg(long = "theorem-check-report")]
        theorem_check_report: Vec<PathBuf>,

        /// Output feature extension dataset JSON path. If omitted, JSON is written to stdout.
        #[arg(long)]
        out: Option<PathBuf>,
    },

    /// Build an outcome linkage dataset v0 by joining feature dataset records and outcome observations.
    OutcomeLinkageDataset {
        /// Input feature extension dataset JSON path.
        #[arg(long = "feature-dataset")]
        feature_dataset: PathBuf,

        /// Outcome observation input JSON path.
        #[arg(long)]
        outcome: PathBuf,

        /// Output outcome linkage dataset JSON path. If omitted, JSON is written to stdout.
        #[arg(long)]
        out: Option<PathBuf>,
    },

    /// Build a B10 report outcome daily ledger from outcome and drift artifacts.
    ReportOutcomeDailyLedger {
        /// Input outcome linkage dataset JSON path.
        #[arg(long = "outcome-linkage")]
        outcome_linkage: PathBuf,

        /// Input Architecture Drift Ledger JSON path.
        #[arg(long = "drift-ledger")]
        drift_ledger: PathBuf,

        /// Ledger id for the generated daily artifact.
        #[arg(
            long = "ledger-id",
            default_value = "fixture-b10-report-outcome-daily-ledger"
        )]
        ledger_id: String,

        /// Generation timestamp.
        #[arg(long = "generated-at")]
        generated_at: String,

        /// Aggregation window start timestamp.
        #[arg(long = "window-start")]
        window_start: Option<String>,

        /// Aggregation window end timestamp.
        #[arg(long = "window-end")]
        window_end: Option<String>,

        /// Aggregation window kind.
        #[arg(long = "window-kind", default_value = "daily")]
        window_kind: String,

        /// Retention period in days for source reports.
        #[arg(long = "retention-days", default_value_t = 90)]
        retention_days: usize,

        /// Output report outcome daily ledger JSON path. If omitted, JSON is written to stdout.
        #[arg(long)]
        out: Option<PathBuf>,
    },

    /// Emit a B10 false positive / false negative calibration review record.
    CalibrationReviewRecord {
        /// Output calibration review record JSON path. If omitted, JSON is written to stdout.
        #[arg(long)]
        out: Option<PathBuf>,
    },

    /// Emit a B10 team-specific threshold tuning policy.
    TeamThresholdPolicy {
        /// Output team threshold policy JSON path. If omitted, JSON is written to stdout.
        #[arg(long)]
        out: Option<PathBuf>,
    },

    /// Emit a B10 ownership / boundary erosion monitoring artifact.
    OwnershipBoundaryMonitor {
        /// Output ownership boundary monitor JSON path. If omitted, JSON is written to stdout.
        #[arg(long)]
        out: Option<PathBuf>,
    },

    /// Emit a B10 repair suggestion adoption tracking record.
    RepairAdoptionRecord {
        /// Output repair adoption record JSON path. If omitted, JSON is written to stdout.
        #[arg(long)]
        out: Option<PathBuf>,
    },

    /// Emit a B10 incident / rollback / MTTR correlation monitor artifact.
    IncidentCorrelationMonitor {
        /// Output incident correlation monitor JSON path. If omitted, JSON is written to stdout.
        #[arg(long)]
        out: Option<PathBuf>,
    },

    /// Emit a B10 empirical hypothesis refresh cycle artifact.
    HypothesisRefreshCycle {
        /// Output hypothesis refresh cycle JSON path. If omitted, JSON is written to stdout.
        #[arg(long)]
        out: Option<PathBuf>,
    },

    /// Build a workflow-level RelationComplexityObservation from candidate evidence.
    RelationComplexity {
        /// Input relation complexity candidate JSON path.
        #[arg(long)]
        input: PathBuf,

        /// Output observation JSON path. If omitted, JSON is written to stdout.
        #[arg(long)]
        out: Option<PathBuf>,
    },

    /// Build a repository-revision Signature snapshot store record.
    Snapshot {
        /// Input ArchSig JSON path.
        #[arg(long)]
        input: PathBuf,

        /// Optional ComponentUniverse validation report JSON path.
        #[arg(long = "validation-report")]
        validation_report: Option<PathBuf>,

        /// Repository owner.
        #[arg(long = "repo-owner")]
        repo_owner: String,

        /// Repository name.
        #[arg(long = "repo-name")]
        repo_name: String,

        /// Repository default branch.
        #[arg(long = "default-branch", default_value = "main")]
        default_branch: String,

        /// Optional repository remote URL.
        #[arg(long = "remote-url")]
        remote_url: Option<String>,

        /// Measured revision SHA.
        #[arg(long = "revision-sha")]
        revision_sha: String,

        /// Optional measured revision ref.
        #[arg(long = "revision-ref")]
        revision_ref: Option<String>,

        /// Optional measured branch.
        #[arg(long = "revision-branch")]
        revision_branch: Option<String>,

        /// Optional measured commit timestamp.
        #[arg(long = "committed-at")]
        committed_at: Option<String>,

        /// Optional parent SHA. Repeat for merge commits.
        #[arg(long = "parent-sha")]
        parent_sha: Vec<String>,

        /// Scan timestamp.
        #[arg(long = "scanned-at")]
        scanned_at: String,

        /// Optional scanner id.
        #[arg(long = "scanner-id")]
        scanner_id: Option<String>,

        /// Scan trigger.
        #[arg(long, default_value = "manual")]
        trigger: String,

        /// Optional scan root recorded in the snapshot.
        #[arg(long = "scan-root")]
        scan_root: Option<String>,

        /// Optional policy version.
        #[arg(long = "policy-version")]
        policy_version: Option<String>,

        /// Optional policy source path.
        #[arg(long = "policy-path")]
        policy_path: Option<String>,

        /// Optional policy content hash.
        #[arg(long = "policy-content-hash")]
        policy_content_hash: Option<String>,

        /// Optional extractor output artifact path.
        #[arg(long = "extractor-output-path")]
        extractor_output_path: Option<String>,

        /// Optional snapshot tag. Repeat for multiple tags.
        #[arg(long)]
        tag: Vec<String>,

        /// Optional analysis note.
        #[arg(long)]
        notes: Option<String>,

        /// Output snapshot JSON path. If omitted, JSON is written to stdout.
        #[arg(long)]
        out: Option<PathBuf>,
    },

    /// Diff two Signature snapshot store records.
    #[command(alias = "diff")]
    SignatureDiff {
        /// Before snapshot store record JSON path.
        #[arg(long = "before-snapshot", alias = "before")]
        before_snapshot: PathBuf,

        /// After snapshot store record JSON path.
        #[arg(long = "after-snapshot", alias = "after")]
        after_snapshot: PathBuf,

        /// Optional before ArchSig JSON for component / edge evidence diff.
        #[arg(long = "before-sig0")]
        before_sig0: Option<PathBuf>,

        /// Optional after ArchSig JSON for component / edge evidence diff.
        #[arg(long = "after-sig0")]
        after_sig0: Option<PathBuf>,

        /// Optional PR metadata JSON for attribution. Repeat for multiple PRs.
        #[arg(long = "pr-metadata")]
        pr_metadata: Vec<PathBuf>,

        /// Output diff report JSON path. If omitted, JSON is written to stdout.
        #[arg(long)]
        out: Option<PathBuf>,
    },

    /// Build an AIR v0 document from Signature artifacts.
    Air {
        /// Input ArchSig Sig0 JSON path.
        #[arg(long)]
        sig0: PathBuf,

        /// Optional ComponentUniverse validation report JSON path.
        #[arg(long)]
        validation: Option<PathBuf>,

        /// Optional Signature diff report JSON path.
        #[arg(long)]
        diff: Option<PathBuf>,

        /// Optional PR metadata JSON path.
        #[arg(long = "pr-metadata")]
        pr_metadata: Option<PathBuf>,

        /// Optional law / policy JSON path recorded as AIR policy artifact.
        #[arg(long = "law-policy")]
        law_policy: Option<PathBuf>,

        /// Optional framework adapter evidence JSON path. Repeat for multiple adapters.
        #[arg(long = "framework-adapter")]
        framework_adapters: Vec<PathBuf>,

        /// Output AIR JSON path. If omitted, JSON is written to stdout.
        #[arg(long)]
        out: Option<PathBuf>,
    },

    /// Validate a supplied ArchMap v0 JSON artifact.
    Archmap {
        /// Input ArchMap JSON path.
        #[arg(long)]
        input: PathBuf,

        /// Optional Sig0 JSON path used for static / semantic conflict checks.
        #[arg(long)]
        sig0: Option<PathBuf>,

        /// Output ArchMap validation report JSON path. If omitted, JSON is written to stdout.
        #[arg(long)]
        out: Option<PathBuf>,
    },

    /// Emit a bounded external-agent protocol for generating ArchMap JSON.
    ArchmapGenerate {
        /// Source inventory JSON path used by the external agent.
        #[arg(long = "source-inventory")]
        source_inventory: PathBuf,

        /// Prompt pack path retained as provenance.
        #[arg(long = "prompt-pack")]
        prompt_pack: PathBuf,

        /// Model provider name retained as provenance.
        #[arg(long, default_value = "external-agent")]
        provider: String,

        /// Model id retained as provenance.
        #[arg(long = "model-id", default_value = "unspecified")]
        model_id: String,

        /// Output generation protocol JSON path. If omitted, JSON is written to stdout.
        #[arg(long)]
        out: Option<PathBuf>,
    },

    /// Project a supplied ArchMap v0 JSON artifact into SFT operation-support input.
    ArchmapSftInput {
        /// Input ArchMap JSON path.
        #[arg(long)]
        archmap: PathBuf,

        /// Output operation-support-estimate-v0 JSON path. If omitted, JSON is written to stdout.
        #[arg(long)]
        out: Option<PathBuf>,
    },

    /// Project an ArchSig analysis packet into SFT operation-support input.
    ArchsigAnalysisSftInput {
        /// Input archsig-analysis-packet/v1 or archsig-analysis-packet-v0 JSON path.
        #[arg(long = "analysis-packet")]
        analysis_packet: PathBuf,

        /// Output operation-support-estimate-v0 JSON path. If omitted, JSON is written to stdout.
        #[arg(long)]
        out: Option<PathBuf>,
    },

    /// Project a supplied ArchMap v0 JSON artifact into AIR v0.
    AirFromArchmap {
        /// Input ArchMap JSON path.
        #[arg(long)]
        archmap: PathBuf,

        /// Optional Sig0 JSON path used to preserve static / semantic conflicts.
        #[arg(long)]
        sig0: Option<PathBuf>,

        /// Optional ArchMap validation report path recorded by callers in workflow artifacts.
        #[arg(long)]
        validation: Option<PathBuf>,

        /// Output AIR JSON path. If omitted, JSON is written to stdout.
        #[arg(long)]
        out: Option<PathBuf>,
    },

    /// Validate an AIR v0 document.
    ValidateAir {
        /// Input AIR JSON path.
        #[arg(long)]
        input: PathBuf,

        /// Output AIR validation report JSON path. If omitted, JSON is written to stdout.
        #[arg(long)]
        out: Option<PathBuf>,

        /// Treat measured claims without evidence refs as failures instead of warnings.
        #[arg(long)]
        strict_measured_evidence: bool,
    },

    /// Build a static Feature Extension Report v0 from an AIR v0 document.
    FeatureReport {
        /// Input AIR JSON path.
        #[arg(long)]
        air: PathBuf,

        /// Output Feature Extension Report JSON path. If omitted, JSON is written to stdout.
        #[arg(long)]
        out: Option<PathBuf>,
    },

    /// Check theorem package preconditions for AIR v0 claims.
    TheoremCheck {
        /// Input AIR JSON path.
        #[arg(long)]
        air: PathBuf,

        /// Output theorem precondition check report JSON path. If omitted, JSON is written to stdout.
        #[arg(long)]
        out: Option<PathBuf>,
    },

    /// Validate a repair rule registry. If input is omitted, validate the static registry.
    RepairRegistry {
        /// Optional repair rule registry JSON path.
        #[arg(long)]
        input: Option<PathBuf>,

        /// Output repair rule registry validation report JSON path. If omitted, JSON is written to stdout.
        #[arg(long)]
        out: Option<PathBuf>,
    },

    /// Validate a synthesis constraint artifact. If input is omitted, validate the static artifact.
    SynthesisConstraints {
        /// Optional synthesis constraint artifact JSON path.
        #[arg(long)]
        input: Option<PathBuf>,

        /// Output synthesis constraint validation report JSON path. If omitted, JSON is written to stdout.
        #[arg(long)]
        out: Option<PathBuf>,
    },

    /// Validate a no-solution certificate. If input is omitted, validate the static certificate.
    NoSolutionCertificate {
        /// Optional no-solution certificate JSON path.
        #[arg(long)]
        input: Option<PathBuf>,

        /// Output no-solution certificate validation report JSON path. If omitted, JSON is written to stdout.
        #[arg(long)]
        out: Option<PathBuf>,
    },

    /// Validate an organization policy. If input is omitted, validate the static B7 policy.
    OrganizationPolicy {
        /// Optional organization policy JSON path.
        #[arg(long)]
        input: Option<PathBuf>,

        /// Output organization policy validation report JSON path. If omitted, JSON is written to stdout.
        #[arg(long)]
        out: Option<PathBuf>,
    },

    /// Validate a project-local architecture-policy v0 artifact.
    ArchitecturePolicy {
        /// Architecture policy JSON path.
        #[arg(long)]
        input: PathBuf,

        /// Output architecture policy validation report JSON path. If omitted, JSON is written to stdout.
        #[arg(long)]
        out: Option<PathBuf>,
    },

    /// Evaluate architecture-policy laws against a Sig0 artifact.
    LawViolationReport {
        /// Sig0 JSON path.
        #[arg(long)]
        sig0: PathBuf,

        /// Architecture policy JSON path.
        #[arg(long)]
        policy: PathBuf,

        /// Output law violation report JSON path. If omitted, JSON is written to stdout.
        #[arg(long)]
        out: Option<PathBuf>,
    },

    /// Validate a law policy template registry. If input is omitted, validate the static B8 registry.
    LawPolicyTemplates {
        /// Optional law policy template registry JSON path.
        #[arg(long)]
        input: Option<PathBuf>,

        /// Output law policy template registry validation report JSON path. If omitted, JSON is written to stdout.
        #[arg(long)]
        out: Option<PathBuf>,
    },

    /// Validate a custom rule plugin registry. If input is omitted, validate the static B8 registry.
    CustomRulePlugins {
        /// Optional custom rule plugin registry JSON path.
        #[arg(long)]
        input: Option<PathBuf>,

        /// Output custom rule plugin registry validation report JSON path. If omitted, JSON is written to stdout.
        #[arg(long)]
        out: Option<PathBuf>,
    },

    /// Validate a measurement unit registry. If input is omitted, validate the static B8 registry.
    MeasurementUnits {
        /// Optional measurement unit registry JSON path.
        #[arg(long)]
        input: Option<PathBuf>,

        /// Output measurement unit registry validation report JSON path. If omitted, JSON is written to stdout.
        #[arg(long)]
        out: Option<PathBuf>,
    },

    /// Validate the Architecture Dynamics common measurement contract.
    DynamicsMeasurements {
        /// Optional dynamics measurement contract JSON path.
        #[arg(long)]
        input: Option<PathBuf>,

        /// Output dynamics measurement contract validation report JSON path. If omitted, JSON is written to stdout.
        #[arg(long)]
        out: Option<PathBuf>,
    },

    /// Emit or validate a pr-force-report-v0 artifact.
    PrForceReport {
        /// Optional PR force report JSON path to validate.
        #[arg(long)]
        input: Option<PathBuf>,

        /// Emit the canonical minimal pr-force-report-v0 fixture instead of a validation report.
        #[arg(long)]
        fixture: bool,

        /// Output PR force report or validation report JSON path. If omitted, JSON is written to stdout.
        #[arg(long)]
        out: Option<PathBuf>,
    },

    /// Emit or validate a signature-trajectory-report-v0 artifact.
    SignatureTrajectoryReport {
        /// Optional Signature trajectory report JSON path to validate.
        #[arg(long)]
        input: Option<PathBuf>,

        /// Emit the canonical minimal signature-trajectory-report-v0 fixture.
        #[arg(long)]
        fixture: bool,

        /// Output trajectory report or validation report JSON path. If omitted, JSON is written to stdout.
        #[arg(long)]
        out: Option<PathBuf>,
    },

    /// Emit or validate an architecture-dynamics-metrics-report-v0 artifact.
    ArchitectureDynamicsMetrics {
        /// Optional Architecture Dynamics metrics report JSON path to validate.
        #[arg(long)]
        input: Option<PathBuf>,

        /// Emit the canonical minimal architecture-dynamics-metrics-report-v0 fixture.
        #[arg(long)]
        fixture: bool,

        /// Output metrics report or validation report JSON path. If omitted, JSON is written to stdout.
        #[arg(long)]
        out: Option<PathBuf>,
    },

    /// Emit or validate an architecture-field-snapshot-v0 artifact.
    ArchitectureFieldSnapshot {
        /// Optional Architecture field snapshot JSON path to validate.
        #[arg(long)]
        input: Option<PathBuf>,

        /// Emit the canonical minimal architecture-field-snapshot-v0 fixture.
        #[arg(long)]
        fixture: bool,

        /// Output field snapshot or validation report JSON path. If omitted, JSON is written to stdout.
        #[arg(long)]
        out: Option<PathBuf>,
    },

    /// Emit or validate an operation-proposal-log-v0 artifact.
    OperationProposalLog {
        /// Optional Operation proposal log JSON path to validate.
        #[arg(long)]
        input: Option<PathBuf>,

        /// Emit the canonical minimal operation-proposal-log-v0 fixture.
        #[arg(long)]
        fixture: bool,

        /// Output proposal log or validation report JSON path. If omitted, JSON is written to stdout.
        #[arg(long)]
        out: Option<PathBuf>,
    },

    /// Emit or validate a software-field-measurement-v0 artifact.
    SoftwareFieldMeasurement {
        /// Optional SoftwareFieldMeasurement JSON path to validate.
        #[arg(long)]
        input: Option<PathBuf>,

        /// Emit the canonical minimal software-field-measurement-v0 fixture.
        #[arg(long)]
        fixture: bool,

        /// Output measurement or validation report JSON path. If omitted, JSON is written to stdout.
        #[arg(long)]
        out: Option<PathBuf>,
    },

    /// Emit or validate a fieldsig-run-manifest-v0 artifact.
    #[command(name = "fieldsig-run-manifest")]
    FieldSigRunManifest {
        /// Optional FieldSig run manifest JSON path to validate.
        #[arg(long)]
        input: Option<PathBuf>,

        /// Emit the canonical minimal fieldsig-run-manifest-v0 fixture.
        #[arg(long)]
        fixture: bool,

        /// Output manifest or validation report JSON path. If omitted, JSON is written to stdout.
        #[arg(long)]
        out: Option<PathBuf>,
    },

    /// Emit or validate an artifact-descriptor-v0 artifact.
    ArtifactDescriptor {
        /// Optional ArtifactDescriptor JSON path to validate.
        #[arg(long)]
        input: Option<PathBuf>,

        /// Markdown PRD / Spec / proposal path to normalize into artifact-descriptor-v0.
        #[arg(long = "from-markdown")]
        from_markdown: Option<PathBuf>,

        /// GitHub Issue JSON path to normalize into artifact-descriptor-v0.
        #[arg(long = "from-github-issue-json")]
        from_github_issue_json: Option<PathBuf>,

        /// AI proposal JSON path to normalize into artifact-descriptor-v0.
        #[arg(long = "from-ai-proposal-json")]
        from_ai_proposal_json: Option<PathBuf>,

        /// Artifact kind for --from-markdown output.
        #[arg(long = "artifact-kind", default_value = "prd", value_parser = ["prd", "spec", "issue", "ai-proposal"])]
        artifact_kind: String,

        /// Emit the canonical minimal artifact-descriptor-v0 fixture.
        #[arg(long)]
        fixture: bool,

        /// Output descriptor or validation report JSON path. If omitted, JSON is written to stdout.
        #[arg(long)]
        out: Option<PathBuf>,
    },

    /// Emit or validate an intentmap-v0 artifact.
    IntentMap {
        /// Optional IntentMap JSON path to validate.
        #[arg(long)]
        input: Option<PathBuf>,

        /// Emit the canonical minimal intentmap-v0 fixture.
        #[arg(long)]
        fixture: bool,

        /// Output IntentMap or validation report JSON path. If omitted, JSON is written to stdout.
        #[arg(long)]
        out: Option<PathBuf>,
    },

    /// Emit or validate an intent-archmap-alignment-v0 artifact.
    IntentArchmapAlignment {
        /// Optional AlignmentMap JSON path to validate.
        #[arg(long)]
        input: Option<PathBuf>,

        /// IntentMap JSON path used for dangling reference validation.
        #[arg(long = "intent-map")]
        intent_map: Option<PathBuf>,

        /// ArchMap JSON path used for dangling reference validation.
        #[arg(long)]
        archmap: Option<PathBuf>,

        /// Emit the canonical minimal intent-archmap-alignment-v0 fixture.
        #[arg(long)]
        fixture: bool,

        /// Output AlignmentMap or validation report JSON path. If omitted, JSON is written to stdout.
        #[arg(long)]
        out: Option<PathBuf>,
    },

    /// Build operation support from IntentMap x ArchMap alignment.
    IntentForecast {
        /// IntentMap JSON path.
        #[arg(long = "intent-map")]
        intent_map: PathBuf,

        /// ArchMap JSON path.
        #[arg(long)]
        archmap: PathBuf,

        /// AlignmentMap JSON path.
        #[arg(long)]
        alignment: PathBuf,

        /// Output directory for operation support, ForecastCone, ConsequenceEnvelope, and validations.
        #[arg(long = "out-dir")]
        out_dir: PathBuf,

        /// Bounded horizon step count for forecast-cone-skeleton-v0 generation.
        #[arg(long = "horizon-steps", default_value_t = 3)]
        horizon_steps: u32,

        /// Human-readable horizon boundary for forecast-cone-skeleton-v0 generation.
        #[arg(
            long = "horizon-window",
            default_value = "selected bounded intent forecast horizon"
        )]
        horizon_window: String,
    },

    /// Emit or validate an operation-support-estimate-v0 artifact.
    OperationSupportEstimate {
        /// Optional OperationSupportEstimate JSON path to validate.
        #[arg(long)]
        input: Option<PathBuf>,

        /// ArtifactDescriptor JSON path to generate operation-support-estimate-v0 from.
        #[arg(long)]
        descriptor: Option<PathBuf>,

        /// Emit the canonical minimal operation-support-estimate-v0 fixture.
        #[arg(long)]
        fixture: bool,

        /// Output estimate or validation report JSON path. If omitted, JSON is written to stdout.
        #[arg(long)]
        out: Option<PathBuf>,
    },

    /// Emit or validate a forecast-cone-skeleton-v0 artifact.
    ForecastConeSkeleton {
        /// Optional ForecastCone skeleton JSON path to validate.
        #[arg(long)]
        input: Option<PathBuf>,

        /// OperationSupportEstimate JSON path to generate forecast-cone-skeleton-v0 from.
        #[arg(long = "operation-support")]
        operation_support: Option<PathBuf>,

        /// Bounded horizon step count for --operation-support generation.
        #[arg(long = "horizon-steps", default_value_t = 3)]
        horizon_steps: u32,

        /// Human-readable horizon boundary for --operation-support generation.
        #[arg(
            long = "horizon-window",
            default_value = "selected bounded forecast horizon"
        )]
        horizon_window: String,

        /// Emit the canonical minimal forecast-cone-skeleton-v0 fixture.
        #[arg(long)]
        fixture: bool,

        /// Output cone or validation report JSON path. If omitted, JSON is written to stdout.
        #[arg(long)]
        out: Option<PathBuf>,
    },

    /// Emit or validate a consequence-envelope-report-v0 artifact.
    ConsequenceEnvelope {
        /// Optional ConsequenceEnvelope report JSON path to validate.
        #[arg(long)]
        input: Option<PathBuf>,

        /// ForecastConeSkeleton JSON path to generate consequence-envelope-report-v0 from.
        #[arg(long = "forecast-cone")]
        forecast_cone: Option<PathBuf>,

        /// Emit the canonical minimal consequence-envelope-report-v0 fixture.
        #[arg(long)]
        fixture: bool,

        /// Output report or validation report JSON path. If omitted, JSON is written to stdout.
        #[arg(long)]
        out: Option<PathBuf>,
    },

    /// Emit or validate an sft-review-summary-v0 artifact.
    SftReviewSummary {
        /// Optional SFT review summary JSON path to validate.
        #[arg(long)]
        input: Option<PathBuf>,

        /// ConsequenceEnvelope report JSON path to generate sft-review-summary-v0 from.
        #[arg(long = "consequence-envelope")]
        consequence_envelope: Option<PathBuf>,

        /// Emit the canonical minimal sft-review-summary-v0 fixture.
        #[arg(long)]
        fixture: bool,

        /// Output summary or validation report JSON path. If omitted, JSON is written to stdout.
        #[arg(long)]
        out: Option<PathBuf>,
    },

    /// Build the end-to-end SFT forecast pipeline from a PRD / Spec / Issue artifact.
    SftForecast {
        /// Markdown PRD / Spec / Issue / AI proposal artifact path.
        #[arg(long)]
        artifact: PathBuf,

        /// Input format for the generated artifact-descriptor-v0.
        #[arg(long = "artifact-format", default_value = "markdown", value_parser = ["markdown", "github-issue-json", "ai-proposal-json"])]
        artifact_format: String,

        /// Artifact kind for markdown-generated artifact-descriptor-v0.
        #[arg(long = "artifact-kind", default_value = "prd", value_parser = ["prd", "spec", "issue", "ai-proposal"])]
        artifact_kind: String,

        /// Bounded horizon step count for forecast-cone-skeleton-v0 generation.
        #[arg(long = "horizon-steps", default_value_t = 3)]
        horizon_steps: u32,

        /// Human-readable horizon boundary for forecast-cone-skeleton-v0 generation.
        #[arg(
            long = "horizon-window",
            default_value = "selected bounded forecast horizon"
        )]
        horizon_window: String,

        /// Output directory for intermediate artifacts, validation reports, and final envelope.
        #[arg(long = "out-dir")]
        out_dir: PathBuf,
    },

    /// Emit or validate a forecast-calibration-hook-v0 artifact.
    ForecastCalibrationHook {
        /// Optional ForecastCalibrationHook JSON path to validate.
        #[arg(long)]
        input: Option<PathBuf>,

        /// Emit the canonical minimal forecast-calibration-hook-v0 fixture.
        #[arg(long)]
        fixture: bool,

        /// Output hook or validation report JSON path. If omitted, JSON is written to stdout.
        #[arg(long)]
        out: Option<PathBuf>,
    },

    /// Emit or validate a pr-quality-analysis-report-v0 artifact.
    PrQualityAnalysis {
        /// Optional PR quality analysis JSON path to validate.
        #[arg(long)]
        input: Option<PathBuf>,

        /// Emit the canonical minimal pr-quality-analysis-report-v0 fixture.
        #[arg(long)]
        fixture: bool,

        /// Output report or validation report JSON path. If omitted, JSON is written to stdout.
        #[arg(long)]
        out: Option<PathBuf>,
    },

    /// Emit or validate an aat-observable-bundle-v0 artifact.
    AatObservableBundle {
        /// Optional AAT observable bundle JSON path to validate.
        #[arg(long)]
        input: Option<PathBuf>,

        /// Emit the canonical minimal aat-observable-bundle-v0 fixture.
        #[arg(long)]
        fixture: bool,

        /// Output bundle or validation report JSON path. If omitted, JSON is written to stdout.
        #[arg(long)]
        out: Option<PathBuf>,
    },

    /// Emit or validate an intent-calibration-record-v0 artifact.
    IntentCalibrationRecord {
        /// Optional intent calibration record JSON path to validate.
        #[arg(long)]
        input: Option<PathBuf>,

        /// Emit the canonical minimal intent-calibration-record-v0 fixture.
        #[arg(long)]
        fixture: bool,

        /// Output record or validation report JSON path. If omitted, JSON is written to stdout.
        #[arg(long)]
        out: Option<PathBuf>,
    },

    /// Emit, validate, or generate an AI proposal governance artifact.
    AiProposalGovernance {
        /// Optional AI proposal governance JSON path to validate.
        #[arg(long)]
        input: Option<PathBuf>,

        /// ArtifactDescriptor JSON path to project into ai-proposal-governance-v0.
        #[arg(long)]
        descriptor: Option<PathBuf>,

        /// Optional operation-support-estimate-v0 id retained as a governance source ref.
        #[arg(long = "operation-support-id")]
        operation_support_id: Option<String>,

        /// Optional consequence-envelope-report-v0 id retained as a governance source ref.
        #[arg(long = "consequence-envelope-id")]
        consequence_envelope_id: Option<String>,

        /// Emit the canonical minimal ai-proposal-governance-v0 fixture.
        #[arg(long)]
        fixture: bool,

        /// Output governance artifact or validation report JSON path. If omitted, JSON is written to stdout.
        #[arg(long)]
        out: Option<PathBuf>,
    },

    /// Emit the B9 detectable values / reported axes catalog.
    ReportedAxesCatalog {
        /// Output reported axes catalog JSON path. If omitted, JSON is written to stdout.
        #[arg(long)]
        out: Option<PathBuf>,
    },

    /// Build a B7 warn / fail / advisory policy decision report.
    PolicyDecision {
        /// Feature Extension Report JSON path.
        #[arg(long = "feature-report")]
        feature_report: PathBuf,

        /// Optional organization policy JSON path. If omitted, the static B7 policy is used.
        #[arg(long)]
        policy: Option<PathBuf>,

        /// Output policy decision report JSON path. If omitted, JSON is written to stdout.
        #[arg(long)]
        out: Option<PathBuf>,
    },

    /// Validate report artifact retention metadata. If input is omitted, validate the static B7 manifest.
    ReportArtifacts {
        /// Optional report artifact retention manifest JSON path.
        #[arg(long)]
        input: Option<PathBuf>,

        /// Output report artifact retention validation report JSON path. If omitted, JSON is written to stdout.
        #[arg(long)]
        out: Option<PathBuf>,
    },

    /// Render a GitHub Checks / PR comment Markdown summary.
    PrComment {
        /// Feature Extension Report JSON path.
        #[arg(long = "feature-report")]
        feature_report: PathBuf,

        /// Optional policy decision report JSON path.
        #[arg(long = "policy-decision")]
        policy_decision: Option<PathBuf>,

        /// Output Markdown path. If omitted, Markdown is written to stdout.
        #[arg(long)]
        out: Option<PathBuf>,
    },

    /// Compare baseline/current reports and apply suppression / accepted-risk workflow metadata.
    BaselineSuppression {
        /// Baseline Feature Extension Report JSON path.
        #[arg(long = "baseline-feature-report")]
        baseline_feature_report: PathBuf,

        /// Current Feature Extension Report JSON path.
        #[arg(long = "current-feature-report")]
        current_feature_report: PathBuf,

        /// Optional baseline policy decision report JSON path.
        #[arg(long = "baseline-policy-decision")]
        baseline_policy_decision: Option<PathBuf>,

        /// Optional current policy decision report JSON path.
        #[arg(long = "current-policy-decision")]
        current_policy_decision: Option<PathBuf>,

        /// Optional report artifact retention manifest JSON path.
        #[arg(long = "retention-manifest")]
        retention_manifest: Option<PathBuf>,

        /// Optional suppression metadata JSON path. Repeat for multiple files.
        #[arg(long)]
        suppression: Vec<PathBuf>,

        /// Optional accepted-risk metadata JSON path. Repeat for multiple files.
        #[arg(long = "accepted-risk")]
        accepted_risk: Vec<PathBuf>,

        /// Output baseline suppression report JSON path. If omitted, JSON is written to stdout.
        #[arg(long)]
        out: Option<PathBuf>,
    },

    /// Check B9 schema migration / compatibility metadata between two artifacts.
    SchemaCatalog {
        /// Output schema version catalog JSON path. If omitted, JSON is written to stdout.
        #[arg(long)]
        out: Option<PathBuf>,
    },

    /// Check B9 schema migration / compatibility metadata between two artifacts.
    SchemaCompatibility {
        /// Baseline artifact JSON path.
        #[arg(long)]
        before: PathBuf,

        /// Current or migrated artifact JSON path.
        #[arg(long)]
        after: PathBuf,

        /// Optional schema version catalog JSON path. If omitted, the static B9 catalog is used.
        #[arg(long)]
        catalog: Option<PathBuf>,

        /// Output schema compatibility check report JSON path. If omitted, JSON is written to stdout.
        #[arg(long)]
        out: Option<PathBuf>,
    },
}

fn main() -> ExitCode {
    match run() {
        Ok(code) => code,
        Err(error) => {
            eprintln!("{error}");
            ExitCode::from(2)
        }
    }
}

fn run() -> Result<ExitCode, Box<dyn Error>> {
    let args = Args::parse();

    match args.command {
        Some(Command::Validate {
            input,
            out,
            universe_mode,
        }) => {
            let file = File::open(&input)?;
            let document: Sig0Document = serde_json::from_reader(file)?;
            let report = validate_component_universe_report(
                &document,
                &input.display().to_string(),
                &universe_mode,
            )?;
            let failed = report.summary.result == "fail";
            write_json(out, &report)?;
            Ok(if failed {
                ExitCode::from(1)
            } else {
                ExitCode::SUCCESS
            })
        }
        Some(Command::Dataset {
            before,
            after,
            pr_metadata,
            after_role,
            out,
        }) => {
            let before_document: Sig0Document = serde_json::from_reader(File::open(&before)?)?;
            let after_document: Sig0Document = serde_json::from_reader(File::open(&after)?)?;
            let metadata: EmpiricalDatasetInput =
                serde_json::from_reader(File::open(&pr_metadata)?)?;
            let dataset =
                build_empirical_dataset(&before_document, &after_document, metadata, &after_role)?;
            write_json(out, &dataset)?;
            Ok(ExitCode::SUCCESS)
        }
        Some(Command::PrMetadata {
            pull_request,
            files,
            reviews,
            review_threads,
            out,
        }) => {
            let metadata = build_pr_metadata_from_github_files(
                &pull_request,
                &files,
                reviews.as_deref(),
                review_threads.as_deref(),
            )?;
            write_json(out, &metadata)?;
            Ok(ExitCode::SUCCESS)
        }
        Some(Command::PrHistoryDataset {
            pull_request,
            files,
            reviews,
            review_threads,
            signature_artifact,
            feature_report_artifact,
            out,
        }) => {
            let dataset = build_pr_history_dataset_from_github_files(
                &pull_request,
                &files,
                reviews.as_deref(),
                review_threads.as_deref(),
                &signature_artifact,
                &feature_report_artifact,
            )?;
            write_json(out, &dataset)?;
            Ok(ExitCode::SUCCESS)
        }
        Some(Command::FeatureExtensionDataset {
            pr_history,
            feature_report,
            theorem_check_report,
            out,
        }) => {
            let dataset = build_feature_extension_dataset_from_files(
                &pr_history,
                &feature_report,
                &theorem_check_report,
            )?;
            write_json(out, &dataset)?;
            Ok(ExitCode::SUCCESS)
        }
        Some(Command::OutcomeLinkageDataset {
            feature_dataset,
            outcome,
            out,
        }) => {
            let dataset = build_outcome_linkage_dataset_from_files(&feature_dataset, &outcome)?;
            write_json(out, &dataset)?;
            Ok(ExitCode::SUCCESS)
        }
        Some(Command::ReportOutcomeDailyLedger {
            outcome_linkage,
            drift_ledger,
            ledger_id,
            generated_at,
            window_start,
            window_end,
            window_kind,
            retention_days,
            out,
        }) => {
            let ledger = build_report_outcome_daily_ledger_from_files(
                &outcome_linkage,
                &drift_ledger,
                ReportOutcomeDailyLedgerInput {
                    ledger_id,
                    generated_at,
                    aggregation_window: DriftLedgerAggregationWindowV0 {
                        window_start,
                        window_end,
                        window_kind,
                    },
                    retention_period_days: retention_days,
                },
            )?;
            write_json(out, &ledger)?;
            Ok(ExitCode::SUCCESS)
        }
        Some(Command::CalibrationReviewRecord { out }) => {
            let record: CalibrationReviewRecordV0 = static_calibration_review_record();
            write_json(out, &record)?;
            Ok(ExitCode::SUCCESS)
        }
        Some(Command::TeamThresholdPolicy { out }) => {
            let policy: TeamThresholdPolicyV0 = static_team_threshold_policy();
            write_json(out, &policy)?;
            Ok(ExitCode::SUCCESS)
        }
        Some(Command::OwnershipBoundaryMonitor { out }) => {
            let monitor: OwnershipBoundaryMonitorV0 = static_ownership_boundary_monitor();
            write_json(out, &monitor)?;
            Ok(ExitCode::SUCCESS)
        }
        Some(Command::RepairAdoptionRecord { out }) => {
            let record: RepairAdoptionRecordV0 = static_repair_adoption_record();
            write_json(out, &record)?;
            Ok(ExitCode::SUCCESS)
        }
        Some(Command::IncidentCorrelationMonitor { out }) => {
            let monitor: IncidentCorrelationMonitorV0 = static_incident_correlation_monitor();
            write_json(out, &monitor)?;
            Ok(ExitCode::SUCCESS)
        }
        Some(Command::HypothesisRefreshCycle { out }) => {
            let cycle: HypothesisRefreshCycleV0 = static_hypothesis_refresh_cycle();
            write_json(out, &cycle)?;
            Ok(ExitCode::SUCCESS)
        }
        Some(Command::RelationComplexity { input, out }) => {
            let observation = extract_relation_complexity_observation_from_file(&input)?;
            write_json(out, &observation)?;
            Ok(ExitCode::SUCCESS)
        }
        Some(Command::Snapshot {
            input,
            validation_report,
            repo_owner,
            repo_name,
            default_branch,
            remote_url,
            revision_sha,
            revision_ref,
            revision_branch,
            committed_at,
            parent_sha,
            scanned_at,
            scanner_id,
            trigger,
            scan_root,
            policy_version,
            policy_path,
            policy_content_hash,
            extractor_output_path,
            tag,
            notes,
            out,
        }) => {
            let document: Sig0Document = read_json(&input)?;
            let validation: Option<ComponentUniverseValidationReport> = validation_report
                .as_ref()
                .map(|path| read_json(path))
                .transpose()?;
            let validation_report_path = validation_report.map(|path| path.display().to_string());
            let snapshot = build_signature_snapshot_record(
                &document,
                validation.as_ref(),
                SnapshotRecordInput {
                    repository: SnapshotRepositoryRef {
                        owner: repo_owner,
                        name: repo_name,
                        default_branch,
                        remote_url,
                    },
                    revision: RepositoryRevisionRef {
                        sha: revision_sha,
                        ref_name: revision_ref,
                        branch: revision_branch,
                        committed_at,
                        parent_shas: parent_sha,
                    },
                    scan: ScanMetadata {
                        scanned_at,
                        scanner_id,
                        trigger,
                        root: scan_root,
                    },
                    policy_version,
                    policy_source_path: policy_path,
                    policy_content_hash,
                    extractor_output_path,
                    validation_report_path,
                    tags: tag,
                    notes,
                },
            );
            write_json(out, &snapshot)?;
            Ok(ExitCode::SUCCESS)
        }
        Some(Command::SignatureDiff {
            before_snapshot,
            after_snapshot,
            before_sig0,
            after_sig0,
            pr_metadata,
            out,
        }) => {
            let before: SignatureSnapshotStoreRecordV0 = read_json(&before_snapshot)?;
            let after: SignatureSnapshotStoreRecordV0 = read_json(&after_snapshot)?;
            let before_document: Option<Sig0Document> = before_sig0
                .as_ref()
                .map(|path| read_json(path))
                .transpose()?;
            let after_document: Option<Sig0Document> = after_sig0
                .as_ref()
                .map(|path| read_json(path))
                .transpose()?;
            let pr_metadata = pr_metadata
                .iter()
                .map(read_json)
                .collect::<Result<Vec<EmpiricalDatasetInput>, Box<dyn Error>>>()?;
            let report = build_signature_diff_report(
                &before,
                &after,
                before_document.as_ref(),
                after_document.as_ref(),
                &pr_metadata,
            );
            write_json(out, &report)?;
            Ok(ExitCode::SUCCESS)
        }
        Some(Command::Air {
            sig0,
            validation,
            diff,
            pr_metadata,
            law_policy,
            framework_adapters,
            out,
        }) => {
            let document: Sig0Document = read_json(&sig0)?;
            let validation_report: Option<ComponentUniverseValidationReport> =
                validation.as_ref().map(read_json).transpose()?;
            let diff_report: Option<SignatureDiffReportV0> =
                diff.as_ref().map(read_json).transpose()?;
            let pr_metadata_document: Option<EmpiricalDatasetInput> =
                pr_metadata.as_ref().map(read_json).transpose()?;
            let mut air = build_air_document(
                &document,
                validation_report.as_ref(),
                diff_report.as_ref(),
                pr_metadata_document.as_ref(),
                AirDocumentInput {
                    sig0_path: sig0.display().to_string(),
                    validation_path: validation.map(|path| path.display().to_string()),
                    diff_path: diff.map(|path| path.display().to_string()),
                    pr_metadata_path: pr_metadata.map(|path| path.display().to_string()),
                    law_policy_path: law_policy.map(|path| path.display().to_string()),
                },
            );
            for (index, path) in framework_adapters.iter().enumerate() {
                let adapter: FrameworkAdapterEvidenceV0 = read_json(path)?;
                attach_framework_adapter_evidence(
                    &mut air,
                    &adapter,
                    path.display().to_string(),
                    index,
                )?;
            }
            write_json(out, &air)?;
            Ok(ExitCode::SUCCESS)
        }
        Some(Command::Archmap { input, sig0, out }) => {
            let document: ArchMapDocumentV0 = read_json(&input)?;
            let sig0_document: Option<Sig0Document> = sig0.as_ref().map(read_json).transpose()?;
            let source_inventory_path = document
                .source_inventory_ref
                .as_ref()
                .and_then(|source_inventory_ref| source_inventory_ref.path.as_deref());
            let mut source_inventory_document: Option<ArchMapSourceInventoryV0> = None;
            let mut source_inventory_error: Option<String> = None;
            if let Some(path) = source_inventory_path {
                match resolve_archmap_sidecar_path(&input, path) {
                    Some(resolved_path) => match read_json(&resolved_path) {
                        Ok(source_inventory) => source_inventory_document = Some(source_inventory),
                        Err(error) => {
                            source_inventory_error = Some(format!(
                                "source inventory artifact could not be read: {error}"
                            ));
                        }
                    },
                    None => {
                        source_inventory_error =
                            Some("source inventory artifact path does not exist".to_string());
                    }
                }
            }
            let source_inventory = source_inventory_path.map(|path| ArchMapSourceInventoryInput {
                path,
                document: source_inventory_document.as_ref(),
                read_error: source_inventory_error.clone(),
            });
            let report: ArchMapValidationReportV0 = validate_archmap_report(
                &document,
                &input.display().to_string(),
                sig0_document.as_ref(),
                source_inventory,
            );
            let failed = report.summary.result == "fail";
            write_json(out, &report)?;
            Ok(if failed {
                ExitCode::from(1)
            } else {
                ExitCode::SUCCESS
            })
        }
        Some(Command::ArchmapGenerate {
            source_inventory,
            prompt_pack,
            provider,
            model_id,
            out,
        }) => {
            let inventory: ArchMapSourceInventoryV0 = read_json(&source_inventory)?;
            let protocol = serde_json::json!({
                "schemaVersion": "archmap-generation-protocol-v0",
                "protocolId": format!("archmap-generation:{}", inventory.inventory_id),
                "sourceInventoryRef": {
                    "artifactId": inventory.inventory_id,
                    "kind": "source_inventory",
                    "path": source_inventory.display().to_string()
                },
                "promptPackRef": {
                    "artifactId": "archmap-prompt-pack",
                    "kind": "prompt",
                    "path": prompt_pack.display().to_string()
                },
                "modelProvenance": {
                    "provider": provider,
                    "modelId": model_id
                },
                "requiredWorkflow": [
                    "read source inventory includedRefs / excludedRefs / privateRefs / unavailableRefs separately",
                    "produce archmap-v0 JSON with sourceRefs, preserves, forgets, missingEvidence, and nonConclusions",
                    "run archsig archmap --input <archmap.json> before downstream projection",
                    "preserve invalid, dangling, unsupported, private, and unavailable evidence as boundary data"
                ],
                "generationBoundary": {
                    "selectionBoundary": inventory.selection_boundary,
                    "privateRefCount": inventory.private_refs.len(),
                    "unavailableRefCount": inventory.unavailable_refs.len(),
                    "nonConclusions": [
                        "external agent output is not semantic truth",
                        "generation protocol does not reconstruct private context",
                        "validation pass does not prove architecture lawfulness"
                    ]
                }
            });
            write_json(out, &protocol)?;
            Ok(ExitCode::SUCCESS)
        }
        Some(Command::ArchmapSftInput { archmap, out }) => {
            let document: ArchMapDocumentV0 = read_json(&archmap)?;
            let estimate: OperationSupportEstimateV0 =
                build_operation_support_estimate_from_archmap(
                    &document,
                    &archmap.display().to_string(),
                );
            write_json(out, &estimate)?;
            Ok(ExitCode::SUCCESS)
        }
        Some(Command::ArchsigAnalysisSftInput {
            analysis_packet,
            out,
        }) => {
            let packet: serde_json::Value = read_json(&analysis_packet)?;
            let estimate = build_operation_support_estimate_from_archsig_analysis_packet(
                &packet,
                &analysis_packet.display().to_string(),
            )?;
            write_json(out, &estimate)?;
            Ok(ExitCode::SUCCESS)
        }
        Some(Command::AirFromArchmap {
            archmap,
            sig0,
            validation,
            out,
        }) => {
            let document: ArchMapDocumentV0 = read_json(&archmap)?;
            let sig0_document: Option<Sig0Document> = sig0.as_ref().map(read_json).transpose()?;
            if let Some(validation_path) = validation.as_ref() {
                let _: ArchMapValidationReportV0 = read_json(validation_path)?;
            }
            let air = build_air_from_archmap(
                &document,
                &archmap.display().to_string(),
                sig0_document.as_ref(),
            );
            write_json(out, &air)?;
            Ok(ExitCode::SUCCESS)
        }
        Some(Command::ValidateAir {
            input,
            out,
            strict_measured_evidence,
        }) => {
            let document: AirDocumentV0 = read_json(&input)?;
            let report: AirValidationReport = validate_air_document_report(
                &document,
                &input.display().to_string(),
                strict_measured_evidence,
            );
            let failed = report.summary.result == "fail";
            write_json(out, &report)?;
            Ok(if failed {
                ExitCode::from(1)
            } else {
                ExitCode::SUCCESS
            })
        }
        Some(Command::FeatureReport { air, out }) => {
            let document: AirDocumentV0 = read_json(&air)?;
            let report: FeatureExtensionReportV0 =
                build_feature_extension_report(&document, &air.display().to_string());
            write_json(out, &report)?;
            Ok(ExitCode::SUCCESS)
        }
        Some(Command::TheoremCheck { air, out }) => {
            let document: AirDocumentV0 = read_json(&air)?;
            let report: TheoremPreconditionCheckReportV0 =
                build_theorem_precondition_check_report(&document, &air.display().to_string());
            write_json(out, &report)?;
            Ok(ExitCode::SUCCESS)
        }
        Some(Command::RepairRegistry { input, out }) => {
            let registry: RepairRuleRegistryV0 = input
                .as_ref()
                .map(read_json)
                .transpose()?
                .unwrap_or_else(static_repair_rule_registry);
            let input_path = input
                .as_ref()
                .map(|path| path.display().to_string())
                .unwrap_or_else(|| "static-repair-rule-registry".to_string());
            let report: RepairRuleRegistryValidationReportV0 =
                validate_repair_rule_registry_report(&registry, &input_path);
            let failed = report.summary.result == "fail";
            write_json(out, &report)?;
            Ok(if failed {
                ExitCode::from(1)
            } else {
                ExitCode::SUCCESS
            })
        }
        Some(Command::SynthesisConstraints { input, out }) => {
            let artifact: SynthesisConstraintArtifactV0 = input
                .as_ref()
                .map(read_json)
                .transpose()?
                .unwrap_or_else(static_synthesis_constraint_artifact);
            let input_path = input
                .as_ref()
                .map(|path| path.display().to_string())
                .unwrap_or_else(|| "static-synthesis-constraint-artifact".to_string());
            let report: SynthesisConstraintValidationReportV0 =
                validate_synthesis_constraint_artifact_report(&artifact, &input_path);
            let failed = report.summary.result == "fail";
            write_json(out, &report)?;
            Ok(if failed {
                ExitCode::from(1)
            } else {
                ExitCode::SUCCESS
            })
        }
        Some(Command::NoSolutionCertificate { input, out }) => {
            let certificate: NoSolutionCertificateV0 = input
                .as_ref()
                .map(read_json)
                .transpose()?
                .unwrap_or_else(static_no_solution_certificate);
            let input_path = input
                .as_ref()
                .map(|path| path.display().to_string())
                .unwrap_or_else(|| "static-no-solution-certificate".to_string());
            let report: NoSolutionCertificateValidationReportV0 =
                validate_no_solution_certificate_report(&certificate, &input_path);
            let failed = report.summary.result == "fail";
            write_json(out, &report)?;
            Ok(if failed {
                ExitCode::from(1)
            } else {
                ExitCode::SUCCESS
            })
        }
        Some(Command::OrganizationPolicy { input, out }) => {
            let policy: OrganizationPolicyV0 = input
                .as_ref()
                .map(read_json)
                .transpose()?
                .unwrap_or_else(static_organization_policy);
            let input_path = input
                .as_ref()
                .map(|path| path.display().to_string())
                .unwrap_or_else(|| "static-organization-policy".to_string());
            let report: OrganizationPolicyValidationReportV0 =
                validate_organization_policy_report(&policy, &input_path);
            let failed = report.summary.result == "fail";
            write_json(out, &report)?;
            Ok(if failed {
                ExitCode::from(1)
            } else {
                ExitCode::SUCCESS
            })
        }
        Some(Command::ArchitecturePolicy { input, out }) => {
            let policy: ArchitecturePolicyV0 = read_json(&input)?;
            let input_path = input.display().to_string();
            let report: ArchitecturePolicyValidationReportV0 =
                validate_architecture_policy_report(&policy, &input_path);
            let failed = report.summary.result == "fail";
            write_json(out, &report)?;
            Ok(if failed {
                ExitCode::from(1)
            } else {
                ExitCode::SUCCESS
            })
        }
        Some(Command::LawViolationReport { sig0, policy, out }) => {
            let sig0_document: Sig0Document = read_json(&sig0)?;
            let policy_document: ArchitecturePolicyV0 = read_json(&policy)?;
            let report: LawViolationReportV0 = build_law_violation_report(
                &sig0_document,
                Some(&sig0.display().to_string()),
                &policy_document,
                Some(&policy.display().to_string()),
            );
            write_json(out, &report)?;
            Ok(ExitCode::SUCCESS)
        }
        Some(Command::LawPolicyTemplates { input, out }) => {
            let registry: LawPolicyTemplateRegistryV0 = input
                .as_ref()
                .map(read_json)
                .transpose()?
                .unwrap_or_else(static_law_policy_template_registry);
            let input_path = input
                .as_ref()
                .map(|path| path.display().to_string())
                .unwrap_or_else(|| "static-law-policy-template-registry".to_string());
            let report: LawPolicyTemplateRegistryValidationReportV0 =
                validate_law_policy_template_registry_report(&registry, &input_path);
            let failed = report.summary.result == "fail";
            write_json(out, &report)?;
            Ok(if failed {
                ExitCode::from(1)
            } else {
                ExitCode::SUCCESS
            })
        }
        Some(Command::CustomRulePlugins { input, out }) => {
            let registry: CustomRulePluginRegistryV0 = input
                .as_ref()
                .map(read_json)
                .transpose()?
                .unwrap_or_else(static_custom_rule_plugin_registry);
            let input_path = input
                .as_ref()
                .map(|path| path.display().to_string())
                .unwrap_or_else(|| "static-custom-rule-plugin-registry".to_string());
            let report: CustomRulePluginRegistryValidationReportV0 =
                validate_custom_rule_plugin_registry_report(&registry, &input_path);
            let failed = report.summary.result == "fail";
            write_json(out, &report)?;
            Ok(if failed {
                ExitCode::from(1)
            } else {
                ExitCode::SUCCESS
            })
        }
        Some(Command::MeasurementUnits { input, out }) => {
            let registry: MeasurementUnitRegistryV0 = input
                .as_ref()
                .map(read_json)
                .transpose()?
                .unwrap_or_else(static_measurement_unit_registry);
            let input_path = input
                .as_ref()
                .map(|path| path.display().to_string())
                .unwrap_or_else(|| "static-measurement-unit-registry".to_string());
            let report: MeasurementUnitRegistryValidationReportV0 =
                validate_measurement_unit_registry_report(&registry, &input_path);
            let failed = report.summary.result == "fail";
            write_json(out, &report)?;
            Ok(if failed {
                ExitCode::from(1)
            } else {
                ExitCode::SUCCESS
            })
        }
        Some(Command::DynamicsMeasurements { input, out }) => {
            let contract: DynamicsMeasurementContractV0 = input
                .as_ref()
                .map(read_json)
                .transpose()?
                .unwrap_or_else(static_dynamics_measurement_contract);
            let input_path = input
                .as_ref()
                .map(|path| path.display().to_string())
                .unwrap_or_else(|| "static-dynamics-measurement-contract".to_string());
            let report: DynamicsMeasurementContractValidationReportV0 =
                validate_dynamics_measurement_contract_report(&contract, &input_path);
            let failed = report.summary.result == "fail";
            write_json(out, &report)?;
            Ok(if failed {
                ExitCode::from(1)
            } else {
                ExitCode::SUCCESS
            })
        }
        Some(Command::PrForceReport {
            input,
            fixture,
            out,
        }) => {
            if fixture {
                let report: PrForceReportV0 = static_pr_force_report();
                write_json(out, &report)?;
                return Ok(ExitCode::SUCCESS);
            }
            let report: PrForceReportV0 = input
                .as_ref()
                .map(read_json)
                .transpose()?
                .unwrap_or_else(static_pr_force_report);
            let input_path = input
                .as_ref()
                .map(|path| path.display().to_string())
                .unwrap_or_else(|| "static-pr-force-report".to_string());
            let validation: PrForceReportValidationReportV0 =
                validate_pr_force_report(&report, &input_path);
            let failed = validation.summary.result == "fail";
            write_json(out, &validation)?;
            Ok(if failed {
                ExitCode::from(1)
            } else {
                ExitCode::SUCCESS
            })
        }
        Some(Command::SignatureTrajectoryReport {
            input,
            fixture,
            out,
        }) => {
            if fixture {
                let report: SignatureTrajectoryReportV0 = static_signature_trajectory_report();
                write_json(out, &report)?;
                return Ok(ExitCode::SUCCESS);
            }
            let report: SignatureTrajectoryReportV0 = input
                .as_ref()
                .map(read_json)
                .transpose()?
                .unwrap_or_else(static_signature_trajectory_report);
            let input_path = input
                .as_ref()
                .map(|path| path.display().to_string())
                .unwrap_or_else(|| "static-signature-trajectory-report".to_string());
            let validation: SignatureTrajectoryReportValidationReportV0 =
                validate_signature_trajectory_report(&report, &input_path);
            let failed = validation.summary.result == "fail";
            write_json(out, &validation)?;
            Ok(if failed {
                ExitCode::from(1)
            } else {
                ExitCode::SUCCESS
            })
        }
        Some(Command::ArchitectureDynamicsMetrics {
            input,
            fixture,
            out,
        }) => {
            if fixture {
                let report: ArchitectureDynamicsMetricsReportV0 =
                    static_architecture_dynamics_metrics_report();
                write_json(out, &report)?;
                return Ok(ExitCode::SUCCESS);
            }
            let report: ArchitectureDynamicsMetricsReportV0 = input
                .as_ref()
                .map(read_json)
                .transpose()?
                .unwrap_or_else(static_architecture_dynamics_metrics_report);
            let input_path = input
                .as_ref()
                .map(|path| path.display().to_string())
                .unwrap_or_else(|| "static-architecture-dynamics-metrics-report".to_string());
            let validation: ArchitectureDynamicsMetricsReportValidationReportV0 =
                validate_architecture_dynamics_metrics_report(&report, &input_path);
            let failed = validation.summary.result == "fail";
            write_json(out, &validation)?;
            Ok(if failed {
                ExitCode::from(1)
            } else {
                ExitCode::SUCCESS
            })
        }
        Some(Command::ArchitectureFieldSnapshot {
            input,
            fixture,
            out,
        }) => {
            if fixture {
                let snapshot: ArchitectureFieldSnapshotV0 = static_architecture_field_snapshot();
                write_json(out, &snapshot)?;
                return Ok(ExitCode::SUCCESS);
            }
            let snapshot: ArchitectureFieldSnapshotV0 = input
                .as_ref()
                .map(read_json)
                .transpose()?
                .unwrap_or_else(static_architecture_field_snapshot);
            let input_path = input
                .as_ref()
                .map(|path| path.display().to_string())
                .unwrap_or_else(|| "static-architecture-field-snapshot".to_string());
            let validation: ArchitectureFieldSnapshotValidationReportV0 =
                validate_architecture_field_snapshot(&snapshot, &input_path);
            let failed = validation.summary.result == "fail";
            write_json(out, &validation)?;
            Ok(if failed {
                ExitCode::from(1)
            } else {
                ExitCode::SUCCESS
            })
        }
        Some(Command::OperationProposalLog {
            input,
            fixture,
            out,
        }) => {
            if fixture {
                let log: OperationProposalLogV0 = static_operation_proposal_log();
                write_json(out, &log)?;
                return Ok(ExitCode::SUCCESS);
            }
            let log: OperationProposalLogV0 = input
                .as_ref()
                .map(read_json)
                .transpose()?
                .unwrap_or_else(static_operation_proposal_log);
            let input_path = input
                .as_ref()
                .map(|path| path.display().to_string())
                .unwrap_or_else(|| "static-operation-proposal-log".to_string());
            let validation: OperationProposalLogValidationReportV0 =
                validate_operation_proposal_log(&log, &input_path);
            let failed = validation.summary.result == "fail";
            write_json(out, &validation)?;
            Ok(if failed {
                ExitCode::from(1)
            } else {
                ExitCode::SUCCESS
            })
        }
        Some(Command::SoftwareFieldMeasurement {
            input,
            fixture,
            out,
        }) => {
            if fixture {
                let measurement: SoftwareFieldMeasurementV0 = static_software_field_measurement();
                write_json(out, &measurement)?;
                return Ok(ExitCode::SUCCESS);
            }
            let input_path = input
                .as_ref()
                .map(|path| path.display().to_string())
                .unwrap_or_else(|| "static".to_string());
            let measurement: SoftwareFieldMeasurementV0 = input
                .map(|path| read_json(&path))
                .transpose()?
                .unwrap_or_else(static_software_field_measurement);
            let validation: SoftwareFieldMeasurementValidationReportV0 =
                validate_software_field_measurement(&measurement, &input_path);
            let failed = validation.summary.result == "fail";
            write_json(out, &validation)?;
            Ok(if failed {
                ExitCode::from(1)
            } else {
                ExitCode::SUCCESS
            })
        }
        Some(Command::FieldSigRunManifest {
            input,
            fixture,
            out,
        }) => {
            if fixture {
                let manifest: FieldSigRunManifestV0 = static_fieldsig_run_manifest();
                write_json(out, &manifest)?;
                return Ok(ExitCode::SUCCESS);
            }
            let input_path = input
                .as_ref()
                .map(|path| path.display().to_string())
                .unwrap_or_else(|| "static".to_string());
            let manifest: FieldSigRunManifestV0 = input
                .map(|path| read_json(&path))
                .transpose()?
                .unwrap_or_else(static_fieldsig_run_manifest);
            let validation: FieldSigRunManifestValidationReportV0 =
                validate_fieldsig_run_manifest(&manifest, &input_path);
            let failed = validation.summary.result == "fail";
            write_json(out, &validation)?;
            Ok(if failed {
                ExitCode::from(1)
            } else {
                ExitCode::SUCCESS
            })
        }
        Some(Command::ArtifactDescriptor {
            input,
            from_markdown,
            from_github_issue_json,
            from_ai_proposal_json,
            artifact_kind,
            fixture,
            out,
        }) => {
            if fixture {
                let descriptor: ArtifactDescriptorV0 = static_artifact_descriptor();
                write_json(out, &descriptor)?;
                return Ok(ExitCode::SUCCESS);
            }
            if let Some(markdown_path) = from_markdown {
                let contents = std::fs::read_to_string(&markdown_path)?;
                let descriptor: ArtifactDescriptorV0 = build_artifact_descriptor_from_markdown(
                    &markdown_path.display().to_string(),
                    &contents,
                    &artifact_kind,
                );
                write_json(out, &descriptor)?;
                return Ok(ExitCode::SUCCESS);
            }
            if let Some(issue_json_path) = from_github_issue_json {
                let value: serde_json::Value = read_json(&issue_json_path)?;
                let descriptor: ArtifactDescriptorV0 =
                    build_artifact_descriptor_from_github_issue_json(
                        &issue_json_path.display().to_string(),
                        &value,
                    );
                write_json(out, &descriptor)?;
                return Ok(ExitCode::SUCCESS);
            }
            if let Some(proposal_json_path) = from_ai_proposal_json {
                let value: serde_json::Value = read_json(&proposal_json_path)?;
                let descriptor: ArtifactDescriptorV0 =
                    build_artifact_descriptor_from_ai_proposal_json(
                        &proposal_json_path.display().to_string(),
                        &value,
                    );
                write_json(out, &descriptor)?;
                return Ok(ExitCode::SUCCESS);
            }
            let descriptor: ArtifactDescriptorV0 = input
                .as_ref()
                .map(read_json)
                .transpose()?
                .unwrap_or_else(static_artifact_descriptor);
            let input_path = input
                .as_ref()
                .map(|path| path.display().to_string())
                .unwrap_or_else(|| "static-artifact-descriptor".to_string());
            let validation: ArtifactDescriptorValidationReportV0 =
                validate_artifact_descriptor_report(&descriptor, &input_path);
            let failed = validation.summary.result == "fail";
            write_json(out, &validation)?;
            Ok(if failed {
                ExitCode::from(1)
            } else {
                ExitCode::SUCCESS
            })
        }
        Some(Command::IntentMap {
            input,
            fixture,
            out,
        }) => {
            if fixture {
                let intent_map: IntentMapV0 = static_intent_map();
                write_json(out, &intent_map)?;
                return Ok(ExitCode::SUCCESS);
            }
            let intent_map: IntentMapV0 = input
                .as_ref()
                .map(read_json)
                .transpose()?
                .unwrap_or_else(static_intent_map);
            let input_path = input
                .as_ref()
                .map(|path| path.display().to_string())
                .unwrap_or_else(|| "static-intentmap".to_string());
            let validation: IntentMapValidationReportV0 =
                validate_intent_map(&intent_map, &input_path);
            let failed = validation.summary.result == "fail";
            write_json(out, &validation)?;
            Ok(if failed {
                ExitCode::from(1)
            } else {
                ExitCode::SUCCESS
            })
        }
        Some(Command::IntentArchmapAlignment {
            input,
            intent_map,
            archmap,
            fixture,
            out,
        }) => {
            if fixture {
                let alignment: IntentArchMapAlignmentV0 = static_intent_archmap_alignment();
                write_json(out, &alignment)?;
                return Ok(ExitCode::SUCCESS);
            }
            let alignment: IntentArchMapAlignmentV0 = input
                .as_ref()
                .map(read_json)
                .transpose()?
                .unwrap_or_else(static_intent_archmap_alignment);
            let intent_map_doc: Option<IntentMapV0> =
                intent_map.as_ref().map(read_json).transpose()?;
            let archmap_doc: Option<ArchMapDocumentV0> =
                archmap.as_ref().map(read_json).transpose()?;
            let input_path = input
                .as_ref()
                .map(|path| path.display().to_string())
                .unwrap_or_else(|| "static-intent-archmap-alignment".to_string());
            let validation: IntentArchMapAlignmentValidationReportV0 =
                validate_intent_archmap_alignment(
                    &alignment,
                    intent_map_doc.as_ref(),
                    archmap_doc.as_ref(),
                    &input_path,
                );
            let failed = validation.summary.result == "fail";
            write_json(out, &validation)?;
            Ok(if failed {
                ExitCode::from(1)
            } else {
                ExitCode::SUCCESS
            })
        }
        Some(Command::IntentForecast {
            intent_map,
            archmap,
            alignment,
            out_dir,
            horizon_steps,
            horizon_window,
        }) => {
            std::fs::create_dir_all(&out_dir)?;
            let intent_map_doc: IntentMapV0 = read_json(&intent_map)?;
            let archmap_doc: ArchMapDocumentV0 = read_json(&archmap)?;
            let alignment_doc: IntentArchMapAlignmentV0 = read_json(&alignment)?;

            let intent_validation_path = out_dir.join("intentmap-validation.json");
            let alignment_validation_path =
                out_dir.join("intent-archmap-alignment-validation.json");
            let estimate_path = out_dir.join("operation-support-estimate.json");
            let estimate_validation_path =
                out_dir.join("operation-support-estimate-validation.json");
            let cone_path = out_dir.join("forecast-cone-skeleton.json");
            let cone_validation_path = out_dir.join("forecast-cone-skeleton-validation.json");
            let envelope_path = out_dir.join("consequence-envelope-report.json");
            let envelope_validation_path = out_dir.join("consequence-envelope-validation.json");

            let intent_validation: IntentMapValidationReportV0 =
                validate_intent_map(&intent_map_doc, &intent_map.display().to_string());
            let alignment_validation: IntentArchMapAlignmentValidationReportV0 =
                validate_intent_archmap_alignment(
                    &alignment_doc,
                    Some(&intent_map_doc),
                    Some(&archmap_doc),
                    &alignment.display().to_string(),
                );
            let estimate: OperationSupportEstimateV0 =
                build_operation_support_estimate_from_intent_alignment(
                    &intent_map_doc,
                    &archmap_doc,
                    &alignment_doc,
                );
            let estimate_validation: OperationSupportEstimateValidationReportV0 =
                validate_operation_support_estimate(
                    &estimate,
                    &estimate_path.display().to_string(),
                );
            let cone: ForecastConeSkeletonV0 = build_forecast_cone_skeleton_from_operation_support(
                &estimate,
                horizon_steps,
                &horizon_window,
            );
            let cone_validation: ForecastConeSkeletonValidationReportV0 =
                validate_forecast_cone_skeleton(&cone, &cone_path.display().to_string());
            let envelope: ConsequenceEnvelopeReportV0 =
                build_consequence_envelope_from_forecast_cone(&cone);
            let envelope_validation: ConsequenceEnvelopeValidationReportV0 =
                validate_consequence_envelope_report(
                    &envelope,
                    &envelope_path.display().to_string(),
                );
            let failed = intent_validation.summary.result == "fail"
                || alignment_validation.summary.result == "fail"
                || estimate_validation.summary.result == "fail"
                || cone_validation.summary.result == "fail"
                || envelope_validation.summary.result == "fail";

            write_json(Some(intent_validation_path), &intent_validation)?;
            write_json(Some(alignment_validation_path), &alignment_validation)?;
            write_json(Some(estimate_path), &estimate)?;
            write_json(Some(estimate_validation_path), &estimate_validation)?;
            write_json(Some(cone_path), &cone)?;
            write_json(Some(cone_validation_path), &cone_validation)?;
            write_json(Some(envelope_path), &envelope)?;
            write_json(Some(envelope_validation_path), &envelope_validation)?;

            Ok(if failed {
                ExitCode::from(1)
            } else {
                ExitCode::SUCCESS
            })
        }
        Some(Command::OperationSupportEstimate {
            input,
            descriptor,
            fixture,
            out,
        }) => {
            if fixture {
                let estimate: OperationSupportEstimateV0 = static_operation_support_estimate();
                write_json(out, &estimate)?;
                return Ok(ExitCode::SUCCESS);
            }
            if let Some(descriptor_path) = descriptor {
                let descriptor: ArtifactDescriptorV0 = read_json(&descriptor_path)?;
                let estimate: OperationSupportEstimateV0 =
                    build_operation_support_estimate_from_descriptor(&descriptor);
                write_json(out, &estimate)?;
                return Ok(ExitCode::SUCCESS);
            }
            let estimate: OperationSupportEstimateV0 = input
                .as_ref()
                .map(read_json)
                .transpose()?
                .unwrap_or_else(static_operation_support_estimate);
            let input_path = input
                .as_ref()
                .map(|path| path.display().to_string())
                .unwrap_or_else(|| "static-operation-support-estimate".to_string());
            let validation: OperationSupportEstimateValidationReportV0 =
                validate_operation_support_estimate(&estimate, &input_path);
            let failed = validation.summary.result == "fail";
            write_json(out, &validation)?;
            Ok(if failed {
                ExitCode::from(1)
            } else {
                ExitCode::SUCCESS
            })
        }
        Some(Command::ForecastConeSkeleton {
            input,
            operation_support,
            horizon_steps,
            horizon_window,
            fixture,
            out,
        }) => {
            if fixture {
                let cone: ForecastConeSkeletonV0 = static_forecast_cone_skeleton();
                write_json(out, &cone)?;
                return Ok(ExitCode::SUCCESS);
            }
            if let Some(operation_support_path) = operation_support {
                let estimate: OperationSupportEstimateV0 = read_json(&operation_support_path)?;
                let cone: ForecastConeSkeletonV0 =
                    build_forecast_cone_skeleton_from_operation_support(
                        &estimate,
                        horizon_steps,
                        &horizon_window,
                    );
                write_json(out, &cone)?;
                return Ok(ExitCode::SUCCESS);
            }
            let cone: ForecastConeSkeletonV0 = input
                .as_ref()
                .map(read_json)
                .transpose()?
                .unwrap_or_else(static_forecast_cone_skeleton);
            let input_path = input
                .as_ref()
                .map(|path| path.display().to_string())
                .unwrap_or_else(|| "static-forecast-cone-skeleton".to_string());
            let validation: ForecastConeSkeletonValidationReportV0 =
                validate_forecast_cone_skeleton(&cone, &input_path);
            let failed = validation.summary.result == "fail";
            write_json(out, &validation)?;
            Ok(if failed {
                ExitCode::from(1)
            } else {
                ExitCode::SUCCESS
            })
        }
        Some(Command::ConsequenceEnvelope {
            input,
            forecast_cone,
            fixture,
            out,
        }) => {
            if fixture {
                let envelope: ConsequenceEnvelopeReportV0 = static_consequence_envelope_report();
                write_json(out, &envelope)?;
                return Ok(ExitCode::SUCCESS);
            }
            if let Some(forecast_cone_path) = forecast_cone {
                let cone: ForecastConeSkeletonV0 = read_json(&forecast_cone_path)?;
                let envelope: ConsequenceEnvelopeReportV0 =
                    build_consequence_envelope_from_forecast_cone(&cone);
                write_json(out, &envelope)?;
                return Ok(ExitCode::SUCCESS);
            }
            let envelope: ConsequenceEnvelopeReportV0 = input
                .as_ref()
                .map(read_json)
                .transpose()?
                .unwrap_or_else(static_consequence_envelope_report);
            let input_path = input
                .as_ref()
                .map(|path| path.display().to_string())
                .unwrap_or_else(|| "static-consequence-envelope".to_string());
            let validation: ConsequenceEnvelopeValidationReportV0 =
                validate_consequence_envelope_report(&envelope, &input_path);
            let failed = validation.summary.result == "fail";
            write_json(out, &validation)?;
            Ok(if failed {
                ExitCode::from(1)
            } else {
                ExitCode::SUCCESS
            })
        }
        Some(Command::SftReviewSummary {
            input,
            consequence_envelope,
            fixture,
            out,
        }) => {
            if fixture {
                let summary: SftReviewSummaryV0 = static_sft_review_summary();
                write_json(out, &summary)?;
                return Ok(ExitCode::SUCCESS);
            }
            if let Some(envelope_path) = consequence_envelope {
                let envelope: ConsequenceEnvelopeReportV0 = read_json(&envelope_path)?;
                let summary: SftReviewSummaryV0 =
                    build_sft_review_summary_from_consequence_envelope(&envelope);
                write_json(out, &summary)?;
                return Ok(ExitCode::SUCCESS);
            }
            let summary: SftReviewSummaryV0 = input
                .as_ref()
                .map(read_json)
                .transpose()?
                .unwrap_or_else(static_sft_review_summary);
            let input_path = input
                .as_ref()
                .map(|path| path.display().to_string())
                .unwrap_or_else(|| "static-sft-review-summary".to_string());
            let validation: SftReviewSummaryValidationReportV0 =
                validate_sft_review_summary(&summary, &input_path);
            let failed = validation.validation_summary.result == "fail";
            write_json(out, &validation)?;
            Ok(if failed {
                ExitCode::from(1)
            } else {
                ExitCode::SUCCESS
            })
        }
        Some(Command::SftForecast {
            artifact,
            artifact_format,
            artifact_kind,
            horizon_steps,
            horizon_window,
            out_dir,
        }) => {
            std::fs::create_dir_all(&out_dir)?;

            let artifact_path = artifact.display().to_string();
            let descriptor: ArtifactDescriptorV0 = match artifact_format.as_str() {
                "github-issue-json" => {
                    let value: serde_json::Value = read_json(&artifact)?;
                    build_artifact_descriptor_from_github_issue_json(&artifact_path, &value)
                }
                "ai-proposal-json" => {
                    let value: serde_json::Value = read_json(&artifact)?;
                    build_artifact_descriptor_from_ai_proposal_json(&artifact_path, &value)
                }
                _ => {
                    let contents = std::fs::read_to_string(&artifact)?;
                    build_artifact_descriptor_from_markdown(
                        &artifact_path,
                        &contents,
                        &artifact_kind,
                    )
                }
            };
            let descriptor_path = out_dir.join("artifact-descriptor.json");
            let descriptor_validation_path = out_dir.join("artifact-descriptor-validation.json");
            let descriptor_validation: ArtifactDescriptorValidationReportV0 =
                validate_artifact_descriptor_report(
                    &descriptor,
                    &descriptor_path.display().to_string(),
                );

            let estimate: OperationSupportEstimateV0 =
                build_operation_support_estimate_from_descriptor(&descriptor);
            let estimate_path = out_dir.join("operation-support-estimate.json");
            let estimate_validation_path =
                out_dir.join("operation-support-estimate-validation.json");
            let estimate_validation: OperationSupportEstimateValidationReportV0 =
                validate_operation_support_estimate(
                    &estimate,
                    &estimate_path.display().to_string(),
                );

            let cone: ForecastConeSkeletonV0 = build_forecast_cone_skeleton_from_operation_support(
                &estimate,
                horizon_steps,
                &horizon_window,
            );
            let cone_path = out_dir.join("forecast-cone-skeleton.json");
            let cone_validation_path = out_dir.join("forecast-cone-skeleton-validation.json");
            let cone_validation: ForecastConeSkeletonValidationReportV0 =
                validate_forecast_cone_skeleton(&cone, &cone_path.display().to_string());

            let envelope: ConsequenceEnvelopeReportV0 =
                build_consequence_envelope_from_forecast_cone(&cone);
            let envelope_path = out_dir.join("consequence-envelope-report.json");
            let envelope_validation_path = out_dir.join("consequence-envelope-validation.json");
            let envelope_validation: ConsequenceEnvelopeValidationReportV0 =
                validate_consequence_envelope_report(
                    &envelope,
                    &envelope_path.display().to_string(),
                );
            let review_summary: SftReviewSummaryV0 =
                build_sft_review_summary_from_consequence_envelope(&envelope);
            let review_summary_path = out_dir.join("sft-review-summary.json");
            let review_summary_validation_path = out_dir.join("sft-review-summary-validation.json");
            let review_summary_validation: SftReviewSummaryValidationReportV0 =
                validate_sft_review_summary(
                    &review_summary,
                    &review_summary_path.display().to_string(),
                );

            let failed = descriptor_validation.summary.result == "fail"
                || estimate_validation.summary.result == "fail"
                || cone_validation.summary.result == "fail"
                || envelope_validation.summary.result == "fail"
                || review_summary_validation.validation_summary.result == "fail";

            write_json(Some(descriptor_path), &descriptor)?;
            write_json(Some(descriptor_validation_path), &descriptor_validation)?;
            write_json(Some(estimate_path), &estimate)?;
            write_json(Some(estimate_validation_path), &estimate_validation)?;
            write_json(Some(cone_path), &cone)?;
            write_json(Some(cone_validation_path), &cone_validation)?;
            write_json(Some(envelope_path), &envelope)?;
            write_json(Some(envelope_validation_path), &envelope_validation)?;
            write_json(Some(review_summary_path), &review_summary)?;
            write_json(
                Some(review_summary_validation_path),
                &review_summary_validation,
            )?;

            Ok(if failed {
                ExitCode::from(1)
            } else {
                ExitCode::SUCCESS
            })
        }
        Some(Command::ForecastCalibrationHook {
            input,
            fixture,
            out,
        }) => {
            if fixture {
                let hook: ForecastCalibrationHookV0 = static_forecast_calibration_hook();
                write_json(out, &hook)?;
                return Ok(ExitCode::SUCCESS);
            }
            let hook: ForecastCalibrationHookV0 = input
                .as_ref()
                .map(read_json)
                .transpose()?
                .unwrap_or_else(static_forecast_calibration_hook);
            let input_path = input
                .as_ref()
                .map(|path| path.display().to_string())
                .unwrap_or_else(|| "static-forecast-calibration-hook".to_string());
            let validation: ForecastCalibrationHookValidationReportV0 =
                validate_forecast_calibration_hook(&hook, &input_path);
            let failed = validation.summary.result == "fail";
            write_json(out, &validation)?;
            Ok(if failed {
                ExitCode::from(1)
            } else {
                ExitCode::SUCCESS
            })
        }
        Some(Command::PrQualityAnalysis {
            input,
            fixture,
            out,
        }) => {
            if fixture {
                let report: PrQualityAnalysisReportV0 = static_pr_quality_analysis_report();
                write_json(out, &report)?;
                return Ok(ExitCode::SUCCESS);
            }
            let report: PrQualityAnalysisReportV0 = input
                .as_ref()
                .map(read_json)
                .transpose()?
                .unwrap_or_else(static_pr_quality_analysis_report);
            let input_path = input
                .as_ref()
                .map(|path| path.display().to_string())
                .unwrap_or_else(|| "static-pr-quality-analysis".to_string());
            let validation: PrQualityAnalysisValidationReportV0 =
                validate_pr_quality_analysis_report(&report, &input_path);
            let failed = validation.summary.result == "fail";
            write_json(out, &validation)?;
            Ok(if failed {
                ExitCode::from(1)
            } else {
                ExitCode::SUCCESS
            })
        }
        Some(Command::AatObservableBundle {
            input,
            fixture,
            out,
        }) => {
            if fixture {
                let bundle: AatObservableBundleV0 = static_aat_observable_bundle();
                write_json(out, &bundle)?;
                return Ok(ExitCode::SUCCESS);
            }
            let bundle: AatObservableBundleV0 = input
                .as_ref()
                .map(read_json)
                .transpose()?
                .unwrap_or_else(static_aat_observable_bundle);
            let input_path = input
                .as_ref()
                .map(|path| path.display().to_string())
                .unwrap_or_else(|| "static-aat-observable-bundle".to_string());
            let validation: AatObservableBundleValidationReportV0 =
                validate_aat_observable_bundle(&bundle, &input_path);
            let failed = validation.summary.result == "fail";
            write_json(out, &validation)?;
            Ok(if failed {
                ExitCode::from(1)
            } else {
                ExitCode::SUCCESS
            })
        }
        Some(Command::IntentCalibrationRecord {
            input,
            fixture,
            out,
        }) => {
            if fixture {
                let record: IntentCalibrationRecordV0 = static_intent_calibration_record();
                write_json(out, &record)?;
                return Ok(ExitCode::SUCCESS);
            }
            let record: IntentCalibrationRecordV0 = input
                .as_ref()
                .map(read_json)
                .transpose()?
                .unwrap_or_else(static_intent_calibration_record);
            let input_path = input
                .as_ref()
                .map(|path| path.display().to_string())
                .unwrap_or_else(|| "static-intent-calibration-record".to_string());
            let validation: IntentCalibrationValidationReportV0 =
                validate_intent_calibration_record(&record, &input_path);
            let failed = validation.summary.result == "fail";
            write_json(out, &validation)?;
            Ok(if failed {
                ExitCode::from(1)
            } else {
                ExitCode::SUCCESS
            })
        }
        Some(Command::AiProposalGovernance {
            input,
            descriptor,
            operation_support_id,
            consequence_envelope_id,
            fixture,
            out,
        }) => {
            if fixture {
                let governance: AiProposalGovernanceV0 = static_ai_proposal_governance();
                write_json(out, &governance)?;
                return Ok(ExitCode::SUCCESS);
            }
            if let Some(descriptor_path) = descriptor {
                let descriptor_value: ArtifactDescriptorV0 = read_json(&descriptor_path)?;
                let governance: AiProposalGovernanceV0 =
                    build_ai_proposal_governance_from_descriptor(
                        &descriptor_value,
                        operation_support_id.as_deref(),
                        consequence_envelope_id.as_deref(),
                    );
                write_json(out, &governance)?;
                return Ok(ExitCode::SUCCESS);
            }
            let governance: AiProposalGovernanceV0 = input
                .as_ref()
                .map(read_json)
                .transpose()?
                .unwrap_or_else(static_ai_proposal_governance);
            let input_path = input
                .as_ref()
                .map(|path| path.display().to_string())
                .unwrap_or_else(|| "static-ai-proposal-governance".to_string());
            let validation: AiProposalGovernanceValidationReportV0 =
                validate_ai_proposal_governance(&governance, &input_path);
            let failed = validation.summary.result == "fail";
            write_json(out, &validation)?;
            Ok(if failed {
                ExitCode::from(1)
            } else {
                ExitCode::SUCCESS
            })
        }
        Some(Command::ReportedAxesCatalog { out }) => {
            let catalog: DetectableValuesReportedAxesCatalogV0 =
                static_detectable_values_reported_axes_catalog();
            write_json(out, &catalog)?;
            Ok(ExitCode::SUCCESS)
        }
        Some(Command::PolicyDecision {
            feature_report,
            policy,
            out,
        }) => {
            let report_input: FeatureExtensionReportV0 = read_json(&feature_report)?;
            let organization_policy: OrganizationPolicyV0 = policy
                .as_ref()
                .map(read_json)
                .transpose()?
                .unwrap_or_else(static_organization_policy);
            let policy_path = policy
                .as_ref()
                .map(|path| path.display().to_string())
                .unwrap_or_else(|| "static-organization-policy".to_string());
            let report: PolicyDecisionReportV0 = build_policy_decision_report(
                &report_input,
                &feature_report.display().to_string(),
                &organization_policy,
                &policy_path,
            );
            let failed = report.summary.decision == "fail";
            write_json(out, &report)?;
            Ok(if failed {
                ExitCode::from(1)
            } else {
                ExitCode::SUCCESS
            })
        }
        Some(Command::ReportArtifacts { input, out }) => {
            let manifest: ReportArtifactRetentionManifestV0 = input
                .as_ref()
                .map(read_json)
                .transpose()?
                .unwrap_or_else(static_report_artifact_retention_manifest);
            let input_path = input
                .as_ref()
                .map(|path| path.display().to_string())
                .unwrap_or_else(|| "static-report-artifact-retention-manifest".to_string());
            let report: ReportArtifactRetentionValidationReportV0 =
                validate_report_artifact_retention_report(&manifest, &input_path);
            let failed = report.summary.result == "fail";
            write_json(out, &report)?;
            Ok(if failed {
                ExitCode::from(1)
            } else {
                ExitCode::SUCCESS
            })
        }
        Some(Command::PrComment {
            feature_report,
            policy_decision,
            out,
        }) => {
            let report: FeatureExtensionReportV0 = read_json(&feature_report)?;
            let policy: Option<PolicyDecisionReportV0> =
                policy_decision.as_ref().map(read_json).transpose()?;
            let markdown = render_pr_comment_markdown(&report, policy.as_ref());
            write_text(out, &markdown)?;
            Ok(ExitCode::SUCCESS)
        }
        Some(Command::BaselineSuppression {
            baseline_feature_report,
            current_feature_report,
            baseline_policy_decision,
            current_policy_decision,
            retention_manifest,
            suppression,
            accepted_risk,
            out,
        }) => {
            let baseline_report: FeatureExtensionReportV0 = read_json(&baseline_feature_report)?;
            let current_report: FeatureExtensionReportV0 = read_json(&current_feature_report)?;
            let baseline_policy: Option<PolicyDecisionReportV0> = baseline_policy_decision
                .as_ref()
                .map(read_json)
                .transpose()?;
            let current_policy: Option<PolicyDecisionReportV0> = current_policy_decision
                .as_ref()
                .map(read_json)
                .transpose()?;
            let retention: Option<ReportArtifactRetentionManifestV0> =
                retention_manifest.as_ref().map(read_json).transpose()?;
            let suppressions = read_risk_dispositions(&suppression)?;
            let accepted_risks = read_risk_dispositions(&accepted_risk)?;
            let report = build_baseline_suppression_report(
                &baseline_report,
                &baseline_feature_report.display().to_string(),
                &current_report,
                &current_feature_report.display().to_string(),
                baseline_policy.as_ref(),
                baseline_policy_decision
                    .as_ref()
                    .map(|path| path.display().to_string())
                    .as_deref(),
                current_policy.as_ref(),
                current_policy_decision
                    .as_ref()
                    .map(|path| path.display().to_string())
                    .as_deref(),
                retention.as_ref(),
                retention_manifest
                    .as_ref()
                    .map(|path| path.display().to_string())
                    .as_deref(),
                &suppressions,
                &accepted_risks,
            );
            let failed = report.summary.result == "fail";
            write_json(out, &report)?;
            Ok(if failed {
                ExitCode::from(1)
            } else {
                ExitCode::SUCCESS
            })
        }
        Some(Command::SchemaCatalog { out }) => {
            let catalog: SchemaVersionCatalogV0 = static_schema_version_catalog();
            write_json(out, &catalog)?;
            Ok(ExitCode::SUCCESS)
        }
        Some(Command::SchemaCompatibility {
            before,
            after,
            catalog,
            out,
        }) => {
            let before_value: serde_json::Value = read_json(&before)?;
            let after_value: serde_json::Value = read_json(&after)?;
            let catalog_value: SchemaVersionCatalogV0 = catalog
                .as_ref()
                .map(read_json)
                .transpose()?
                .unwrap_or_else(static_schema_version_catalog);
            let report: SchemaCompatibilityCheckReportV0 = build_schema_compatibility_check_report(
                &before_value,
                &before.display().to_string(),
                &after_value,
                &after.display().to_string(),
                &catalog_value,
            );
            let failed = report.summary.result != "pass";
            write_json(out, &report)?;
            Ok(if failed {
                ExitCode::from(1)
            } else {
                ExitCode::SUCCESS
            })
        }
        None => {
            let document = match args.language.as_str() {
                "lean" => {
                    if policy_schema_version(args.policy.as_deref())?.as_deref()
                        == Some("architecture-policy-v0")
                    {
                        let mut document = extract_sig0_with_runtime(
                            &args.root,
                            None,
                            args.runtime_edges.as_deref(),
                        )?;
                        if let Some(policy_path) = args.policy.as_deref() {
                            let architecture_policy = read_architecture_policy(policy_path)?;
                            apply_architecture_policy_to_sig0(
                                &mut document,
                                &architecture_policy,
                                Some(&policy_path.display().to_string()),
                            );
                        }
                        document
                    } else {
                        extract_sig0_with_runtime(
                            &args.root,
                            args.policy.as_deref(),
                            args.runtime_edges.as_deref(),
                        )?
                    }
                }
                "python" => {
                    if args.runtime_edges.is_some() {
                        return Err(
                            "runtime edge projection is not part of python-import-graph-v0".into(),
                        );
                    }
                    let mut document =
                        extract_python_sig0(&args.root, &args.source_roots, &args.package_roots)?;
                    if let Some(policy_path) = args.policy.as_deref() {
                        let architecture_policy = read_architecture_policy(policy_path)?;
                        apply_architecture_policy_to_sig0(
                            &mut document,
                            &architecture_policy,
                            Some(&policy_path.display().to_string()),
                        );
                    }
                    document
                }
                _ => unreachable!("clap restricts language values"),
            };
            write_json(args.out, &document)?;
            Ok(ExitCode::SUCCESS)
        }
    }
}

fn policy_schema_version(path: Option<&Path>) -> Result<Option<String>, Box<dyn Error>> {
    let Some(path) = path else {
        return Ok(None);
    };
    let source = std::fs::read_to_string(path)?;
    let value: serde_json::Value = serde_json::from_str(&source)?;
    Ok(value
        .get("schemaVersion")
        .and_then(|value| value.as_str())
        .map(str::to_string))
}

fn write_json<T: serde::Serialize>(out: Option<PathBuf>, value: &T) -> Result<(), Box<dyn Error>> {
    match out {
        Some(path) => {
            if let Some(parent) = path.parent() {
                if !parent.as_os_str().is_empty() {
                    std::fs::create_dir_all(parent)?;
                }
            }
            let mut file = File::create(path)?;
            serde_json::to_writer_pretty(&mut file, value)?;
            writeln!(file)?;
        }
        None => {
            let stdout = io::stdout();
            let mut handle = stdout.lock();
            serde_json::to_writer_pretty(&mut handle, value)?;
            writeln!(handle)?;
        }
    }
    Ok(())
}

fn write_text(out: Option<PathBuf>, value: &str) -> Result<(), Box<dyn Error>> {
    match out {
        Some(path) => {
            if let Some(parent) = path.parent() {
                if !parent.as_os_str().is_empty() {
                    std::fs::create_dir_all(parent)?;
                }
            }
            let mut file = File::create(path)?;
            file.write_all(value.as_bytes())?;
        }
        None => {
            let stdout = io::stdout();
            let mut handle = stdout.lock();
            handle.write_all(value.as_bytes())?;
        }
    }
    Ok(())
}

fn read_json<T: serde::de::DeserializeOwned>(path: &PathBuf) -> Result<T, Box<dyn Error>> {
    Ok(serde_json::from_reader(File::open(path)?)?)
}

fn resolve_archmap_sidecar_path(archmap_path: &Path, sidecar_path: &str) -> Option<PathBuf> {
    let raw_path = PathBuf::from(sidecar_path);
    if raw_path.is_absolute() {
        return raw_path.exists().then_some(raw_path);
    }

    if let Ok(current_dir) = std::env::current_dir() {
        let candidate = current_dir.join(&raw_path);
        if candidate.exists() {
            return Some(candidate);
        }
    }

    let archmap_parent = archmap_path.parent()?;
    let local_candidate = archmap_parent.join(&raw_path);
    if local_candidate.exists() {
        return Some(local_candidate);
    }
    for ancestor in archmap_parent.ancestors() {
        let candidate = ancestor.join(&raw_path);
        if candidate.exists() {
            return Some(candidate);
        }
    }
    None
}

fn read_risk_dispositions(paths: &[PathBuf]) -> Result<Vec<RiskDispositionV0>, Box<dyn Error>> {
    let mut dispositions = Vec::new();
    for path in paths {
        let value: serde_json::Value = read_json(path)?;
        if value.is_array() {
            let mut batch: Vec<RiskDispositionV0> = serde_json::from_value(value)?;
            dispositions.append(&mut batch);
        } else {
            dispositions.push(serde_json::from_value(value)?);
        }
    }
    Ok(dispositions)
}
