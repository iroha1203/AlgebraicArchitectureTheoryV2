use std::error::Error;
use std::fs::File;
use std::io::{self, Write};
use std::path::PathBuf;
use std::process::ExitCode;

use archsig::{
    AirDocumentInput, AirDocumentV0, AirValidationReport, ArchitectureDynamicsMetricsReportV0,
    ArchitectureDynamicsMetricsReportValidationReportV0, CalibrationReviewRecordV0,
    ComponentUniverseValidationReport, CustomRulePluginRegistryV0,
    CustomRulePluginRegistryValidationReportV0, DEFAULT_UNIVERSE_MODE,
    DetectableValuesReportedAxesCatalogV0, DriftLedgerAggregationWindowV0,
    DynamicsMeasurementContractV0, DynamicsMeasurementContractValidationReportV0,
    EmpiricalDatasetInput, FeatureExtensionReportV0, FrameworkAdapterEvidenceV0,
    HypothesisRefreshCycleV0, IncidentCorrelationMonitorV0, LawPolicyTemplateRegistryV0,
    LawPolicyTemplateRegistryValidationReportV0, MeasurementUnitRegistryV0,
    MeasurementUnitRegistryValidationReportV0, NoSolutionCertificateV0,
    NoSolutionCertificateValidationReportV0, OrganizationPolicyV0,
    OrganizationPolicyValidationReportV0, OwnershipBoundaryMonitorV0, PolicyDecisionReportV0,
    PrForceReportV0, PrForceReportValidationReportV0, RepairAdoptionRecordV0, RepairRuleRegistryV0,
    RepairRuleRegistryValidationReportV0, ReportArtifactRetentionManifestV0,
    ReportArtifactRetentionValidationReportV0, ReportOutcomeDailyLedgerInput,
    RepositoryRevisionRef, RiskDispositionV0, ScanMetadata, SchemaCompatibilityCheckReportV0,
    SchemaVersionCatalogV0, Sig0Document, SignatureDiffReportV0, SignatureSnapshotStoreRecordV0,
    SignatureTrajectoryReportV0, SignatureTrajectoryReportValidationReportV0, SnapshotRecordInput,
    SnapshotRepositoryRef, SynthesisConstraintArtifactV0, SynthesisConstraintValidationReportV0,
    TeamThresholdPolicyV0, TheoremPreconditionCheckReportV0, attach_framework_adapter_evidence,
    build_air_document, build_baseline_suppression_report, build_empirical_dataset,
    build_feature_extension_dataset_from_files, build_feature_extension_report,
    build_outcome_linkage_dataset_from_files, build_policy_decision_report,
    build_pr_history_dataset_from_github_files, build_pr_metadata_from_github_files,
    build_report_outcome_daily_ledger_from_files, build_schema_compatibility_check_report,
    build_signature_diff_report, build_signature_snapshot_record,
    build_theorem_precondition_check_report, extract_python_sig0,
    extract_relation_complexity_observation_from_file, extract_sig0_with_runtime,
    render_pr_comment_markdown, static_architecture_dynamics_metrics_report,
    static_calibration_review_record, static_custom_rule_plugin_registry,
    static_detectable_values_reported_axes_catalog, static_dynamics_measurement_contract,
    static_hypothesis_refresh_cycle, static_incident_correlation_monitor,
    static_law_policy_template_registry, static_measurement_unit_registry,
    static_no_solution_certificate, static_organization_policy, static_ownership_boundary_monitor,
    static_pr_force_report, static_repair_adoption_record, static_repair_rule_registry,
    static_report_artifact_retention_manifest, static_schema_version_catalog,
    static_signature_trajectory_report, static_synthesis_constraint_artifact,
    static_team_threshold_policy, validate_air_document_report,
    validate_architecture_dynamics_metrics_report, validate_component_universe_report,
    validate_custom_rule_plugin_registry_report, validate_dynamics_measurement_contract_report,
    validate_law_policy_template_registry_report, validate_measurement_unit_registry_report,
    validate_no_solution_certificate_report, validate_organization_policy_report,
    validate_pr_force_report, validate_repair_rule_registry_report,
    validate_report_artifact_retention_report, validate_signature_trajectory_report,
    validate_synthesis_constraint_artifact_report,
};
use clap::{Parser, Subcommand};

#[derive(Debug, Parser)]
#[command(version, about = "Extract ArchSig JSON from Lean module imports")]
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
                "lean" => extract_sig0_with_runtime(
                    &args.root,
                    args.policy.as_deref(),
                    args.runtime_edges.as_deref(),
                )?,
                "python" => {
                    if args.policy.is_some() {
                        return Err(
                            "Python policy measurement is tracked by the Sig0 / AIR normalization work"
                                .into(),
                        );
                    }
                    if args.runtime_edges.is_some() {
                        return Err(
                            "runtime edge projection is not part of python-import-graph-v0".into(),
                        );
                    }
                    extract_python_sig0(&args.root, &args.source_roots, &args.package_roots)?
                }
                _ => unreachable!("clap restricts language values"),
            };
            write_json(args.out, &document)?;
            Ok(ExitCode::SUCCESS)
        }
    }
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
