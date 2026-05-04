use std::error::Error;
use std::fs::File;
use std::io::{self, Write};
use std::path::PathBuf;
use std::process::ExitCode;

use archsig::{
    AirDocumentInput, AirDocumentV0, AirValidationReport, ComponentUniverseValidationReport,
    DEFAULT_UNIVERSE_MODE, EmpiricalDatasetInput, FeatureExtensionReportV0,
    LawPolicyTemplateRegistryV0, LawPolicyTemplateRegistryValidationReportV0,
    NoSolutionCertificateV0, NoSolutionCertificateValidationReportV0, OrganizationPolicyV0,
    OrganizationPolicyValidationReportV0, PolicyDecisionReportV0, RepairRuleRegistryV0,
    RepairRuleRegistryValidationReportV0, ReportArtifactRetentionManifestV0,
    ReportArtifactRetentionValidationReportV0, RepositoryRevisionRef, RiskDispositionV0,
    ScanMetadata, Sig0Document, SignatureDiffReportV0, SignatureSnapshotStoreRecordV0,
    SnapshotRecordInput, SnapshotRepositoryRef, SynthesisConstraintArtifactV0,
    SynthesisConstraintValidationReportV0, TheoremPreconditionCheckReportV0, build_air_document,
    build_baseline_suppression_report, build_empirical_dataset,
    build_feature_extension_dataset_from_files, build_feature_extension_report,
    build_outcome_linkage_dataset_from_files, build_policy_decision_report,
    build_pr_history_dataset_from_github_files, build_pr_metadata_from_github_files,
    build_signature_diff_report, build_signature_snapshot_record,
    build_theorem_precondition_check_report, extract_python_sig0,
    extract_relation_complexity_observation_from_file, extract_sig0_with_runtime,
    render_pr_comment_markdown, static_law_policy_template_registry,
    static_no_solution_certificate, static_organization_policy, static_repair_rule_registry,
    static_report_artifact_retention_manifest, static_synthesis_constraint_artifact,
    validate_air_document_report, validate_component_universe_report,
    validate_law_policy_template_registry_report, validate_no_solution_certificate_report,
    validate_organization_policy_report, validate_repair_rule_registry_report,
    validate_report_artifact_retention_report, validate_synthesis_constraint_artifact_report,
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
            out,
        }) => {
            let document: Sig0Document = read_json(&sig0)?;
            let validation_report: Option<ComponentUniverseValidationReport> =
                validation.as_ref().map(read_json).transpose()?;
            let diff_report: Option<SignatureDiffReportV0> =
                diff.as_ref().map(read_json).transpose()?;
            let pr_metadata_document: Option<EmpiricalDatasetInput> =
                pr_metadata.as_ref().map(read_json).transpose()?;
            let air = build_air_document(
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
