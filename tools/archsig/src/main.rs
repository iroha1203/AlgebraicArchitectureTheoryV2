use std::error::Error;
use std::fs::File;
use std::io::{self, Write};
use std::path::PathBuf;
use std::process::ExitCode;

use archsig::{
    AirDocumentInput, AirDocumentV0, AirValidationReport, ComponentUniverseValidationReport,
    DEFAULT_UNIVERSE_MODE, EmpiricalDatasetInput, FeatureExtensionReportV0, RepositoryRevisionRef,
    ScanMetadata, Sig0Document, SignatureDiffReportV0, SignatureSnapshotStoreRecordV0,
    SnapshotRecordInput, SnapshotRepositoryRef, TheoremPreconditionCheckReportV0,
    build_air_document, build_empirical_dataset, build_feature_extension_report,
    build_pr_metadata_from_github_files, build_signature_diff_report,
    build_signature_snapshot_record, build_theorem_precondition_check_report,
    extract_relation_complexity_observation_from_file, extract_sig0_with_runtime,
    validate_air_document_report, validate_component_universe_report,
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
        None => {
            let document = extract_sig0_with_runtime(
                &args.root,
                args.policy.as_deref(),
                args.runtime_edges.as_deref(),
            )?;
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

fn read_json<T: serde::de::DeserializeOwned>(path: &PathBuf) -> Result<T, Box<dyn Error>> {
    Ok(serde_json::from_reader(File::open(path)?)?)
}
