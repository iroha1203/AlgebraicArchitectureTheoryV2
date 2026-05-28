use std::collections::BTreeSet;
use std::error::Error;
use std::fs::File;
use std::io::{self, Write};
use std::path::{Path, PathBuf};
use std::process::ExitCode;

use archsig::{
    AAT_OBSERVABLE_BUNDLE_SCHEMA_VERSION, ARCHMAP_SCHEMA_VERSION, AatAnalyticAxisV0,
    AatConceptMappingV0, AatCoverageBoundaryV0, AatFeatureExtensionEvidenceV0,
    AatLlmReviewSurfaceV0, AatObservableBundleV0, AatObservableBundleValidationReportV0,
    AatObservableSourceRefV0, AatObservedAxisV0, AatOperationCandidateV0,
    AatProjectionObservationEvidenceV0, AatRepairSynthesisEvidenceV0, AatResponsibilityBoundaryV0,
    AatReviewActionV0, AatSelectedUniverseV0, AatSemanticDiagramEvidenceV0,
    AatStateEffectLawEvidenceV0, AatTheoremBoundaryV0, AatWitnessCatalogEntryV0, AirDocumentInput,
    AirDocumentV0, AirValidationReport, ArchMapDocumentV0, ArchMapSourceInventoryInput,
    ArchMapSourceInventoryV0, ArchMapValidationReportV0, ArchitecturePolicyV0,
    ArchitecturePolicyValidationReportV0, ComponentUniverseValidationReport,
    CustomRulePluginRegistryV0, CustomRulePluginRegistryValidationReportV0, DEFAULT_UNIVERSE_MODE,
    DetectableValuesReportedAxesCatalogV0, EmpiricalDatasetInput, FeatureExtensionReportV0,
    FrameworkAdapterEvidenceV0, LawPolicyDocumentV0, LawPolicyTemplateRegistryV0,
    LawPolicyTemplateRegistryValidationReportV0, LawViolationReportV0, MeasurementUnitRegistryV0,
    MeasurementUnitRegistryValidationReportV0, NoSolutionCertificateV0,
    NoSolutionCertificateValidationReportV0, OrganizationPolicyV0,
    OrganizationPolicyValidationReportV0, PolicyDecisionReportV0, PrQualityAnalysisReportV0,
    PrQualityAnalysisValidationReportV0, RepairRuleRegistryV0,
    RepairRuleRegistryValidationReportV0, ReportArtifactRetentionManifestV0,
    ReportArtifactRetentionValidationReportV0, RepositoryRevisionRef, RiskDispositionV0,
    ScanMetadata, SchemaCompatibilityCheckReportV0, SchemaVersionCatalogV0, Sig0Document,
    SignatureDiffReportV0, SignatureSnapshotStoreRecordV0, SnapshotRecordInput,
    SnapshotRepositoryRef, SynthesisConstraintArtifactV0, SynthesisConstraintValidationReportV0,
    TheoremPreconditionCheckReportV0, apply_architecture_policy_to_sig0,
    attach_framework_adapter_evidence, build_air_document, build_air_from_archmap,
    build_archsig_analysis_packet, build_baseline_suppression_report,
    build_feature_extension_report, build_feature_extension_report_with_archmap_diagnostics,
    build_law_violation_report, build_policy_decision_report,
    build_schema_compatibility_check_report, build_signature_diff_report,
    build_signature_snapshot_record, build_theorem_precondition_check_report, extract_python_sig0,
    extract_relation_complexity_observation_from_file, extract_sig0_with_runtime,
    read_architecture_policy, render_pr_comment_markdown, static_aat_observable_bundle,
    static_custom_rule_plugin_registry, static_detectable_values_reported_axes_catalog,
    static_law_policy, static_law_policy_template_registry, static_measurement_unit_registry,
    static_no_solution_certificate, static_organization_policy, static_pr_quality_analysis_report,
    static_repair_rule_registry, static_report_artifact_retention_manifest,
    static_schema_version_catalog, static_synthesis_constraint_artifact,
    validate_aat_observable_bundle, validate_air_document_report,
    validate_architecture_policy_report, validate_archmap_report,
    validate_archsig_analysis_packet_report, validate_component_universe_report,
    validate_custom_rule_plugin_registry_report, validate_law_policy_report,
    validate_law_policy_template_registry_report, validate_measurement_unit_registry_report,
    validate_no_solution_certificate_report, validate_organization_policy_report,
    validate_pr_quality_analysis_report, validate_repair_rule_registry_report,
    validate_report_artifact_retention_report, validate_synthesis_constraint_artifact_report,
};
use clap::{Parser, Subcommand};

#[derive(Debug, Parser)]
#[command(
    version,
    about = "Validate LLM-native ArchMap, LawPolicy, and ArchSig analysis artifacts"
)]
struct Args {
    #[command(subcommand)]
    command: Option<Command>,
}

#[derive(Debug, Subcommand)]
enum Command {
    /// Run a bounded language adapter scan and emit Sig0 evidence.
    AdapterScan {
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
    },

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

    /// Validate or emit a LawPolicy artifact for LLM-native ArchSig analysis.
    LawPolicy {
        /// Optional LawPolicy JSON path. If omitted, the static fixture policy is validated.
        #[arg(long)]
        input: Option<PathBuf>,

        /// Emit the canonical law-policy-v0 fixture instead of a validation report.
        #[arg(long)]
        fixture: bool,

        /// Output LawPolicy fixture or validation report JSON path. If omitted, JSON is written to stdout.
        #[arg(long)]
        out: Option<PathBuf>,
    },

    /// Build an ArchSig analysis packet from ArchMap + LawPolicy.
    ArchsigAnalysis {
        /// Input ArchMap observation artifact path.
        #[arg(long)]
        archmap: PathBuf,

        /// Input LawPolicy artifact path.
        #[arg(long = "law-policy")]
        law_policy: PathBuf,

        /// Output archsig-analysis-packet-v0 JSON path. If omitted, JSON is written to stdout.
        #[arg(long)]
        out: Option<PathBuf>,

        /// Optional output validation report path.
        #[arg(long = "validation-out")]
        validation_out: Option<PathBuf>,

        /// Optional LLM interpretation packet output path. This writes the same structured packet for LLM reading.
        #[arg(long = "llm-interpretation-out")]
        llm_interpretation_out: Option<PathBuf>,
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

    /// Build the ArchMap-primary review workflow artifacts.
    ArchmapWorkflow {
        /// Input ArchMap JSON path.
        #[arg(long)]
        archmap: PathBuf,

        /// Optional Sig0 adapter evidence used only for conflict checks.
        #[arg(long)]
        sig0: Option<PathBuf>,

        /// Output directory for workflow artifacts.
        #[arg(long = "out-dir")]
        out_dir: PathBuf,

        /// Treat measured AIR claims without evidence refs as validation failures.
        #[arg(long)]
        strict_measured_evidence: bool,
    },

    /// Run the LLM-native ArchMap -> LawPolicy -> ArchSig analysis workflow.
    LlmNativeWorkflow {
        /// Input ArchMap observation artifact path.
        #[arg(long)]
        archmap: PathBuf,

        /// Input LawPolicy artifact path.
        #[arg(long = "law-policy")]
        law_policy: PathBuf,

        /// Output directory for LLM-native workflow artifacts.
        #[arg(long = "out-dir")]
        out_dir: PathBuf,
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
        Some(Command::AdapterScan {
            root,
            out,
            policy,
            runtime_edges,
            language,
            source_roots,
            package_roots,
        }) => {
            let document = build_adapter_sig0(
                &root,
                policy.as_deref(),
                runtime_edges.as_deref(),
                &language,
                &source_roots,
                &package_roots,
            )?;
            write_json(out, &document)?;
            Ok(ExitCode::SUCCESS)
        }
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
        Some(Command::LawPolicy {
            input,
            fixture,
            out,
        }) => {
            if fixture {
                let policy = static_law_policy();
                write_json(out, &policy)?;
                return Ok(ExitCode::SUCCESS);
            }
            let policy: LawPolicyDocumentV0 = input
                .as_ref()
                .map(read_json)
                .transpose()?
                .unwrap_or_else(static_law_policy);
            let input_path = input
                .as_ref()
                .map(|path| path.display().to_string())
                .unwrap_or_else(|| "static-law-policy".to_string());
            let report = validate_law_policy_report(&policy, &input_path);
            let failed = report.summary.result == "fail";
            write_json(out, &report)?;
            Ok(if failed {
                ExitCode::from(1)
            } else {
                ExitCode::SUCCESS
            })
        }
        Some(Command::ArchsigAnalysis {
            archmap,
            law_policy,
            out,
            validation_out,
            llm_interpretation_out,
        }) => {
            let archmap_document: ArchMapDocumentV0 = read_json(&archmap)?;
            let law_policy_document: LawPolicyDocumentV0 = read_json(&law_policy)?;
            let packet = build_archsig_analysis_packet(
                &archmap_document,
                &law_policy_document,
                Some(&archmap.display().to_string()),
                Some(&law_policy.display().to_string()),
            );
            let validation =
                validate_archsig_analysis_packet_report(&packet, "archsig-analysis-packet");
            let failed = validation.summary.result == "fail";
            if let Some(path) = validation_out {
                write_json(Some(path), &validation)?;
            }
            if let Some(path) = llm_interpretation_out {
                write_json(Some(path), &packet)?;
            }
            write_json(out, &packet)?;
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
                    "produce archmap-observation-map-v0 JSON with atomObservations, moleculeObservations, semanticObservations, observationGaps, projectionInfo, concernHints, provenance, and nonConclusions",
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
        Some(Command::ArchmapWorkflow {
            archmap,
            sig0,
            out_dir,
            strict_measured_evidence,
        }) => {
            let report_path = out_dir.join("archmap-validation.json");
            let air_path = out_dir.join("air.json");
            let air_validation_path = out_dir.join("air-validation.json");
            let theorem_check_path = out_dir.join("theorem-precondition-check.json");
            let feature_report_path = out_dir.join("feature-report.json");
            let observable_bundle_path = out_dir.join("aat-observable-bundle.json");
            let observable_validation_path = out_dir.join("aat-observable-bundle-validation.json");

            let document: ArchMapDocumentV0 = read_json(&archmap)?;
            let sig0_document: Option<Sig0Document> = sig0.as_ref().map(read_json).transpose()?;
            let source_inventory_path = document
                .source_inventory_ref
                .as_ref()
                .and_then(|source_inventory_ref| source_inventory_ref.path.as_deref());
            let mut source_inventory_document: Option<ArchMapSourceInventoryV0> = None;
            let mut source_inventory_error: Option<String> = None;
            if let Some(path) = source_inventory_path {
                match resolve_archmap_sidecar_path(&archmap, path) {
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
            let archmap_report = validate_archmap_report(
                &document,
                &archmap.display().to_string(),
                sig0_document.as_ref(),
                source_inventory,
            );
            let archmap_failed = archmap_report.summary.result == "fail";
            write_json(Some(report_path.clone()), &archmap_report)?;

            let air = build_air_from_archmap(
                &document,
                &archmap.display().to_string(),
                sig0_document.as_ref(),
            );
            write_json(Some(air_path.clone()), &air)?;

            let air_validation = validate_air_document_report(
                &air,
                &air_path.display().to_string(),
                strict_measured_evidence,
            );
            let air_failed = air_validation.summary.result == "fail";
            write_json(Some(air_validation_path.clone()), &air_validation)?;

            let theorem_check =
                build_theorem_precondition_check_report(&air, &air_path.display().to_string());
            write_json(Some(theorem_check_path.clone()), &theorem_check)?;

            let feature_report = build_feature_extension_report_with_archmap_diagnostics(
                &air,
                &air_path.display().to_string(),
                &archmap_report.homomorphism_diagnostics,
            );
            write_json(Some(feature_report_path.clone()), &feature_report)?;

            let observable_bundle = observable_bundle_from_archmap_workflow(
                &document,
                &air,
                &archmap_report,
                &theorem_check,
                &feature_report,
                &archmap,
                &report_path,
                &air_path,
                &air_validation_path,
                &theorem_check_path,
                &feature_report_path,
            );
            write_json(Some(observable_bundle_path.clone()), &observable_bundle)?;
            let observable_validation = validate_aat_observable_bundle(
                &observable_bundle,
                &observable_bundle_path.display().to_string(),
            );
            let observable_failed = observable_validation.summary.result == "fail";
            write_json(Some(observable_validation_path), &observable_validation)?;

            Ok(if archmap_failed || air_failed || observable_failed {
                ExitCode::from(1)
            } else {
                ExitCode::SUCCESS
            })
        }
        Some(Command::LlmNativeWorkflow {
            archmap,
            law_policy,
            out_dir,
        }) => {
            let archmap_validation_path = out_dir.join("archmap-validation.json");
            let law_policy_validation_path = out_dir.join("law-policy-validation.json");
            let analysis_packet_path = out_dir.join("archsig-analysis-packet.json");
            let analysis_validation_path = out_dir.join("archsig-analysis-validation.json");
            let llm_interpretation_path = out_dir.join("llm-interpretation-packet.json");

            let archmap_document: ArchMapDocumentV0 = read_json(&archmap)?;
            let source_inventory_path = archmap_document
                .source_inventory_ref
                .as_ref()
                .and_then(|source_inventory_ref| source_inventory_ref.path.as_deref());
            let mut source_inventory_document: Option<ArchMapSourceInventoryV0> = None;
            let mut source_inventory_error: Option<String> = None;
            if let Some(path) = source_inventory_path {
                match resolve_archmap_sidecar_path(&archmap, path) {
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
            let archmap_validation = validate_archmap_report(
                &archmap_document,
                &archmap.display().to_string(),
                None,
                source_inventory,
            );
            let archmap_failed = archmap_validation.summary.result == "fail";
            write_json(Some(archmap_validation_path), &archmap_validation)?;

            let law_policy_document: LawPolicyDocumentV0 = read_json(&law_policy)?;
            let law_policy_validation =
                validate_law_policy_report(&law_policy_document, &law_policy.display().to_string());
            let law_policy_failed = law_policy_validation.summary.result == "fail";
            write_json(Some(law_policy_validation_path), &law_policy_validation)?;

            let analysis_packet = build_archsig_analysis_packet(
                &archmap_document,
                &law_policy_document,
                Some(&archmap.display().to_string()),
                Some(&law_policy.display().to_string()),
            );
            write_json(Some(analysis_packet_path.clone()), &analysis_packet)?;
            write_json(Some(llm_interpretation_path), &analysis_packet)?;
            let analysis_validation = validate_archsig_analysis_packet_report(
                &analysis_packet,
                &analysis_packet_path.display().to_string(),
            );
            let analysis_failed = analysis_validation.summary.result == "fail";
            write_json(Some(analysis_validation_path), &analysis_validation)?;

            Ok(if archmap_failed || law_policy_failed || analysis_failed {
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
            Err("ArchSig is ArchMap-primary; use `archsig archmap-workflow` for review artifacts or `archsig adapter-scan` for bounded Lean/Python evidence.".into())
        }
    }
}

fn build_adapter_sig0(
    root: &Path,
    policy: Option<&Path>,
    runtime_edges: Option<&Path>,
    language: &str,
    source_roots: &[PathBuf],
    package_roots: &[PathBuf],
) -> Result<Sig0Document, Box<dyn Error>> {
    let document = match language {
        "lean" => {
            if policy_schema_version(policy)?.as_deref() == Some("architecture-policy-v0") {
                let mut document = extract_sig0_with_runtime(root, None, runtime_edges)?;
                if let Some(policy_path) = policy {
                    let architecture_policy = read_architecture_policy(policy_path)?;
                    apply_architecture_policy_to_sig0(
                        &mut document,
                        &architecture_policy,
                        Some(&policy_path.display().to_string()),
                    );
                }
                document
            } else {
                extract_sig0_with_runtime(root, policy, runtime_edges)?
            }
        }
        "python" => {
            if runtime_edges.is_some() {
                return Err("runtime edge projection is not part of python-import-graph-v0".into());
            }
            let mut document = extract_python_sig0(root, source_roots, package_roots)?;
            if let Some(policy_path) = policy {
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
    Ok(document)
}

fn observable_bundle_from_archmap_workflow(
    archmap: &ArchMapDocumentV0,
    air: &AirDocumentV0,
    archmap_validation: &ArchMapValidationReportV0,
    theorem_check: &TheoremPreconditionCheckReportV0,
    feature_report: &FeatureExtensionReportV0,
    archmap_path: &Path,
    archmap_validation_path: &Path,
    air_path: &Path,
    air_validation_path: &Path,
    theorem_check_path: &Path,
    feature_report_path: &Path,
) -> AatObservableBundleV0 {
    let source_refs = vec![
        AatObservableSourceRefV0 {
            source_ref_id: "source:archmap:primary".to_string(),
            artifact_kind: "archmap".to_string(),
            schema_version: ARCHMAP_SCHEMA_VERSION.to_string(),
            path: archmap_path.display().to_string(),
            retained_fields: vec![
                "sourceUniverse".to_string(),
                "atomObservations".to_string(),
                "moleculeObservations".to_string(),
                "semanticObservations".to_string(),
                "observationGaps".to_string(),
                "projectionInfo".to_string(),
                "concernHints".to_string(),
                "nonConclusions".to_string(),
            ],
            non_conclusions: vec![
                "ArchMap is supplied atom observation evidence, not architecture ground truth"
                    .to_string(),
            ],
        },
        AatObservableSourceRefV0 {
            source_ref_id: "source:archmap-validation:primary".to_string(),
            artifact_kind: "archmap-validation-report".to_string(),
            schema_version: "archmap-validation-report-v0".to_string(),
            path: archmap_validation_path.display().to_string(),
            retained_fields: vec![
                "sourceInventoryChecks".to_string(),
                "claimBoundaryChecks".to_string(),
                "formalPromotionGuardrailChecks".to_string(),
                "leanPreservationPreconditionChecklist".to_string(),
                "homomorphismDiagnostics".to_string(),
            ],
            non_conclusions: vec![
                "ArchMap validation does not prove semantic completeness".to_string(),
            ],
        },
        AatObservableSourceRefV0 {
            source_ref_id: "source:air:primary".to_string(),
            artifact_kind: "air".to_string(),
            schema_version: "aat-air-v0".to_string(),
            path: air_path.display().to_string(),
            retained_fields: vec![
                "artifacts".to_string(),
                "evidence".to_string(),
                "claims".to_string(),
                "coverage".to_string(),
            ],
            non_conclusions: vec![
                "AIR projection records review claims, not Lean theorem discharge".to_string(),
            ],
        },
        AatObservableSourceRefV0 {
            source_ref_id: "source:air-validation:primary".to_string(),
            artifact_kind: "air-validation-report".to_string(),
            schema_version: "aat-air-validation-report-v0".to_string(),
            path: air_validation_path.display().to_string(),
            retained_fields: vec!["claimChecks".to_string(), "coverageChecks".to_string()],
            non_conclusions: vec!["AIR validation does not approve merge".to_string()],
        },
        AatObservableSourceRefV0 {
            source_ref_id: "source:theorem-check:primary".to_string(),
            artifact_kind: "theorem-precondition-check-report".to_string(),
            schema_version: "theorem-precondition-check-report-v0".to_string(),
            path: theorem_check_path.display().to_string(),
            retained_fields: vec!["checks".to_string(), "summary".to_string()],
            non_conclusions: vec![
                "precondition check is not a proof of the referenced theorem".to_string(),
            ],
        },
        AatObservableSourceRefV0 {
            source_ref_id: "source:feature-report:primary".to_string(),
            artifact_kind: "feature-extension-report".to_string(),
            schema_version: "feature-extension-report-v0".to_string(),
            path: feature_report_path.display().to_string(),
            retained_fields: vec![
                "coverageGaps".to_string(),
                "theoremPreconditionChecks".to_string(),
                "nonConclusions".to_string(),
            ],
            non_conclusions: vec![
                "feature report is a review artifact, not a global safety guarantee".to_string(),
            ],
        },
    ];
    let source_ref_ids: Vec<String> = source_refs
        .iter()
        .map(|source_ref| source_ref.source_ref_id.clone())
        .collect();
    let concept_mappings =
        archmap_primary_concept_mappings(archmap_validation, theorem_check, feature_report);
    let review_actions = archmap_primary_review_actions(archmap_validation, theorem_check);
    let witness_ref = feature_report
        .introduced_obstruction_witnesses
        .first()
        .map(|witness| witness.witness_id.clone())
        .unwrap_or_else(|| "witness:archmap-primary-boundary".to_string());
    let theorem_claim_ref = theorem_check
        .checks
        .first()
        .map(|check| check.claim_id.clone())
        .unwrap_or_else(|| "claim:archmap-primary-theorem-boundary".to_string());

    AatObservableBundleV0 {
        schema_version: AAT_OBSERVABLE_BUNDLE_SCHEMA_VERSION.to_string(),
        bundle_id: format!("archmap-primary-workflow:{}", archmap.map_id),
        architecture_id: archmap.architecture_id.clone(),
        source_refs,
        selected_universe: AatSelectedUniverseV0 {
            universe_id: format!("universe:{}", archmap.architecture_id),
            included_refs: archmap
                .source_universe
                .included_refs
                .iter()
                .map(archmap_source_ref_label)
                .collect(),
            excluded_refs: archmap
                .source_universe
                .excluded_refs
                .iter()
                .map(archmap_source_ref_label)
                .collect(),
            private_refs: archmap
                .source_universe
                .private_refs
                .iter()
                .map(archmap_source_ref_label)
                .collect(),
            unavailable_refs: archmap
                .source_universe
                .unavailable_refs
                .iter()
                .map(archmap_source_ref_label)
                .collect(),
            unsupported_refs: archmap.coverage.unsupported_constructs.clone(),
            dynamic_boundary_refs: archmap.source_universe.known_blind_spots.clone(),
            exactness_assumptions: vec![archmap.source_universe.selection_boundary.clone()],
            measurement_status: "partiallyMeasured".to_string(),
            non_conclusions: vec![
                "selected universe is not the complete deployed system".to_string(),
                "excluded, private, unavailable, and unsupported refs are not measured zero"
                    .to_string(),
            ],
        },
        concept_mappings,
        observed_axes: vec![
            AatObservedAxisV0 {
                axis_id: "axis:archmap-atom-observations".to_string(),
                concept_refs: vec!["concept:architecture-object".to_string()],
                artifact_refs: vec!["source:archmap:primary".to_string()],
                measurement_status: "partiallyMeasured".to_string(),
                value: Some(archmap.atom_observations.len() as i64),
                boundary: "atomObservations are supplied source-grounded evidence, not complete architecture enumeration"
                    .to_string(),
                non_conclusions: vec!["atom observation count is not a quality score".to_string()],
            },
            AatObservedAxisV0 {
                axis_id: "axis:air-relations".to_string(),
                concept_refs: vec!["concept:projection-observation".to_string()],
                artifact_refs: vec!["source:air:primary".to_string()],
                measurement_status: "partiallyMeasured".to_string(),
                value: Some(air.relations.len() as i64),
                boundary: "AIR relations are projected from ArchMap and optional adapter evidence"
                    .to_string(),
                non_conclusions: vec!["relation count is not global coupling proof".to_string()],
            },
        ],
        coverage_boundaries: vec![
            AatCoverageBoundaryV0 {
                boundary_id: "coverage:archmap-selected-universe".to_string(),
                boundary_kind: "selection-boundary".to_string(),
                affected_refs: source_ref_ids.clone(),
                measurement_status: "partiallyMeasured".to_string(),
                review_action_ref: Some("review:inspect-coverage-boundary".to_string()),
                non_conclusions: vec!["selected coverage is not system completeness".to_string()],
            },
            AatCoverageBoundaryV0 {
                boundary_id: "coverage:unmeasured-semantic-and-runtime".to_string(),
                boundary_kind: "unmeasured".to_string(),
                affected_refs: archmap.coverage.unmeasured_layers.clone(),
                measurement_status: "unmeasured".to_string(),
                review_action_ref: Some("review:request-next-evidence".to_string()),
                non_conclusions: vec!["unmeasured layer is not measured zero".to_string()],
            },
            AatCoverageBoundaryV0 {
                boundary_id: "coverage:out-of-scope-private-unavailable".to_string(),
                boundary_kind: "out-of-scope".to_string(),
                affected_refs: archmap
                    .source_universe
                    .private_refs
                    .iter()
                    .chain(archmap.source_universe.unavailable_refs.iter())
                    .map(archmap_source_ref_label)
                    .collect(),
                measurement_status: "outOfScope".to_string(),
                review_action_ref: Some("review:inspect-coverage-boundary".to_string()),
                non_conclusions: vec![
                    "out-of-scope evidence is retained as boundary data".to_string(),
                ],
            },
        ],
        witness_catalog: vec![AatWitnessCatalogEntryV0 {
            witness_ref: witness_ref.clone(),
            witness_kind: feature_report
                .review_summary
                .top_witnesses
                .first()
                .cloned()
                .unwrap_or_else(|| "coverage-boundary".to_string()),
            law_refs: feature_report.theorem_package_refs.clone(),
            source_refs: source_ref_ids.clone(),
            measurement_status: "partiallyMeasured".to_string(),
            severity: feature_report.review_summary.required_action.clone(),
            review_action_ref: "review:request-next-evidence".to_string(),
            non_conclusions: vec![
                "witness is review evidence, not incident causality or theorem proof".to_string(),
            ],
        }],
        operation_candidates: vec![AatOperationCandidateV0 {
            operation_ref: "operation:archmap-primary-review".to_string(),
            operation_kind: "review-workflow".to_string(),
            role: feature_report.split_status.clone(),
            confidence: "medium".to_string(),
            deterministic_cues: vec![
                format!("air relation count: {}", air.relations.len()),
                format!(
                    "feature report action: {}",
                    feature_report.review_summary.required_action
                ),
            ],
            llm_judgment_needed: vec![
                "semantic operation classification".to_string(),
                "review severity and next evidence prioritization".to_string(),
            ],
            evidence_refs: source_ref_ids.clone(),
            preserved_invariant_refs: feature_report
                .preserved_invariants
                .iter()
                .map(|invariant| invariant.invariant.clone())
                .collect(),
            possible_transferred_obstruction_refs: vec![witness_ref.clone()],
            non_conclusions: vec!["operation candidate is not theorem discharge".to_string()],
        }],
        projection_observation_evidence: vec![AatProjectionObservationEvidenceV0 {
            evidence_ref: "evidence:archmap-to-air".to_string(),
            evidence_kind: "archmap-projection".to_string(),
            source_ref: "source:archmap:primary".to_string(),
            target_ref: "source:air:primary".to_string(),
            local_contract_boundary: "ArchMap source refs and map items are retained".to_string(),
            global_layering_boundary: "global layering is not concluded from projection"
                .to_string(),
            witness_refs: vec![witness_ref.clone()],
            non_conclusions: vec![
                "projection evidence does not prove semantic preservation".to_string(),
            ],
        }],
        feature_extension_evidence: vec![AatFeatureExtensionEvidenceV0 {
            evidence_ref: "evidence:feature-report:primary".to_string(),
            feature_ref: feature_report
                .feature
                .feature_id
                .clone()
                .unwrap_or_else(|| format!("feature:{}", archmap.architecture_id)),
            operation_ref: "operation:archmap-primary-review".to_string(),
            obstruction_classifications: feature_report.review_summary.top_witnesses.clone(),
            source_refs: source_ref_ids.clone(),
            witness_refs: vec![witness_ref.clone()],
            missing_evidence_refs: feature_report.undischarged_assumptions.clone(),
            static_boundary: "adapter evidence is optional".to_string(),
            runtime_boundary: feature_report.runtime_summary.measurement_boundary.clone(),
            semantic_boundary: feature_report
                .semantic_path_summary
                .measurement_boundary
                .clone(),
            coverage_boundary: archmap.source_universe.selection_boundary.clone(),
            non_conclusions: feature_report.non_conclusions.clone(),
        }],
        semantic_diagram_evidence: vec![AatSemanticDiagramEvidenceV0 {
            evidence_ref: "evidence:semantic-diagrams:primary".to_string(),
            path_refs: feature_report
                .semantic_path_summary
                .representative_path_ids
                .clone(),
            homotopy_refs: Vec::new(),
            diagram_refs: feature_report
                .semantic_path_summary
                .representative_diagram_ids
                .clone(),
            filler_status: feature_report
                .semantic_path_summary
                .measurement_boundary
                .clone(),
            nonfillability_witness_refs: feature_report
                .semantic_path_summary
                .representative_nonfillability_witness_ids
                .clone(),
            observation_refs: vec!["source:feature-report:primary".to_string()],
            measurement_status: "partiallyMeasured".to_string(),
            non_conclusions: feature_report.semantic_path_summary.non_conclusions.clone(),
        }],
        state_effect_law_evidence: vec![AatStateEffectLawEvidenceV0 {
            evidence_ref: "evidence:state-effect-boundary:primary".to_string(),
            law_kind: "selected-architecture-policy".to_string(),
            law_case_refs: air.policies.laws.clone(),
            measurement_status: "partiallyMeasured".to_string(),
            witness_refs: vec![witness_ref.clone()],
            unmeasured_law_families: archmap.coverage.unmeasured_layers.clone(),
            non_conclusions: vec![
                "selected law evidence is not global architecture lawfulness".to_string(),
            ],
        }],
        repair_synthesis_evidence: vec![AatRepairSynthesisEvidenceV0 {
            evidence_ref: "evidence:repair-boundary:primary".to_string(),
            repair_step_refs: feature_report
                .repair_suggestions
                .iter()
                .map(|suggestion| suggestion.suggestion_id.clone())
                .collect(),
            synthesis_candidate_refs: Vec::new(),
            no_solution_certificate_refs: Vec::new(),
            selected_obstruction_decrease_refs: Vec::new(),
            transferred_risk_refs: feature_report.complexity_transfer_candidates.clone(),
            solver_status: "not-run".to_string(),
            non_conclusions: vec![
                "repair suggestions are review candidates, not guaranteed improvements".to_string(),
            ],
        }],
        analytic_axes: vec![AatAnalyticAxisV0 {
            axis_id: "analytic:feature-report-coverage".to_string(),
            metric_ref: "feature-report.coverageGaps".to_string(),
            representation_strength: vec!["review-summary".to_string()],
            selected_witness_universe: vec![witness_ref.clone()],
            aggregate_zero_reflection:
                "zero coverage gaps would still require explicit exactness assumptions".to_string(),
            coverage_assumptions: vec![archmap.source_universe.selection_boundary.clone()],
            non_conclusions: vec!["aggregate value is not semantic flatness".to_string()],
        }],
        theorem_boundaries: vec![AatTheoremBoundaryV0 {
            boundary_ref: "boundary:theorem-precondition:primary".to_string(),
            claim_ref: theorem_claim_ref,
            claim_level: "tooling-validation".to_string(),
            claim_classification: archmap_theorem_boundary_classification(
                archmap_validation,
                theorem_check,
            ),
            missing_preconditions: archmap_theorem_boundary_missing_preconditions(
                archmap_validation,
                theorem_check,
            ),
            measured_violation_refs: vec![witness_ref],
            review_action_ref: "review:inspect-theorem-boundary".to_string(),
            non_conclusions: vec!["theorem precondition check is not a Lean proof".to_string()],
        }],
        review_actions,
        llm_review_surface: AatLlmReviewSurfaceV0 {
            skill_ref: "tools/archsig/skills/aat-reviewer/SKILL.md".to_string(),
            input_artifact_refs: source_ref_ids,
            review_questions: vec![
                "Which invariant is preserved, broken, unmeasured, or out of scope?".to_string(),
                "Which ArchMap evidence would change the review decision?".to_string(),
                "Which theorem boundary blocks formal promotion?".to_string(),
            ],
            output_categories: vec![
                "violation".to_string(),
                "risk".to_string(),
                "acceptable".to_string(),
                "unmeasured".to_string(),
                "nextEvidence".to_string(),
            ],
            deterministic_inputs: vec![
                "ArchMap validation".to_string(),
                "AIR validation".to_string(),
                "theorem precondition checks".to_string(),
                "feature report coverage gaps".to_string(),
            ],
            llm_judgment_boundaries: vec![
                "semantic operation classification".to_string(),
                "next evidence prioritization".to_string(),
            ],
            human_review_boundaries: vec![
                "risk acceptance".to_string(),
                "product decision resolution".to_string(),
                "merge approval".to_string(),
            ],
            non_conclusions: vec![
                "LLM review does not prove semantic correctness".to_string(),
                "LLM review does not approve merge automatically".to_string(),
            ],
        },
        responsibility_boundary: AatResponsibilityBoundaryV0 {
            deterministic_tool: vec![
                "validate schema version and refs".to_string(),
                "preserve measurement status and nonConclusions".to_string(),
                "surface measured witnesses and dangling refs".to_string(),
            ],
            llm_review: vec![
                "interpret operation candidates against AAT questions".to_string(),
                "translate nonConclusions into next evidence".to_string(),
            ],
            human_review: vec![
                "decide acceptable residual risk".to_string(),
                "accept or reject design tradeoffs".to_string(),
            ],
            formal_proof: vec![
                "Lean theorem packages remain separate from ArchSig validation".to_string(),
            ],
            non_conclusions: vec![
                "responsibility split does not make tooling output a proof".to_string(),
            ],
        },
        non_conclusions: vec![
            "AAT observable bundle is tooling evidence, not a Lean theorem proof".to_string(),
            "validation pass does not prove extractor completeness".to_string(),
            "unmeasured is not measured zero".to_string(),
            "LLM review output is judgment support, not automatic merge approval".to_string(),
            "ArchMap workflow does not prove architecture lawfulness".to_string(),
        ],
    }
}

fn archmap_primary_concept_mappings(
    validation: &ArchMapValidationReportV0,
    theorem_check: &TheoremPreconditionCheckReportV0,
    feature_report: &FeatureExtensionReportV0,
) -> Vec<AatConceptMappingV0> {
    vec![
        archmap_concept_mapping(
            "concept:architecture-object",
            "ArchitectureObject / ComponentUniverse",
            archmap_family_measurement_status(validation, "object"),
            "reviewable",
            &["object map status is selected-source relative"],
        ),
        archmap_concept_mapping(
            "concept:obstruction-witness",
            "ObstructionWitness",
            if !validation
                .homomorphism_diagnostics
                .obstruction_refs
                .is_empty()
                || !feature_report.introduced_obstruction_witnesses.is_empty()
            {
                "measuredNonzero"
            } else {
                archmap_family_measurement_status(validation, "obstruction")
            },
            "reviewable",
            &["obstruction witness absence is not global lawfulness"],
        ),
        archmap_concept_mapping(
            "concept:theorem-boundary",
            "TheoremBoundary / NonConclusion",
            "unmeasured",
            archmap_theorem_review_status(validation, theorem_check),
            &[
                "theorem boundary status records blocked preconditions and guardrails",
                "theorem check is not Lean theorem discharge",
            ],
        ),
        archmap_concept_mapping(
            "concept:operation",
            "ArchitectureOperation",
            "partiallyMeasured",
            "reviewable",
            &["operation candidate is review evidence, not theorem discharge"],
        ),
        archmap_concept_mapping(
            "concept:projection-observation",
            "Projection / Observation / LSP / DIP",
            archmap_family_measurement_status(validation, "relation"),
            "reviewable",
            &["projection / observation evidence is bounded to selected refs"],
        ),
        archmap_concept_mapping(
            "concept:feature-extension",
            "FeatureExtension / ExtensionObstruction",
            "partiallyMeasured",
            "reviewable",
            &["feature report is not a global safety guarantee"],
        ),
        archmap_concept_mapping(
            "concept:semantic-diagram",
            "Path / Homotopy / DiagramFiller / NonFillability",
            archmap_semantic_diagram_measurement_status(validation),
            archmap_checklist_review_status(
                validation,
                &[
                    "SemanticDiagramPreservation",
                    "SemanticCommutationPreservation",
                    "NonfillabilityWitnessPreservation",
                ],
            ),
            &["semantic diagram evidence is selected-observation relative"],
        ),
        archmap_concept_mapping(
            "concept:state-effect",
            "StateTransition / EffectBoundary",
            archmap_family_measurement_status(validation, "law"),
            "reviewable",
            &["state/effect law evidence is not event log completeness"],
        ),
        archmap_concept_mapping(
            "concept:repair-synthesis",
            "Repair / Synthesis / ComplexityTransfer",
            if !feature_report.repair_suggestions.is_empty()
                || !feature_report.complexity_transfer_candidates.is_empty()
            {
                "partiallyMeasured"
            } else {
                "outOfScope"
            },
            "reviewable",
            &["repair suggestion is not guaranteed improvement or solver completeness"],
        ),
        archmap_concept_mapping(
            "concept:analytic-representation",
            "AnalyticRepresentation / ObstructionValuation",
            archmap_family_measurement_status(validation, "signatureAxis"),
            "reviewable",
            &["analytic axis value is not structural flatness without reflection assumptions"],
        ),
    ]
}

fn archmap_concept_mapping(
    concept_id: &str,
    aat_concept: &str,
    measurement_status: &str,
    review_status: &str,
    non_conclusions: &[&str],
) -> AatConceptMappingV0 {
    AatConceptMappingV0 {
        concept_id: concept_id.to_string(),
        aat_concept: aat_concept.to_string(),
        artifact_refs: vec![
            "source:archmap:primary".to_string(),
            "source:air:primary".to_string(),
        ],
        report_refs: vec![
            "source:archmap-validation:primary".to_string(),
            "source:theorem-check:primary".to_string(),
            "source:feature-report:primary".to_string(),
        ],
        skill_refs: vec!["tools/archsig/skills/aat-reviewer/SKILL.md".to_string()],
        expressibility: "representable".to_string(),
        retention_status: "retained".to_string(),
        review_status: review_status.to_string(),
        measurement_status: measurement_status.to_string(),
        responsibility: "deterministic+LLM+human".to_string(),
        non_conclusions: non_conclusions
            .iter()
            .map(|non_conclusion| non_conclusion.to_string())
            .chain(["concept mapping is not a Lean theorem".to_string()])
            .collect(),
    }
}

fn archmap_primary_review_actions(
    validation: &ArchMapValidationReportV0,
    theorem_check: &TheoremPreconditionCheckReportV0,
) -> Vec<AatReviewActionV0> {
    let theorem_next_evidence =
        archmap_theorem_boundary_missing_preconditions(validation, theorem_check);
    vec![
        AatReviewActionV0 {
            review_action_id: "review:inspect-coverage-boundary".to_string(),
            category: "boundary".to_string(),
            source_refs: vec!["source:archmap:primary".to_string()],
            action: "review selected universe, private refs, unavailable refs, and unsupported constructs".to_string(),
            next_evidence: vec!["source inventory update".to_string()],
            owner: "human-review".to_string(),
            non_conclusions: vec!["coverage review does not prove system completeness".to_string()],
        },
        AatReviewActionV0 {
            review_action_id: "review:request-next-evidence".to_string(),
            category: "nextEvidence".to_string(),
            source_refs: vec!["source:feature-report:primary".to_string()],
            action: "request missing runtime, semantic, or theorem evidence before strengthening claims".to_string(),
            next_evidence: vec!["runtime traces".to_string(), "semantic map refinement".to_string()],
            owner: "human-review".to_string(),
            non_conclusions: vec!["missing evidence is not measured zero".to_string()],
        },
        AatReviewActionV0 {
            review_action_id: "review:inspect-theorem-boundary".to_string(),
            category: "theoremBoundary".to_string(),
            source_refs: vec![
                "source:archmap-validation:primary".to_string(),
                "source:theorem-check:primary".to_string(),
            ],
            action: format!(
                "keep formal theorem claims blocked unless ArchMap preservation checklist and theorem preconditions are discharged ({})",
                archmap_checklist_review_status(validation, &[
                    "FormalPromotionGuardrail",
                    "CoverageExactnessBoundary",
                ])
            ),
            next_evidence: if theorem_next_evidence.is_empty() {
                vec!["Lean theorem package evidence".to_string()]
            } else {
                theorem_next_evidence
            },
            owner: "formal-proof".to_string(),
            non_conclusions: vec!["precondition report is not Lean theorem discharge".to_string()],
        },
    ]
}

fn archmap_family_measurement_status(
    validation: &ArchMapValidationReportV0,
    family: &str,
) -> &'static str {
    let Some(summary) = validation
        .homomorphism_diagnostics
        .map_family_summaries
        .iter()
        .find(|summary| summary.map_family == family)
    else {
        return "unmeasured";
    };
    if summary.entry_count == 0 || summary.unmeasured_count == summary.entry_count {
        "unmeasured"
    } else if summary.measured_count > 0 {
        "partiallyMeasured"
    } else {
        "partiallyMeasured"
    }
}

fn archmap_semantic_diagram_measurement_status(
    validation: &ArchMapValidationReportV0,
) -> &'static str {
    if validation
        .lean_preservation_precondition_checklist
        .iter()
        .any(|entry| {
            matches!(
                entry.lean_package_field.as_str(),
                "SemanticDiagramPreservation"
                    | "SemanticCommutationPreservation"
                    | "NonfillabilityWitnessPreservation"
            ) && matches!(
                entry.status.as_str(),
                "candidate" | "satisfiedBySuppliedAssumption"
            )
        })
    {
        "measuredNonzero"
    } else {
        "unmeasured"
    }
}

fn archmap_checklist_review_status(
    validation: &ArchMapValidationReportV0,
    fields: &[&str],
) -> &'static str {
    let entries = validation
        .lean_preservation_precondition_checklist
        .iter()
        .filter(|entry| fields.contains(&entry.lean_package_field.as_str()));
    let mut saw_candidate = false;
    for entry in entries {
        match entry.status.as_str() {
            "blockedByFormalPromotionGuardrail" => return "blockedByFormalPromotionGuardrail",
            "blockedByUnmeasuredCoverage" => return "blockedByUnmeasuredCoverage",
            "satisfiedBySuppliedAssumption" => saw_candidate = true,
            "candidate" => saw_candidate = true,
            _ => {}
        }
    }
    if saw_candidate {
        "candidate"
    } else {
        "unmeasured"
    }
}

fn archmap_theorem_review_status(
    validation: &ArchMapValidationReportV0,
    theorem_check: &TheoremPreconditionCheckReportV0,
) -> &'static str {
    if validation
        .lean_preservation_precondition_checklist
        .iter()
        .any(|entry| entry.status == "blockedByFormalPromotionGuardrail")
    {
        "blockedByFormalPromotionGuardrail"
    } else if validation
        .lean_preservation_precondition_checklist
        .iter()
        .any(|entry| entry.status == "blockedByUnmeasuredCoverage")
        || theorem_check.summary.blocked_claim_count > 0
    {
        "blockedByUnmeasuredCoverage"
    } else {
        "candidate"
    }
}

fn archmap_theorem_boundary_classification(
    validation: &ArchMapValidationReportV0,
    theorem_check: &TheoremPreconditionCheckReportV0,
) -> String {
    if validation
        .lean_preservation_precondition_checklist
        .iter()
        .any(|entry| entry.status == "blockedByFormalPromotionGuardrail")
    {
        "blockedByFormalPromotionGuardrail".to_string()
    } else if theorem_check.summary.result == "fail" {
        "blockedByTheoremPrecondition".to_string()
    } else {
        theorem_check.summary.result.clone()
    }
}

fn archmap_theorem_boundary_missing_preconditions(
    validation: &ArchMapValidationReportV0,
    theorem_check: &TheoremPreconditionCheckReportV0,
) -> Vec<String> {
    stable_dedup(
        theorem_check
            .checks
            .iter()
            .flat_map(|check| check.missing_preconditions.clone())
            .chain(
                validation
                    .lean_preservation_precondition_checklist
                    .iter()
                    .flat_map(|entry| {
                        entry
                            .blocking_reasons
                            .iter()
                            .chain(entry.missing_evidence.iter())
                            .cloned()
                            .collect::<Vec<_>>()
                    }),
            )
            .collect(),
    )
}

fn stable_dedup(items: Vec<String>) -> Vec<String> {
    let mut seen = BTreeSet::new();
    let mut deduped = Vec::new();
    for item in items {
        if seen.insert(item.clone()) {
            deduped.push(item);
        }
    }
    deduped
}

fn archmap_source_ref_label(source_ref: &archsig::ArchMapSourceRef) -> String {
    source_ref
        .artifact_id
        .clone()
        .or_else(|| source_ref.path.clone())
        .or_else(|| source_ref.symbol.clone())
        .unwrap_or_else(|| source_ref.kind.clone())
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
