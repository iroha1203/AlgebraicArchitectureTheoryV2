use std::collections::BTreeMap;
use std::error::Error;
use std::path::Path;
use std::path::PathBuf;
use std::process::ExitCode;

use archsig::{
    ARCHMAP_CANDIDATE_PACKET_V1_SCHEMA, ARCHMAP_COVERAGE_LEDGER_V1_SCHEMA,
    ARCHMAP_EXTRACTION_CONSISTENCY_V1_SCHEMA, ARCHMAP_SCOPE_MANIFEST_V1_SCHEMA, ARCHMAP_V2_SCHEMA,
    ARCHSIG_REPAIR_PLAN_V1_SCHEMA, ARCHSIG_VALIDATION_FAILED_BEFORE_MEASUREMENT, ArchMapDocumentV2,
    ArchMapValidationReportV2, ArchmapCoverageLedgerV1, ArchmapExtractionConsistencyV1,
    ArchmapScopeManifestV1, AuthoringAuditInputV1, ExtractionDiffOptions,
    LAW_EQUATION_SURFACE_V1_SCHEMA, LAW_POLICY_V1_SCHEMA, LawEquationSurfaceV1,
    LawPolicyDocumentV1, MEASUREMENT_PROFILE_V1_SCHEMA, MeasurementProfileV1, RepairPlanDocumentV1,
    SchemaVersionCatalogV0, ScopeManifestOptions, archmap_authoring_audit_checks_v1,
    build_comparison_artifacts_with_refinement_v1, build_extraction_consistency_v1,
    build_foundation_measurement_packet_v1, build_gate_report_v1, build_insight_brief_v1,
    build_insight_report_v1, build_measurement_summary_v1, build_measurement_view_model_v1,
    build_measurement_viewer_data_v1,
    build_policy_bundle, build_repair_plan_validation_report_v1, build_scope_manifest_v1,
    component_fingerprints as build_component_fingerprints, normalize_archmap_v2,
    parse_candidate_packet_value, resolve_and_verify_policy_bundle, static_schema_version_catalog,
    validate_archmap_v2_report, validate_authoring_audit_input_v1, validate_law_policy_v1_report,
    validate_law_surface_v1_report, validate_measurement_packet_value_v1,
    validate_measurement_profile_v1_checks, validate_refactor_morphism_v1,
};
use clap::{Parser, Subcommand};
use globset::{Glob, GlobSetBuilder};
use serde_json::Value;
use walkdir::WalkDir;

mod cli;
use cli::*;

#[derive(Debug, Parser)]
#[command(
    version,
    about = "Validate ArchMap, LawPolicy, and ArchSig analysis artifacts"
)]
struct Args {
    #[command(subcommand)]
    command: Option<Command>,
}

#[derive(Debug, Subcommand)]
enum Command {
    /// Validate a supplied ArchMap observation JSON artifact.
    Archmap {
        /// Input ArchMap JSON path.
        #[arg(long)]
        input: PathBuf,

        /// Optional authoring scope manifest for survey traceability audit.
        #[arg(long = "scope-manifest")]
        scope_manifest: Option<PathBuf>,

        /// Optional candidate packet path or glob for survey traceability audit. Repeat for multiple inputs.
        #[arg(long = "candidate-packets")]
        candidate_packets: Vec<String>,

        /// Optional extraction consistency artifact path for adjudicated provenance closure. Repeat for multiple inputs.
        #[arg(long = "extraction-consistency")]
        extraction_consistency: Vec<PathBuf>,

        /// Optional coverage ledger for survey traceability audit.
        #[arg(long = "coverage-ledger")]
        coverage_ledger: Option<PathBuf>,

        /// Output ArchMap validation report JSON path. If omitted, JSON is written to stdout.
        #[arg(long)]
        out: Option<PathBuf>,
    },

    /// Build a deterministic authoring scope manifest worklist.
    ScopeManifest {
        /// Repository root to scan.
        #[arg(long = "repo-root", default_value = ".")]
        repo_root: PathBuf,

        /// Include glob. Repeat for multiple patterns.
        #[arg(long = "include", required = true)]
        include: Vec<String>,

        /// Exclude glob. Repeat for multiple patterns.
        #[arg(long = "exclude")]
        exclude: Vec<String>,

        /// Author evidence file as <kind>:<name>=<repo-relative-path>.
        #[arg(long = "add-evidence")]
        add_evidence: Vec<String>,

        /// Previous scope manifest. Emits only new or content-changed worklist rows.
        #[arg(long)]
        baseline: Option<PathBuf>,

        /// Manifest id. Tests and reproducible runs should set this explicitly.
        #[arg(long, default_value = "scope:archmap-authoring")]
        id: String,

        /// Requested scope text to record in scopeSpec.
        #[arg(long = "requested-scope")]
        requested_scope: Option<String>,

        /// Scope approver to record in scopeSpec.
        #[arg(long = "approved-by")]
        approved_by: Option<String>,

        /// Deterministic test override for repository.revision.
        #[arg(long = "revision-override")]
        revision_override: Option<String>,

        /// Deterministic test override for repository.dirty.
        #[arg(long = "dirty-override")]
        dirty_override: Option<bool>,

        /// Output scope manifest JSON path. If omitted, JSON is written to stdout.
        #[arg(long)]
        out: Option<PathBuf>,
    },

    /// Compare candidate packets by authoring atom-match-key without adjudicating adoption.
    ExtractionDiff {
        /// Pass A candidate packet JSON path. Repeat for multiple chunks.
        #[arg(long = "pass-a", required = true)]
        pass_a: Vec<PathBuf>,

        /// Pass B candidate packet JSON path. Omit only for explicit single-pass degraded records.
        #[arg(long = "pass-b")]
        pass_b: Vec<PathBuf>,

        /// Consistency artifact id.
        #[arg(long, default_value = "consistency:archmap-authoring")]
        id: String,

        /// Scope manifest ref override. Defaults to the first pass A packet's scopeManifestRef.
        #[arg(long = "scope-manifest-ref")]
        scope_manifest_ref: Option<String>,

        /// Output extraction consistency JSON path. If omitted, JSON is written to stdout.
        #[arg(long)]
        out: Option<PathBuf>,
    },

    /// Compute deterministic supply-bench metrics over run-pair consistency artifacts.
    SupplyBench {
        /// Run pair as <pair-id>=<extraction-consistency.json>. Repeat per pair.
        #[arg(long = "pair", required = true)]
        pair: Vec<String>,

        /// Chunk class label as <pair-id>=<class> (e.g. tuned, prompt-literal-disjoint).
        #[arg(long = "chunk-class")]
        chunk_class: Vec<String>,

        /// Reference alignment as <pair-id>=<reference-alignment.json>.
        #[arg(long = "alignment")]
        alignment: Vec<String>,

        /// Reference slice JSON path (archmap-reference-slice/v1).
        #[arg(long = "reference")]
        reference: Option<PathBuf>,

        /// Comparison-series key JSON recorded verbatim in the report.
        #[arg(long = "series-key")]
        series_key: Option<PathBuf>,

        /// Report artifact id.
        #[arg(long, default_value = "supply-bench:archmap-authoring")]
        id: String,

        /// Output report JSON path. If omitted, JSON is written to stdout.
        #[arg(long)]
        out: Option<PathBuf>,
    },

    /// Validate a LawPolicy v0.5.4 selector artifact for ArchSig AAT analysis.
    LawPolicy {
        /// Input LawPolicy v0.5.4 JSON path.
        #[arg(long = "law-policy")]
        law_policy: PathBuf,

        /// Input MeasurementProfile v0.5.4 JSON path.
        #[arg(long = "measurement-profile")]
        measurement_profile: PathBuf,

        /// Supplied law-equation-surface/v0.5.4 JSON path.
        #[arg(long = "law-surface")]
        law_surface: PathBuf,

        /// Output LawPolicy fixture or validation report JSON path. If omitted, JSON is written to stdout.
        #[arg(long)]
        out: Option<PathBuf>,
    },

    /// Validate a supplied law-equation-surface/v0.5.4 author declaration.
    LawSurface {
        /// Input law-equation-surface/v0.5.4 JSON path.
        #[arg(long = "law-surface")]
        law_surface: PathBuf,

        /// Output law-equation-surface validation report JSON path. If omitted, JSON is written to stdout.
        #[arg(long)]
        out: Option<PathBuf>,
    },

    /// Validate a standalone MeasurementProfile v0.5.4 artifact.
    MeasurementProfile {
        /// Input MeasurementProfile v0.5.4 JSON path.
        #[arg(long = "measurement-profile")]
        measurement_profile: PathBuf,

        /// Output MeasurementProfile validation report JSON path. If omitted, JSON is written to stdout.
        #[arg(long)]
        out: Option<PathBuf>,
    },

    /// Validate a standalone RepairPlan v0.5.4 artifact.
    RepairPlan {
        /// Input ArchMap observation artifact path used to resolve RepairPlan chart and semantic refs.
        #[arg(long)]
        archmap: PathBuf,

        /// Input RepairPlan v0.5.4 JSON path.
        #[arg(long = "repair-plan")]
        repair_plan: PathBuf,

        /// Optional residual measurement packet JSON path for measured residual binding.
        #[arg(long = "residual-packet")]
        residual_packet: Option<PathBuf>,

        /// Output RepairPlan validation report JSON path. If omitted, JSON is written to stdout.
        #[arg(long)]
        out: Option<PathBuf>,
    },

    /// Run the primary ArchMap + policy-bundle (LawPolicy + law surface + MeasurementProfile) -> ArchSig analysis workflow.
    Analyze {
        /// Input ArchMap observation artifact path.
        #[arg(long)]
        archmap: PathBuf,

        /// Input LawPolicy artifact path.
        #[arg(
            long = "law-policy",
            required_unless_present = "policy_bundle",
            conflicts_with = "policy_bundle"
        )]
        law_policy: Option<PathBuf>,

        /// Optional law-equation-surface/v0.5.4 artifact supplying evaluator execution plans.
        #[arg(long = "law-surface", conflicts_with = "policy_bundle")]
        law_surface: Option<PathBuf>,

        /// Input MeasurementProfile artifact path.
        #[arg(
            long = "measurement-profile",
            required_unless_present = "policy_bundle",
            conflicts_with = "policy_bundle"
        )]
        measurement_profiles: Option<Vec<PathBuf>>,

        /// Policy bundle supplying the LawPolicy, law surface, MeasurementProfile, and fingerprints.
        #[arg(long = "policy-bundle", conflicts_with_all = ["law_policy", "law_surface", "measurement_profiles"])]
        policy_bundle: Option<PathBuf>,

        /// Optional SAGA RepairPlan artifact path.
        #[arg(long = "repair-plan")]
        repair_plan: Option<PathBuf>,

        /// Optional residual packet path used by measured RepairPlan residuals.
        #[arg(long = "residual-packet")]
        residual_packet: Option<PathBuf>,

        /// Optional refactor-morphism/v0.5.4 artifact enabling declared verdict transport.
        #[arg(long = "refactor-morphism")]
        refactor_morphism: Option<PathBuf>,

        /// Output directory for ArchSig analysis workflow artifacts.
        #[arg(long = "out-dir")]
        out_dir: PathBuf,

        /// Append a wall-clock suffix to the deterministic run id. Omitted by default to keep byte-identical outputs.
        #[arg(long)]
        stamp: bool,
    },

    /// Apply a gate policy to an ArchSig measurement packet.
    Gate {
        /// Input archsig-measurement-packet/v0.5.4 JSON path.
        #[arg(long)]
        packet: PathBuf,

        /// Input archsig-gate-policy/v0.5.4 JSON path.
        #[arg(long)]
        policy: PathBuf,

        /// Optional archsig-comparison-report/v0.5.4 JSON path for introduced-by-change rules.
        #[arg(long)]
        comparison: Option<PathBuf>,

        /// Output archsig-gate-report/v0.5.4 JSON path. If omitted, JSON is written to stdout.
        #[arg(long)]
        out: Option<PathBuf>,
    },

    /// Compare two ArchSig analyze run directories at record level.
    Compare {
        /// Base run directory containing normalized-archmap, measurement packet, and run manifest.
        #[arg(long = "base-run")]
        base_run: PathBuf,

        /// Head run directory containing normalized-archmap, measurement packet, and run manifest.
        #[arg(long = "head-run")]
        head_run: PathBuf,

        /// Output directory for archmap-diff.json and archsig-comparison-report.json.
        #[arg(long = "out-dir")]
        out_dir: PathBuf,

        /// Optional refinement-comparison/v0.5.4 artifact enabling fingerprint-bound class-zero transport.
        #[arg(long = "refinement")]
        refinement: Option<PathBuf>,
    },
    /// Create or validate an ArchSig policy bundle.
    PolicyBundle {
        /// Existing policy bundle to validate. Omit this when creating a bundle.
        #[arg(long = "policy-bundle", conflicts_with_all = ["law_policy", "law_surface", "measurement_profile"])]
        policy_bundle: Option<PathBuf>,

        /// LawPolicy component used when creating or explicitly verifying a bundle.
        #[arg(long = "law-policy", requires_all = ["law_surface", "measurement_profile"])]
        law_policy: Option<PathBuf>,

        /// Law equation surface component used when creating or explicitly verifying a bundle.
        #[arg(long = "law-surface", requires_all = ["law_policy", "measurement_profile"])]
        law_surface: Option<PathBuf>,

        /// MeasurementProfile component used when creating or explicitly verifying a bundle.
        #[arg(long = "measurement-profile", requires_all = ["law_policy", "law_surface"])]
        measurement_profile: Option<PathBuf>,

        /// Bundle identifier for a newly created bundle.
        #[arg(long, default_value = "policy-bundle:archsig-v052")]
        id: String,

        /// Output bundle or validation report path. If omitted, JSON is written to stdout.
        #[arg(long)]
        out: Option<PathBuf>,
    },
    SchemaCatalog {
        /// Output schema version catalog JSON path. If omitted, JSON is written to stdout.
        #[arg(long)]
        out: Option<PathBuf>,
    },
}

fn main() -> ExitCode {
    match run() {
        Ok(code) => code,
        Err(error) => {
            eprintln!("{error}");
            if is_internal_runtime_error(&error.to_string()) {
                ExitCode::from(3)
            } else {
                ExitCode::from(2)
            }
        }
    }
}

fn parse_pair_assignments(
    entries: &[String],
    flag: &str,
) -> Result<BTreeMap<String, String>, Box<dyn Error>> {
    let mut map = BTreeMap::new();
    for entry in entries {
        let (pair_id, value) = entry
            .split_once('=')
            .ok_or_else(|| format!("{flag} must be <pair-id>=<value>, got {entry}"))?;
        if map.insert(pair_id.to_string(), value.to_string()).is_some() {
            return Err(format!("{flag} repeats pair id {pair_id}").into());
        }
    }
    Ok(map)
}

fn is_internal_runtime_error(message: &str) -> bool {
    let lower = message.to_ascii_lowercase();
    [
        "is a directory",
        "permission denied",
        "read-only file system",
        "no space left on device",
        "too many open files",
        "broken pipe",
    ]
    .iter()
    .any(|needle| lower.contains(needle))
}

fn validate_archmap_command_input(
    input: &PathBuf,
    scope_manifest: &Option<PathBuf>,
    candidate_packets: &[String],
    extraction_consistency: &[PathBuf],
    coverage_ledger: &Option<PathBuf>,
) -> Result<(serde_json::Value, bool), Box<dyn Error>> {
    let raw: serde_json::Value = read_json(input)?;
    match json_schema(&raw) {
        Some(ARCHMAP_V2_SCHEMA) => {
            let document: ArchMapDocumentV2 = serde_json::from_value(raw)?;
            let mut report = validate_archmap_v2_report(&document, &stable_input_ref(input));
            if authoring_audit_requested(
                scope_manifest,
                candidate_packets,
                extraction_consistency,
                coverage_ledger,
            ) {
                let audit_input = load_authoring_audit_input(
                    scope_manifest,
                    candidate_packets,
                    extraction_consistency,
                    coverage_ledger,
                )?;
                validate_authoring_audit_input_v1(&audit_input)
                    .map_err(|errors| errors.join("; "))?;
                report
                    .checks
                    .extend(archmap_authoring_audit_checks_v1(&document, &audit_input));
                refresh_archmap_report_summary(&mut report);
            }
            let failed = report.summary.result == "fail";
            Ok((serde_json::to_value(report)?, failed))
        }
        _ => {
            require_schema(&raw, ARCHMAP_V2_SCHEMA, "--input")?;
            unreachable!("require_schema returns on success for archmap/v0.5.4")
        }
    }
}

fn authoring_audit_requested(
    scope_manifest: &Option<PathBuf>,
    candidate_packets: &[String],
    extraction_consistency: &[PathBuf],
    coverage_ledger: &Option<PathBuf>,
) -> bool {
    scope_manifest.is_some()
        || !candidate_packets.is_empty()
        || !extraction_consistency.is_empty()
        || coverage_ledger.is_some()
}

fn load_authoring_audit_input(
    scope_manifest: &Option<PathBuf>,
    candidate_packets: &[String],
    extraction_consistency: &[PathBuf],
    coverage_ledger: &Option<PathBuf>,
) -> Result<AuthoringAuditInputV1, Box<dyn Error>> {
    let scope_manifest_path = scope_manifest
        .as_ref()
        .ok_or("--scope-manifest is required when authoring audit flags are used")?;
    let coverage_ledger_path = coverage_ledger
        .as_ref()
        .ok_or("--coverage-ledger is required when authoring audit flags are used")?;
    if candidate_packets.is_empty() {
        return Err("--candidate-packets is required when authoring audit flags are used".into());
    }

    let scope_manifest_raw: serde_json::Value = read_json(scope_manifest_path)?;
    require_schema(
        &scope_manifest_raw,
        ARCHMAP_SCOPE_MANIFEST_V1_SCHEMA,
        "--scope-manifest",
    )?;
    let coverage_ledger_raw: serde_json::Value = read_json(coverage_ledger_path)?;
    require_schema(
        &coverage_ledger_raw,
        ARCHMAP_COVERAGE_LEDGER_V1_SCHEMA,
        "--coverage-ledger",
    )?;

    let mut packet_paths = Vec::new();
    for spec in candidate_packets {
        packet_paths.extend(resolve_candidate_packet_spec(spec)?);
    }
    packet_paths.sort();
    packet_paths.dedup();

    let mut packets = Vec::new();
    for path in packet_paths {
        let raw: serde_json::Value = read_json(&path)?;
        require_schema(
            &raw,
            ARCHMAP_CANDIDATE_PACKET_V1_SCHEMA,
            "--candidate-packets",
        )?;
        packets.push(parse_candidate_packet_value(
            raw,
            &path.display().to_string(),
        )?);
    }

    let mut consistency_reports = Vec::new();
    for path in extraction_consistency {
        let raw: serde_json::Value = read_json(path)?;
        require_schema(
            &raw,
            ARCHMAP_EXTRACTION_CONSISTENCY_V1_SCHEMA,
            "--extraction-consistency",
        )?;
        consistency_reports.push(serde_json::from_value::<ArchmapExtractionConsistencyV1>(
            raw,
        )?);
    }

    Ok(AuthoringAuditInputV1 {
        scope_manifest: serde_json::from_value::<ArchmapScopeManifestV1>(scope_manifest_raw)?,
        candidate_packets: packets,
        extraction_consistency: consistency_reports,
        coverage_ledger: serde_json::from_value::<ArchmapCoverageLedgerV1>(coverage_ledger_raw)?,
    })
}

fn resolve_candidate_packet_spec(spec: &str) -> Result<Vec<PathBuf>, Box<dyn Error>> {
    if !contains_glob_meta(spec) {
        return Ok(vec![PathBuf::from(spec)]);
    }
    let glob = Glob::new(spec)?;
    let mut builder = GlobSetBuilder::new();
    builder.add(glob);
    let set = builder.build()?;
    let root = glob_search_root(spec);
    let mut paths = Vec::new();
    for entry in WalkDir::new(&root).follow_links(false).into_iter() {
        let entry = entry?;
        if entry.file_type().is_file() && set.is_match(entry.path()) {
            paths.push(entry.path().to_path_buf());
        }
    }
    if paths.is_empty() {
        return Err(format!("--candidate-packets matched no files: {spec}").into());
    }
    Ok(paths)
}

fn contains_glob_meta(spec: &str) -> bool {
    spec.chars()
        .any(|character| matches!(character, '*' | '?' | '[' | '{'))
}

fn glob_search_root(spec: &str) -> PathBuf {
    let first_meta = spec.find(['*', '?', '[', '{']).unwrap_or(spec.len());
    let prefix = &spec[..first_meta];
    let root = Path::new(prefix)
        .parent()
        .filter(|path| !path.as_os_str().is_empty())
        .unwrap_or_else(|| Path::new("."));
    root.to_path_buf()
}

fn refresh_archmap_report_summary(report: &mut ArchMapValidationReportV2) {
    let failed_check_count = report
        .checks
        .iter()
        .filter(|check| check.result == "fail")
        .count();
    let warning_check_count = report
        .checks
        .iter()
        .filter(|check| check.result == "warn")
        .count();
    report.summary.failed_check_count = failed_check_count;
    report.summary.warning_check_count = warning_check_count;
    report.summary.result = if failed_check_count > 0 {
        "fail"
    } else if warning_check_count > 0 {
        "warn"
    } else {
        "pass"
    }
    .to_string();
}

fn validate_law_policy_command_input(
    input: &PathBuf,
    measurement_profile: &MeasurementProfileV1,
    law_surface: &LawEquationSurfaceV1,
) -> Result<(serde_json::Value, bool), Box<dyn Error>> {
    let raw: serde_json::Value = read_json(input)?;
    require_schema(&raw, LAW_POLICY_V1_SCHEMA, "--law-policy")?;
    let policy: LawPolicyDocumentV1 = serde_json::from_value(raw)?;
    let report = validate_law_policy_v1_report(
        &policy,
        &stable_input_ref(input),
        Some(measurement_profile),
        Some(law_surface),
    );
    let failed = report.summary.result == "fail";
    Ok((serde_json::to_value(report)?, failed))
}

fn validate_measurement_profile_command_input(
    input: &PathBuf,
) -> Result<(serde_json::Value, MeasurementProfileV1, bool), Box<dyn Error>> {
    let raw: serde_json::Value = read_json(input)?;
    require_schema(&raw, MEASUREMENT_PROFILE_V1_SCHEMA, "--measurement-profile")?;
    let profile: MeasurementProfileV1 = serde_json::from_value(raw)?;
    let checks = validate_measurement_profile_v1_checks(&profile);
    let failed_check_count = checks.iter().filter(|check| check.result == "fail").count();
    let warning_check_count = checks.iter().filter(|check| check.result == "warn").count();
    let failed = failed_check_count > 0;
    Ok((
        serde_json::json!({
            "schema": "measurement-profile-validation-report/v0.5.4",
            "input": {
                "schema": profile.schema,
                "path": stable_input_ref(input),
                "id": profile.profile_id
            },
            "checks": checks,
            "summary": {
                "result": if failed { "fail" } else if warning_check_count > 0 { "warn" } else { "pass" },
                "failedCheckCount": failed_check_count,
                "warningCheckCount": warning_check_count
            }
        }),
        profile,
        failed,
    ))
}

fn validate_law_surface_command_input(
    input: &PathBuf,
) -> Result<(serde_json::Value, bool), Box<dyn Error>> {
    let raw: serde_json::Value = read_json(input)?;
    require_schema(&raw, LAW_EQUATION_SURFACE_V1_SCHEMA, "--law-surface")?;
    let surface: LawEquationSurfaceV1 = serde_json::from_value(raw.clone())?;
    let report = validate_law_surface_v1_report(&surface, &raw, &stable_input_ref(input));
    let failed = report.summary.result == "fail";
    Ok((serde_json::to_value(report)?, failed))
}

fn validate_repair_plan_command_input(
    input: &PathBuf,
    archmap: &ArchMapDocumentV2,
    residual_packet: Option<&PathBuf>,
) -> Result<(serde_json::Value, RepairPlanDocumentV1, bool), Box<dyn Error>> {
    let raw: serde_json::Value = read_json(input)?;
    require_schema(&raw, ARCHSIG_REPAIR_PLAN_V1_SCHEMA, "--repair-plan")?;
    let plan: RepairPlanDocumentV1 = serde_json::from_value(raw)?;
    let residual_packet_json: Option<serde_json::Value> =
        residual_packet.map(read_json).transpose()?;
    let report = build_repair_plan_validation_report_v1(
        &plan,
        archmap,
        &stable_input_ref(input),
        residual_packet_json.as_ref(),
    );
    let failed = report["summary"]["result"] == "fail";
    Ok((report, plan, failed))
}

fn json_schema(document: &serde_json::Value) -> Option<&str> {
    document.get("schema").and_then(|value| value.as_str())
}

fn stable_input_ref(input: &Path) -> String {
    let file_name = input
        .file_name()
        .and_then(|name| name.to_str())
        .unwrap_or("artifact.json");
    format!("input:{file_name}")
}

fn summary_result(document: &serde_json::Value) -> &str {
    document["summary"]["result"].as_str().unwrap_or("fail")
}

fn validation_result_summary(document: &serde_json::Value) -> serde_json::Value {
    let result = summary_result(document);
    validation_result_summary_from_counts(
        result,
        document["summary"]["failedCheckCount"]
            .as_u64()
            .unwrap_or_else(|| usize::from(result == "fail") as u64) as usize,
        document["summary"]["warningCheckCount"]
            .as_u64()
            .unwrap_or(0) as usize,
    )
}

fn validation_result_summary_from_counts(
    result: &str,
    failed_check_count: usize,
    warning_check_count: usize,
) -> serde_json::Value {
    serde_json::json!({
        "result": result,
        "failedCheckCount": failed_check_count,
        "warningCheckCount": warning_check_count
    })
}

fn run() -> Result<ExitCode, Box<dyn Error>> {
    let args = Args::parse();

    match args.command {
        Some(Command::Archmap {
            input,
            scope_manifest,
            candidate_packets,
            extraction_consistency,
            coverage_ledger,
            out,
        }) => {
            let (report, failed) = validate_archmap_command_input(
                &input,
                &scope_manifest,
                &candidate_packets,
                &extraction_consistency,
                &coverage_ledger,
            )?;
            write_json(out, &report)?;
            Ok(if failed {
                ExitCode::from(1)
            } else {
                ExitCode::SUCCESS
            })
        }
        Some(Command::ScopeManifest {
            repo_root,
            include,
            exclude,
            add_evidence,
            baseline,
            id,
            requested_scope,
            approved_by,
            revision_override,
            dirty_override,
            out,
        }) => {
            let manifest = build_scope_manifest_v1(&ScopeManifestOptions {
                repo_root,
                include_globs: include,
                exclude_globs: exclude,
                added_evidence: add_evidence,
                requested_scope,
                approved_by,
                id,
                baseline,
                revision_override,
                dirty_override,
            })?;
            write_json(out, &manifest)?;
            Ok(ExitCode::SUCCESS)
        }
        Some(Command::ExtractionDiff {
            pass_a,
            pass_b,
            id,
            scope_manifest_ref,
            out,
        }) => {
            let report = build_extraction_consistency_v1(&ExtractionDiffOptions {
                pass_a,
                pass_b,
                id,
                scope_manifest_ref,
            })?;
            write_json(out, &report)?;
            Ok(ExitCode::SUCCESS)
        }
        Some(Command::SupplyBench {
            pair,
            chunk_class,
            alignment,
            reference,
            series_key,
            id,
            out,
        }) => {
            let chunk_classes = parse_pair_assignments(&chunk_class, "--chunk-class")?;
            let alignments = parse_pair_assignments(&alignment, "--alignment")?;
            let mut pairs = Vec::new();
            let mut pair_ids = std::collections::BTreeSet::new();
            for entry in &pair {
                let (pair_id, path) = entry.split_once('=').ok_or_else(|| {
                    format!("--pair must be <pair-id>=<path>, got {entry}")
                })?;
                pair_ids.insert(pair_id.to_string());
                pairs.push(archsig::SupplyBenchPairInput {
                    pair_id: pair_id.to_string(),
                    chunk_class: chunk_classes.get(pair_id).cloned(),
                    consistency: PathBuf::from(path),
                    alignment: alignments.get(pair_id).map(PathBuf::from),
                });
            }
            for key in chunk_classes.keys().chain(alignments.keys()) {
                if !pair_ids.contains(key) {
                    return Err(format!(
                        "--chunk-class / --alignment references unknown pair id {key}"
                    )
                    .into());
                }
            }
            let report = archsig::build_supply_bench_report_v1(&archsig::SupplyBenchOptions {
                id,
                pairs,
                reference,
                series_key,
            })?;
            write_json(out, &report)?;
            Ok(ExitCode::SUCCESS)
        }
        Some(Command::LawPolicy {
            law_policy,
            measurement_profile,
            law_surface,
            out,
        }) => {
            let (_, profile, profile_failed) =
                validate_measurement_profile_command_input(&measurement_profile)?;
            let law_surface_raw = read_json(&law_surface)?;
            require_schema(&law_surface_raw, LAW_EQUATION_SURFACE_V1_SCHEMA, "--law-surface")?;
            let law_surface_document: LawEquationSurfaceV1 =
                serde_json::from_value(law_surface_raw)?;
            let (_, law_surface_failed) = validate_law_surface_command_input(&law_surface)?;
            let (report, policy_failed) = validate_law_policy_command_input(
                &law_policy,
                &profile,
                &law_surface_document,
            )?;
            write_json(out, &report)?;
            Ok(if policy_failed || profile_failed || law_surface_failed {
                ExitCode::from(1)
            } else {
                ExitCode::SUCCESS
            })
        }
        Some(Command::LawSurface { law_surface, out }) => {
            reject_output_overwrite(&law_surface, &out)?;
            let (report, failed) = validate_law_surface_command_input(&law_surface)?;
            write_json(out, &report)?;
            Ok(if failed {
                ExitCode::from(1)
            } else {
                ExitCode::SUCCESS
            })
        }
        Some(Command::MeasurementProfile {
            measurement_profile,
            out,
        }) => {
            let (report, _, failed) = validate_measurement_profile_command_input(&measurement_profile)?;
            write_json(out, &report)?;
            Ok(if failed {
                ExitCode::from(1)
            } else {
                ExitCode::SUCCESS
            })
        }
        Some(Command::RepairPlan {
            archmap,
            repair_plan,
            residual_packet,
            out,
        }) => {
            let (_, archmap_failed) =
                validate_archmap_command_input(&archmap, &None, &[], &[], &None)?;
            if archmap_failed {
                return Err("--archmap validation failed before repair-plan validation".into());
            }
            let archmap_document: ArchMapDocumentV2 = read_json(&archmap)?;
            let (report, _, failed) =
                validate_repair_plan_command_input(
                    &repair_plan,
                    &archmap_document,
                    residual_packet.as_ref(),
                )?;
            write_json(out, &report)?;
            Ok(if failed {
                ExitCode::from(1)
            } else {
                ExitCode::SUCCESS
            })
        }
        Some(Command::Gate {
            packet,
            policy,
            comparison,
            out,
        }) => {
            reject_output_overwrite(&packet, &out)?;
            reject_output_overwrite(&policy, &out)?;
            if let Some(comparison) = &comparison {
                reject_output_overwrite(comparison, &out)?;
            }
            let (report, exit_code) = build_gate_report_v1(&packet, &policy, comparison.as_deref())?;
            write_json(out, &report)?;
            Ok(ExitCode::from(exit_code as u8))
        }
        Some(Command::Compare {
            base_run,
            head_run,
            out_dir,
            refinement,
        }) => {
            let (archmap_diff, comparison_report) =
                build_comparison_artifacts_with_refinement_v1(
                    &base_run,
                    &head_run,
                    refinement.as_deref(),
                )?;
            std::fs::create_dir_all(&out_dir)?;
            write_json(Some(out_dir.join("archmap-diff.json")), &archmap_diff)?;
            write_json(
                Some(out_dir.join("archsig-comparison-report.json")),
                &comparison_report,
            )?;
            Ok(ExitCode::SUCCESS)
        }
        Some(Command::PolicyBundle {
            policy_bundle,
            law_policy,
            law_surface,
            measurement_profile,
            id,
            out,
        }) => {
            if let Some(bundle_path) = policy_bundle {
                reject_output_overwrite(&bundle_path, &out)?;
                let resolved = resolve_and_verify_policy_bundle(&bundle_path, None, None, None)?;
                write_json(out, &resolved.report)?;
                Ok(if resolved.report["summary"]["result"] == "pass" {
                    ExitCode::SUCCESS
                } else {
                    ExitCode::from(1)
                })
            } else {
                let law_policy = law_policy.ok_or(
                    "--law-policy, --law-surface, and --measurement-profile are required when creating a policy bundle",
                )?;
                let law_surface = law_surface.ok_or(
                    "--law-policy, --law-surface, and --measurement-profile are required when creating a policy bundle",
                )?;
                let measurement_profile = measurement_profile.ok_or(
                    "--law-policy, --law-surface, and --measurement-profile are required when creating a policy bundle",
                )?;
                let out = out.ok_or(
                    "--out is required when creating a policy bundle so component references remain resolvable",
                )?;
                reject_output_overwrite(&law_policy, &Some(out.clone()))?;
                reject_output_overwrite(&law_surface, &Some(out.clone()))?;
                reject_output_overwrite(&measurement_profile, &Some(out.clone()))?;
                let bundle = build_policy_bundle(
                    &law_policy,
                    &law_surface,
                    &measurement_profile,
                    Some(&out),
                    &id,
                )?;
                write_json(Some(out), &bundle)?;
                Ok(ExitCode::SUCCESS)
            }
        }
        Some(Command::Analyze {
            archmap,
            law_policy,
            law_surface,
            measurement_profiles,
            policy_bundle,
            repair_plan,
            residual_packet,
            refactor_morphism,
            out_dir,
            stamp,
        }) => {
            let (law_policy, law_surface, measurement_profile_paths, bundle_fingerprints) =
                if let Some(bundle_path) = policy_bundle {
                    let resolved = resolve_and_verify_policy_bundle(&bundle_path, None, None, None)?;
                    if resolved.report["summary"]["result"] != "pass" {
                        return Err("policy bundle fingerprint validation failed".into());
                    }
                    (
                        resolved.law_policy,
                        Some(resolved.law_surface),
                        vec![resolved.measurement_profile],
                        Some(serde_json::json!(resolved.bundle.component_fingerprints)),
                    )
                } else {
                    (
                        law_policy.ok_or("--law-policy is required without --policy-bundle")?,
                        law_surface,
                        measurement_profiles
                            .ok_or("--measurement-profile is required without --policy-bundle")?,
                        None,
                    )
                };
            let measurement_profile = measurement_profile_paths
                .first()
                .cloned()
                .ok_or("at least one --measurement-profile is required")?;
            let archmap_validation_path = out_dir.join("archmap-validation.json");
            let law_policy_validation_path = out_dir.join("law-policy-validation.json");
            let analysis_summary_path = out_dir.join("archsig-analysis-summary.json");
            let atom_viewer_data_path = out_dir.join("archsig-atom-viewer-data.json");
            let view_model_path = out_dir.join("archsig-measurement-view-model.json");
            let run_manifest_path = out_dir.join("archsig-run-manifest.json");
            let normalized_archmap_path = out_dir.join("normalized-archmap.json");
            let measurement_packet_path = out_dir.join("archsig-measurement-packet.json");
            let insight_report_path = out_dir.join("archsig-insight-report.json");
            let insight_brief_path = out_dir.join("archsig-insight-brief.md");
            let analysis_validation_path = out_dir.join("archsig-analysis-validation.json");
            let repair_plan_validation_path = out_dir.join("repair-plan-validation.json");
            let law_surface_validation_path = out_dir.join("law-surface-validation.json");

            let (archmap_preflight, archmap_failed) =
                validate_archmap_command_input(&archmap, &None, &[], &[], &None)?;
            let archmap_document: ArchMapDocumentV2 = read_json(&archmap)?;
            let mut measurement_profile_documents = Vec::new();
            let mut measurement_profile_failed = false;
            for path in &measurement_profile_paths {
                let (_report, document, failed) = validate_measurement_profile_command_input(path)?;
                measurement_profile_documents.push(document);
                measurement_profile_failed |= failed;
            }
            let _measurement_profile_document = measurement_profile_documents
                .first()
                .cloned()
                .ok_or("at least one --measurement-profile is required")?;
            let measurement_profile_catalog = measurement_profile_documents
                .iter()
                .map(|profile| (profile.profile_id.clone(), profile.clone()))
                .collect::<BTreeMap<_, _>>();
            if measurement_profile_catalog.len() != measurement_profile_documents.len() {
                return Err("--measurement-profile inputs must have unique profileId values".into());
            }
            let law_surface_preflight = law_surface
                .as_ref()
                .map(validate_law_surface_command_input)
                .transpose()?;
            let law_surface_document = law_surface
                .as_ref()
                .map(read_json)
                .transpose()?
                .map(serde_json::from_value::<LawEquationSurfaceV1>)
                .transpose()?;
            let law_policy_document: LawPolicyDocumentV1 = read_json(&law_policy)?;
            let law_policy_report = archsig::validate_law_policy_v1_report_with_profiles(
                &law_policy_document,
                &stable_input_ref(&law_policy),
                &measurement_profile_catalog,
                law_surface_document.as_ref(),
            );
            let law_policy_failed = law_policy_report.summary.result == "fail";
            let law_policy_preflight = serde_json::to_value(law_policy_report)?;
            let repair_plan_preflight = repair_plan
                .as_ref()
                .map(|path| {
                    validate_repair_plan_command_input(
                        path,
                        &archmap_document,
                        residual_packet.as_ref(),
                    )
                })
                .transpose()?;
            let repair_plan_document = repair_plan_preflight
                .as_ref()
                .map(|(_, document, _)| document.clone());
            let repair_plan_failed = repair_plan_preflight
                .as_ref()
                .is_some_and(|(_, _, failed)| *failed);
            let refactor_morphism_value = refactor_morphism
                .as_ref()
                .map(read_json)
                .transpose()?;
            if let Some(refactor_morphism_value) = refactor_morphism_value.as_ref() {
                validate_refactor_morphism_v1(refactor_morphism_value)?;
            }
            let law_surface_failed = law_surface_preflight
                .as_ref()
                .is_some_and(|(_, failed)| *failed);
            let archmap_input_ref = artifact_input_ref(&archmap);
            let law_policy_input_ref = artifact_input_ref(&law_policy);
            let law_surface_input_ref = law_surface
                .as_ref()
                .map(|path| artifact_input_ref(path));
            let measurement_profile_input_ref = artifact_input_ref(&measurement_profile);
            let measurement_profile_input_refs = measurement_profile_paths
                .iter()
                .map(|path| artifact_input_ref(path))
                .collect::<Vec<_>>();
            let repair_plan_input_ref = repair_plan.as_ref().map(|path| artifact_input_ref(path));
            let residual_packet_input_ref =
                residual_packet.as_ref().map(|path| artifact_input_ref(path));
            let archmap_contract_input: Value = read_json(&archmap)?;
            let law_policy_contract_input: Value = read_json(&law_policy)?;
            let measurement_profile_contract_inputs = measurement_profile_paths
                .iter()
                .map(read_json)
                .collect::<Result<Vec<_>, _>>()?;
            let mut validation_generated_artifacts =
                vec!["archmap-validation.json", "law-policy-validation.json"];
            if law_surface_preflight.is_some() {
                validation_generated_artifacts.push("law-surface-validation.json");
            }
            if repair_plan_preflight.is_some() {
                validation_generated_artifacts.push("repair-plan-validation.json");
            }
            let mut failure_generated_artifacts = validation_generated_artifacts.clone();
            failure_generated_artifacts.extend([
                "archsig-insight-report.json",
                "archsig-insight-brief.md",
                "archsig-atom-viewer-data.json",
                "archsig-run-manifest.json",
            ]);
            let mut measurement_generated_artifacts = validation_generated_artifacts.clone();
            measurement_generated_artifacts.extend([
                "normalized-archmap.json",
                "archsig-measurement-packet.json",
                "archsig-analysis-validation.json",
                "archsig-analysis-summary.json",
                "archsig-insight-report.json",
                "archsig-insight-brief.md",
                "archsig-atom-viewer-data.json",
                "archsig-measurement-view-model.json",
                "archsig-run-manifest.json",
            ]);
            let component_fingerprints = bundle_fingerprints.or(Some(serde_json::json!(
                build_component_fingerprints(&law_policy, law_surface.as_deref().ok_or(
                    "analyze requires --law-surface for LawPolicy v0.5.4",
                )?, &measurement_profile)?
            )));
            let run_contract = AnalyzeRunContract::from_inputs(
                &archmap,
                &law_policy,
                law_surface.as_deref(),
                &measurement_profile_paths
                    .iter()
                    .map(PathBuf::as_path)
                    .collect::<Vec<_>>(),
                residual_packet.as_deref(),
                repair_plan.as_deref(),
                contract_profile_fingerprint(
                    &law_policy_contract_input,
                    &measurement_profile_contract_inputs,
                )?,
                contract_site_cover_digest(&archmap_contract_input)?,
                component_fingerprints,
                stamp,
            )?;
            std::fs::create_dir_all(&out_dir)?;
            remove_analyze_success_artifacts(&out_dir)?;
            write_json(
                Some(archmap_validation_path),
                &with_run_contract(&archmap_preflight, &run_contract)?,
            )?;
            write_json(
                Some(law_policy_validation_path),
                &with_run_contract(&law_policy_preflight, &run_contract)?,
            )?;
            if let Some((repair_plan_report, _, _)) = &repair_plan_preflight {
                write_json(
                    Some(repair_plan_validation_path),
                    &with_run_contract(repair_plan_report, &run_contract)?,
                )?;
            }
            if let Some((law_surface_report, _)) = &law_surface_preflight {
                write_json(
                    Some(law_surface_validation_path.clone()),
                    &with_run_contract(law_surface_report, &run_contract)?,
                )?;
            }
            if archmap_failed
                || law_policy_failed
                || measurement_profile_failed
                || repair_plan_failed
                || law_surface_failed
            {
                let mut insight_report = build_validation_failure_insight_report(
                    &archmap_preflight,
                    &law_policy_preflight,
                    law_surface_preflight
                        .as_ref()
                        .map(|(report, _)| report),
                    repair_plan_preflight
                        .as_ref()
                        .map(|(report, _, _)| report),
                );
                let insight_brief = build_insight_brief_v1(&insight_report);
                attach_run_contract(&mut insight_report, &run_contract);
                let mut viewer_data = build_validation_failure_viewer_data(&insight_report);
                attach_run_contract(&mut viewer_data, &run_contract);
                write_json(Some(insight_report_path), &insight_report)?;
                std::fs::write(insight_brief_path, insight_brief)?;
                write_json(Some(atom_viewer_data_path), &viewer_data)?;
                write_json(
                    Some(run_manifest_path),
                    &serde_json::json!({
                        "schema": "archsig-run-manifest/v0.5.4",
                        "toolVersion": run_contract.tool_version.clone(),
                        "runId": run_contract.run_id.clone(),
                        "inputDigests": run_contract.input_digests.clone(),
                        "componentFingerprints": run_contract.component_fingerprints.clone(),
                        "commandName": "analyze",
                        "mode": "validation-failure",
                        "conclusionCode": ARCHSIG_VALIDATION_FAILED_BEFORE_MEASUREMENT,
                        "archmapInputPath": archmap_input_ref,
                        "lawPolicyInputPath": law_policy_input_ref,
                        "lawSurfaceInputPath": law_surface_input_ref,
                        "measurementProfileInputPath": measurement_profile_input_ref,
                        "measurementProfileInputPaths": measurement_profile_input_refs,
                        "repairPlanInputPath": repair_plan_input_ref,
                        "rawArtifactRetention": "not-computed",
                        "generatedArtifacts": failure_generated_artifacts,
                        "omittedArtifacts": [
                            "normalized-archmap.json",
                            "archsig-measurement-packet.json",
                            "archsig-analysis-validation.json",
                            "archsig-analysis-summary.json",
                            "archsig-measurement-view-model.json",
                        ],
                        "artifactLinks": {
                            "insightReport": "archsig-insight-report.json",
                            "insightBrief": "archsig-insight-brief.md",
                            "viewerData": "archsig-atom-viewer-data.json"
                        },
                        "validationReports": {
                            "archmap": "archmap-validation.json",
                            "lawPolicy": "law-policy-validation.json",
                            "lawSurface": law_surface_preflight.as_ref().map(|_| "law-surface-validation.json"),
                            "repairPlan": repair_plan_preflight.as_ref().map(|_| "repair-plan-validation.json"),
                            "analysis": null
                        },
                        "rawArtifactPaths": null,
                        "validationResultSummary": {
                            "archmap": validation_result_summary(&archmap_preflight),
                            "lawPolicy": validation_result_summary(&law_policy_preflight),
                            "lawSurface": law_surface_preflight.as_ref().map(|(report, _)| validation_result_summary(report)),
                            "repairPlan": repair_plan_preflight.as_ref().map(|(report, _, _)| validation_result_summary(report)),
                            "analysis": validation_result_summary_from_counts("not_computed", 0, 0)
                        },
                        "nonConclusions": [
                            "Validation failure insight is a pre-normalization projection and does not contain measurement packet claims.",
                            "No measurement packet, structural verdict, or AG invariant was computed after failed preflight validation."
                        ]
                    }),
                )?;
                eprintln!(
                    "archsig analyze wrote validation insight artifacts to {} and stopped before normalization",
                    out_dir.display()
                );
                if law_surface.is_none() {
                    eprintln!("analyze requires --law-surface for LawPolicy v0.5.4");
                }
                return Ok(ExitCode::from(2));
            }
            let normalized_archmap = normalize_archmap_v2(&archmap_document, &archmap_input_ref);
            let measurement_packet = match build_foundation_measurement_packet_v1(
                &normalized_archmap,
                &archmap_document,
                &law_policy_document,
                law_surface_document.as_ref(),
                &measurement_profile_catalog,
                repair_plan_document.as_ref(),
                &archmap_input_ref,
                &law_policy_input_ref,
                law_surface_input_ref.as_deref(),
                &measurement_profile_input_ref,
                repair_plan_input_ref.as_deref(),
                residual_packet_input_ref.as_deref(),
                refactor_morphism_value.as_ref(),
            )
            {
                Ok(packet) => packet,
                Err(message) => {
                    let mut runtime_failure_generated_artifacts = validation_generated_artifacts.clone();
                    runtime_failure_generated_artifacts.extend([
                        "archsig-analysis-validation.json",
                        "archsig-run-manifest.json",
                    ]);
                    let analysis_failure = serde_json::json!({
                        "schema": "archsig-measurement-packet-validation-report/v0.5.4",
                        "packetSchema": "archsig-measurement-packet/v0.5.4",
                        "checks": [{
                            "id": "analysis-execution-plan",
                            "result": "fail",
                            "message": message.clone()
                        }],
                        "summary": {
                            "result": "fail",
                            "failedCheckCount": 1,
                            "warningCheckCount": 0
                        }
                    });
                    write_json(
                        Some(analysis_validation_path),
                        &with_run_contract(&analysis_failure, &run_contract)?,
                    )?;
                    write_json(
                        Some(run_manifest_path),
                        &serde_json::json!({
                            "schema": "archsig-run-manifest/v0.5.4",
                            "toolVersion": run_contract.tool_version.clone(),
                            "runId": run_contract.run_id.clone(),
                            "inputDigests": run_contract.input_digests.clone(),
                            "componentFingerprints": run_contract.component_fingerprints.clone(),
                            "commandName": "analyze",
                            "mode": "analysis-failure",
                            "conclusionCode": "ANALYSIS_FAILED_BEFORE_MEASUREMENT",
                            "archmapInputPath": archmap_input_ref,
                            "lawPolicyInputPath": law_policy_input_ref,
                            "lawSurfaceInputPath": law_surface_input_ref,
                            "measurementProfileInputPath": measurement_profile_input_ref,
                            "measurementProfileInputPaths": measurement_profile_input_refs,
                            "repairPlanInputPath": repair_plan_input_ref,
                            "rawArtifactRetention": "not-computed",
                            "generatedArtifacts": runtime_failure_generated_artifacts,
                            "omittedArtifacts": [
                                "normalized-archmap.json",
                                "archsig-measurement-packet.json",
                                "archsig-analysis-summary.json",
                                "archsig-insight-report.json",
                                "archsig-insight-brief.md",
                                "archsig-atom-viewer-data.json"
                            ],
                            "validationReports": {
                                "archmap": "archmap-validation.json",
                                "lawPolicy": "law-policy-validation.json",
                                "lawSurface": law_surface_preflight.as_ref().map(|_| "law-surface-validation.json"),
                                "repairPlan": repair_plan_preflight.as_ref().map(|_| "repair-plan-validation.json"),
                                "analysis": "archsig-analysis-validation.json"
                            },
                            "validationResultSummary": {
                                "archmap": validation_result_summary(&archmap_preflight),
                                "lawPolicy": validation_result_summary(&law_policy_preflight),
                                "lawSurface": law_surface_preflight.as_ref().map(|(report, _)| validation_result_summary(report)),
                                "repairPlan": repair_plan_preflight.as_ref().map(|(report, _, _)| validation_result_summary(report)),
                                "analysis": validation_result_summary_from_counts("fail", 1, 0)
                            },
                            "nonConclusions": [
                                "Execution-plan failure occurred after input validation and before normalization.",
                                "No measurement packet, structural verdict, or AG invariant was computed."
                            ]
                        }),
                    )?;
                    eprintln!("archsig analyze execution plan failed before measurement: {message}");
                    return Ok(ExitCode::from(2));
                }
            };
            write_json(
                Some(normalized_archmap_path),
                &with_run_contract(&normalized_archmap, &run_contract)?,
            )?;
            let packet_value = with_run_contract(&measurement_packet, &run_contract)?;
            let packet_validation = validate_measurement_packet_value_v1(&packet_value);
            let packet_failed = packet_validation.iter().any(|check| check.result == "fail");
            let packet_failed_check_count = packet_validation
                .iter()
                .filter(|check| check.result == "fail")
                .count();
            let packet_warning_check_count = packet_validation
                .iter()
                .filter(|check| check.result == "warn")
                .count();
            write_json(
                Some(measurement_packet_path.clone()),
                &packet_value,
            )?;
            let measurement_summary = build_measurement_summary_v1(&measurement_packet);
            let insight_report = build_insight_report_v1(
                &normalized_archmap,
                &measurement_packet,
                &measurement_summary,
            );
            let insight_brief = build_insight_brief_v1(&insight_report);
            let measurement_viewer_data = build_measurement_viewer_data_v1(
                &normalized_archmap,
                &archmap_document,
                &measurement_packet,
                &measurement_summary,
                &insight_report,
            );
            let mut measurement_viewer_data =
                with_run_contract(&measurement_viewer_data, &run_contract)?;
            measurement_viewer_data["inputDigests"]["measurementPacket"] = serde_json::json!({
                "path": "input:archsig-measurement-packet.json",
                "sha256": canonical_json_file_digest(&measurement_packet_path)?
            });
            write_json(
                Some(analysis_validation_path),
                &with_run_contract(&serde_json::json!({
                    "schema": "archsig-measurement-packet-validation-report/v0.5.4",
                    "packetSchema": measurement_packet.schema,
                    "checks": packet_validation,
                    "summary": {
                        "result": if packet_failed { "fail" } else { "pass" },
                        "failedCheckCount": packet_failed_check_count,
                        "warningCheckCount": packet_warning_check_count
                    }
                }), &run_contract)?,
            )?;
            write_json(
                Some(analysis_summary_path),
                &with_run_contract(&measurement_summary, &run_contract)?,
            )?;
            write_json(
                Some(atom_viewer_data_path),
                &measurement_viewer_data,
            )?;
            let packet_value = serde_json::to_value(&measurement_packet)?;
            let view_model = build_measurement_view_model_v1(
                &packet_value,
                &normalized_archmap,
                &measurement_summary,
            );
            let mut view_model = with_run_contract(&view_model, &run_contract)?;
            view_model["inputDigests"]["measurementPacket"] = serde_json::json!({
                "path": "input:archsig-measurement-packet.json",
                "sha256": canonical_json_file_digest(&measurement_packet_path)?
            });
            write_json(Some(view_model_path), &view_model)?;
            write_json(
                Some(insight_report_path),
                &with_run_contract(&insight_report, &run_contract)?,
            )?;
            std::fs::write(insight_brief_path, insight_brief)?;
            write_json(
                Some(run_manifest_path),
                &serde_json::json!({
                    "schema": "archsig-run-manifest/v0.5.4",
                    "toolVersion": run_contract.tool_version.clone(),
                    "runId": run_contract.run_id.clone(),
                    "inputDigests": run_contract.input_digests.clone(),
                    "componentFingerprints": run_contract.component_fingerprints.clone(),
                    "commandName": "analyze",
                    "mode": "measurement",
                    "conclusionCode": null,
                    "archmapInputPath": archmap_input_ref,
                    "lawPolicyInputPath": law_policy_input_ref,
                    "lawSurfaceInputPath": law_surface_input_ref,
                    "measurementProfileInputPath": measurement_profile_input_ref,
                    "measurementProfileInputPaths": measurement_profile_input_refs,
                    "repairPlanInputPath": repair_plan_input_ref,
                    "rawArtifactRetention": "omitted",
                    "generatedArtifacts": measurement_generated_artifacts,
                    "omittedArtifacts": [],
                    "artifactLinks": {
                        "measurementPacket": "archsig-measurement-packet.json",
                        "summary": "archsig-analysis-summary.json",
                        "insightReport": "archsig-insight-report.json",
                        "insightBrief": "archsig-insight-brief.md",
                        "viewerData": "archsig-atom-viewer-data.json",
                        "viewModel": "archsig-measurement-view-model.json"
                    },
                    "validationReports": {
                        "archmap": "archmap-validation.json",
                        "lawPolicy": "law-policy-validation.json",
                        "lawSurface": law_surface_preflight.as_ref().map(|_| "law-surface-validation.json"),
                        "repairPlan": repair_plan_preflight.as_ref().map(|_| "repair-plan-validation.json"),
                        "analysis": "archsig-analysis-validation.json"
                    },
                    "rawArtifactPaths": null,
                    "validationResultSummary": {
                        "archmap": validation_result_summary(&archmap_preflight),
                        "lawPolicy": validation_result_summary(&law_policy_preflight),
                        "lawSurface": law_surface_preflight.as_ref().map(|(report, _)| validation_result_summary(report)),
                        "repairPlan": repair_plan_preflight.as_ref().map(|(report, _, _)| validation_result_summary(report)),
                        "analysis": validation_result_summary_from_counts(
                            if packet_failed { "fail" } else { "pass" },
                            packet_failed_check_count,
                            packet_warning_check_count
                        )
                    },
                    "nonConclusions": [
                        "Finite-poset-site run manifest records the v0.5.4 AG measurement foundation artifacts.",
                        "Foundation packet rows are not completed AG invariant evaluator computation."
                    ]
                }),
            )?;
            Ok(if packet_failed {
                ExitCode::from(2)
            } else {
                ExitCode::SUCCESS
            })
        }
        Some(Command::SchemaCatalog { out }) => {
            let catalog: SchemaVersionCatalogV0 = static_schema_version_catalog();
            write_json(out, &catalog)?;
            Ok(ExitCode::SUCCESS)
        }
        None => Err("ArchSig is ArchMap/LawPolicy/measurement-packet primary; use `archsig analyze` for the main analysis path.".into()),
    }
}

fn remove_analyze_success_artifacts(out_dir: &PathBuf) -> Result<(), Box<dyn Error>> {
    let mut artifacts = vec![
        "archsig-analysis-summary.json".to_string(),
        "archsig-atom-viewer-data.json".to_string(),
        "archsig-measurement-view-model.json".to_string(),
        "archsig-run-manifest.json".to_string(),
        "normalized-archmap.json".to_string(),
        "archsig-measurement-packet.json".to_string(),
        "archsig-insight-report.json".to_string(),
        "archsig-insight-brief.md".to_string(),
        "archsig-analysis-validation.json".to_string(),
        "law-surface-validation.json".to_string(),
        "repair-plan-validation.json".to_string(),
    ];
    artifacts.extend([
        ["typed", "evaluator", "results.json"].join("-"),
        ["architecture", "distance.json"].join("-"),
        ["archsig", "analysis", "packet.json"].join("-"),
        ["archsig", "analysis", "detail", "index.json"].join("-"),
        ["llm", "interpretation", "packet.json"].join("-"),
    ]);
    for artifact in artifacts {
        let path = out_dir.join(artifact);
        match std::fs::remove_file(&path) {
            Ok(()) => {}
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => {}
            Err(error) => return Err(Box::new(error)),
        }
    }
    Ok(())
}

fn build_validation_failure_insight_report(
    archmap_validation: &Value,
    law_policy_validation: &Value,
    law_surface_validation: Option<&Value>,
    repair_plan_validation: Option<&Value>,
) -> Value {
    let failed_refs = validation_failure_refs(
        archmap_validation,
        law_policy_validation,
        law_surface_validation,
        repair_plan_validation,
    );
    let primary_ref = failed_refs
        .first()
        .cloned()
        .unwrap_or_else(|| "validation:unknown-failure".to_string());
    serde_json::json!({
        "schema": "archsig-insight-report/v0.5.4",
        "reportId": "insight:validation-failure",
        "sourcePacketRef": null,
        "generatedAt": "deterministic-run-artifact",
        "outputArtifacts": {
            "summaryRef": null,
            "briefRef": "archsig-insight-brief.md",
            "viewerDataRef": "archsig-atom-viewer-data.json"
        },
        "headline": {
            "conclusionCode": ARCHSIG_VALIDATION_FAILED_BEFORE_MEASUREMENT,
            "title": "Validation failed before measurement",
            "summary": "ArchSig stopped before normalization because an input validation check failed.",
            "decisionState": "blocked",
            "primaryVerdictRefs": [],
            "boundaryDigestRef": "boundary-digest:validation"
        },
        "readThisFirst": {
            "heading": "Read this first",
                "conclusion": ARCHSIG_VALIDATION_FAILED_BEFORE_MEASUREMENT,
            "whatItMeans": "No measurement packet or AG invariant was computed. Fix the failing ArchMap, LawPolicy, or RepairPlan validation first.",
            "whereToLookFirst": failed_refs,
            "nextAction": "Inspect failed validation checks",
            "boundary": "Pre-normalization validation failed; no structural verdict is available.",
            "details": {
                "validationRefs": failed_refs,
                "sourceRefs": [],
                "atomRefs": [],
                "contextRefs": []
            }
        },
        "insightCards": [{
            "id": "insight:validation-failure:001",
            "kind": "validation_failure",
            "severity": "blocking",
            "title": "Validation failed before measurement",
            "oneLine": "ArchSig stopped before normalization because input validation failed.",
            "whyItMatters": "The viewer and brief can identify the blocker, but they must not present measurement conclusions that were never computed.",
            "evidence": {
                "structuralVerdictRefs": [],
                "computedInvariantRefs": [],
                "analyticReadingRefs": [],
                "assumptionRefs": [],
                "sourceRefs": [],
                "atomRefs": [],
                "contextRefs": [],
                "coverRefs": [],
                "evaluatorRefs": [],
                "validationRefs": failed_refs,
                "evidenceResolutionStatus": "validation_failure_before_measurement"
            },
            "sampleRefs": {
                "atomRefs": [],
                "contextRefs": [],
                "sourceRefs": [],
                "note": "No normalized ArchMap projection exists after validation failure."
            },
            "nextAction": {
                "label": "Inspect failed validation checks",
                "kind": "validation_blocker",
                "targetRefs": [primary_ref]
            },
            "viewerNavigation": {
                "sceneId": "boundary-assumption",
                "highlightRefs": {
                    "atomRefs": [],
                    "contextRefs": [],
                    "sourceRefs": [],
                    "validationRefs": failed_refs
                }
            },
            "tourRefs": ["tour:validation-failure:001"],
            "rankingBasis": ["validation_failure"],
            "nonClaims": [
                "This is not a measured AG obstruction.",
                "No measurement packet, structural verdict, or analytic reading was computed."
            ]
        }],
        "actionQueue": [{
            "id": "action:validation:1",
            "kind": "validation_blocker",
            "title": "Inspect failed validation checks",
            "reason": "Input validation failed before ArchSig could normalize and measure.",
            "targetRefs": failed_refs,
            "expectedUserOutcome": "Fix the input contract before reading measurement claims.",
            "nonClaims": ["No AG measurement conclusion exists for this run."]
        }],
        "boundaryDigest": {
            "id": "boundary-digest:validation",
            "shortText": "Validation failed before normalization; measurement is not computed.",
            "checkedCount": 0,
            "assumedCount": 0,
            "violatedCount": 1,
            "unmeasuredCount": 0,
            "unknownCount": 0,
            "notComputedCount": 1,
            "blockingCount": 1,
            "blocking": failed_refs,
            "nonClaims": ["Validation failure does not imply measured nonzero or measured zero."]
        },
        "viewerVisualScenes": [validation_failure_scene(&failed_refs)],
        "guidedTours": [{
            "tourId": "tour:validation-failure:001",
            "title": "Validation failed before measurement",
            "insightRefs": ["insight:validation-failure:001"],
            "steps": [{
                "sceneId": "boundary-assumption",
                "caption": "This boundary explains why no measurement packet was produced.",
                "highlightRefs": {
                    "validationRefs": failed_refs
                }
            }]
        }],
        "copyBlocks": {
            "sourceRefs": [],
            "llmHandoff": {
                "instruction": "Use this as a validation blocker only. Do not infer measurement conclusions.",
                "boundary": "Validation failed before normalization.",
                "topInsights": ["ArchSig stopped before measurement because validation failed."]
            }
        },
        "rankingBasis": ["validation_failure"],
        "claimValidation": {
            "measuredClaimsRequireStructuralVerdictRefs": true,
            "analyticReadingsDoNotPromoteLawfulOrUnlawful": true,
            "validationFailureDoesNotCreateMeasurementClaim": true
        },
        "nonConclusions": [
            "Validation failure insight is a pre-normalization projection.",
            "No measurement packet claims are generated."
        ]
    })
}

fn build_validation_failure_viewer_data(insight_report: &Value) -> Value {
    serde_json::json!({
        "schema": "archsig-atom-viewer-data/v0.5.4",
        "sourceArtifactRefs": {
            "archmapValidation": "archmap-validation.json",
            "lawPolicyValidation": "law-policy-validation.json",
            "insightReport": "archsig-insight-report.json",
            "insightBrief": "archsig-insight-brief.md"
        },
        "decisionBar": {
            "conclusion": ARCHSIG_VALIDATION_FAILED_BEFORE_MEASUREMENT,
            "validation": "see archmap-validation.json and law-policy-validation.json",
            "boundaryDigest": insight_report["boundaryDigest"]["shortText"],
            "artifactLinks": insight_report["outputArtifacts"]
        },
        "insightQueue": insight_report["insightCards"],
        "actionQueue": insight_report["actionQueue"],
        "viewerVisualScenes": insight_report["viewerVisualScenes"],
        "guidedTours": insight_report["guidedTours"],
        "copyBlocks": insight_report["copyBlocks"],
        "sagaDescent": {
            "projectionBoundary": "SAGA fields are unavailable because validation stopped before measurement.",
            "sourcePacketRef": "archsig-measurement-packet.json",
            "stages": [
                {"stageId": "grounding", "order": 0, "status": "not_computed", "rows": [], "measurements": [], "visualRole": "grounding"},
                {"stageId": "descent", "order": 1, "status": "not_computed", "rows": [], "measurements": [], "harmonicDebt": [], "visualRole": "descent-measurement"},
                {"stageId": "comparison", "order": 2, "status": "not_computed", "rows": [], "visualRole": "transfer-comparison"},
                {"stageId": "silence", "order": 3, "status": "not_computed", "rows": [], "visualRole": "silence"}
            ],
            "silenceRows": [],
            "leafFieldMap": [],
            "nonClaims": ["Validation stopped before a measurement packet could supply SAGA fields."]
        },
        "reportPane": {
            "readThisFirst": insight_report["readThisFirst"],
            "insightQueue": insight_report["insightCards"],
            "actionQueue": insight_report["actionQueue"],
            "evidenceDetailShape": ["What", "Why", "Measurement", "Boundary", "Next"],
            "boundaryDigest": insight_report["boundaryDigest"],
            "artifactLinks": insight_report["outputArtifacts"]
        },
        "finitePosetSite": {
            "atoms": [],
            "contexts": [],
            "covers": []
        },
        "largeGraphStrategy": {
            "mode": "validation_blocked",
            "thresholds": {
                "fullGeometryAtoms": 2_000,
                "instancedAtoms": 10_000,
                "clusterAtoms": 50_000
            },
            "topInsightEvidencePinning": {
                "policy": "preserve_for_top_insight",
                "preservedRefs": insight_report["readThisFirst"]["whereToLookFirst"],
                "aggregatedRefs": [],
                "omittedRefs": []
            }
        },
        "omittedDetailCounts": {
            "omittedAtoms": 0,
            "omittedEdges": 0,
            "omittedContextMemberships": 0,
            "omittedCoverOverlaps": 0,
            "omittedSceneLayerObjects": 0,
            "omittedLabels": 0,
            "omittedSourceRefs": 0,
            "omittedReasons": ["normalization did not run after validation failure"]
        },
        "nonConclusions": [
            "Validation failure viewer data is a diagnostic projection, not a measurement scene."
        ]
    })
}

fn validation_failure_refs(
    archmap_validation: &Value,
    law_policy_validation: &Value,
    law_surface_validation: Option<&Value>,
    repair_plan_validation: Option<&Value>,
) -> Vec<String> {
    let mut refs = Vec::new();
    refs.extend(validation_report_failure_refs(
        "archmap-validation",
        archmap_validation,
    ));
    refs.extend(validation_report_failure_refs(
        "law-policy-validation",
        law_policy_validation,
    ));
    if let Some(law_surface_validation) = law_surface_validation {
        refs.extend(validation_report_failure_refs(
            "law-surface-validation",
            law_surface_validation,
        ));
    }
    if let Some(repair_plan_validation) = repair_plan_validation {
        refs.extend(validation_report_failure_refs(
            "repair-plan-validation",
            repair_plan_validation,
        ));
    }
    if refs.is_empty() {
        refs.push("validation:failed".to_string());
    }
    refs
}

fn validation_report_failure_refs(prefix: &str, report: &Value) -> Vec<String> {
    report["checks"]
        .as_array()
        .into_iter()
        .flatten()
        .filter(|check| check["result"].as_str() == Some("fail"))
        .map(|check| {
            format!(
                "{}:{}",
                prefix,
                check["id"]
                    .as_str()
                    .or_else(|| check["checkId"].as_str())
                    .unwrap_or("failed-check")
            )
        })
        .collect()
}

fn validation_failure_scene(failed_refs: &[String]) -> Value {
    serde_json::json!({
        "sceneId": "boundary-assumption",
        "kind": "validation_boundary",
        "title": "Validation Boundary",
        "sceneStatus": "active",
        "userQuestion": "Why did ArchSig stop before measurement?",
        "axisMapping": {
            "x": "input contract",
            "y": "validation result",
            "z": "blocked measurement stage"
        },
        "primaryRefs": {
            "insightRefs": ["insight:validation-failure:001"],
            "validationRefs": failed_refs,
            "atomRefs": [],
            "contextRefs": [],
            "coverRefs": [],
            "sourceRefs": []
        },
        "layers": [{
            "layerId": "layer:boundary-assumption:validation-wall",
            "kind": "boundary_wall",
            "geometryRole": "wall",
            "encodingRef": "encoding:boundary-assumption:validation",
            "clickTargetKind": "validationBlocker",
            "refs": {
                "validationRefs": failed_refs
            },
            "omissionPolicy": "preserve_for_top_insight",
            "animationPurpose": "navigation"
        }],
        "visualEncodings": [{
            "encodingId": "encoding:boundary-assumption:validation",
            "colorRole": "not_computed",
            "shapeRole": "wall_fog",
            "lineRole": "broken_line",
            "textRole": "validation blocker before measurement"
        }],
        "boundaryDigestRef": "boundary-digest:validation"
    })
}
