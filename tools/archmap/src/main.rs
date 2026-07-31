use std::collections::{BTreeMap, BTreeSet};
use std::error::Error;
use std::path::{Path, PathBuf};
use std::process::ExitCode;

use archmap::{
    ARCHMAP_CANDIDATE_PACKET_V1_SCHEMA, ARCHMAP_COVERAGE_LEDGER_V1_SCHEMA,
    ARCHMAP_EXTRACTION_CONSISTENCY_V1_SCHEMA, ARCHMAP_SCOPE_MANIFEST_V1_SCHEMA, ARCHMAP_V2_SCHEMA,
    AuthoringAuditInputV1, ExtractionDiffOptions, ScopeManifestOptions, SupplyBenchOptions,
    SupplyBenchPairInput, archmap_authoring_audit_checks_v1, build_extraction_consistency_v1,
    build_scope_manifest_v1, parse_candidate_packet_value, validate_authoring_audit_input_v1,
};
use archsig::{
    ArchMapDocumentV2, ArchMapValidationReportV2, ArchmapCoverageLedgerV1,
    ArchmapExtractionConsistencyV1, ArchmapScopeManifestV1, validate_archmap_v2_report,
};
use clap::{Parser, Subcommand};
use globset::{Glob, GlobSetBuilder};
use serde_json::Value;
use walkdir::WalkDir;

mod io;
use io::*;

#[derive(Debug, Parser)]
#[command(
    version,
    about = "Author and validate source-grounded ArchMap artifacts"
)]
struct Args {
    #[command(subcommand)]
    command: Command,
}

#[derive(Debug, Subcommand)]
enum Command {
    /// Validate an ArchMap observation artifact and optional authoring audit.
    Archmap {
        #[arg(long)]
        input: PathBuf,
        #[arg(long = "scope-manifest")]
        scope_manifest: Option<PathBuf>,
        #[arg(long = "candidate-packets")]
        candidate_packets: Vec<String>,
        #[arg(long = "extraction-consistency")]
        extraction_consistency: Vec<PathBuf>,
        #[arg(long = "coverage-ledger")]
        coverage_ledger: Option<PathBuf>,
        #[arg(long)]
        out: Option<PathBuf>,
    },
    /// Build a deterministic authoring scope manifest worklist.
    ScopeManifest {
        #[arg(long = "repo-root", default_value = ".")]
        repo_root: PathBuf,
        #[arg(long = "include", required = true)]
        include: Vec<String>,
        #[arg(long = "exclude")]
        exclude: Vec<String>,
        #[arg(long = "add-evidence")]
        add_evidence: Vec<String>,
        #[arg(long)]
        baseline: Option<PathBuf>,
        #[arg(long, default_value = "scope:archmap-authoring")]
        id: String,
        #[arg(long = "requested-scope")]
        requested_scope: Option<String>,
        #[arg(long = "approved-by")]
        approved_by: Option<String>,
        #[arg(long = "revision-override")]
        revision_override: Option<String>,
        #[arg(long = "dirty-override")]
        dirty_override: Option<bool>,
        #[arg(long)]
        out: Option<PathBuf>,
    },
    /// Compare two authoring passes without adjudicating adoption.
    ExtractionDiff {
        #[arg(long = "pass-a", required = true)]
        pass_a: Vec<PathBuf>,
        #[arg(long = "pass-b")]
        pass_b: Vec<PathBuf>,
        #[arg(long, default_value = "consistency:archmap-authoring")]
        id: String,
        #[arg(long = "scope-manifest-ref")]
        scope_manifest_ref: Option<String>,
        #[arg(long)]
        out: Option<PathBuf>,
    },
    /// Compute deterministic supply-bench metrics over consistency artifacts.
    SupplyBench {
        #[arg(long = "pair", required = true)]
        pair: Vec<String>,
        #[arg(long = "chunk-class")]
        chunk_class: Vec<String>,
        #[arg(long = "alignment")]
        alignment: Vec<String>,
        #[arg(long)]
        reference: Option<PathBuf>,
        #[arg(long = "series-key")]
        series_key: Option<PathBuf>,
        #[arg(long, default_value = "supply-bench:archmap-authoring")]
        id: String,
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

fn run() -> Result<ExitCode, Box<dyn Error>> {
    match Args::parse().command {
        Command::Archmap {
            input,
            scope_manifest,
            candidate_packets,
            extraction_consistency,
            coverage_ledger,
            out,
        } => {
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
        Command::ScopeManifest {
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
        } => {
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
        Command::ExtractionDiff {
            pass_a,
            pass_b,
            id,
            scope_manifest_ref,
            out,
        } => {
            let report = build_extraction_consistency_v1(&ExtractionDiffOptions {
                pass_a,
                pass_b,
                id,
                scope_manifest_ref,
            })?;
            write_json(out, &report)?;
            Ok(ExitCode::SUCCESS)
        }
        Command::SupplyBench {
            pair,
            chunk_class,
            alignment,
            reference,
            series_key,
            id,
            out,
        } => {
            let chunk_classes = parse_pair_assignments(&chunk_class, "--chunk-class")?;
            let alignments = parse_pair_assignments(&alignment, "--alignment")?;
            let mut pairs = Vec::new();
            let mut pair_ids = BTreeSet::new();
            for entry in &pair {
                let (pair_id, path) = entry
                    .split_once('=')
                    .ok_or_else(|| format!("--pair must be <pair-id>=<path>, got {entry}"))?;
                pair_ids.insert(pair_id.to_string());
                pairs.push(SupplyBenchPairInput {
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
            let report = archmap::build_supply_bench_report_v1(&SupplyBenchOptions {
                id,
                pairs,
                reference,
                series_key,
            })?;
            write_json(out, &report)?;
            Ok(ExitCode::SUCCESS)
        }
    }
}

fn validate_archmap_command_input(
    input: &PathBuf,
    scope_manifest: &Option<PathBuf>,
    candidate_packets: &[String],
    extraction_consistency: &[PathBuf],
    coverage_ledger: &Option<PathBuf>,
) -> Result<(Value, bool), Box<dyn Error>> {
    let raw: Value = read_json(input)?;
    if raw.get("schema").and_then(Value::as_str) != Some(ARCHMAP_V2_SCHEMA) {
        require_schema(&raw, ARCHMAP_V2_SCHEMA, "--input")?;
    }
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
        validate_authoring_audit_input_v1(&audit_input).map_err(|errors| errors.join("; "))?;
        report
            .checks
            .extend(archmap_authoring_audit_checks_v1(&document, &audit_input));
        refresh_archmap_report_summary(&mut report);
    }
    let failed = report.summary.result == "fail";
    Ok((serde_json::to_value(report)?, failed))
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

    let scope_manifest_raw: Value = read_json(scope_manifest_path)?;
    require_schema(
        &scope_manifest_raw,
        ARCHMAP_SCOPE_MANIFEST_V1_SCHEMA,
        "--scope-manifest",
    )?;
    let coverage_ledger_raw: Value = read_json(coverage_ledger_path)?;
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
        let raw: Value = read_json(&path)?;
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
        let raw: Value = read_json(path)?;
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
    Path::new(prefix)
        .parent()
        .filter(|path| !path.as_os_str().is_empty())
        .unwrap_or_else(|| Path::new("."))
        .to_path_buf()
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

fn stable_input_ref(input: &Path) -> String {
    let file_name = input
        .file_name()
        .and_then(|name| name.to_str())
        .unwrap_or("artifact.json");
    format!("input:{file_name}")
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
