use std::collections::BTreeSet;
use std::error::Error;
use std::path::PathBuf;
use std::process::ExitCode;

use archsig::{
    ARCHMAP_V1_SCHEMA, ArchMapDocumentV1, LAW_POLICY_V1_SCHEMA, LawPolicyDocumentV1,
    SchemaVersionCatalogV0, build_architecture_distance_v1, build_typed_analysis_packet_v1,
    build_typed_analysis_summary_v1, build_typed_analysis_validation_v1,
    build_typed_atom_viewer_data_v1, build_typed_detail_index_v1,
    build_typed_llm_interpretation_packet_v1, evaluate_typed_v1, normalize_archmap_v1,
    static_law_evaluator_registry_v1, static_schema_version_catalog, validate_archmap_v1_report,
    validate_law_policy_v1_report,
};
use clap::{Parser, Subcommand};

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

        /// Output ArchMap validation report JSON path. If omitted, JSON is written to stdout.
        #[arg(long)]
        out: Option<PathBuf>,
    },

    /// Validate a LawPolicy v1 selector artifact for ArchSig AAT analysis.
    LawPolicy {
        /// Input LawPolicy v1 JSON path.
        #[arg(long)]
        input: PathBuf,

        /// Output LawPolicy fixture or validation report JSON path. If omitted, JSON is written to stdout.
        #[arg(long)]
        out: Option<PathBuf>,
    },

    /// Run the primary ArchMap + LawPolicy -> ArchSig analysis workflow.
    Analyze {
        /// Input ArchMap observation artifact path.
        #[arg(long)]
        archmap: PathBuf,

        /// Input LawPolicy artifact path.
        #[arg(long = "law-policy")]
        law_policy: PathBuf,

        /// Output directory for ArchSig analysis workflow artifacts.
        #[arg(long = "out-dir")]
        out_dir: PathBuf,

        /// Also write full raw analysis artifacts for FieldSig handoff and deep evidence lookup.
        #[arg(long = "emit-raw-artifacts")]
        emit_raw_artifacts: bool,

        /// Fail when architecture distance would rely on missing profile selection or unmeasured rows.
        #[arg(long = "strict-distance")]
        strict_distance: bool,
    },

    /// Produce a lightweight ArchSig PR review report from base ArchMap v1, PR-local ArchMap delta, and LawPolicy v1.
    PrReview {
        /// Input base archmap/v1 JSON path.
        #[arg(long = "base-archmap")]
        base_archmap: PathBuf,

        /// Reserved for future typed head review. Current v1 PR review rejects this option.
        #[arg(long = "after-archmap")]
        after_archmap: Option<PathBuf>,

        /// Reserved for future typed path review. Current v1 PR review rejects this option.
        #[arg(long = "path-archmap")]
        path_archmap: Vec<PathBuf>,

        /// Input archmap-delta-v0 JSON path. This is the PR-local ArchMap observation delta.
        #[arg(long = "delta-archmap")]
        delta_archmap: PathBuf,

        /// Input law-policy/v1 JSON path.
        #[arg(long = "law-policy")]
        law_policy: PathBuf,

        /// Output archsig-pr-review-report-v1 JSON path. If omitted, JSON is written to stdout.
        #[arg(long)]
        out: Option<PathBuf>,
    },

    /// Emit the current LLM Atom ArchMap schema catalog.
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
            ExitCode::from(2)
        }
    }
}

fn validate_archmap_command_input(
    input: &PathBuf,
) -> Result<(serde_json::Value, bool, bool), Box<dyn Error>> {
    let raw: serde_json::Value = read_json(input)?;
    require_schema(&raw, ARCHMAP_V1_SCHEMA, "--input")?;
    let document: ArchMapDocumentV1 = serde_json::from_value(raw)?;
    let report = validate_archmap_v1_report(&document, &input.display().to_string());
    let failed = report.summary.result == "fail";
    Ok((serde_json::to_value(report)?, failed, true))
}

fn validate_law_policy_command_input(
    input: &PathBuf,
) -> Result<(serde_json::Value, bool, bool), Box<dyn Error>> {
    let raw: serde_json::Value = read_json(input)?;
    require_schema(&raw, LAW_POLICY_V1_SCHEMA, "--input")?;
    let policy: LawPolicyDocumentV1 = serde_json::from_value(raw)?;
    let report = validate_law_policy_v1_report(&policy, &input.display().to_string());
    let failed = report.summary.result == "fail";
    Ok((serde_json::to_value(report)?, failed, true))
}

fn json_schema(document: &serde_json::Value) -> Option<&str> {
    document
        .get("schema")
        .or_else(|| document.get("schemaVersion"))
        .and_then(|value| value.as_str())
}

fn summary_result(document: &serde_json::Value) -> &str {
    document["summary"]["result"].as_str().unwrap_or("fail")
}

fn run() -> Result<ExitCode, Box<dyn Error>> {
    let args = Args::parse();

    match args.command {
        Some(Command::Archmap { input, out }) => {
            let (report, failed, _) = validate_archmap_command_input(&input)?;
            write_json(out, &report)?;
            Ok(if failed {
                ExitCode::from(1)
            } else {
                ExitCode::SUCCESS
            })
        }
        Some(Command::LawPolicy {
            input,
            out,
        }) => {
            let (report, failed, _) = validate_law_policy_command_input(&input)?;
            write_json(out, &report)?;
            Ok(if failed {
                ExitCode::from(1)
            } else {
                ExitCode::SUCCESS
            })
        }
        Some(Command::PrReview {
            base_archmap,
            after_archmap,
            path_archmap,
            delta_archmap,
            law_policy,
            out,
        }) => {
            let base_archmap_document: serde_json::Value = read_json(&base_archmap)?;
            let law_policy_document: serde_json::Value = read_json(&law_policy)?;
            require_schema(&base_archmap_document, ARCHMAP_V1_SCHEMA, "--base-archmap")?;
            require_schema(&law_policy_document, LAW_POLICY_V1_SCHEMA, "--law-policy")?;
            if after_archmap.is_some() || !path_archmap.is_empty() {
                return Err(
                    "v1 pr-review accepts only base archmap, delta archmap, and law-policy/v1; typed head/path review is not current runtime surface"
                        .into(),
                );
            }
            let base_archmap_typed: ArchMapDocumentV1 =
                serde_json::from_value(base_archmap_document.clone())?;
            let normalized =
                normalize_archmap_v1(&base_archmap_typed, &base_archmap.display().to_string());
            let law_policy_typed: LawPolicyDocumentV1 =
                serde_json::from_value(law_policy_document.clone())?;
            let typed_results = evaluate_typed_v1(
                &normalized,
                &law_policy_typed,
                &static_law_evaluator_registry_v1(),
                "normalized-archmap.json",
                &law_policy.display().to_string(),
            );
            let delta_archmap_document: serde_json::Value = read_json(&delta_archmap)?;
            require_schema(&delta_archmap_document, "archmap-delta-v0", "--delta-archmap")?;
            let report = serde_json::json!({
                "schemaVersion": "archsig-pr-review-report-v1",
                "reviewKind": "typed-evaluator-pr-review",
                "canonicalInputs": {
                    "baseArchMap": {
                        "path": base_archmap.display().to_string(),
                        "schema": json_schema(&base_archmap_document)
                    },
                    "deltaArchMap": {
                        "path": delta_archmap.display().to_string(),
                        "schemaVersion": json_schema(&delta_archmap_document),
                        "changedObservationRefs": delta_archmap_document
                            .get("changedObservationRefs")
                            .cloned()
                            .unwrap_or(serde_json::Value::Array(Vec::new()))
                    },
                    "lawPolicy": {
                        "path": law_policy.display().to_string(),
                        "schema": json_schema(&law_policy_document)
                    }
                },
                "typedEvaluatorSummary": typed_results.summary,
                "typedEvaluatorResults": typed_results.results,
                "positiveBoundedConclusions": typed_results.positive_bounded_conclusions,
                "reviewFocus": {
                    "rule": "Review changed refs against typed evaluator statuses; blocked, unknown, and unmeasured are not measured zero.",
                    "detailRefs": typed_results.results.iter()
                        .flat_map(|result| result.detail_refs.iter().cloned())
                        .collect::<BTreeSet<_>>()
                        .into_iter()
                        .collect::<Vec<_>>()
                },
                "nonConclusions": [
                    "v1 pr-review is bounded to supplied ArchMap v1, LawPolicy v1, delta refs, and evaluator registry results.",
                    "v1 pr-review does not reconstruct v0 witness rules, signature axes, coverage requirements, or distance formulas.",
                    "v1 pr-review is not a Lean proof object."
                ]
            });
            write_json(out, &report)?;
            Ok(ExitCode::SUCCESS)
        }
        Some(Command::Analyze {
            archmap,
            law_policy,
            out_dir,
            emit_raw_artifacts,
            strict_distance,
        }) => {
            let archmap_validation_path = out_dir.join("archmap-validation.json");
            let law_policy_validation_path = out_dir.join("law-policy-validation.json");
            let analysis_summary_path = out_dir.join("archsig-analysis-summary.json");
            let atom_viewer_data_path = out_dir.join("archsig-atom-viewer-data.json");
            let run_manifest_path = out_dir.join("archsig-run-manifest.json");
            let normalized_archmap_path = out_dir.join("normalized-archmap.json");
            let typed_evaluator_results_path = out_dir.join("typed-evaluator-results.json");
            let architecture_distance_path = out_dir.join("architecture-distance.json");
            let analysis_packet_path = out_dir.join("archsig-analysis-packet.json");
            let analysis_validation_path = out_dir.join("archsig-analysis-validation.json");
            let llm_interpretation_path = out_dir.join("llm-interpretation-packet.json");

            let (archmap_preflight, archmap_failed, archmap_is_v1) =
                validate_archmap_command_input(&archmap)?;
            let (law_policy_preflight, law_policy_failed, law_policy_is_v1) =
                validate_law_policy_command_input(&law_policy)?;
            if !archmap_is_v1 || !law_policy_is_v1 {
                return Err("archsig analyze accepts only archmap/v1 and law-policy/v1".into());
            }
            std::fs::create_dir_all(&out_dir)?;
            remove_analyze_success_artifacts(&out_dir)?;
            write_json(Some(archmap_validation_path), &archmap_preflight)?;
            write_json(Some(law_policy_validation_path), &law_policy_preflight)?;
            if archmap_failed || law_policy_failed {
                eprintln!(
                    "archsig analyze wrote v1 validation artifacts to {} and stopped before normalization",
                    out_dir.display()
                );
                return Ok(ExitCode::from(1));
            }
            let law_policy_document: LawPolicyDocumentV1 = read_json(&law_policy)?;
            if strict_distance && law_policy_document.distance_profile_ref.is_none() {
                eprintln!("--strict-distance rejected law-policy/v1 without distanceProfileRef");
                return Ok(ExitCode::from(1));
            }
            let archmap_document: ArchMapDocumentV1 = read_json(&archmap)?;
            let normalized_archmap =
                normalize_archmap_v1(&archmap_document, &archmap.display().to_string());
            write_json(Some(normalized_archmap_path), &normalized_archmap)?;
            let typed_results = evaluate_typed_v1(
                &normalized_archmap,
                &law_policy_document,
                &static_law_evaluator_registry_v1(),
                "normalized-archmap.json",
                &law_policy.display().to_string(),
            );
            write_json(Some(typed_evaluator_results_path), &typed_results)?;
            let architecture_distance = build_architecture_distance_v1(
                &normalized_archmap,
                &law_policy_document,
                &typed_results,
            )
            .map_err(|message| -> Box<dyn Error> { message.into() })?;
            write_json(Some(architecture_distance_path), &architecture_distance)?;
            let analysis_packet = build_typed_analysis_packet_v1(
                &normalized_archmap,
                &typed_results,
                &architecture_distance,
            );
            let analysis_summary = build_typed_analysis_summary_v1(
                &normalized_archmap,
                &typed_results,
                &architecture_distance,
            );
            let atom_viewer_data = build_typed_atom_viewer_data_v1(
                &normalized_archmap,
                &typed_results,
                &analysis_summary,
            );
            let analysis_validation =
                build_typed_analysis_validation_v1(&analysis_packet, &typed_results);
            write_json(Some(analysis_validation_path), &analysis_validation)?;
            write_json(Some(analysis_summary_path.clone()), &analysis_summary)?;
            write_json(Some(atom_viewer_data_path.clone()), &atom_viewer_data)?;
            if emit_raw_artifacts {
                write_json(Some(analysis_packet_path), &analysis_packet)?;
                write_json(
                    Some(out_dir.join("archsig-analysis-detail-index.json")),
                    &build_typed_detail_index_v1(&typed_results, &analysis_packet),
                )?;
                write_json(
                    Some(llm_interpretation_path),
                    &build_typed_llm_interpretation_packet_v1(
                        &typed_results,
                        &architecture_distance,
                    ),
                )?;
            }
            write_json(
                Some(run_manifest_path),
                &build_analyze_run_manifest_v1(
                    &archmap,
                    &law_policy,
                    emit_raw_artifacts,
                    summary_result(&archmap_preflight),
                    summary_result(&law_policy_preflight),
                    analysis_validation["summary"]["result"]
                        .as_str()
                        .unwrap_or("fail"),
                ),
            )?;
            if strict_distance
                && typed_results.summary.blocked_count
                    + typed_results.summary.unknown_count
                    + typed_results.summary.unmeasured_count
                    + typed_results.replacement_summary.blocked_count
                    > 0
            {
                eprintln!(
                    "--strict-distance rejected v1 typed evaluator results with blocked, unknown, unmeasured, or replacement-blocked distance statuses"
                );
                return Ok(ExitCode::from(1));
            }
            if strict_distance
                && architecture_distance["summary"]["blockedOrUnmeasuredCount"]
                    .as_u64()
                    .unwrap_or(0)
                    > 0
            {
                eprintln!(
                    "--strict-distance rejected v1 architecture distance with blocked or unmeasured readings"
                );
                return Ok(ExitCode::from(1));
            }
            Ok(ExitCode::SUCCESS)
        }
        Some(Command::SchemaCatalog { out }) => {
            let catalog: SchemaVersionCatalogV0 = static_schema_version_catalog();
            write_json(out, &catalog)?;
            Ok(ExitCode::SUCCESS)
        }
        None => {
            Err("ArchSig is ArchMap/LawPolicy/analysis-packet primary; use `archsig analyze` for the main analysis path.".into())
        }
    }
}

fn remove_analyze_success_artifacts(out_dir: &PathBuf) -> Result<(), Box<dyn Error>> {
    for artifact in [
        "archsig-analysis-summary.json",
        "archsig-atom-viewer-data.json",
        "archsig-run-manifest.json",
        "normalized-archmap.json",
        "typed-evaluator-results.json",
        "architecture-distance.json",
        "archsig-analysis-packet.json",
        "archsig-analysis-detail-index.json",
        "archsig-analysis-validation.json",
        "llm-interpretation-packet.json",
    ] {
        let path = out_dir.join(artifact);
        match std::fs::remove_file(&path) {
            Ok(()) => {}
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => {}
            Err(error) => return Err(Box::new(error)),
        }
    }
    Ok(())
}
