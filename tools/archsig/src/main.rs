use std::collections::BTreeSet;
use std::error::Error;
use std::path::{Path, PathBuf};
use std::process::ExitCode;

use archsig::{
    ARCHMAP_V1_SCHEMA, ArchMapDocumentV1, ArchMapDocumentV2, LAW_POLICY_V1_SCHEMA,
    LawPolicyDocumentV1, SchemaVersionCatalogV0, build_architecture_distance_v1,
    build_comparison_artifacts_v1, build_foundation_measurement_packet_v1, build_gate_report_v1,
    build_insight_brief_v1, build_insight_report_v1, build_measurement_summary_v1,
    build_measurement_viewer_data_v1, build_typed_analysis_packet_v1,
    build_typed_analysis_summary_v1, build_typed_analysis_validation_v1,
    build_typed_atom_viewer_data_v1, build_typed_detail_index_v1,
    build_typed_llm_interpretation_packet_v1, enrich_architecture_distance_with_part4_bundle_v1,
    evaluate_typed_v1, normalize_archmap_v1, normalize_archmap_v2,
    static_law_evaluator_registry_v1, static_schema_version_catalog, validate_archmap_v1_report,
    validate_archmap_v2_report, validate_law_policy_v1_report, validate_measurement_packet_v1,
};
use clap::{Parser, Subcommand};
use serde_json::Value;

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

        /// Append a wall-clock suffix to the deterministic run id. Omitted by default to keep byte-identical outputs.
        #[arg(long)]
        stamp: bool,
    },

    /// Apply a gate policy to an ArchSig measurement packet.
    Gate {
        /// Input archsig-measurement-packet/v0.5.0 JSON path.
        #[arg(long)]
        packet: PathBuf,

        /// Input archsig-gate-policy/v0.5.0 JSON path.
        #[arg(long)]
        policy: PathBuf,

        /// Optional archsig-comparison-report/v0.5.0 JSON path for introduced-by-change rules.
        #[arg(long)]
        comparison: Option<PathBuf>,

        /// Output archsig-gate-report/v0.5.0 JSON path. If omitted, JSON is written to stdout.
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
    },

    /// Produce a lightweight ArchSig PR review report from base ArchMap v1, PR-local ArchMap delta, and LawPolicy v1.
    PrReview {
        /// Input base archmap/v0.5.0 JSON path.
        #[arg(long = "base-archmap")]
        base_archmap: PathBuf,

        /// Optional typed head archmap/v0.5.0 JSON path.
        #[arg(long = "after-archmap")]
        after_archmap: Option<PathBuf>,

        /// Optional typed intermediate archmap/v0.5.0 JSON path. May be supplied multiple times.
        #[arg(long = "path-archmap")]
        path_archmap: Vec<PathBuf>,

        /// Input archmap-delta/v0.5.0 JSON path. This is the PR-local ArchMap observation delta.
        #[arg(long = "delta-archmap")]
        delta_archmap: PathBuf,

        /// Input law-policy/v0.5.0 JSON path.
        #[arg(long = "law-policy")]
        law_policy: PathBuf,

        /// Output archsig-pr-review-report/v0.5.0 JSON path. If omitted, JSON is written to stdout.
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
    match json_schema(&raw) {
        Some(ARCHMAP_V1_SCHEMA) if is_archmap_v2_shape(&raw) => {
            let document: ArchMapDocumentV2 = serde_json::from_value(raw)?;
            let report = validate_archmap_v2_report(&document, &input.display().to_string());
            let failed = report.summary.result == "fail";
            Ok((serde_json::to_value(report)?, failed, false))
        }
        Some(ARCHMAP_V1_SCHEMA) => {
            let document: ArchMapDocumentV1 = serde_json::from_value(raw)?;
            let report = validate_archmap_v1_report(&document, &input.display().to_string());
            let failed = report.summary.result == "fail";
            Ok((serde_json::to_value(report)?, failed, true))
        }
        _ => {
            require_schema(&raw, ARCHMAP_V1_SCHEMA, "--input")?;
            unreachable!("require_schema returns on success for archmap/v0.5.0")
        }
    }
}

fn is_archmap_v2_shape(document: &serde_json::Value) -> bool {
    document.get("extractionDoctrineRef").is_some()
        || document.get("contexts").is_some()
        || document.get("covers").is_some()
        || document
            .get("atoms")
            .and_then(|value| value.as_array())
            .is_some_and(|atoms| atoms.iter().any(|atom| atom.get("axis").is_some()))
}

fn require_structural_archmap_shape(
    document: &serde_json::Value,
    field_name: &str,
) -> Result<(), Box<dyn Error>> {
    if is_archmap_v2_shape(document) {
        return Err(format!(
            "{field_name} must use structural ArchMap shape under {ARCHMAP_V1_SCHEMA}; finite-poset-site ArchMap shape is accepted by archmap/analyze, not pr-review"
        )
        .into());
    }
    Ok(())
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
    document.get("schema").and_then(|value| value.as_str())
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

fn build_pr_review_v1_analysis(
    label: &str,
    archmap_path: &Path,
    archmap_document: &Value,
    law_policy_document: &LawPolicyDocumentV1,
    law_policy_path: &Path,
) -> Result<Value, Box<dyn Error>> {
    let archmap_typed: ArchMapDocumentV1 = serde_json::from_value(archmap_document.clone())
        .map_err(|error| {
            format!(
                "{} failed ArchMap v1 validation for pr-review: {error}",
                archmap_path.display()
            )
        })?;
    let archmap_validation =
        validate_archmap_v1_report(&archmap_typed, &archmap_path.display().to_string());
    if archmap_validation.summary.result == "fail" {
        return Err(format!(
            "{} failed ArchMap v1 validation for pr-review",
            archmap_path.display()
        )
        .into());
    }
    let normalized = normalize_archmap_v1(&archmap_typed, &archmap_path.display().to_string());
    let typed_results = evaluate_typed_v1(
        &normalized,
        law_policy_document,
        &static_law_evaluator_registry_v1(),
        &format!("pr-review:{label}:normalized-archmap.json"),
        &law_policy_path.display().to_string(),
    );
    let architecture_distance =
        build_architecture_distance_v1(&normalized, law_policy_document, &typed_results)
            .map_err(|message| -> Box<dyn Error> { message.into() })?;
    let packet =
        build_typed_analysis_packet_v1(&normalized, &typed_results, &architecture_distance);
    let detail_index = build_typed_detail_index_v1(&typed_results, &packet);
    let detail_refs = typed_results
        .results
        .iter()
        .chain(typed_results.replacement_evaluator_results.iter())
        .flat_map(|result| result.detail_refs.iter().cloned())
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect::<Vec<_>>();

    Ok(serde_json::json!({
        "analysisLabel": label,
        "archmapPath": archmap_path.display().to_string(),
        "archmapSchema": ARCHMAP_V1_SCHEMA,
        "packetRef": format!("report:/v1Analysis/{label}"),
        "packetSchema": packet["schema"],
        "analysisId": packet["analysisId"],
        "architectureDistanceRef": format!("report:/v1Analysis/{label}/architectureDistanceSummary"),
        "architectureDistanceSummary": architecture_distance["summary"],
        "distanceDiagnosis": packet["distanceDiagnosis"],
        "typedEvaluatorSummary": typed_results.summary,
        "typedEvaluatorResults": typed_results.results,
        "positiveBoundedConclusions": typed_results.positive_bounded_conclusions,
        "detailRefs": detail_refs,
        "generatedPacketRefs": packet["generatedPacketRefs"],
        "structuralPacketRefs": {
            "generatedObstructions": packet["generatedPacketRefs"]["generatedObstructions"],
            "generatedRepairTargets": packet["generatedPacketRefs"]["generatedRepairTargets"],
            "architectureSpectrumReport": packet["generatedPacketRefs"]["architectureSpectrumReport"],
            "architectureHomotopyReport": packet["generatedPacketRefs"]["architectureHomotopyReport"],
            "structuralReadingReviewSurface": packet["generatedPacketRefs"]["structuralReadingReviewSurface"],
            "representationMetricReadings": packet["generatedPacketRefs"]["representationMetricReadings"],
            "observationProjectionReadings": packet["generatedPacketRefs"]["observationProjectionReadings"],
            "stateTransitionAlgebraReadings": packet["generatedPacketRefs"]["stateTransitionAlgebraReadings"],
            "effectRelationAlgebraReadings": packet["generatedPacketRefs"]["effectRelationAlgebraReadings"],
            "synthesisBlockageReadings": packet["generatedPacketRefs"]["synthesisBlockageReadings"],
            "operationPreconditionReadinessReadings": packet["generatedPacketRefs"]["operationPreconditionReadinessReadings"],
            "pathMultiplicityLossReadings": packet["generatedPacketRefs"]["pathMultiplicityLossReadings"]
        },
        "structuralReadingReviewSurface": packet["structuralReadingReviewSurface"],
        "structuralReadingRefs": packet["structuralReadingReviewSurface"]["connectedReadingRefs"],
        "detailIndexSummary": {
            "schema": detail_index["schema"],
            "entryCount": detail_index["entries"].as_array().map(Vec::len).unwrap_or_default(),
            "refDictionaryCount": detail_index["refDictionary"].as_array().map(Vec::len).unwrap_or_default()
        },
        "detailIndexEntries": compact_detail_entries(&detail_index),
        "nonConclusions": [
            "PR review analysis snapshot is derived from ArchMap v1 + LawPolicy v1, not from raw diff.",
            "Report-local packet refs are evidence navigation refs, not proof objects."
        ]
    }))
}

fn compact_detail_entries(detail_index: &Value) -> Vec<Value> {
    detail_index["entries"]
        .as_array()
        .into_iter()
        .flatten()
        .filter(|entry| {
            entry["supportAtomRefs"]
                .as_array()
                .is_some_and(|refs| !refs.is_empty())
                || entry["normalizedAtomRefs"]
                    .as_array()
                    .is_some_and(|refs| !refs.is_empty())
        })
        .map(|entry| {
            serde_json::json!({
                "resultRef": entry["resultRef"],
                "packetRef": entry["packetRef"],
                "status": entry["status"],
                "supportAtomRefs": entry["supportAtomRefs"],
                "normalizedAtomRefs": entry["normalizedAtomRefs"],
                "detailRefs": entry["detailRefs"]
            })
        })
        .collect()
}

fn delta_packet_ref_intersections(changed_refs: &[String], analyses: &[(String, &Value)]) -> Value {
    Value::Array(
        changed_refs
            .iter()
            .map(|changed_ref| {
                let normalized_ref = format!("n:{changed_ref}");
                let snapshot_matches = analyses
                    .iter()
                    .filter_map(|(label, analysis)| {
                        let matched_entries = analysis["detailIndexEntries"]
                            .as_array()
                            .into_iter()
                            .flatten()
                            .filter(|entry| entry_mentions_atom_ref(entry, &normalized_ref))
                            .map(|entry| {
                                serde_json::json!({
                                    "resultRef": entry["resultRef"],
                                    "packetRef": entry["packetRef"],
                                    "status": entry["status"],
                                    "supportAtomRefs": entry["supportAtomRefs"],
                                    "normalizedAtomRefs": entry["normalizedAtomRefs"],
                                    "detailRefs": entry["detailRefs"]
                                })
                            })
                            .collect::<Vec<_>>();
                        (!matched_entries.is_empty()).then(|| {
                            serde_json::json!({
                                "analysisLabel": label,
                                "analysisRef": analysis["packetRef"],
                                "matchedPacketRefCount": matched_entries.len(),
                                "matchedPacketRefs": matched_entries
                            })
                        })
                    })
                    .collect::<Vec<_>>();
                let matched_count = snapshot_matches
                    .iter()
                    .map(|snapshot| snapshot["matchedPacketRefCount"].as_u64().unwrap_or(0))
                    .sum::<u64>();
                let matched_packet_refs = snapshot_matches
                    .iter()
                    .flat_map(|snapshot| {
                        snapshot["matchedPacketRefs"]
                            .as_array()
                            .into_iter()
                            .flatten()
                            .cloned()
                    })
                    .collect::<Vec<_>>();
                serde_json::json!({
                    "deltaRef": changed_ref,
                    "normalizedAtomRef": normalized_ref,
                    "matchedPacketRefCount": matched_count,
                    "snapshotMatches": snapshot_matches,
                    "matchedPacketRefs": matched_packet_refs,
                    "status": if matched_count == 0 {
                        "blockedByMissingPacketRefIntersection"
                    } else {
                        "matchedDerivedPacketRefs"
                    },
                    "nonConclusion": "delta ref matching is bounded to supplied ArchMap v1 atom ids and v1 detail index refs"
                })
            })
            .collect(),
    )
}

fn entry_mentions_atom_ref(entry: &Value, normalized_ref: &str) -> bool {
    ["supportAtomRefs", "normalizedAtomRefs"]
        .into_iter()
        .any(|field| {
            entry[field]
                .as_array()
                .is_some_and(|refs| refs.iter().any(|reference| reference == normalized_ref))
        })
}

fn pr_structural_diagnosis(
    base_analysis: &Value,
    after_analysis: Option<&Value>,
    path_analyses: &[Value],
    delta_intersections: &Value,
) -> Value {
    let base_total = measured_total(base_analysis);
    let after_total = after_analysis.map(measured_total);
    let endpoint_delta = after_total.map(|after_total| after_total - base_total);
    let path_totals = path_analyses.iter().map(measured_total).collect::<Vec<_>>();
    let total_path_movement = if path_totals.is_empty() && after_total.is_none() {
        None
    } else {
        let mut previous = base_total;
        let mut total = 0_i64;
        for next in path_totals.iter().copied().chain(after_total) {
            total += (next - previous).abs();
            previous = next;
        }
        Some(total)
    };
    let unmatched_delta_count = delta_intersections
        .as_array()
        .into_iter()
        .flatten()
        .filter(|entry| entry["matchedPacketRefCount"].as_u64().unwrap_or(0) == 0)
        .count();
    let blocked_count = std::iter::once(base_analysis)
        .chain(after_analysis)
        .chain(path_analyses.iter())
        .map(pr_analysis_blocked_count)
        .sum::<u64>();
    let safe_change_status = if unmatched_delta_count > 0 {
        "blockedByUnmatchedDeltaRefs"
    } else if blocked_count > 0 {
        "blockedByIncompleteTypedSupport"
    } else if endpoint_delta.is_some_and(|delta| delta > 0) {
        "needsReviewForIncreasedDistance"
    } else {
        "boundedNoNewSelectedObstruction"
    };

    serde_json::json!({
        "schema": "archsig-pr-structural-diagnosis/v0.5.0",
        "basis": "ArchMapDelta refs + v1 typed evaluator results + v1 generated packet refs",
        "basePacketRef": base_analysis["packetRef"],
        "afterPacketRef": after_analysis
            .map(|analysis| analysis["packetRef"].clone())
            .unwrap_or(Value::Null),
        "pathPacketRefs": path_analyses
            .iter()
            .map(|analysis| analysis["packetRef"].clone())
            .collect::<Vec<_>>(),
        "endpointDistanceMovement": endpoint_delta
            .map(|delta| serde_json::json!({
                "status": "measuredFromSuppliedBaseAndAfterArchMap",
                "baseMeasuredTotal": base_total,
                "afterMeasuredTotal": after_total.unwrap_or(base_total),
                "delta": delta,
                "unit": "architecture-distance-point"
            }))
            .unwrap_or_else(|| serde_json::json!({
                "status": "blockedWithoutAfterArchMap",
                "blockerRefs": ["afterArchMap:not-supplied"],
                "reading": "missing head ArchMap is blocked, not measured zero"
            })),
        "totalPathMovement": total_path_movement
            .map(|movement| serde_json::json!({
                "status": if path_analyses.is_empty() {
                    "measuredEndpointOnly"
                } else {
                    "measuredFromSuppliedIntermediateArchMaps"
                },
                "measuredTotal": movement,
                "unit": "architecture-distance-point"
            }))
            .unwrap_or_else(|| serde_json::json!({
                "status": "blockedWithoutAfterArchMap",
                "blockerRefs": ["afterArchMap:not-supplied"]
            })),
        "hiddenExcursionBoundary": if after_analysis.is_some() && path_analyses.is_empty() {
            serde_json::json!({
                "status": "blockedWithoutIntermediateArchMapPathSnapshots",
                "reading": "endpoint movement is visible, hidden excursion requires supplied path ArchMaps"
            })
        } else if after_analysis.is_some() {
            serde_json::json!({
                "status": "boundedBySuppliedIntermediateArchMaps",
                "pathSnapshotCount": path_analyses.len()
            })
        } else {
            serde_json::json!({
                "status": "blockedWithoutAfterArchMap"
            })
        },
        "safeChangeBudget": {
            "status": safe_change_status,
            "unmatchedDeltaRefCount": unmatched_delta_count,
            "blockedOrUnmeasuredSupportCount": blocked_count,
            "reading": "blocked / unknown / unmeasured support limits review budget and is not measured zero"
        },
        "structuralReadingRefs": base_analysis["structuralReadingRefs"],
        "reviewFocusRefs": review_focus_refs(delta_intersections),
        "nonConclusions": [
            "PR structural diagnosis is not merge approval.",
            "PR structural diagnosis does not forecast future incidents.",
            "Hidden excursion is bounded to supplied ArchMap path snapshots."
        ]
    })
}

fn measured_total(analysis: &Value) -> i64 {
    analysis["architectureDistanceSummary"]["measuredTotal"]
        .as_i64()
        .unwrap_or(0)
}

fn pr_analysis_blocked_count(analysis: &Value) -> u64 {
    analysis["typedEvaluatorSummary"]["blockedCount"]
        .as_u64()
        .unwrap_or(0)
        + analysis["typedEvaluatorSummary"]["unknownCount"]
            .as_u64()
            .unwrap_or(0)
        + analysis["typedEvaluatorSummary"]["unmeasuredCount"]
            .as_u64()
            .unwrap_or(0)
        + analysis["architectureDistanceSummary"]["blockedOrUnmeasuredCount"]
            .as_u64()
            .unwrap_or(0)
}

fn review_focus_refs(delta_intersections: &Value) -> Vec<String> {
    delta_intersections
        .as_array()
        .into_iter()
        .flatten()
        .flat_map(|intersection| {
            intersection["matchedPacketRefs"]
                .as_array()
                .into_iter()
                .flatten()
        })
        .filter_map(|entry| {
            entry["packetRef"]
                .as_str()
                .or_else(|| entry["resultRef"].as_str())
                .map(str::to_string)
        })
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect()
}

fn required_string_array(value: &Value, field: &str) -> Result<Vec<String>, Box<dyn Error>> {
    let Some(items) = value.get(field).and_then(Value::as_array) else {
        return Err(format!("{field} must be a non-empty string array").into());
    };
    if items.is_empty() {
        return Err(format!("{field} must be a non-empty string array").into());
    }
    let mut strings = Vec::with_capacity(items.len());
    for item in items {
        let Some(text) = item.as_str() else {
            return Err(format!("{field} must contain only strings").into());
        };
        if text.trim().is_empty() {
            return Err(format!("{field} must not contain blank refs").into());
        }
        strings.push(text.to_string());
    }
    Ok(strings)
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
        Some(Command::Gate {
            packet,
            policy,
            comparison,
            out,
        }) => {
            let (report, exit_code) = build_gate_report_v1(&packet, &policy, comparison.as_deref())?;
            write_json(out, &report)?;
            Ok(ExitCode::from(exit_code as u8))
        }
        Some(Command::Compare {
            base_run,
            head_run,
            out_dir,
        }) => {
            let (archmap_diff, comparison_report) =
                build_comparison_artifacts_v1(&base_run, &head_run)?;
            std::fs::create_dir_all(&out_dir)?;
            write_json(Some(out_dir.join("archmap-diff.json")), &archmap_diff)?;
            write_json(
                Some(out_dir.join("archsig-comparison-report.json")),
                &comparison_report,
            )?;
            Ok(ExitCode::SUCCESS)
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
            require_structural_archmap_shape(&base_archmap_document, "--base-archmap")?;
            require_schema(&law_policy_document, LAW_POLICY_V1_SCHEMA, "--law-policy")?;
            let law_policy_typed: LawPolicyDocumentV1 = serde_json::from_value(
                law_policy_document.clone(),
            )
            .map_err(|error| {
                format!(
                    "{} failed LawPolicy v1 validation for pr-review: {error}",
                    law_policy.display()
                )
            })?;
            let law_policy_validation =
                validate_law_policy_v1_report(&law_policy_typed, &law_policy.display().to_string());
            if law_policy_validation.summary.result == "fail" {
                return Err(format!(
                    "{} failed LawPolicy v1 validation for pr-review",
                    law_policy.display()
                )
                .into());
            }
            if after_archmap.is_none() && !path_archmap.is_empty() {
                return Err(
                    "--path-archmap requires --after-archmap so endpoint movement is bounded"
                        .into(),
                );
            }
            let base_analysis = build_pr_review_v1_analysis(
                "base",
                &base_archmap,
                &base_archmap_document,
                &law_policy_typed,
                &law_policy,
            )?;
            let after_analysis = after_archmap
                .as_ref()
                .map(|after_archmap| {
                    let after_archmap_document: Value = read_json(after_archmap)?;
                    require_schema(&after_archmap_document, ARCHMAP_V1_SCHEMA, "--after-archmap")?;
                    require_structural_archmap_shape(&after_archmap_document, "--after-archmap")?;
                    build_pr_review_v1_analysis(
                        "after",
                        after_archmap,
                        &after_archmap_document,
                        &law_policy_typed,
                        &law_policy,
                    )
                })
                .transpose()?;
            let path_analyses = path_archmap
                .iter()
                .enumerate()
                .map(|(index, path_archmap)| {
                    let path_archmap_document: Value = read_json(path_archmap)?;
                    require_schema(
                        &path_archmap_document,
                        ARCHMAP_V1_SCHEMA,
                        "--path-archmap",
                    )?;
                    require_structural_archmap_shape(&path_archmap_document, "--path-archmap")?;
                    build_pr_review_v1_analysis(
                        &format!("path-{index}"),
                        path_archmap,
                        &path_archmap_document,
                        &law_policy_typed,
                        &law_policy,
                    )
                })
                .collect::<Result<Vec<_>, Box<dyn Error>>>()?;
            let delta_archmap_document: serde_json::Value = read_json(&delta_archmap)?;
            require_schema(&delta_archmap_document, "archmap-delta/v0.5.0", "--delta-archmap")?;
            let changed_refs = required_string_array(&delta_archmap_document, "changedObservationRefs")?;
            let mut intersection_analyses = vec![("base".to_string(), &base_analysis)];
            if let Some(after_analysis) = after_analysis.as_ref() {
                intersection_analyses.push(("after".to_string(), after_analysis));
            }
            for (index, analysis) in path_analyses.iter().enumerate() {
                intersection_analyses.push((format!("path-{index}"), analysis));
            }
            let delta_packet_ref_intersections =
                delta_packet_ref_intersections(&changed_refs, &intersection_analyses);
            let pr_structural_diagnosis = pr_structural_diagnosis(
                &base_analysis,
                after_analysis.as_ref(),
                &path_analyses,
                &delta_packet_ref_intersections,
            );
            let report = serde_json::json!({
                "schema": "archsig-pr-review-report/v0.5.0",
                "reviewKind": "v1-output-replacement-structural-pr-review",
                "canonicalInputs": {
                    "baseArchMap": {
                        "path": base_archmap.display().to_string(),
                        "schema": json_schema(&base_archmap_document)
                    },
                    "afterArchMap": after_archmap.as_ref().map(|path| serde_json::json!({
                        "path": path.display().to_string(),
                        "schema": ARCHMAP_V1_SCHEMA
                    })).unwrap_or(Value::Null),
                    "pathArchMaps": path_archmap.iter().map(|path| serde_json::json!({
                        "path": path.display().to_string(),
                        "schema": ARCHMAP_V1_SCHEMA
                    })).collect::<Vec<_>>(),
                    "deltaArchMap": {
                        "path": delta_archmap.display().to_string(),
                        "schema": json_schema(&delta_archmap_document),
                        "changedObservationRefs": changed_refs
                    },
                    "lawPolicy": {
                        "path": law_policy.display().to_string(),
                        "schema": json_schema(&law_policy_document)
                    }
                },
                "typedEvaluatorSummary": base_analysis["typedEvaluatorSummary"],
                "typedEvaluatorResults": base_analysis["typedEvaluatorResults"],
                "positiveBoundedConclusions": base_analysis["positiveBoundedConclusions"],
                "v1Analysis": {
                    "base": base_analysis,
                    "after": after_analysis.unwrap_or(Value::Null),
                    "path": path_analyses
                },
                "deltaPacketRefIntersections": delta_packet_ref_intersections,
                "prStructuralDiagnosis": pr_structural_diagnosis,
                "reviewFocus": {
                    "rule": "Review changed refs against typed evaluator statuses and v1 derived packet refs; blocked, unknown, and unmeasured are not measured zero.",
                    "detailRefs": base_analysis["detailRefs"],
                    "packetRefs": base_analysis["structuralPacketRefs"],
                    "changedRefPacketIntersections": delta_packet_ref_intersections
                },
                "nonConclusions": [
                    "v1 pr-review is bounded to supplied ArchMap v1, LawPolicy v1, delta refs, and evaluator registry results.",
                    "v1 pr-review reads derived output replacement refs; it does not accept v0 base/head packets as input.",
                    "safe change budget and hidden excursion are review cues, not merge approval or future incident forecast.",
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
            stamp,
        }) => {
            let archmap_validation_path = out_dir.join("archmap-validation.json");
            let law_policy_validation_path = out_dir.join("law-policy-validation.json");
            let analysis_summary_path = out_dir.join("archsig-analysis-summary.json");
            let atom_viewer_data_path = out_dir.join("archsig-atom-viewer-data.json");
            let run_manifest_path = out_dir.join("archsig-run-manifest.json");
            let normalized_archmap_path = out_dir.join("normalized-archmap.json");
            let typed_evaluator_results_path = out_dir.join("typed-evaluator-results.json");
            let architecture_distance_path = out_dir.join("architecture-distance.json");
            let measurement_packet_path = out_dir.join("archsig-measurement-packet.json");
            let insight_report_path = out_dir.join("archsig-insight-report.json");
            let insight_brief_path = out_dir.join("archsig-insight-brief.md");
            let analysis_packet_path = out_dir.join("archsig-analysis-packet.json");
            let analysis_validation_path = out_dir.join("archsig-analysis-validation.json");
            let llm_interpretation_path = out_dir.join("llm-interpretation-packet.json");

            let (archmap_preflight, archmap_failed, archmap_is_v1) =
                validate_archmap_command_input(&archmap)?;
            let (law_policy_preflight, law_policy_failed, law_policy_is_v1) =
                validate_law_policy_command_input(&law_policy)?;
            if !law_policy_is_v1 {
                return Err("archsig analyze accepts only law-policy/v0.5.0".into());
            }
            let archmap_input_ref = artifact_input_ref(&archmap);
            let law_policy_input_ref = artifact_input_ref(&law_policy);
            let archmap_contract_input: Value = read_json(&archmap)?;
            let law_policy_contract_input: Value = read_json(&law_policy)?;
            let run_contract = AnalyzeRunContract::from_inputs(
                &archmap,
                &law_policy,
                contract_profile_fingerprint(&law_policy_contract_input, archmap_is_v1)?,
                contract_site_cover_digest(&archmap_contract_input, archmap_is_v1)?,
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
            if archmap_failed || law_policy_failed {
                let mut insight_report = build_validation_failure_insight_report(
                    &archmap_preflight,
                    &law_policy_preflight,
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
                        "schema": "archsig-run-manifest/v0.5.0",
                        "toolVersion": run_contract.tool_version.clone(),
                        "runId": run_contract.run_id.clone(),
                        "inputDigests": run_contract.input_digests.clone(),
                        "commandName": "analyze",
                        "mode": "validation-failure",
                        "conclusionCode": "VALIDATION_FAILED_BEFORE_MEASUREMENT",
                        "archmapInputPath": archmap_input_ref,
                        "lawPolicyInputPath": law_policy_input_ref,
                        "rawArtifactRetention": "not-computed",
                        "generatedArtifacts": [
                            "archmap-validation.json",
                            "law-policy-validation.json",
                            "archsig-insight-report.json",
                            "archsig-insight-brief.md",
                            "archsig-atom-viewer-data.json",
                            "archsig-run-manifest.json"
                        ],
                        "omittedArtifacts": [
                            "normalized-archmap.json",
                            "typed-evaluator-results.json",
                            "architecture-distance.json",
                            "archsig-measurement-packet.json",
                            "archsig-analysis-validation.json",
                            "archsig-analysis-summary.json",
                            "archsig-analysis-packet.json",
                            "archsig-analysis-detail-index.json",
                            "llm-interpretation-packet.json"
                        ],
                        "artifactLinks": {
                            "insightReport": "archsig-insight-report.json",
                            "insightBrief": "archsig-insight-brief.md",
                            "viewerData": "archsig-atom-viewer-data.json"
                        },
                        "validationReports": {
                            "archmap": "archmap-validation.json",
                            "lawPolicy": "law-policy-validation.json",
                            "analysis": null
                        },
                        "rawArtifactPaths": null,
                        "validationResultSummary": {
                            "archmap": validation_result_summary(&archmap_preflight),
                            "lawPolicy": validation_result_summary(&law_policy_preflight),
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
                return Ok(ExitCode::from(2));
            }
            if !archmap_is_v1 {
                let law_policy_document: LawPolicyDocumentV1 = read_json(&law_policy)?;
                let archmap_document: ArchMapDocumentV2 = read_json(&archmap)?;
                let normalized_archmap =
                    normalize_archmap_v2(&archmap_document, &archmap_input_ref);
                write_json(
                    Some(normalized_archmap_path),
                    &with_run_contract(&normalized_archmap, &run_contract)?,
                )?;
                let measurement_packet = build_foundation_measurement_packet_v1(
                    &normalized_archmap,
                    &law_policy_document,
                    &archmap_input_ref,
                    &law_policy_input_ref,
                )
                .map_err(|message| -> Box<dyn Error> { message.into() })?;
                let packet_validation = validate_measurement_packet_v1(&measurement_packet);
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
                    Some(measurement_packet_path),
                    &with_run_contract(&measurement_packet, &run_contract)?,
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
                    &measurement_packet,
                    &measurement_summary,
                    &insight_report,
                );
                write_json(
                    Some(analysis_validation_path),
                    &with_run_contract(&serde_json::json!({
                        "schema": "archsig-measurement-packet-validation-report/v0.5.0",
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
                    &with_run_contract(&measurement_viewer_data, &run_contract)?,
                )?;
                write_json(
                    Some(insight_report_path),
                    &with_run_contract(&insight_report, &run_contract)?,
                )?;
                std::fs::write(insight_brief_path, insight_brief)?;
                write_json(
                    Some(run_manifest_path),
                    &serde_json::json!({
                        "schema": "archsig-run-manifest/v0.5.0",
                        "toolVersion": run_contract.tool_version.clone(),
                        "runId": run_contract.run_id.clone(),
                        "inputDigests": run_contract.input_digests.clone(),
                        "commandName": "analyze",
                        "mode": "measurement",
                        "conclusionCode": null,
                        "archmapInputPath": archmap_input_ref,
                        "lawPolicyInputPath": law_policy_input_ref,
                        "rawArtifactRetention": "omitted",
                        "generatedArtifacts": [
                            "archmap-validation.json",
                            "law-policy-validation.json",
                            "normalized-archmap.json",
                            "archsig-measurement-packet.json",
                            "archsig-analysis-validation.json",
                            "archsig-analysis-summary.json",
                            "archsig-insight-report.json",
                            "archsig-insight-brief.md",
                            "archsig-atom-viewer-data.json",
                            "archsig-run-manifest.json"
                        ],
                        "omittedArtifacts": [
                            "typed-evaluator-results.json",
                            "architecture-distance.json",
                            "archsig-analysis-packet.json",
                            "archsig-analysis-detail-index.json",
                            "llm-interpretation-packet.json"
                        ],
                        "artifactLinks": {
                            "measurementPacket": "archsig-measurement-packet.json",
                            "summary": "archsig-analysis-summary.json",
                            "insightReport": "archsig-insight-report.json",
                            "insightBrief": "archsig-insight-brief.md",
                            "viewerData": "archsig-atom-viewer-data.json"
                        },
                        "validationReports": {
                            "archmap": "archmap-validation.json",
                            "lawPolicy": "law-policy-validation.json",
                            "analysis": "archsig-analysis-validation.json"
                        },
                        "rawArtifactPaths": null,
                        "validationResultSummary": {
                            "archmap": validation_result_summary(&archmap_preflight),
                            "lawPolicy": validation_result_summary(&law_policy_preflight),
                            "analysis": validation_result_summary_from_counts(
                                if packet_failed { "fail" } else { "pass" },
                                packet_failed_check_count,
                                packet_warning_check_count
                            )
                        },
                        "nonConclusions": [
                            "Finite-poset-site run manifest records the v0.5.0 AG measurement foundation artifacts.",
                            "Foundation packet rows are not completed AG invariant evaluator computation."
                        ]
                    }),
                )?;
                let non_terminal_count = measurement_summary["structuralVerdictSummary"]
                    ["nonTerminalCount"]
                    .as_u64()
                    .unwrap_or(0);
                let analytic_not_computed_count = measurement_packet
                    .computed_invariants
                    .iter()
                    .filter(|invariant| {
                        invariant["status"]
                            .as_str()
                            .is_some_and(|status| status == "not_computed")
                    })
                    .count();
                let violated_assumption_count =
                    measurement_summary["assumptionSummary"]["violatedCount"]
                        .as_u64()
                        .unwrap_or(0);
                if strict_distance
                    && (non_terminal_count > 0
                        || analytic_not_computed_count > 0
                        || violated_assumption_count > 0)
                {
                    eprintln!(
                        "--strict-distance rejected v2 measurement foundation with unmeasured structural verdict rows, not_computed analytic invariants, or violated assumptions"
                    );
                    return Ok(ExitCode::from(1));
                }
                return Ok(if packet_failed {
                    ExitCode::from(2)
                } else {
                    ExitCode::SUCCESS
                });
            }
            let law_policy_document: LawPolicyDocumentV1 = read_json(&law_policy)?;
            if strict_distance && law_policy_document.distance_profile_ref.is_none() {
                eprintln!("--strict-distance rejected law-policy/v0.5.0 without distanceProfileRef");
                return Ok(ExitCode::from(1));
            }
            let archmap_document: ArchMapDocumentV1 = read_json(&archmap)?;
            let normalized_archmap = normalize_archmap_v1(&archmap_document, &archmap_input_ref);
            write_json(
                Some(normalized_archmap_path),
                &with_run_contract(&normalized_archmap, &run_contract)?,
            )?;
            let typed_results = evaluate_typed_v1(
                &normalized_archmap,
                &law_policy_document,
                &static_law_evaluator_registry_v1(),
                "normalized-archmap.json",
                &law_policy_input_ref,
            );
            write_json(
                Some(typed_evaluator_results_path),
                &with_run_contract(&typed_results, &run_contract)?,
            )?;
            let base_architecture_distance = build_architecture_distance_v1(
                &normalized_archmap,
                &law_policy_document,
                &typed_results,
            )
            .map_err(|message| -> Box<dyn Error> { message.into() })?;
            let base_analysis_packet = build_typed_analysis_packet_v1(
                &normalized_archmap,
                &typed_results,
                &base_architecture_distance,
            );
            let architecture_distance = enrich_architecture_distance_with_part4_bundle_v1(
                &base_architecture_distance,
                &base_analysis_packet,
                emit_raw_artifacts,
            );
            write_json(
                Some(architecture_distance_path),
                &with_run_contract(&architecture_distance, &run_contract)?,
            )?;
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
            write_json(
                Some(analysis_validation_path),
                &with_run_contract(&analysis_validation, &run_contract)?,
            )?;
            write_json(
                Some(analysis_summary_path.clone()),
                &with_run_contract(&analysis_summary, &run_contract)?,
            )?;
            write_json(
                Some(atom_viewer_data_path.clone()),
                &with_run_contract(&atom_viewer_data, &run_contract)?,
            )?;
            if emit_raw_artifacts {
                write_json(
                    Some(analysis_packet_path),
                    &with_run_contract(&analysis_packet, &run_contract)?,
                )?;
                write_json(
                    Some(out_dir.join("archsig-analysis-detail-index.json")),
                    &with_run_contract(
                        &build_typed_detail_index_v1(&typed_results, &analysis_packet),
                        &run_contract,
                    )?,
                )?;
                write_json(
                    Some(llm_interpretation_path),
                    &with_run_contract(&build_typed_llm_interpretation_packet_v1(
                        &normalized_archmap,
                        &typed_results,
                        &architecture_distance,
                    ), &run_contract)?,
                )?;
            }
            write_json(
                Some(run_manifest_path),
                &build_analyze_run_manifest_v1(
                    &run_contract,
                    &archmap,
                    &law_policy,
                    "measurement",
                    None,
                    emit_raw_artifacts,
                    validation_result_summary(&archmap_preflight),
                    validation_result_summary(&law_policy_preflight),
                    validation_result_summary(&analysis_validation),
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
            if strict_distance
                && architecture_distance["measurementStateSummary"]["missingCanonicalFamilyCount"]
                    .as_u64()
                    .unwrap_or(0)
                    > 0
            {
                eprintln!(
                    "--strict-distance rejected v1 architecture distance with missing canonical Part IV distance families"
                );
                return Ok(ExitCode::from(1));
            }
            if strict_distance
                && architecture_distance["measurementStateSummary"]["status"].as_str()
                    != Some("measured")
            {
                eprintln!(
                    "--strict-distance rejected v1 architecture distance with incomplete canonical distance family states"
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
        "archsig-measurement-packet.json",
        "archsig-insight-report.json",
        "archsig-insight-brief.md",
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

fn build_validation_failure_insight_report(
    archmap_validation: &Value,
    law_policy_validation: &Value,
) -> Value {
    let failed_refs = validation_failure_refs(archmap_validation, law_policy_validation);
    let primary_ref = failed_refs
        .first()
        .cloned()
        .unwrap_or_else(|| "validation:unknown-failure".to_string());
    serde_json::json!({
        "schema": "archsig-insight-report/v0.5.0",
        "reportId": "insight:validation-failure",
        "sourcePacketRef": null,
        "generatedAt": "deterministic-run-artifact",
        "outputArtifacts": {
            "summaryRef": null,
            "briefRef": "archsig-insight-brief.md",
            "viewerDataRef": "archsig-atom-viewer-data.json"
        },
        "headline": {
            "conclusionCode": "VALIDATION_FAILED_BEFORE_MEASUREMENT",
            "title": "Validation failed before measurement",
            "summary": "ArchSig stopped before normalization because an input validation check failed.",
            "decisionState": "blocked",
            "primaryVerdictRefs": [],
            "boundaryDigestRef": "boundary-digest:validation"
        },
        "readThisFirst": {
            "heading": "Read this first",
            "conclusion": "VALIDATION_FAILED_BEFORE_MEASUREMENT",
            "whatItMeans": "No measurement packet or AG invariant was computed. Fix the failing ArchMap or LawPolicy validation first.",
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
        "schema": "archsig-atom-viewer-data/v0.5.0",
        "sourceArtifactRefs": {
            "archmapValidation": "archmap-validation.json",
            "lawPolicyValidation": "law-policy-validation.json",
            "insightReport": "archsig-insight-report.json",
            "insightBrief": "archsig-insight-brief.md"
        },
        "decisionBar": {
            "conclusion": "VALIDATION_FAILED_BEFORE_MEASUREMENT",
            "validation": "see archmap-validation.json and law-policy-validation.json",
            "boundaryDigest": insight_report["boundaryDigest"]["shortText"],
            "artifactLinks": insight_report["outputArtifacts"]
        },
        "insightQueue": insight_report["insightCards"],
        "actionQueue": insight_report["actionQueue"],
        "viewerVisualScenes": insight_report["viewerVisualScenes"],
        "guidedTours": insight_report["guidedTours"],
        "copyBlocks": insight_report["copyBlocks"],
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
