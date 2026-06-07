use std::collections::BTreeSet;
use std::error::Error;
use std::path::{Path, PathBuf};
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
    },

    /// Produce a lightweight ArchSig PR review report from base ArchMap v1, PR-local ArchMap delta, and LawPolicy v1.
    PrReview {
        /// Input base archmap/v1 JSON path.
        #[arg(long = "base-archmap")]
        base_archmap: PathBuf,

        /// Optional typed head archmap/v1 JSON path.
        #[arg(long = "after-archmap")]
        after_archmap: Option<PathBuf>,

        /// Optional typed intermediate archmap/v1 JSON path. May be supplied multiple times.
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
            "schemaVersion": detail_index["schemaVersion"],
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
        "schema": "archsig-pr-structural-diagnosis/v1",
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
            require_schema(&delta_archmap_document, "archmap-delta-v0", "--delta-archmap")?;
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
                "schemaVersion": "archsig-pr-review-report-v1",
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
                        "schemaVersion": json_schema(&delta_archmap_document),
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
                        &normalized_archmap,
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
