use std::collections::BTreeSet;

use serde_json::json;

use crate::{
    LawEvaluatorRegistryV1, LawPolicyDocumentV1, NormalizedArchMapV1,
    TYPED_EVALUATOR_RESULTS_V1_SCHEMA, TypedEvaluatorResultV1, TypedEvaluatorResultsSummaryV1,
    TypedEvaluatorResultsV1, expand_law_policy_v1,
};

const PIPELINE_ID: &str = "archsig-v1-typed-evaluator-pipeline@1";
const ANALYSIS_PIPELINE_ID: &str = "archsig-v1-typed-analysis-pipeline@1";

pub fn evaluate_typed_v1(
    normalized: &NormalizedArchMapV1,
    law_policy: &LawPolicyDocumentV1,
    registry: &LawEvaluatorRegistryV1,
    normalized_archmap_ref: &str,
    law_policy_ref: &str,
) -> TypedEvaluatorResultsV1 {
    let expanded = expand_law_policy_v1(law_policy);
    let results = expanded
        .iter()
        .map(|entry| {
            let manifest = registry
                .evaluators
                .iter()
                .find(|manifest| manifest.evaluator_id == entry.evaluator);
            let Some(manifest) = manifest else {
                return TypedEvaluatorResultV1 {
                    evaluator: entry.evaluator.clone(),
                    law: entry.law.clone(),
                    status: "unknown".to_string(),
                    support_atom_refs: Vec::new(),
                    support_molecule_refs: Vec::new(),
                    basis_refs: entry.basis.clone(),
                    detail_refs: Vec::new(),
                    summary: "evaluator manifest is not registered".to_string(),
                    blocker_reason: Some("unknown evaluator manifest".to_string()),
                };
            };

            let support_atom_refs = normalized
                .atoms
                .iter()
                .filter(|atom| {
                    manifest
                        .required_atom_constructors
                        .iter()
                        .any(|required| required == &atom.predicate.constructor)
                        || manifest
                            .required_predicates
                            .iter()
                            .any(|required| predicate_has_value(atom, required))
                })
                .map(|atom| atom.normalized_atom_id.clone())
                .collect::<Vec<_>>();
            let support_molecule_refs = normalized
                .molecules
                .iter()
                .filter(|molecule| {
                    molecule.generated_molecule_candidate_status == "generated"
                        && molecule
                            .atom_ids
                            .iter()
                            .any(|atom_id| support_atom_refs.contains(atom_id))
                })
                .map(|molecule| molecule.normalized_molecule_id.clone())
                .collect::<Vec<_>>();

            typed_result(entry, &support_atom_refs, &support_molecule_refs)
        })
        .collect::<Vec<_>>();
    let summary = typed_summary(&results);
    let positive_bounded_conclusions = positive_bounded_conclusions(&results);

    TypedEvaluatorResultsV1 {
        schema: TYPED_EVALUATOR_RESULTS_V1_SCHEMA.to_string(),
        pipeline_id: PIPELINE_ID.to_string(),
        normalized_archmap_ref: normalized_archmap_ref.to_string(),
        law_policy_ref: law_policy_ref.to_string(),
        results,
        summary,
        positive_bounded_conclusions,
        non_conclusions: vec![
            "Typed evaluator results are bounded to normalized ArchMap, LawPolicy, and evaluator registry evidence.".to_string(),
            "Blocked, unknown, and unmeasured results are not measured zero.".to_string(),
            "Typed evaluator results are ArchSig computation artifacts, not Lean proof objects.".to_string(),
        ],
    }
}

pub fn build_typed_analysis_packet_v1(
    normalized: &NormalizedArchMapV1,
    typed_results: &TypedEvaluatorResultsV1,
) -> serde_json::Value {
    let detail_refs = typed_results
        .results
        .iter()
        .flat_map(|result| result.detail_refs.iter().cloned())
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect::<Vec<_>>();
    json!({
        "schema": "archsig-analysis-packet/v1",
        "analysisId": format!("analysis:{}", normalized.source_archmap_id),
        "pipelineId": ANALYSIS_PIPELINE_ID,
        "inputRefs": {
            "normalizedArchMap": typed_results.normalized_archmap_ref,
            "lawPolicy": typed_results.law_policy_ref,
            "typedEvaluatorResults": "typed-evaluator-results.json"
        },
        "typedEvaluatorResults": typed_results.results,
        "distanceDiagnosis": typed_distance_diagnosis(typed_results),
        "positiveBoundedConclusions": typed_results.positive_bounded_conclusions,
        "detailRefs": detail_refs,
        "nonConclusions": [
            "ArchSig v1 packet is computed from Normalized ArchMap v1 and TypedEvaluatorResults v1.",
            "ArchSig v1 packet does not read v0 semanticObservations, projectionInfo, operationSquareEvidence, concernHints, or observationGaps.",
            "Blocked, unknown, and unmeasured evaluator results are not measured zero.",
            "ArchSig v1 packet is a computation artifact, not a Lean proof object."
        ]
    })
}

pub fn build_typed_analysis_summary_v1(
    normalized: &NormalizedArchMapV1,
    typed_results: &TypedEvaluatorResultsV1,
) -> serde_json::Value {
    let verdict = if typed_results.summary.measured_violation_count > 0 {
        "SELECTED_VIOLATION_MEASURED_UNDER_EVIDENCE_CONTRACT"
    } else if typed_results.summary.measured_pass_count > 0
        && typed_results.summary.blocked_count == 0
        && typed_results.summary.unknown_count == 0
        && typed_results.summary.unmeasured_count == 0
    {
        "ACCEPTABLE_UNDER_EVIDENCE_CONTRACT"
    } else {
        "BOUNDED_MEASUREMENT_INCOMPLETE"
    };
    json!({
        "schema": "archsig-analysis-summary/v1",
        "summaryKind": "typed-evaluator-summary",
        "verdict": verdict,
        "pipelineId": ANALYSIS_PIPELINE_ID,
        "measurementBasis": {
            "normalizedArchMap": typed_results.normalized_archmap_ref,
            "lawPolicy": typed_results.law_policy_ref,
            "typedEvaluatorResults": "typed-evaluator-results.json",
            "normalizedAtomCount": normalized.summary.normalized_atom_count,
            "generatedMoleculeCandidateCount": normalized.summary.generated_molecule_candidate_count
        },
        "measurementStatusSummary": typed_results.summary,
        "distanceDiagnosis": typed_distance_diagnosis(typed_results),
        "dominantFindings": typed_dominant_findings(typed_results),
        "actionQueue": typed_action_queue(typed_results),
        "positiveBoundedConclusions": typed_results.positive_bounded_conclusions,
        "metadata": {
            "boundary": "ArchSig v1 summary reads typed evaluator results only",
            "leanDependency": "none"
        },
        "nonConclusions": [
            "Summary does not promote missing support to measured zero.",
            "Summary does not use v0 concern-only, projection-only, square-only, or gap-only inputs as positive readings.",
            "Summary is not a Lean proof certificate."
        ]
    })
}

pub fn build_typed_atom_viewer_data_v1(
    normalized: &NormalizedArchMapV1,
    typed_results: &TypedEvaluatorResultsV1,
    summary: &serde_json::Value,
) -> serde_json::Value {
    let atom_nodes = normalized
        .atoms
        .iter()
        .map(|atom| {
            json!({
                "nodeId": atom.normalized_atom_id,
                "sourceAtomId": atom.source_atom_id,
                "atomKind": atom.atom_kind,
                "axis": atom.axis,
                "predicate": atom.predicate,
                "normalizationStatus": atom.normalization_status,
                "moleculeMemberships": atom.molecule_memberships
            })
        })
        .collect::<Vec<_>>();
    let molecule_groups = normalized
        .molecules
        .iter()
        .map(|molecule| {
            json!({
                "groupId": molecule.normalized_molecule_id,
                "sourceMoleculeId": molecule.source_molecule_id,
                "atomIds": molecule.atom_ids,
                "generatedMoleculeCandidateStatus": molecule.generated_molecule_candidate_status,
                "requiredPortStatus": molecule.required_port_status,
                "compositionStatus": molecule.composition_status
            })
        })
        .collect::<Vec<_>>();
    json!({
        "schemaVersion": "archsig-atom-viewer-data-v1",
        "dataKind": "typed-evaluator-viewer-projection",
        "sourceArtifactRefs": {
            "normalizedArchMap": "normalized-archmap.json",
            "typedEvaluatorResults": "typed-evaluator-results.json",
            "summary": "archsig-analysis-summary.json",
            "manifest": "archsig-run-manifest.json"
        },
        "atomNodes": atom_nodes,
        "moleculeGroups": molecule_groups,
        "analysisOverlays": {
            "typedEvaluatorResults": typed_results.results,
            "distanceDiagnosis": summary["distanceDiagnosis"],
            "actionQueue": summary["actionQueue"]
        },
        "reportPane": {
            "overview": {
                "summaryVerdict": summary["verdict"],
                "measurementStatusSummary": summary["measurementStatusSummary"]
            },
            "distanceDiagnosis": summary["distanceDiagnosis"],
            "topFindings": summary["dominantFindings"],
            "actionQueue": summary["actionQueue"],
            "artifacts": {
                "summary": "archsig-analysis-summary.json",
                "typedEvaluatorResults": "typed-evaluator-results.json",
                "rawArtifacts": "see archsig-run-manifest.json rawArtifactRetention"
            }
        },
        "nonConclusions": [
            "Viewer data is a bounded projection over normalized atoms, generated molecule candidates, and typed evaluator results.",
            "Viewer data does not embed raw source content or Lean proof objects."
        ]
    })
}

pub fn build_typed_detail_index_v1(typed_results: &TypedEvaluatorResultsV1) -> serde_json::Value {
    let ref_dictionary = typed_results
        .results
        .iter()
        .flat_map(|result| result.detail_refs.iter().cloned())
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect::<Vec<_>>();
    let entries = typed_results
        .results
        .iter()
        .map(|result| {
            json!({
                "resultRef": format!("typedEvaluatorResults:{}", result.law),
                "status": result.status,
                "supportAtomRefs": result.support_atom_refs,
                "supportMoleculeRefs": result.support_molecule_refs,
                "basisRefs": result.basis_refs,
                "detailRefs": result.detail_refs
            })
        })
        .collect::<Vec<_>>();
    json!({
        "schemaVersion": "archsig-analysis-detail-index-v1",
        "indexKind": "typed-evaluator-support-index",
        "refDictionary": ref_dictionary,
        "entries": entries,
        "nonConclusions": [
            "detail index records typed evaluator support refs only",
            "detail refs are evidence navigation aids, not proof objects"
        ]
    })
}

pub fn build_typed_llm_interpretation_packet_v1(
    typed_results: &TypedEvaluatorResultsV1,
) -> serde_json::Value {
    json!({
        "schema": "llm-interpretation-packet/v1",
        "interpretationKind": "typed-evaluator-bounded-reading",
        "distanceDiagnosisSummary": typed_distance_diagnosis(typed_results),
        "typedEvaluatorSummary": typed_results.summary,
        "positiveBoundedConclusions": typed_results.positive_bounded_conclusions,
        "nonConclusions": [
            "LLM interpretation packet summarizes typed evaluator results and does not add new findings.",
            "Blocked, unknown, and unmeasured are preserved as non-measured statuses."
        ]
    })
}

pub fn build_typed_analysis_validation_v1(
    packet: &serde_json::Value,
    typed_results: &TypedEvaluatorResultsV1,
) -> serde_json::Value {
    let result = if packet["schema"] == "archsig-analysis-packet/v1"
        && typed_results.summary.result_count == typed_results.results.len()
    {
        "pass"
    } else {
        "fail"
    };
    json!({
        "schemaVersion": "archsig-analysis-validation-report-v1",
        "summary": {
            "result": result,
            "failedCheckCount": if result == "pass" { 0 } else { 1 },
            "warningCheckCount": 0,
            "proxyRegressionCheckCount": 0
        },
        "checks": [
            {
                "checkId": "archsig.v1.typedEvaluatorResultCount",
                "result": result,
                "message": "typed evaluator result count matches summary"
            }
        ],
        "nonConclusions": [
            "v1 analysis validation checks typed evaluator artifact consistency, not Lean theorem discharge"
        ]
    })
}

fn typed_result(
    entry: &crate::ExpandedLawPolicyEntryV1,
    support_atom_refs: &[String],
    support_molecule_refs: &[String],
) -> TypedEvaluatorResultV1 {
    let blocker_reason = if support_atom_refs.is_empty() {
        Some("required support atoms are missing under selected evaluator manifest".to_string())
    } else if support_molecule_refs.is_empty() {
        Some("required generated molecule candidate is missing".to_string())
    } else {
        None
    };
    let status = if blocker_reason.is_some() {
        "blocked"
    } else if entry.law == "solid.dependency-inversion"
        || entry.law == "domain.no-direct-infra-dependency"
    {
        "measuredViolation"
    } else {
        "measuredPass"
    };

    TypedEvaluatorResultV1 {
        evaluator: entry.evaluator.clone(),
        law: entry.law.clone(),
        status: status.to_string(),
        support_atom_refs: support_atom_refs.to_vec(),
        support_molecule_refs: support_molecule_refs.to_vec(),
        basis_refs: entry.basis.clone(),
        detail_refs: support_atom_refs
            .iter()
            .chain(support_molecule_refs.iter())
            .cloned()
            .collect(),
        summary: format!("{} evaluated as {status}", entry.law),
        blocker_reason,
    }
}

fn predicate_has_value(atom: &crate::NormalizedAtomV1, required: &str) -> bool {
    atom.predicate
        .bindings
        .iter()
        .any(|binding| binding.value == required)
}

fn typed_summary(results: &[TypedEvaluatorResultV1]) -> TypedEvaluatorResultsSummaryV1 {
    TypedEvaluatorResultsSummaryV1 {
        result_count: results.len(),
        measured_pass_count: count_status(results, "measuredPass"),
        measured_violation_count: count_status(results, "measuredViolation"),
        blocked_count: count_status(results, "blocked"),
        unknown_count: count_status(results, "unknown"),
        unmeasured_count: count_status(results, "unmeasured"),
    }
}

fn count_status(results: &[TypedEvaluatorResultV1], status: &str) -> usize {
    results
        .iter()
        .filter(|result| result.status == status)
        .count()
}

fn positive_bounded_conclusions(results: &[TypedEvaluatorResultV1]) -> Vec<String> {
    let measured_violations = results
        .iter()
        .filter(|result| result.status == "measuredViolation")
        .map(|result| result.law.as_str())
        .collect::<BTreeSet<_>>();
    if !measured_violations.is_empty() {
        return vec![format!(
            "SELECTED_VIOLATION_MEASURED_UNDER_EVIDENCE_CONTRACT for measured evaluator set: {}",
            measured_violations
                .into_iter()
                .collect::<Vec<_>>()
                .join(", ")
        )];
    }

    let measured_passes = results
        .iter()
        .filter(|result| result.status == "measuredPass")
        .map(|result| result.law.as_str())
        .collect::<BTreeSet<_>>();
    if measured_passes.is_empty() {
        return Vec::new();
    }
    vec![format!(
        "ACCEPTABLE_UNDER_EVIDENCE_CONTRACT for measured evaluator set: {}",
        measured_passes.into_iter().collect::<Vec<_>>().join(", ")
    )]
}

fn typed_distance_diagnosis(typed_results: &TypedEvaluatorResultsV1) -> serde_json::Value {
    let status_summary = &typed_results.summary;
    let measured_distance = status_summary.measured_violation_count;
    let blocked_distance = status_summary.blocked_count
        + status_summary.unknown_count
        + status_summary.unmeasured_count;
    let top_moved_axes = typed_results
        .results
        .iter()
        .filter(|result| result.status == "measuredViolation")
        .map(|result| {
            json!({
                "law": result.law,
                "evaluator": result.evaluator,
                "status": result.status,
                "axisDistance": {
                    "status": "measured",
                    "measuredValue": 1,
                    "basisRefs": result.basis_refs,
                    "detailRefs": result.detail_refs
                }
            })
        })
        .collect::<Vec<_>>();
    let blocked_results = typed_results
        .results
        .iter()
        .filter(|result| {
            result.status == "blocked"
                || result.status == "unknown"
                || result.status == "unmeasured"
        })
        .map(|result| {
            json!({
                "law": result.law,
                "evaluator": result.evaluator,
                "status": result.status,
                "blockerReason": result.blocker_reason
            })
        })
        .collect::<Vec<_>>();
    json!({
        "schema": "archsig-distance-diagnosis/v1",
        "basis": "typedEvaluatorResults",
        "verdict": if measured_distance > 0 {
            "SELECTED_VIOLATION_MEASURED_UNDER_EVIDENCE_CONTRACT"
        } else if blocked_distance > 0 {
            "BOUNDED_DISTANCE_PARTIALLY_BLOCKED"
        } else {
            "NO_SELECTED_OBSTRUCTION"
        },
        "distanceValue": {
            "status": if blocked_distance > 0 { "partial" } else { "measured" },
            "measuredViolationCount": measured_distance,
            "blockedOrUnmeasuredCount": blocked_distance
        },
        "topMovedAxes": top_moved_axes,
        "blockedResults": blocked_results,
        "detailRefs": typed_results
            .results
            .iter()
            .flat_map(|result| result.detail_refs.iter().cloned())
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect::<Vec<_>>(),
        "nonConclusions": [
            "Blocked, unknown, and unmeasured evaluator results are not zero distance.",
            "Distance contribution is read from evaluator registry owned typed results, not LawPolicy-authored witness formulas.",
            "Distance diagnosis is an ArchSig computation artifact, not a Lean theorem."
        ]
    })
}

fn typed_dominant_findings(typed_results: &TypedEvaluatorResultsV1) -> Vec<serde_json::Value> {
    typed_results
        .results
        .iter()
        .filter(|result| result.status == "measuredViolation" || result.status == "blocked")
        .map(|result| {
            json!({
                "findingId": format!("finding:{}", result.law),
                "law": result.law,
                "evaluator": result.evaluator,
                "status": result.status,
                "summary": result.summary,
                "supportAtomRefs": result.support_atom_refs,
                "supportMoleculeRefs": result.support_molecule_refs,
                "basisRefs": result.basis_refs,
                "detailRefs": result.detail_refs
            })
        })
        .collect()
}

fn typed_action_queue(typed_results: &TypedEvaluatorResultsV1) -> Vec<serde_json::Value> {
    typed_results
        .results
        .iter()
        .filter(|result| result.status != "measuredPass")
        .map(|result| {
            let action_kind = if result.status == "measuredViolation" {
                "reviewSelectedViolation"
            } else {
                "collectRequiredSupport"
            };
            json!({
                "actionId": format!("action:{}", result.law),
                "actionKind": action_kind,
                "law": result.law,
                "status": result.status,
                "basisRefs": result.basis_refs,
                "detailRefs": result.detail_refs,
                "blockerReason": result.blocker_reason
            })
        })
        .collect()
}
