use std::collections::{BTreeMap, BTreeSet};

use serde_json::{Value, json};

use crate::law_policy::{REPLACEMENT_REGISTRY_REF, is_known_v1_distance_profile};
use crate::{
    ARCHITECTURE_DISTANCE_V1_SCHEMA, LawEvaluatorRegistryV1, LawPolicyDocumentV1,
    NormalizedArchMapV1, NormalizedAtomV1, NormalizedMoleculeV1, ReplacementEvaluatorManifestV1,
    ReplacementRegistryResolutionV1, TYPED_EVALUATOR_RESULTS_V1_SCHEMA, TypedEvaluatorResultV1,
    TypedEvaluatorResultsSummaryV1, TypedEvaluatorResultsV1, expand_law_policy_v1,
};

const PIPELINE_ID: &str = "archsig-v1-typed-evaluator-pipeline@1";
const ANALYSIS_PIPELINE_ID: &str = "archsig-v1-typed-analysis-pipeline@1";

#[derive(Clone, Copy)]
struct ArchitectureDistanceProfileV1 {
    profile_ref: &'static str,
    atom_kind_weight: i64,
    axis_weight: i64,
    predicate_constructor_weight: i64,
    predicate_binding_weight: i64,
    configuration_atom_weight: i64,
    signature_violation_weight: i64,
    dependency_inversion_operation_cost: i64,
    infrastructure_dependency_operation_cost: i64,
    default_operation_cost: i64,
}

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
                    replacement_id: None,
                    replacement_for_v0_field: None,
                    typed_output_packet_refs: Vec::new(),
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

            let support_atoms = normalized
                .atoms
                .iter()
                .filter(|atom| support_atom_refs.contains(&atom.normalized_atom_id))
                .collect::<Vec<_>>();

            typed_result(
                entry,
                &support_atom_refs,
                &support_molecule_refs,
                &support_atoms,
            )
        })
        .collect::<Vec<_>>();
    let replacement_evaluator_results =
        evaluate_replacement_registry_v1(normalized, registry, &results);
    let summary = typed_summary(&results);
    let replacement_summary = typed_summary(&replacement_evaluator_results);
    let replacement_registry_resolution =
        replacement_registry_resolution(&registry.replacement_registry, &replacement_summary);
    let positive_bounded_conclusions = positive_bounded_conclusions(&results);

    TypedEvaluatorResultsV1 {
        schema: TYPED_EVALUATOR_RESULTS_V1_SCHEMA.to_string(),
        pipeline_id: PIPELINE_ID.to_string(),
        normalized_archmap_ref: normalized_archmap_ref.to_string(),
        law_policy_ref: law_policy_ref.to_string(),
        replacement_registry_ref: REPLACEMENT_REGISTRY_REF.to_string(),
        replacement_registry: registry.replacement_registry.clone(),
        results,
        replacement_evaluator_results,
        summary,
        replacement_summary,
        replacement_registry_resolution,
        positive_bounded_conclusions,
        non_conclusions: vec![
            "Typed evaluator results are bounded to normalized ArchMap, LawPolicy, and evaluator registry evidence.".to_string(),
            "Replacement evaluator results are derived from normalized ArchMap and registry manifests, not from removed v0 input fields.".to_string(),
            "Blocked, unknown, and unmeasured results are not measured zero.".to_string(),
            "Typed evaluator results are ArchSig computation artifacts, not Lean proof objects.".to_string(),
        ],
    }
}

pub fn build_typed_analysis_packet_v1(
    normalized: &NormalizedArchMapV1,
    typed_results: &TypedEvaluatorResultsV1,
    architecture_distance: &Value,
) -> serde_json::Value {
    let generated_law_inputs = generated_law_inputs_v1(typed_results);
    let signature_axes = signature_axes_v1(typed_results, architecture_distance);
    let generated_obstructions = generated_obstructions_v1(typed_results);
    let generated_repair_targets = generated_repair_targets_v1(&generated_obstructions);
    let detail_refs = typed_results
        .results
        .iter()
        .chain(typed_results.replacement_evaluator_results.iter())
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
            "typedEvaluatorResults": "typed-evaluator-results.json",
            "replacementRegistry": typed_results.replacement_registry_ref
        },
        "replacementRegistry": typed_results.replacement_registry,
        "replacementRegistryResolution": typed_results.replacement_registry_resolution,
        "typedEvaluatorResults": typed_results.results,
        "replacementEvaluatorResults": typed_results.replacement_evaluator_results,
        "replacementEvaluatorResultsById": replacement_results_by_id(typed_results),
        "typedEvaluatorDiagnosis": typed_evaluator_diagnosis(typed_results),
        "architectureDistance": architecture_distance,
        "distanceDiagnosis": architecture_distance["distanceDiagnosis"],
        "generatedLawInputs": generated_law_inputs,
        "signatureAxes": signature_axes,
        "generatedObstructions": generated_obstructions,
        "generatedRepairTargets": generated_repair_targets,
        "generatedPacketRefs": {
            "basis": "typed-evaluator-results + law-evaluator-registry",
            "generatedLawInputs": "/generatedLawInputs",
            "signatureAxes": "/signatureAxes",
            "generatedObstructions": "/generatedObstructions",
            "generatedRepairTargets": "/generatedRepairTargets",
            "typedEvaluatorResults": "/typedEvaluatorResults",
            "architectureDistanceSignatureReadings": "/architectureDistance/signatureDistanceReadings"
        },
        "positiveBoundedConclusions": typed_results.positive_bounded_conclusions,
        "detailRefs": detail_refs,
        "nonConclusions": [
            "ArchSig v1 packet is computed from Normalized ArchMap v1 and TypedEvaluatorResults v1.",
            "Generated law inputs, signature axes, obstruction candidates, and repair targets are derived packet refs over typed evaluator results and registry basis.",
            "ArchSig v1 packet does not read v0 semanticObservations, projectionInfo, operationSquareEvidence, concernHints, or observationGaps.",
            "Blocked, unknown, and unmeasured evaluator results are not measured zero.",
            "ArchSig v1 packet is a computation artifact, not a Lean proof object."
        ]
    })
}

pub fn build_typed_analysis_summary_v1(
    normalized: &NormalizedArchMapV1,
    typed_results: &TypedEvaluatorResultsV1,
    architecture_distance: &Value,
) -> serde_json::Value {
    let replacement_blocked_count = typed_results.replacement_summary.blocked_count;
    let verdict = if typed_results.summary.measured_violation_count > 0 {
        "SELECTED_VIOLATION_MEASURED_UNDER_EVIDENCE_CONTRACT"
    } else if typed_results.summary.measured_pass_count > 0
        && typed_results.summary.blocked_count == 0
        && typed_results.summary.unknown_count == 0
        && typed_results.summary.unmeasured_count == 0
        && replacement_blocked_count == 0
    {
        "ACCEPTABLE_UNDER_EVIDENCE_CONTRACT"
    } else {
        "BOUNDED_MEASUREMENT_INCOMPLETE"
    };
    json!({
        "schema": "archsig-analysis-summary/v1",
        "summaryKind": "typed-evaluator-summary",
        "verdict": verdict,
        "conclusion": typed_conclusion(typed_results, architecture_distance),
        "pipelineId": ANALYSIS_PIPELINE_ID,
        "measurementBasis": {
            "normalizedArchMap": typed_results.normalized_archmap_ref,
            "lawPolicy": typed_results.law_policy_ref,
            "typedEvaluatorResults": "typed-evaluator-results.json",
            "replacementRegistry": typed_results.replacement_registry_ref,
            "architectureDistance": "architecture-distance.json",
            "normalizedAtomCount": normalized.summary.normalized_atom_count,
            "generatedMoleculeCandidateCount": normalized.summary.generated_molecule_candidate_count
        },
        "measurementStatusSummary": typed_results.summary,
        "replacementRegistryResolution": typed_results.replacement_registry_resolution,
        "replacementStatusSummary": typed_results.replacement_summary,
        "typedEvaluatorDiagnosis": typed_evaluator_diagnosis(typed_results),
        "architectureDistance": architecture_distance["summary"],
        "distanceDiagnosis": architecture_distance["distanceDiagnosis"],
        "dominantFindings": typed_dominant_findings(typed_results),
        "actionQueue": typed_action_queue(typed_results),
        "positiveBoundedConclusions": typed_results.positive_bounded_conclusions,
        "metadata": {
            "boundary": "ArchSig v1 summary reads typed evaluator results and architecture distance as separate artifacts",
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
            "replacementEvaluatorResults": typed_results.replacement_evaluator_results,
            "replacementRegistryResolution": typed_results.replacement_registry_resolution,
            "typedEvaluatorDiagnosis": summary["typedEvaluatorDiagnosis"],
            "architectureDistance": summary["architectureDistance"],
            "distanceDiagnosis": summary["distanceDiagnosis"],
            "actionQueue": summary["actionQueue"]
        },
        "reportPane": {
            "conclusion": summary["conclusion"],
            "overview": {
                "summaryVerdict": summary["verdict"],
                "measurementStatusSummary": summary["measurementStatusSummary"]
            },
            "architectureDistance": summary["architectureDistance"],
            "replacementRegistryResolution": summary["replacementRegistryResolution"],
            "typedEvaluatorDiagnosis": summary["typedEvaluatorDiagnosis"],
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

pub fn build_typed_detail_index_v1(
    typed_results: &TypedEvaluatorResultsV1,
    packet: &serde_json::Value,
) -> serde_json::Value {
    let ref_dictionary = typed_results
        .results
        .iter()
        .chain(typed_results.replacement_evaluator_results.iter())
        .flat_map(|result| result.detail_refs.iter().cloned())
        .chain(derived_packet_refs(packet))
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect::<Vec<_>>();
    let mut entries = typed_results
        .results
        .iter()
        .chain(typed_results.replacement_evaluator_results.iter())
        .map(|result| {
            let result_ref = if let Some(replacement_id) = result.replacement_id.as_deref() {
                format!("replacementEvaluatorResults:{replacement_id}")
            } else {
                format!("typedEvaluatorResults:{}", result.law)
            };
            json!({
                "resultRef": result_ref,
                "status": result.status,
                "supportAtomRefs": result.support_atom_refs,
                "supportMoleculeRefs": result.support_molecule_refs,
                "basisRefs": result.basis_refs,
                "detailRefs": result.detail_refs,
                "replacementId": result.replacement_id,
                "replacementForV0Field": result.replacement_for_v0_field,
                "typedOutputPacketRefs": result.typed_output_packet_refs
            })
        })
        .collect::<Vec<_>>();
    entries.extend(derived_detail_index_entries(packet));
    json!({
        "schemaVersion": "archsig-analysis-detail-index-v1",
        "indexKind": "typed-evaluator-support-index",
        "sections": [
            detail_index_section_v1("typedEvaluatorResults", "/typedEvaluatorResults", packet_array_len(packet, "typedEvaluatorResults")),
            detail_index_section_v1("generatedLawInputs", "/generatedLawInputs", packet_array_len(packet, "generatedLawInputs")),
            detail_index_section_v1("signatureAxes", "/signatureAxes", packet_array_len(packet, "signatureAxes")),
            detail_index_section_v1("generatedObstructions", "/generatedObstructions", packet_array_len(packet, "generatedObstructions")),
            detail_index_section_v1("generatedRepairTargets", "/generatedRepairTargets", packet_array_len(packet, "generatedRepairTargets")),
            detail_index_section_v1("replacementEvaluatorResults", "/replacementEvaluatorResults", packet_array_len(packet, "replacementEvaluatorResults"))
        ],
        "refDictionary": ref_dictionary,
        "entries": entries,
        "nonConclusions": [
            "detail index records typed evaluator support refs only",
            "derived packet refs point to v1 generated surfaces, not removed v0 input fields",
            "detail refs are evidence navigation aids, not proof objects"
        ]
    })
}

pub fn build_typed_llm_interpretation_packet_v1(
    typed_results: &TypedEvaluatorResultsV1,
    architecture_distance: &Value,
) -> serde_json::Value {
    json!({
        "schema": "llm-interpretation-packet/v1",
        "interpretationKind": "typed-evaluator-bounded-reading",
        "primaryConclusion": typed_conclusion(typed_results, architecture_distance),
        "typedEvaluatorDiagnosis": typed_evaluator_diagnosis(typed_results),
        "architectureDistance": architecture_distance["summary"],
        "distanceDiagnosisSummary": architecture_distance["distanceDiagnosis"],
        "typedEvaluatorSummary": typed_results.summary,
        "replacementRegistryResolution": typed_results.replacement_registry_resolution,
        "positiveBoundedConclusions": typed_results.positive_bounded_conclusions,
        "nonConclusions": [
            "LLM interpretation packet summarizes typed evaluator results and does not add new findings.",
            "Blocked, unknown, and unmeasured are preserved as non-measured statuses."
        ]
    })
}

pub fn build_architecture_distance_v1(
    normalized: &NormalizedArchMapV1,
    law_policy: &LawPolicyDocumentV1,
    typed_results: &TypedEvaluatorResultsV1,
) -> Result<Value, String> {
    let profile_ref = law_policy
        .distance_profile_ref
        .as_deref()
        .unwrap_or("distance-profile:architecture-default@1");
    if !is_known_v1_distance_profile(profile_ref) {
        return Err(format!(
            "unknown architecture distance profile ref: {profile_ref}"
        ));
    }
    let profile = architecture_distance_profile_v1(profile_ref).ok_or_else(|| {
        format!("architecture distance profile ref is known but unresolved: {profile_ref}")
    })?;
    let atom_distance_readings = architecture_atom_distance_readings(normalized, profile);
    let configuration_distance_readings =
        architecture_configuration_distance_readings(normalized, profile);
    let signature_distance_readings =
        architecture_signature_distance_readings(typed_results, profile);
    let operation_distance_readings =
        architecture_operation_distance_readings(typed_results, profile);
    let atom_subtotal = measured_sum(&atom_distance_readings, "measuredValue");
    let configuration_subtotal = measured_sum(&configuration_distance_readings, "measuredValue");
    let signature_subtotal = measured_sum(&signature_distance_readings, "measuredValue");
    let operation_subtotal = measured_sum(&operation_distance_readings, "measuredValue");
    let measured_total =
        atom_subtotal + configuration_subtotal + signature_subtotal + operation_subtotal;
    let blocked_or_unmeasured_count = count_non_measured(&atom_distance_readings)
        + count_non_measured(&configuration_distance_readings)
        + count_non_measured(&signature_distance_readings)
        + count_non_measured(&operation_distance_readings);
    let status = if blocked_or_unmeasured_count > 0 {
        "partial"
    } else {
        "measured"
    };
    let distance_summary = json!({
        "status": status,
        "profileRef": profile_ref,
        "measuredTotal": measured_total,
        "unit": "architecture-distance-point",
        "breakdown": {
            "atomGeometry": atom_subtotal,
            "configuration": configuration_subtotal,
            "signature": signature_subtotal,
            "operation": operation_subtotal
        },
        "blockedOrUnmeasuredCount": blocked_or_unmeasured_count,
        "readingCounts": {
            "atomDistanceReadings": atom_distance_readings.len(),
            "configurationDistanceReadings": configuration_distance_readings.len(),
            "signatureDistanceReadings": signature_distance_readings.len(),
            "operationDistanceReadings": operation_distance_readings.len()
        }
    });
    let top_moved_axes = signature_distance_readings
        .iter()
        .filter(|reading| {
            reading["status"] == "measured" && reading["measuredValue"].as_i64().unwrap_or(0) > 0
        })
        .cloned()
        .collect::<Vec<_>>();
    Ok(json!({
        "schema": ARCHITECTURE_DISTANCE_V1_SCHEMA,
        "distanceKind": "architectureDistance",
        "profileRef": profile.profile_ref,
        "profileSource": if law_policy.distance_profile_ref.is_some() {
            "law-policy-selector"
        } else {
            "registry-default"
        },
        "profile": {
            "profileRef": profile.profile_ref,
            "atomWeights": {
                "atomKind": profile.atom_kind_weight,
                "axis": profile.axis_weight,
                "predicateConstructor": profile.predicate_constructor_weight,
                "predicateBindings": profile.predicate_binding_weight
            },
            "configurationAtomWeight": profile.configuration_atom_weight,
            "signatureViolationWeight": profile.signature_violation_weight,
            "operationCosts": {
                "solid.dependency-inversion": profile.dependency_inversion_operation_cost,
                "domain.no-direct-infra-dependency": profile.infrastructure_dependency_operation_cost,
                "default": profile.default_operation_cost
            }
        },
        "sourceRefs": {
            "normalizedArchMap": "normalized-archmap.json",
            "typedEvaluatorResults": "typed-evaluator-results.json"
        },
        "summary": distance_summary,
        "distanceDiagnosis": {
            "schema": "archsig-distance-diagnosis/v1",
            "basis": "architectureDistance",
            "verdict": if measured_total > 0 {
                "ARCHITECTURE_DISTANCE_MEASURED"
            } else if blocked_or_unmeasured_count > 0 {
                "ARCHITECTURE_DISTANCE_PARTIALLY_BLOCKED"
            } else {
                "ARCHITECTURE_DISTANCE_ZERO"
            },
            "distanceValue": {
                "status": status,
                "measuredTotal": measured_total,
                "unit": "architecture-distance-point",
                "blockedOrUnmeasuredCount": blocked_or_unmeasured_count
            },
            "topMovedAxes": top_moved_axes,
            "blockedResults": blocked_distance_results(
                &atom_distance_readings,
                &configuration_distance_readings,
                &signature_distance_readings,
                &operation_distance_readings
            ),
            "detailRefs": architecture_distance_detail_refs(
                &atom_distance_readings,
                &configuration_distance_readings,
                &signature_distance_readings,
                &operation_distance_readings
            )
        },
        "atomDistanceReadings": atom_distance_readings,
        "configurationDistanceReadings": configuration_distance_readings,
        "signatureDistanceReadings": signature_distance_readings,
        "operationDistanceReadings": operation_distance_readings,
        "metadata": {
            "theorySourceRef": "docs/aat/mathematical_theory/part_4_distance_measure_geometry.md",
            "publicNamingBoundary": "public summary surfaces use architecture distance naming; AAT mathematics section names remain raw artifact metadata"
        },
        "nonConclusions": [
            "Architecture distance is computed over supplied ArchMap v1 atoms, generated molecule candidates, selected law evaluator results, and the selected distance profile.",
            "Unmeasured or blocked distance is not measured zero.",
            "Architecture distance is an ArchSig diagnostic artifact, not a Lean proof object."
        ]
    }))
}

pub fn build_typed_analysis_validation_v1(
    packet: &serde_json::Value,
    typed_results: &TypedEvaluatorResultsV1,
) -> serde_json::Value {
    let packet_schema_pass = packet["schema"] == "archsig-analysis-packet/v1";
    let typed_count_pass = typed_results.summary.result_count == typed_results.results.len();
    let architecture_distance_pass =
        packet["architectureDistance"]["schema"] == ARCHITECTURE_DISTANCE_V1_SCHEMA;
    let distance_diagnosis_pass = packet["distanceDiagnosis"]["basis"] == "architectureDistance";
    let profile_ref_pass =
        architecture_distance_profile_refs_match(&packet["architectureDistance"]);
    let breakdown_sum_pass = architecture_distance_breakdown_sums(&packet["architectureDistance"]);
    let reading_counts_pass =
        architecture_distance_reading_counts_match(&packet["architectureDistance"]);
    let replacement_registry_present_pass = packet["replacementRegistry"]
        .as_array()
        .is_some_and(|items| !items.is_empty());
    let replacement_results_match_pass = packet["replacementEvaluatorResults"]
        .as_array()
        .is_some_and(|items| {
            items.len()
                == packet["replacementRegistryResolution"]["manifestCount"]
                    .as_u64()
                    .unwrap_or(0) as usize
        });
    let replacement_output_refs_pass =
        packet["replacementRegistry"]
            .as_array()
            .is_some_and(|items| {
                items.iter().all(|item| {
                    item["replacementId"].as_str().is_some()
                        && item["replacedV0Field"].as_str().is_some()
                        && item["typedOutputPacketRefs"]
                            .as_array()
                            .is_some_and(|refs| {
                                !refs.is_empty()
                                    && refs.iter().all(|reference| {
                                        reference.as_str().is_some_and(|pointer| {
                                            packet.pointer(pointer).is_some()
                                        })
                                    })
                            })
                        && item["positiveFixtures"]
                            .as_array()
                            .is_some_and(|fixtures| !fixtures.is_empty())
                        && item["negativeFixtures"]
                            .as_array()
                            .is_some_and(|fixtures| !fixtures.is_empty())
                })
            });
    let generated_law_inputs_pass = packet["generatedLawInputs"]
        .as_array()
        .is_some_and(|items| {
            items.len() == typed_results.results.len()
                && items.iter().enumerate().all(|(index, item)| {
                    let Some(result) = typed_results.results.get(index) else {
                        return false;
                    };
                    item["typedEvaluatorResultRef"]
                        .as_str()
                        .is_some_and(|reference| {
                            reference == format!("/typedEvaluatorResults/{index}")
                                && packet.pointer(reference).is_some()
                        })
                        && item["law"] == result.law
                        && item["evaluator"] == result.evaluator
                        && item["status"] == result.status
                        && item["supportAtomRefs"] == json!(result.support_atom_refs)
                        && item["supportMoleculeRefs"] == json!(result.support_molecule_refs)
                        && item["registryBasisRefs"]
                            .as_array()
                            .is_some_and(|refs| !refs.is_empty())
                        && item["supportAtomRefs"].is_array()
                        && item["supportMoleculeRefs"].is_array()
                })
        });
    let signature_axes_pass = packet["signatureAxes"].as_array().is_some_and(|items| {
        items.len() == typed_results.results.len()
            && items.iter().enumerate().all(|(index, item)| {
                let Some(result) = typed_results.results.get(index) else {
                    return false;
                };
                item["typedEvaluatorResultRef"]
                    .as_str()
                    .is_some_and(|reference| {
                        reference == format!("/typedEvaluatorResults/{index}")
                            && packet.pointer(reference).is_some()
                    })
                    && item["lawRef"] == result.law
                    && item["evaluatorRef"] == result.evaluator
                    && item["status"] == result.status
                    && item["supportAtomRefs"] == json!(result.support_atom_refs)
                    && item["supportMoleculeRefs"] == json!(result.support_molecule_refs)
                    && item["generatedLawInputRef"]
                        .as_str()
                        .is_some_and(|reference| {
                            reference == format!("/generatedLawInputs/{index}")
                                && packet.pointer(reference).is_some()
                        })
                    && item["signatureAxisId"].as_str().is_some()
                    && item["signatureDistanceReadingRefs"]
                        .as_array()
                        .is_some_and(|refs| {
                            refs.iter().all(|reference| {
                                reference
                                    .as_str()
                                    .is_some_and(|pointer| packet.pointer(pointer).is_some())
                            })
                        })
            })
    });
    let generated_obstructions_pass =
        packet["generatedObstructions"]
            .as_array()
            .is_some_and(|items| {
                items.iter().all(|item| {
                    let Some(result) =
                        item["typedEvaluatorResultRef"]
                            .as_str()
                            .and_then(|reference| {
                                typed_result_from_packet_ref(typed_results, reference)
                            })
                    else {
                        return false;
                    };
                    result.status != "measuredPass"
                        && item["law"] == result.law
                        && item["evaluator"] == result.evaluator
                        && item["supportAtomRefs"] == json!(result.support_atom_refs)
                        && item["supportMoleculeRefs"] == json!(result.support_molecule_refs)
                        && item["typedEvaluatorResultRef"]
                            .as_str()
                            .is_some_and(|reference| packet.pointer(reference).is_some())
                        && item["generatedLawInputRef"]
                            .as_str()
                            .is_some_and(|reference| packet.pointer(reference).is_some())
                        && item["signatureAxisRef"]
                            .as_str()
                            .is_some_and(|reference| packet.pointer(reference).is_some())
                        && item["obstructionKind"].as_str().is_some()
                })
            });
    let generated_repair_targets_pass =
        packet["generatedRepairTargets"]
            .as_array()
            .is_some_and(|items| {
                items.iter().all(|item| {
                    let Some(obstruction) = item["generatedObstructionRef"]
                        .as_str()
                        .and_then(|reference| packet.pointer(reference))
                    else {
                        return false;
                    };
                    item["targetKind"] == repair_target_kind(obstruction)
                        && item["supportAtomRefs"] == obstruction["supportAtomRefs"]
                        && item["supportMoleculeRefs"] == obstruction["supportMoleculeRefs"]
                        && item["registryBasisRefs"] == obstruction["registryBasisRefs"]
                        && item["basisRefs"] == obstruction["basisRefs"]
                        && item["signatureAxisRef"] == obstruction["signatureAxisRef"]
                        && item["localStatus"] == obstruction["localStatus"]
                        && item["generatedObstructionRef"]
                            .as_str()
                            .is_some_and(|reference| packet.pointer(reference).is_some())
                        && item["typedEvaluatorResultRef"]
                            .as_str()
                            .is_some_and(|reference| packet.pointer(reference).is_some())
                        && item["targetKind"].as_str().is_some()
                })
            });
    let generated_packet_refs_pass =
        packet["generatedPacketRefs"]
            .as_object()
            .is_some_and(|refs| {
                [
                    "generatedLawInputs",
                    "signatureAxes",
                    "generatedObstructions",
                    "generatedRepairTargets",
                    "typedEvaluatorResults",
                    "architectureDistanceSignatureReadings",
                ]
                .iter()
                .all(|field| {
                    refs.get(*field)
                        .and_then(Value::as_str)
                        .is_some_and(|pointer| packet.pointer(pointer).is_some())
                })
            });
    let removed_v0_input_fields_absent_pass = [
        "semanticObservations",
        "projectionInfo",
        "operationSquareEvidence",
        "concernHints",
        "observationGaps",
    ]
    .iter()
    .all(|field| packet.get(*field).is_none());
    let checks_pass = [
        packet_schema_pass,
        typed_count_pass,
        architecture_distance_pass,
        distance_diagnosis_pass,
        profile_ref_pass,
        breakdown_sum_pass,
        reading_counts_pass,
        replacement_registry_present_pass,
        replacement_results_match_pass,
        replacement_output_refs_pass,
        generated_law_inputs_pass,
        signature_axes_pass,
        generated_obstructions_pass,
        generated_repair_targets_pass,
        generated_packet_refs_pass,
        removed_v0_input_fields_absent_pass,
    ];
    let result = if checks_pass.iter().copied().all(|passed| passed) {
        "pass"
    } else {
        "fail"
    };
    let failed_check_count = checks_pass.iter().copied().filter(|passed| !passed).count();
    json!({
        "schemaVersion": "archsig-analysis-validation-report-v1",
        "summary": {
            "result": result,
            "failedCheckCount": failed_check_count,
            "warningCheckCount": 0,
            "proxyRegressionCheckCount": 0
        },
        "checks": [
            {
                "checkId": "archsig.v1.analysisPacketSchema",
                "result": if packet_schema_pass { "pass" } else { "fail" },
                "message": "analysis packet schema is v1"
            },
            {
                "checkId": "archsig.v1.typedEvaluatorResultCount",
                "result": if typed_count_pass { "pass" } else { "fail" },
                "message": "typed evaluator result count matches summary"
            },
            {
                "checkId": "archsig.v1.architectureDistancePresent",
                "result": if architecture_distance_pass { "pass" } else { "fail" },
                "message": "architecture distance artifact is present in the v1 analysis packet"
            },
            {
                "checkId": "archsig.v1.distanceDiagnosisUsesArchitectureDistance",
                "result": if distance_diagnosis_pass { "pass" } else { "fail" },
                "message": "distanceDiagnosis is backed by architecture distance, not typed evaluator counts"
            },
            {
                "checkId": "archsig.v1.architectureDistanceProfileRefsMatch",
                "result": if profile_ref_pass { "pass" } else { "fail" },
                "message": "architecture distance profile refs agree across top-level, profile body, and summary"
            },
            {
                "checkId": "archsig.v1.architectureDistanceBreakdownSums",
                "result": if breakdown_sum_pass { "pass" } else { "fail" },
                "message": "architecture distance measuredTotal equals the sum of measured distance breakdown fields"
            },
            {
                "checkId": "archsig.v1.architectureDistanceReadingCounts",
                "result": if reading_counts_pass { "pass" } else { "fail" },
                "message": "architecture distance readingCounts match the emitted reading arrays"
            },
            {
                "checkId": "archsig.v1.replacementRegistryPresent",
                "result": if replacement_registry_present_pass { "pass" } else { "fail" },
                "message": "removed v0 field replacement registry manifest is present in the v1 packet"
            },
            {
                "checkId": "archsig.v1.replacementRegistryResultsMatch",
                "result": if replacement_results_match_pass { "pass" } else { "fail" },
                "message": "replacement evaluator result count matches replacement registry resolution manifest count"
            },
            {
                "checkId": "archsig.v1.replacementRegistryOutputRefs",
                "result": if replacement_output_refs_pass { "pass" } else { "fail" },
                "message": "each replacement manifest declares typed output refs and positive / negative fixture coverage"
            },
            {
                "checkId": "archsig.v1.generatedLawInputsTraceTypedResults",
                "result": if generated_law_inputs_pass { "pass" } else { "fail" },
                "message": "generatedLawInputs are derived from typed evaluator results and registry basis"
            },
            {
                "checkId": "archsig.v1.signatureAxesTraceTypedResults",
                "result": if signature_axes_pass { "pass" } else { "fail" },
                "message": "signatureAxes resolve to generated law inputs, typed evaluator results, and signature distance readings"
            },
            {
                "checkId": "archsig.v1.generatedObstructionsTraceTypedResults",
                "result": if generated_obstructions_pass { "pass" } else { "fail" },
                "message": "generatedObstructions resolve to typed evaluator result and signature axis refs"
            },
            {
                "checkId": "archsig.v1.generatedRepairTargetsTraceObstructions",
                "result": if generated_repair_targets_pass { "pass" } else { "fail" },
                "message": "generatedRepairTargets resolve to generated obstruction refs"
            },
            {
                "checkId": "archsig.v1.generatedPacketRefsResolve",
                "result": if generated_packet_refs_pass { "pass" } else { "fail" },
                "message": "top-level generated packet refs resolve to v1 packet JSON pointers"
            },
            {
                "checkId": "archsig.v1.removedV0InputFieldsAbsent",
                "result": if removed_v0_input_fields_absent_pass { "pass" } else { "fail" },
                "message": "v1 packet does not restore removed v0 input fields as root inputs"
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
    support_atoms: &[&NormalizedAtomV1],
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
    } else if typed_violation_detected(entry, support_atoms) {
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
        replacement_id: None,
        replacement_for_v0_field: None,
        typed_output_packet_refs: Vec::new(),
        summary: format!("{} evaluated as {status}", entry.law),
        blocker_reason,
    }
}

fn replacement_results_by_id(typed_results: &TypedEvaluatorResultsV1) -> Value {
    let mut object = serde_json::Map::new();
    for result in &typed_results.replacement_evaluator_results {
        if let Some(replacement_id) = result.replacement_id.as_deref() {
            object.insert(replacement_id.to_string(), json!(result));
        }
    }
    Value::Object(object)
}

fn generated_law_inputs_v1(typed_results: &TypedEvaluatorResultsV1) -> Vec<Value> {
    typed_results
        .results
        .iter()
        .enumerate()
        .map(|(index, result)| {
            let signature_axis_id = signature_axis_id(&result.law);
            json!({
                "lawInputId": generated_law_input_id(&result.law),
                "law": result.law,
                "evaluator": result.evaluator,
                "status": result.status,
                "typedEvaluatorResultRef": typed_evaluator_result_ref(index),
                "registryBasisRefs": registry_basis_refs(result),
                "basisRefs": result.basis_refs,
                "applicableLawAxes": [signature_axis_id],
                "localStatuses": [local_status(result)],
                "supportAtomRefs": result.support_atom_refs,
                "supportMoleculeRefs": result.support_molecule_refs,
                "detailRefs": result.detail_refs,
                "blockerReason": result.blocker_reason,
                "nonConclusions": [
                    "generatedLawInputs/v1 is a derived packet surface over typed evaluator results",
                    "LawPolicy v1 supplies evaluator selection only; it does not supply witness, axis, or obstruction DSL"
                ]
            })
        })
        .collect()
}

fn signature_axes_v1(
    typed_results: &TypedEvaluatorResultsV1,
    architecture_distance: &Value,
) -> Vec<Value> {
    typed_results
        .results
        .iter()
        .enumerate()
        .map(|(index, result)| {
            let value = if result.status == "measuredViolation" {
                1
            } else {
                0
            };
            json!({
                "signatureAxisId": signature_axis_id(&result.law),
                "axisRef": format!("law-axis:{}", stable_ref(&result.law)),
                "lawRef": result.law,
                "evaluatorRef": result.evaluator,
                "value": value,
                "measurementStatus": measurement_status(result),
                "status": result.status,
                "typedEvaluatorResultRef": typed_evaluator_result_ref(index),
                "generatedLawInputRef": format!("/generatedLawInputs/{index}"),
                "signatureDistanceReadingRefs": signature_distance_reading_refs(architecture_distance, index),
                "registryBasisRefs": registry_basis_refs(result),
                "basisRefs": result.basis_refs,
                "sourceRefs": result.support_atom_refs,
                "supportAtomRefs": result.support_atom_refs,
                "supportMoleculeRefs": result.support_molecule_refs,
                "detailRefs": result.detail_refs,
                "blockerReason": result.blocker_reason,
                "nonConclusions": [
                    "signatureAxes/v1 is derived from typed evaluator status and architecture distance readings",
                    "zero value means no selected measured violation for this axis; blocked status is not measured zero"
                ]
            })
        })
        .collect()
}

fn generated_obstructions_v1(typed_results: &TypedEvaluatorResultsV1) -> Vec<Value> {
    typed_results
        .results
        .iter()
        .enumerate()
        .filter(|(_, result)| result.status != "measuredPass")
        .map(|(index, result)| {
            json!({
                "generatedObstructionId": generated_obstruction_id(&result.law),
                "obstructionKind": if result.status == "measuredViolation" {
                    "measuredLawViolation"
                } else {
                    "blockedObstructionCandidate"
                },
                "law": result.law,
                "evaluator": result.evaluator,
                "localStatus": local_status(result),
                "blockerStatus": if result.status == "measuredViolation" {
                    "locallyMeasured"
                } else {
                    "locallyBlocked"
                },
                "typedEvaluatorResultRef": typed_evaluator_result_ref(index),
                "generatedLawInputRef": format!("/generatedLawInputs/{index}"),
                "signatureAxisRef": format!("/signatureAxes/{index}"),
                "registryBasisRefs": registry_basis_refs(result),
                "basisRefs": result.basis_refs,
                "supportAtomRefs": result.support_atom_refs,
                "supportMoleculeRefs": result.support_molecule_refs,
                "detailRefs": result.detail_refs,
                "blockerReason": result.blocker_reason,
                "nonConclusions": [
                    "generatedObstructions/v1 is derived from typed evaluator status only",
                    "blocked obstruction candidates are missing-evidence diagnostics, not measured violations"
                ]
            })
        })
        .collect()
}

fn generated_repair_targets_v1(generated_obstructions: &[Value]) -> Vec<Value> {
    generated_obstructions
        .iter()
        .enumerate()
        .map(|(index, obstruction)| {
            let target_kind = if obstruction["obstructionKind"] == "measuredLawViolation" {
                "reviewMeasuredViolation"
            } else {
                "collectMissingEvidence"
            };
            json!({
                "generatedRepairTargetId": format!(
                    "generated-repair-target:{}",
                    stable_ref(
                        obstruction["law"]
                            .as_str()
                            .unwrap_or("unknown-law")
                    )
                ),
                "targetKind": target_kind,
                "law": obstruction["law"],
                "evaluator": obstruction["evaluator"],
                "generatedObstructionRef": format!("/generatedObstructions/{index}"),
                "typedEvaluatorResultRef": obstruction["typedEvaluatorResultRef"],
                "signatureAxisRef": obstruction["signatureAxisRef"],
                "localStatus": obstruction["localStatus"],
                "registryBasisRefs": obstruction["registryBasisRefs"],
                "basisRefs": obstruction["basisRefs"],
                "supportAtomRefs": obstruction["supportAtomRefs"],
                "supportMoleculeRefs": obstruction["supportMoleculeRefs"],
                "detailRefs": obstruction["detailRefs"],
                "blockerReason": obstruction["blockerReason"],
                "nonConclusions": [
                    "generatedRepairTargets/v1 names bounded review targets; it does not prove a repair operation",
                    "repair target generation does not read removed v0 repair candidate inputs"
                ]
            })
        })
        .collect()
}

fn generated_law_input_id(law: &str) -> String {
    format!("generated-law-input:{}", stable_ref(law))
}

fn signature_axis_id(law: &str) -> String {
    format!("sig-axis:{}", stable_ref(law))
}

fn generated_obstruction_id(law: &str) -> String {
    format!("generated-obstruction:{}", stable_ref(law))
}

fn typed_evaluator_result_ref(index: usize) -> String {
    format!("/typedEvaluatorResults/{index}")
}

fn typed_result_from_packet_ref<'a>(
    typed_results: &'a TypedEvaluatorResultsV1,
    reference: &str,
) -> Option<&'a TypedEvaluatorResultV1> {
    reference
        .strip_prefix("/typedEvaluatorResults/")
        .and_then(|index| index.parse::<usize>().ok())
        .and_then(|index| typed_results.results.get(index))
}

fn repair_target_kind(obstruction: &Value) -> &'static str {
    if obstruction["obstructionKind"] == "measuredLawViolation" {
        "reviewMeasuredViolation"
    } else {
        "collectMissingEvidence"
    }
}

fn registry_basis_refs(result: &TypedEvaluatorResultV1) -> Vec<String> {
    vec![
        format!("law-evaluator-registry@1/evaluators/{}", result.evaluator),
        format!("law-evaluator-registry@1/laws/{}", result.law),
        "law-evaluator-registry@1/distance-contribution".to_string(),
    ]
}

fn local_status(result: &TypedEvaluatorResultV1) -> &'static str {
    match result.status.as_str() {
        "measuredViolation" => "localViolated",
        "measuredPass" => "localSatisfied",
        "blocked" | "unknown" | "unmeasured" => "locallyBlocked",
        _ => "locallyUnknown",
    }
}

fn measurement_status(result: &TypedEvaluatorResultV1) -> &'static str {
    match result.status.as_str() {
        "measuredPass" | "measuredViolation" => "measured",
        "blocked" | "unknown" | "unmeasured" => "blocked",
        _ => "unknown",
    }
}

fn signature_distance_reading_refs(architecture_distance: &Value, index: usize) -> Vec<String> {
    architecture_distance["signatureDistanceReadings"]
        .as_array()
        .and_then(|readings| readings.get(index))
        .map(|_| {
            vec![format!(
                "/architectureDistance/signatureDistanceReadings/{index}"
            )]
        })
        .unwrap_or_default()
}

fn detail_index_section_v1(name: &str, pointer: &str, count: usize) -> Value {
    json!({
        "name": name,
        "packetRef": format!("packet:{pointer}"),
        "count": count
    })
}

fn packet_array_len(packet: &Value, field: &str) -> usize {
    packet[field].as_array().map(Vec::len).unwrap_or_default()
}

fn derived_packet_refs(packet: &Value) -> Vec<String> {
    [
        "generatedLawInputs",
        "signatureAxes",
        "generatedObstructions",
        "generatedRepairTargets",
    ]
    .iter()
    .flat_map(|field| {
        packet[field].as_array().into_iter().flat_map(move |items| {
            (0..items.len()).map(move |index| format!("packet:/{field}/{index}"))
        })
    })
    .collect()
}

fn derived_detail_index_entries(packet: &Value) -> Vec<Value> {
    let mut entries = Vec::new();
    entries.extend(derived_detail_entries_for_field(
        packet,
        "generatedLawInputs",
        "lawInputId",
        "generatedLawInputs",
    ));
    entries.extend(derived_detail_entries_for_field(
        packet,
        "signatureAxes",
        "signatureAxisId",
        "signatureAxes",
    ));
    entries.extend(derived_detail_entries_for_field(
        packet,
        "generatedObstructions",
        "generatedObstructionId",
        "generatedObstructions",
    ));
    entries.extend(derived_detail_entries_for_field(
        packet,
        "generatedRepairTargets",
        "generatedRepairTargetId",
        "generatedRepairTargets",
    ));
    entries
}

fn derived_detail_entries_for_field(
    packet: &Value,
    field: &str,
    id_field: &str,
    namespace: &str,
) -> Vec<Value> {
    packet[field]
        .as_array()
        .into_iter()
        .flat_map(|items| {
            items.iter().enumerate().map(move |(index, item)| {
                let fallback_id = format!("{namespace}:{index}");
                let id = item[id_field].as_str().unwrap_or(&fallback_id);
                json!({
                    "resultRef": format!("{namespace}:{id}"),
                    "packetRef": format!("packet:/{field}/{index}"),
                    "typedEvaluatorResultRef": item["typedEvaluatorResultRef"],
                    "generatedLawInputRef": item["generatedLawInputRef"],
                    "signatureAxisRef": item["signatureAxisRef"],
                    "generatedObstructionRef": item["generatedObstructionRef"],
                    "status": item["status"],
                    "localStatus": item["localStatus"],
                    "targetKind": item["targetKind"],
                    "supportAtomRefs": item["supportAtomRefs"],
                    "supportMoleculeRefs": item["supportMoleculeRefs"],
                    "basisRefs": item["basisRefs"],
                    "registryBasisRefs": item["registryBasisRefs"],
                    "detailRefs": item["detailRefs"]
                })
            })
        })
        .collect()
}

fn evaluate_replacement_registry_v1(
    normalized: &NormalizedArchMapV1,
    registry: &LawEvaluatorRegistryV1,
    law_results: &[TypedEvaluatorResultV1],
) -> Vec<TypedEvaluatorResultV1> {
    registry
        .replacement_registry
        .iter()
        .map(|manifest| replacement_result(normalized, manifest, law_results))
        .collect()
}

fn replacement_result(
    normalized: &NormalizedArchMapV1,
    manifest: &ReplacementEvaluatorManifestV1,
    law_results: &[TypedEvaluatorResultV1],
) -> TypedEvaluatorResultV1 {
    match manifest.replacement_id.as_str() {
        "missing-evidence.reading@1" => missing_evidence_replacement_result(manifest, law_results),
        "concern.boundary@1" | "non-conclusion.boundary@1" => boundary_replacement_result(manifest),
        _ => support_based_replacement_result(normalized, manifest),
    }
}

fn support_based_replacement_result(
    normalized: &NormalizedArchMapV1,
    manifest: &ReplacementEvaluatorManifestV1,
) -> TypedEvaluatorResultV1 {
    let support_atom_refs = replacement_support_atom_refs(normalized, manifest);
    let support_molecule_refs =
        replacement_support_molecule_refs(normalized, manifest, &support_atom_refs);
    let blocker_reason = if support_atom_refs.is_empty() {
        Some(format!(
            "required replacement atom constructors are missing: {}",
            manifest.required_atom_constructors.join(", ")
        ))
    } else if support_molecule_refs.is_empty() {
        Some(manifest.missing_blocker_rule.clone())
    } else {
        None
    };
    let status = if blocker_reason.is_some() {
        "blocked"
    } else {
        "measuredPass"
    };
    typed_replacement_result(
        manifest,
        status,
        support_atom_refs,
        support_molecule_refs,
        format!(
            "{} resolved as {status} from normalized ArchMap support",
            manifest.replacement_id
        ),
        blocker_reason,
    )
}

fn missing_evidence_replacement_result(
    manifest: &ReplacementEvaluatorManifestV1,
    law_results: &[TypedEvaluatorResultV1],
) -> TypedEvaluatorResultV1 {
    let blocked_results = law_results
        .iter()
        .filter(|result| {
            result.status == "blocked"
                || result.status == "unknown"
                || result.status == "unmeasured"
        })
        .collect::<Vec<_>>();
    let detail_refs = blocked_results
        .iter()
        .flat_map(|result| result.detail_refs.iter().cloned())
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect::<Vec<_>>();
    let blocker_reason = (!blocked_results.is_empty()).then(|| {
        format!(
            "{} selected evaluator result(s) have missing support under registry requirements",
            blocked_results.len()
        )
    });
    let status = if blocker_reason.is_some() {
        "blocked"
    } else {
        "measuredPass"
    };
    typed_replacement_result(
        manifest,
        status,
        Vec::new(),
        Vec::new(),
        if status == "blocked" {
            "missing evidence was derived from blocked typed evaluator requirements".to_string()
        } else {
            "no selected evaluator missing-evidence reading was derived".to_string()
        },
        blocker_reason,
    )
    .with_detail_refs(detail_refs)
}

fn boundary_replacement_result(
    manifest: &ReplacementEvaluatorManifestV1,
) -> TypedEvaluatorResultV1 {
    typed_replacement_result(
        manifest,
        "unmeasured",
        Vec::new(),
        Vec::new(),
        format!(
            "{} is a boundary replacement; removed v0 prose is not diagnostic input",
            manifest.replacement_id
        ),
        Some(manifest.missing_blocker_rule.clone()),
    )
}

fn typed_replacement_result(
    manifest: &ReplacementEvaluatorManifestV1,
    status: &str,
    support_atom_refs: Vec<String>,
    support_molecule_refs: Vec<String>,
    summary: String,
    blocker_reason: Option<String>,
) -> TypedEvaluatorResultV1 {
    let detail_refs = support_atom_refs
        .iter()
        .chain(support_molecule_refs.iter())
        .cloned()
        .collect();
    TypedEvaluatorResultV1 {
        evaluator: manifest.evaluator_id.clone(),
        law: manifest.law_id.clone(),
        status: status.to_string(),
        support_atom_refs,
        support_molecule_refs,
        basis_refs: vec![format!(
            "replacement-registry:{}",
            manifest.replaced_v0_field
        )],
        detail_refs,
        replacement_id: Some(manifest.replacement_id.clone()),
        replacement_for_v0_field: Some(manifest.replaced_v0_field.clone()),
        typed_output_packet_refs: manifest.typed_output_packet_refs.clone(),
        summary,
        blocker_reason,
    }
}

trait WithDetailRefs {
    fn with_detail_refs(self, detail_refs: Vec<String>) -> Self;
}

impl WithDetailRefs for TypedEvaluatorResultV1 {
    fn with_detail_refs(mut self, detail_refs: Vec<String>) -> Self {
        self.detail_refs = detail_refs;
        self
    }
}

fn replacement_support_atom_refs(
    normalized: &NormalizedArchMapV1,
    manifest: &ReplacementEvaluatorManifestV1,
) -> Vec<String> {
    normalized
        .atoms
        .iter()
        .filter(|atom| {
            manifest
                .required_atom_constructors
                .iter()
                .any(|required| normalized_atom_matches_constructor(atom, required))
        })
        .map(|atom| atom.normalized_atom_id.clone())
        .collect()
}

fn replacement_support_molecule_refs(
    normalized: &NormalizedArchMapV1,
    manifest: &ReplacementEvaluatorManifestV1,
    support_atom_refs: &[String],
) -> Vec<String> {
    normalized
        .molecules
        .iter()
        .filter(|molecule| {
            molecule.generated_molecule_candidate_status == "generated"
                && molecule
                    .atom_ids
                    .iter()
                    .any(|atom_id| support_atom_refs.contains(atom_id))
                && replacement_molecule_condition_matches(normalized, molecule, manifest)
        })
        .map(|molecule| molecule.normalized_molecule_id.clone())
        .collect()
}

fn replacement_molecule_condition_matches(
    normalized: &NormalizedArchMapV1,
    molecule: &NormalizedMoleculeV1,
    manifest: &ReplacementEvaluatorManifestV1,
) -> bool {
    match manifest.replacement_id.as_str() {
        "semantic.interpretation@1" => molecule_has_constructor(normalized, molecule, "semantic"),
        "projection.reading@1" => molecule_has_any_constructor(
            normalized,
            molecule,
            &["component", "relation", "capability"],
        ),
        "operation-square.reading@1" => {
            molecule_has_constructor(normalized, molecule, "relation")
                && molecule_has_any_constructor(normalized, molecule, &["effect", "runtime"])
        }
        _ => true,
    }
}

fn molecule_has_constructor(
    normalized: &NormalizedArchMapV1,
    molecule: &NormalizedMoleculeV1,
    constructor: &str,
) -> bool {
    molecule_has_any_constructor(normalized, molecule, &[constructor])
}

fn molecule_has_any_constructor(
    normalized: &NormalizedArchMapV1,
    molecule: &NormalizedMoleculeV1,
    constructors: &[&str],
) -> bool {
    molecule.atom_ids.iter().any(|atom_id| {
        normalized
            .atoms
            .iter()
            .find(|atom| atom.normalized_atom_id == *atom_id)
            .is_some_and(|atom| {
                constructors
                    .iter()
                    .any(|constructor| normalized_atom_matches_constructor(atom, constructor))
            })
    })
}

fn normalized_atom_matches_constructor(atom: &NormalizedAtomV1, constructor: &str) -> bool {
    atom.predicate.constructor == constructor
        || atom.atom_kind == constructor
        || matches!(
            (constructor, atom.predicate.constructor.as_str()),
            ("dataState", "dataState")
                | ("authority", "boundaryAuthority")
                | ("contract", "contractSpecification")
                | ("semantic", "semanticInterpretation")
                | ("runtime", "runtimeInteraction")
        )
}

fn replacement_registry_resolution(
    manifests: &[ReplacementEvaluatorManifestV1],
    summary: &TypedEvaluatorResultsSummaryV1,
) -> ReplacementRegistryResolutionV1 {
    ReplacementRegistryResolutionV1 {
        schema: "archsig-replacement-registry-resolution/v1".to_string(),
        registry_ref: REPLACEMENT_REGISTRY_REF.to_string(),
        manifest_count: manifests.len(),
        resolved_replacement_count: summary.measured_pass_count + summary.measured_violation_count,
        blocked_replacement_count: summary.blocked_count,
        non_diagnostic_replacement_count: summary.unknown_count + summary.unmeasured_count,
        replaced_v0_fields: manifests
            .iter()
            .map(|manifest| manifest.replaced_v0_field.clone())
            .collect(),
        non_conclusions: vec![
            "Replacement registry resolution does not re-enable removed v0 ArchMap fields."
                .to_string(),
            "Concern and non-conclusion boundary replacements are intentionally unmeasured."
                .to_string(),
        ],
    }
}

fn architecture_distance_profile_refs_match(architecture_distance: &Value) -> bool {
    let top_level = architecture_distance["profileRef"].as_str();
    top_level.is_some()
        && top_level == architecture_distance["summary"]["profileRef"].as_str()
        && top_level == architecture_distance["profile"]["profileRef"].as_str()
}

fn architecture_distance_breakdown_sums(architecture_distance: &Value) -> bool {
    let Some(measured_total) = architecture_distance["summary"]["measuredTotal"].as_i64() else {
        return false;
    };
    let breakdown = &architecture_distance["summary"]["breakdown"];
    let subtotal = ["atomGeometry", "configuration", "signature", "operation"]
        .iter()
        .filter_map(|field| breakdown[*field].as_i64())
        .sum::<i64>();
    measured_total == subtotal
}

fn architecture_distance_reading_counts_match(architecture_distance: &Value) -> bool {
    let counts = &architecture_distance["summary"]["readingCounts"];
    [
        ("atomDistanceReadings", "atomDistanceReadings"),
        (
            "configurationDistanceReadings",
            "configurationDistanceReadings",
        ),
        ("signatureDistanceReadings", "signatureDistanceReadings"),
        ("operationDistanceReadings", "operationDistanceReadings"),
    ]
    .iter()
    .all(|(count_field, array_field)| {
        let Some(expected) = counts[*count_field].as_u64() else {
            return false;
        };
        architecture_distance[*array_field]
            .as_array()
            .is_some_and(|items| items.len() as u64 == expected)
    })
}

fn typed_violation_detected(
    entry: &crate::ExpandedLawPolicyEntryV1,
    support_atoms: &[&NormalizedAtomV1],
) -> bool {
    match entry.law.as_str() {
        "domain.no-direct-infra-dependency" => support_atoms
            .iter()
            .filter(|atom| atom.predicate.constructor == "dependsOn")
            .any(|atom| {
                let subject = binding_value(atom, "subject");
                let object = binding_value(atom, "object");
                subject.is_some_and(is_domain_ref) && object.is_some_and(is_infrastructure_ref)
            }),
        "solid.dependency-inversion" => support_atoms
            .iter()
            .filter(|atom| atom.predicate.constructor == "dependsOn")
            .any(|atom| {
                let object = binding_value(atom, "object");
                object.is_some_and(is_concrete_infrastructure_ref)
            }),
        _ => false,
    }
}

fn binding_value<'a>(atom: &'a NormalizedAtomV1, role: &str) -> Option<&'a str> {
    atom.predicate
        .bindings
        .iter()
        .find(|binding| binding.role == role)
        .map(|binding| binding.value.as_str())
}

fn is_domain_ref(value: &str) -> bool {
    value.contains("domain.") || value.contains("src.domain")
}

fn is_infrastructure_ref(value: &str) -> bool {
    value.contains("infra.") || value.contains("store.") || value.contains("InMemory")
}

fn is_concrete_infrastructure_ref(value: &str) -> bool {
    is_infrastructure_ref(value) && !value.contains("InventoryStore")
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

fn typed_evaluator_diagnosis(typed_results: &TypedEvaluatorResultsV1) -> serde_json::Value {
    let status_summary = &typed_results.summary;
    let measured_violation_count = status_summary.measured_violation_count;
    let blocked_or_unmeasured_count = status_summary.blocked_count
        + status_summary.unknown_count
        + status_summary.unmeasured_count
        + typed_results.replacement_summary.blocked_count;
    let violating_laws = typed_results
        .results
        .iter()
        .filter(|result| result.status == "measuredViolation")
        .map(|result| {
            json!({
                "law": result.law,
                "evaluator": result.evaluator,
                "status": result.status,
                "basisRefs": result.basis_refs,
                "detailRefs": result.detail_refs
            })
        })
        .collect::<Vec<_>>();
    let blocked_results = typed_results
        .results
        .iter()
        .chain(
            typed_results
                .replacement_evaluator_results
                .iter()
                .filter(|result| result.status == "blocked"),
        )
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
                "replacementId": result.replacement_id,
                "replacementForV0Field": result.replacement_for_v0_field,
                "blockerReason": result.blocker_reason
            })
        })
        .collect::<Vec<_>>();
    json!({
        "schema": "archsig-typed-evaluator-diagnosis/v1",
        "basis": "typedEvaluatorResults",
        "verdict": if measured_violation_count > 0 {
            "SELECTED_VIOLATION_MEASURED_UNDER_EVIDENCE_CONTRACT"
        } else if blocked_or_unmeasured_count > 0 {
            "BOUNDED_EVALUATION_PARTIALLY_BLOCKED"
        } else {
            "NO_SELECTED_OBSTRUCTION"
        },
        "violationCount": measured_violation_count,
        "blockedOrUnmeasuredCount": blocked_or_unmeasured_count,
        "replacementBlockedCount": typed_results.replacement_summary.blocked_count,
        "violatingLaws": violating_laws,
        "blockedResults": blocked_results,
        "detailRefs": typed_results
            .results
            .iter()
            .chain(typed_results.replacement_evaluator_results.iter())
            .flat_map(|result| result.detail_refs.iter().cloned())
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect::<Vec<_>>(),
        "metadata": {
            "publicNamingBoundary": "typed evaluator counts are not architecture distance"
        }
    })
}

fn typed_conclusion(
    typed_results: &TypedEvaluatorResultsV1,
    architecture_distance: &Value,
) -> Value {
    let violated_laws = laws_with_status(typed_results, "measuredViolation");
    let passed_laws = laws_with_status(typed_results, "measuredPass");
    let blocked_laws = typed_results
        .results
        .iter()
        .filter(|result| {
            result.status == "blocked"
                || result.status == "unknown"
                || result.status == "unmeasured"
        })
        .map(|result| result.law.clone())
        .collect::<Vec<_>>();
    let blocked_replacement_readings = typed_results
        .replacement_evaluator_results
        .iter()
        .filter(|result| result.status == "blocked")
        .filter_map(|result| result.replacement_id.clone())
        .collect::<Vec<_>>();
    let status = if !violated_laws.is_empty() {
        "violation_detected"
    } else if !blocked_laws.is_empty() || !blocked_replacement_readings.is_empty() {
        "incomplete"
    } else {
        "acceptable"
    };
    let plain_conclusion = match status {
        "violation_detected" => "違反あり",
        "incomplete" => "未測定あり",
        _ => "違反なし",
    };
    let primary_evidence_refs = typed_results
        .results
        .iter()
        .filter(|result| result.status == "measuredViolation")
        .flat_map(|result| result.detail_refs.iter().cloned())
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect::<Vec<_>>();
    json!({
        "status": status,
        "plainConclusion": plain_conclusion,
        "violatedLaws": violated_laws,
        "passedLaws": passed_laws,
        "blockedLaws": blocked_laws,
        "blockedReplacementReadings": blocked_replacement_readings,
        "distance": architecture_distance["summary"],
        "typedEvaluatorDiagnosis": {
            "violationCount": typed_results.summary.measured_violation_count,
            "blockedOrUnmeasuredCount": typed_results.summary.blocked_count
                + typed_results.summary.unknown_count
                + typed_results.summary.unmeasured_count
                + typed_results.replacement_summary.blocked_count,
            "replacementBlockedCount": typed_results.replacement_summary.blocked_count
        },
        "primaryEvidenceRefs": primary_evidence_refs,
        "nextActions": typed_next_actions(typed_results)
    })
}

fn laws_with_status(typed_results: &TypedEvaluatorResultsV1, status: &str) -> Vec<String> {
    typed_results
        .results
        .iter()
        .filter(|result| result.status == status)
        .map(|result| result.law.clone())
        .collect()
}

fn typed_next_actions(typed_results: &TypedEvaluatorResultsV1) -> Vec<Value> {
    typed_results
        .results
        .iter()
        .chain(
            typed_results
                .replacement_evaluator_results
                .iter()
                .filter(|result| result.status == "blocked"),
        )
        .filter(|result| result.status == "measuredViolation" || result.status == "blocked")
        .map(|result| {
            json!({
                "law": result.law,
                "replacementId": result.replacement_id,
                "actionKind": if result.status == "blocked" {
                    "collectEvidence"
                } else {
                    "reviewViolation"
                },
                "detailRefs": result.detail_refs,
                "blockerReason": result.blocker_reason
            })
        })
        .collect()
}

fn architecture_distance_profile_v1(profile_ref: &str) -> Option<ArchitectureDistanceProfileV1> {
    match profile_ref {
        "distance-profile:practical-rust-service@1" => Some(ArchitectureDistanceProfileV1 {
            profile_ref: "distance-profile:practical-rust-service@1",
            atom_kind_weight: 1,
            axis_weight: 1,
            predicate_constructor_weight: 1,
            predicate_binding_weight: 2,
            configuration_atom_weight: 1,
            signature_violation_weight: 2,
            dependency_inversion_operation_cost: 4,
            infrastructure_dependency_operation_cost: 6,
            default_operation_cost: 3,
        }),
        "distance-profile:architecture-default@1" => Some(ArchitectureDistanceProfileV1 {
            profile_ref: "distance-profile:architecture-default@1",
            atom_kind_weight: 1,
            axis_weight: 1,
            predicate_constructor_weight: 1,
            predicate_binding_weight: 1,
            configuration_atom_weight: 1,
            signature_violation_weight: 1,
            dependency_inversion_operation_cost: 4,
            infrastructure_dependency_operation_cost: 5,
            default_operation_cost: 3,
        }),
        _ => None,
    }
}

fn architecture_atom_distance_readings(
    normalized: &NormalizedArchMapV1,
    profile: ArchitectureDistanceProfileV1,
) -> Vec<Value> {
    let atoms_by_id = normalized
        .atoms
        .iter()
        .map(|atom| (atom.normalized_atom_id.as_str(), atom))
        .collect::<BTreeMap<_, _>>();
    let mut readings = Vec::new();
    for molecule in &normalized.molecules {
        if molecule.generated_molecule_candidate_status != "generated" {
            readings.push(blocked_distance_reading(
                "atomDistance",
                &format!(
                    "atom-distance:{}",
                    stable_ref(&molecule.normalized_molecule_id)
                ),
                "molecule candidate is not generated",
                vec![molecule.normalized_molecule_id.clone()],
            ));
            continue;
        }
        for left_index in 0..molecule.atom_ids.len() {
            for right_index in (left_index + 1)..molecule.atom_ids.len() {
                let left_id = &molecule.atom_ids[left_index];
                let right_id = &molecule.atom_ids[right_index];
                let Some(left) = atoms_by_id.get(left_id.as_str()) else {
                    readings.push(blocked_distance_reading(
                        "atomDistance",
                        &format!(
                            "atom-distance:{}:{}",
                            stable_ref(left_id),
                            stable_ref(right_id)
                        ),
                        "left atom ref is missing from normalized ArchMap",
                        vec![molecule.normalized_molecule_id.clone(), left_id.clone()],
                    ));
                    continue;
                };
                let Some(right) = atoms_by_id.get(right_id.as_str()) else {
                    readings.push(blocked_distance_reading(
                        "atomDistance",
                        &format!(
                            "atom-distance:{}:{}",
                            stable_ref(left_id),
                            stable_ref(right_id)
                        ),
                        "right atom ref is missing from normalized ArchMap",
                        vec![molecule.normalized_molecule_id.clone(), right_id.clone()],
                    ));
                    continue;
                };
                let components = atom_distance_components(left, right, profile);
                let measured_value = components
                    .iter()
                    .filter_map(|component| component["value"].as_i64())
                    .sum::<i64>();
                readings.push(json!({
                    "readingId": format!("atom-distance:{}:{}", stable_ref(left_id), stable_ref(right_id)),
                    "distanceFamily": "atomGeometry",
                    "status": "measured",
                    "measuredValue": measured_value,
                    "unit": "architecture-distance-point",
                    "sourceAtomRef": left_id,
                    "targetAtomRef": right_id,
                    "moleculeRef": molecule.normalized_molecule_id,
                    "components": components,
                    "detailRefs": [left_id, right_id, &molecule.normalized_molecule_id]
                }));
            }
        }
    }
    readings
}

fn atom_distance_components(
    left: &NormalizedAtomV1,
    right: &NormalizedAtomV1,
    profile: ArchitectureDistanceProfileV1,
) -> Vec<Value> {
    vec![
        distance_component(
            "atomKind",
            &left.atom_kind,
            &right.atom_kind,
            profile.atom_kind_weight,
        ),
        distance_component("axis", &left.axis, &right.axis, profile.axis_weight),
        distance_component(
            "predicateConstructor",
            &left.predicate.constructor,
            &right.predicate.constructor,
            profile.predicate_constructor_weight,
        ),
        json!({
            "component": "predicateBindings",
            "left": binding_values(left),
            "right": binding_values(right),
            "weight": profile.predicate_binding_weight,
            "value": binding_distance(left, right) * profile.predicate_binding_weight
        }),
    ]
}

fn distance_component(component: &str, left: &str, right: &str, weight: i64) -> Value {
    json!({
        "component": component,
        "left": left,
        "right": right,
        "weight": weight,
        "value": if left == right { 0 } else { weight }
    })
}

fn binding_values(atom: &NormalizedAtomV1) -> Vec<String> {
    atom.predicate
        .bindings
        .iter()
        .map(|binding| format!("{}={}", binding.role, binding.value))
        .collect()
}

fn binding_distance(left: &NormalizedAtomV1, right: &NormalizedAtomV1) -> i64 {
    let left_values = binding_values(left).into_iter().collect::<BTreeSet<_>>();
    let right_values = binding_values(right).into_iter().collect::<BTreeSet<_>>();
    left_values.symmetric_difference(&right_values).count() as i64
}

fn architecture_configuration_distance_readings(
    normalized: &NormalizedArchMapV1,
    profile: ArchitectureDistanceProfileV1,
) -> Vec<Value> {
    normalized
        .molecules
        .iter()
        .map(|molecule| configuration_distance_reading(molecule, profile))
        .collect()
}

fn configuration_distance_reading(
    molecule: &NormalizedMoleculeV1,
    profile: ArchitectureDistanceProfileV1,
) -> Value {
    if molecule.generated_molecule_candidate_status != "generated" {
        return blocked_distance_reading(
            "configurationDistance",
            &format!(
                "configuration-distance:{}",
                stable_ref(&molecule.normalized_molecule_id)
            ),
            "molecule candidate is not generated",
            vec![molecule.normalized_molecule_id.clone()],
        );
    }
    let measured_value =
        molecule.atom_ids.len().saturating_sub(1) as i64 * profile.configuration_atom_weight;
    json!({
        "readingId": format!("configuration-distance:{}", stable_ref(&molecule.normalized_molecule_id)),
        "distanceFamily": "configuration",
        "status": "measured",
        "measuredValue": measured_value,
        "unit": "architecture-distance-point",
        "moleculeRef": molecule.normalized_molecule_id,
        "atomCount": molecule.atom_ids.len(),
        "weight": profile.configuration_atom_weight,
        "basis": "configuration size above single atom baseline",
        "detailRefs": std::iter::once(molecule.normalized_molecule_id.clone())
            .chain(molecule.atom_ids.iter().cloned())
            .collect::<Vec<_>>()
    })
}

fn architecture_signature_distance_readings(
    typed_results: &TypedEvaluatorResultsV1,
    profile: ArchitectureDistanceProfileV1,
) -> Vec<Value> {
    typed_results
        .results
        .iter()
        .map(|result| {
            if result.status == "blocked"
                || result.status == "unknown"
                || result.status == "unmeasured"
            {
                return blocked_distance_reading(
                    "signatureDistance",
                    &format!("signature-distance:{}", stable_ref(&result.law)),
                    result
                        .blocker_reason
                        .as_deref()
                        .unwrap_or("typed evaluator result is not measured"),
                    result.detail_refs.clone(),
                );
            }
            json!({
                "readingId": format!("signature-distance:{}", stable_ref(&result.law)),
                "distanceFamily": "signature",
                "law": result.law,
                "evaluator": result.evaluator,
                "status": "measured",
                "measuredValue": if result.status == "measuredViolation" {
                    profile.signature_violation_weight
                } else {
                    0
                },
                "unit": "architecture-distance-point",
                "weight": profile.signature_violation_weight,
                "basisRefs": result.basis_refs,
                "detailRefs": result.detail_refs
            })
        })
        .collect()
}

fn architecture_operation_distance_readings(
    typed_results: &TypedEvaluatorResultsV1,
    profile: ArchitectureDistanceProfileV1,
) -> Vec<Value> {
    typed_results
        .results
        .iter()
        .filter(|result| result.status == "measuredViolation" || result.status == "blocked")
        .map(|result| {
            if result.status == "blocked" {
                return blocked_distance_reading(
                    "operationDistance",
                    &format!("operation-distance:{}", stable_ref(&result.law)),
                    result
                        .blocker_reason
                        .as_deref()
                        .unwrap_or("operation cannot be selected for blocked evaluator result"),
                    result.detail_refs.clone(),
                );
            }
            let (operation_kind, cost) = recommended_operation(&result.law, profile);
            json!({
                "readingId": format!("operation-distance:{}", stable_ref(&result.law)),
                "distanceFamily": "operation",
                "law": result.law,
                "status": "measured",
                "operationKind": operation_kind,
                "measuredValue": cost,
                "unit": "architecture-distance-point",
                "basis": "registry-owned recommended operation cost for selected violation",
                "detailRefs": result.detail_refs
            })
        })
        .collect()
}

fn recommended_operation(law: &str, profile: ArchitectureDistanceProfileV1) -> (&'static str, i64) {
    match law {
        "solid.dependency-inversion" => (
            "introduce-or-confirm-port-boundary",
            profile.dependency_inversion_operation_cost,
        ),
        "domain.no-direct-infra-dependency" => (
            "split-domain-infrastructure-boundary",
            profile.infrastructure_dependency_operation_cost,
        ),
        _ => ("review-selected-violation", profile.default_operation_cost),
    }
}

fn blocked_distance_reading(
    family: &str,
    reading_id: &str,
    blocker_reason: &str,
    detail_refs: Vec<String>,
) -> Value {
    json!({
        "readingId": reading_id,
        "distanceFamily": family,
        "status": "blocked",
        "measuredValue": null,
        "unit": "architecture-distance-point",
        "blockerReason": blocker_reason,
        "detailRefs": detail_refs
    })
}

fn measured_sum(readings: &[Value], value_field: &str) -> i64 {
    readings
        .iter()
        .filter(|reading| reading["status"] == "measured")
        .filter_map(|reading| reading[value_field].as_i64())
        .sum()
}

fn count_non_measured(readings: &[Value]) -> usize {
    readings
        .iter()
        .filter(|reading| reading["status"] != "measured")
        .count()
}

fn blocked_distance_results(
    atom_readings: &[Value],
    configuration_readings: &[Value],
    signature_readings: &[Value],
    operation_readings: &[Value],
) -> Vec<Value> {
    atom_readings
        .iter()
        .chain(configuration_readings.iter())
        .chain(signature_readings.iter())
        .chain(operation_readings.iter())
        .filter(|reading| reading["status"] != "measured")
        .map(|reading| {
            json!({
                "readingId": reading["readingId"],
                "distanceFamily": reading["distanceFamily"],
                "status": reading["status"],
                "blockerReason": reading["blockerReason"],
                "detailRefs": reading["detailRefs"]
            })
        })
        .collect()
}

fn architecture_distance_detail_refs(
    atom_readings: &[Value],
    configuration_readings: &[Value],
    signature_readings: &[Value],
    operation_readings: &[Value],
) -> Vec<String> {
    atom_readings
        .iter()
        .chain(configuration_readings.iter())
        .chain(signature_readings.iter())
        .chain(operation_readings.iter())
        .flat_map(|reading| {
            reading["detailRefs"]
                .as_array()
                .into_iter()
                .flatten()
                .filter_map(|value| value.as_str().map(ToString::to_string))
        })
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect()
}

fn stable_ref(value: &str) -> String {
    value
        .chars()
        .map(|character| {
            if character.is_ascii_alphanumeric() {
                character
            } else {
                '-'
            }
        })
        .collect()
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{LawPolicyDocumentV1, NormalizedArchMapSummaryV1};

    #[test]
    fn architecture_distance_builder_rejects_unknown_profile_ref() {
        let normalized = NormalizedArchMapV1 {
            schema: "normalized-archmap/v1".to_string(),
            normalizer_id: "test-normalizer".to_string(),
            source_archmap_ref: "archmap.json".to_string(),
            source_archmap_id: "archmap:test".to_string(),
            atoms: Vec::new(),
            molecules: Vec::new(),
            summary: NormalizedArchMapSummaryV1 {
                atom_count: 0,
                normalized_atom_count: 0,
                molecule_count: 0,
                generated_molecule_candidate_count: 0,
                blocked_molecule_candidate_count: 0,
            },
            non_conclusions: Vec::new(),
        };
        let policy = LawPolicyDocumentV1 {
            schema: "law-policy/v1".to_string(),
            id: "policy:test".to_string(),
            distance_profile_ref: Some("distance-profile:unknown@1".to_string()),
            policies: Vec::new(),
        };
        let typed_results = TypedEvaluatorResultsV1 {
            schema: TYPED_EVALUATOR_RESULTS_V1_SCHEMA.to_string(),
            pipeline_id: PIPELINE_ID.to_string(),
            normalized_archmap_ref: "normalized-archmap.json".to_string(),
            law_policy_ref: "law-policy.json".to_string(),
            replacement_registry_ref: REPLACEMENT_REGISTRY_REF.to_string(),
            replacement_registry: Vec::new(),
            results: Vec::new(),
            replacement_evaluator_results: Vec::new(),
            summary: TypedEvaluatorResultsSummaryV1 {
                result_count: 0,
                measured_pass_count: 0,
                measured_violation_count: 0,
                blocked_count: 0,
                unknown_count: 0,
                unmeasured_count: 0,
            },
            replacement_summary: TypedEvaluatorResultsSummaryV1 {
                result_count: 0,
                measured_pass_count: 0,
                measured_violation_count: 0,
                blocked_count: 0,
                unknown_count: 0,
                unmeasured_count: 0,
            },
            replacement_registry_resolution: ReplacementRegistryResolutionV1 {
                schema: "archsig-replacement-registry-resolution/v1".to_string(),
                registry_ref: REPLACEMENT_REGISTRY_REF.to_string(),
                manifest_count: 0,
                resolved_replacement_count: 0,
                blocked_replacement_count: 0,
                non_diagnostic_replacement_count: 0,
                replaced_v0_fields: Vec::new(),
                non_conclusions: Vec::new(),
            },
            positive_bounded_conclusions: Vec::new(),
            non_conclusions: Vec::new(),
        };

        let error = build_architecture_distance_v1(&normalized, &policy, &typed_results)
            .expect_err("unknown distance profile must fail closed");
        assert!(error.contains("unknown architecture distance profile ref"));
    }
}
