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
    let spectrum = architecture_spectrum_v1(normalized, typed_results);
    let homotopy = architecture_homotopy_v1(normalized, typed_results, &spectrum);
    let structural = architecture_structural_v1(
        normalized,
        typed_results,
        architecture_distance,
        &generated_obstructions,
        &generated_repair_targets,
        &spectrum,
        &homotopy,
    );
    let part4_distance_coverage_ledger = typed_part4_distance_coverage_ledger_v1(
        architecture_distance,
        &spectrum,
        &homotopy,
        &structural,
    );
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
        "part4DistanceCoverageLedger": part4_distance_coverage_ledger,
        "generatedLawInputs": generated_law_inputs,
        "signatureAxes": signature_axes,
        "generatedObstructions": generated_obstructions,
        "generatedRepairTargets": generated_repair_targets,
        "curvatureSupportReadings": spectrum["curvatureSupportReadings"],
        "curvatureTransferReadings": spectrum["curvatureTransferReadings"],
        "curvatureMassReadings": spectrum["curvatureMassReadings"],
        "spectralAnalysisReadings": spectrum["spectralAnalysisReadings"],
        "spectralModeReadings": spectrum["spectralModeReadings"],
        "spectralDrilldownReadings": spectrum["spectralDrilldownReadings"],
        "architectureSpectrumReport": spectrum["architectureSpectrumReport"],
        "pathHomotopyDiagramReadings": homotopy["pathHomotopyDiagramReadings"],
        "homotopyHolonomyReadings": homotopy["homotopyHolonomyReadings"],
        "stokesStyleReadings": homotopy["stokesStyleReadings"],
        "homotopyDistanceReadings": homotopy["homotopyDistanceReadings"],
        "architectureHomotopyReport": homotopy["architectureHomotopyReport"],
        "representationMetricReadings": structural["representationMetricReadings"],
        "localCurvatureDiagramReadings": structural["localCurvatureDiagramReadings"],
        "threeLayerFlatnessReadings": structural["threeLayerFlatnessReadings"],
        "observationProjectionReadings": structural["observationProjectionReadings"],
        "stateTransitionAlgebraReadings": structural["stateTransitionAlgebraReadings"],
        "effectRelationAlgebraReadings": structural["effectRelationAlgebraReadings"],
        "synthesisBlockageReadings": structural["synthesisBlockageReadings"],
        "operationPreconditionReadinessReadings": structural["operationPreconditionReadinessReadings"],
        "pathMultiplicityLossReadings": structural["pathMultiplicityLossReadings"],
        "structuralReadingReviewSurface": structural["structuralReadingReviewSurface"],
        "generatedPacketRefs": {
            "basis": "typed-evaluator-results + law-evaluator-registry",
            "generatedLawInputs": "/generatedLawInputs",
            "signatureAxes": "/signatureAxes",
            "generatedObstructions": "/generatedObstructions",
            "generatedRepairTargets": "/generatedRepairTargets",
            "architectureSpectrumReport": "/architectureSpectrumReport",
            "curvatureSupportReadings": "/curvatureSupportReadings",
            "curvatureTransferReadings": "/curvatureTransferReadings",
            "curvatureMassReadings": "/curvatureMassReadings",
            "spectralAnalysisReadings": "/spectralAnalysisReadings",
            "spectralModeReadings": "/spectralModeReadings",
            "spectralDrilldownReadings": "/spectralDrilldownReadings",
            "architectureHomotopyReport": "/architectureHomotopyReport",
            "pathHomotopyDiagramReadings": "/pathHomotopyDiagramReadings",
            "homotopyHolonomyReadings": "/homotopyHolonomyReadings",
            "stokesStyleReadings": "/stokesStyleReadings",
            "homotopyDistanceReadings": "/homotopyDistanceReadings",
            "structuralReadingReviewSurface": "/structuralReadingReviewSurface",
            "representationMetricReadings": "/representationMetricReadings",
            "localCurvatureDiagramReadings": "/localCurvatureDiagramReadings",
            "threeLayerFlatnessReadings": "/threeLayerFlatnessReadings",
            "observationProjectionReadings": "/observationProjectionReadings",
            "stateTransitionAlgebraReadings": "/stateTransitionAlgebraReadings",
            "effectRelationAlgebraReadings": "/effectRelationAlgebraReadings",
            "synthesisBlockageReadings": "/synthesisBlockageReadings",
            "operationPreconditionReadinessReadings": "/operationPreconditionReadinessReadings",
            "pathMultiplicityLossReadings": "/pathMultiplicityLossReadings",
            "typedEvaluatorResults": "/typedEvaluatorResults",
            "architectureDistanceSignatureReadings": "/architectureDistance/signatureDistanceReadings",
            "part4DistanceCoverageLedger": "/part4DistanceCoverageLedger"
        },
        "positiveBoundedConclusions": typed_results.positive_bounded_conclusions,
        "detailRefs": detail_refs,
        "nonConclusions": [
            "ArchSig v1 packet is computed from Normalized ArchMap v1 and TypedEvaluatorResults v1.",
            "Generated law inputs, signature axes, obstruction candidates, and repair targets are derived packet refs over typed evaluator results and registry basis.",
            "ArchitectureSpectrumReport/v1 is derived from normalized support, typed evaluator results, and coverage status; it does not read v0 spectrumMeasurementProfile.",
            "ArchitectureHomotopyReport/v1 is derived from normalized relations, explicit molecule candidates, typed evaluator results, and coverage status; it does not read v0 operationSquareEvidence or homotopyMeasurementProfile.",
            "StructuralReadingReviewSurface/v1 is derived from normalized atoms, explicit molecule candidates, typed evaluator results, and generated packet refs; it does not read v0 projectionInfo, concernHints, or observationGaps as positive input.",
            "ArchSig v1 packet does not read v0 semanticObservations, projectionInfo, operationSquareEvidence, concernHints, observationGaps, or homotopyMeasurementProfile.",
            "Blocked, unknown, and unmeasured evaluator results are not measured zero.",
            "ArchSig v1 packet is a computation artifact, not a Lean proof object."
        ]
    })
}

fn typed_part4_distance_coverage_ledger_v1(
    architecture_distance: &Value,
    spectrum: &Value,
    homotopy: &Value,
    structural: &Value,
) -> Vec<Value> {
    let boundary_status =
        typed_part4_boundary_status_v1(architecture_distance, spectrum, homotopy, structural);
    vec![
        typed_part4_ledger_entry_v1(
            "part4-ledger:distance-aat",
            "definition:1.1",
            "DistanceAAT",
            "foundation",
            boundary_status.clone(),
            packet_refs(&["/architectureDistance", "/distanceDiagnosis"]),
            vec!["architecture-distance.json#/summary"],
            1,
        ),
        typed_part4_ledger_entry_v1(
            "part4-ledger:atom-geometry",
            "definitions:2.1-2.5",
            "Fiber / Carrier / Valence / Semantic Anchor / Atom Layout distance",
            "atomGeometry",
            typed_family_status_from_array(architecture_distance, "atomDistanceReadings"),
            packet_refs(&["/architectureDistance/atomDistanceReadings"]),
            vec!["architecture-distance.json#/atomDistanceReadings"],
            packet_array_len(architecture_distance, "atomDistanceReadings"),
        ),
        typed_part4_ledger_entry_v1(
            "part4-ledger:configuration-context",
            "definitions:3.1-3.2",
            "Configuration-indexed distance and Context distance",
            "configurationGeometry",
            typed_family_status_from_array(architecture_distance, "configurationDistanceReadings"),
            packet_refs(&["/architectureDistance/configurationDistanceReadings"]),
            vec!["architecture-distance.json#/configurationDistanceReadings"],
            packet_array_len(architecture_distance, "configurationDistanceReadings"),
        ),
        typed_part4_ledger_entry_v1(
            "part4-ledger:signature-geometry",
            "definitions:4.1-4.4",
            "Axis distance, Signature distance, Safe margin, and Signature drift",
            "signatureGeometry",
            typed_family_status_from_array(architecture_distance, "signatureDistanceReadings"),
            packet_refs(&[
                "/architectureDistance/signatureDistanceReadings",
                "/signatureAxes",
            ]),
            vec![
                "architecture-distance.json#/signatureDistanceReadings",
                "archsig-analysis-summary.json#/distanceDiagnosis/topMovedAxes",
            ],
            packet_array_len(architecture_distance, "signatureDistanceReadings"),
        ),
        typed_part4_ledger_entry_v1(
            "part4-ledger:operation-geometry",
            "definitions:5.1-5.5",
            "Operation cost, Operation distance, Flatness distance, Repair route, and Side-effect bound",
            "operationGeometry",
            typed_family_status_from_array(architecture_distance, "operationDistanceReadings"),
            packet_refs(&["/architectureDistance/operationDistanceReadings"]),
            vec![
                "architecture-distance.json#/operationDistanceReadings",
                "archsig-analysis-summary.json#/distanceDiagnosis",
            ],
            packet_array_len(architecture_distance, "operationDistanceReadings"),
        ),
        typed_part4_ledger_entry_v1(
            "part4-ledger:obstruction-curvature",
            "definitions:6.1-6.3",
            "Obstruction measure, Curvature mass, and Curvature transport",
            "curvatureGeometry",
            typed_family_status_from_array(spectrum, "curvatureMassReadings"),
            packet_refs(&[
                "/curvatureSupportReadings",
                "/curvatureTransferReadings",
                "/curvatureMassReadings",
            ]),
            vec![
                "architecture-distance.json#/obstructionMeasureReadings",
                "architecture-distance.json#/curvatureSupportReadings",
                "architecture-distance.json#/curvatureTransferReadings",
                "architecture-distance.json#/curvatureMassReadings",
                "archsig-analysis-summary.json#/distanceDiagnosis/curvatureInsights",
            ],
            packet_array_len(spectrum, "curvatureMassReadings"),
        ),
        typed_part4_ledger_entry_v1(
            "part4-ledger:homotopy-filling",
            "definitions:7.1-7.4",
            "Homotopy distance, Filling cost, Observation gap lower bound, and Architectural Dehn function",
            "homotopyFillingGeometry",
            typed_family_status_from_array(homotopy, "homotopyDistanceReadings"),
            packet_refs(&[
                "/homotopyDistanceReadings",
                "/architectureHomotopyReport",
                "/homotopyHolonomyReadings",
            ]),
            vec![
                "archsig-analysis-packet.json#/homotopyDistanceReadings",
                "archsig-analysis-packet.json#/architectureHomotopyReport",
            ],
            packet_array_len(homotopy, "homotopyDistanceReadings"),
        ),
        typed_part4_ledger_entry_v1(
            "part4-ledger:representation-metric",
            "definitions:8.1-8.2",
            "Representation stability and Representation faithfulness",
            "representationMetric",
            representation_metric_family_status_v1(structural),
            packet_refs(&["/representationMetricReadings"]),
            vec![
                "architecture-distance.json#/representationMetricReadings",
                "archsig-analysis-summary.json#/distanceDiagnosis/representationInsights",
            ],
            packet_array_len(structural, "representationMetricReadings"),
        ),
        typed_part4_ledger_entry_v1(
            "part4-ledger:measurement-boundary",
            "definitions:9.1-9.3",
            "DistanceValue, unmeasured-is-not-zero, and DistanceProfile",
            "measurementBoundary",
            boundary_status.clone(),
            packet_refs(&[
                "/architectureDistance/profile",
                "/architectureDistance/summary",
                "/architectureDistance/distanceDiagnosis",
            ]),
            vec![
                "architecture-distance.json#/profile",
                "architecture-distance.json#/summary",
                "archsig-analysis-summary.json#/distanceDiagnosis",
            ],
            architecture_distance["summary"]["readingCounts"]
                .as_object()
                .map(|counts| counts.len())
                .unwrap_or_default(),
        ),
        typed_part4_ledger_entry_v1(
            "part4-ledger:bounded-diagnostic-conclusion",
            "definitions:10.1-10.2",
            "Diagnostic scope and Bounded diagnostic conclusion",
            "boundedDiagnosticConclusion",
            boundary_status,
            packet_refs(&["/distanceDiagnosis", "/structuralReadingReviewSurface"]),
            vec![
                "archsig-analysis-summary.json#/conclusion",
                "archsig-analysis-summary.json#/distanceDiagnosis",
                "llm-interpretation-packet.json#/distanceDiagnosisSummary",
            ],
            1,
        ),
    ]
}

fn typed_part4_ledger_entry_v1(
    ledger_entry_id: &str,
    part4_definition_ref: &str,
    definition_title: &str,
    distance_family: &str,
    measurement_status: impl Into<String>,
    raw_packet_refs: Vec<String>,
    primary_artifact_refs: Vec<&str>,
    reading_count: usize,
) -> Value {
    let measurement_status = measurement_status.into();
    let coverage_status = if reading_count == 0 {
        "not-applicable"
    } else if measurement_status == "blocked" {
        "primary-blocked"
    } else {
        "primary"
    };
    let blocker_refs = if measurement_status == "blocked" {
        vec![format!("blockedDistanceFamily:{distance_family}")]
    } else if measurement_status == "unmeasured" {
        vec![format!("unmeasuredDistanceFamily:{distance_family}")]
    } else if measurement_status == "partial" {
        vec![format!("partialDistanceFamily:{distance_family}")]
    } else {
        Vec::new()
    };
    json!({
        "ledgerEntryId": ledger_entry_id,
        "part4DefinitionRef": part4_definition_ref,
        "definitionTitle": definition_title,
        "distanceFamily": distance_family,
        "coverageStatus": coverage_status,
        "measurementStatus": measurement_status,
        "readingCount": reading_count,
        "primaryArtifactRefs": primary_artifact_refs,
        "rawPacketRefs": raw_packet_refs,
        "blockerRefs": blocker_refs,
        "evidenceBoundary": "typed v1 ledger records where the selected Part IV distance family is exposed in ArchSig outputs; it is not a proof object",
        "nonConclusions": [
            "ArchSig distance coverage is relative to the supplied ArchMap, selected LawPolicy, typed evaluator results, and distance profile.",
            "Unmeasured or blocked distance is not measured zero.",
            "Part IV distance coverage ledger is an output navigation contract, not a Lean theorem proof."
        ]
    })
}

fn packet_refs(refs: &[&str]) -> Vec<String> {
    refs.iter()
        .map(|reference| format!("packet:{reference}"))
        .collect()
}

fn typed_family_status_from_array(source: &Value, field: &str) -> String {
    let Some(items) = source[field].as_array() else {
        return "not-applicable".to_string();
    };
    if items.is_empty() {
        return "not-applicable".to_string();
    }
    let statuses = items
        .iter()
        .filter_map(|item| {
            item["measurementStatus"]
                .as_str()
                .or_else(|| item["status"].as_str())
        })
        .collect::<Vec<_>>();
    if statuses
        .iter()
        .any(|status| status.to_ascii_lowercase().contains("blocked"))
    {
        "blocked".to_string()
    } else if statuses
        .iter()
        .any(|status| matches!(*status, "unmeasured" | "unknown" | "unavailable"))
    {
        "unmeasured".to_string()
    } else if statuses.iter().any(|status| {
        matches!(
            *status,
            "measured" | "measuredPass" | "measuredViolation" | "measuredZero" | "zero"
        )
    }) {
        "measured".to_string()
    } else {
        "partial".to_string()
    }
}

fn typed_part4_boundary_status_v1(
    architecture_distance: &Value,
    spectrum: &Value,
    homotopy: &Value,
    structural: &Value,
) -> String {
    let statuses = [
        typed_family_status_from_array(architecture_distance, "atomDistanceReadings"),
        typed_family_status_from_array(architecture_distance, "configurationDistanceReadings"),
        typed_family_status_from_array(architecture_distance, "signatureDistanceReadings"),
        typed_family_status_from_array(architecture_distance, "operationDistanceReadings"),
        typed_family_status_from_array(spectrum, "curvatureMassReadings"),
        typed_family_status_from_array(homotopy, "homotopyDistanceReadings"),
        representation_metric_family_status_v1(structural),
    ];
    if statuses
        .iter()
        .any(|status| matches!(status.as_str(), "blocked" | "unmeasured" | "partial"))
    {
        "partial".to_string()
    } else {
        "measured".to_string()
    }
}

pub fn enrich_architecture_distance_with_part4_bundle_v1(
    architecture_distance: &Value,
    packet: &Value,
    emit_raw_artifacts: bool,
) -> Value {
    let mut enriched = architecture_distance.clone();
    let family_summaries = architecture_distance_family_summaries_v1(
        architecture_distance,
        packet,
        emit_raw_artifacts,
    );
    let measurement_state_summary =
        architecture_distance_measurement_state_summary(&family_summaries);
    let obstruction_measure_readings = primary_obstruction_measure_readings_v1(packet);
    let curvature_support_readings = packet_array_clone(packet, "curvatureSupportReadings");
    let curvature_transfer_readings = packet_array_clone(packet, "curvatureTransferReadings");
    let curvature_mass_readings = packet_array_clone(packet, "curvatureMassReadings");
    let curvature_insights = curvature_primary_insights_v1(
        &obstruction_measure_readings,
        &curvature_support_readings,
        &curvature_transfer_readings,
        &curvature_mass_readings,
    );
    let representation_metric_readings = primary_representation_metric_readings_v1(packet);
    let representation_insights =
        representation_primary_insights_v1(&representation_metric_readings);
    let mut primary_insights_refs = vec![
        "architecture-distance.json#/familySummaries",
        "architecture-distance.json#/measurementStateSummary",
        "architecture-distance.json#/distanceDiagnosis/familySummaries",
        "architecture-distance.json#/distanceDiagnosis/curvatureInsights",
        "architecture-distance.json#/distanceDiagnosis/representationInsights",
        "archsig-analysis-summary.json#/distanceDiagnosis",
        "archsig-atom-viewer-data.json#/reportPane/distanceDiagnosis",
    ];
    let optional_raw_artifact_refs = json!([
        "llm-interpretation-packet.json#/distanceDiagnosisSummary",
        "archsig-analysis-detail-index.json#/sections/part4DistanceCoverageLedger"
    ]);
    if emit_raw_artifacts {
        primary_insights_refs.extend([
            "llm-interpretation-packet.json#/distanceDiagnosisSummary",
            "archsig-analysis-detail-index.json#/sections/part4DistanceCoverageLedger",
        ]);
    }
    let primary_insights_refs = json!(primary_insights_refs);
    let measured_total_scope = architecture_distance_measured_total_scope(&family_summaries);
    let bundle_status = measurement_state_summary["status"]
        .as_str()
        .unwrap_or("partial")
        .to_string();
    let verdict = if bundle_status == "missing-family" {
        "ARCHITECTURE_DISTANCE_MISSING_CANONICAL_FAMILY"
    } else if bundle_status == "partial" {
        "ARCHITECTURE_DISTANCE_PARTIALLY_BLOCKED"
    } else if enriched["summary"]["measuredTotal"]
        .as_i64()
        .unwrap_or_default()
        > 0
    {
        "ARCHITECTURE_DISTANCE_MEASURED"
    } else {
        "ARCHITECTURE_DISTANCE_ZERO"
    };

    enriched["familySummaries"] = Value::Array(family_summaries.clone());
    enriched["measurementStateSummary"] = measurement_state_summary.clone();
    enriched["obstructionMeasureReadings"] = obstruction_measure_readings.clone();
    enriched["curvatureSupportReadings"] = curvature_support_readings.clone();
    enriched["curvatureTransferReadings"] = curvature_transfer_readings.clone();
    enriched["curvatureMassReadings"] = curvature_mass_readings.clone();
    enriched["curvatureInsights"] = curvature_insights.clone();
    enriched["representationMetricReadings"] = representation_metric_readings.clone();
    enriched["representationInsights"] = representation_insights.clone();
    enriched["primaryInsightsRefs"] = primary_insights_refs.clone();
    enriched["optionalRawArtifactRefs"] = optional_raw_artifact_refs.clone();
    enriched["summary"]["status"] = json!(bundle_status);
    enriched["summary"]["familyCount"] = measurement_state_summary["familyCount"].clone();
    enriched["summary"]["missingCanonicalFamilyCount"] =
        measurement_state_summary["missingCanonicalFamilyCount"].clone();
    enriched["summary"]["explicitBlockedFamilyCount"] =
        measurement_state_summary["blockedFamilyCount"].clone();
    enriched["summary"]["notApplicableFamilyCount"] =
        measurement_state_summary["notApplicableFamilyCount"].clone();
    enriched["summary"]["measuredTotalScope"] = measured_total_scope.clone();
    enriched["summary"]["measuredTotalFamilyRefs"] =
        measured_total_scope["includedFamilies"].clone();
    enriched["summary"]["nonAggregatedFamilyRefs"] =
        measured_total_scope["nonAggregatedFamilies"].clone();
    enriched["distanceDiagnosis"]["verdict"] = json!(verdict);
    enriched["distanceDiagnosis"]["familySummaries"] = Value::Array(family_summaries);
    enriched["distanceDiagnosis"]["measurementStateSummary"] = measurement_state_summary;
    enriched["distanceDiagnosis"]["primaryInsightsRefs"] = primary_insights_refs;
    enriched["distanceDiagnosis"]["optionalRawArtifactRefs"] = optional_raw_artifact_refs;
    enriched["distanceDiagnosis"]["curvatureInsights"] = curvature_insights;
    enriched["distanceDiagnosis"]["representationInsights"] = representation_insights;
    enriched["distanceDiagnosis"]["distanceValue"]["status"] =
        enriched["summary"]["status"].clone();
    enriched["distanceDiagnosis"]["distanceValue"]["measuredTotalScope"] = measured_total_scope;
    enriched
}

fn packet_array_clone(packet: &Value, field: &str) -> Value {
    Value::Array(
        packet[field]
            .as_array()
            .into_iter()
            .flatten()
            .cloned()
            .collect(),
    )
}

fn primary_obstruction_measure_readings_v1(packet: &Value) -> Value {
    Value::Array(
        packet["curvatureSupportReadings"]
            .as_array()
            .into_iter()
            .flatten()
            .enumerate()
            .map(|(index, support)| {
                let curvature_status = support["curvatureValue"]["status"]
                    .as_str()
                    .unwrap_or("blockedByCoverageGap");
                let status = if curvature_status == "blockedByCoverageGap" {
                    "blocked"
                } else {
                    "measured"
                };
                json!({
                    "readingId": format!(
                        "obstruction-measure:{}",
                        stable_ref(support["law"].as_str().unwrap_or("selected-law"))
                    ),
                    "distanceFamily": "curvatureGeometry",
                    "part4DefinitionRef": "definitions:6.1",
                    "definitionName": "Obstruction Measure",
                    "status": status,
                    "measurementStatus": support["measurementStatus"],
                    "law": support["law"],
                    "evaluator": support["evaluator"],
                    "axisRef": support["axisRef"],
                    "supportReadingRef": format!("/curvatureSupportReadings/{index}"),
                    "primarySupportReadingRef": format!(
                        "architecture-distance.json#/curvatureSupportReadings/{index}"
                    ),
                    "obstructionMeasure": {
                        "status": support["curvatureValue"]["status"],
                        "measuredValue": support["curvatureValue"]["value"],
                        "unit": support["curvatureValue"]["unit"],
                        "blockerRefs": support["coverageGapRefs"]
                    },
                    "supportRefs": support["supportRefs"],
                    "witnessRefs": support["witnessRefs"],
                    "moleculeRefs": support["moleculeRefs"],
                    "sourceRefs": support["sourceRefs"],
                    "coverageGapRefs": support["coverageGapRefs"],
                    "basisRefs": support["basisRefs"],
                    "registryBasisRefs": support["registryBasisRefs"],
                    "readingBoundary": support["readingBoundary"],
                    "evidenceBoundary": "obstruction measure is selected-support curvature evidence, not a global lawfulness proof",
                    "nonConclusions": support["nonConclusions"]
                })
            })
            .collect(),
    )
}

fn curvature_primary_insights_v1(
    obstruction_measure_readings: &Value,
    curvature_support_readings: &Value,
    curvature_transfer_readings: &Value,
    curvature_mass_readings: &Value,
) -> Value {
    let supports = curvature_support_readings
        .as_array()
        .into_iter()
        .flatten()
        .collect::<Vec<_>>();
    let measured_zero_support_count = supports
        .iter()
        .filter(|reading| reading["curvatureValue"]["status"] == "measuredZero")
        .count();
    let measured_nonzero_support_count = supports
        .iter()
        .filter(|reading| reading["curvatureValue"]["status"] == "measuredNonzero")
        .count();
    let blocked_support_count = supports
        .iter()
        .filter(|reading| reading["curvatureValue"]["status"] == "blockedByCoverageGap")
        .count();
    let status = if supports.is_empty() {
        "no-selected-support"
    } else if blocked_support_count > 0 {
        "partial"
    } else if measured_nonzero_support_count > 0 {
        "measured-nonzero"
    } else {
        "measured-zero"
    };
    let mut top_supports = supports
        .iter()
        .enumerate()
        .map(|(index, reading)| {
            json!({
                "supportReadingRef": format!("architecture-distance.json#/curvatureSupportReadings/{index}"),
                "obstructionMeasureReadingRef": format!("architecture-distance.json#/obstructionMeasureReadings/{index}"),
                "law": reading["law"],
                "axisRef": reading["axisRef"],
                "curvatureValue": reading["curvatureValue"],
                "measurementStatus": reading["measurementStatus"],
                "supportRefs": reading["supportRefs"],
                "witnessRefs": reading["witnessRefs"],
                "moleculeRefs": reading["moleculeRefs"],
                "sourceRefs": reading["sourceRefs"],
                "coverageGapRefs": reading["coverageGapRefs"],
                "recommendedNextAction": if reading["curvatureValue"]["status"] == "measuredZero" {
                    "treat as selected-support zero and keep coverage boundary visible"
                } else if reading["curvatureValue"]["status"] == "measuredNonzero" {
                    "review selected obstruction witness and affected source refs"
                } else {
                    "collect missing witness support before reading this axis as zero"
                }
            })
        })
        .collect::<Vec<_>>();
    top_supports.sort_by_key(|reading| {
        if reading["curvatureValue"]["status"] == "measuredNonzero" {
            0
        } else if reading["curvatureValue"]["status"] == "blockedByCoverageGap" {
            1
        } else {
            2
        }
    });
    top_supports.truncate(6);
    let transfer = curvature_transfer_readings
        .as_array()
        .and_then(|items| items.first())
        .cloned()
        .unwrap_or(Value::Null);
    let mass = curvature_mass_readings
        .as_array()
        .and_then(|items| items.first())
        .cloned()
        .unwrap_or(Value::Null);
    json!({
        "status": status,
        "obstructionMeasureReadingCount": obstruction_measure_readings
            .as_array()
            .map(|items| items.len())
            .unwrap_or_default(),
        "curvatureSupportReadingCount": supports.len(),
        "curvatureTransferReadingCount": curvature_transfer_readings
            .as_array()
            .map(|items| items.len())
            .unwrap_or_default(),
        "curvatureMassReadingCount": curvature_mass_readings
            .as_array()
            .map(|items| items.len())
            .unwrap_or_default(),
        "measuredZeroSupportCount": measured_zero_support_count,
        "measuredNonzeroSupportCount": measured_nonzero_support_count,
        "blockedSupportCount": blocked_support_count,
        "curvatureMass": {
            "readingRef": mass["curvatureMassReadingId"],
            "measurementStatus": mass["measurementStatus"],
            "measuredZeroSupportCount": mass["measuredZeroSupportCount"],
            "measuredNonzeroSupportCount": mass["measuredNonzeroSupportCount"],
            "blockedSupportCount": mass["blockedSupportCount"],
            "supportReadingRefs": mass["supportReadingRefs"]
        },
        "curvatureTransport": {
            "readingRef": transfer["readingId"],
            "spectralRadiusKind": transfer["transferOperator"]["spectralRadiusKind"],
            "transferEdgeCount": transfer["transferEdges"]
                .as_array()
                .map(|items| items.len())
                .unwrap_or_default(),
            "recurrentObstructionModeCount": transfer["recurrentObstructionModes"]
                .as_array()
                .map(|items| items.len())
                .unwrap_or_default()
        },
        "topCurvatureSupports": top_supports,
        "reading": "curvature insights expose selected obstruction support, zero/nonzero/blocked counts, and transport state without treating zero curvature as global lawfulness",
        "nonConclusions": [
            "Measured zero curvature is bounded to selected support rows.",
            "Blocked support is not measured zero.",
            "Curvature transport is current-state diagnostic structure, not future incident prediction."
        ]
    })
}

fn primary_representation_metric_readings_v1(packet: &Value) -> Value {
    Value::Array(
        packet["representationMetricReadings"]
            .as_array()
            .into_iter()
            .flatten()
            .enumerate()
            .map(|(index, reading)| {
                let reading_id = reading["readingId"]
                    .as_str()
                    .or_else(|| reading["representationMetricReadingId"].as_str())
                    .unwrap_or("representation-metric:selected");
                let analytic_status = reading["analyticDistance"]["status"]
                    .as_str()
                    .unwrap_or("blocked");
                let structural_status = reading["structuralDistance"]["status"]
                    .as_str()
                    .unwrap_or("blocked");
                let raw_measurement_status =
                    reading["measurementStatus"].as_str().unwrap_or("blocked");
                let coverage_blocker_refs = representation_coverage_blocker_refs(reading);
                let witness_completeness_blocker_refs =
                    representation_witness_completeness_blocker_refs(reading);
                let status = if representation_status_is_blocked(raw_measurement_status)
                    || representation_status_is_blocked(structural_status)
                    || representation_status_is_blocked(analytic_status)
                {
                    "blocked"
                } else if analytic_status == "boundedProxy"
                    || representation_has_blocked_faithfulness(reading)
                {
                    "partial"
                } else if matches!(structural_status, "measured" | "zero")
                    && matches!(analytic_status, "measured" | "zero")
                {
                    "measured"
                } else {
                    "blocked"
                };
                let blocker_refs = representation_blocker_refs(reading);
                let source_refs = representation_source_refs(reading);
                let lipschitz_upper_bound = representation_lipschitz_upper_bound(reading);
                let bi_lipschitz_faithfulness =
                    representation_bi_lipschitz_faithfulness(reading, &blocker_refs);

                json!({
                    "readingId": reading_id,
                    "distanceFamily": "representationMetric",
                    "status": status,
                    "measurementStatus": status,
                    "representationFamily": reading["representationFamily"],
                    "representationRef": reading["representationRef"],
                    "rawPacketReadingRef": format!("packet:/representationMetricReadings/{index}"),
                    "primaryReadingRef": format!("architecture-distance.json#/representationMetricReadings/{index}"),
                    "typedEvaluatorResultRefs": reading["typedEvaluatorResultRefs"],
                    "normalizedAtomRefs": reading["normalizedAtomRefs"],
                    "normalizedMoleculeRefs": reading["normalizedMoleculeRefs"],
                    "signatureDistanceReadingRefs": reading["signatureDistanceReadingRefs"],
                    "operationDistanceReadingRefs": reading["operationDistanceReadingRefs"],
                    "sourceRefs": source_refs,
                    "structuralDistance": reading["structuralDistance"],
                    "analyticDistance": reading["analyticDistance"],
                    "lipschitzUpperBound": lipschitz_upper_bound,
                    "biLipschitzFaithfulness": bi_lipschitz_faithfulness,
                    "coverageGapRefs": reading["coverageGapRefs"],
                    "coverageBlockerRefs": coverage_blocker_refs,
                    "witnessCompletenessBlockerRefs": witness_completeness_blocker_refs,
                    "blockerRefs": blocker_refs,
                    "part4DefinitionReadings": [
                        {
                            "componentKind": "representationStability",
                            "part4DefinitionRef": "definitions:8.1",
                            "definitionName": "Representation Stability",
                            "structuralDistanceRef": format!("architecture-distance.json#/representationMetricReadings/{index}/structuralDistance"),
                            "analyticDistanceRef": format!("architecture-distance.json#/representationMetricReadings/{index}/analyticDistance"),
                            "lipschitzUpperBoundRef": format!("architecture-distance.json#/representationMetricReadings/{index}/lipschitzUpperBound")
                        },
                        {
                            "componentKind": "representationFaithfulness",
                            "part4DefinitionRef": "definitions:8.2",
                            "definitionName": "Representation Faithfulness",
                            "faithfulnessRef": format!("architecture-distance.json#/representationMetricReadings/{index}/biLipschitzFaithfulness")
                        }
                    ],
                    "evidenceBoundary": "representation metric is selected-scope evidence; bounded proxy telemetry is not a measured analytic distance or structural faithfulness claim",
                    "nonConclusions": [
                        "Bounded proxy analytic distance is not a measured representation distance.",
                        "Blocked faithfulness is not selected structural faithfulness.",
                        "Representation stability is scoped to selected structural and analytic readings, not all future comparable architectures."
                    ]
                })
            })
            .collect(),
    )
}

fn representation_primary_insights_v1(representation_metric_readings: &Value) -> Value {
    let readings = representation_metric_readings
        .as_array()
        .into_iter()
        .flatten()
        .collect::<Vec<_>>();
    let measured_structural_distance_count = readings
        .iter()
        .filter(|reading| {
            matches!(
                reading["structuralDistance"]["status"].as_str(),
                Some("measured" | "zero")
            )
        })
        .count();
    let measured_analytic_distance_count = readings
        .iter()
        .filter(|reading| {
            matches!(
                reading["analyticDistance"]["status"].as_str(),
                Some("measured" | "zero")
            )
        })
        .count();
    let bounded_proxy_analytic_count = readings
        .iter()
        .filter(|reading| reading["analyticDistance"]["status"] == "boundedProxy")
        .count();
    let blocked_analytic_distance_count = readings
        .iter()
        .filter(|reading| {
            matches!(
                reading["analyticDistance"]["status"].as_str(),
                Some("blocked" | "blockedByCoverageGap" | "unmeasured" | "unavailable")
            )
        })
        .count();
    let blocked_faithfulness_count = readings
        .iter()
        .filter(|reading| {
            !matches!(
                reading["biLipschitzFaithfulness"]["status"].as_str(),
                Some("measured" | "zero")
            )
        })
        .count();
    let status = if readings.is_empty() {
        "no-selected-representation"
    } else if bounded_proxy_analytic_count > 0
        || blocked_analytic_distance_count > 0
        || blocked_faithfulness_count > 0
    {
        "partial"
    } else {
        "measured"
    };
    let top_readings = readings
        .iter()
        .take(6)
        .map(|reading| {
            json!({
                "readingRef": reading["primaryReadingRef"],
                "representationFamily": reading["representationFamily"],
                "status": reading["status"],
                "structuralDistance": reading["structuralDistance"],
                "analyticDistance": reading["analyticDistance"],
                "lipschitzUpperBound": reading["lipschitzUpperBound"],
                "biLipschitzFaithfulness": reading["biLipschitzFaithfulness"],
                "sourceRefs": reading["sourceRefs"],
                "blockerRefs": reading["blockerRefs"],
                "recommendedNextAction": if reading["analyticDistance"]["status"] == "boundedProxy" {
                    "collect measured analytic representation evidence before reading proxy telemetry as distance"
                } else if !matches!(
                    reading["biLipschitzFaithfulness"]["status"].as_str(),
                    Some("measured" | "zero")
                ) {
                    "collect coverage and witness completeness evidence before claiming representation faithfulness"
                } else {
                    "read as selected-scope representation stability only"
                }
            })
        })
        .collect::<Vec<_>>();
    json!({
        "status": status,
        "representationMetricReadingCount": readings.len(),
        "measuredStructuralDistanceCount": measured_structural_distance_count,
        "measuredAnalyticDistanceCount": measured_analytic_distance_count,
        "boundedProxyAnalyticCount": bounded_proxy_analytic_count,
        "blockedAnalyticDistanceCount": blocked_analytic_distance_count,
        "blockedFaithfulnessCount": blocked_faithfulness_count,
        "topRepresentationMetrics": top_readings,
        "reading": "representation insights expose selected structural distance, analytic-distance state, Lipschitz upper-bound availability, and blocked faithfulness without promoting proxy telemetry to measured distance",
        "nonConclusions": [
            "Bounded proxy telemetry is not measured Representation Stability.",
            "Blocked bi-Lipschitz faithfulness is not Representation Faithfulness.",
            "Selected representation readings do not prove global structural equivalence."
        ]
    })
}

fn representation_lipschitz_upper_bound(reading: &Value) -> Value {
    let analytic_status = reading["analyticDistance"]["status"]
        .as_str()
        .unwrap_or("blocked");
    if analytic_status == "boundedProxy" {
        json!({
            "status": "blockedByProxy",
            "unit": "selected-L-upper-bound",
            "blockerRefs": representation_blocker_refs(reading),
            "reading": "Lipschitz upper-bound is blocked because analytic distance is bounded proxy telemetry, not measured representation distance"
        })
    } else if reading["lipschitzStability"].is_object() {
        reading["lipschitzStability"].clone()
    } else {
        json!({
            "status": "blocked",
            "unit": "selected-L-upper-bound",
            "blockerRefs": representation_blocker_refs(reading),
            "reading": "Lipschitz upper-bound is blocked until selected structural and analytic distances are measured with provenance"
        })
    }
}

fn representation_bi_lipschitz_faithfulness(reading: &Value, blocker_refs: &[String]) -> Value {
    if reading["biLipschitzFaithfulness"].is_object() {
        return reading["biLipschitzFaithfulness"].clone();
    }
    json!({
        "status": "blocked",
        "unit": "selected-bi-lipschitz-faithfulness",
        "blockerRefs": blocker_refs,
        "reading": "bi-Lipschitz faithfulness is blocked until coverage and witness completeness are supplied for the selected representation scope"
    })
}

fn representation_has_blocked_faithfulness(reading: &Value) -> bool {
    let status = reading["biLipschitzFaithfulness"]["status"].as_str();
    !matches!(status, Some("measured" | "zero"))
        || !representation_coverage_blocker_refs(reading).is_empty()
        || !representation_witness_completeness_blocker_refs(reading).is_empty()
}

fn representation_blocker_refs(reading: &Value) -> Vec<String> {
    let mut refs = representation_coverage_blocker_refs(reading);
    refs.extend(representation_witness_completeness_blocker_refs(reading));
    if let Some(status) = reading["measurementStatus"].as_str() {
        if representation_status_is_blocked(status) {
            refs.push(format!("measurement-status:{status}"));
        }
    }
    if reading["analyticDistance"]["status"] == "boundedProxy" {
        refs.push("bounded-proxy:selected-analytic-distance-not-measured".to_string());
    }
    if representation_has_blocked_faithfulness(reading) {
        refs.push("faithfulness:coverage-and-witness-completeness-required".to_string());
    }
    unique_string_values(refs.into_iter())
}

fn representation_coverage_blocker_refs(reading: &Value) -> Vec<String> {
    let mut refs = json_string_array_value(reading, "coverageGapRefs");
    refs.extend(json_string_array_value(reading, "coverageBlockerRefs"));
    if representation_has_proxy_or_unmeasured_faithfulness(reading) {
        refs.push("coverage-completeness:selected-representation-scope-not-certified".to_string());
    }
    unique_string_values(refs.into_iter())
}

fn representation_witness_completeness_blocker_refs(reading: &Value) -> Vec<String> {
    let mut refs = json_string_array_value(reading, "witnessCompletenessBlockerRefs");
    if representation_has_proxy_or_unmeasured_faithfulness(reading) {
        refs.push(
            "witness-completeness:selected-representation-faithfulness-not-certified".to_string(),
        );
    }
    unique_string_values(refs.into_iter())
}

fn representation_has_proxy_or_unmeasured_faithfulness(reading: &Value) -> bool {
    reading["analyticDistance"]["status"] == "boundedProxy"
        || !matches!(
            reading["biLipschitzFaithfulness"]["status"].as_str(),
            Some("measured" | "zero")
        )
}

fn representation_status_is_blocked(status: &str) -> bool {
    let normalized = status.to_ascii_lowercase();
    normalized.contains("blocked")
        || matches!(
            normalized.as_str(),
            "unmeasured" | "unknown" | "unavailable" | "incomparable" | "infinite"
        )
}

fn representation_source_refs(reading: &Value) -> Vec<String> {
    let mut refs = Vec::new();
    for field in [
        "normalizedAtomRefs",
        "normalizedMoleculeRefs",
        "typedEvaluatorResultRefs",
        "signatureDistanceReadingRefs",
        "operationDistanceReadingRefs",
        "sourceReadingRefs",
        "evidenceRefs",
    ] {
        refs.extend(json_string_array_value(reading, field));
    }
    unique_string_values(refs.into_iter())
}

fn representation_metric_family_status_v1(structural: &Value) -> String {
    let readings = structural["representationMetricReadings"]
        .as_array()
        .into_iter()
        .flatten()
        .collect::<Vec<_>>();
    if readings.is_empty() {
        return "blocked".to_string();
    }
    if readings.iter().any(|reading| {
        reading["analyticDistance"]["status"] == "boundedProxy"
            || representation_has_blocked_faithfulness(reading)
    }) {
        return "partial".to_string();
    }
    typed_family_status_from_array(structural, "representationMetricReadings")
}

fn architecture_distance_family_summaries_v1(
    architecture_distance: &Value,
    packet: &Value,
    emit_raw_artifacts: bool,
) -> Vec<Value> {
    packet["part4DistanceCoverageLedger"]
        .as_array()
        .into_iter()
        .flatten()
        .enumerate()
        .map(|(index, entry)| {
            let family = entry["distanceFamily"].as_str().unwrap_or("unknown");
            let measurement_status = entry["measurementStatus"].as_str().unwrap_or("unknown");
            let contribution =
                architecture_distance_measured_contribution(architecture_distance, family);
            let eligible_for_measured_total_scope = contribution.is_some();
            let actually_measured_contribution =
                eligible_for_measured_total_scope && measurement_status == "measured";
            let contribution_status = match (contribution, measurement_status) {
                (Some(_), "measured") => "measured-contribution".to_string(),
                (Some(0), "not-applicable") => {
                    "zero-contribution-not-applicable-not-measured-zero".to_string()
                }
                (Some(_), status) => format!("scoped-{status}-contribution"),
                (None, _) => "non-aggregated-canonical-family".to_string(),
            };
            let mut primary_refs = entry["primaryArtifactRefs"]
                .as_array()
                .cloned()
                .unwrap_or_default()
                .into_iter()
                .filter(|reference| {
                    emit_raw_artifacts
                        || reference
                            .as_str()
                            .is_some_and(|reference| !is_raw_only_artifact_ref(reference))
                })
                .collect::<Vec<_>>();
            let optional_raw_refs = entry["primaryArtifactRefs"]
                .as_array()
                .cloned()
                .unwrap_or_default()
                .into_iter()
                .filter(|reference| reference.as_str().is_some_and(is_raw_only_artifact_ref))
                .collect::<Vec<_>>();
            primary_refs.insert(
                0,
                json!(format!("architecture-distance.json#/familySummaries/{index}")),
            );
            json!({
                "familySummaryId": format!("architecture-distance-family:{family}"),
                "sourceLedgerRef": format!("packet:/part4DistanceCoverageLedger/{index}"),
                "ledgerEntryId": entry["ledgerEntryId"],
                "part4DefinitionRef": entry["part4DefinitionRef"],
                "definitionTitle": entry["definitionTitle"],
                "distanceFamily": family,
                "coverageStatus": entry["coverageStatus"],
                "measurementStatus": entry["measurementStatus"],
                "readingCount": entry["readingCount"],
                "measuredTotalContribution": contribution,
                "measuredTotalContributionStatus": contribution_status,
                "unit": if eligible_for_measured_total_scope {
                    json!("architecture-distance-point")
                } else {
                    Value::Null
                },
                "eligibleForMeasuredTotalScope": eligible_for_measured_total_scope,
                "actuallyMeasuredContribution": actually_measured_contribution,
                "includedInMeasuredTotal": eligible_for_measured_total_scope,
                "numericAggregationStatus": if actually_measured_contribution {
                    "measured-contribution-in-measuredTotal"
                } else if eligible_for_measured_total_scope {
                    "eligible-scope-without-measured-contribution"
                } else {
                    "non-aggregated-canonical-family"
                },
                "rawPacketRefs": entry["rawPacketRefs"],
                "primaryArtifactRefs": primary_refs,
                "optionalRawArtifactRefs": optional_raw_refs,
                "blockerRefs": entry["blockerRefs"],
                "evidenceBoundary": "family summary mirrors part4DistanceCoverageLedger and makes the measuredTotal aggregation scope explicit"
            })
        })
        .collect()
}

fn is_raw_only_artifact_ref(reference: &str) -> bool {
    reference.starts_with("archsig-analysis-packet.json#")
        || reference.starts_with("archsig-analysis-detail-index.json#")
        || reference.starts_with("llm-interpretation-packet.json#")
}

fn architecture_distance_measured_contribution(
    architecture_distance: &Value,
    family: &str,
) -> Option<i64> {
    let breakdown = &architecture_distance["summary"]["breakdown"];
    match family {
        "atomGeometry" => breakdown["atomGeometry"].as_i64(),
        "configurationGeometry" => breakdown["configuration"].as_i64(),
        "signatureGeometry" => breakdown["signature"].as_i64(),
        "operationGeometry" => breakdown["operation"].as_i64(),
        _ => None,
    }
}

fn architecture_distance_measurement_state_summary(family_summaries: &[Value]) -> Value {
    let expected = BTreeSet::from([
        "foundation",
        "atomGeometry",
        "configurationGeometry",
        "signatureGeometry",
        "operationGeometry",
        "curvatureGeometry",
        "homotopyFillingGeometry",
        "representationMetric",
        "measurementBoundary",
        "boundedDiagnosticConclusion",
    ]);
    let present = family_summaries
        .iter()
        .filter_map(|summary| summary["distanceFamily"].as_str())
        .collect::<BTreeSet<_>>();
    let missing = expected
        .iter()
        .filter(|family| !present.contains(**family))
        .copied()
        .collect::<Vec<_>>();
    let status_count = |status: &str| {
        family_summaries
            .iter()
            .filter(|summary| summary["measurementStatus"] == status)
            .count()
    };
    let blocked_count = status_count("blocked");
    let unmeasured_count = status_count("unmeasured");
    let partial_count = status_count("partial");
    let not_applicable_count = status_count("not-applicable");
    let missing_count = missing.len();
    let status = if missing_count > 0 {
        "missing-family"
    } else if blocked_count + unmeasured_count + partial_count > 0 {
        "partial"
    } else {
        "measured"
    };
    json!({
        "status": status,
        "expectedFamilyCount": expected.len(),
        "familyCount": family_summaries.len(),
        "missingCanonicalFamilyCount": missing_count,
        "missingCanonicalFamilies": missing,
        "measuredFamilyCount": status_count("measured"),
        "zeroFamilyCount": status_count("zero"),
        "blockedFamilyCount": blocked_count,
        "unmeasuredFamilyCount": unmeasured_count,
        "partialFamilyCount": partial_count,
        "notApplicableFamilyCount": not_applicable_count,
        "nonAggregatedFamilyCount": family_summaries
            .iter()
            .filter(|summary| summary["includedInMeasuredTotal"] == false)
            .count(),
        "evidenceBoundary": "measurementStateSummary counts canonical distance families; blocked or unmeasured families are explicit states, not measured zero"
    })
}

fn architecture_distance_measured_total_scope(family_summaries: &[Value]) -> Value {
    let included = family_summaries
        .iter()
        .filter(|summary| summary["includedInMeasuredTotal"] == true)
        .filter_map(|summary| summary["distanceFamily"].as_str())
        .collect::<Vec<_>>();
    let non_aggregated = family_summaries
        .iter()
        .filter(|summary| summary["includedInMeasuredTotal"] == false)
        .filter_map(|summary| summary["distanceFamily"].as_str())
        .collect::<Vec<_>>();
    json!({
        "scope": "aggregated architecture-distance-point families only",
        "includedFamilies": included,
        "nonAggregatedFamilies": non_aggregated,
        "reading": "measuredTotal is not the total of all canonical distance definitions; inspect familySummaries for every canonical family state"
    })
}

pub fn build_typed_analysis_summary_v1(
    normalized: &NormalizedArchMapV1,
    typed_results: &TypedEvaluatorResultsV1,
    architecture_distance: &Value,
) -> serde_json::Value {
    let replacement_blocked_count = typed_results.replacement_summary.blocked_count;
    let spectrum = architecture_spectrum_v1(normalized, typed_results);
    let homotopy = architecture_homotopy_v1(normalized, typed_results, &spectrum);
    let generated_obstructions = generated_obstructions_v1(typed_results);
    let generated_repair_targets = generated_repair_targets_v1(&generated_obstructions);
    let structural = architecture_structural_v1(
        normalized,
        typed_results,
        architecture_distance,
        &generated_obstructions,
        &generated_repair_targets,
        &spectrum,
        &homotopy,
    );
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
            "architectureSpectrumReport": "archsig-analysis-packet.json#/architectureSpectrumReport",
            "architectureHomotopyReport": "archsig-analysis-packet.json#/architectureHomotopyReport",
            "structuralReadingReviewSurface": "archsig-analysis-packet.json#/structuralReadingReviewSurface",
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
        "richDominantFindings": rich_dominant_findings_v1(&spectrum, &homotopy, &structural),
        "architectureSpectrumReport": spectrum["architectureSpectrumReport"],
        "architectureSpectrumSummary": architecture_spectrum_summary_v1(&spectrum),
        "architectureHomotopyReport": homotopy["architectureHomotopyReport"],
        "architectureHomotopySummary": architecture_homotopy_summary_v1(&homotopy),
        "structuralReadingReviewSurface": structural["structuralReadingReviewSurface"],
        "structuralReadingReviewSummary": structural_reading_review_summary_v1(&structural),
        "richPacketRefs": rich_packet_refs_v1(architecture_distance, &spectrum, &homotopy, &structural),
        "richReadingGuide": rich_reading_guide_v1(),
        "actionQueue": rich_action_queue_v1(typed_results, &spectrum, &homotopy, &structural),
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
            "architectureSpectrumReport": summary["architectureSpectrumReport"],
            "architectureHomotopyReport": summary["architectureHomotopyReport"],
            "structuralReadingReviewSurface": summary["structuralReadingReviewSurface"],
            "richPacketRefs": summary["richPacketRefs"],
            "richDominantFindings": summary["richDominantFindings"],
            "actionQueue": summary["actionQueue"]
        },
        "reportPane": {
            "conclusion": summary["conclusion"],
            "overview": {
                "summaryVerdict": summary["verdict"],
                "measurementStatusSummary": summary["measurementStatusSummary"]
            },
            "architectureDistance": summary["architectureDistance"],
            "architectureSpectrumReport": summary["architectureSpectrumReport"],
            "architectureSpectrumSummary": summary["architectureSpectrumSummary"],
            "architectureHomotopyReport": summary["architectureHomotopyReport"],
            "architectureHomotopySummary": summary["architectureHomotopySummary"],
            "structuralReadingReviewSurface": summary["structuralReadingReviewSurface"],
            "structuralReadingReviewSummary": summary["structuralReadingReviewSummary"],
            "richReadingGuide": summary["richReadingGuide"],
            "richPacketRefs": summary["richPacketRefs"],
            "richDominantFindings": summary["richDominantFindings"],
            "replacementRegistryResolution": summary["replacementRegistryResolution"],
            "typedEvaluatorDiagnosis": summary["typedEvaluatorDiagnosis"],
            "distanceDiagnosis": summary["distanceDiagnosis"],
            "topFindings": summary["dominantFindings"],
            "actionQueue": summary["actionQueue"],
            "omittedDetailCounts": {
                "rawPacketArrays": "omitted from viewer data; use richPacketRefs and optional raw artifacts",
                "typedEvaluatorResultRows": typed_results.results.len(),
                "replacementEvaluatorResultRows": typed_results.replacement_evaluator_results.len(),
                "atomNodes": atom_nodes.len(),
                "moleculeGroups": molecule_groups.len()
            },
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
            detail_index_section_v1("part4DistanceCoverageLedger", "/part4DistanceCoverageLedger", packet_array_len(packet, "part4DistanceCoverageLedger")),
            detail_index_section_v1("generatedLawInputs", "/generatedLawInputs", packet_array_len(packet, "generatedLawInputs")),
            detail_index_section_v1("signatureAxes", "/signatureAxes", packet_array_len(packet, "signatureAxes")),
            detail_index_section_v1("generatedObstructions", "/generatedObstructions", packet_array_len(packet, "generatedObstructions")),
            detail_index_section_v1("generatedRepairTargets", "/generatedRepairTargets", packet_array_len(packet, "generatedRepairTargets")),
            detail_index_section_v1("curvatureSupportReadings", "/curvatureSupportReadings", packet_array_len(packet, "curvatureSupportReadings")),
            detail_index_section_v1("curvatureTransferReadings", "/curvatureTransferReadings", packet_array_len(packet, "curvatureTransferReadings")),
            detail_index_section_v1("curvatureMassReadings", "/curvatureMassReadings", packet_array_len(packet, "curvatureMassReadings")),
            detail_index_section_v1("spectralAnalysisReadings", "/spectralAnalysisReadings", packet_array_len(packet, "spectralAnalysisReadings")),
            detail_index_section_v1("spectralModeReadings", "/spectralModeReadings", packet_array_len(packet, "spectralModeReadings")),
            detail_index_section_v1("spectralDrilldownReadings", "/spectralDrilldownReadings", packet_array_len(packet, "spectralDrilldownReadings")),
            detail_index_section_v1("architectureSpectrumReport.topHotspots", "/architectureSpectrumReport/topHotspots", packet_nested_array_len(packet, &["architectureSpectrumReport", "topHotspots"])),
            detail_index_section_v1("architectureSpectrumReport.recurrentObstructions", "/architectureSpectrumReport/recurrentObstructions", packet_nested_array_len(packet, &["architectureSpectrumReport", "recurrentObstructions"])),
            detail_index_section_v1("pathHomotopyDiagramReadings", "/pathHomotopyDiagramReadings", packet_array_len(packet, "pathHomotopyDiagramReadings")),
            detail_index_section_v1("homotopyHolonomyReadings", "/homotopyHolonomyReadings", packet_array_len(packet, "homotopyHolonomyReadings")),
            detail_index_section_v1("stokesStyleReadings", "/stokesStyleReadings", packet_array_len(packet, "stokesStyleReadings")),
            detail_index_section_v1("homotopyDistanceReadings", "/homotopyDistanceReadings", packet_array_len(packet, "homotopyDistanceReadings")),
            detail_index_section_v1("architectureHomotopyReport.filledLoops", "/architectureHomotopyReport/filledLoops", packet_nested_array_len(packet, &["architectureHomotopyReport", "filledLoops"])),
            detail_index_section_v1("architectureHomotopyReport.unfilledLoops", "/architectureHomotopyReport/unfilledLoops", packet_nested_array_len(packet, &["architectureHomotopyReport", "unfilledLoops"])),
            detail_index_section_v1("architectureHomotopyReport.nonzeroHolonomyLoops", "/architectureHomotopyReport/nonzeroHolonomyLoops", packet_nested_array_len(packet, &["architectureHomotopyReport", "nonzeroHolonomyLoops"])),
            detail_index_section_v1("representationMetricReadings", "/representationMetricReadings", packet_array_len(packet, "representationMetricReadings")),
            detail_index_section_v1("localCurvatureDiagramReadings", "/localCurvatureDiagramReadings", packet_array_len(packet, "localCurvatureDiagramReadings")),
            detail_index_section_v1("threeLayerFlatnessReadings", "/threeLayerFlatnessReadings", packet_array_len(packet, "threeLayerFlatnessReadings")),
            detail_index_section_v1("observationProjectionReadings", "/observationProjectionReadings", packet_array_len(packet, "observationProjectionReadings")),
            detail_index_section_v1("stateTransitionAlgebraReadings", "/stateTransitionAlgebraReadings", packet_array_len(packet, "stateTransitionAlgebraReadings")),
            detail_index_section_v1("effectRelationAlgebraReadings", "/effectRelationAlgebraReadings", packet_array_len(packet, "effectRelationAlgebraReadings")),
            detail_index_section_v1("synthesisBlockageReadings", "/synthesisBlockageReadings", packet_array_len(packet, "synthesisBlockageReadings")),
            detail_index_section_v1("operationPreconditionReadinessReadings", "/operationPreconditionReadinessReadings", packet_array_len(packet, "operationPreconditionReadinessReadings")),
            detail_index_section_v1("pathMultiplicityLossReadings", "/pathMultiplicityLossReadings", packet_array_len(packet, "pathMultiplicityLossReadings")),
            detail_index_section_v1("structuralReadingReviewSurface.connectedReadingRefs", "/structuralReadingReviewSurface/connectedReadingRefs", packet_nested_array_len(packet, &["structuralReadingReviewSurface", "connectedReadingRefs"])),
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
    normalized: &NormalizedArchMapV1,
    typed_results: &TypedEvaluatorResultsV1,
    architecture_distance: &Value,
) -> serde_json::Value {
    let spectrum = architecture_spectrum_v1(normalized, typed_results);
    let homotopy = architecture_homotopy_v1(normalized, typed_results, &spectrum);
    let generated_obstructions = generated_obstructions_v1(typed_results);
    let generated_repair_targets = generated_repair_targets_v1(&generated_obstructions);
    let structural = architecture_structural_v1(
        normalized,
        typed_results,
        architecture_distance,
        &generated_obstructions,
        &generated_repair_targets,
        &spectrum,
        &homotopy,
    );
    json!({
        "schema": "llm-interpretation-packet/v1",
        "interpretationKind": "typed-evaluator-bounded-reading",
        "primaryConclusion": typed_conclusion(typed_results, architecture_distance),
        "typedEvaluatorDiagnosis": typed_evaluator_diagnosis(typed_results),
        "architectureDistance": architecture_distance["summary"],
        "distanceDiagnosisSummary": architecture_distance["distanceDiagnosis"],
        "architectureSpectrumReportSummary": architecture_spectrum_summary_v1(&spectrum),
        "architectureHomotopyReportSummary": architecture_homotopy_summary_v1(&homotopy),
        "structuralReadingReviewSummary": structural_reading_review_summary_v1(&structural),
        "richPacketRefs": rich_packet_refs_v1(architecture_distance, &spectrum, &homotopy, &structural),
        "readingGuidance": rich_reading_guide_v1(),
        "actionQueueSummary": rich_action_queue_summary_v1(typed_results, &spectrum, &homotopy, &structural),
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
    let operation_distance_readings = architecture_operation_distance_readings(
        typed_results,
        profile,
        &signature_distance_readings,
    );
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
    let atom_configuration_insights = atom_configuration_primary_insights(
        &atom_distance_readings,
        &configuration_distance_readings,
    );
    let operation_insights = operation_primary_insights(&operation_distance_readings);
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
                "domain.no-direct-infra-dependency": profile.infrastructure_dependency_operation_cost
            },
            "operationCostFallbackPolicy": "blockedWhenOperationCostMissing"
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
            "topMovedAtomPairs": atom_configuration_insights["topMovedAtomPairs"].clone(),
            "topMovedMolecules": atom_configuration_insights["topMovedMolecules"].clone(),
            "atomConfigurationInsights": atom_configuration_insights.clone(),
            "operationInsights": operation_insights.clone(),
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
        "atomConfigurationInsights": atom_configuration_insights,
        "operationInsights": operation_insights,
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
    let architecture_distance_bundle_pass = architecture_distance_bundle_matches_packet(packet);
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
                    "architectureSpectrumReport",
                    "curvatureSupportReadings",
                    "curvatureTransferReadings",
                    "curvatureMassReadings",
                    "spectralAnalysisReadings",
                    "spectralModeReadings",
                    "spectralDrilldownReadings",
                    "architectureHomotopyReport",
                    "pathHomotopyDiagramReadings",
                    "homotopyHolonomyReadings",
                    "stokesStyleReadings",
                    "homotopyDistanceReadings",
                    "structuralReadingReviewSurface",
                    "representationMetricReadings",
                    "localCurvatureDiagramReadings",
                    "threeLayerFlatnessReadings",
                    "observationProjectionReadings",
                    "stateTransitionAlgebraReadings",
                    "effectRelationAlgebraReadings",
                    "synthesisBlockageReadings",
                    "operationPreconditionReadinessReadings",
                    "pathMultiplicityLossReadings",
                    "typedEvaluatorResults",
                    "architectureDistanceSignatureReadings",
                    "part4DistanceCoverageLedger",
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
        "spectrumMeasurementProfile",
        "homotopyMeasurementProfile",
        "concernHints",
        "observationGaps",
    ]
    .iter()
    .all(|field| packet.get(*field).is_none());
    let architecture_spectrum_report_pass = architecture_spectrum_report_valid(packet);
    let architecture_homotopy_report_pass = architecture_homotopy_report_valid(packet);
    let structural_reading_review_surface_pass = structural_reading_review_surface_valid(packet);
    let checks_pass = [
        packet_schema_pass,
        typed_count_pass,
        architecture_distance_pass,
        distance_diagnosis_pass,
        profile_ref_pass,
        breakdown_sum_pass,
        reading_counts_pass,
        architecture_distance_bundle_pass,
        replacement_registry_present_pass,
        replacement_results_match_pass,
        replacement_output_refs_pass,
        generated_law_inputs_pass,
        signature_axes_pass,
        generated_obstructions_pass,
        generated_repair_targets_pass,
        generated_packet_refs_pass,
        removed_v0_input_fields_absent_pass,
        architecture_spectrum_report_pass,
        architecture_homotopy_report_pass,
        structural_reading_review_surface_pass,
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
                "checkId": "archsig.v1.architectureDistanceCanonicalBundle",
                "result": if architecture_distance_bundle_pass { "pass" } else { "fail" },
                "message": "architecture-distance familySummaries mirror the raw packet distance coverage ledger and expose measuredTotal scope"
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
            },
            {
                "checkId": "archsig.v1.architectureSpectrumReportSurface",
                "result": if architecture_spectrum_report_pass { "pass" } else { "fail" },
                "message": "ArchitectureSpectrumReport resolves curvature support, transfer, hotspot, recurrent obstruction, and coverage refs"
            },
            {
                "checkId": "archsig.v1.architectureHomotopyReportSurface",
                "result": if architecture_homotopy_report_pass { "pass" } else { "fail" },
                "message": "ArchitectureHomotopyReport resolves path, loop, filler, holonomy, Stokes, and missing filler refs without treating gaps as zero"
            },
            {
                "checkId": "archsig.v1.structuralReadingReviewSurface",
                "result": if structural_reading_review_surface_pass { "pass" } else { "fail" },
                "message": "structural reading review surface resolves v1 structural readings to typed evaluator, generated packet, and normalized support refs"
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

fn architecture_spectrum_report_valid(packet: &Value) -> bool {
    let report = &packet["architectureSpectrumReport"];
    if !report.is_object()
        || report["reportId"].as_str().is_none()
        || report["profileRef"].as_str().is_none()
        || report["measuredBoundary"].as_str().is_none()
        || !report["nonConclusions"]
            .as_array()
            .is_some_and(|items| !items.is_empty())
    {
        return false;
    }
    let Some(supports) = packet["curvatureSupportReadings"].as_array() else {
        return false;
    };
    if supports.is_empty() {
        return false;
    }
    if !supports.iter().enumerate().all(|(index, reading)| {
        reading["typedEvaluatorResultRef"]
            .as_str()
            .is_some_and(|reference| packet.pointer(reference).is_some())
            && reading["supportRefs"].is_array()
            && reading["witnessRefs"].is_array()
            && reading["curvatureValue"]["status"].as_str().is_some()
            && (reading["curvatureValue"]["status"] != "blockedByCoverageGap"
                || reading["coverageGapRefs"]
                    .as_array()
                    .is_some_and(|refs| !refs.is_empty()))
            && report["topHotspots"].as_array().is_some_and(|hotspots| {
                hotspots.iter().any(|hotspot| {
                    hotspot["supportReadingRef"] == format!("/curvatureSupportReadings/{index}")
                        && hotspot["supportRefs"] == reading["supportRefs"]
                        && hotspot["witnessRefs"] == reading["witnessRefs"]
                        && hotspot["coverageGapRefs"] == reading["coverageGapRefs"]
                })
            })
    }) {
        return false;
    }
    if !packet["curvatureTransferReadings"]
        .as_array()
        .is_some_and(|items| {
            items.iter().all(|reading| {
                let row_count = reading["transferOperator"]["rowCount"]
                    .as_u64()
                    .unwrap_or_default();
                let column_count = reading["transferOperator"]["columnCount"]
                    .as_u64()
                    .unwrap_or_default();
                reading["transferOperator"].is_object()
                    && row_count == supports.len() as u64
                    && column_count == supports.len() as u64
                    && reading["transferOperator"]["sparseEntries"]
                        .as_array()
                        .is_some_and(|entries| {
                            entries.iter().all(|entry| {
                                entry["row"].as_u64().is_some_and(|row| row < row_count)
                                    && entry["column"]
                                        .as_u64()
                                        .is_some_and(|column| column < column_count)
                                    && entry["weight"].as_i64().is_some()
                            })
                        })
                    && reading["transferEdges"].as_array().is_some_and(|edges| {
                        edges.iter().all(|edge| {
                            edge["supportIndex"]
                                .as_u64()
                                .is_some_and(|index| index < supports.len() as u64)
                                && packet_ref_field_resolves(packet, edge, "fromSupportRef")
                                && packet_ref_field_resolves(packet, edge, "toSupportRef")
                                && edge["weight"].as_i64().is_some()
                        })
                    })
                    && reading["recurrentObstructionModes"]
                        .as_array()
                        .is_some_and(|modes| {
                            modes.iter().all(|mode| {
                                packet_ref_array_field_resolves(packet, mode, "transferEdgeRefs")
                            })
                        })
            })
        })
    {
        return false;
    }
    if !packet["curvatureMassReadings"]
        .as_array()
        .is_some_and(|items| {
            !items.is_empty()
                && items
                    .iter()
                    .all(|item| packet_ref_array_field_resolves(packet, item, "supportReadingRefs"))
        })
    {
        return false;
    }
    if !packet["spectralAnalysisReadings"]
        .as_array()
        .is_some_and(|items| {
            !items.is_empty()
                && items
                    .iter()
                    .all(|item| packet_ref_array_field_resolves(packet, item, "supportReadingRefs"))
        })
    {
        return false;
    }
    if !packet["spectralModeReadings"]
        .as_array()
        .is_some_and(|items| {
            !items.is_empty()
                && items
                    .iter()
                    .all(|item| packet_ref_field_resolves(packet, item, "supportReadingRef"))
        })
    {
        return false;
    }
    if !packet["spectralDrilldownReadings"]
        .as_array()
        .is_some_and(|items| {
            !items.is_empty()
                && items.iter().all(|item| {
                    packet_ref_field_resolves(packet, item, "supportReadingRef")
                        && packet_ref_array_field_resolves(packet, item, "transferReadingRefs")
                })
        })
    {
        return false;
    }
    if !packet_ref_array_field_resolves(packet, report, "curvatureMassReadingRefs") {
        return false;
    }
    if !report["topEigenmodes"].as_array().is_some_and(|items| {
        !items.is_empty()
            && items
                .iter()
                .all(|item| packet_ref_field_resolves(packet, item, "supportReadingRef"))
    }) {
        return false;
    }
    if !report["topWitnessClusters"]
        .as_array()
        .is_some_and(|items| {
            !items.is_empty()
                && items
                    .iter()
                    .all(|item| packet_ref_array_field_resolves(packet, item, "transferEdgeRefs"))
        })
    {
        return false;
    }
    let coverage_gaps = report["coverageGaps"]
        .as_array()
        .into_iter()
        .flatten()
        .filter_map(|item| item.as_str())
        .collect::<BTreeSet<_>>();
    let support_coverage_gaps = supports
        .iter()
        .flat_map(|reading| {
            reading["coverageGapRefs"]
                .as_array()
                .into_iter()
                .flatten()
                .filter_map(|item| item.as_str())
        })
        .collect::<BTreeSet<_>>();
    coverage_gaps == support_coverage_gaps
}

fn architecture_homotopy_report_valid(packet: &Value) -> bool {
    let report = &packet["architectureHomotopyReport"];
    if !report.is_object()
        || report["schemaVersion"] != "architecture-homotopy-report/v1"
        || report["reportId"].as_str().is_none()
        || !report["nonConclusions"]
            .as_array()
            .is_some_and(|items| !items.is_empty())
    {
        return false;
    }
    if !packet["pathHomotopyDiagramReadings"]
        .as_array()
        .is_some_and(|items| {
            items.iter().all(|item| {
                let support_atom_refs = json_string_array_value(item, "supportAtomRefs")
                    .into_iter()
                    .collect::<BTreeSet<_>>();
                item["supportAtomRefs"].as_array().is_some()
                    && item["selectedAxes"].as_array().is_some()
                    && item["pathPairRefs"].as_array().is_some_and(|pairs| {
                        pairs.iter().all(|pair| {
                            pair["fromAtomRef"]
                                .as_str()
                                .is_some_and(|reference| support_atom_refs.contains(reference))
                                && pair["toAtomRef"]
                                    .as_str()
                                    .is_some_and(|reference| support_atom_refs.contains(reference))
                        })
                    })
                    && item["fillerStatus"].as_str().is_some_and(|status| {
                        status == "measuredFiller" || status == "missingFillerEvidence"
                    })
                    && (item["fillerStatus"] != "missingFillerEvidence"
                        || item["coverageGapRefs"]
                            .as_array()
                            .is_some_and(|refs| !refs.is_empty()))
            })
        })
    {
        return false;
    }
    if !packet["homotopyHolonomyReadings"]
        .as_array()
        .is_some_and(|items| {
            items.iter().all(|item| {
                packet_ref_field_resolves(packet, item, "pathHomotopyDiagramRef")
                    && packet_ref_array_field_resolves(packet, item, "nonzeroCurvatureSupportRefs")
                    && item["holonomyStatus"].as_str().is_some_and(|status| {
                        status == "measuredZero"
                            || status == "measuredNonzero"
                            || status == "blockedByMissingFiller"
                            || status == "unmeasuredSelectedAxisDifference"
                    })
                    && if item["holonomyStatus"] == "blockedByMissingFiller"
                        || item["holonomyStatus"] == "unmeasuredSelectedAxisDifference"
                    {
                        item["holonomyValue"].is_null()
                            && item["coverageGapRefs"]
                                .as_array()
                                .is_some_and(|refs| !refs.is_empty())
                    } else {
                        item["holonomyValue"].as_i64().is_some()
                    }
            })
        })
    {
        return false;
    }
    if !packet["stokesStyleReadings"]
        .as_array()
        .is_some_and(|items| {
            items.iter().all(|item| {
                packet_ref_field_resolves(packet, item, "pathHomotopyDiagramRef")
                    && packet_ref_field_resolves(packet, item, "holonomyReadingRef")
                    && item["localCurvatureCells"].as_array().is_some()
                    && if item["stokesStatus"] == "blockedByMissingFiller"
                        || item["stokesStatus"] == "blockedByCoverageGap"
                    {
                        item["localCurvatureCells"]
                            .as_array()
                            .is_some_and(Vec::is_empty)
                            && item["coverageGapRefs"]
                                .as_array()
                                .is_some_and(|refs| !refs.is_empty())
                    } else {
                        item["coverageGapRefs"].as_array().is_some()
                    }
            })
        })
    {
        return false;
    }
    if !packet["homotopyDistanceReadings"]
        .as_array()
        .is_some_and(|items| {
            items.iter().all(|item| {
                packet_ref_field_resolves(packet, item, "pathHomotopyDiagramRef")
                    && packet_ref_field_resolves(packet, item, "holonomyReadingRef")
                    && if item["measurementStatus"] == "blockedByMissingFiller"
                        || item["measurementStatus"] == "blockedByCoverageGap"
                    {
                        item["homotopyDistance"].is_null()
                            && item["fillingCost"].is_null()
                            && item["observationGapLowerBound"]
                                .as_i64()
                                .is_some_and(|value| value > 0)
                    } else {
                        item["homotopyDistance"].as_i64().is_some()
                            && item["fillingCost"].as_u64().is_some()
                    }
            })
        })
    {
        return false;
    }
    for field in [
        "pathHomotopyDiagramReadingRefs",
        "homotopyHolonomyReadingRefs",
        "stokesStyleReadingRefs",
        "homotopyDistanceReadingRefs",
    ] {
        if !packet_ref_array_field_resolves(packet, report, field) {
            return false;
        }
    }
    if !report["filledLoops"].as_array().is_some_and(|items| {
        items.iter().all(|item| {
            packet_ref_field_resolves(packet, item, "pathHomotopyDiagramRef")
                && packet_ref_field_resolves(packet, item, "holonomyReadingRef")
                && packet_ref_field_resolves(packet, item, "stokesReadingRef")
                && packet_ref_field_resolves(packet, item, "homotopyDistanceReadingRef")
                && item["loopStatus"] == "filled"
        })
    }) {
        return false;
    }
    if !report["unfilledLoops"].as_array().is_some_and(|items| {
        items.iter().all(|item| {
            packet_ref_field_resolves(packet, item, "pathHomotopyDiagramRef")
                && packet_ref_field_resolves(packet, item, "holonomyReadingRef")
                && packet_ref_field_resolves(packet, item, "stokesReadingRef")
                && packet_ref_field_resolves(packet, item, "homotopyDistanceReadingRef")
                && packet_ref_field_resolves(packet, item, "missingFillerEvidenceRef")
                && item["loopStatus"] == "unfilled"
        })
    }) {
        return false;
    }
    if !report["nonzeroHolonomyLoops"]
        .as_array()
        .is_some_and(|items| {
            items.iter().all(|item| {
                item["holonomyReadingRef"]
                    .as_str()
                    .and_then(|reference| packet.pointer(reference))
                    .is_some_and(|reading| reading["holonomyStatus"] == "measuredNonzero")
            })
        })
    {
        return false;
    }
    if !report["topLocalCurvatureCells"]
        .as_array()
        .is_some_and(|items| {
            items.iter().all(|item| {
                packet_ref_field_resolves(packet, item, "stokesReadingRef")
                    && packet_ref_field_resolves(packet, item, "localCurvatureCellRef")
            })
        })
    {
        return false;
    }
    if !report["missingFillerEvidence"]
        .as_array()
        .is_some_and(|items| {
            items.iter().all(|item| {
                packet_ref_field_resolves(packet, item, "pathHomotopyDiagramRef")
                    && packet_ref_field_resolves(packet, item, "holonomyReadingRef")
                    && item["gapRef"].as_str().is_some()
            })
        })
    {
        return false;
    }
    if !report["architecturalHoleReadings"]
        .as_array()
        .is_some_and(|items| {
            items.iter().all(|item| {
                packet_ref_field_resolves(packet, item, "missingFillerEvidenceRef")
                    && item["gapRef"].as_str().is_some()
            })
        })
    {
        return false;
    }
    if report["spectrumContextRef"] != "archsig-analysis-packet.json#/architectureSpectrumReport"
        || !packet_ref_array_field_resolves(packet, report, "nonzeroCurvatureSupportRefs")
    {
        return false;
    }
    let coverage_gaps = report["coverageGaps"]
        .as_array()
        .into_iter()
        .flatten()
        .filter_map(|item| item.as_str())
        .collect::<BTreeSet<_>>();
    let expected_gaps = report["missingFillerEvidence"]
        .as_array()
        .into_iter()
        .flatten()
        .filter_map(|item| item["gapRef"].as_str())
        .chain(
            packet["homotopyHolonomyReadings"]
                .as_array()
                .into_iter()
                .flatten()
                .flat_map(|reading| {
                    reading["coverageGapRefs"]
                        .as_array()
                        .into_iter()
                        .flatten()
                        .filter_map(|item| item.as_str())
                }),
        )
        .collect::<BTreeSet<_>>();
    coverage_gaps == expected_gaps
}

fn structural_reading_review_surface_valid(packet: &Value) -> bool {
    let surface = &packet["structuralReadingReviewSurface"];
    if !surface.is_object()
        || surface["schemaVersion"] != "structural-reading-review-surface/v1"
        || !surface["currentStateReading"]
            .as_str()
            .is_some_and(|reading| reading.contains("current architecture state"))
        || !surface["reviewFocus"]
            .as_array()
            .is_some_and(|items| !items.is_empty())
        || !surface["nonConclusions"]
            .as_array()
            .is_some_and(|items| !items.is_empty())
    {
        return false;
    }
    let structural_fields = [
        "representationMetricReadings",
        "localCurvatureDiagramReadings",
        "threeLayerFlatnessReadings",
        "observationProjectionReadings",
        "stateTransitionAlgebraReadings",
        "effectRelationAlgebraReadings",
        "synthesisBlockageReadings",
        "operationPreconditionReadinessReadings",
        "pathMultiplicityLossReadings",
    ];
    if !structural_fields.iter().all(|field| {
        packet[*field].as_array().is_some_and(|readings| {
            !readings.is_empty()
                && readings.iter().all(|reading| {
                    reading["readingId"].as_str().is_some()
                        && reading["measurementStatus"]
                            .as_str()
                            .is_some_and(|status| status != "measuredZero")
                        && reading["normalizedAtomRefs"].as_array().is_some()
                        && reading["normalizedMoleculeRefs"].as_array().is_some()
                        && reading["coverageGapRefs"].as_array().is_some()
                        && reading["typedEvaluatorResultRefs"]
                            .as_array()
                            .is_some_and(|refs| {
                                !refs.is_empty()
                                    && refs.iter().all(|reference| {
                                        reference.as_str().is_some_and(|pointer| {
                                            packet.pointer(pointer).is_some()
                                        })
                                    })
                            })
                        && (!reading["measurementStatus"]
                            .as_str()
                            .is_some_and(|status| status == "measured")
                            || !structural_reading_has_gap(reading))
                })
        })
    }) {
        return false;
    }
    let expected_connected_reading_refs = expected_structural_connected_reading_refs(packet);
    if expected_connected_reading_refs.is_empty() {
        return false;
    }
    if !surface["connectedReadingRefs"]
        .as_array()
        .is_some_and(|refs| {
            refs.len() == expected_connected_reading_refs.len()
                && refs.iter().zip(expected_connected_reading_refs.iter()).all(
                    |(reference, expected)| {
                        reference.as_str().is_some_and(|pointer| {
                            pointer == expected && packet.pointer(pointer).is_some()
                        })
                    },
                )
        })
    {
        return false;
    }
    surface["typedEvaluatorResultRefs"]
        .as_array()
        .is_some_and(|refs| {
            !refs.is_empty()
                && refs.iter().all(|reference| {
                    reference
                        .as_str()
                        .is_some_and(|pointer| packet.pointer(pointer).is_some())
                })
        })
}

fn expected_structural_connected_reading_refs(packet: &Value) -> Vec<String> {
    [
        "representationMetricReadings",
        "localCurvatureDiagramReadings",
        "threeLayerFlatnessReadings",
        "observationProjectionReadings",
        "stateTransitionAlgebraReadings",
        "effectRelationAlgebraReadings",
        "synthesisBlockageReadings",
        "operationPreconditionReadinessReadings",
        "pathMultiplicityLossReadings",
    ]
    .iter()
    .flat_map(|field| {
        packet[*field]
            .as_array()
            .into_iter()
            .flat_map(move |readings| {
                (0..readings.len()).map(move |index| format!("/{field}/{index}"))
            })
    })
    .collect()
}

fn structural_reading_is_measured(reading: &Value) -> bool {
    reading["measurementStatus"] == "measured"
        && reading["coverageGapRefs"]
            .as_array()
            .is_some_and(|refs| refs.is_empty())
        && reading["typedEvaluatorResultRefs"]
            .as_array()
            .is_some_and(|refs| !refs.is_empty())
}

fn structural_reading_has_gap(reading: &Value) -> bool {
    reading["coverageGapRefs"]
        .as_array()
        .is_none_or(|refs| !refs.is_empty())
        || reading["typedEvaluatorResultRefs"]
            .as_array()
            .is_none_or(|refs| refs.is_empty())
}

fn packet_ref_field_resolves(packet: &Value, item: &Value, field: &str) -> bool {
    item[field]
        .as_str()
        .is_some_and(|packet_ref| packet.pointer(packet_ref).is_some())
}

fn packet_ref_array_field_resolves(packet: &Value, item: &Value, field: &str) -> bool {
    item[field].as_array().is_some_and(|refs| {
        refs.iter().all(|reference| {
            reference
                .as_str()
                .is_some_and(|pointer| packet.pointer(pointer).is_some())
        })
    })
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

fn architecture_spectrum_v1(
    normalized: &NormalizedArchMapV1,
    typed_results: &TypedEvaluatorResultsV1,
) -> Value {
    let curvature_support_readings = curvature_support_readings_v1(typed_results);
    let curvature_transfer_readings = curvature_transfer_readings_v1(&curvature_support_readings);
    let curvature_mass_readings = curvature_mass_readings_v1(&curvature_support_readings);
    let spectral_analysis_readings =
        spectral_analysis_readings_v1(normalized, &curvature_support_readings);
    let spectral_mode_readings = spectral_mode_readings_v1(&curvature_support_readings);
    let spectral_drilldown_readings =
        spectral_drilldown_readings_v1(&curvature_support_readings, &curvature_transfer_readings);
    let architecture_spectrum_report = architecture_spectrum_report_v1(
        normalized,
        &curvature_support_readings,
        &curvature_transfer_readings,
        &curvature_mass_readings,
    );
    json!({
        "curvatureSupportReadings": curvature_support_readings,
        "curvatureTransferReadings": curvature_transfer_readings,
        "curvatureMassReadings": curvature_mass_readings,
        "spectralAnalysisReadings": spectral_analysis_readings,
        "spectralModeReadings": spectral_mode_readings,
        "spectralDrilldownReadings": spectral_drilldown_readings,
        "architectureSpectrumReport": architecture_spectrum_report
    })
}

fn curvature_support_readings_v1(typed_results: &TypedEvaluatorResultsV1) -> Vec<Value> {
    typed_results
        .results
        .iter()
        .enumerate()
        .map(|(index, result)| {
            let axis_ref = signature_axis_id(&result.law);
            let measurement_status = spectrum_measurement_status(result);
            let curvature_value = if result.status == "measuredViolation" {
                Some(1)
            } else if result.status == "measuredPass" {
                Some(0)
            } else {
                None
            };
            let coverage_gap_refs = if curvature_value.is_some() {
                Vec::new()
            } else {
                vec![format!(
                    "coverage-gap:{}:{}",
                    stable_ref(&result.law),
                    stable_ref(result.blocker_reason.as_deref().unwrap_or("missing-support"))
                )]
            };
            json!({
                "readingId": format!("curvature-support:{}", stable_ref(&result.law)),
                "profileRef": "spectrum-profile:v1-typed-evaluator@1",
                "typedEvaluatorResultRef": typed_evaluator_result_ref(index),
                "law": result.law,
                "evaluator": result.evaluator,
                "axisRef": axis_ref,
                "measurementStatus": measurement_status,
                "curvatureValue": {
                    "status": if let Some(value) = curvature_value {
                        if value == 0 { "measuredZero" } else { "measuredNonzero" }
                    } else {
                        "blockedByCoverageGap"
                    },
                    "value": curvature_value,
                    "unit": "selected-axis-curvature"
                },
                "weight": if result.status == "measuredViolation" { 1 } else { 0 },
                "supportRefs": result.detail_refs,
                "witnessRefs": result.support_atom_refs,
                "moleculeRefs": result.support_molecule_refs,
                "sourceRefs": result.detail_refs,
                "coverageGapRefs": coverage_gap_refs,
                "basisRefs": result.basis_refs,
                "registryBasisRefs": registry_basis_refs(result),
                "readingBoundary": {
                    "basis": "typed evaluator status over normalized ArchMap support",
                    "zeroBoundary": "measured zero only means no selected measured violation for this evaluator under present support",
                    "blockedBoundary": "blocked / unknown / unmeasured evaluator statuses are coverage gaps, not zero curvature"
                },
                "nonConclusions": [
                    "curvatureSupportReadings/v1 is a bounded ArchSig diagnostic, not a Lean theorem discharge",
                    "zero curvature support does not prove global lawfulness, flatness, or source-observation completeness"
                ]
            })
        })
        .collect()
}

fn curvature_transfer_readings_v1(curvature_support_readings: &[Value]) -> Vec<Value> {
    let transfer_edges = curvature_support_readings
        .iter()
        .enumerate()
        .flat_map(|(index, reading)| {
            let reading_ref = format!("/curvatureSupportReadings/{index}");
            let mut edges = Vec::new();
            if reading["curvatureValue"]["status"] == "measuredNonzero"
                || reading["curvatureValue"]["status"] == "blockedByCoverageGap"
            {
                edges.push(json!({
                    "edgeId": format!(
                        "curvature-transfer-edge:{}",
                        stable_ref(reading["law"].as_str().unwrap_or("selected-law"))
                    ),
                    "edgeKind": "selfRecurrentSupport",
                    "supportIndex": index,
                    "fromSupportRef": reading_ref,
                    "toSupportRef": reading_ref,
                    "weight": if reading["curvatureValue"]["status"] == "measuredNonzero" { 1 } else { 0 },
                    "coverageStatus": if reading["curvatureValue"]["status"] == "blockedByCoverageGap" {
                        "blockedByCoverageGap"
                    } else {
                        "measured"
                    },
                    "supportRefs": reading["supportRefs"],
                    "witnessRefs": reading["witnessRefs"],
                    "coverageGapRefs": reading["coverageGapRefs"]
                }));
            }
            edges
        })
        .collect::<Vec<_>>();
    let recurrent_modes = transfer_edges
        .iter()
        .enumerate()
        .map(|(index, edge)| {
            json!({
                "modeId": format!("recurrent-obstruction-mode:{index}"),
                "recurrenceKind": edge["edgeKind"],
                "spectralRadiusReading": if edge["coverageStatus"] == "blockedByCoverageGap" {
                    "blocked by coverage gap; no zero spectrum conclusion"
                } else {
                    "bounded self recurrence over measured nonzero support"
                },
                "transferEdgeRefs": [format!("/curvatureTransferReadings/0/transferEdges/{index}")],
                "supportRefs": edge["supportRefs"],
                "witnessRefs": edge["witnessRefs"],
                "coverageGapRefs": edge["coverageGapRefs"],
                "reading": "current-state recurrent support reading; not empirical amplification"
            })
        })
        .collect::<Vec<_>>();
    let sparse_entries = transfer_edges
        .iter()
        .map(|edge| {
            let support_index = edge["supportIndex"].as_u64().unwrap_or_default();
            json!({
                "row": support_index,
                "column": support_index,
                "weight": edge["weight"]
            })
        })
        .collect::<Vec<_>>();
    vec![json!({
        "readingId": "curvature-transfer:v1-typed-evaluator",
        "profileRef": "spectrum-profile:v1-typed-evaluator@1",
        "transferOperator": {
            "operatorKind": "finite-nonnegative-support-transfer",
            "rowCount": curvature_support_readings.len(),
            "columnCount": curvature_support_readings.len(),
            "sparseEntries": sparse_entries,
            "spectralRadiusKind": if transfer_edges.iter().any(|edge| edge["coverageStatus"] == "blockedByCoverageGap") {
                "blockedByCoverageGap"
            } else if transfer_edges.is_empty() {
                "measuredZeroWithinSelectedSupport"
            } else {
                "boundedNonzero"
            }
        },
        "transferEdges": transfer_edges,
        "recurrentObstructionModes": recurrent_modes,
        "measuredBoundary": "transfer spectrum is finite and bounded to selected typed evaluator support rows",
        "nonConclusions": [
            "curvatureTransferReadings/v1 does not predict future incidents or empirical amplification",
            "missing transfer support blocks zero reflection rather than becoming measured zero"
        ]
    })]
}

fn curvature_mass_readings_v1(curvature_support_readings: &[Value]) -> Vec<Value> {
    let measured_nonzero = curvature_support_readings
        .iter()
        .filter(|reading| reading["curvatureValue"]["status"] == "measuredNonzero")
        .count();
    let blocked = curvature_support_readings
        .iter()
        .filter(|reading| reading["curvatureValue"]["status"] == "blockedByCoverageGap")
        .count();
    vec![json!({
        "curvatureMassReadingId": "curvature-mass:v1-typed-evaluator",
        "profileRef": "spectrum-profile:v1-typed-evaluator@1",
        "measurementStatus": if blocked > 0 { "partial" } else { "measured" },
        "measuredNonzeroSupportCount": measured_nonzero,
        "measuredZeroSupportCount": curvature_support_readings
            .iter()
            .filter(|reading| reading["curvatureValue"]["status"] == "measuredZero")
            .count(),
        "blockedSupportCount": blocked,
        "supportReadingRefs": (0..curvature_support_readings.len())
            .map(|index| format!("/curvatureSupportReadings/{index}"))
            .collect::<Vec<_>>(),
        "nonConclusions": [
            "curvature mass is a selected-support diagnostic count, not an architecture health score"
        ]
    })]
}

fn spectral_analysis_readings_v1(
    normalized: &NormalizedArchMapV1,
    curvature_support_readings: &[Value],
) -> Vec<Value> {
    vec![json!({
        "spectralReadingId": "spectral-analysis:v1-typed-evaluator-support",
        "profileRef": "spectrum-profile:v1-typed-evaluator@1",
        "operatorKind": "finite-selected-support-transfer",
        "normalizedAtomCount": normalized.summary.normalized_atom_count,
        "generatedMoleculeCandidateCount": normalized.summary.generated_molecule_candidate_count,
        "supportReadingRefs": (0..curvature_support_readings.len())
            .map(|index| format!("/curvatureSupportReadings/{index}"))
            .collect::<Vec<_>>(),
        "measuredBoundary": "spectrum is computed over emitted v1 curvature support rows only",
        "nonConclusions": [
            "spectralAnalysisReadings/v1 is not a global graph spectrum for every source relation"
        ]
    })]
}

fn spectral_mode_readings_v1(curvature_support_readings: &[Value]) -> Vec<Value> {
    curvature_support_readings
        .iter()
        .enumerate()
        .map(|(index, reading)| {
            json!({
                "spectralModeId": format!(
                    "spectral-mode:{}",
                    stable_ref(reading["law"].as_str().unwrap_or("selected-law"))
                ),
                "rank": index + 1,
                "modeKind": if reading["curvatureValue"]["status"] == "measuredNonzero" {
                    "nonzeroCurvatureMode"
                } else if reading["curvatureValue"]["status"] == "blockedByCoverageGap" {
                    "coverageBlockedMode"
                } else {
                    "measuredZeroMode"
                },
                "axisRef": reading["axisRef"],
                "curvatureValue": reading["curvatureValue"],
                "supportReadingRef": format!("/curvatureSupportReadings/{index}"),
                "supportRefs": reading["supportRefs"],
                "witnessRefs": reading["witnessRefs"],
                "coverageGapRefs": reading["coverageGapRefs"],
                "recommendedReviewTarget": if reading["curvatureValue"]["status"] == "measuredZero" {
                    "retain zero as selected-support reading with coverage boundary"
                } else {
                    "review selected support, witness refs, and coverage gaps"
                }
            })
        })
        .collect()
}

fn spectral_drilldown_readings_v1(
    curvature_support_readings: &[Value],
    curvature_transfer_readings: &[Value],
) -> Vec<Value> {
    curvature_support_readings
        .iter()
        .enumerate()
        .map(|(index, reading)| {
            json!({
                "drilldownId": format!(
                    "spectral-drilldown:{}",
                    stable_ref(reading["law"].as_str().unwrap_or("selected-law"))
                ),
                "supportReadingRef": format!("/curvatureSupportReadings/{index}"),
                "transferReadingRefs": if curvature_transfer_readings.is_empty() {
                    Vec::<String>::new()
                } else {
                    vec!["/curvatureTransferReadings/0".to_string()]
                },
                "sourceRefs": reading["sourceRefs"],
                "supportRefs": reading["supportRefs"],
                "witnessRefs": reading["witnessRefs"],
                "coverageGapRefs": reading["coverageGapRefs"],
                "reading": "bounded drilldown over v1 typed evaluator support"
            })
        })
        .collect()
}

fn architecture_spectrum_report_v1(
    normalized: &NormalizedArchMapV1,
    curvature_support_readings: &[Value],
    curvature_transfer_readings: &[Value],
    curvature_mass_readings: &[Value],
) -> Value {
    let coverage_gaps = curvature_support_readings
        .iter()
        .flat_map(|reading| json_string_array_value(reading, "coverageGapRefs"))
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect::<Vec<_>>();
    let mut top_hotspots = curvature_support_readings
        .iter()
        .enumerate()
        .map(|(index, reading)| {
            json!({
                "hotspotId": format!(
                    "spectrum-hotspot:{}",
                    stable_ref(reading["law"].as_str().unwrap_or("selected-law"))
                ),
                "axisRef": reading["axisRef"],
                "curvatureValue": reading["curvatureValue"]["value"],
                "curvatureStatus": reading["curvatureValue"]["status"],
                "supportReadingRef": format!("/curvatureSupportReadings/{index}"),
                "supportRefs": reading["supportRefs"],
                "witnessRefs": reading["witnessRefs"],
                "coverageGapRefs": reading["coverageGapRefs"],
                "sourceRefs": reading["sourceRefs"],
                "recommendedNextAction": if reading["curvatureValue"]["status"] == "measuredZero" {
                    "keep selected-support zero bounded by coverage and exactness assumptions"
                } else if reading["curvatureValue"]["status"] == "measuredNonzero" {
                    "review nonzero selected-axis support before repair planning"
                } else {
                    "collect missing support before reading this axis as zero"
                }
            })
        })
        .collect::<Vec<_>>();
    top_hotspots.sort_by_key(spectrum_hotspot_priority);
    let recurrent_obstructions = curvature_transfer_readings
        .first()
        .and_then(|reading| reading["recurrentObstructionModes"].as_array())
        .into_iter()
        .flatten()
        .cloned()
        .collect::<Vec<_>>();
    let status = if !coverage_gaps.is_empty() {
        "needsCoverageReview"
    } else if recurrent_obstructions.is_empty()
        && top_hotspots
            .iter()
            .all(|hotspot| hotspot["curvatureStatus"] == "measuredZero")
    {
        "measuredZeroWithinSelectedSupport"
    } else {
        "actionable"
    };
    json!({
        "reportId": "architecture-spectrum-report:v1-typed-evaluator",
        "profileRef": "spectrum-profile:v1-typed-evaluator@1",
        "status": status,
        "measurementStatus": if coverage_gaps.is_empty() { "measured" } else { "partial" },
        "readingBoundary": {
            "basis": "normalized ArchMap v1 support + selected typed evaluator results",
            "normalizerId": normalized.normalizer_id,
            "zeroSpectrumBoundary": "zero spectrum is bounded to selected measured support rows and does not imply global lawfulness",
            "coverageBoundary": "coverage gaps block zero reflection and remain explicit report gaps"
        },
        "topHotspots": top_hotspots,
        "topEigenmodes": spectral_mode_readings_v1(curvature_support_readings),
        "topWitnessClusters": witness_clusters_v1(curvature_support_readings),
        "recurrentObstructions": recurrent_obstructions,
        "coverageGaps": coverage_gaps,
        "curvatureMassReadingRefs": curvature_mass_readings
            .iter()
            .enumerate()
            .map(|(index, _)| format!("/curvatureMassReadings/{index}"))
            .collect::<Vec<_>>(),
        "measuredBoundary": "ArchitectureSpectrumReport/v1 is measured from selected v1 curvature support and transfer readings under explicit coverage boundaries",
        "recommendedReviewFocus": [
            "start from nonzero or coverage-blocked hotspots with support and witness refs",
            "treat measured zero as selected-support zero, not global flatness",
            "use recurrent obstruction modes as current-state review signals only"
        ],
        "nonConclusions": [
            "ArchitectureSpectrumReport/v1 is not a single architecture quality score",
            "ArchitectureSpectrumReport/v1 does not prove global lawfulness or flatness",
            "ArchitectureSpectrumReport/v1 does not predict future incidents or empirical cost increase",
            "ArchitectureSpectrumReport/v1 does not replace FieldSig forecast or governance"
        ]
    })
}

fn witness_clusters_v1(curvature_support_readings: &[Value]) -> Vec<Value> {
    curvature_support_readings
        .iter()
        .enumerate()
        .filter(|(_, reading)| {
            reading["supportRefs"]
                .as_array()
                .is_some_and(|refs| !refs.is_empty())
        })
        .map(|(index, reading)| {
            json!({
                "clusterRef": format!(
                    "spectrum-witness-cluster:{}",
                    stable_ref(reading["law"].as_str().unwrap_or("selected-law"))
                ),
                "clusterBasis": "typed evaluator support refs grouped by selected law axis",
                "axisRefs": [reading["axisRef"].clone()],
                "witnessRefs": reading["witnessRefs"],
                "supportRefs": reading["supportRefs"],
                "sourceRefs": reading["sourceRefs"],
                "transferEdgeRefs": transfer_edge_refs_for_support_index(curvature_support_readings, index),
                "clusterWeight": reading["weight"],
                "reading": "v1 witness cluster is derived from normalized support refs, not labels"
            })
        })
        .collect()
}

fn transfer_edge_refs_for_support_index(
    curvature_support_readings: &[Value],
    support_index: usize,
) -> Vec<String> {
    let Some(reading) = curvature_support_readings.get(support_index) else {
        return Vec::new();
    };
    if reading["curvatureValue"]["status"] != "measuredNonzero"
        && reading["curvatureValue"]["status"] != "blockedByCoverageGap"
    {
        return Vec::new();
    }
    let edge_index = curvature_support_readings
        .iter()
        .take(support_index)
        .filter(|candidate| {
            candidate["curvatureValue"]["status"] == "measuredNonzero"
                || candidate["curvatureValue"]["status"] == "blockedByCoverageGap"
        })
        .count();
    vec![format!(
        "/curvatureTransferReadings/0/transferEdges/{edge_index}"
    )]
}

fn spectrum_hotspot_priority(hotspot: &Value) -> u8 {
    match hotspot["curvatureStatus"].as_str().unwrap_or_default() {
        "measuredNonzero" => 0,
        "blockedByCoverageGap" => 1,
        "measuredZero" => 2,
        _ => 3,
    }
}

fn architecture_spectrum_summary_v1(spectrum: &Value) -> Value {
    let report = &spectrum["architectureSpectrumReport"];
    json!({
        "reportRef": "archsig-analysis-packet.json#/architectureSpectrumReport",
        "reportPacketPointer": "/architectureSpectrumReport",
        "status": report["status"],
        "measurementStatus": report["measurementStatus"],
        "hotspotCount": report["topHotspots"].as_array().map(Vec::len).unwrap_or_default(),
        "recurrentObstructionCount": report["recurrentObstructions"].as_array().map(Vec::len).unwrap_or_default(),
        "coverageGapCount": report["coverageGaps"].as_array().map(Vec::len).unwrap_or_default(),
        "topHotspotRefs": report["topHotspots"]
            .as_array()
            .into_iter()
            .flatten()
            .take(5)
            .filter_map(|hotspot| hotspot["hotspotId"].as_str().map(str::to_string))
            .collect::<Vec<_>>(),
        "nonConclusions": report["nonConclusions"]
    })
}

fn architecture_homotopy_v1(
    normalized: &NormalizedArchMapV1,
    typed_results: &TypedEvaluatorResultsV1,
    spectrum: &Value,
) -> Value {
    let path_homotopy_diagram_readings = path_homotopy_diagram_readings_v1(normalized);
    let homotopy_holonomy_readings = homotopy_holonomy_readings_v1(normalized, spectrum);
    let stokes_style_readings = stokes_style_readings_v1(normalized, &homotopy_holonomy_readings);
    let homotopy_distance_readings =
        homotopy_distance_readings_v1(normalized, &homotopy_holonomy_readings);
    let architecture_homotopy_report = architecture_homotopy_report_v1(
        normalized,
        typed_results,
        spectrum,
        &path_homotopy_diagram_readings,
        &homotopy_holonomy_readings,
        &stokes_style_readings,
        &homotopy_distance_readings,
    );
    json!({
        "pathHomotopyDiagramReadings": path_homotopy_diagram_readings,
        "homotopyHolonomyReadings": homotopy_holonomy_readings,
        "stokesStyleReadings": stokes_style_readings,
        "homotopyDistanceReadings": homotopy_distance_readings,
        "architectureHomotopyReport": architecture_homotopy_report
    })
}

fn path_homotopy_diagram_readings_v1(normalized: &NormalizedArchMapV1) -> Vec<Value> {
    normalized
        .molecules
        .iter()
        .enumerate()
        .map(|(index, molecule)| {
            let atoms = molecule_atoms(normalized, molecule);
            json!({
                "pathHomotopyDiagramReadingId": format!(
                    "path-homotopy-diagram:{}",
                    stable_ref(&molecule.normalized_molecule_id)
                ),
                "diagramKind": if molecule.generated_molecule_candidate_status == "generated" {
                    "filledLoopCandidate"
                } else {
                    "missingFillerCandidate"
                },
                "moleculeRef": molecule.normalized_molecule_id,
                "moleculeIndex": index,
                "supportAtomRefs": molecule.atom_ids,
                "selectedAxes": atom_axes(&atoms),
                "pathPairRefs": molecule
                    .atom_ids
                    .windows(2)
                    .enumerate()
                    .map(|(pair_index, pair)| {
                        json!({
                            "pathPairId": format!(
                                "path-pair:{}:{pair_index}",
                                stable_ref(&molecule.normalized_molecule_id)
                            ),
                            "fromAtomRef": pair[0],
                            "toAtomRef": pair[1]
                        })
                    })
                    .collect::<Vec<_>>(),
                "fillerStatus": if molecule.generated_molecule_candidate_status == "generated" {
                    "measuredFiller"
                } else {
                    "missingFillerEvidence"
                },
                "coverageGapRefs": if molecule.generated_molecule_candidate_status == "generated" {
                    Vec::<String>::new()
                } else {
                    vec![format!(
                        "coverage-gap:homotopy:{}",
                        stable_ref(&molecule.normalized_molecule_id)
                    )]
                },
                "readingBoundary": {
                    "basis": "explicit normalized ArchMap v1 molecule membership",
                    "nonConclusion": "same endpoint or shared membership is not global homotopy equivalence"
                }
            })
        })
        .collect()
}

fn homotopy_holonomy_readings_v1(normalized: &NormalizedArchMapV1, spectrum: &Value) -> Vec<Value> {
    let nonzero_support_atom_refs = nonzero_curvature_support_atom_refs(spectrum);
    let nonzero_support_molecule_refs = nonzero_curvature_support_molecule_refs(spectrum);
    normalized
        .molecules
        .iter()
        .enumerate()
        .map(|(index, molecule)| {
            let atoms = molecule_atoms(normalized, molecule);
            let is_filled = molecule.generated_molecule_candidate_status == "generated";
            let witness_refs = molecule
                .atom_ids
                .iter()
                .filter(|atom_id| nonzero_support_atom_refs.contains(atom_id.as_str()))
                .cloned()
                .collect::<Vec<_>>();
            let nonzero_support_refs = nonzero_curvature_support_refs_for_molecule(
                spectrum,
                molecule,
                &nonzero_support_molecule_refs,
                &nonzero_support_atom_refs,
            );
            let has_nonzero_support = !nonzero_support_refs.is_empty();
            let has_unmeasured_axis_signal = selected_axis_difference_signal(&atoms);
            let holonomy_status = if !is_filled {
                "blockedByMissingFiller"
            } else if has_nonzero_support {
                "measuredNonzero"
            } else if has_unmeasured_axis_signal {
                "unmeasuredSelectedAxisDifference"
            } else {
                "measuredZero"
            };
            let coverage_gap_refs = if !is_filled {
                vec![format!(
                    "coverage-gap:homotopy:{}",
                    stable_ref(&molecule.normalized_molecule_id)
                )]
            } else if holonomy_status == "unmeasuredSelectedAxisDifference" {
                vec![format!(
                    "coverage-gap:homotopy-selected-axis:{}",
                    stable_ref(&molecule.normalized_molecule_id)
                )]
            } else {
                Vec::new()
            };
            json!({
                "holonomyReadingId": format!(
                    "homotopy-holonomy:{}",
                    stable_ref(&molecule.normalized_molecule_id)
                ),
                "pathHomotopyDiagramRef": format!("/pathHomotopyDiagramReadings/{index}"),
                "moleculeRef": molecule.normalized_molecule_id,
                "supportAtomRefs": molecule.atom_ids,
                "selectedAxes": atom_axes(&atoms),
                "holonomyValue": if holonomy_status == "measuredNonzero" {
                    json!(nonzero_support_refs.len())
                } else if holonomy_status == "measuredZero" {
                    json!(0)
                } else {
                    Value::Null
                },
                "holonomyStatus": holonomy_status,
                "coverageGapRefs": coverage_gap_refs,
                "nonzeroCurvatureSupportRefs": nonzero_support_refs,
                "witnessRefs": witness_refs,
                "readingBoundary": {
                    "basis": "selected typed evaluator nonzero curvature support inside an explicit molecule candidate",
                    "zeroBoundary": "measured zero is selected-axis zero for this explicit molecule only",
                    "missingFillerBoundary": "missing filler blocks holonomy zero reflection",
                    "unmeasuredAxisBoundary": "semantic/runtime axis presence without selected nonzero evaluator support remains unmeasured, not nonzero"
                }
            })
        })
        .collect()
}

fn stokes_style_readings_v1(
    normalized: &NormalizedArchMapV1,
    homotopy_holonomy_readings: &[Value],
) -> Vec<Value> {
    normalized
        .molecules
        .iter()
        .enumerate()
        .map(|(index, molecule)| {
            let atoms = molecule_atoms(normalized, molecule);
            let holonomy = &homotopy_holonomy_readings[index];
            let is_filled = molecule.generated_molecule_candidate_status == "generated";
            let local_curvature_cells = if is_filled {
                atoms
                    .iter()
                    .filter(|atom| {
                        holonomy["witnessRefs"]
                            .as_array()
                            .into_iter()
                            .flatten()
                            .any(|reference| reference == &atom.normalized_atom_id)
                    })
                    .enumerate()
                    .map(|(cell_index, atom)| {
                        json!({
                            "localCurvatureCellId": format!(
                                "local-curvature-cell:{}:{cell_index}",
                                stable_ref(&molecule.normalized_molecule_id)
                            ),
                            "atomRef": atom.normalized_atom_id,
                            "axis": atom.axis,
                            "curvatureValue": 1,
                            "supportRefs": [atom.normalized_atom_id.clone()]
                        })
                    })
                    .collect::<Vec<_>>()
            } else {
                Vec::new()
            };
            json!({
                "stokesReadingId": format!("stokes-style:{}", stable_ref(&molecule.normalized_molecule_id)),
                "pathHomotopyDiagramRef": format!("/pathHomotopyDiagramReadings/{index}"),
                "holonomyReadingRef": format!("/homotopyHolonomyReadings/{index}"),
                "moleculeRef": molecule.normalized_molecule_id,
                "stokesStatus": if !is_filled {
                    "blockedByMissingFiller"
                } else if holonomy["holonomyStatus"] == "measuredNonzero" {
                    "boundedNonzeroWithMeasuredFilling"
                } else if holonomy["holonomyStatus"] == "unmeasuredSelectedAxisDifference" {
                    "blockedByCoverageGap"
                } else {
                    "measuredZeroWithinSelectedFilling"
                },
                "boundaryHolonomyValue": holonomy["holonomyValue"],
                "localCurvatureCells": local_curvature_cells,
                "coverageGapRefs": holonomy["coverageGapRefs"],
                "readingBoundary": {
                    "basis": "bounded Stokes-style reading over an explicit filled molecule candidate",
                    "missingFillerBoundary": "no local curvature conclusion is emitted without measured filling"
                },
                "nonConclusions": [
                    "Stokes-style reading is not a Lean theorem discharge",
                    "filled-loop nonzero holonomy is bounded to selected axes and explicit molecule support"
                ]
            })
        })
        .collect()
}

fn homotopy_distance_readings_v1(
    normalized: &NormalizedArchMapV1,
    homotopy_holonomy_readings: &[Value],
) -> Vec<Value> {
    normalized
        .molecules
        .iter()
        .enumerate()
        .map(|(index, molecule)| {
            let holonomy = &homotopy_holonomy_readings[index];
            let is_filled = molecule.generated_molecule_candidate_status == "generated";
            let homotopy_distance = if !is_filled {
                Value::Null
            } else {
                holonomy["holonomyValue"].clone()
            };
            json!({
                "homotopyDistanceReadingId": format!(
                    "homotopy-distance:{}",
                    stable_ref(&molecule.normalized_molecule_id)
                ),
                "pathHomotopyDiagramRef": format!("/pathHomotopyDiagramReadings/{index}"),
                "holonomyReadingRef": format!("/homotopyHolonomyReadings/{index}"),
                "moleculeRef": molecule.normalized_molecule_id,
                "measurementStatus": if !is_filled {
                    "blockedByMissingFiller"
                } else if holonomy["holonomyStatus"] == "unmeasuredSelectedAxisDifference" {
                    "blockedByCoverageGap"
                } else {
                    "measured"
                },
                "homotopyDistance": if holonomy["holonomyStatus"] == "unmeasuredSelectedAxisDifference" {
                    Value::Null
                } else {
                    homotopy_distance
                },
                "fillingCost": if is_filled && holonomy["holonomyStatus"] != "unmeasuredSelectedAxisDifference" {
                    json!(molecule.atom_ids.len())
                } else {
                    Value::Null
                },
                "observationGapLowerBound": if !is_filled || holonomy["holonomyStatus"] == "unmeasuredSelectedAxisDifference" { 1 } else { 0 },
                "coverageGapRefs": holonomy["coverageGapRefs"],
                "nonConclusions": [
                    "homotopyDistanceReadings/v1 is a selected explicit-molecule reading, not global path distance"
                ]
            })
        })
        .collect()
}

fn architecture_homotopy_report_v1(
    normalized: &NormalizedArchMapV1,
    typed_results: &TypedEvaluatorResultsV1,
    spectrum: &Value,
    path_homotopy_diagram_readings: &[Value],
    homotopy_holonomy_readings: &[Value],
    stokes_style_readings: &[Value],
    homotopy_distance_readings: &[Value],
) -> Value {
    let filled_indices = normalized
        .molecules
        .iter()
        .enumerate()
        .filter_map(|(index, molecule)| {
            (molecule.generated_molecule_candidate_status == "generated").then_some(index)
        })
        .collect::<Vec<_>>();
    let unfilled_indices = normalized
        .molecules
        .iter()
        .enumerate()
        .filter_map(|(index, molecule)| {
            (molecule.generated_molecule_candidate_status != "generated").then_some(index)
        })
        .collect::<Vec<_>>();
    let missing_filler_evidence = unfilled_indices
        .iter()
        .enumerate()
        .map(|(gap_index, molecule_index)| {
            let molecule = &normalized.molecules[*molecule_index];
            json!({
                "missingFillerEvidenceId": format!(
                    "missing-filler:{}",
                    stable_ref(&molecule.normalized_molecule_id)
                ),
                "pathHomotopyDiagramRef": format!("/pathHomotopyDiagramReadings/{molecule_index}"),
                "holonomyReadingRef": format!("/homotopyHolonomyReadings/{molecule_index}"),
                "moleculeRef": molecule.normalized_molecule_id,
                "gapRef": format!(
                    "coverage-gap:homotopy:{}",
                    stable_ref(&molecule.normalized_molecule_id)
                ),
                "gapIndex": gap_index,
                "blockerReason": molecule.normalization_blocker_reason,
                "reading": "missing explicit molecule filler blocks zero holonomy and Stokes-style local curvature conclusions"
            })
        })
        .collect::<Vec<_>>();
    let filled_loops = filled_indices
        .iter()
        .map(|index| homotopy_loop_entry(normalized, *index, None))
        .collect::<Vec<_>>();
    let unfilled_loops = unfilled_indices
        .iter()
        .enumerate()
        .map(|(gap_index, index)| homotopy_loop_entry(normalized, *index, Some(gap_index)))
        .collect::<Vec<_>>();
    let nonzero_holonomy_loops = homotopy_holonomy_readings
        .iter()
        .enumerate()
        .filter(|(_, reading)| reading["holonomyStatus"] == "measuredNonzero")
        .map(|(index, _)| homotopy_loop_entry(normalized, index, None))
        .collect::<Vec<_>>();
    let top_local_curvature_cells = stokes_style_readings
        .iter()
        .enumerate()
        .flat_map(|(stokes_index, reading)| {
            reading["localCurvatureCells"]
                .as_array()
                .into_iter()
                .flatten()
                .enumerate()
                .map(move |(cell_index, cell)| {
                    json!({
                        "localCurvatureCellRef": format!(
                            "/stokesStyleReadings/{stokes_index}/localCurvatureCells/{cell_index}"
                        ),
                        "stokesReadingRef": format!("/stokesStyleReadings/{stokes_index}"),
                        "atomRef": cell["atomRef"],
                        "axis": cell["axis"],
                        "curvatureValue": cell["curvatureValue"]
                    })
                })
        })
        .collect::<Vec<_>>();
    let coverage_gaps = missing_filler_evidence
        .iter()
        .filter_map(|item| item["gapRef"].as_str().map(str::to_string))
        .chain(
            homotopy_holonomy_readings
                .iter()
                .flat_map(|reading| json_string_array_value(reading, "coverageGapRefs")),
        )
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect::<Vec<_>>();
    let status = if !coverage_gaps.is_empty() {
        "needsHomotopyEvidenceReview"
    } else if nonzero_holonomy_loops.is_empty() {
        "measuredZeroWithinSelectedFillings"
    } else {
        "actionable"
    };
    json!({
        "schemaVersion": "architecture-homotopy-report/v1",
        "reportId": "architecture-homotopy-report:v1-explicit-molecule-support",
        "selectedLawPolicyRef": typed_results.law_policy_ref,
        "archMapRef": typed_results.normalized_archmap_ref,
        "analysisPacketRef": "archsig-analysis-packet.json#/architectureHomotopyReport",
        "status": status,
        "measurementStatus": if coverage_gaps.is_empty() { "measured" } else { "partial" },
        "selectedAxes": normalized
            .atoms
            .iter()
            .map(|atom| atom.axis.clone())
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect::<Vec<_>>(),
        "homotopyComplexSummary": {
            "explicitMoleculeCount": normalized.molecules.len(),
            "filledLoopCount": filled_loops.len(),
            "unfilledLoopCount": unfilled_loops.len(),
            "nonzeroHolonomyLoopCount": nonzero_holonomy_loops.len(),
            "topLocalCurvatureCellCount": top_local_curvature_cells.len()
        },
        "measuredPathPairSummary": {
            "pathHomotopyDiagramReadingCount": path_homotopy_diagram_readings.len()
        },
        "measuredLoopSummary": {
            "filledLoopCount": filled_loops.len(),
            "unfilledLoopCount": unfilled_loops.len(),
            "nonzeroHolonomyLoopCount": nonzero_holonomy_loops.len()
        },
        "filledLoops": filled_loops,
        "unfilledLoops": unfilled_loops,
        "nonzeroHolonomyLoops": nonzero_holonomy_loops,
        "topLocalCurvatureCells": top_local_curvature_cells,
        "missingFillerEvidence": missing_filler_evidence,
        "architecturalHoleReadings": missing_filler_evidence
            .iter()
            .enumerate()
            .filter_map(|(index, evidence)| {
                evidence["gapRef"].as_str().map(|gap_ref| json!({
                "holeReadingId": format!("architectural-hole:{index}"),
                "missingFillerEvidenceRef": format!("/architectureHomotopyReport/missingFillerEvidence/{index}"),
                "gapRef": gap_ref,
                "reading": "architectural hole reading from missing explicit filler evidence"
            }))
            })
            .collect::<Vec<_>>(),
        "aggregateReadings": {
            "HolMass": homotopy_holonomy_readings
                .iter()
                .filter(|reading| reading["holonomyStatus"] == "measuredNonzero")
                .count(),
            "FillRatio": if normalized.molecules.is_empty() {
                Value::Null
            } else {
                json!(filled_indices.len() as f64 / normalized.molecules.len() as f64)
            },
            "CurvedFillMass": stokes_style_readings
                .iter()
                .flat_map(|reading| reading["localCurvatureCells"].as_array().into_iter().flatten())
                .count(),
            "HoleHolonomy": unfilled_indices.len()
        },
        "pathHomotopyDiagramReadingRefs": (0..path_homotopy_diagram_readings.len())
            .map(|index| format!("/pathHomotopyDiagramReadings/{index}"))
            .collect::<Vec<_>>(),
        "homotopyHolonomyReadingRefs": (0..homotopy_holonomy_readings.len())
            .map(|index| format!("/homotopyHolonomyReadings/{index}"))
            .collect::<Vec<_>>(),
        "stokesStyleReadingRefs": (0..stokes_style_readings.len())
            .map(|index| format!("/stokesStyleReadings/{index}"))
            .collect::<Vec<_>>(),
        "homotopyDistanceReadingRefs": (0..homotopy_distance_readings.len())
            .map(|index| format!("/homotopyDistanceReadings/{index}"))
            .collect::<Vec<_>>(),
        "spectrumContextRef": "archsig-analysis-packet.json#/architectureSpectrumReport",
        "nonzeroCurvatureSupportRefs": spectrum["curvatureSupportReadings"]
            .as_array()
            .into_iter()
            .flatten()
            .enumerate()
            .filter(|(_, reading)| reading["curvatureValue"]["status"] == "measuredNonzero")
            .map(|(index, _)| format!("/curvatureSupportReadings/{index}"))
            .collect::<Vec<_>>(),
        "coverageGaps": coverage_gaps,
        "recommendedReviewFocus": [
            "review unfilled loops before reading holonomy as zero",
            "review nonzero holonomy loops with their measured filler and local curvature cells",
            "treat aggregate readings as prioritization signals, not architecture quality scores"
        ],
        "nonConclusions": [
            "ArchitectureHomotopyReport/v1 does not reconstruct every path in the architecture object",
            "unmeasured path is not flat or equivalent",
            "missing filler is not a violation proof and is not measured zero",
            "unfilled loop is an architectural hole reading, not defect absence or defect proof",
            "nonzero holonomy is selected typed-evaluator support inside explicit molecule scope, not future incident proof",
            "filled loop nonzero holonomy needs measured filling before local curvature can be read",
            "ArchitectureHomotopyReport/v1 is not a Lean theorem discharge"
        ]
    })
}

fn homotopy_loop_entry(
    normalized: &NormalizedArchMapV1,
    molecule_index: usize,
    missing_filler_index: Option<usize>,
) -> Value {
    let molecule = &normalized.molecules[molecule_index];
    let atoms = molecule_atoms(normalized, molecule);
    json!({
        "loopId": format!("homotopy-loop:{}", stable_ref(&molecule.normalized_molecule_id)),
        "moleculeRef": molecule.normalized_molecule_id,
        "pathHomotopyDiagramRef": format!("/pathHomotopyDiagramReadings/{molecule_index}"),
        "holonomyReadingRef": format!("/homotopyHolonomyReadings/{molecule_index}"),
        "stokesReadingRef": format!("/stokesStyleReadings/{molecule_index}"),
        "homotopyDistanceReadingRef": format!("/homotopyDistanceReadings/{molecule_index}"),
        "missingFillerEvidenceRef": missing_filler_index
            .map(|index| format!("/architectureHomotopyReport/missingFillerEvidence/{index}")),
        "supportAtomRefs": molecule.atom_ids,
        "selectedAxes": atom_axes(&atoms),
        "loopStatus": if missing_filler_index.is_some() {
            "unfilled"
        } else {
            "filled"
        }
    })
}

fn architecture_homotopy_summary_v1(homotopy: &Value) -> Value {
    let report = &homotopy["architectureHomotopyReport"];
    json!({
        "reportRef": "archsig-analysis-packet.json#/architectureHomotopyReport",
        "reportPacketPointer": "/architectureHomotopyReport",
        "status": report["status"],
        "measurementStatus": report["measurementStatus"],
        "filledLoopCount": report["filledLoops"].as_array().map(Vec::len).unwrap_or_default(),
        "unfilledLoopCount": report["unfilledLoops"].as_array().map(Vec::len).unwrap_or_default(),
        "nonzeroHolonomyLoopCount": report["nonzeroHolonomyLoops"].as_array().map(Vec::len).unwrap_or_default(),
        "topArchitecturalHoleRefs": report["unfilledLoops"]
            .as_array()
            .into_iter()
            .flatten()
            .enumerate()
            .take(5)
            .map(|(index, _)| format!("/architectureHomotopyReport/unfilledLoops/{index}"))
            .collect::<Vec<_>>(),
        "topArchitecturalHoleIds": report["unfilledLoops"]
            .as_array()
            .into_iter()
            .flatten()
            .take(5)
            .filter_map(|item| item["loopId"].as_str().map(str::to_string))
            .collect::<Vec<_>>(),
        "topNonzeroHolonomyRefs": report["nonzeroHolonomyLoops"]
            .as_array()
            .into_iter()
            .flatten()
            .enumerate()
            .take(5)
            .map(|(index, _)| format!("/architectureHomotopyReport/nonzeroHolonomyLoops/{index}"))
            .collect::<Vec<_>>(),
        "topNonzeroHolonomyIds": report["nonzeroHolonomyLoops"]
            .as_array()
            .into_iter()
            .flatten()
            .take(5)
            .filter_map(|item| item["loopId"].as_str().map(str::to_string))
            .collect::<Vec<_>>(),
        "nonConclusions": report["nonConclusions"]
    })
}

fn architecture_structural_v1(
    normalized: &NormalizedArchMapV1,
    typed_results: &TypedEvaluatorResultsV1,
    architecture_distance: &Value,
    generated_obstructions: &[Value],
    generated_repair_targets: &[Value],
    spectrum: &Value,
    homotopy: &Value,
) -> Value {
    let representation_metric_readings =
        representation_metric_readings_v1(normalized, typed_results, architecture_distance);
    let local_curvature_diagram_readings =
        local_curvature_diagram_readings_v1(normalized, typed_results, spectrum);
    let three_layer_flatness_readings = three_layer_flatness_readings_v1(normalized, typed_results);
    let observation_projection_readings =
        observation_projection_readings_v1(normalized, typed_results);
    let state_transition_algebra_readings =
        state_transition_algebra_readings_v1(normalized, typed_results);
    let effect_relation_algebra_readings =
        effect_relation_algebra_readings_v1(normalized, typed_results);
    let synthesis_blockage_readings =
        synthesis_blockage_readings_v1(normalized, typed_results, generated_obstructions);
    let operation_precondition_readiness_readings = operation_precondition_readiness_readings_v1(
        normalized,
        typed_results,
        generated_repair_targets,
    );
    let path_multiplicity_loss_readings =
        path_multiplicity_loss_readings_v1(normalized, typed_results, homotopy);

    let arrays = [
        (
            "representationMetricReadings",
            representation_metric_readings.clone(),
        ),
        (
            "localCurvatureDiagramReadings",
            local_curvature_diagram_readings.clone(),
        ),
        (
            "threeLayerFlatnessReadings",
            three_layer_flatness_readings.clone(),
        ),
        (
            "observationProjectionReadings",
            observation_projection_readings.clone(),
        ),
        (
            "stateTransitionAlgebraReadings",
            state_transition_algebra_readings.clone(),
        ),
        (
            "effectRelationAlgebraReadings",
            effect_relation_algebra_readings.clone(),
        ),
        (
            "synthesisBlockageReadings",
            synthesis_blockage_readings.clone(),
        ),
        (
            "operationPreconditionReadinessReadings",
            operation_precondition_readiness_readings.clone(),
        ),
        (
            "pathMultiplicityLossReadings",
            path_multiplicity_loss_readings.clone(),
        ),
    ];
    let connected_reading_refs = arrays
        .iter()
        .flat_map(|(field, readings)| {
            readings
                .iter()
                .enumerate()
                .map(move |(index, _)| format!("/{field}/{index}"))
        })
        .collect::<Vec<_>>();
    let coverage_gap_refs = arrays
        .iter()
        .flat_map(|(_, readings)| {
            readings
                .iter()
                .flat_map(|reading| json_string_array_value(reading, "coverageGapRefs"))
        })
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect::<Vec<_>>();
    let measured_count = arrays
        .iter()
        .flat_map(|(_, readings)| readings.iter())
        .filter(|reading| structural_reading_is_measured(reading))
        .count();
    let blocked_count = arrays
        .iter()
        .flat_map(|(_, readings)| readings.iter())
        .filter(|reading| !structural_reading_is_measured(reading))
        .count();
    let status = if blocked_count > 0 {
        "needsReview"
    } else {
        "measuredWithinSelectedStructuralSupport"
    };

    json!({
        "representationMetricReadings": representation_metric_readings,
        "localCurvatureDiagramReadings": local_curvature_diagram_readings,
        "threeLayerFlatnessReadings": three_layer_flatness_readings,
        "observationProjectionReadings": observation_projection_readings,
        "stateTransitionAlgebraReadings": state_transition_algebra_readings,
        "effectRelationAlgebraReadings": effect_relation_algebra_readings,
        "synthesisBlockageReadings": synthesis_blockage_readings,
        "operationPreconditionReadinessReadings": operation_precondition_readiness_readings,
        "pathMultiplicityLossReadings": path_multiplicity_loss_readings,
        "structuralReadingReviewSurface": {
            "surfaceId": "structural-reading-review-surface:v1",
            "schemaVersion": "structural-reading-review-surface/v1",
            "status": status,
            "measurementStatus": if blocked_count == 0 { "measured" } else { "partial" },
            "currentStateReading": format!(
                "ArchSig v1 reads current architecture state from normalized ArchMap {}, {} typed evaluator result(s), {} structural reading(s), and {} coverage gap(s)",
                normalized.source_archmap_id,
                typed_results.results.len(),
                connected_reading_refs.len(),
                coverage_gap_refs.len()
            ),
            "measuredStructuralReadingCount": measured_count,
            "blockedStructuralReadingCount": blocked_count,
            "connectedReadingRefs": connected_reading_refs,
            "typedEvaluatorResultRefs": typed_result_refs(typed_results),
            "normalizedAtomRefs": normalized_atom_ids(normalized),
            "normalizedMoleculeRefs": normalized_molecule_ids(normalized),
            "coverageGapRefs": coverage_gap_refs,
            "reviewFocus": [
                "read representation metrics and local curvature before interpreting structural pressure as quality",
                "read projection, state/effect algebra, and path multiplicity before treating missing coordinates as zero",
                "read synthesis and operation precondition rows as bounded review queues, not repair safety"
            ],
            "evidenceBoundary": "structural readings are generated from normalized ArchMap v1, typed evaluator results, and generated packet refs; they do not restore removed v0 input fields",
            "nonConclusions": [
                "structuralReadingReviewSurface/v1 is not a Lean theorem proof",
                "structuralReadingReviewSurface/v1 is not a global architecture quality score",
                "blocked structural rows are not measured zero",
                "repair and synthesis rows are review telemetry, not automatic repair safety"
            ]
        }
    })
}

fn representation_metric_readings_v1(
    normalized: &NormalizedArchMapV1,
    typed_results: &TypedEvaluatorResultsV1,
    architecture_distance: &Value,
) -> Vec<Value> {
    let coverage_gap_refs = structural_coverage_gap_refs(typed_results);
    let signature_distance_refs = architecture_distance["signatureDistanceReadings"]
        .as_array()
        .into_iter()
        .flatten()
        .enumerate()
        .map(|(index, _)| format!("/architectureDistance/signatureDistanceReadings/{index}"))
        .collect::<Vec<_>>();
    let operation_distance_refs = architecture_distance["operationDistanceReadings"]
        .as_array()
        .into_iter()
        .flatten()
        .enumerate()
        .map(|(index, _)| format!("/architectureDistance/operationDistanceReadings/{index}"))
        .collect::<Vec<_>>();
    vec![json!({
        "readingId": format!("representation-metric:{}", stable_ref(&normalized.source_archmap_id)),
        "representationFamily": "typedEvaluatorSupportGraph",
        "measurementStatus": if typed_results.results.is_empty() {
            "blockedByMissingTypedEvaluatorResults"
        } else if coverage_gap_refs.is_empty() {
            "measured"
        } else {
            "partial"
        },
        "typedEvaluatorResultRefs": typed_result_refs(typed_results),
        "normalizedAtomRefs": normalized_atom_ids(normalized),
        "normalizedMoleculeRefs": normalized_molecule_ids(normalized),
        "signatureDistanceReadingRefs": signature_distance_refs,
        "operationDistanceReadingRefs": operation_distance_refs,
        "structuralDistance": {
            "status": if normalized.atoms.is_empty() { "blocked" } else { "measured" },
            "supportSize": normalized.atoms.len(),
            "moleculeSupportSize": normalized.molecules.len(),
            "evaluatorBasisRefs": typed_results
                .results
                .iter()
                .flat_map(|result| result.basis_refs.iter().cloned())
                .collect::<BTreeSet<_>>()
                .into_iter()
                .collect::<Vec<_>>()
        },
        "analyticDistance": {
            "status": "boundedProxy",
            "reading": "selected typed evaluator support graph size is review telemetry, not an architecture quality score"
        },
        "coverageGapRefs": coverage_gap_refs,
        "evidenceBoundary": "representation metric reads normalized support and typed evaluator refs only; it is not global structural faithfulness"
    })]
}

fn local_curvature_diagram_readings_v1(
    normalized: &NormalizedArchMapV1,
    typed_results: &TypedEvaluatorResultsV1,
    spectrum: &Value,
) -> Vec<Value> {
    let supports = spectrum["curvatureSupportReadings"]
        .as_array()
        .into_iter()
        .flatten()
        .enumerate()
        .map(|(index, reading)| {
            let status = if reading["curvatureValue"]["status"] == "measuredNonzero" {
                "measured"
            } else if reading["curvatureValue"]["status"] == "measuredZero" {
                "measured"
            } else {
                "blockedByCoverageGap"
            };
            json!({
                "readingId": format!("local-curvature-diagram:{index}"),
                "curvatureSupportReadingRef": format!("/curvatureSupportReadings/{index}"),
                "typedEvaluatorResultRefs": [reading["typedEvaluatorResultRef"].clone()],
                "normalizedAtomRefs": reading["witnessRefs"],
                "normalizedMoleculeRefs": reading["moleculeRefs"],
                "measurementStatus": status,
                "curvatureStatus": reading["curvatureValue"]["status"],
                "coverageGapRefs": reading["coverageGapRefs"],
                "reading": "local curvature diagram is bounded to selected typed evaluator curvature support",
                "evidenceBoundary": "absence of nonzero support is selected-support zero only, not global flatness"
            })
        })
        .collect::<Vec<_>>();
    if supports.is_empty() {
        vec![structural_blocked_row(
            "local-curvature-diagram:none",
            "blockedByMissingCurvatureSupport",
            normalized,
            typed_results,
            &[],
        )]
    } else {
        supports
    }
}

fn three_layer_flatness_readings_v1(
    normalized: &NormalizedArchMapV1,
    typed_results: &TypedEvaluatorResultsV1,
) -> Vec<Value> {
    let axes = normalized_axis_counts(normalized);
    let coverage_gap_refs = structural_coverage_gap_refs(typed_results);
    vec![json!({
        "readingId": format!("three-layer-flatness:{}", stable_ref(&normalized.source_archmap_id)),
        "measurementStatus": if typed_results.results.is_empty() {
            "blockedByMissingTypedEvaluatorResults"
        } else if coverage_gap_refs.is_empty() {
            "measured"
        } else {
            "partial"
        },
        "typedEvaluatorResultRefs": typed_result_refs(typed_results),
        "normalizedAtomRefs": normalized_atom_ids(normalized),
        "normalizedMoleculeRefs": normalized_molecule_ids(normalized),
        "staticStatus": layer_status(&axes, "static"),
        "runtimeStatus": layer_status(&axes, "runtime"),
        "semanticStatus": layer_status(&axes, "semantic"),
        "axisCounts": axes,
        "coverageGapRefs": coverage_gap_refs,
        "nonImplicationReading": "static, runtime, and semantic support are separate selected readings; one layer does not imply global flatness of another",
        "recommendedNextAction": "review blocked typed evaluator rows before interpreting layer separation as flatness"
    })]
}

fn observation_projection_readings_v1(
    normalized: &NormalizedArchMapV1,
    typed_results: &TypedEvaluatorResultsV1,
) -> Vec<Value> {
    let atom_refs = normalized_atom_ids(normalized);
    vec![json!({
        "readingId": format!("observation-projection:{}", stable_ref(&normalized.source_archmap_id)),
        "measurementStatus": if atom_refs.is_empty() {
            "blockedByMissingAtoms"
        } else if typed_results.results.is_empty() {
            "blockedByMissingTypedEvaluatorResults"
        } else {
            "measured"
        },
        "typedEvaluatorResultRefs": typed_result_refs(typed_results),
        "normalizedAtomRefs": atom_refs,
        "normalizedMoleculeRefs": normalized_molecule_ids(normalized),
        "observedAtomFamilies": normalized
            .atoms
            .iter()
            .map(|atom| atom.atom_kind.clone())
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect::<Vec<_>>(),
        "observedCoordinates": normalized
            .atoms
            .iter()
            .map(|atom| json!({
                "atomRef": atom.normalized_atom_id,
                "atomKind": atom.atom_kind,
                "axis": atom.axis,
                "predicate": atom.predicate.normalized_name
            }))
            .collect::<Vec<_>>(),
        "forgottenCoordinateEvidence": Vec::<Value>::new(),
        "coverageGapRefs": Vec::<String>::new(),
        "reconstructionRisk": "boundedToAuthoredArchMapV1",
        "evidenceBoundary": "projection reading records observed normalized coordinates only; it does not reconstruct removed v0 projectionInfo"
    })]
}

fn state_transition_algebra_readings_v1(
    normalized: &NormalizedArchMapV1,
    typed_results: &TypedEvaluatorResultsV1,
) -> Vec<Value> {
    let state_refs = atoms_by_axis_or_kind(normalized, &["dataflow"], &["dataState"]);
    let effect_refs = atoms_by_axis_or_kind(normalized, &["semantic"], &["effect"]);
    let runtime_refs = atoms_by_axis_or_kind(normalized, &["runtime"], &["runtimeInteraction"]);
    let blocked = state_refs.is_empty() || effect_refs.is_empty();
    vec![json!({
        "readingId": format!("state-transition-algebra:{}", stable_ref(&normalized.source_archmap_id)),
        "measurementStatus": if blocked { "blockedByMissingStateOrEffectEvidence" } else { "measured" },
        "typedEvaluatorResultRefs": typed_result_refs(typed_results),
        "normalizedAtomRefs": state_refs.iter().chain(effect_refs.iter()).chain(runtime_refs.iter()).cloned().collect::<Vec<_>>(),
        "normalizedMoleculeRefs": normalized_molecule_ids(normalized),
        "stateAtomRefs": state_refs,
        "effectAtomRefs": effect_refs,
        "runtimeAtomRefs": runtime_refs,
        "lawEvaluations": state_effect_law_evaluations(blocked),
        "coverageGapRefs": if blocked { vec![format!("coverage-gap:state-transition:{}", stable_ref(&normalized.source_archmap_id))] } else { Vec::new() },
        "reading": "state/effect algebra is evaluated from explicit normalized state/effect/runtime atoms",
        "evidenceBoundary": "missing state/effect evidence blocks transition algebra and is not measured zero"
    })]
}

fn effect_relation_algebra_readings_v1(
    normalized: &NormalizedArchMapV1,
    typed_results: &TypedEvaluatorResultsV1,
) -> Vec<Value> {
    let effect_refs = atoms_by_axis_or_kind(normalized, &["semantic"], &["effect"]);
    let relation_refs = atoms_by_axis_or_kind(normalized, &["static"], &["relation"]);
    let blocked = effect_refs.is_empty() || relation_refs.is_empty();
    vec![json!({
        "readingId": format!("effect-relation-algebra:{}", stable_ref(&normalized.source_archmap_id)),
        "measurementStatus": if blocked { "blockedByMissingEffectRelationEvidence" } else { "measured" },
        "typedEvaluatorResultRefs": typed_result_refs(typed_results),
        "normalizedAtomRefs": effect_refs.iter().chain(relation_refs.iter()).cloned().collect::<Vec<_>>(),
        "normalizedMoleculeRefs": normalized_molecule_ids(normalized),
        "requiredEffectRelations": ["orderingPreservation", "replaySafety", "idempotency", "compensationAvailability"],
        "relationInputs": relation_refs,
        "effectAtomRefs": effect_refs,
        "relationEvaluatorStatus": if blocked { "blocked" } else { "observed" },
        "coverageGapRefs": if blocked { vec![format!("coverage-gap:effect-relation:{}", stable_ref(&normalized.source_archmap_id))] } else { Vec::new() },
        "effectOrderingPressure": if blocked { "unmeasured" } else { "needsReview" },
        "evidenceBoundary": "effect relation reading is derived from normalized relation/effect atoms, not concernHints"
    })]
}

fn synthesis_blockage_readings_v1(
    normalized: &NormalizedArchMapV1,
    typed_results: &TypedEvaluatorResultsV1,
    generated_obstructions: &[Value],
) -> Vec<Value> {
    if generated_obstructions.is_empty() {
        return vec![json!({
            "readingId": format!("synthesis-blockage:none:{}", stable_ref(&normalized.source_archmap_id)),
            "measurementStatus": "blockedByNoGeneratedObstruction",
            "typedEvaluatorResultRefs": typed_result_refs(typed_results),
            "normalizedAtomRefs": normalized_atom_ids(normalized),
            "normalizedMoleculeRefs": normalized_molecule_ids(normalized),
            "targetConstructionRefs": Vec::<String>::new(),
            "constraintRefs": Vec::<String>::new(),
            "missingEvidenceRefs": structural_coverage_gap_refs(typed_results),
            "blockageStatus": "notMeasured",
            "noSolutionCertificateStatus": "notCertified",
            "coverageGapRefs": structural_coverage_gap_refs(typed_results),
            "synthesisBoundary": "no generated obstruction means no measured synthesis blocker; this row is a bounded non-measured review boundary"
        })];
    }
    generated_obstructions
        .iter()
        .enumerate()
        .map(|(index, obstruction)| {
            let measurement_status = if obstruction["obstructionKind"] == "measuredLawViolation" {
                "measured"
            } else {
                "blockedByMissingEvidence"
            };
            json!({
                "readingId": format!("synthesis-blockage:{index}"),
                "measurementStatus": measurement_status,
                "typedEvaluatorResultRefs": [obstruction["typedEvaluatorResultRef"].clone()],
                "normalizedAtomRefs": obstruction["supportAtomRefs"],
                "normalizedMoleculeRefs": obstruction["supportMoleculeRefs"],
                "targetConstructionRefs": [format!("/generatedObstructions/{index}")],
                "constraintRefs": obstruction["registryBasisRefs"],
                "missingEvidenceRefs": obstruction["coverageGapRefs"],
                "blockageStatus": if obstruction["obstructionKind"] == "measuredLawViolation" { "measuredObstructionReview" } else { "blockedByMissingEvidence" },
                "noSolutionCertificateStatus": "notCertified",
                "coverageGapRefs": obstruction["coverageGapRefs"],
                "synthesisBoundary": "generated obstruction is a structural review target, not a synthesis no-solution theorem"
            })
        })
        .collect()
}

fn operation_precondition_readiness_readings_v1(
    normalized: &NormalizedArchMapV1,
    typed_results: &TypedEvaluatorResultsV1,
    generated_repair_targets: &[Value],
) -> Vec<Value> {
    if generated_repair_targets.is_empty() {
        return vec![json!({
            "readingId": format!("operation-precondition-readiness:none:{}", stable_ref(&normalized.source_archmap_id)),
            "measurementStatus": "blockedByNoRepairTarget",
            "typedEvaluatorResultRefs": typed_result_refs(typed_results),
            "normalizedAtomRefs": normalized_atom_ids(normalized),
            "normalizedMoleculeRefs": normalized_molecule_ids(normalized),
            "operationRef": Value::Null,
            "readinessStatus": "notMeasured",
            "preconditionRefs": Vec::<String>::new(),
            "missingPreconditionRefs": structural_coverage_gap_refs(typed_results),
            "coverageGapRefs": structural_coverage_gap_refs(typed_results),
            "candidateBoundary": "no generated repair target means no measured operation precondition row; this is not repair safety"
        })];
    }
    generated_repair_targets
        .iter()
        .enumerate()
        .map(|(index, target)| {
            json!({
                "readingId": format!("operation-precondition-readiness:{index}"),
                "measurementStatus": if target["targetKind"] == "reviewMeasuredViolation" { "partial" } else { "blockedByMissingEvidence" },
                "typedEvaluatorResultRefs": [target["typedEvaluatorResultRef"].clone()],
                "normalizedAtomRefs": target["supportAtomRefs"],
                "normalizedMoleculeRefs": target["supportMoleculeRefs"],
                "operationRef": format!("/generatedRepairTargets/{index}"),
                "readinessStatus": if target["targetKind"] == "reviewMeasuredViolation" { "needsHumanReview" } else { "blockedByEvidenceCollection" },
                "preconditionRefs": target["registryBasisRefs"],
                "missingPreconditionRefs": target["coverageGapRefs"],
                "coverageGapRefs": target["coverageGapRefs"],
                "candidateBoundary": "repair target is a review operation candidate only; precondition readiness is not automatic repair safety"
            })
        })
        .collect()
}

fn path_multiplicity_loss_readings_v1(
    normalized: &NormalizedArchMapV1,
    typed_results: &TypedEvaluatorResultsV1,
    homotopy: &Value,
) -> Vec<Value> {
    if normalized.molecules.is_empty() {
        return vec![json!({
            "readingId": format!("path-multiplicity-loss:none:{}", stable_ref(&normalized.source_archmap_id)),
            "measurementStatus": "blockedByNoMoleculeSupport",
            "typedEvaluatorResultRefs": typed_result_refs(typed_results),
            "normalizedAtomRefs": normalized_atom_ids(normalized),
            "normalizedMoleculeRefs": Vec::<String>::new(),
            "observedPathCount": 0,
            "alternatePathPressure": 0,
            "reachabilityForgottenRefs": Vec::<String>::new(),
            "coverageGapRefs": Vec::<String>::new(),
            "multiplicityLossStatus": "notMeasured",
            "homotopyBoundary": "no explicit molecule support means no path multiplicity conclusion"
        })];
    }
    normalized
        .molecules
        .iter()
        .enumerate()
        .map(|(index, molecule)| {
            let holonomy = homotopy["homotopyHolonomyReadings"]
                .as_array()
                .and_then(|items| items.get(index))
                .cloned()
                .unwrap_or(Value::Null);
            let typed_evaluator_result_refs = typed_result_refs(typed_results);
            let homotopy_ref = format!("/homotopyHolonomyReadings/{index}");
            let holonomy_missing = holonomy.is_null();
            let coverage_gap_refs = if holonomy_missing {
                vec![format!(
                    "coverage-gap:path-multiplicity-missing-holonomy:{}",
                    stable_ref(&molecule.normalized_molecule_id)
                )]
            } else {
                json_string_array_value(&holonomy, "coverageGapRefs")
            };
            json!({
                "readingId": format!("path-multiplicity-loss:{}", stable_ref(&molecule.normalized_molecule_id)),
                "measurementStatus": if coverage_gap_refs.is_empty() { "measured" } else { "blockedByCoverageGap" },
                "typedEvaluatorResultRefs": typed_evaluator_result_refs,
                "homotopyHolonomyReadingRef": if holonomy_missing { Value::Null } else { json!(homotopy_ref) },
                "normalizedAtomRefs": molecule.atom_ids,
                "normalizedMoleculeRefs": [molecule.normalized_molecule_id.clone()],
                "observedPathCount": molecule.atom_ids.len(),
                "alternatePathPressure": if molecule.atom_ids.len() > 1 { molecule.atom_ids.len() - 1 } else { 0 },
                "reachabilityForgottenRefs": coverage_gap_refs,
                "coverageGapRefs": coverage_gap_refs,
                "multiplicityLossStatus": if holonomy_missing { "blockedByMissingHolonomyEvidence" } else if holonomy["holonomyStatus"] == "blockedByMissingFiller" { "blockedByMissingFiller" } else { "boundedToExplicitMolecule" },
                "homotopyBoundary": "explicit molecule membership is a bounded path support reading, not global reachability completeness"
            })
        })
        .collect()
}

fn structural_reading_review_summary_v1(structural: &Value) -> Value {
    let surface = &structural["structuralReadingReviewSurface"];
    json!({
        "surfaceRef": "archsig-analysis-packet.json#/structuralReadingReviewSurface",
        "surfacePacketPointer": "/structuralReadingReviewSurface",
        "status": surface["status"],
        "measurementStatus": surface["measurementStatus"],
        "connectedReadingCount": surface["connectedReadingRefs"].as_array().map(Vec::len).unwrap_or_default(),
        "measuredStructuralReadingCount": surface["measuredStructuralReadingCount"],
        "blockedStructuralReadingCount": surface["blockedStructuralReadingCount"],
        "topStructuralReadingRefs": surface["connectedReadingRefs"]
            .as_array()
            .into_iter()
            .flatten()
            .take(8)
            .filter_map(|item| item.as_str().map(str::to_string))
            .collect::<Vec<_>>(),
        "coverageGapRefs": surface["coverageGapRefs"],
        "nonConclusions": surface["nonConclusions"]
    })
}

fn rich_packet_refs_v1(
    architecture_distance: &Value,
    spectrum: &Value,
    homotopy: &Value,
    structural: &Value,
) -> Value {
    json!({
        "schemaVersion": "archsig-rich-packet-refs/v1",
        "distanceDiagnosisDetailRefs": json_string_array_value(&architecture_distance["distanceDiagnosis"], "detailRefs"),
        "spectrumHotspotRefs": packet_refs_from_nested_array(&spectrum["architectureSpectrumReport"], "topHotspots", "architectureSpectrumReport/topHotspots", 8),
        "recurrentObstructionRefs": packet_refs_from_nested_array(&spectrum["architectureSpectrumReport"], "recurrentObstructions", "architectureSpectrumReport/recurrentObstructions", 8),
        "architecturalHoleRefs": packet_refs_from_nested_array(&homotopy["architectureHomotopyReport"], "unfilledLoops", "architectureHomotopyReport/unfilledLoops", 8),
        "nonzeroHolonomyRefs": packet_refs_from_nested_array(&homotopy["architectureHomotopyReport"], "nonzeroHolonomyLoops", "architectureHomotopyReport/nonzeroHolonomyLoops", 8),
        "structuralReadingRefs": structural["structuralReadingReviewSurface"]["connectedReadingRefs"]
            .as_array()
            .into_iter()
            .flatten()
            .take(12)
            .filter_map(|item| item.as_str().map(packet_ref))
            .collect::<Vec<_>>(),
        "structuralSurfaceRef": "packet:/structuralReadingReviewSurface",
        "summaryBoundary": "compact refs only; raw reading arrays remain in the optional analysis packet"
    })
}

fn rich_dominant_findings_v1(spectrum: &Value, homotopy: &Value, structural: &Value) -> Value {
    json!({
        "spectrumHotspots": packet_refs_from_nested_array(&spectrum["architectureSpectrumReport"], "topHotspots", "architectureSpectrumReport/topHotspots", 5),
        "recurrentObstructions": packet_refs_from_nested_array(&spectrum["architectureSpectrumReport"], "recurrentObstructions", "architectureSpectrumReport/recurrentObstructions", 5),
        "architecturalHoles": packet_refs_from_nested_array(&homotopy["architectureHomotopyReport"], "unfilledLoops", "architectureHomotopyReport/unfilledLoops", 5),
        "nonzeroHolonomy": packet_refs_from_nested_array(&homotopy["architectureHomotopyReport"], "nonzeroHolonomyLoops", "architectureHomotopyReport/nonzeroHolonomyLoops", 5),
        "projectionFidelityLoss": packet_refs_from_array(&structural["observationProjectionReadings"], "observationProjectionReadings", 3),
        "synthesisBlockage": packet_refs_from_array(&structural["synthesisBlockageReadings"], "synthesisBlockageReadings", 3),
        "operationPreconditionReadiness": packet_refs_from_array(&structural["operationPreconditionReadinessReadings"], "operationPreconditionReadinessReadings", 3),
        "pathMultiplicityLoss": packet_refs_from_array(&structural["pathMultiplicityLossReadings"], "pathMultiplicityLossReadings", 3),
        "boundary": "dominant findings are compact packet refs, not copied raw readings"
    })
}

fn rich_reading_guide_v1() -> Value {
    json!({
        "schemaVersion": "archsig-rich-reading-guide/v1",
        "readingOrder": [
            "conclusion",
            "distanceDiagnosis",
            "richDominantFindings",
            "architectureSpectrumSummary",
            "architectureHomotopySummary",
            "structuralReadingReviewSummary",
            "actionQueue"
        ],
        "detailPolicy": "open packet refs only for selected findings; summary and viewer do not duplicate raw packet arrays",
        "boundedInterpretation": [
            "read selected evidence before turning a ref into a review finding",
            "blocked rows are review queue items, not measured zero",
            "viewer layout distance is separate from diagnostic distance"
        ]
    })
}

fn rich_action_queue_v1(
    typed_results: &TypedEvaluatorResultsV1,
    spectrum: &Value,
    homotopy: &Value,
    structural: &Value,
) -> Vec<Value> {
    let mut queue = typed_action_queue(typed_results);
    queue.extend(
        packet_refs_from_nested_array(
            &spectrum["architectureSpectrumReport"],
            "topHotspots",
            "architectureSpectrumReport/topHotspots",
            5,
        )
        .into_iter()
        .enumerate()
        .map(|(index, packet_ref)| {
            rich_queue_item(
                "spectrumHotspot",
                index,
                "reviewSpectrumHotspot",
                "selectedSupportPressure",
                vec![packet_ref],
            )
        }),
    );
    queue.extend(
        packet_refs_from_nested_array(
            &homotopy["architectureHomotopyReport"],
            "unfilledLoops",
            "architectureHomotopyReport/unfilledLoops",
            5,
        )
        .into_iter()
        .enumerate()
        .map(|(index, packet_ref)| {
            rich_queue_item(
                "architecturalHole",
                index,
                "reviewMissingFiller",
                "boundedHomotopyGap",
                vec![packet_ref],
            )
        }),
    );
    queue.extend(
        packet_refs_from_nested_array(
            &homotopy["architectureHomotopyReport"],
            "nonzeroHolonomyLoops",
            "architectureHomotopyReport/nonzeroHolonomyLoops",
            5,
        )
        .into_iter()
        .enumerate()
        .map(|(index, packet_ref)| {
            rich_queue_item(
                "nonzeroHolonomy",
                index,
                "reviewNonzeroHolonomy",
                "measuredPathPressure",
                vec![packet_ref],
            )
        }),
    );
    for (kind, field, action_kind, conclusion) in [
        (
            "projectionFidelityLoss",
            "observationProjectionReadings",
            "reviewProjectionReading",
            "boundedProjectionReview",
        ),
        (
            "synthesisBlockage",
            "synthesisBlockageReadings",
            "reviewSynthesisBlockage",
            "boundedSynthesisReview",
        ),
        (
            "operationPreconditionReadiness",
            "operationPreconditionReadinessReadings",
            "reviewOperationPrecondition",
            "boundedRepairReadinessReview",
        ),
        (
            "pathMultiplicityLoss",
            "pathMultiplicityLossReadings",
            "reviewPathMultiplicity",
            "boundedPathMultiplicityReview",
        ),
    ] {
        queue.extend(
            packet_refs_from_array(&structural[field], field, 3)
                .into_iter()
                .enumerate()
                .map(|(index, packet_ref)| {
                    rich_queue_item(kind, index, action_kind, conclusion, vec![packet_ref])
                }),
        );
    }
    queue
}

fn rich_action_queue_summary_v1(
    typed_results: &TypedEvaluatorResultsV1,
    spectrum: &Value,
    homotopy: &Value,
    structural: &Value,
) -> Value {
    let queue = rich_action_queue_v1(typed_results, spectrum, homotopy, structural);
    json!({
        "queueItemCount": queue.len(),
        "topActionKinds": queue
            .iter()
            .take(10)
            .filter_map(|item| item["actionKind"].as_str().map(str::to_string))
            .collect::<Vec<_>>(),
        "topDetailRefs": queue
            .iter()
            .flat_map(|item| json_string_array_value(item, "detailRefs"))
            .take(12)
            .collect::<Vec<_>>(),
        "boundary": "LLM should inspect packet refs before converting queue items into review comments"
    })
}

fn rich_queue_item(
    kind: &str,
    index: usize,
    action_kind: &str,
    conclusion: &str,
    detail_refs: Vec<String>,
) -> Value {
    json!({
        "actionId": format!("action:{kind}:{index}"),
        "kind": kind,
        "actionKind": action_kind,
        "conclusion": conclusion,
        "detailRefs": detail_refs,
        "boundary": "compact rich output ref; inspect packet detail before source-level conclusion"
    })
}

fn packet_refs_from_array(value: &Value, field: &str, limit: usize) -> Vec<String> {
    value
        .as_array()
        .into_iter()
        .flat_map(|items| {
            items
                .iter()
                .enumerate()
                .take(limit)
                .map(move |(index, _)| format!("packet:/{field}/{index}"))
        })
        .collect()
}

fn packet_refs_from_nested_array(
    value: &Value,
    field: &str,
    packet_path: &str,
    limit: usize,
) -> Vec<String> {
    value[field]
        .as_array()
        .into_iter()
        .flat_map(|items| {
            items
                .iter()
                .enumerate()
                .take(limit)
                .map(move |(index, _)| format!("packet:/{packet_path}/{index}"))
        })
        .collect()
}

fn packet_ref(pointer: &str) -> String {
    format!("packet:{pointer}")
}

fn structural_blocked_row(
    reading_id: &str,
    measurement_status: &str,
    normalized: &NormalizedArchMapV1,
    typed_results: &TypedEvaluatorResultsV1,
    coverage_gap_refs: &[String],
) -> Value {
    json!({
        "readingId": reading_id,
        "measurementStatus": measurement_status,
        "typedEvaluatorResultRefs": typed_result_refs(typed_results),
        "normalizedAtomRefs": normalized_atom_ids(normalized),
        "normalizedMoleculeRefs": normalized_molecule_ids(normalized),
        "coverageGapRefs": coverage_gap_refs,
        "evidenceBoundary": "blocked structural row is not measured zero"
    })
}

fn typed_result_refs(typed_results: &TypedEvaluatorResultsV1) -> Vec<String> {
    (0..typed_results.results.len())
        .map(|index| format!("/typedEvaluatorResults/{index}"))
        .collect()
}

fn normalized_atom_ids(normalized: &NormalizedArchMapV1) -> Vec<String> {
    normalized
        .atoms
        .iter()
        .map(|atom| atom.normalized_atom_id.clone())
        .collect()
}

fn normalized_molecule_ids(normalized: &NormalizedArchMapV1) -> Vec<String> {
    normalized
        .molecules
        .iter()
        .map(|molecule| molecule.normalized_molecule_id.clone())
        .collect()
}

fn structural_coverage_gap_refs(typed_results: &TypedEvaluatorResultsV1) -> Vec<String> {
    typed_results
        .results
        .iter()
        .enumerate()
        .filter(|(_, result)| {
            result.status != "measuredPass" && result.status != "measuredViolation"
        })
        .map(|(index, result)| {
            result
                .blocker_reason
                .as_ref()
                .map(|reason| {
                    format!(
                        "coverage-gap:typed-evaluator:{index}:{}",
                        stable_ref(reason)
                    )
                })
                .unwrap_or_else(|| format!("coverage-gap:typed-evaluator:{index}"))
        })
        .collect()
}

fn normalized_axis_counts(normalized: &NormalizedArchMapV1) -> Value {
    let mut counts = serde_json::Map::new();
    for atom in &normalized.atoms {
        let count = counts
            .get(&atom.axis)
            .and_then(Value::as_u64)
            .unwrap_or_default()
            + 1;
        counts.insert(atom.axis.clone(), json!(count));
    }
    Value::Object(counts)
}

fn layer_status(axis_counts: &Value, axis: &str) -> &'static str {
    if axis_counts[axis].as_u64().unwrap_or_default() > 0 {
        "observedWithinSelectedArchMap"
    } else {
        "unmeasuredWithinSelectedArchMap"
    }
}

fn atoms_by_axis_or_kind(
    normalized: &NormalizedArchMapV1,
    axes: &[&str],
    kinds: &[&str],
) -> Vec<String> {
    normalized
        .atoms
        .iter()
        .filter(|atom| {
            axes.contains(&atom.axis.as_str()) || kinds.contains(&atom.atom_kind.as_str())
        })
        .map(|atom| atom.normalized_atom_id.clone())
        .collect()
}

fn state_effect_law_evaluations(blocked: bool) -> Vec<Value> {
    [
        "stateTransitionRelation",
        "commutativity",
        "idempotency",
        "replaySafety",
        "orderingPreservation",
        "invariantPreservation",
    ]
    .into_iter()
    .map(|axis| {
        json!({
            "lawAxis": axis,
            "status": if blocked { "blocked" } else { "observed" },
            "requiredInputRefs": Vec::<String>::new(),
            "observedInputRefs": Vec::<String>::new(),
            "blockedReasonRefs": if blocked { vec![format!("coverage-gap:state-transition-axis:{}", stable_ref(axis))] } else { Vec::new() },
            "reading": "state/effect law axis is bounded to normalized v1 support"
        })
    })
    .collect()
}

fn molecule_atoms<'a>(
    normalized: &'a NormalizedArchMapV1,
    molecule: &NormalizedMoleculeV1,
) -> Vec<&'a NormalizedAtomV1> {
    molecule
        .atom_ids
        .iter()
        .filter_map(|atom_id| {
            normalized
                .atoms
                .iter()
                .find(|atom| &atom.normalized_atom_id == atom_id)
        })
        .collect()
}

fn atom_axes(atoms: &[&NormalizedAtomV1]) -> Vec<String> {
    atoms
        .iter()
        .map(|atom| atom.axis.clone())
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect()
}

fn selected_axis_difference_signal(atoms: &[&NormalizedAtomV1]) -> bool {
    atoms
        .iter()
        .any(|atom| atom.axis == "semantic" || atom.axis == "runtime")
}

fn nonzero_curvature_support_atom_refs(spectrum: &Value) -> BTreeSet<&str> {
    spectrum["curvatureSupportReadings"]
        .as_array()
        .into_iter()
        .flatten()
        .filter(|reading| reading["curvatureValue"]["status"] == "measuredNonzero")
        .flat_map(|reading| {
            reading["witnessRefs"]
                .as_array()
                .into_iter()
                .flatten()
                .filter_map(Value::as_str)
        })
        .collect()
}

fn nonzero_curvature_support_molecule_refs(spectrum: &Value) -> BTreeSet<&str> {
    spectrum["curvatureSupportReadings"]
        .as_array()
        .into_iter()
        .flatten()
        .filter(|reading| reading["curvatureValue"]["status"] == "measuredNonzero")
        .flat_map(|reading| {
            reading["moleculeRefs"]
                .as_array()
                .into_iter()
                .flatten()
                .filter_map(Value::as_str)
        })
        .collect()
}

fn nonzero_curvature_support_refs_for_molecule(
    spectrum: &Value,
    molecule: &NormalizedMoleculeV1,
    nonzero_support_molecule_refs: &BTreeSet<&str>,
    nonzero_support_atom_refs: &BTreeSet<&str>,
) -> Vec<String> {
    if !nonzero_support_molecule_refs.contains(molecule.normalized_molecule_id.as_str())
        && !molecule
            .atom_ids
            .iter()
            .any(|atom_id| nonzero_support_atom_refs.contains(atom_id.as_str()))
    {
        return Vec::new();
    }
    spectrum["curvatureSupportReadings"]
        .as_array()
        .into_iter()
        .flatten()
        .enumerate()
        .filter(|(_, reading)| {
            reading["curvatureValue"]["status"] == "measuredNonzero"
                && (json_string_array_value(reading, "moleculeRefs")
                    .iter()
                    .any(|reference| reference == &molecule.normalized_molecule_id)
                    || json_string_array_value(reading, "witnessRefs")
                        .iter()
                        .any(|reference| molecule.atom_ids.contains(reference)))
        })
        .map(|(index, _)| format!("/curvatureSupportReadings/{index}"))
        .collect()
}

fn spectrum_measurement_status(result: &TypedEvaluatorResultV1) -> &'static str {
    match result.status.as_str() {
        "measuredPass" | "measuredViolation" => "measured",
        "blocked" | "unknown" | "unmeasured" => "blockedByCoverageGap",
        _ => "unknown",
    }
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

fn packet_nested_array_len(packet: &Value, path: &[&str]) -> usize {
    let mut value = packet;
    for field in path {
        value = &value[*field];
    }
    value.as_array().map(Vec::len).unwrap_or_default()
}

fn derived_packet_refs(packet: &Value) -> Vec<String> {
    [
        "generatedLawInputs",
        "part4DistanceCoverageLedger",
        "signatureAxes",
        "generatedObstructions",
        "generatedRepairTargets",
        "curvatureSupportReadings",
        "curvatureTransferReadings",
        "curvatureMassReadings",
        "spectralAnalysisReadings",
        "spectralModeReadings",
        "spectralDrilldownReadings",
        "pathHomotopyDiagramReadings",
        "homotopyHolonomyReadings",
        "stokesStyleReadings",
        "homotopyDistanceReadings",
        "representationMetricReadings",
        "localCurvatureDiagramReadings",
        "threeLayerFlatnessReadings",
        "observationProjectionReadings",
        "stateTransitionAlgebraReadings",
        "effectRelationAlgebraReadings",
        "synthesisBlockageReadings",
        "operationPreconditionReadinessReadings",
        "pathMultiplicityLossReadings",
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
        "part4DistanceCoverageLedger",
        "ledgerEntryId",
        "part4DistanceCoverageLedger",
    ));
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
    entries.extend(derived_detail_entries_for_field(
        packet,
        "curvatureSupportReadings",
        "readingId",
        "curvatureSupportReadings",
    ));
    entries.extend(derived_detail_entries_for_field(
        packet,
        "curvatureTransferReadings",
        "readingId",
        "curvatureTransferReadings",
    ));
    entries.extend(derived_detail_entries_for_field(
        packet,
        "curvatureMassReadings",
        "curvatureMassReadingId",
        "curvatureMassReadings",
    ));
    entries.extend(derived_detail_entries_for_field(
        packet,
        "spectralAnalysisReadings",
        "spectralReadingId",
        "spectralAnalysisReadings",
    ));
    entries.extend(derived_detail_entries_for_field(
        packet,
        "spectralModeReadings",
        "spectralModeId",
        "spectralModeReadings",
    ));
    entries.extend(derived_detail_entries_for_field(
        packet,
        "spectralDrilldownReadings",
        "drilldownId",
        "spectralDrilldownReadings",
    ));
    entries.extend(derived_detail_entries_for_nested_array(
        packet,
        &["architectureSpectrumReport", "topHotspots"],
        "hotspotId",
        "architectureSpectrumReport.topHotspots",
        "packet:/architectureSpectrumReport/topHotspots",
    ));
    entries.extend(derived_detail_entries_for_nested_array(
        packet,
        &["architectureSpectrumReport", "recurrentObstructions"],
        "modeId",
        "architectureSpectrumReport.recurrentObstructions",
        "packet:/architectureSpectrumReport/recurrentObstructions",
    ));
    entries.extend(derived_detail_entries_for_field(
        packet,
        "pathHomotopyDiagramReadings",
        "pathHomotopyDiagramReadingId",
        "pathHomotopyDiagramReadings",
    ));
    entries.extend(derived_detail_entries_for_field(
        packet,
        "homotopyHolonomyReadings",
        "holonomyReadingId",
        "homotopyHolonomyReadings",
    ));
    entries.extend(derived_detail_entries_for_field(
        packet,
        "stokesStyleReadings",
        "stokesReadingId",
        "stokesStyleReadings",
    ));
    entries.extend(derived_detail_entries_for_field(
        packet,
        "homotopyDistanceReadings",
        "homotopyDistanceReadingId",
        "homotopyDistanceReadings",
    ));
    entries.extend(derived_detail_entries_for_nested_array(
        packet,
        &["architectureHomotopyReport", "filledLoops"],
        "loopId",
        "architectureHomotopyReport.filledLoops",
        "packet:/architectureHomotopyReport/filledLoops",
    ));
    entries.extend(derived_detail_entries_for_nested_array(
        packet,
        &["architectureHomotopyReport", "unfilledLoops"],
        "loopId",
        "architectureHomotopyReport.unfilledLoops",
        "packet:/architectureHomotopyReport/unfilledLoops",
    ));
    entries.extend(derived_detail_entries_for_nested_array(
        packet,
        &["architectureHomotopyReport", "nonzeroHolonomyLoops"],
        "loopId",
        "architectureHomotopyReport.nonzeroHolonomyLoops",
        "packet:/architectureHomotopyReport/nonzeroHolonomyLoops",
    ));
    for field in [
        "representationMetricReadings",
        "localCurvatureDiagramReadings",
        "threeLayerFlatnessReadings",
        "observationProjectionReadings",
        "stateTransitionAlgebraReadings",
        "effectRelationAlgebraReadings",
        "synthesisBlockageReadings",
        "operationPreconditionReadinessReadings",
        "pathMultiplicityLossReadings",
    ] {
        entries.extend(derived_detail_entries_for_field(
            packet,
            field,
            "readingId",
            field,
        ));
    }
    entries.extend(derived_detail_entries_for_string_nested_array(
        packet,
        &["structuralReadingReviewSurface", "connectedReadingRefs"],
        "structuralReadingReviewSurface.connectedReadingRefs",
        "packet:/structuralReadingReviewSurface/connectedReadingRefs",
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
                    "typedEvaluatorResultRefs": item["typedEvaluatorResultRefs"],
                    "normalizedAtomRefs": item["normalizedAtomRefs"],
                    "normalizedMoleculeRefs": item["normalizedMoleculeRefs"],
                    "coverageGapRefs": item["coverageGapRefs"],
                    "generatedLawInputRef": item["generatedLawInputRef"],
                    "signatureAxisRef": item["signatureAxisRef"],
                    "generatedObstructionRef": item["generatedObstructionRef"],
                    "homotopyHolonomyReadingRef": item["homotopyHolonomyReadingRef"],
                    "status": item["status"],
                    "localStatus": item["localStatus"],
                    "measurementStatus": item["measurementStatus"],
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

fn derived_detail_entries_for_nested_array(
    packet: &Value,
    path: &[&str],
    id_field: &str,
    namespace: &str,
    packet_ref_prefix: &str,
) -> Vec<Value> {
    let mut value = packet;
    for field in path {
        value = &value[*field];
    }
    value
        .as_array()
        .into_iter()
        .flat_map(|items| {
            items.iter().enumerate().map(move |(index, item)| {
                let fallback_id = format!("{namespace}:{index}");
                let id = item[id_field].as_str().unwrap_or(&fallback_id);
                json!({
                    "resultRef": format!("{namespace}:{id}"),
                    "packetRef": format!("{packet_ref_prefix}/{index}"),
                    "supportReadingRef": item["supportReadingRef"],
                    "transferEdgeRefs": item["transferEdgeRefs"],
                    "supportRefs": item["supportRefs"],
                    "witnessRefs": item["witnessRefs"],
                    "coverageGapRefs": item["coverageGapRefs"]
                })
            })
        })
        .collect()
}

fn derived_detail_entries_for_string_nested_array(
    packet: &Value,
    path: &[&str],
    namespace: &str,
    packet_ref_prefix: &str,
) -> Vec<Value> {
    let mut value = packet;
    for field in path {
        value = &value[*field];
    }
    value
        .as_array()
        .into_iter()
        .flat_map(|items| {
            items.iter().enumerate().filter_map(move |(index, item)| {
                item.as_str().map(|reference| {
                    json!({
                        "resultRef": format!("{namespace}:{index}"),
                        "packetRef": format!("{packet_ref_prefix}/{index}"),
                        "connectedReadingRef": reference
                    })
                })
            })
        })
        .collect()
}

fn json_string_array_value(value: &Value, field: &str) -> Vec<String> {
    value[field]
        .as_array()
        .into_iter()
        .flatten()
        .filter_map(|item| item.as_str().map(str::to_string))
        .collect()
}

fn unique_string_values(values: impl Iterator<Item = String>) -> Vec<String> {
    values.collect::<BTreeSet<_>>().into_iter().collect()
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

fn architecture_distance_bundle_matches_packet(packet: &Value) -> bool {
    let architecture_distance = &packet["architectureDistance"];
    let Some(family_summaries) = architecture_distance["familySummaries"].as_array() else {
        return false;
    };
    let Some(ledger) = packet["part4DistanceCoverageLedger"].as_array() else {
        return false;
    };
    if family_summaries.len() != ledger.len() || family_summaries.len() != 10 {
        return false;
    }
    if architecture_distance["measurementStateSummary"]["familyCount"].as_u64()
        != Some(family_summaries.len() as u64)
    {
        return false;
    }
    if architecture_distance["measurementStateSummary"]["missingCanonicalFamilyCount"].as_u64()
        != Some(0)
    {
        return false;
    }
    if !architecture_distance["primaryInsightsRefs"]
        .as_array()
        .is_some_and(|refs| !refs.is_empty())
    {
        return false;
    }
    let scope = &architecture_distance["summary"]["measuredTotalScope"];
    if scope["scope"].as_str() != Some("aggregated architecture-distance-point families only")
        || !scope["includedFamilies"]
            .as_array()
            .is_some_and(|families| {
                [
                    "atomGeometry",
                    "configurationGeometry",
                    "signatureGeometry",
                    "operationGeometry",
                ]
                .iter()
                .all(|family| families.iter().any(|value| value == family))
            })
        || !scope["nonAggregatedFamilies"]
            .as_array()
            .is_some_and(|families| {
                [
                    "foundation",
                    "curvatureGeometry",
                    "homotopyFillingGeometry",
                    "representationMetric",
                    "measurementBoundary",
                    "boundedDiagnosticConclusion",
                ]
                .iter()
                .all(|family| families.iter().any(|value| value == family))
            })
    {
        return false;
    }

    family_summaries
        .iter()
        .zip(ledger.iter())
        .enumerate()
        .all(|(index, (summary, entry))| {
            summary["ledgerEntryId"] == entry["ledgerEntryId"]
                && summary["distanceFamily"] == entry["distanceFamily"]
                && summary["coverageStatus"] == entry["coverageStatus"]
                && summary["measurementStatus"] == entry["measurementStatus"]
                && summary["readingCount"] == entry["readingCount"]
                && summary["rawPacketRefs"] == entry["rawPacketRefs"]
                && summary["sourceLedgerRef"]
                    == format!("packet:/part4DistanceCoverageLedger/{index}")
                && summary["primaryArtifactRefs"]
                    .as_array()
                    .is_some_and(|refs| {
                        refs.iter().any(|reference| {
                            reference
                                == &json!(format!(
                                    "architecture-distance.json#/familySummaries/{index}"
                                ))
                        })
                    })
        })
}

fn typed_violation_detected(
    entry: &crate::ExpandedLawPolicyEntryV1,
    support_atoms: &[&NormalizedAtomV1],
) -> bool {
    match entry.law.as_str() {
        "domain.no-direct-infra-dependency" => support_atoms
            .iter()
            .filter(|atom| atom_has_predicate_name(atom, "dependsOn"))
            .any(|atom| {
                let subject = binding_value(atom, "subject");
                let object = binding_value(atom, "object");
                subject.is_some_and(is_domain_ref) && object.is_some_and(is_infrastructure_ref)
            }),
        "solid.dependency-inversion" => support_atoms
            .iter()
            .filter(|atom| atom_has_predicate_name(atom, "dependsOn"))
            .any(|atom| {
                let object = binding_value(atom, "object");
                object.is_some_and(is_concrete_infrastructure_ref)
            }),
        _ => false,
    }
}

fn atom_has_predicate_name(atom: &NormalizedAtomV1, name: &str) -> bool {
    atom.predicate.constructor == name
        || atom
            .predicate
            .bindings
            .iter()
            .any(|binding| binding.role == "predicate" && binding.value == name)
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
                let part4_definition_readings =
                    atom_part4_definition_readings(left, right, molecule, profile);
                let measured_value = part4_definition_readings
                    .iter()
                    .filter_map(|component| component["measuredValue"].as_i64())
                    .sum::<i64>();
                let blocked_definition_refs = part4_definition_readings
                    .iter()
                    .filter(|component| component["status"] != "measured")
                    .map(|component| component["definitionRef"].clone())
                    .collect::<Vec<_>>();
                let blocker_refs = part4_definition_readings
                    .iter()
                    .flat_map(|component| {
                        component["blockerRefs"]
                            .as_array()
                            .into_iter()
                            .flatten()
                            .cloned()
                    })
                    .collect::<Vec<_>>();
                let atom_reading_status = if blocked_definition_refs.is_empty() {
                    "measured"
                } else {
                    "partial"
                };
                let atom_layout_distance = json!({
                    "definitionRef": "definitions:2.5",
                    "definitionName": "Atom Layout Distance",
                    "status": atom_reading_status,
                    "measuredValue": if atom_reading_status == "measured" {
                        json!(measured_value)
                    } else {
                        Value::Null
                    },
                    "unit": "architecture-distance-point",
                    "componentRefs": part4_definition_readings
                        .iter()
                        .filter_map(|component| component["definitionRef"].as_str())
                        .collect::<Vec<_>>(),
                    "blockedDefinitionRefs": blocked_definition_refs,
                    "blockerRefs": blocker_refs,
                    "evaluatorBasisRefs": [
                        "normalizedAtom.atomKind",
                        "normalizedAtom.predicate",
                        "normalizedAtom.valenceTemplateId",
                        "normalizedAtom.moleculeMemberships"
                    ],
                    "reading": "Atom layout distance composes measured Fiber, Carrier, Valence, and Semantic Anchor distance rows for this explicit atom pair"
                });
                readings.push(json!({
                    "readingId": format!("atom-distance:{}:{}", stable_ref(left_id), stable_ref(right_id)),
                    "distanceFamily": "atomGeometry",
                    "status": atom_reading_status,
                    "measuredValue": if atom_reading_status == "measured" {
                        json!(measured_value)
                    } else {
                        Value::Null
                    },
                    "unit": "architecture-distance-point",
                    "sourceAtomRef": left_id,
                    "targetAtomRef": right_id,
                    "moleculeRef": molecule.normalized_molecule_id,
                    "blockerReason": if atom_reading_status == "measured" {
                        Value::Null
                    } else {
                        json!("one or more atom geometry definition rows are blocked")
                    },
                    "blockerRefs": atom_layout_distance["blockerRefs"],
                    "blockedDefinitionRefs": atom_layout_distance["blockedDefinitionRefs"],
                    "part4DefinitionReadings": part4_definition_readings,
                    "atomLayoutDistance": atom_layout_distance,
                    "components": atom_distance_components(left, right, profile),
                    "detailRefs": [left_id, right_id, &molecule.normalized_molecule_id]
                }));
            }
        }
    }
    readings
}

fn atom_part4_definition_readings(
    left: &NormalizedAtomV1,
    right: &NormalizedAtomV1,
    molecule: &NormalizedMoleculeV1,
    profile: ArchitectureDistanceProfileV1,
) -> Vec<Value> {
    let left_carriers = binding_values(left);
    let right_carriers = binding_values(right);
    let left_memberships = left
        .molecule_memberships
        .iter()
        .cloned()
        .collect::<BTreeSet<_>>();
    let right_memberships = right
        .molecule_memberships
        .iter()
        .cloned()
        .collect::<BTreeSet<_>>();
    let membership_delta = left_memberships
        .symmetric_difference(&right_memberships)
        .count() as i64;
    let valence_template_delta = if left.valence_template_id == right.valence_template_id {
        0
    } else {
        profile.axis_weight
    };
    let valence_value = valence_template_delta + membership_delta * profile.axis_weight;
    let semantic_anchor_status = if left_carriers.is_empty() || right_carriers.is_empty() {
        "blocked"
    } else {
        "measured"
    };
    let semantic_anchor_value = if semantic_anchor_status == "measured" {
        binding_distance(left, right) * profile.predicate_binding_weight
    } else {
        0
    };
    vec![
        json!({
            "definitionRef": "definitions:2.1",
            "definitionName": "Fiber Distance",
            "componentKind": "fiber",
            "status": "measured",
            "measuredValue": if left.atom_kind == right.atom_kind { 0 } else { profile.atom_kind_weight },
            "unit": "architecture-distance-point",
            "leftFiber": {
                "base": left.atom_kind,
                "payload": left.predicate.constructor
            },
            "rightFiber": {
                "base": right.atom_kind,
                "payload": right.predicate.constructor
            },
            "evaluatorBasisRefs": ["normalizedAtom.atomKind", "normalizedAtom.predicate.constructor"],
            "sourceRefs": [left.normalized_atom_id.clone(), right.normalized_atom_id.clone()]
        }),
        json!({
            "definitionRef": "definitions:2.2",
            "definitionName": "Carrier Distance",
            "componentKind": "carrier",
            "status": "measured",
            "measuredValue": carrier_distance(left, right) * profile.predicate_binding_weight,
            "unit": "architecture-distance-point",
            "leftCarrierRefs": left_carriers,
            "rightCarrierRefs": right_carriers,
            "evaluatorBasisRefs": ["normalizedAtom.predicate.bindings"],
            "sourceRefs": [left.normalized_atom_id.clone(), right.normalized_atom_id.clone()]
        }),
        json!({
            "definitionRef": "definitions:2.3",
            "definitionName": "Valence Distance",
            "componentKind": "valence",
            "status": "measured",
            "measuredValue": valence_value,
            "unit": "architecture-distance-point",
            "leftValenceTemplateRef": left.valence_template_id,
            "rightValenceTemplateRef": right.valence_template_id,
            "sharedMoleculeRef": molecule.normalized_molecule_id,
            "leftMoleculeMembershipRefs": left.molecule_memberships,
            "rightMoleculeMembershipRefs": right.molecule_memberships,
            "evaluatorBasisRefs": ["normalizedAtom.valenceTemplateId", "normalizedAtom.moleculeMemberships"],
            "sourceRefs": [left.normalized_atom_id.clone(), right.normalized_atom_id.clone(), molecule.normalized_molecule_id.clone()]
        }),
        json!({
            "definitionRef": "definitions:2.4",
            "definitionName": "Semantic Anchor Distance",
            "componentKind": "semanticAnchor",
            "status": semantic_anchor_status,
            "measuredValue": if semantic_anchor_status == "measured" {
                json!(semantic_anchor_value)
            } else {
                Value::Null
            },
            "unit": "architecture-distance-point",
            "leftSemanticAnchorRefs": binding_values(left),
            "rightSemanticAnchorRefs": binding_values(right),
            "blockerRefs": if semantic_anchor_status == "blocked" {
                vec![format!(
                    "missingSemanticAnchor:{}:{}",
                    stable_ref(&left.normalized_atom_id),
                    stable_ref(&right.normalized_atom_id)
                )]
            } else {
                Vec::new()
            },
            "evaluatorBasisRefs": ["normalizedAtom.predicate.bindings"],
            "sourceRefs": [left.normalized_atom_id.clone(), right.normalized_atom_id.clone()],
            "evidenceBoundary": "missing semantic anchor blocks this definition row instead of becoming measured zero"
        }),
    ]
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

fn carrier_distance(left: &NormalizedAtomV1, right: &NormalizedAtomV1) -> i64 {
    binding_distance(left, right)
}

fn architecture_configuration_distance_readings(
    normalized: &NormalizedArchMapV1,
    profile: ArchitectureDistanceProfileV1,
) -> Vec<Value> {
    let atoms_by_id = normalized
        .atoms
        .iter()
        .map(|atom| (atom.normalized_atom_id.as_str(), atom))
        .collect::<BTreeMap<_, _>>();
    let mut readings = normalized
        .molecules
        .iter()
        .map(|molecule| configuration_distance_reading(molecule, &atoms_by_id, profile))
        .collect::<Vec<_>>();
    add_molecule_contribution_rates(&mut readings);
    readings
}

fn configuration_distance_reading(
    molecule: &NormalizedMoleculeV1,
    atoms_by_id: &BTreeMap<&str, &NormalizedAtomV1>,
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
    if molecule.atom_ids.len() < 2 {
        return blocked_distance_reading(
            "configurationDistance",
            &format!(
                "configuration-distance:{}",
                stable_ref(&molecule.normalized_molecule_id)
            ),
            "configuration requires at least two distinct atom refs for indexed distance",
            vec![molecule.normalized_molecule_id.clone()],
        );
    }
    for atom_id in &molecule.atom_ids {
        if !atoms_by_id.contains_key(atom_id.as_str()) {
            return blocked_distance_reading(
                "configurationDistance",
                &format!(
                    "configuration-distance:{}",
                    stable_ref(&molecule.normalized_molecule_id)
                ),
                "configuration atom ref is missing from normalized ArchMap",
                vec![molecule.normalized_molecule_id.clone(), atom_id.clone()],
            );
        }
    }
    let hyperedge_ref = format!(
        "configuration-hyperedge:{}",
        stable_ref(&molecule.normalized_molecule_id)
    );
    let hypergraph_ref = format!(
        "configuration-hypergraph:{}",
        stable_ref(&molecule.normalized_molecule_id)
    );
    let selected_pair_distances = configuration_selected_pair_distances(
        molecule,
        atoms_by_id,
        profile,
        &hyperedge_ref,
        &hypergraph_ref,
    );
    let indexed_total = selected_pair_distances
        .iter()
        .filter_map(|pair| pair["configurationIndexedDistance"]["measuredValue"].as_i64())
        .sum::<i64>();
    let context_total = selected_pair_distances
        .iter()
        .filter_map(|pair| pair["contextDistance"]["measuredValue"].as_i64())
        .sum::<i64>();
    let configuration_indexed_distance = json!({
        "definitionRef": "definitions:3.1",
        "definitionName": "Configuration-Indexed Distance",
        "status": "measured",
        "measuredValue": indexed_total,
        "unit": "configuration-hop",
        "selectedPairCount": selected_pair_distances.len(),
        "selectedPairRefs": selected_pair_distances
            .iter()
            .map(|pair| pair["pairRef"].clone())
            .collect::<Vec<_>>(),
        "typedHypergraphRefs": [hypergraph_ref.clone()],
        "evaluatorBasisRefs": ["normalizedMolecule.atomIds", "explicitMoleculeMembership"],
        "reading": "configuration-indexed distance aggregates shortest paths for every explicit atom pair selected by molecule membership"
    });
    let context_distance = json!({
        "definitionRef": "definitions:3.2",
        "definitionName": "Context Distance",
        "status": "measured",
        "measuredValue": context_total,
        "unit": "configuration-context-gap",
        "selectedPairCount": selected_pair_distances.len(),
        "selectedPairRefs": selected_pair_distances
            .iter()
            .map(|pair| pair["pairRef"].clone())
            .collect::<Vec<_>>(),
        "evaluatorBasisRefs": ["normalizedAtom.moleculeMemberships"],
        "reading": "context distance aggregates explicit molecule membership overlap for every selected atom pair"
    });
    let measured_value = indexed_total + context_total;
    let configuration_distance_bundle = json!({
        "status": "measured",
        "measuredValue": measured_value,
        "unit": "architecture-distance-point",
        "componentRefs": [
            "configurationIndexedDistance",
            "contextDistance"
        ],
        "blockerRefs": [],
        "evaluatorBasisRefs": [
            "normalizedMolecule.atomIds",
            "normalizedAtom.moleculeMemberships"
        ],
        "reading": "configuration bundle combines typed hypergraph shortest path and molecule context overlap"
    });
    json!({
        "readingId": format!("configuration-distance:{}", stable_ref(&molecule.normalized_molecule_id)),
        "distanceFamily": "configurationGeometry",
        "status": "measured",
        "measuredValue": measured_value,
        "unit": "architecture-distance-point",
        "moleculeRef": molecule.normalized_molecule_id,
        "atomCount": molecule.atom_ids.len(),
        "selectedPairCount": selected_pair_distances.len(),
        "weight": profile.configuration_atom_weight,
        "basis": "all explicit atom-pair shortest paths plus molecule context overlap",
        "typedHypergraph": {
            "configurationRef": molecule.normalized_molecule_id,
            "nodeRefs": molecule.atom_ids,
            "hyperedgeRefs": [hyperedge_ref],
            "hyperedges": [{
                "hyperedgeKind": "explicitMoleculeMembership",
                "atomRefs": molecule.atom_ids,
                "sourceMoleculeRef": molecule.normalized_molecule_id
            }]
        },
        "selectedPairDistances": selected_pair_distances,
        "configurationIndexedDistance": configuration_indexed_distance,
        "contextDistance": context_distance,
        "configurationDistanceBundle": configuration_distance_bundle,
        "sourceRefs": std::iter::once(molecule.source_molecule_id.clone())
            .chain(molecule.atom_ids.iter().cloned())
            .collect::<Vec<_>>(),
        "detailRefs": std::iter::once(molecule.normalized_molecule_id.clone())
            .chain(molecule.atom_ids.iter().cloned())
            .collect::<Vec<_>>()
    })
}

fn add_molecule_contribution_rates(readings: &mut [Value]) {
    let total = readings
        .iter()
        .filter_map(|reading| reading["measuredValue"].as_i64())
        .sum::<i64>();
    for reading in readings {
        let value = reading["measuredValue"].as_i64().unwrap_or(0);
        reading["moleculeContributionRate"] = if total > 0 {
            json!({
                "numerator": value,
                "denominator": total,
                "ratio": value as f64 / total as f64
            })
        } else {
            Value::Null
        };
    }
}

fn configuration_selected_pair_distances(
    molecule: &NormalizedMoleculeV1,
    atoms_by_id: &BTreeMap<&str, &NormalizedAtomV1>,
    profile: ArchitectureDistanceProfileV1,
    hyperedge_ref: &str,
    hypergraph_ref: &str,
) -> Vec<Value> {
    let mut pairs = Vec::new();
    for left_index in 0..molecule.atom_ids.len() {
        for right_index in (left_index + 1)..molecule.atom_ids.len() {
            let left_ref = &molecule.atom_ids[left_index];
            let right_ref = &molecule.atom_ids[right_index];
            let Some(left_atom) = atoms_by_id.get(left_ref.as_str()) else {
                continue;
            };
            let Some(right_atom) = atoms_by_id.get(right_ref.as_str()) else {
                continue;
            };
            let left_memberships = left_atom
                .molecule_memberships
                .iter()
                .cloned()
                .collect::<BTreeSet<_>>();
            let right_memberships = right_atom
                .molecule_memberships
                .iter()
                .cloned()
                .collect::<BTreeSet<_>>();
            let shared_contexts = left_memberships
                .intersection(&right_memberships)
                .cloned()
                .collect::<Vec<_>>();
            let union_contexts = left_memberships
                .union(&right_memberships)
                .cloned()
                .collect::<Vec<_>>();
            let context_gap = union_contexts.len().saturating_sub(shared_contexts.len()) as i64;
            pairs.push(json!({
                "pairRef": format!(
                    "configuration-pair:{}:{}",
                    stable_ref(left_ref),
                    stable_ref(right_ref)
                ),
                "sourceAtomRef": left_ref,
                "targetAtomRef": right_ref,
                "configurationIndexedDistance": {
                    "status": "measured",
                    "measuredValue": profile.configuration_atom_weight,
                    "unit": "configuration-hop",
                    "shortestPathAtomRefs": [left_ref, right_ref],
                    "shortestPathHyperedgeRefs": [hyperedge_ref],
                    "typedHypergraphRefs": [hypergraph_ref],
                    "evaluatorBasisRefs": ["normalizedMolecule.atomIds", "explicitMoleculeMembership"]
                },
                "contextDistance": {
                    "status": "measured",
                    "measuredValue": context_gap * profile.configuration_atom_weight,
                    "unit": "configuration-context-gap",
                    "sourceAtomContextRefs": left_atom.molecule_memberships,
                    "targetAtomContextRefs": right_atom.molecule_memberships,
                    "sharedContextRefs": shared_contexts,
                    "contextUnionRefs": union_contexts,
                    "evaluatorBasisRefs": ["normalizedAtom.moleculeMemberships"]
                },
                "sourceRefs": [
                    molecule.normalized_molecule_id.clone(),
                    left_ref.clone(),
                    right_ref.clone()
                ]
            }));
        }
    }
    pairs
}

fn atom_configuration_primary_insights(
    atom_distance_readings: &[Value],
    configuration_distance_readings: &[Value],
) -> Value {
    let mut atom_pairs = atom_distance_readings
        .iter()
        .filter(|reading| reading["status"] == "measured")
        .filter_map(|reading| {
            let measured_value = reading["measuredValue"].as_i64()?;
            Some(json!({
                "readingRef": reading["readingId"],
                "measuredValue": measured_value,
                "sourceAtomRef": reading["sourceAtomRef"],
                "targetAtomRef": reading["targetAtomRef"],
                "moleculeRef": reading["moleculeRef"],
                "dominantDefinitionRows": top_definition_rows(reading, "part4DefinitionReadings"),
                "atomLayoutDistance": reading["atomLayoutDistance"]
            }))
        })
        .collect::<Vec<_>>();
    atom_pairs.sort_by(|left, right| {
        right["measuredValue"]
            .as_i64()
            .cmp(&left["measuredValue"].as_i64())
    });
    atom_pairs.truncate(5);

    let mut molecules = configuration_distance_readings
        .iter()
        .filter(|reading| reading["status"] == "measured")
        .filter_map(|reading| {
            let measured_value = reading["measuredValue"].as_i64()?;
            Some(json!({
                "readingRef": reading["readingId"],
                "moleculeRef": reading["moleculeRef"],
                "measuredValue": measured_value,
                "selectedPairCount": reading["selectedPairCount"],
                "topSelectedPairDistances": top_configuration_pair_rows(reading),
                "moleculeContributionRate": reading["moleculeContributionRate"],
                "configurationIndexedDistance": reading["configurationIndexedDistance"],
                "contextDistance": reading["contextDistance"],
                "typedHypergraphRef": reading["configurationIndexedDistance"]["typedHypergraphRefs"][0],
                "sourceRefs": reading["sourceRefs"],
                "detailRefs": reading["detailRefs"]
            }))
        })
        .collect::<Vec<_>>();
    molecules.sort_by(|left, right| {
        right["measuredValue"]
            .as_i64()
            .cmp(&left["measuredValue"].as_i64())
    });
    molecules.truncate(5);

    json!({
        "topMovedAtomPairs": atom_pairs,
        "topMovedMolecules": molecules,
        "reading": "atom/configuration insights use canonical definition rows, typed hypergraph shortest paths, and explicit molecule context overlap"
    })
}

fn top_configuration_pair_rows(reading: &Value) -> Vec<Value> {
    let mut rows = reading["selectedPairDistances"]
        .as_array()
        .into_iter()
        .flatten()
        .cloned()
        .collect::<Vec<_>>();
    rows.sort_by(|left, right| {
        let right_value = right["configurationIndexedDistance"]["measuredValue"]
            .as_i64()
            .unwrap_or(0)
            + right["contextDistance"]["measuredValue"]
                .as_i64()
                .unwrap_or(0);
        let left_value = left["configurationIndexedDistance"]["measuredValue"]
            .as_i64()
            .unwrap_or(0)
            + left["contextDistance"]["measuredValue"]
                .as_i64()
                .unwrap_or(0);
        right_value.cmp(&left_value)
    });
    rows.truncate(3);
    rows
}

fn top_definition_rows(reading: &Value, field: &str) -> Vec<Value> {
    let mut rows = reading[field]
        .as_array()
        .into_iter()
        .flatten()
        .filter(|row| row["status"] == "measured")
        .cloned()
        .collect::<Vec<_>>();
    rows.sort_by(|left, right| {
        right["measuredValue"]
            .as_i64()
            .cmp(&left["measuredValue"].as_i64())
    });
    rows.truncate(3);
    rows
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
    signature_distance_readings: &[Value],
) -> Vec<Value> {
    typed_results
        .results
        .iter()
        .filter(|result| operation_distance_result_is_primary(result, profile))
        .map(|result| {
            if result.status == "blocked" {
                return blocked_distance_reading(
                    "operationGeometry",
                    &format!("operation-distance:{}", stable_ref(&result.law)),
                    result
                        .blocker_reason
                        .as_deref()
                        .unwrap_or("operation cannot be selected for blocked evaluator result"),
                    result.detail_refs.clone(),
                );
            }
            let Some(operation) = recommended_operation(&result.law, profile) else {
                return blocked_distance_reading(
                    "operationGeometry",
                    &format!("operation-distance:{}", stable_ref(&result.law)),
                    "operation cost is not declared by the selected DistanceProfile",
                    result.detail_refs.clone(),
                );
            };
            let selected_repair = result.status == "measuredViolation";
            let signature_reading =
                signature_distance_reading_for_law(signature_distance_readings, &result.law);
            let signature_reading_ref = signature_reading
                .and_then(|reading| reading["readingId"].as_str())
                .unwrap_or("unavailable");
            let current_signature_distance = signature_reading
                .and_then(|reading| {
                    (reading["status"] == "measured").then(|| reading["measuredValue"].as_i64())
                })
                .flatten();
            let signature_blocker_refs = if selected_repair && current_signature_distance.is_none()
            {
                vec![format!("missingSignatureDistanceWitness:{}", result.law)]
            } else {
                Vec::new()
            };
            let target_decrease = if selected_repair {
                current_signature_distance
            } else {
                Some(0)
            };
            let distance_to_flat = target_decrease
                .map(|decrease| current_signature_distance.unwrap_or(0).saturating_sub(decrease));
            let transfer_risk_blocker_refs = if selected_repair {
                vec![format!("missingTransferRiskEvidence:{}", result.law)]
            } else {
                Vec::new()
            };
            let row_blocker_refs = signature_blocker_refs
                .iter()
                .cloned()
                .chain(transfer_risk_blocker_refs.iter().cloned())
                .collect::<Vec<_>>();
            let row_status = if row_blocker_refs.is_empty() {
                "measured"
            } else {
                "blocked"
            };
            let measured_value = if row_status == "measured" {
                if selected_repair {
                    Some(operation.cost)
                } else {
                    Some(0)
                }
            } else {
                None
            };
            let repair_route_status = if selected_repair && !transfer_risk_blocker_refs.is_empty() {
                "candidate-blocked-by-missing-transfer-risk-evidence"
            } else if selected_repair {
                "candidate"
            } else {
                "not-required"
            };
            json!({
                "readingId": format!("operation-distance:{}", stable_ref(&result.law)),
                "distanceFamily": "operationGeometry",
                "law": result.law,
                "evaluator": result.evaluator,
                "status": row_status,
                "operationKind": operation.operation_kind,
                "measuredValue": measured_value,
                "unit": "architecture-distance-point",
                "blockerRefs": row_blocker_refs,
                "part4DefinitionReadings": [
                    {
                        "definitionRef": "definitions:5.1",
                        "definitionName": "Operation Cost",
                        "componentKind": "operationCost",
                        "status": "measured",
                        "measuredValue": operation.cost,
                        "unit": "architecture-distance-point",
                        "sourceRef": operation.cost_source_ref,
                        "includedInMeasuredValue": selected_repair,
                        "evaluatorBasisRefs": [
                            format!("operationCost:{}", operation.operation_kind),
                            format!("profile:{}", profile.profile_ref),
                            operation.cost_source_ref
                        ],
                        "reading": "operation cost is selected from the current ArchSig DistanceProfile table"
                    },
                    {
                        "definitionRef": "definitions:5.2",
                        "definitionName": "Operation Distance",
                        "componentKind": "targetDistanceDecrease",
                        "status": if target_decrease.is_some() { "measured" } else { "blocked" },
                        "measuredValue": target_decrease,
                        "unit": "architecture-distance-point",
                        "signatureDistanceReadingRef": signature_reading_ref,
                        "blockerRefs": signature_blocker_refs,
                        "evaluatorBasisRefs": [
                            format!("targetDecrease:{}", result.status),
                            format!("law:{}", result.law),
                            format!("signatureDistanceReading:{signature_reading_ref}")
                        ],
                        "reading": "target decrease is read from the selected signature-distance witness for violations and is zero for an already measured pass"
                    },
                    {
                        "definitionRef": "definitions:5.3",
                        "definitionName": "Distance to Selected Flatness",
                        "componentKind": "distanceToSelectedFlat",
                        "status": if distance_to_flat.is_some() { "measured" } else { "blocked" },
                        "measuredValue": distance_to_flat,
                        "unit": "architecture-distance-point",
                        "signatureDistanceReadingRef": signature_reading_ref,
                        "blockerRefs": signature_blocker_refs,
                        "evaluatorBasisRefs": [
                            format!("selectedFlat:{}", result.law),
                            format!("targetDecrease:{}", target_decrease.unwrap_or(0)),
                            format!("signatureDistanceReading:{signature_reading_ref}")
                        ],
                        "reading": "distance to selected flatness subtracts the target decrease from the selected signature-distance witness and does not claim global flatness"
                    },
                    {
                        "definitionRef": "definitions:5.4",
                        "definitionName": "Repair Route",
                        "componentKind": "repairRoute",
                        "status": repair_route_status,
                        "measuredValue": null,
                        "unit": "route-state",
                        "sourceRefs": result.detail_refs,
                        "preconditionRefs": operation.precondition_refs,
                        "transferRiskRefs": [],
                        "transferRiskBlockerRefs": transfer_risk_blocker_refs,
                        "evaluatorBasisRefs": [
                            format!("repairRoute:{}", operation.operation_kind),
                            format!("lawStatus:{}", result.status)
                        ],
                        "reading": if selected_repair {
                            "selected violation has a diagnostic repair-route candidate, not an automatic safe refactoring"
                        } else {
                            "selected law is already measured pass; route records the maintained boundary and is not a required repair"
                        }
                    },
                    {
                        "definitionRef": "definitions:5.5",
                        "definitionName": "Side-Effect Bound",
                        "componentKind": "sideEffectBound",
                        "status": if transfer_risk_blocker_refs.is_empty() { "measured" } else { "blocked" },
                        "measuredValue": if transfer_risk_blocker_refs.is_empty() { Some(0) } else { None },
                        "unit": "selected-transfer-risk-count",
                        "transferRiskRefs": [],
                        "blockerRefs": transfer_risk_blocker_refs,
                        "evaluatorBasisRefs": [
                            format!("sideEffectBound:{}", operation.operation_kind),
                            "selected-law-axis-only".to_string()
                        ],
                        "reading": "side-effect bound is measured zero only when no repair is selected; selected repair routes require transfer-risk evidence and otherwise remain blocked"
                    }
                ],
                "operationCost": {
                    "status": "measured",
                    "measuredValue": operation.cost,
                    "unit": "architecture-distance-point",
                    "sourceRef": operation.cost_source_ref,
                    "includedInMeasuredValue": selected_repair,
                    "evaluatorBasisRefs": [
                        format!("operationCost:{}", operation.operation_kind),
                        format!("profile:{}", profile.profile_ref)
                    ]
                },
                "targetDistanceDecrease": {
                    "status": if target_decrease.is_some() { "measured" } else { "blocked" },
                    "measuredValue": target_decrease,
                    "unit": "architecture-distance-point",
                    "signatureDistanceReadingRef": signature_reading_ref,
                    "blockerRefs": signature_blocker_refs,
                    "evaluatorBasisRefs": [
                        format!("targetDecrease:{}", result.status),
                        format!("law:{}", result.law),
                        format!("signatureDistanceReading:{signature_reading_ref}")
                    ]
                },
                "distanceToSelectedFlat": {
                    "status": if distance_to_flat.is_some() { "measured" } else { "blocked" },
                    "measuredValue": distance_to_flat,
                    "unit": "architecture-distance-point",
                    "signatureDistanceReadingRef": signature_reading_ref,
                    "blockerRefs": signature_blocker_refs,
                    "evaluatorBasisRefs": [
                        format!("selectedFlat:{}", result.law),
                        format!("targetDecrease:{}", target_decrease.unwrap_or(0)),
                        format!("signatureDistanceReading:{signature_reading_ref}")
                    ]
                },
                "repairRoute": {
                    "status": repair_route_status,
                    "routeKind": operation.operation_kind,
                    "sourceRefs": result.detail_refs,
                    "preconditionRefs": operation.precondition_refs,
                    "transferRiskRefs": [],
                    "transferRiskBlockerRefs": transfer_risk_blocker_refs,
                    "safetyBoundary": "diagnostic route candidate only; ArchSig does not claim automatic repair safety"
                },
                "sideEffectBound": {
                    "status": if transfer_risk_blocker_refs.is_empty() { "measured" } else { "blocked" },
                    "measuredValue": if transfer_risk_blocker_refs.is_empty() { Some(0) } else { None },
                    "unit": "selected-transfer-risk-count",
                    "transferRiskRefs": [],
                    "blockerRefs": transfer_risk_blocker_refs,
                    "evaluatorBasisRefs": [
                        format!("sideEffectBound:{}", operation.operation_kind),
                        "selected-law-axis-only".to_string()
                    ]
                },
                "basis": "operation geometry is resolved from the selected LawPolicy DistanceProfile and typed evaluator result",
                "detailRefs": result.detail_refs,
                "evidenceBoundary": "operation distance is a diagnostic reading over selected law evidence; it is not automatic repair safety and does not generate atoms",
                "nonConclusions": [
                    "Repair route candidates are not automatic safe refactorings.",
                    "Operation distance does not claim that operations generate Atom input.",
                    "Distance to selected flatness is scoped to the selected law axis and evidence contract."
                ]
            })
        })
        .collect()
}

fn signature_distance_reading_for_law<'a>(
    signature_distance_readings: &'a [Value],
    law: &str,
) -> Option<&'a Value> {
    signature_distance_readings
        .iter()
        .find(|reading| reading["law"].as_str() == Some(law))
}

fn operation_distance_result_is_primary(
    result: &TypedEvaluatorResultV1,
    profile: ArchitectureDistanceProfileV1,
) -> bool {
    result.status == "blocked"
        || result.status == "measuredViolation"
        || (result.status == "measuredPass"
            && recommended_operation(&result.law, profile).is_some())
}

struct OperationRecommendationV1 {
    operation_kind: &'static str,
    cost: i64,
    cost_source_ref: &'static str,
    precondition_refs: Vec<&'static str>,
}

fn recommended_operation(
    law: &str,
    profile: ArchitectureDistanceProfileV1,
) -> Option<OperationRecommendationV1> {
    match law {
        "solid.dependency-inversion" => Some(OperationRecommendationV1 {
            operation_kind: "introduce-or-confirm-port-boundary",
            cost: profile.dependency_inversion_operation_cost,
            cost_source_ref: "distanceProfile.operationCosts.solid.dependency-inversion",
            precondition_refs: vec![
                "precondition:port-boundary-observed",
                "precondition:dependency-target-classified",
            ],
        }),
        "domain.no-direct-infra-dependency" => Some(OperationRecommendationV1 {
            operation_kind: "split-domain-infrastructure-boundary",
            cost: profile.infrastructure_dependency_operation_cost,
            cost_source_ref: "distanceProfile.operationCosts.domain.no-direct-infra-dependency",
            precondition_refs: vec![
                "precondition:domain-boundary-observed",
                "precondition:infrastructure-adapter-observed",
            ],
        }),
        _ => None,
    }
}

fn operation_primary_insights(operation_distance_readings: &[Value]) -> Value {
    let mut candidates = operation_distance_readings
        .iter()
        .filter(|reading| reading["status"] == "measured" || reading["status"] == "blocked")
        .map(|reading| {
            json!({
                "readingRef": reading["readingId"],
                "law": reading["law"],
                "operationKind": reading["operationKind"],
                "measuredValue": reading["measuredValue"],
                "operationCost": reading["operationCost"],
                "targetDistanceDecrease": reading["targetDistanceDecrease"],
                "distanceToSelectedFlat": reading["distanceToSelectedFlat"],
                "repairRoute": reading["repairRoute"],
                "sideEffectBound": reading["sideEffectBound"],
                "detailRefs": reading["detailRefs"]
            })
        })
        .collect::<Vec<_>>();
    candidates.sort_by(|left, right| {
        let right_value = right["measuredValue"]
            .as_i64()
            .or_else(|| right["operationCost"]["measuredValue"].as_i64());
        let left_value = left["measuredValue"]
            .as_i64()
            .or_else(|| left["operationCost"]["measuredValue"].as_i64());
        right_value.cmp(&left_value)
    });
    candidates.truncate(5);

    json!({
        "topOperationCandidates": candidates,
        "reading": "operation insights expose profile cost, target decrease, selected flatness distance, repair-route state, and side-effect bound without claiming automatic repair safety"
    })
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

    #[test]
    fn architecture_distance_bundle_validation_fails_when_family_summary_drifts() {
        let mut packet = json!({
            "architectureDistance": {
                "summary": {
                    "measuredTotalScope": {
                        "scope": "aggregated architecture-distance-point families only",
                        "includedFamilies": [
                            "atomGeometry",
                            "configurationGeometry",
                            "signatureGeometry",
                            "operationGeometry"
                        ],
                        "nonAggregatedFamilies": [
                            "foundation",
                            "curvatureGeometry",
                            "homotopyFillingGeometry",
                            "representationMetric",
                            "measurementBoundary",
                            "boundedDiagnosticConclusion"
                        ]
                    }
                },
                "measurementStateSummary": {
                    "familyCount": 10,
                    "missingCanonicalFamilyCount": 0
                },
                "primaryInsightsRefs": ["architecture-distance.json#/familySummaries"],
                "familySummaries": []
            },
            "part4DistanceCoverageLedger": []
        });
        let families = [
            "foundation",
            "atomGeometry",
            "configurationGeometry",
            "signatureGeometry",
            "operationGeometry",
            "curvatureGeometry",
            "homotopyFillingGeometry",
            "representationMetric",
            "measurementBoundary",
            "boundedDiagnosticConclusion",
        ];
        let summaries = families
            .iter()
            .enumerate()
            .map(|(index, family)| {
                json!({
                    "ledgerEntryId": format!("part4-ledger:{family}"),
                    "distanceFamily": family,
                    "coverageStatus": "primary",
                    "measurementStatus": "measured",
                    "readingCount": 1,
                    "rawPacketRefs": [format!("packet:/{family}")],
                    "sourceLedgerRef": format!("packet:/part4DistanceCoverageLedger/{index}"),
                    "primaryArtifactRefs": [
                        format!("architecture-distance.json#/familySummaries/{index}")
                    ]
                })
            })
            .collect::<Vec<_>>();
        packet["architectureDistance"]["familySummaries"] = Value::Array(summaries.clone());
        packet["part4DistanceCoverageLedger"] = Value::Array(summaries);
        assert!(
            architecture_distance_bundle_matches_packet(&packet),
            "control packet must satisfy the canonical bundle contract"
        );

        let mut missing_summary = packet.clone();
        missing_summary["architectureDistance"]["familySummaries"]
            .as_array_mut()
            .expect("family summaries are mutable")
            .pop();
        assert!(
            !architecture_distance_bundle_matches_packet(&missing_summary),
            "missing family summary must fail canonical bundle validation"
        );

        let mut drifted_status = packet;
        drifted_status["architectureDistance"]["familySummaries"][1]["measurementStatus"] =
            json!("blocked");
        assert!(
            !architecture_distance_bundle_matches_packet(&drifted_status),
            "family summary status drift must fail canonical bundle validation"
        );
    }

    #[test]
    fn atom_semantic_anchor_distance_blocks_missing_anchor_instead_of_zero() {
        let left = NormalizedAtomV1 {
            source_atom_id: "atom:left".to_string(),
            normalized_atom_id: "n:atom:left".to_string(),
            atom_kind: "semantic".to_string(),
            axis: "semantic".to_string(),
            predicate: crate::NormalizedAtomPredicateV1 {
                constructor: "semantic".to_string(),
                normalized_name: "semantic()".to_string(),
                bindings: Vec::new(),
            },
            shape_coordinate_status: "resolved".to_string(),
            valence_template_id: "valence:semantic@1".to_string(),
            molecule_memberships: vec!["mol:test".to_string()],
            normalization_status: "normalized".to_string(),
            normalization_blocker_reason: None,
        };
        let right = NormalizedAtomV1 {
            source_atom_id: "atom:right".to_string(),
            normalized_atom_id: "n:atom:right".to_string(),
            atom_kind: "semantic".to_string(),
            axis: "semantic".to_string(),
            predicate: crate::NormalizedAtomPredicateV1 {
                constructor: "semantic".to_string(),
                normalized_name: "semantic(order)".to_string(),
                bindings: vec![crate::NormalizedAtomBindingV1 {
                    role: "anchor".to_string(),
                    value: "order".to_string(),
                }],
            },
            shape_coordinate_status: "resolved".to_string(),
            valence_template_id: "valence:semantic@1".to_string(),
            molecule_memberships: vec!["mol:test".to_string()],
            normalization_status: "normalized".to_string(),
            normalization_blocker_reason: None,
        };
        let molecule = NormalizedMoleculeV1 {
            source_molecule_id: "mol:test".to_string(),
            normalized_molecule_id: "n:mol:test".to_string(),
            atom_ids: vec!["n:atom:left".to_string(), "n:atom:right".to_string()],
            generated_molecule_candidate_status: "generated".to_string(),
            required_port_status: "resolvedFromExplicitMembership".to_string(),
            composition_status: "compatibleCandidate".to_string(),
            normalization_blocker_reason: None,
        };
        let profile = architecture_distance_profile_v1("distance-profile:architecture-default@1")
            .expect("default profile exists");

        let readings = atom_part4_definition_readings(&left, &right, &molecule, profile);
        let semantic_anchor = readings
            .iter()
            .find(|reading| reading["componentKind"] == "semanticAnchor")
            .expect("semantic anchor row is emitted");
        assert_eq!(semantic_anchor["status"].as_str(), Some("blocked"));
        assert!(
            semantic_anchor["measuredValue"].is_null(),
            "missing semantic anchor must not become measured zero"
        );
        assert!(
            semantic_anchor["blockerRefs"]
                .as_array()
                .is_some_and(|refs| !refs.is_empty()),
            "missing semantic anchor must carry a blocker ref"
        );
        let normalized = NormalizedArchMapV1 {
            schema: "normalized-archmap/v1".to_string(),
            normalizer_id: "test-normalizer".to_string(),
            source_archmap_ref: "archmap.json".to_string(),
            source_archmap_id: "archmap:test".to_string(),
            atoms: vec![left, right],
            molecules: vec![molecule],
            summary: NormalizedArchMapSummaryV1 {
                atom_count: 2,
                normalized_atom_count: 2,
                molecule_count: 1,
                generated_molecule_candidate_count: 1,
                blocked_molecule_candidate_count: 0,
            },
            non_conclusions: Vec::new(),
        };
        let policy = LawPolicyDocumentV1 {
            schema: "law-policy/v1".to_string(),
            id: "policy:test".to_string(),
            distance_profile_ref: Some("distance-profile:architecture-default@1".to_string()),
            policies: Vec::new(),
        };
        let typed_results = empty_typed_results_for_test();
        let architecture_distance =
            build_architecture_distance_v1(&normalized, &policy, &typed_results)
                .expect("architecture distance builds");
        assert_eq!(
            architecture_distance["summary"]["blockedOrUnmeasuredCount"].as_u64(),
            Some(1),
            "row-level semantic anchor blockers must propagate to architecture distance summary"
        );
        assert_eq!(
            architecture_distance["atomDistanceReadings"][0]["status"].as_str(),
            Some("partial"),
            "parent atom reading must become partial when a definition row is blocked"
        );
        assert!(
            architecture_distance["distanceDiagnosis"]["blockedResults"]
                .as_array()
                .is_some_and(|blocked| blocked.iter().any(|result| result["readingId"]
                    == architecture_distance["atomDistanceReadings"][0]["readingId"])),
            "blockedResults must expose the parent atom reading blocker"
        );
    }

    #[test]
    fn operation_distance_blocks_violation_without_declared_profile_cost() {
        let profile = architecture_distance_profile_v1("distance-profile:architecture-default@1")
            .expect("default profile exists");
        let mut typed_results = empty_typed_results_for_test();
        typed_results.results.push(TypedEvaluatorResultV1 {
            evaluator: "evaluator:test".to_string(),
            law: "custom.unpriced-operation".to_string(),
            status: "measuredViolation".to_string(),
            support_atom_refs: Vec::new(),
            support_molecule_refs: Vec::new(),
            basis_refs: vec!["test:law-policy".to_string()],
            detail_refs: vec!["atom:test".to_string()],
            replacement_id: None,
            replacement_for_v0_field: None,
            typed_output_packet_refs: Vec::new(),
            summary: "synthetic violation without operation cost".to_string(),
            blocker_reason: None,
        });

        let readings = architecture_operation_distance_readings(&typed_results, profile, &[]);
        assert_eq!(readings.len(), 1);
        assert_eq!(readings[0]["status"].as_str(), Some("blocked"));
        assert_eq!(
            readings[0]["blockerReason"].as_str(),
            Some("operation cost is not declared by the selected DistanceProfile")
        );
        assert!(
            readings[0]["measuredValue"].is_null(),
            "missing operation cost must not fall back to a guessed measured value"
        );
    }

    #[test]
    fn curvature_insights_do_not_treat_empty_support_as_zero() {
        let insights =
            curvature_primary_insights_v1(&json!([]), &json!([]), &json!([]), &json!([]));
        assert_eq!(
            insights["status"].as_str(),
            Some("no-selected-support"),
            "empty curvature support is not selected-support zero"
        );
        assert_eq!(insights["measuredZeroSupportCount"].as_u64(), Some(0));
        assert!(
            insights["topCurvatureSupports"]
                .as_array()
                .is_some_and(|items| items.is_empty())
        );
    }

    #[test]
    fn representation_insights_do_not_treat_bounded_proxy_as_measured() {
        let readings = primary_representation_metric_readings_v1(&json!({
            "representationMetricReadings": [
                {
                    "readingId": "representation-metric:test",
                    "representationFamily": "typedEvaluatorSupportGraph",
                    "measurementStatus": "measured",
                    "structuralDistance": {
                        "status": "measured",
                        "supportSize": 2,
                        "evaluatorBasisRefs": ["basis:test"]
                    },
                    "analyticDistance": {
                        "status": "boundedProxy",
                        "reading": "proxy telemetry"
                    },
                    "lipschitzStability": {
                        "status": "measured",
                        "measuredValue": 1,
                        "unit": "selected-L-upper-bound"
                    },
                    "coverageGapRefs": [],
                    "typedEvaluatorResultRefs": ["/typedEvaluatorResults/0"],
                    "normalizedAtomRefs": ["n:atom:test"],
                    "normalizedMoleculeRefs": ["n:mol:test"]
                },
                {
                    "readingId": "representation-metric:blocked",
                    "representationFamily": "typedEvaluatorSupportGraph",
                    "measurementStatus": "blockedByMissingTypedEvaluatorResults",
                    "structuralDistance": {
                        "status": "blocked"
                    },
                    "analyticDistance": {
                        "status": "boundedProxy",
                        "reading": "proxy telemetry"
                    },
                    "coverageGapRefs": [],
                    "typedEvaluatorResultRefs": [],
                    "normalizedAtomRefs": [],
                    "normalizedMoleculeRefs": []
                }
            ]
        }));
        let insights = representation_primary_insights_v1(&readings);
        assert_eq!(readings[0]["status"].as_str(), Some("partial"));
        assert_eq!(
            readings[0]["lipschitzUpperBound"]["status"],
            "blockedByProxy"
        );
        assert_eq!(readings[0]["biLipschitzFaithfulness"]["status"], "blocked");
        assert_eq!(readings[1]["status"].as_str(), Some("blocked"));
        assert!(
            readings[0]["coverageBlockerRefs"]
                .as_array()
                .is_some_and(|items| !items.is_empty())
        );
        assert!(
            readings[0]["witnessCompletenessBlockerRefs"]
                .as_array()
                .is_some_and(|items| !items.is_empty())
        );
        assert_eq!(insights["status"].as_str(), Some("partial"));
        assert_eq!(insights["measuredAnalyticDistanceCount"].as_u64(), Some(0));
        assert_eq!(insights["boundedProxyAnalyticCount"].as_u64(), Some(2));
        assert_eq!(insights["blockedFaithfulnessCount"].as_u64(), Some(2));
    }

    fn empty_typed_results_for_test() -> TypedEvaluatorResultsV1 {
        TypedEvaluatorResultsV1 {
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
        }
    }
}
