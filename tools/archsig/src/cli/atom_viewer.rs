pub(crate) fn build_atom_viewer_data(
    archmap: &ArchMapDocumentV0,
    packet: &serde_json::Value,
    summary: &serde_json::Value,
    archmap_path: &Path,
    law_policy_path: &Path,
) -> ArchSigAtomViewerDataV0 {
    const ATOM_NODE_LIMIT: usize = 20_000;
    const MOLECULE_GROUP_LIMIT: usize = 120;
    const EDGE_LIMIT: usize = 30_000;
    const OVERLAY_LIMIT: usize = 80;
    const LABEL_LIMIT: usize = 3;
    const SOURCE_REF_SAMPLE_LIMIT: usize = 3;

    let mut atom_molecule_ref_counts: BTreeMap<&str, usize> = BTreeMap::new();
    for molecule in &archmap.molecule_observations {
        for atom_ref in &molecule.atom_observation_refs {
            *atom_molecule_ref_counts
                .entry(atom_ref.as_str())
                .or_default() += 1;
        }
    }
    let atom_nodes = archmap
        .atom_observations
        .iter()
        .map(|atom| {
            (
                atom_priority_score(
                    atom,
                    atom_molecule_ref_counts
                        .get(atom.atom_observation_id.as_str())
                        .copied()
                        .unwrap_or_default(),
                ),
                atom,
            )
        })
        .collect::<Vec<_>>();
    let mut atom_candidates = atom_nodes;
    atom_candidates.sort_by(|(left_score, left), (right_score, right)| {
        right_score
            .cmp(left_score)
            .then_with(|| left.atom_observation_id.cmp(&right.atom_observation_id))
    });
    let selected_atom_ids = atom_candidates
        .iter()
        .take(ATOM_NODE_LIMIT)
        .map(|(_, atom)| atom.atom_observation_id.as_str())
        .collect::<BTreeSet<_>>();
    let atom_nodes = atom_candidates
        .into_iter()
        .take(ATOM_NODE_LIMIT)
        .map(|(priority_score, atom)| {
            let molecule_ref_count = atom_molecule_ref_counts
                .get(atom.atom_observation_id.as_str())
                .copied()
                .unwrap_or_default();
            ArchSigAtomViewerAtomNodeV0 {
                node_id: atom.atom_observation_id.clone(),
                atom_family: atom.atom_family.clone(),
                subject_ref: atom.subject_ref.clone(),
                predicate: atom.predicate.clone(),
                observation_status: atom.observation_status.clone(),
                confidence: atom.confidence.clone(),
                object_ref_count: atom.object_refs.len(),
                source_ref_count: atom.source_refs.len(),
                source_ref_samples: source_ref_samples(&atom.source_refs, SOURCE_REF_SAMPLE_LIMIT),
                labels: atom_labels(atom, LABEL_LIMIT),
                projection_refs: atom.projection_refs.clone(),
                selection_reason: format!(
                    "topNPriority: status={} confidence={} sourceRefs={} moleculeRefs={}",
                    atom.observation_status,
                    atom.confidence,
                    atom.source_refs.len(),
                    molecule_ref_count
                ),
                priority_score,
                visual: ArchSigAtomViewerVisualV0 {
                    kind: "atom".to_string(),
                    color_by: Some("observationStatus".to_string()),
                    size_by: Some("sourceRefCount".to_string()),
                    hull_by: None,
                },
            }
        })
        .collect::<Vec<_>>();

    let molecule_groups = archmap
        .molecule_observations
        .iter()
        .map(|molecule| (molecule_priority_score(molecule), molecule))
        .collect::<Vec<_>>();
    let mut molecule_groups = molecule_groups;
    molecule_groups.sort_by(|(left_score, left), (right_score, right)| {
        right_score.cmp(left_score).then_with(|| {
            left.molecule_observation_id
                .cmp(&right.molecule_observation_id)
        })
    });
    let molecule_groups = molecule_groups
        .into_iter()
        .take(MOLECULE_GROUP_LIMIT)
        .map(|(priority_score, molecule)| {
            let selected_refs = molecule
                .atom_observation_refs
                .iter()
                .filter(|atom_ref| selected_atom_ids.contains(atom_ref.as_str()))
                .cloned()
                .collect::<Vec<_>>();
            ArchSigAtomViewerMoleculeGroupV0 {
                group_id: molecule.molecule_observation_id.clone(),
                molecule_family: molecule.molecule_family.clone(),
                role_name: molecule.role_name.clone(),
                atom_observation_refs: selected_refs.clone(),
                observation_status: molecule.observation_status.clone(),
                confidence: molecule.confidence.clone(),
                source_ref_count: molecule.source_refs.len(),
                source_ref_samples: source_ref_samples(
                    &molecule.source_refs,
                    SOURCE_REF_SAMPLE_LIMIT,
                ),
                labels: molecule_labels(molecule, LABEL_LIMIT),
                omitted_atom_observation_ref_count: molecule
                    .atom_observation_refs
                    .len()
                    .saturating_sub(selected_refs.len()),
                selection_reason: format!(
                    "topNPriority: status={} confidence={} sourceRefs={} atomRefs={}",
                    molecule.observation_status,
                    molecule.confidence,
                    molecule.source_refs.len(),
                    molecule.atom_observation_refs.len()
                ),
                priority_score,
                visual: ArchSigAtomViewerVisualV0 {
                    kind: "moleculeGroup".to_string(),
                    color_by: None,
                    size_by: None,
                    hull_by: Some("atomObservationRefs".to_string()),
                },
            }
        })
        .collect::<Vec<_>>();

    let mut atom_edges = Vec::new();
    let mut omitted_edge_count = 0usize;
    for molecule in &molecule_groups {
        for atom_ref in &molecule.atom_observation_refs {
            if atom_edges.len() >= EDGE_LIMIT {
                omitted_edge_count += 1;
                continue;
            }
            atom_edges.push(ArchSigAtomViewerEdgeV0 {
                edge_id: format!("edge:{}:{}", molecule.group_id, atom_ref),
                source_node_ref: molecule.group_id.clone(),
                target_node_ref: atom_ref.clone(),
                edge_kind: "moleculeContainsAtom".to_string(),
                relation_ref: Some(molecule.group_id.clone()),
                visual: ArchSigAtomViewerVisualV0 {
                    kind: "moleculeAtomEdge".to_string(),
                    color_by: Some("edgeKind".to_string()),
                    size_by: None,
                    hull_by: None,
                },
            });
        }
    }

    let signature_axes = array_field_with_limit(packet, "signatureAxes", Some(OVERLAY_LIMIT));
    let obstruction_circuits =
        array_field_with_limit(packet, "obstructionCircuits", Some(OVERLAY_LIMIT));
    let signature_axis_omissions = omitted_array_count(packet, "signatureAxes", OVERLAY_LIMIT);
    let obstruction_circuit_omissions =
        omitted_array_count(packet, "obstructionCircuits", OVERLAY_LIMIT);
    let overlays = serde_json::json!({
        "signatureAxes": signature_axes,
        "obstructionCircuits": obstruction_circuits,
        "coverageGaps": json_field(summary, "coverageGapSummary"),
        "dominantFindings": json_field(summary, "dominantFindings"),
        "actionQueue": json_field(summary, "actionQueue"),
        "omittedOverlayCounts": {
            "signatureAxes": signature_axis_omissions,
            "obstructionCircuits": obstruction_circuit_omissions
        },
        "focusFilterDefaults": {
            "families": ["obstructionCircuits", "coverageGaps", "repairFocus", "moleculeGroups"],
            "policy": "viewer UI may filter this bounded projection without loading raw packet detail"
        }
    });
    let aat_geometry_overlays = build_aat_geometry_overlays(packet, OVERLAY_LIMIT);
    let report_pane = serde_json::json!({
        "overview": {
            "mapId": &archmap.map_id,
            "architectureId": &archmap.architecture_id,
            "analysisId": json_field(packet, "analysisId"),
            "summaryVerdict": json_field(summary, "verdict"),
            "validation": json_field(summary, "validation"),
            "measurementStatusSummary": json_field(summary, "measurementStatusSummary")
        },
        "distanceDiagnosis": json_field(summary, "distanceDiagnosis"),
        "topFindings": json_field(summary, "dominantFindings"),
        "actionQueue": json_field(summary, "actionQueue"),
        "coverageAndBoundaries": {
            "coverageGaps": json_field(summary, "coverageGapSummary"),
            "measurementBasis": json_field(summary, "measurementBasis"),
            "metadata": json_field(summary, "metadata")
        },
        "artifacts": {
            "summary": "archsig-analysis-summary.json",
            "manifest": "archsig-run-manifest.json",
            "rawArtifacts": "see archsig-run-manifest.json rawArtifactRetention"
        }
    });

    ArchSigAtomViewerDataV0 {
        schema_version: ARCHSIG_ATOM_VIEWER_DATA_SCHEMA_VERSION.to_string(),
        data_kind: "bounded-atom-viewer-projection".to_string(),
        source_artifact_refs: ArchSigAtomViewerSourceArtifactRefsV0 {
            archmap: archmap_path.display().to_string(),
            law_policy: law_policy_path.display().to_string(),
            summary: "archsig-analysis-summary.json".to_string(),
            manifest: "archsig-run-manifest.json".to_string(),
        },
        layout_settings: ArchSigAtomViewerLayoutSettingsV0 {
            layout_kind: "aat-bounded-force-3d".to_string(),
            node_limit: ATOM_NODE_LIMIT,
            molecule_group_limit: MOLECULE_GROUP_LIMIT,
            edge_limit: EDGE_LIMIT,
            overlay_limit: OVERLAY_LIMIT,
            label_limit: LABEL_LIMIT,
            source_ref_sample_limit: SOURCE_REF_SAMPLE_LIMIT,
            distance_boundary:
                "3D distance is a visual projection, not an AAT theorem metric".to_string(),
        },
        atom_nodes,
        molecule_groups,
        atom_edges,
        law_axis_overlays: overlays["signatureAxes"].clone(),
        analysis_overlays: overlays,
        aat_geometry_overlays,
        report_pane,
        omitted_detail_counts: ArchSigAtomViewerOmittedDetailCountsV0 {
            atom_nodes: archmap.atom_observations.len().saturating_sub(ATOM_NODE_LIMIT),
            molecule_groups: archmap
                .molecule_observations
                .len()
                .saturating_sub(MOLECULE_GROUP_LIMIT),
            atom_edges: omitted_edge_count,
            source_refs: omitted_source_ref_count(archmap, SOURCE_REF_SAMPLE_LIMIT),
            labels: omitted_label_count(archmap, LABEL_LIMIT),
            overlay_items: signature_axis_omissions + obstruction_circuit_omissions,
            raw_packet_detail: "raw packet is not embedded in viewer data".to_string(),
            omitted_reasons: vec![
                "atom nodes are selected by deterministic top-N priority over observation status, confidence, source refs, object refs, projection refs, and molecule refs".to_string(),
                "molecule groups are selected by deterministic top-N priority over observation status, confidence, source refs, and atom refs".to_string(),
                "source refs and labels are represented by count plus bounded samples".to_string(),
                "diagnostic distance readings are bounded projections; full evaluator rows remain in optional raw artifacts".to_string(),
                "raw packet detail is intentionally omitted from browser viewer data".to_string(),
            ],
        },
        truncation_policy: ArchSigAtomViewerTruncationPolicyV0 {
            atom_nodes: format!("top {ATOM_NODE_LIMIT} ArchMap atom observations by viewer priority"),
            molecule_groups: format!(
                "top {MOLECULE_GROUP_LIMIT} ArchMap molecule observations by viewer priority"
            ),
            overlays: format!("top {OVERLAY_LIMIT} items per selected overlay family"),
            future_work:
                "Viewer UI can add focus filters over this bounded projection without reading raw packet detail"
                    .to_string(),
        },
        non_conclusions: vec![
            "viewer data is a bounded visual projection, not a replacement for the analysis packet"
                .to_string(),
            "3D layout distance is not a theorem metric, semantic equivalence, or causal relation"
                .to_string(),
            "raw packet detail is intentionally omitted unless analyze is rerun with --emit-raw-artifacts"
                .to_string(),
        ],
    }
}

fn source_ref_samples(
    refs: &[archsig::ArchMapSourceRef],
    limit: usize,
) -> Vec<archsig::ArchMapSourceRef> {
    refs.iter().take(limit).cloned().collect()
}

fn atom_priority_score(atom: &archsig::ArchMapAtomObservationV0, molecule_ref_count: usize) -> i64 {
    status_score(&atom.observation_status)
        + confidence_score(&atom.confidence)
        + (atom.source_refs.len() as i64 * 20)
        + (atom.object_refs.len() as i64 * 10)
        + (atom.projection_refs.len() as i64 * 10)
        + (molecule_ref_count as i64 * 50)
}

fn molecule_priority_score(molecule: &archsig::ArchMapMoleculeObservationV0) -> i64 {
    status_score(&molecule.observation_status)
        + confidence_score(&molecule.confidence)
        + (molecule.source_refs.len() as i64 * 20)
        + (molecule.atom_observation_refs.len() as i64 * 15)
}

fn status_score(status: &str) -> i64 {
    match status {
        "observed" => 1_000,
        "inferred" => 500,
        "partial" => 250,
        _ => 0,
    }
}

fn confidence_score(confidence: &str) -> i64 {
    match confidence {
        "high" => 300,
        "medium" => 150,
        "low" => 25,
        _ => 0,
    }
}

fn atom_labels(atom: &archsig::ArchMapAtomObservationV0, limit: usize) -> Vec<String> {
    [
        atom.atom_family.as_str(),
        atom.subject_ref.as_str(),
        atom.predicate.as_str(),
    ]
    .into_iter()
    .take(limit)
    .map(str::to_string)
    .collect()
}

fn molecule_labels(molecule: &archsig::ArchMapMoleculeObservationV0, limit: usize) -> Vec<String> {
    [
        molecule.molecule_family.as_str(),
        molecule.role_name.as_str(),
        molecule.observation_status.as_str(),
    ]
    .into_iter()
    .take(limit)
    .map(str::to_string)
    .collect()
}

fn omitted_array_count(value: &serde_json::Value, field: &str, limit: usize) -> usize {
    value
        .get(field)
        .and_then(|items| items.as_array())
        .map(|items| items.len().saturating_sub(limit))
        .unwrap_or_default()
}

fn build_aat_geometry_overlays(packet: &serde_json::Value, limit: usize) -> serde_json::Value {
    const GEOMETRY_ATOM_REF_SAMPLE_LIMIT: usize = 5000;
    let spectrum_report = packet
        .get("architectureSpectrumReport")
        .map(|report| compact_geometry_report(report, limit, GEOMETRY_ATOM_REF_SAMPLE_LIMIT))
        .unwrap_or_else(|| serde_json::Value::Array(Vec::new()));
    let diagnostic_distance_readings = serde_json::json!({
        "atomDistances": compact_geometry_array(packet, "atomDistanceReadings", limit, GEOMETRY_ATOM_REF_SAMPLE_LIMIT),
        "configurationDistances": compact_geometry_array(packet, "configurationDistanceReadings", limit, GEOMETRY_ATOM_REF_SAMPLE_LIMIT),
        "signatureDistances": compact_geometry_array(packet, "signatureDistanceReadings", limit, GEOMETRY_ATOM_REF_SAMPLE_LIMIT),
        "operationDistances": compact_geometry_array(packet, "operationDistanceReadings", limit, GEOMETRY_ATOM_REF_SAMPLE_LIMIT),
        "curvatureMassDistances": compact_geometry_array(packet, "curvatureMassReadings", limit, GEOMETRY_ATOM_REF_SAMPLE_LIMIT),
        "homotopyDistances": compact_geometry_array(packet, "homotopyDistanceReadings", limit, GEOMETRY_ATOM_REF_SAMPLE_LIMIT),
        "representationMetrics": compact_geometry_array(packet, "representationMetricReadings", limit, GEOMETRY_ATOM_REF_SAMPLE_LIMIT)
    });
    let omitted_distance_counts = serde_json::json!({
        "atomDistances": omitted_array_count(packet, "atomDistanceReadings", limit),
        "configurationDistances": omitted_array_count(packet, "configurationDistanceReadings", limit),
        "signatureDistances": omitted_array_count(packet, "signatureDistanceReadings", limit),
        "operationDistances": omitted_array_count(packet, "operationDistanceReadings", limit),
        "curvatureMassDistances": omitted_array_count(packet, "curvatureMassReadings", limit),
        "homotopyDistances": omitted_array_count(packet, "homotopyDistanceReadings", limit),
        "representationMetrics": omitted_array_count(packet, "representationMetricReadings", limit)
    });
    serde_json::json!({
        "schemaVersion": "archsig-aat-geometry-overlays-v0",
        "projectionBoundary": "bounded projection of computed ArchSig AAT geometry readings; not a theorem metric and not a raw packet copy",
        "curvatureSupports": compact_geometry_array(packet, "curvatureSupportReadings", limit, GEOMETRY_ATOM_REF_SAMPLE_LIMIT),
        "curvatureTransfers": compact_geometry_array(packet, "curvatureTransferReadings", limit, GEOMETRY_ATOM_REF_SAMPLE_LIMIT),
        "generatedAtomShapes": compact_geometry_array(packet, "generatedAtomShapes", limit, GEOMETRY_ATOM_REF_SAMPLE_LIMIT),
        "generatedMolecules": compact_geometry_array(packet, "generatedMolecules", limit, GEOMETRY_ATOM_REF_SAMPLE_LIMIT),
        "generatedLawInputs": compact_geometry_array(packet, "generatedLawInputs", limit, GEOMETRY_ATOM_REF_SAMPLE_LIMIT),
        "generatedObstructions": compact_geometry_array(packet, "generatedObstructions", limit, GEOMETRY_ATOM_REF_SAMPLE_LIMIT),
        "generatedRepairTargets": compact_geometry_array(packet, "generatedRepairTargets", limit, GEOMETRY_ATOM_REF_SAMPLE_LIMIT),
        "diagnosticDistanceBoundary": "diagnostic distances come from Part IV evaluator readings; viewerDistanceInputs are visual layout support and must not be read as diagnostic metrics",
        "diagnosticDistanceReadings": diagnostic_distance_readings,
        "viewerDistanceInputs": compact_viewer_distance_inputs(packet, limit, GEOMETRY_ATOM_REF_SAMPLE_LIMIT),
        "spectrumReport": spectrum_report,
        "pathPairs": compact_geometry_array(packet, "pathPairCandidates", limit, GEOMETRY_ATOM_REF_SAMPLE_LIMIT),
        "loops": compact_geometry_array(packet, "loopCandidates", limit, GEOMETRY_ATOM_REF_SAMPLE_LIMIT),
        "holonomyReadings": compact_geometry_array(packet, "homotopyHolonomyReadings", limit, GEOMETRY_ATOM_REF_SAMPLE_LIMIT),
        "stokesReadings": compact_geometry_array(packet, "stokesStyleReadings", limit, GEOMETRY_ATOM_REF_SAMPLE_LIMIT),
        "homotopyReport": packet
            .get("architectureHomotopyReport")
            .map(|report| compact_geometry_report(report, limit, GEOMETRY_ATOM_REF_SAMPLE_LIMIT))
            .unwrap_or_else(|| serde_json::Value::Array(Vec::new())),
        "nonzeroMonodromyWitnesses": compact_geometry_array(packet, "nonzeroMonodromyWitnesses", limit, GEOMETRY_ATOM_REF_SAMPLE_LIMIT),
        "localCurvatureDiagrams": compact_geometry_array(packet, "localCurvatureDiagramReadings", limit, GEOMETRY_ATOM_REF_SAMPLE_LIMIT),
        "pathHomotopyDiagrams": compact_geometry_array(packet, "pathHomotopyDiagramReadings", limit, GEOMETRY_ATOM_REF_SAMPLE_LIMIT),
        "flatnessReading": json_field(packet, "flatnessReading"),
        "omittedGeometryCounts": {
            "curvatureSupports": omitted_array_count(packet, "curvatureSupportReadings", limit),
            "curvatureTransfers": omitted_array_count(packet, "curvatureTransferReadings", limit),
            "generatedAtomShapes": omitted_array_count(packet, "generatedAtomShapes", limit),
            "generatedMolecules": omitted_array_count(packet, "generatedMolecules", limit),
            "generatedLawInputs": omitted_array_count(packet, "generatedLawInputs", limit),
            "generatedObstructions": omitted_array_count(packet, "generatedObstructions", limit),
            "generatedRepairTargets": omitted_array_count(packet, "generatedRepairTargets", limit),
            "diagnosticDistanceReadings": omitted_distance_counts,
            "viewerDistanceInputs": omitted_array_count(packet, "viewerDistanceInputs", limit),
            "pathPairs": omitted_array_count(packet, "pathPairCandidates", limit),
            "loops": omitted_array_count(packet, "loopCandidates", limit),
            "holonomyReadings": omitted_array_count(packet, "homotopyHolonomyReadings", limit),
            "stokesReadings": omitted_array_count(packet, "stokesStyleReadings", limit),
            "nonzeroMonodromyWitnesses": omitted_array_count(packet, "nonzeroMonodromyWitnesses", limit),
            "localCurvatureDiagrams": omitted_array_count(packet, "localCurvatureDiagramReadings", limit),
            "pathHomotopyDiagrams": omitted_array_count(packet, "pathHomotopyDiagramReadings", limit)
        }
    })
}

fn compact_geometry_array(
    value: &serde_json::Value,
    field: &str,
    limit: usize,
    atom_ref_limit: usize,
) -> serde_json::Value {
    serde_json::Value::Array(
        array_items(value, field)
            .into_iter()
            .take(limit)
            .map(|item| compact_geometry_item(item, atom_ref_limit))
            .collect(),
    )
}

fn compact_viewer_distance_inputs(
    value: &serde_json::Value,
    limit: usize,
    atom_ref_limit: usize,
) -> serde_json::Value {
    serde_json::Value::Array(
        array_items(value, "viewerDistanceInputs")
            .into_iter()
            .take(limit)
            .map(|item| compact_viewer_distance_input(item, atom_ref_limit))
            .collect(),
    )
}

fn compact_viewer_distance_input(
    value: &serde_json::Value,
    atom_ref_limit: usize,
) -> serde_json::Value {
    let mut atom_refs = BTreeSet::new();
    collect_atom_refs(value, &mut atom_refs);
    let sampled_atom_refs = atom_refs
        .iter()
        .take(atom_ref_limit)
        .cloned()
        .collect::<Vec<_>>();
    let atom_shape_refs = string_array(value, "atomShapeRefs")
        .into_iter()
        .take(atom_ref_limit)
        .collect::<Vec<_>>();
    let coordinate_components = string_array(value, "coordinateComponents")
        .into_iter()
        .take(24)
        .collect::<Vec<_>>();
    serde_json::json!({
        "id": json_field(value, "distanceInputId"),
        "kind": json_field(value, "distanceKind"),
        "status": compact_first_string_field(value, &["status", "measurementStatus"]),
        "value": json_field(value, "distanceValue"),
        "distanceInputId": json_field(value, "distanceInputId"),
        "distanceKind": json_field(value, "distanceKind"),
        "sourceRef": json_field(value, "sourceRef"),
        "targetRef": json_field(value, "targetRef"),
        "generatedMoleculeRef": json_field(value, "generatedMoleculeRef"),
        "atomShapeRefs": atom_shape_refs,
        "coordinateComponents": coordinate_components,
        "distanceValue": json_field(value, "distanceValue"),
        "evidenceBoundary": json_field(value, "evidenceBoundary"),
        "atomRefs": sampled_atom_refs,
        "atomRefCount": atom_refs.len(),
        "omittedAtomRefs": atom_refs.len().saturating_sub(atom_ref_limit)
    })
}

fn compact_geometry_report(
    value: &serde_json::Value,
    limit: usize,
    atom_ref_limit: usize,
) -> serde_json::Value {
    if value.is_null() {
        return serde_json::Value::Array(Vec::new());
    }
    if let Some(items) = value.as_array() {
        return serde_json::Value::Array(
            items
                .iter()
                .take(limit)
                .map(|item| compact_geometry_item(item, atom_ref_limit))
                .collect(),
        );
    }
    let mut compact_items = Vec::new();
    collect_compact_geometry_report_items(value, limit, atom_ref_limit, &mut compact_items);
    serde_json::Value::Array(compact_items)
}

fn collect_compact_geometry_report_items(
    value: &serde_json::Value,
    limit: usize,
    atom_ref_limit: usize,
    out: &mut Vec<serde_json::Value>,
) {
    if out.len() >= limit {
        return;
    }
    match value {
        serde_json::Value::Array(items) => {
            for item in items {
                if out.len() >= limit {
                    return;
                }
                if item.is_object() {
                    let compact = compact_geometry_item(item, atom_ref_limit);
                    if compact
                        .get("atomRefCount")
                        .and_then(serde_json::Value::as_u64)
                        .unwrap_or_default()
                        > 0
                    {
                        out.push(compact);
                    }
                }
            }
        }
        serde_json::Value::Object(map) => {
            for item in map.values() {
                collect_compact_geometry_report_items(item, limit, atom_ref_limit, out);
            }
        }
        _ => {}
    }
}

fn compact_geometry_item(value: &serde_json::Value, atom_ref_limit: usize) -> serde_json::Value {
    let mut atom_refs = BTreeSet::new();
    collect_atom_refs(value, &mut atom_refs);
    let sampled_atom_refs = atom_refs
        .iter()
        .take(atom_ref_limit)
        .cloned()
        .collect::<Vec<_>>();
    serde_json::json!({
        "id": compact_first_string_field(value, &[
            "ref",
            "readingRef",
            "readingId",
            "obstructionRef",
            "obstructionCircuitId",
            "pathRef",
            "loopRef",
            "axisRef"
        ]),
        "kind": compact_first_string_field(value, &[
            "kind",
            "readingKind",
            "curvatureKind",
            "holonomyKind",
            "status",
            "curvatureStatus"
        ]),
        "status": compact_first_string_field(value, &[
            "status",
            "coverageStatus",
            "curvatureStatus",
            "holonomyStatus",
            "flatnessStatus"
        ]),
        "value": compact_first_number_field(value, &[
            "curvatureValue",
            "value",
            "score",
            "defectValue",
            "cycleWeight",
            "coverageGapCount",
            "refCount",
            "sourceRefCount"
        ]),
        "atomRefs": sampled_atom_refs,
        "atomRefCount": atom_refs.len(),
        "omittedAtomRefs": atom_refs.len().saturating_sub(atom_ref_limit)
    })
}

fn collect_atom_refs(value: &serde_json::Value, refs: &mut BTreeSet<String>) {
    match value {
        serde_json::Value::String(text) => {
            if text.starts_with("atom:") {
                refs.insert(text.clone());
            }
        }
        serde_json::Value::Array(items) => {
            for item in items {
                collect_atom_refs(item, refs);
            }
        }
        serde_json::Value::Object(map) => {
            for item in map.values() {
                collect_atom_refs(item, refs);
            }
        }
        _ => {}
    }
}

fn compact_first_string_field(value: &serde_json::Value, keys: &[&str]) -> serde_json::Value {
    keys.iter()
        .find_map(|key| value.get(*key).and_then(serde_json::Value::as_str))
        .map(|text| serde_json::Value::String(text.to_string()))
        .unwrap_or(serde_json::Value::Null)
}

fn compact_first_number_field(value: &serde_json::Value, keys: &[&str]) -> serde_json::Value {
    keys.iter()
        .find_map(|key| value.get(*key).and_then(serde_json::Value::as_f64))
        .and_then(serde_json::Number::from_f64)
        .map(serde_json::Value::Number)
        .unwrap_or(serde_json::Value::Null)
}

fn omitted_source_ref_count(archmap: &ArchMapDocumentV0, sample_limit: usize) -> usize {
    let atom_omissions = archmap
        .atom_observations
        .iter()
        .map(|atom| atom.source_refs.len().saturating_sub(sample_limit))
        .sum::<usize>();
    let molecule_omissions = archmap
        .molecule_observations
        .iter()
        .map(|molecule| molecule.source_refs.len().saturating_sub(sample_limit))
        .sum::<usize>();
    atom_omissions + molecule_omissions
}

fn omitted_label_count(archmap: &ArchMapDocumentV0, label_limit: usize) -> usize {
    let atom_label_count = archmap.atom_observations.len() * 3;
    let molecule_label_count = archmap.molecule_observations.len() * 3;
    atom_label_count.saturating_sub(archmap.atom_observations.len() * label_limit)
        + molecule_label_count.saturating_sub(archmap.molecule_observations.len() * label_limit)
}
