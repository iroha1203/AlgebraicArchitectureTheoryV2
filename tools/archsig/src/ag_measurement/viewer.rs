pub fn build_measurement_viewer_data_v1(
    normalized: &NormalizedArchMapV2,
    archmap_document: &ArchMapDocumentV2,
    packet: &ArchSigMeasurementPacketV1,
    summary: &Value,
    insight_report: &Value,
) -> Value {
    let atom_count = normalized.atoms.len();
    let preserved_atom_refs = top_insight_atom_refs(insight_report);
    let preserved_context_refs = top_insight_context_refs(insight_report);
    let viewer_atoms = projected_atoms(normalized, &preserved_atom_refs, 10_000);
    let viewer_contexts = projected_contexts(normalized, &preserved_context_refs, 20_000);
    let viewer_covers = projected_covers(normalized, 10_000);
    let atom_nodes = viewer_atom_nodes(&viewer_atoms, archmap_document, insight_report);
    let molecule_groups = viewer_molecule_groups(&viewer_contexts);
    let atom_edges = viewer_atom_edges(&viewer_contexts);
    let context_memberships = normalized
        .atoms
        .iter()
        .map(|atom| atom.context_memberships.len())
        .sum::<usize>();
    let cover_overlaps = normalized
        .covers
        .iter()
        .map(|cover| cover.context_ids.len().saturating_sub(1))
        .sum::<usize>();
    let scene_layer_objects = insight_report["viewerVisualScenes"]
        .as_array()
        .into_iter()
        .flatten()
        .flat_map(|scene| scene["layers"].as_array().into_iter().flatten())
        .count();
    let large_graph_mode = atom_count >= 10_000
        || context_memberships > 20_000
        || cover_overlaps > 10_000
        || scene_layer_objects > 1_000;
    let omitted_detail_counts = insight_report["viewerVisualScenes"]
        .as_array()
        .map(|scenes| insight_omitted_detail_counts_v1(normalized, scenes))
        .unwrap_or_else(|| insight_omitted_detail_counts_v1(normalized, &[]));
    let saga_descent = build_saga_descent_viewer_projection(packet);
    json!({
        "schema": "archsig-atom-viewer-data/v0.5.4",
        "sourceArtifactRefs": {
            "normalizedArchMap": "normalized-archmap.json",
            "measurementPacket": "archsig-measurement-packet.json",
            "summary": "archsig-analysis-summary.json",
            "insightReport": "archsig-insight-report.json",
            "insightBrief": "archsig-insight-brief.md"
        },
        "decisionBar": {
            "conclusion": insight_report["headline"]["conclusionCode"],
            "validation": "see archsig-analysis-validation.json",
            "boundaryDigest": insight_report["boundaryDigest"]["shortText"],
            "artifactLinks": insight_report["outputArtifacts"]
        },
        "atomNodes": atom_nodes,
        "moleculeGroups": molecule_groups,
        "atomEdges": atom_edges,
        "insightQueue": insight_report["insightCards"],
        "actionQueue": insight_report["actionQueue"],
        "viewerVisualScenes": insight_report["viewerVisualScenes"],
        "guidedTours": insight_report["guidedTours"],
        "copyBlocks": insight_report["copyBlocks"],
        "sagaDescent": saga_descent,
        "aatGeometryOverlays": {
            "schema": "archsig-aat-geometry-overlays/v0.5.4",
            "projectionBoundary": "bounded viewer projection of measured ArchSig AG geometry; visual richness is not a new verdict",
            "gluingGeometry": insight_report["gluingGeometry"],
            "nerve": insight_report["gluingGeometry"]["nerve"],
            "cocycleRibbon": insight_report["gluingGeometry"]["cocycleRibbon"],
            "locusField": insight_report["gluingGeometry"]["locusField"],
            "spectrumLandscape": insight_report["gluingGeometry"]["spectrumLandscape"],
            "forbiddenCages": insight_report["gluingGeometry"]["forbiddenCages"],
            "repairMorphs": insight_report["gluingGeometry"]["repairMorphs"],
            "atomGlyphs": insight_report["gluingGeometry"]["atomGlyphs"],
            "analyticOverlayBundle": insight_report["gluingGeometry"]["analyticOverlayBundle"],
            "periodStokes": insight_report["gluingGeometry"]["periodStokes"],
            "periodPairingOverlays": insight_report["gluingGeometry"]["analyticOverlayBundle"]["periodPairingOverlays"],
            "transferCostOverlays": insight_report["gluingGeometry"]["analyticOverlayBundle"]["transferCostOverlays"],
            "spectralGapOverlays": insight_report["gluingGeometry"]["analyticOverlayBundle"]["spectralGapOverlays"],
            "curvatureHotspotOverlays": insight_report["gluingGeometry"]["analyticOverlayBundle"]["curvatureHotspotOverlays"],
            "singularityConcentrationOverlays": insight_report["gluingGeometry"]["analyticOverlayBundle"]["singularityConcentrationOverlays"],
            "omittedGeometryCounts": insight_report["gluingGeometry"]["omittedGeometryCounts"],
            "nonClaims": insight_report["gluingGeometry"]["nonClaims"]
        },
        "reportPane": {
            "conclusion": summary["conclusion"],
            "profileRef": packet.profile.profile_id,
            "assumptionSummary": summary["assumptionSummary"],
            "structuralVerdictSummary": summary["structuralVerdictSummary"],
            "readThisFirst": insight_report["readThisFirst"],
            "insightQueue": insight_report["insightCards"],
            "actionQueue": insight_report["actionQueue"],
            "evidenceDetailShape": ["What", "Why", "Where", "Measurement", "Boundary", "Next"],
            "boundaryDigest": insight_report["boundaryDigest"],
            "omittedDetailCounts": omitted_detail_counts,
            "artifactLinks": insight_report["outputArtifacts"]
        },
        "finitePosetSite": {
            "atoms": viewer_atoms,
            "contexts": viewer_contexts,
            "covers": viewer_covers
        },
        "largeGraphStrategy": {
            "mode": if large_graph_mode { "cluster_aggregation" } else { "full_projection" },
            "thresholds": {
                "fullGeometryAtoms": 2_000,
                "instancedAtoms": 10_000,
                "clusterAtoms": 50_000,
                "contextMemberships": 20_000,
                "coverOverlaps": 10_000,
                "sceneLayerObjects": 1_000
            },
            "topInsightEvidencePinning": {
                "policy": "preserve_for_top_insight",
                "preservedRefs": top_insight_preserved_refs(insight_report),
                "aggregatedRefs": if large_graph_mode { vec!["background-geometry"] } else { Vec::<&str>::new() },
                "omittedRefs": if large_graph_mode { vec!["background-labels"] } else { Vec::<&str>::new() }
            }
        },
        "omittedDetailCounts": insight_report["omittedDetailCounts"],
        "nonConclusions": [
            "Viewer data is a bounded projection of ArchMap v2 and measurement packet foundation rows.",
            "Layout and site visualization are ArchView presentation data; AG invariant values come from ArchSig measurement artifacts.",
            "Holonomy-like views are restriction path or cover path exploration, not monodromy verdicts.",
            "Theorem-candidate readings are not displayed as structural conclusions."
        ]
    })
}

fn build_saga_descent_viewer_projection(packet: &ArchSigMeasurementPacketV1) -> Value {
    let mut field_map = Vec::new();
    let mut grounding_rows = Vec::new();
    let mut descent_rows = Vec::new();

    for (index, row) in packet.structural_verdict.iter().enumerate() {
        let stage = match row.evaluator.as_str() {
            "ag.saga-grounded" => "grounding",
            "ag.saga-descent" => "descent",
            _ => continue,
        };
        let mut row_value = json!({
            "evaluator": row.evaluator,
            "law": row.law,
            "verdict": row.verdict,
            "inScope": row.verdict_data.in_scope,
            "zero": row.verdict_data.zero,
            "nonZero": row.verdict_data.non_zero,
            "methodStatus": row.verdict_data.method_status,
            "reason": row.reason,
            "dependsOnAssumptions": row.depends_on_assumptions
        });
        if let Some(cert_ref) = row.verdict_data.cert_ref.as_ref() {
            row_value["certRef"] = json!(cert_ref);
        }
        let row_index = if stage == "grounding" {
            grounding_rows.len()
        } else {
            descent_rows.len()
        };
        let prefix = if stage == "grounding" {
            format!("stages[0].rows[{row_index}]")
        } else {
            format!("stages[1].rows[{row_index}]")
        };
        for field in [
            "evaluator",
            "law",
            "verdict",
            "inScope",
            "zero",
            "nonZero",
            "methodStatus",
            "certRef",
            "reason",
            "dependsOnAssumptions",
        ] {
            let packet_path = if field == "inScope"
                || field == "zero"
                || field == "nonZero"
                || field == "methodStatus"
                || field == "certRef"
            {
                format!("/structuralVerdict/{index}/verdictData/{field}")
            } else {
                format!("/structuralVerdict/{index}/{field}")
            };
            if let Some(value) = row_value.get(field) {
                append_leaf_field_mappings(
                    &mut field_map,
                    &format!("{prefix}.{field}"),
                    &packet_path,
                    value,
                );
            }
        }
        if stage == "grounding" {
            grounding_rows.push(row_value);
        } else {
            descent_rows.push(row_value);
        }
    }

    let mut measurement_rows = Vec::new();
    let comparison_rows = Vec::new();
    let mut harmonic_rows = Vec::new();
    for (index, invariant) in packet.computed_invariants.iter().enumerate() {
        let Some(invariant_id) = invariant["invariantId"].as_str() else {
            continue;
        };
        if invariant_id == "saga-generated-end-to-end-packet"
            && invariant["evaluator"].as_str() == Some("ag.saga-grounded")
        {
            let row_index = grounding_rows.len();
            let mut row = serde_json::Map::new();
            for (output_field, source_path) in [
                ("invariantId", "invariantId"),
                ("evaluator", "evaluator"),
                ("theoremRef", "theoremRef"),
                ("premise", "displayedRequiredLawsHold"),
                ("detectorFindings", "detectorFindings"),
                ("detectorCount", "detectorCount"),
            ] {
                let value = invariant[source_path].clone();
                if !value.is_null() {
                    row.insert(output_field.to_string(), value);
                    let packet_path = format!("/computedInvariants/{index}/{source_path}");
                    append_leaf_field_mappings(
                        &mut field_map,
                        &format!("stages[0].rows[{row_index}].{output_field}"),
                        &packet_path,
                        &row[output_field],
                    );
                }
            }
            grounding_rows.push(Value::Object(row));
        } else if invariant["evaluator"].as_str() == Some("ag.saga-descent")
            && (invariant_id == "saga-descent:residual-class"
                || invariant_id == "saga-descent:boundary-membership"
                || invariant_id == "saga-descent:residual-derivation")
        {
            let measurement_index = measurement_rows.len();
            let mut row = serde_json::Map::new();
            row.insert("invariantId".to_string(), json!(invariant_id));
            for field in ["invariantId", "evaluator", "status", "reason", "whatNext"] {
                if let Some(value) = invariant.get(field) {
                    row.insert(field.to_string(), value.clone());
                    append_leaf_field_mappings(
                        &mut field_map,
                        &format!("stages[1].measurements[{measurement_index}].{field}"),
                        &format!("/computedInvariants/{index}/{field}"),
                        value,
                    );
                }
            }
            for (output_field, source_path) in [
                ("residualClass", "residualClassSupport"),
                ("boundaryMembership", "boundaryMembership"),
                ("residualDerivation", "residualDerivation"),
                ("faithfulnessBasis", "faithfulnessBasis"),
            ] {
                if let Some(value) = invariant.get(source_path) {
                    row.insert(output_field.to_string(), value.clone());
                    append_leaf_field_mappings(
                        &mut field_map,
                        &format!("stages[1].measurements[{measurement_index}].{output_field}"),
                        &format!("/computedInvariants/{index}/{source_path}"),
                        value,
                    );
                }
            }
            measurement_rows.push(Value::Object(row));
        } else if invariant["evaluator"] == "ag.harmonic-debt" {
            let harmonic_index = harmonic_rows.len();
            let mut row = serde_json::Map::new();
            for field in [
                "invariantId",
                "evaluator",
                "status",
                "reason",
                "whatNext",
                "essentialRepairLowerBound",
                "lowerBoundStatus",
            ] {
                if let Some(value) = invariant.get(field) {
                    row.insert(field.to_string(), value.clone());
                    append_leaf_field_mappings(
                        &mut field_map,
                        &format!("stages[1].harmonicDebt[{harmonic_index}].{field}"),
                        &format!("/computedInvariants/{index}/{field}"),
                        value,
                    );
                }
            }
            harmonic_rows.push(Value::Object(row));
        }
    }

    for (index, reading) in packet.analytic_readings.iter().enumerate() {
        if reading.evaluator != "ag.harmonic-debt" {
            continue;
        }
        let harmonic_index = harmonic_rows.len();
        let mut row = serde_json::Map::new();
        row.insert("readingId".to_string(), json!(reading.reading_id));
        row.insert("evaluator".to_string(), json!(reading.evaluator));
        if let Some(regime) = reading.regime.as_ref() {
            row.insert("regime".to_string(), json!(regime));
        }
        row.insert("value".to_string(), reading.value.clone());
        for (field, value) in &row {
            append_leaf_field_mappings(
                &mut field_map,
                &format!("stages[1].harmonicDebt[{harmonic_index}].{field}"),
                &format!("/analyticReadings/{index}/{field}"),
                value,
            );
        }
        harmonic_rows.push(Value::Object(row));
    }

    let mut silence_rows = packet
        .boundary_statements
        .iter()
        .enumerate()
        .filter(|(_, statement)| {
            statement.kind == "silence_by_design"
                && statement
                    .scope_refs
                    .iter()
                    .any(|scope_ref| saga_scope_ref(packet, scope_ref))
        })
        .enumerate()
        .map(|(row_index, (packet_index, statement))| {
            let row = json!({
                "id": statement.id,
                "status": statement.kind,
                "reason": statement.reason,
                "whatNext": statement.text,
                "scopeRefs": statement.scope_refs
            });
            for (field, packet_field) in [
                ("id", "id"),
                ("status", "kind"),
                ("reason", "reason"),
                ("whatNext", "text"),
                ("scopeRefs", "scopeRefs"),
            ] {
                let value = &row[field];
                let packet_path = format!("/boundaryStatements/{packet_index}/{packet_field}");
                append_leaf_field_mappings(
                    &mut field_map,
                    &format!("silenceRows[{row_index}].{field}"),
                    &packet_path,
                    value,
                );
                append_leaf_field_mappings(
                    &mut field_map,
                    &format!("stages[3].rows[{row_index}].{field}"),
                    &packet_path,
                    value,
                );
            }
            row
        })
        .collect::<Vec<_>>();

    for (index, invariant) in packet.computed_invariants.iter().enumerate() {
        if invariant["status"] != "silence_by_design"
            || !matches!(
                invariant["evaluator"].as_str(),
                Some("ag.saga-grounded") | Some("ag.saga-descent") | Some("ag.harmonic-debt")
            )
        {
            continue;
        }
        let row_index = silence_rows.len();
        let mut row = json!({
            "id": invariant["invariantId"],
            "status": "silence_by_design",
        });
        for field in ["reason", "whatNext"] {
            if let Some(value) = invariant.get(field).filter(|value| !value.is_null()) {
                row[field] = value.clone();
            }
        }
        for (field, packet_field) in [
            ("id", "invariantId"),
            ("status", "status"),
            ("reason", "reason"),
            ("whatNext", "whatNext"),
        ] {
            if let Some(value) = row.get(field).filter(|value| !value.is_null()) {
                let packet_path = format!("/computedInvariants/{index}/{packet_field}");
                append_leaf_field_mappings(
                    &mut field_map,
                    &format!("silenceRows[{row_index}].{field}"),
                    &packet_path,
                    value,
                );
                append_leaf_field_mappings(
                    &mut field_map,
                    &format!("stages[3].rows[{row_index}].{field}"),
                    &packet_path,
                    value,
                );
            }
        }
        silence_rows.push(row);
    }

    let grounding_status = projected_stage_status(&[&grounding_rows]);
    let descent_status =
        projected_stage_status(&[&descent_rows, &measurement_rows, &harmonic_rows]);
    let comparison_status = projected_stage_status(&[&comparison_rows]);

    json!({
        "projectionBoundary": "Every displayed measurement value is selected from the measurement packet or its SAGA-scoped boundary statements; stage status is a presentation aggregation of displayed packet rows and no viewer verdict is synthesized.",
        "sourcePacketRef": "archsig-measurement-packet.json",
        "stages": [
            {
                "stageId": "grounding",
                "order": 0,
                "status": grounding_status,
                "rows": grounding_rows,
                "measurements": [],
                "visualRole": "grounding"
            },
            {
                "stageId": "descent",
                "order": 1,
                "status": descent_status,
                "rows": descent_rows,
                "measurements": measurement_rows,
                "harmonicDebt": harmonic_rows,
                "visualRole": "descent-measurement"
            },
            {
                "stageId": "comparison",
                "order": 2,
                "status": comparison_status,
                "rows": comparison_rows,
                "visualRole": "comparison-record"
            },
            {
                "stageId": "silence",
                "order": 3,
                "status": if silence_rows.is_empty() { "not_computed" } else { "silence_by_design" },
                "rows": silence_rows.clone(),
                "visualRole": "silence"
            }
        ],
        "silenceRows": silence_rows,
        "leafFieldMap": field_map,
        "nonClaims": [
            "The projection does not create structural verdicts, comparison results, or repair decisions.",
            "A missing packet field remains absent; silence_by_design remains visible as a silence row."
        ]
    })
}

fn projected_stage_status(groups: &[&[Value]]) -> &'static str {
    let values = groups
        .iter()
        .flat_map(|group| group.iter())
        .collect::<Vec<_>>();
    if values.is_empty() {
        return "not_computed";
    }
    let statuses = values
        .iter()
        .filter_map(|value| {
            value["status"]
                .as_str()
                .or_else(|| value["verdict"].as_str())
        })
        .collect::<Vec<_>>();
    if statuses.is_empty() {
        return "measured";
    }
    if statuses.iter().all(|status| *status == "silence_by_design") {
        return "silence_by_design";
    }
    if statuses
        .iter()
        .all(|status| *status == "not_computed" || *status == "silence_by_design")
    {
        return "not_computed";
    }
    if statuses.iter().any(|status| {
        matches!(
            *status,
            "measured_nonzero" | "obstruction" | "blocked" | "residual_not_in_b1"
        )
    }) {
        return "measured_nonzero";
    }
    if statuses.iter().all(|status| {
        matches!(
            *status,
            "measured_zero" | "zero" | "established" | "derived_residual_global_coherent"
        )
    }) {
        return "measured_zero";
    }
    "measured"
}

fn saga_scope_ref(packet: &ArchSigMeasurementPacketV1, scope_ref: &str) -> bool {
    if scope_ref.starts_with("structuralVerdict/") {
        return packet.structural_verdict.iter().any(|row| {
            structural_verdict_ref(row) == scope_ref && is_saga_evaluator(&row.evaluator)
        });
    }
    if let Some(index) = scope_ref
        .strip_prefix("computedInvariants/")
        .and_then(|index| index.parse::<usize>().ok())
    {
        return packet
            .computed_invariants
            .get(index)
            .is_some_and(|row| row["evaluator"].as_str().is_some_and(is_saga_evaluator));
    }
    packet.computed_invariants.iter().any(|row| {
        row["invariantId"] == scope_ref && row["evaluator"].as_str().is_some_and(is_saga_evaluator)
    }) || packet
        .analytic_readings
        .iter()
        .any(|reading| reading.reading_id == scope_ref && is_saga_evaluator(&reading.evaluator))
}

fn is_saga_evaluator(evaluator: &str) -> bool {
    matches!(
        evaluator,
        "ag.saga-grounded" | "ag.saga-descent" | "ag.harmonic-debt"
    )
}

fn append_leaf_field_mappings(
    field_map: &mut Vec<Value>,
    viewer_path: &str,
    packet_path: &str,
    value: &Value,
) {
    match value {
        Value::Object(object) => {
            for (key, child) in object {
                append_leaf_field_mappings(
                    field_map,
                    &format!("{viewer_path}.{key}"),
                    &format!("{packet_path}/{key}"),
                    child,
                );
            }
        }
        Value::Array(array) => {
            for (index, child) in array.iter().enumerate() {
                append_leaf_field_mappings(
                    field_map,
                    &format!("{viewer_path}[{index}]"),
                    &format!("{packet_path}/{index}"),
                    child,
                );
            }
        }
        _ => field_map.push(json!({
            "viewerPath": viewer_path,
            "packetPath": packet_path
        })),
    }
}

fn top_insight_preserved_refs(insight_report: &Value) -> Vec<String> {
    let mut refs = BTreeSet::new();
    for value in string_array_at(insight_report, &["headline", "primaryVerdictRefs"]) {
        refs.insert(value);
    }
    if let Some(card) = insight_report["insightCards"]
        .as_array()
        .and_then(|cards| cards.first())
    {
        for path in [
            ["evidence", "structuralVerdictRefs"],
            ["evidence", "computedInvariantRefs"],
            ["evidence", "analyticReadingRefs"],
            ["evidence", "atomRefs"],
            ["evidence", "contextRefs"],
            ["evidence", "sourceRefs"],
            ["nextAction", "targetRefs"],
        ] {
            for value in string_array_at(card, &path) {
                refs.insert(value);
            }
        }
    }
    refs.into_iter().take(32).collect()
}

fn top_insight_atom_refs(insight_report: &Value) -> BTreeSet<String> {
    let mut refs = BTreeSet::new();
    if let Some(card) = insight_report["insightCards"]
        .as_array()
        .and_then(|cards| cards.first())
    {
        for value in string_array_at(card, &["evidence", "atomRefs"]) {
            refs.insert(value);
        }
        for value in string_array_at(card, &["viewerNavigation", "highlightRefs", "atomRefs"]) {
            refs.insert(value);
        }
    }
    refs
}

fn top_insight_context_refs(insight_report: &Value) -> BTreeSet<String> {
    let mut refs = BTreeSet::new();
    if let Some(card) = insight_report["insightCards"]
        .as_array()
        .and_then(|cards| cards.first())
    {
        for value in string_array_at(card, &["evidence", "contextRefs"]) {
            refs.insert(value);
        }
        for value in string_array_at(card, &["viewerNavigation", "highlightRefs", "contextRefs"]) {
            refs.insert(value);
        }
    }
    refs
}

fn projected_atoms(
    normalized: &NormalizedArchMapV2,
    preserved_refs: &BTreeSet<String>,
    limit: usize,
) -> Vec<NormalizedAtomV2> {
    let mut selected = Vec::new();
    let mut seen = BTreeSet::new();
    for atom in normalized.atoms.iter().filter(|atom| {
        preserved_refs.contains(atom.normalized_atom_id.as_str())
            || preserved_refs.contains(atom.source_atom_id.as_str())
    }) {
        if seen.insert(atom.normalized_atom_id.clone()) {
            selected.push(sanitize_viewer_atom(atom.clone()));
        }
    }
    for atom in &normalized.atoms {
        if selected.len() >= limit {
            break;
        }
        if seen.insert(atom.normalized_atom_id.clone()) {
            selected.push(sanitize_viewer_atom(atom.clone()));
        }
    }
    selected.truncate(limit);
    selected
}

fn projected_contexts(
    normalized: &NormalizedArchMapV2,
    preserved_refs: &BTreeSet<String>,
    limit: usize,
) -> Vec<NormalizedContextV2> {
    let mut selected = Vec::new();
    let mut seen = BTreeSet::new();
    for context in normalized.contexts.iter().filter(|context| {
        preserved_refs.contains(context.normalized_context_id.as_str())
            || preserved_refs.contains(context.source_context_id.as_str())
    }) {
        if seen.insert(context.normalized_context_id.clone()) {
            selected.push(sanitize_viewer_context(context.clone()));
        }
    }
    for context in &normalized.contexts {
        if selected.len() >= limit {
            break;
        }
        if seen.insert(context.normalized_context_id.clone()) {
            selected.push(sanitize_viewer_context(context.clone()));
        }
    }
    selected.truncate(limit);
    selected
}

fn projected_covers(normalized: &NormalizedArchMapV2, limit: usize) -> Vec<NormalizedCoverV2> {
    normalized
        .covers
        .iter()
        .take(limit)
        .cloned()
        .map(sanitize_viewer_cover)
        .collect()
}

/// Resolves a semantic source ref (an `archmap.sources` key) into the file
/// path / symbol / line evidence declared by the supplied ArchMap, following
/// one `source` indirection for symbol entries. Unresolvable refs keep the
/// bare `ref` form; the viewer must not invent locations.
fn resolved_source_ref_sample(archmap_document: &ArchMapDocumentV2, reference: &str) -> Value {
    let mut sample = json!({ "ref": reference });
    let mut cited_line = None;
    let entry = match archmap_document.sources.get(reference) {
        Some(entry) => entry,
        None => {
            let Some((base, line)) = crate::archmap::source_ref_line_base(reference) else {
                return sample;
            };
            let Some(entry) = archmap_document.sources.get(base) else {
                return sample;
            };
            cited_line = Some(line);
            entry
        }
    };
    sample["sourceKind"] = json!(entry.kind);
    let path = entry.path.clone().or_else(|| {
        entry
            .source
            .as_ref()
            .and_then(|parent| archmap_document.sources.get(parent))
            .and_then(|parent| parent.path.clone())
    });
    if let Some(path) = path {
        sample["path"] = json!(sanitize_viewer_source_path(&path));
    }
    if let Some(symbol) = &entry.symbol {
        sample["symbol"] = json!(symbol);
    }
    if let Some(line) = entry.line {
        sample["line"] = json!(line);
    }
    // A cited `:line` suffix is more specific than the source entry's own line.
    if let Some(line) = cited_line {
        sample["line"] = json!(line);
    }
    if let Some(section) = &entry.section {
        sample["section"] = json!(section);
    }
    sample
}

fn sanitize_viewer_source_path(path: &str) -> String {
    if is_local_or_private_source_ref(path) {
        "path:redacted-local-path".to_string()
    } else {
        path.to_string()
    }
}

fn viewer_atom_nodes(
    atoms: &[NormalizedAtomV2],
    archmap_document: &ArchMapDocumentV2,
    insight_report: &Value,
) -> Vec<Value> {
    let top_atoms = top_insight_atom_refs(insight_report);
    atoms
        .iter()
        .map(|atom| {
            let source_refs = atom
                .source_refs
                .iter()
                .map(|source_ref| resolved_source_ref_sample(archmap_document, source_ref))
                .collect::<Vec<_>>();
            json!({
                "nodeId": atom.normalized_atom_id,
                "sourceAtomId": atom.source_atom_id,
                "atomKind": atom.atom_kind,
                "atomFamily": atom.atom_kind,
                "subjectRef": atom.subject,
                "axis": atom.axis,
                "predicate": atom.predicate,
                "objectRef": atom.object,
                "observationStatus": atom.normalization_status,
                "normalizationStatus": atom.normalization_status,
                "moleculeMemberships": atom.context_memberships,
                "projectionRefs": atom.context_memberships,
                "sourceRefSamples": source_refs,
                "sourceRefCount": atom.source_refs.len(),
                "objectRefCount": usize::from(atom.object.is_some()),
                "priorityScore": if top_atoms.contains(atom.normalized_atom_id.as_str()) || top_atoms.contains(atom.source_atom_id.as_str()) { 100 } else { 10 },
                "labels": [atom.axis.clone(), atom.predicate.clone()]
            })
        })
        .collect()
}

fn viewer_molecule_groups(contexts: &[NormalizedContextV2]) -> Vec<Value> {
    contexts
        .iter()
        .map(|context| {
            json!({
                "groupId": context.normalized_context_id,
                "sourceMoleculeId": context.source_context_id,
                "atomObservationRefs": context.atom_ids,
                "atomIds": context.atom_ids,
                "generatedMoleculeCandidateStatus": context.poset_status,
                "requiredPortStatus": "not_applicable",
                "compositionStatus": context.poset_status
            })
        })
        .collect()
}

fn viewer_atom_edges(contexts: &[NormalizedContextV2]) -> Vec<Value> {
    let mut edges = Vec::new();
    for context in contexts {
        for target in &context.restricts_to {
            edges.push(json!({
                "edgeId": format!("edge:{}->{}", context.normalized_context_id, target),
                "sourceNodeRef": context.normalized_context_id,
                "targetNodeRef": target,
                "edgeKind": "contextRestriction"
            }));
        }
        for pair in context.atom_ids.windows(2) {
            if let [source, target] = pair {
                edges.push(json!({
                    "edgeId": format!("edge:{}:{}->{}", context.normalized_context_id, source, target),
                    "sourceNodeRef": source,
                    "targetNodeRef": target,
                    "edgeKind": "contextMembership"
                }));
            }
        }
    }
    edges
}

fn sanitize_viewer_atom(mut atom: NormalizedAtomV2) -> NormalizedAtomV2 {
    atom.source_refs = atom
        .source_refs
        .iter()
        .map(|source_ref| sanitize_source_ref(source_ref))
        .collect();
    atom
}

fn sanitize_viewer_context(mut context: NormalizedContextV2) -> NormalizedContextV2 {
    context.source_refs = context
        .source_refs
        .iter()
        .map(|source_ref| sanitize_source_ref(source_ref))
        .collect();
    context
}

fn sanitize_viewer_cover(mut cover: NormalizedCoverV2) -> NormalizedCoverV2 {
    cover.source_refs = cover
        .source_refs
        .iter()
        .map(|source_ref| sanitize_source_ref(source_ref))
        .collect();
    cover
}

fn validate_profile_refs(
    profile: &MeasurementProfileV1,
    normalized: &NormalizedArchMapV2,
) -> Result<(), String> {
    let site_resolves = profile.site_ref == "archmap:/contexts"
        || normalized.contexts.iter().any(|context| {
            context.normalized_context_id == profile.site_ref
                || context.source_context_id == profile.site_ref
        });
    if !site_resolves {
        return Err(format!(
            "measurementProfileRef {} has unresolved siteRef {}",
            profile.profile_id, profile.site_ref
        ));
    }

    let cover_resolves = normalized.covers.iter().any(|cover| {
        cover.normalized_cover_id == profile.cover_ref || cover.source_cover_id == profile.cover_ref
    });
    if !cover_resolves {
        return Err(format!(
            "measurementProfileRef {} has unresolved coverRef {}",
            profile.profile_id, profile.cover_ref
        ));
    }

    Ok(())
}
