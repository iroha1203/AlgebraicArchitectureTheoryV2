fn detail_index(packet: &serde_json::Value) -> serde_json::Value {
    serde_json::json!({
        "packetRefSyntax": "packet:<json-pointer>",
        "sections": [
            detail_index_section("signatureAxes", "/signatureAxes", array_len(packet, "signatureAxes")),
            detail_index_section("part4DistanceFoundation", "/part4DistanceFoundation", object_key_count(packet, "part4DistanceFoundation")),
            detail_index_section("atomDistanceReadings", "/atomDistanceReadings", array_len(packet, "atomDistanceReadings")),
            detail_index_section("configurationDistanceReadings", "/configurationDistanceReadings", array_len(packet, "configurationDistanceReadings")),
            detail_index_section("signatureDistanceReadings", "/signatureDistanceReadings", array_len(packet, "signatureDistanceReadings")),
            detail_index_section("operationDistanceReadings", "/operationDistanceReadings", array_len(packet, "operationDistanceReadings")),
            detail_index_section("curvatureMassReadings", "/curvatureMassReadings", array_len(packet, "curvatureMassReadings")),
            detail_index_section("homotopyDistanceReadings", "/homotopyDistanceReadings", array_len(packet, "homotopyDistanceReadings")),
            detail_index_section("representationMetricReadings", "/representationMetricReadings", array_len(packet, "representationMetricReadings")),
            detail_index_section("architectureSpectrumReport.topHotspots", "/architectureSpectrumReport/topHotspots", array_len(packet.get("architectureSpectrumReport").unwrap_or(&serde_json::Value::Null), "topHotspots")),
            detail_index_section("architectureSpectrumReport.recurrentObstructions", "/architectureSpectrumReport/recurrentObstructions", array_len(packet.get("architectureSpectrumReport").unwrap_or(&serde_json::Value::Null), "recurrentObstructions")),
            detail_index_section("architectureHomotopyReport.unfilledLoops", "/architectureHomotopyReport/unfilledLoops", array_len(packet.get("architectureHomotopyReport").unwrap_or(&serde_json::Value::Null), "unfilledLoops")),
            detail_index_section("architectureHomotopyReport.nonzeroHolonomyLoops", "/architectureHomotopyReport/nonzeroHolonomyLoops", array_len(packet.get("architectureHomotopyReport").unwrap_or(&serde_json::Value::Null), "nonzeroHolonomyLoops")),
            detail_index_section("transferBridgeReadings", "/transferBridgeReadings", array_len(packet, "transferBridgeReadings")),
            detail_index_section("observationProjectionFidelityReadings", "/observationProjectionFidelityReadings", array_len(packet, "observationProjectionFidelityReadings")),
            detail_index_section("atomOriginClosureDebtReadings", "/atomOriginClosureDebtReadings", array_len(packet, "atomOriginClosureDebtReadings")),
            detail_index_section("effectRelationAlgebraReadings", "/effectRelationAlgebraReadings", array_len(packet, "effectRelationAlgebraReadings")),
            detail_index_section("synthesisBlockageReadings", "/synthesisBlockageReadings", array_len(packet, "synthesisBlockageReadings")),
            detail_index_section("operationPreconditionReadinessReadings", "/operationPreconditionReadinessReadings", array_len(packet, "operationPreconditionReadinessReadings")),
            detail_index_section("pathMultiplicityLossReadings", "/pathMultiplicityLossReadings", array_len(packet, "pathMultiplicityLossReadings")),
            detail_index_section("llmInterpretationPacket", "/llmInterpretationPacket", object_key_count(packet, "llmInterpretationPacket"))
        ]
    })
}

fn detail_index_section(name: &str, path: &str, count: usize) -> serde_json::Value {
    serde_json::json!({
        "name": name,
        "packetRef": packet_ref(path),
        "count": count
    })
}

fn detail_refs(_section: &str, path: &str) -> serde_json::Value {
    serde_json::json!([packet_ref(path)])
}

fn trend_insights(packet: &serde_json::Value) -> serde_json::Value {
    serde_json::json!({
        "insightCount": 5,
        "items": [
            cross_axis_cooccurrence_insight(packet),
            operation_freedom_loss_insight(packet),
            path_continuation_defect_insight(packet),
            boundary_residual_localization_insight(packet),
            repair_transfer_risk_insight(packet)
        ]
    })
}

fn cross_axis_cooccurrence_insight(packet: &serde_json::Value) -> serde_json::Value {
    let mut clusters = support_contribution_clusters(packet);
    clusters.sort_by(|left, right| {
        right
            .kind_count
            .cmp(&left.kind_count)
            .then(right.evidence_count.cmp(&left.evidence_count))
            .then(left.support_ref.cmp(&right.support_ref))
    });
    let cluster = clusters.first();
    serde_json::json!({
        "kind": "crossAxisCooccurrence",
        "claim": if cluster.is_some() {
            "multiple readings concentrate on one architecture support"
        } else {
            "no cross-axis support cluster was measured"
        },
        "whyNontrivial": "Intersects law-axis, spectrum, homotopy, bridge, and operation support.",
        "measurement": {
            "clusterCount": clusters.len(),
            "maxReadingKindCount": cluster.map(|cluster| cluster.kind_count).unwrap_or_default()
        },
        "packetRefs": packet_refs(&[
            "/signatureAxes",
            "/architectureSpectrumReport/topHotspots",
            "/architectureHomotopyReport",
            "/transferBridgeReadings"
        ])
    })
}

#[derive(Debug)]
struct SupportCluster {
    support_ref: String,
    reading_kinds: BTreeSet<String>,
    evidence_refs: BTreeSet<String>,
    kind_count: usize,
    evidence_count: usize,
}

fn support_contribution_clusters(packet: &serde_json::Value) -> Vec<SupportCluster> {
    let mut clusters = BTreeMap::<String, SupportCluster>::new();
    for (index, axis) in array_items(packet, "signatureAxes").into_iter().enumerate() {
        if i64_field(axis, "value", 0) == 0 {
            continue;
        }
        let evidence_ref = format!("packet:/signatureAxes/{index}");
        for support in string_array(axis, "sourceRefs")
            .into_iter()
            .chain(optional_string(axis, "axisRef"))
            .chain(optional_string(axis, "lawRef"))
        {
            push_support_contribution(
                &mut clusters,
                "nonzeroSignatureAxis",
                &support,
                &evidence_ref,
            );
        }
    }

    let spectrum = packet
        .get("architectureSpectrumReport")
        .unwrap_or(&serde_json::Value::Null);
    for (index, hotspot) in array_items(spectrum, "topHotspots").into_iter().enumerate() {
        let evidence_ref = format!("packet:/architectureSpectrumReport/topHotspots/{index}");
        for support in string_array(hotspot, "supportRefs")
            .into_iter()
            .chain(string_array(hotspot, "witnessRefs"))
            .chain(optional_string(hotspot, "axisRef"))
        {
            push_support_contribution(&mut clusters, "spectrumHotspot", &support, &evidence_ref);
        }
    }
    for (index, recurrent) in array_items(spectrum, "recurrentObstructions")
        .into_iter()
        .enumerate()
    {
        let evidence_ref = format!("/architectureSpectrumReport/recurrentObstructions/{index}");
        for support in string_array(recurrent, "supportRefs")
            .into_iter()
            .chain(string_array(recurrent, "witnessRefs"))
            .chain(optional_string(recurrent, "modeRef"))
        {
            push_support_contribution(
                &mut clusters,
                "recurrentObstruction",
                &support,
                &format!("packet:{evidence_ref}"),
            );
        }
    }

    let homotopy = packet
        .get("architectureHomotopyReport")
        .unwrap_or(&serde_json::Value::Null);
    for (index, loop_ref) in array_items(homotopy, "unfilledLoops")
        .into_iter()
        .enumerate()
    {
        if let Some(support) = loop_ref.as_str() {
            push_support_contribution(
                &mut clusters,
                "architecturalHole",
                support,
                &format!("packet:/architectureHomotopyReport/unfilledLoops/{index}"),
            );
        }
    }
    for (index, loop_ref) in array_items(homotopy, "nonzeroHolonomyLoops")
        .into_iter()
        .enumerate()
    {
        if let Some(support) = loop_ref.as_str() {
            push_support_contribution(
                &mut clusters,
                "nonzeroHolonomy",
                support,
                &format!("packet:/architectureHomotopyReport/nonzeroHolonomyLoops/{index}"),
            );
        }
    }

    for (reading_index, reading) in array_items(packet, "transferBridgeReadings")
        .into_iter()
        .enumerate()
    {
        for (bridge_index, bridge) in array_items(reading, "bridgeAtomFamilies")
            .into_iter()
            .enumerate()
        {
            let evidence_ref = format!(
                "packet:/transferBridgeReadings/{reading_index}/bridgeAtomFamilies/{bridge_index}"
            );
            for support in optional_string(bridge, "sourceHubMoleculeRef")
                .chain(optional_string(bridge, "targetHubMoleculeRef"))
                .chain(string_array(bridge, "intermediateMoleculeRefs"))
                .chain(
                    string_array(bridge, "sharedAxisRefs")
                        .into_iter()
                        .map(|axis| format!("axis:{axis}")),
                )
            {
                push_support_contribution(&mut clusters, "bridgePressure", &support, &evidence_ref);
            }
        }
    }

    clusters
        .into_values()
        .filter_map(|mut cluster| {
            cluster.kind_count = cluster.reading_kinds.len();
            cluster.evidence_count = cluster.evidence_refs.len();
            (cluster.kind_count >= 2 && cluster.evidence_count >= 2).then_some(cluster)
        })
        .collect()
}

fn push_support_contribution(
    clusters: &mut BTreeMap<String, SupportCluster>,
    kind: &str,
    support_ref: &str,
    evidence_ref: &str,
) {
    let normalized = normalize_support_ref(support_ref);
    if normalized.is_empty() {
        return;
    }
    let cluster = clusters
        .entry(normalized.clone())
        .or_insert(SupportCluster {
            support_ref: normalized,
            reading_kinds: BTreeSet::new(),
            evidence_refs: BTreeSet::new(),
            kind_count: 0,
            evidence_count: 0,
        });
    cluster.reading_kinds.insert(kind.to_string());
    cluster.evidence_refs.insert(evidence_ref.to_string());
}

fn normalize_support_ref(value: &str) -> String {
    let trimmed = value.trim();
    let normalized = trimmed
        .strip_prefix("molecule-reading:")
        .map(|value| format!("molecule:{value}"))
        .unwrap_or_else(|| trimmed.to_string());
    normalized
        .replace("axis-", "axis:")
        .replace("law-", "law:")
        .to_ascii_lowercase()
}

fn operation_freedom_loss_insight(packet: &serde_json::Value) -> serde_json::Value {
    let galois = array_items(packet, "operationInvariantGaloisReadings")
        .into_iter()
        .next();
    let blocked_operation_refs = galois
        .map(|reading| string_array(reading, "blockedOperationRefs"))
        .unwrap_or_default();
    let blocked_operations = blocked_operation_refs
        .iter()
        .map(String::as_str)
        .collect::<BTreeSet<_>>();
    let blocked_preconditions = array_items(packet, "operationPreconditionReadinessReadings")
        .into_iter()
        .filter(|reading| {
            reading
                .get("operationRef")
                .and_then(serde_json::Value::as_str)
                .is_some_and(|operation| blocked_operations.contains(operation))
                || json_field(reading, "readinessStatus")
                    .as_str()
                    .is_some_and(|status| status.contains("blocked"))
        })
        .collect::<Vec<_>>();
    let missing_precondition_count = blocked_preconditions
        .iter()
        .map(|reading| array_len(reading, "missingPreconditionRefs"))
        .sum::<usize>();
    serde_json::json!({
        "kind": "operationFreedomLoss",
        "claim": if blocked_operation_refs.is_empty() && missing_precondition_count == 0 {
            "no operation freedom loss was measured for the selected invariant family"
        } else {
            "selected invariants narrow the observed operation family"
        },
        "whyNontrivial": "Intersects Galois reading, preconditions, and transfer evidence.",
        "measurement": {
            "blockedOperationCount": blocked_operation_refs.len(),
            "missingPreconditionCount": missing_precondition_count
        },
        "packetRefs": packet_refs(&["/operationInvariantGaloisReadings"])
    })
}

fn path_continuation_defect_insight(packet: &serde_json::Value) -> serde_json::Value {
    let mut defects = array_items(packet, "axisWiseMonodromyDefects");
    defects.sort_by_key(|defect| {
        std::cmp::Reverse(
            defect
                .get("distanceValue")
                .and_then(serde_json::Value::as_i64)
                .unwrap_or(-1),
        )
    });
    let top_defect = defects.iter().find(|defect| {
        defect
            .get("distanceValue")
            .and_then(serde_json::Value::as_i64)
            .is_some_and(|value| value > 0)
    });
    let positive_defect_count = defects
        .iter()
        .filter(|defect| {
            defect
                .get("distanceValue")
                .and_then(serde_json::Value::as_i64)
                .is_some_and(|value| value > 0)
        })
        .count();
    let unmeasured_defect_count = defects
        .iter()
        .filter(|defect| json_field(defect, "measurementStatus").as_str() == Some("unmeasured"))
        .count();
    serde_json::json!({
        "kind": "pathContinuationDefect",
        "claim": if top_defect.is_some() {
            "same-endpoint candidates diverge on a selected continuation axis"
        } else if unmeasured_defect_count > 0 {
            "path continuation cannot be read as zero because selected axes remain unmeasured"
        } else {
            "no nonzero selected-axis continuation defect was measured"
        },
        "whyNontrivial": "Compares p/q continuation traces axis by axis.",
        "measurement": {
            "positiveDefectCount": positive_defect_count,
            "unmeasuredDefectCount": unmeasured_defect_count,
            "topAxisFamily": top_defect.and_then(|defect| defect.get("axisFamily").and_then(serde_json::Value::as_str)).unwrap_or("none")
        },
        "packetRefs": packet_refs(&["/axisWiseMonodromyDefects"])
    })
}

fn boundary_residual_localization_insight(packet: &serde_json::Value) -> serde_json::Value {
    let residual = array_items(packet, "featureBoundaryResidualReadings")
        .into_iter()
        .max_by_key(|reading| {
            array_items(reading, "holonomyAxes")
                .into_iter()
                .filter_map(|axis| {
                    axis.get("residualValue")
                        .and_then(serde_json::Value::as_i64)
                })
                .sum::<i64>()
        });
    let measured_axis_refs = residual
        .map(|reading| {
            array_items(reading, "holonomyAxes")
                .into_iter()
                .filter(|axis| json_field(axis, "status").as_str() == Some("measuredResidual"))
                .filter_map(|axis| {
                    axis.get("holonomyAxisRef")
                        .and_then(serde_json::Value::as_str)
                })
                .map(str::to_string)
                .collect::<Vec<_>>()
        })
        .unwrap_or_default();
    let coverage_blocked_count = residual
        .map(|reading| {
            array_items(reading, "holonomyAxes")
                .into_iter()
                .filter(|axis| json_field(axis, "status").as_str() == Some("coverageBlocked"))
                .count()
        })
        .unwrap_or_default();
    let boundary_support_count = residual
        .map(|reading| array_len(reading, "boundarySupportRefs"))
        .unwrap_or_default();
    serde_json::json!({
        "kind": "boundaryResidualLocalization",
        "claim": if !measured_axis_refs.is_empty() {
            "residual obstruction localizes on boundary holonomy axes"
        } else if coverage_blocked_count > 0 {
            "boundary residual localization is blocked by missing selected-axis evidence"
        } else {
            "no boundary-local residual obstruction was measured"
        },
        "whyNontrivial": "Separates core, feature, boundary support, residual axes, and coverage.",
        "measurement": {
            "measuredBoundaryAxisCount": measured_axis_refs.len(),
            "coverageBlockedBoundaryAxisCount": coverage_blocked_count,
            "boundarySupportCount": boundary_support_count
        },
        "packetRefs": packet_refs(&["/featureBoundaryResidualReadings"])
    })
}

fn repair_transfer_risk_insight(packet: &serde_json::Value) -> serde_json::Value {
    let mut deltas = array_items(packet, "operationDeltas");
    deltas.sort_by_key(|delta| std::cmp::Reverse(array_len(delta, "transferredObstructions")));
    let delta = deltas.first().copied();
    let transfer_refs = delta
        .map(|delta| string_array(delta, "transferredObstructions"))
        .unwrap_or_default();
    let decreased_axes = delta
        .map(|delta| string_array(delta, "decreasedAxes"))
        .unwrap_or_default();
    let bridge_refs = array_items(packet, "bridgeSplitObstructionTransferReadings")
        .into_iter()
        .flat_map(|reading| {
            optional_string(reading, "readingId")
                .chain(string_array(reading, "bridgeEdgeRefs"))
                .chain(string_array(reading, "obstructionRefs"))
        })
        .collect::<Vec<_>>();
    serde_json::json!({
        "kind": "repairTransferRisk",
        "claim": if !transfer_refs.is_empty() {
            "candidate repair carries explicit transfer risk"
        } else if !bridge_refs.is_empty() {
            "repair planning depends on bridge-split obstruction transfer evidence"
        } else {
            "no repair transfer risk was measured"
        },
        "whyNontrivial": "Pairs decreased axes with transfer, invariants, bridges, and missing evidence.",
        "measurement": {
            "decreasesAxisCount": decreased_axes.len(),
            "transferRiskCount": transfer_refs.len(),
            "bridgeEvidenceCount": bridge_refs.len()
        },
        "packetRefs": packet_refs(&["/operationDeltas"])
    })
}

fn optional_string(value: &serde_json::Value, key: &str) -> std::vec::IntoIter<String> {
    value
        .get(key)
        .and_then(serde_json::Value::as_str)
        .map(|text| vec![text.to_string()])
        .unwrap_or_default()
        .into_iter()
}

fn compact_ref_list(
    container: &serde_json::Value,
    key: &str,
    ref_key: &str,
    limit: usize,
) -> serde_json::Value {
    serde_json::Value::Array(
        array_items(container, key)
            .into_iter()
            .take(limit)
            .filter_map(|item| {
                item.get(ref_key)
                    .and_then(serde_json::Value::as_str)
                    .map(|text| serde_json::Value::String(text.to_string()))
            })
            .collect(),
    )
}

fn nonzero_axis_ref_list(packet: &serde_json::Value, limit: usize) -> serde_json::Value {
    serde_json::Value::Array(
        array_items(packet, "signatureAxes")
            .into_iter()
            .filter(|axis| i64_field(axis, "value", 0) != 0)
            .take(limit)
            .filter_map(|axis| {
                axis.get("signatureAxisId")
                    .and_then(serde_json::Value::as_str)
                    .map(|text| serde_json::Value::String(text.to_string()))
            })
            .collect(),
    )
}

fn bridge_pressure_ref_list(packet: &serde_json::Value, limit: usize) -> serde_json::Value {
    serde_json::Value::Array(
        bridge_pressure_actions(packet)
            .into_iter()
            .take(limit)
            .filter_map(|reading| {
                reading
                    .get("ref")
                    .and_then(serde_json::Value::as_str)
                    .map(|text| serde_json::Value::String(text.to_string()))
            })
            .collect(),
    )
}

fn homotopy_ref_list(packet: &serde_json::Value, key: &str, limit: usize) -> serde_json::Value {
    let homotopy = packet
        .get("architectureHomotopyReport")
        .unwrap_or(&serde_json::Value::Null);
    serde_json::Value::Array(
        array_items(homotopy, key)
            .into_iter()
            .take(limit)
            .filter_map(|item| {
                item.as_str()
                    .map(|text| serde_json::Value::String(text.to_string()))
            })
            .collect(),
    )
}

fn array_len_keyless(value: &serde_json::Value) -> usize {
    value.as_array().map(Vec::len).unwrap_or_default()
}

fn packet_refs(paths: &[&str]) -> serde_json::Value {
    serde_json::Value::Array(
        paths
            .iter()
            .map(|path| serde_json::Value::String(packet_ref(path)))
            .collect(),
    )
}

fn packet_ref(path: &str) -> String {
    format!("packet:{path}")
}

fn measurement_basis(
    packet: &serde_json::Value,
    archmap_validation: Option<&serde_json::Value>,
    law_policy_validation: Option<&serde_json::Value>,
    analysis_validation: Option<&serde_json::Value>,
) -> serde_json::Value {
    let spectrum = packet
        .get("architectureSpectrumReport")
        .unwrap_or(&serde_json::Value::Null);
    let homotopy = packet
        .get("architectureHomotopyReport")
        .unwrap_or(&serde_json::Value::Null);
    serde_json::json!({
        "archMapRef": json_field(packet, "archMapRef"),
        "selectedLawPolicyRef": json_field(packet, "selectedLawPolicyRef"),
        "spectrumProfileRef": json_field(spectrum, "profileRef"),
        "homotopyProfileRef": json_field(homotopy, "profileRef"),
        "validation": {
            "archmap": validation_result(archmap_validation),
            "lawPolicy": validation_result(law_policy_validation),
            "analysis": validation_result(analysis_validation)
        },
        "coverageGaps": json_string_array(coverage_gap_refs(packet).iter()),
        "monodromyFamily": reading_family_status_summary(packet, "monodromyReadingFamily"),
        "boundaryHolonomyFamily": reading_family_status_summary(packet, "boundaryHolonomyReadingFamily"),
        "spectrumMeasuredBoundary": json_field(spectrum, "measuredBoundary"),
        "homotopyMeasuredBoundary": json_field(homotopy, "measuredBoundary"),
        "projectionFidelityBoundary": first_string_field(packet, "observationProjectionFidelityReadings", "measurementBoundary"),
        "atomOriginBoundary": first_string_field(packet, "atomOriginClosureDebtReadings", "evidenceBoundary"),
        "effectRelationBoundary": first_string_field(packet, "effectRelationAlgebraReadings", "evidenceBoundary"),
        "synthesisBoundary": first_string_field(packet, "synthesisBlockageReadings", "synthesisBoundary"),
        "operationPreconditionBoundary": first_string_field(packet, "operationPreconditionReadinessReadings", "candidateBoundary"),
        "pathMultiplicityBoundary": first_string_field(packet, "pathMultiplicityLossReadings", "homotopyBoundary"),
        "basisStatement": "conclusions are measured from the supplied ArchMap and selected LawPolicy"
    })
}

fn reading_family_status_summary(
    packet: &serde_json::Value,
    family_key: &str,
) -> serde_json::Value {
    let family = packet.get(family_key).unwrap_or(&serde_json::Value::Null);
    serde_json::json!({
        "status": json_field(family, "status"),
        "measuredAxisCount": json_field(family, "measuredAxisCount"),
        "unmeasuredAxisCount": json_field(family, "unmeasuredAxisCount"),
        "positiveWitnessCount": json_field(family, "positiveWitnessCount"),
        "coverageBlockerCount": json_field(family, "coverageBlockerCount")
    })
}

fn first_string_field(
    packet: &serde_json::Value,
    array_key: &str,
    field_key: &str,
) -> serde_json::Value {
    packet
        .get(array_key)
        .and_then(serde_json::Value::as_array)
        .and_then(|items| items.first())
        .and_then(|item| item.get(field_key))
        .cloned()
        .unwrap_or(serde_json::Value::Null)
}

fn validation_result(report: Option<&serde_json::Value>) -> serde_json::Value {
    validation_summary(report)
        .get("result")
        .cloned()
        .unwrap_or(serde_json::Value::Null)
}

fn coverage_gap_refs(packet: &serde_json::Value) -> BTreeSet<String> {
    let mut refs = BTreeSet::new();
    if let Some(flatness) = packet.get("flatnessReading") {
        collect_value_labels(array_items(flatness, "blockedByCoverageGaps"), &mut refs);
    }
    if let Some(spectrum) = packet.get("architectureSpectrumReport") {
        collect_value_labels(array_items(spectrum, "coverageGaps"), &mut refs);
    }
    if let Some(homotopy) = packet.get("architectureHomotopyReport") {
        collect_value_labels(array_items(homotopy, "coverageGaps"), &mut refs);
    }
    refs
}

fn collect_value_labels(items: Vec<&serde_json::Value>, refs: &mut BTreeSet<String>) {
    for item in items {
        if let Some(label) = value_label(item) {
            refs.insert(label);
        }
    }
}

fn value_label(value: &serde_json::Value) -> Option<String> {
    value
        .as_str()
        .map(normalize_gap_label)
        .or_else(|| {
            value
                .get("gapId")
                .and_then(serde_json::Value::as_str)
                .map(normalize_gap_label)
        })
        .or_else(|| {
            value
                .get("id")
                .and_then(serde_json::Value::as_str)
                .map(normalize_gap_label)
        })
        .or_else(|| {
            value
                .get("description")
                .and_then(serde_json::Value::as_str)
                .map(normalize_gap_label)
        })
}

fn normalize_gap_label(value: &str) -> String {
    let trimmed = value.trim();
    if let Some(rest) = trimmed.strip_prefix("gap:") {
        let parts = rest.split(':').take(2).collect::<Vec<_>>();
        if parts.len() == 2 && parts.iter().all(|part| !part.trim().is_empty()) {
            return format!("gap:{}:{}", parts[0].trim(), parts[1].trim());
        }
    }
    if let Some(rest) = trimmed.strip_prefix("coverage:") {
        let label = rest.split(':').next().unwrap_or("").trim();
        if !label.is_empty() {
            return format!("coverage:{label}");
        }
    }
    if let Some((id, _)) = trimmed.split_once(':') {
        let id = id.trim();
        if !id.contains(' ') && !id.is_empty() {
            return id.to_string();
        }
    }
    trimmed.to_string()
}

fn validation_summary(report: Option<&serde_json::Value>) -> serde_json::Value {
    let Some(report) = report else {
        return serde_json::Value::Null;
    };
    if let Some(summary) = report.get("summary") {
        return summary.clone();
    }
    serde_json::json!({
        "result": json_field(report, "status"),
        "failedCheckCount": json_field(report, "failedChecks"),
        "warningCheckCount": json_field(report, "warningChecks"),
        "passedCheckCount": json_field(report, "passedChecks")
    })
}

fn architecture_spectrum_summary(
    packet: &serde_json::Value,
    llm_packet: &serde_json::Value,
    limit: Option<usize>,
) -> serde_json::Value {
    let report = packet
        .get("architectureSpectrumReport")
        .unwrap_or(&serde_json::Value::Null);
    serde_json::json!({
        "reportId": json_field(report, "reportId"),
        "status": json_field(report, "status"),
        "measurementStatus": json_field(report, "measurementStatus"),
        "readingBoundary": json_field(report, "readingBoundary"),
        "profileRef": json_field(report, "profileRef"),
        "summary": array_field_with_limit(llm_packet, "architectureSpectrumReportSummary", limit),
        "hotspots": array_field_with_limit(report, "topHotspots", limit),
        "topEigenmodes": array_field_with_limit(report, "topEigenmodes", limit),
        "witnessClusters": array_field_with_limit(report, "topWitnessClusters", limit),
        "recurrentObstructions": array_field_with_limit(report, "recurrentObstructions", limit),
        "coverageGaps": array_field_with_limit(report, "coverageGaps", limit),
        "measuredBoundary": json_field(report, "measuredBoundary"),
        "recommendedReviewFocus": array_field_with_limit(report, "recommendedReviewFocus", limit),
        "nonConclusions": array_field(report, "nonConclusions")
    })
}

fn architecture_homotopy_summary(
    packet: &serde_json::Value,
    limit: Option<usize>,
) -> serde_json::Value {
    let report = packet
        .get("architectureHomotopyReport")
        .unwrap_or(&serde_json::Value::Null);
    serde_json::json!({
        "reportId": json_field(report, "reportId"),
        "status": json_field(report, "status"),
        "measurementStatus": json_field(report, "measurementStatus"),
        "readingBoundary": json_field(report, "readingBoundary"),
        "profileRef": json_field(report, "profileRef"),
        "filledLoops": array_field_with_limit(report, "filledLoops", limit),
        "unfilledLoops": array_field_with_limit(report, "unfilledLoops", limit),
        "nonzeroHolonomyLoops": array_field_with_limit(report, "nonzeroHolonomyLoops", limit),
        "topLocalCurvatureCells": array_field_with_limit(report, "topLocalCurvatureCells", limit),
        "aggregateReadings": array_field_with_limit(report, "aggregateReadings", limit),
        "coverageGaps": array_field_with_limit(report, "coverageGaps", limit),
        "measuredBoundary": json_field(report, "measuredBoundary"),
        "recommendedReviewFocus": array_field_with_limit(report, "recommendedReviewFocus", limit),
        "nonConclusions": array_field(report, "nonConclusions")
    })
}

pub(crate) fn json_field(value: &serde_json::Value, key: &str) -> serde_json::Value {
    value.get(key).cloned().unwrap_or(serde_json::Value::Null)
}

fn array_field(value: &serde_json::Value, key: &str) -> serde_json::Value {
    serde_json::Value::Array(array_items(value, key).into_iter().cloned().collect())
}

pub(crate) fn array_field_with_limit(
    value: &serde_json::Value,
    key: &str,
    limit: Option<usize>,
) -> serde_json::Value {
    let items = array_items(value, key).into_iter();
    match limit {
        Some(limit) => serde_json::Value::Array(items.take(limit).cloned().collect()),
        None => serde_json::Value::Array(items.cloned().collect()),
    }
}

fn limited_array_field(value: &serde_json::Value, key: &str, limit: usize) -> serde_json::Value {
    serde_json::Value::Array(
        array_items(value, key)
            .into_iter()
            .take(limit)
            .cloned()
            .collect(),
    )
}

pub(crate) fn array_items<'a>(
    value: &'a serde_json::Value,
    key: &str,
) -> Vec<&'a serde_json::Value> {
    value
        .get(key)
        .and_then(serde_json::Value::as_array)
        .map(|items| items.iter().collect())
        .unwrap_or_default()
}

fn array_len(value: &serde_json::Value, key: &str) -> usize {
    value
        .get(key)
        .and_then(serde_json::Value::as_array)
        .map(Vec::len)
        .unwrap_or_default()
}

fn ref_count(value: &serde_json::Value, key: &str) -> usize {
    let Some(value) = value.get(key) else {
        return 0;
    };
    value
        .as_array()
        .map(Vec::len)
        .or_else(|| {
            value
                .get("refCount")
                .and_then(serde_json::Value::as_u64)
                .map(|count| count as usize)
        })
        .unwrap_or_default()
}

fn object_key_count(value: &serde_json::Value, key: &str) -> usize {
    value
        .get(key)
        .and_then(serde_json::Value::as_object)
        .map(serde_json::Map::len)
        .unwrap_or_default()
}

fn object_keys(value: &serde_json::Value, key: &str, limit: usize) -> serde_json::Value {
    let mut keys: Vec<_> = value
        .get(key)
        .and_then(serde_json::Value::as_object)
        .map(|object| object.keys().cloned().collect())
        .unwrap_or_default();
    keys.sort();
    serde_json::Value::Array(
        keys.into_iter()
            .take(limit)
            .map(serde_json::Value::String)
            .collect(),
    )
}

fn i64_field(value: &serde_json::Value, key: &str, default: i64) -> i64 {
    value
        .get(key)
        .and_then(serde_json::Value::as_i64)
        .unwrap_or(default)
}
