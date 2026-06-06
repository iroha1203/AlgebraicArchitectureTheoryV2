pub(crate) fn build_codebase_inspection_report(
    snapshot_path: &Path,
    snapshot: &serde_json::Value,
    index_path: &Path,
    index: &serde_json::Value,
    packet_path: &Path,
    packet: &serde_json::Value,
    law_policy_path: Option<&PathBuf>,
    law_policy: Option<&serde_json::Value>,
    recent_deltas: &[(PathBuf, serde_json::Value)],
    limit: usize,
) -> serde_json::Value {
    let flatness = packet
        .get("flatnessReading")
        .unwrap_or(&serde_json::Value::Null);
    let llm_packet = packet
        .get("llmInterpretationPacket")
        .unwrap_or(&serde_json::Value::Null);

    serde_json::json!({
        "schemaVersion": "archsig-codebase-inspection-report-v0",
        "mode": "codebase-inspection",
        "diagnosisKind": "current-state architectural diagnosis",
        "canonicalInputs": {
            "archMapSnapshot": {
                "path": snapshot_path.display().to_string(),
                "schemaVersion": schema_string(snapshot),
                "snapshotId": json_field(snapshot, "snapshotId"),
                "archMapRef": json_field(snapshot, "archMapRef"),
                "coveredCommitRange": json_field(snapshot, "coveredCommitRange"),
                "coverageSummary": json_field(snapshot, "coverageSummary"),
                "compactionReport": json_field(snapshot, "compactionReport")
            },
            "archMapIndex": {
                "path": index_path.display().to_string(),
                "schemaVersion": schema_string(index),
                "indexId": json_field(index, "indexId"),
                "snapshotRef": json_field(index, "snapshotRef"),
                "sourceRefKeyCount": object_key_count(index, "sourceRefIndex"),
                "atomRefKeyCount": object_key_count(index, "atomRefIndex"),
                "boundaryRefKeyCount": object_key_count(index, "boundaryRefIndex"),
                "axisRefKeyCount": object_key_count(index, "axisRefIndex"),
                "operationHintKeyCount": object_key_count(index, "operationHintIndex"),
                "featureHintKeyCount": object_key_count(index, "featureHintIndex"),
                "coverageGapKeyCount": object_key_count(index, "coverageGapIndex")
            },
            "analysisPacket": {
                "path": packet_path.display().to_string(),
                "analysisId": json_field(packet, "analysisId"),
                "archMapRef": json_field(packet, "archMapRef"),
                "selectedLawPolicyRef": json_field(packet, "selectedLawPolicyRef"),
                "archMapStoreRefs": json_field(packet, "archMapStoreRefs")
            },
            "lawPolicy": law_policy.map(|document| serde_json::json!({
                "path": law_policy_path.map(|path| path.display().to_string()),
                "schemaVersion": schema_string(document),
                "policyId": json_field(document, "policyId"),
                "profileId": json_field(document, "profileId")
            })),
            "recentDeltaWindow": recent_delta_summary(recent_deltas, limit)
        },
        "inspectionFlow": {
            "latestSnapshotRef": json_field(snapshot, "snapshotId"),
            "indexRef": json_field(index, "indexId"),
            "recentDeltaCount": recent_deltas.len(),
            "readingBoundary": "codebase inspection starts from latest ArchMapSnapshot plus ArchMapIndex and optionally narrows current-state context with a recent delta window; it does not replay all historical deltas on every run"
        },
        "currentStateDiagnosis": {
            "subsystemBoundarySummary": {
                "architectureBoundaryRefs": array_field(packet.get("architectureState").unwrap_or(&serde_json::Value::Null), "boundaryRefs"),
                "indexBoundaryKeys": object_keys(index, "boundaryRefIndex", limit),
                "boundaryReadingCount": array_len(packet, "featureBoundaryResidualReadings")
            },
            "featureLikeClusterSummary": {
                "featureIndexKeys": object_keys(index, "featureHintIndex", limit),
                "featureExtensionDiagnosisCount": array_len(packet, "featureExtensionDiagnosisReadings"),
                "featureBoundaryResidualCount": array_len(packet, "featureBoundaryResidualReadings"),
                "summary": limited_array_field(llm_packet, "featureExtensionDiagnosisSummary", limit)
            },
            "operationLikeRelationSummary": {
                "operationIndexKeys": object_keys(index, "operationHintIndex", limit),
                "operationSquareCandidateCount": array_len(packet, "operationSquareCandidates"),
                "pathContinuationTraceCount": array_len(packet, "pathContinuationTraces"),
                "monodromyFamilyStatus": reading_family_status_summary(packet, "monodromyReadingFamily"),
                "boundaryHolonomyFamilyStatus": reading_family_status_summary(packet, "boundaryHolonomyReadingFamily"),
                "summary": limited_array_field(llm_packet, "homotopyOrderSensitivitySummary", limit)
            },
            "topBoundaryHolonomy": top_boundary_holonomy(packet, limit),
            "topOrderSensitiveSquares": top_order_sensitive_squares(packet, limit),
            "architectureSpectrum": architecture_spectrum_summary(packet, llm_packet, Some(limit)),
            "architectureHomotopy": architecture_homotopy_summary(packet, Some(limit)),
            "architectureHealthNextActions": limited_array_field(llm_packet, "recommendedHumanReviewFocus", limit)
        },
        "coverageExactnessBoundary": {
            "flatnessStatus": json_field(flatness, "status"),
            "coverageGaps": array_field(flatness, "blockedByCoverageGaps"),
            "flatnessEvidenceBoundary": json_field(flatness, "evidenceBoundary"),
            "storeCompactionBoundary": json_field(packet.get("archMapStoreRefs").unwrap_or(&serde_json::Value::Null), "compactionBoundary"),
            "snapshotCompactionReport": json_field(snapshot, "compactionReport")
        },
        "surfaceBoundary": {
            "prReviewMode": "change-local diagnosis over base ArchMap / PR-local ArchMapDelta / LawPolicy",
            "codebaseInspectionMode": "current-state architectural diagnosis over latest ArchMapSnapshot / ArchMapIndex / analysis packet",
            "fieldSigBoundary": "FieldSig owns PR / diff / change-vector evolution analysis, forecast, governance, calibration, and longitudinal monitoring"
        },
        "nonConclusions": [
            "ArchSig codebase inspection does not prove repository-wide lawfulness",
            "ArchSig codebase inspection does not prove global safety",
            "ArchSig codebase inspection is not PR / diff evolution analysis",
            "ArchSig codebase inspection does not replace FieldSig longitudinal evolution monitoring",
            "Missing index entries are not absence evidence unless index coverage states a complete universe"
        ]
    })
}

fn recent_delta_summary(
    recent_deltas: &[(PathBuf, serde_json::Value)],
    limit: usize,
) -> serde_json::Value {
    serde_json::Value::Array(
        recent_deltas
            .iter()
            .take(limit)
            .map(|(path, document)| {
                serde_json::json!({
                    "path": path.display().to_string(),
                    "schemaVersion": schema_string(document),
                    "deltaId": json_field(document, "deltaId"),
                    "changedObservationRefs": array_field(document, "changedObservationRefs"),
                    "nonConclusions": array_field(document, "nonConclusions")
                })
            })
            .collect(),
    )
}

fn top_boundary_holonomy(packet: &serde_json::Value, limit: usize) -> serde_json::Value {
    let mut readings = array_items(packet, "featureBoundaryResidualReadings");
    readings.sort_by_key(|reading| std::cmp::Reverse(boundary_residual_score(reading)));
    serde_json::Value::Array(
        readings
            .into_iter()
            .take(limit)
            .map(|reading| {
                serde_json::json!({
                    "readingId": json_field(reading, "readingId"),
                    "boundaryRef": json_field(reading, "boundaryRef"),
                    "status": json_field(reading, "status"),
                    "residualScore": boundary_residual_score(reading),
                    "mixedSubconfigurationRefs": array_field(reading, "mixedSubconfigurationRefs"),
                    "boundarySupportRefs": array_field(reading, "boundarySupportRefs"),
                    "topHolonomyAxes": top_holonomy_axes(reading, 4)
                })
            })
            .collect(),
    )
}

fn top_holonomy_axes(reading: &serde_json::Value, limit: usize) -> serde_json::Value {
    let mut axes = array_items(reading, "holonomyAxes");
    axes.sort_by_key(|axis| std::cmp::Reverse(i64_field(axis, "residualValue", 0)));
    serde_json::Value::Array(
        axes.into_iter()
            .take(limit)
            .map(|axis| {
                serde_json::json!({
                    "axisFamily": json_field(axis, "axisFamily"),
                    "status": json_field(axis, "status"),
                    "residualValue": json_field(axis, "residualValue"),
                    "measuredDefectRefs": array_field(axis, "measuredDefectRefs"),
                    "missingEvidence": array_field(axis, "missingEvidence")
                })
            })
            .collect(),
    )
}

fn boundary_residual_score(reading: &serde_json::Value) -> i64 {
    array_items(reading, "holonomyAxes")
        .into_iter()
        .map(|axis| i64_field(axis, "residualValue", 0))
        .sum()
}

fn top_order_sensitive_squares(packet: &serde_json::Value, limit: usize) -> serde_json::Value {
    let mut witnesses = array_items(packet, "nonzeroMonodromyWitnesses");
    witnesses.sort_by_key(|witness| std::cmp::Reverse(i64_field(witness, "defectValue", 0)));
    serde_json::Value::Array(
        witnesses
            .into_iter()
            .take(limit)
            .map(|witness| {
                serde_json::json!({
                    "witnessId": json_field(witness, "witnessId"),
                    "candidateRef": json_field(witness, "candidateRef"),
                    "axisFamily": json_field(witness, "axisFamily"),
                    "defectValue": json_field(witness, "defectValue"),
                    "operationPair": array_field(witness, "operationPair"),
                    "pathPair": array_field(witness, "pathPair"),
                    "coverageBoundary": json_field(witness, "coverageBoundary"),
                    "recommendedReviewFocus": array_field(witness, "recommendedReviewFocus")
                })
            })
            .collect(),
    )
}
