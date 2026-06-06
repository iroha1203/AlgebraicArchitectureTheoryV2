fn build_signature_distance_readings(
    signature_axes: &[ArchSigSignatureAxisReadingV0],
    law_policy: &LawPolicyDocumentV0,
    foundation: &ArchSigPart4DistanceFoundationV0,
) -> Vec<ArchSigSignatureDistanceReadingV0> {
    if signature_axes.is_empty() {
        return Vec::new();
    }
    let coverage_refs = foundation.profile.coverage_policy_refs.clone();
    let axis_distances = signature_axes
        .iter()
        .map(|axis| signature_axis_distance(axis, foundation, &coverage_refs))
        .collect::<Vec<_>>();
    let measured_axis_refs = axis_distances
        .iter()
        .filter(|axis| matches!(axis.rho_i.status.as_str(), "measured" | "zero"))
        .map(|axis| axis.signature_axis_ref.clone())
        .collect::<Vec<_>>();
    let unmeasured_axis_refs = axis_distances
        .iter()
        .filter(|axis| matches!(axis.rho_i.status.as_str(), "unmeasured" | "blocked"))
        .map(|axis| axis.signature_axis_ref.clone())
        .collect::<Vec<_>>();
    let incomparable_axis_refs = axis_distances
        .iter()
        .filter(|axis| axis.rho_i.status == "incomparable")
        .map(|axis| axis.signature_axis_ref.clone())
        .collect::<Vec<_>>();
    let blocker_refs = axis_distances
        .iter()
        .flat_map(|axis| axis.blocker_refs.clone())
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect::<Vec<_>>();
    let total_measured_distance =
        signature_total_distance_value(&axis_distances, &blocker_refs, &coverage_refs);
    let safe_region_margin =
        signature_safe_region_margin_value(&axis_distances, &blocker_refs, &coverage_refs);
    let path_drift = signature_path_drift_value(&axis_distances, &blocker_refs, &coverage_refs);
    let endpoint_distance =
        signature_endpoint_distance_value(&axis_distances, &blocker_refs, &coverage_refs);
    let safe_region_status = if !blocker_refs.is_empty() {
        "BLOCKED_BY_COVERAGE"
    } else if axis_distances
        .iter()
        .any(|axis| axis.rho_i.measured_value.unwrap_or(0) > 0)
    {
        "OUTSIDE_SELECTED_SAFE_REGION"
    } else {
        "SAFE_WITHIN_POLICY"
    };
    let hidden_excursion_status = if !blocker_refs.is_empty() {
        "hiddenExcursionBlockedByCoverage"
    } else if path_drift.measured_value.unwrap_or(0) > 0 {
        "hiddenExcursionObservedOnSelectedAxes"
    } else {
        "noSelectedHiddenExcursion"
    };
    vec![ArchSigSignatureDistanceReadingV0 {
        signature_distance_reading_id: format!(
            "signature-distance:{}",
            stable_id(&law_policy.law_policy_id)
        ),
        distance_profile_ref: foundation.profile.profile_id.clone(),
        diagnostic_scope_ref: foundation.diagnostic_scope.scope_id.clone(),
        axis_distances,
        total_measured_distance,
        measured_axis_refs,
        unmeasured_axis_refs,
        incomparable_axis_refs,
        safe_region_status: safe_region_status.to_string(),
        safe_region_margin,
        path_drift,
        endpoint_distance,
        hidden_excursion_status: hidden_excursion_status.to_string(),
        coverage_refs,
        confidence: "selected-profile-relative".to_string(),
        evidence_boundary:
            "Signature distance is aggregated from selected LawPolicy signature axes; coverage gaps block safe-region and drift conclusions instead of becoming zero"
                .to_string(),
        non_conclusions: strings(&REQUIRED_NON_CONCLUSIONS),
    }]
}

fn attach_signature_distance_reading_refs(
    signature_axes: &mut [ArchSigSignatureAxisReadingV0],
    readings: &[ArchSigSignatureDistanceReadingV0],
) {
    let refs = readings
        .iter()
        .map(|reading| reading.signature_distance_reading_id.clone())
        .collect::<Vec<_>>();
    for axis in signature_axes {
        axis.signature_distance_reading_refs = refs.clone();
    }
}

fn signature_axis_distance(
    axis: &ArchSigSignatureAxisReadingV0,
    foundation: &ArchSigPart4DistanceFoundationV0,
    coverage_refs: &[String],
) -> ArchSigSignatureAxisDistanceV0 {
    let blocker_refs = effective_signature_axis_blockers(axis);
    let profile_weight = selected_signature_axis_weight(axis, foundation);
    let provenance_refs = unique_strings(
        axis.source_refs
            .iter()
            .cloned()
            .chain(std::iter::once(axis.signature_axis_id.clone()))
            .chain(std::iter::once(axis.law_ref.clone())),
    );
    let evaluator_basis_refs = vec![
        format!("rho_i:axis={}", axis.signature_axis_id),
        format!("axisValue:{}", axis.value),
        format!("profileWeight:{}={profile_weight}", axis.signature_axis_id),
        format!("coverageStatus:{}", axis.coverage_status),
    ];
    let rho_i = if axis.value_type != "integer"
        && axis.value_type != "count"
        && axis.value_type != "nat"
    {
        ArchSigDistanceValueV0 {
            status: "incomparable".to_string(),
            measured_value: None,
            unit: "signature-rho".to_string(),
            provenance_refs: provenance_refs.clone(),
            evaluator_basis_refs: Vec::new(),
            coverage_refs: coverage_refs.to_vec(),
            blocker_refs: vec![format!(
                "incomparable signature value type {}",
                axis.value_type
            )],
            reading: "signature rho_i is incomparable for the selected value type".to_string(),
        }
    } else {
        measured_part4_distance_value(
            axis.value,
            "signature-rho",
            provenance_refs.clone(),
            evaluator_basis_refs.clone(),
            coverage_refs,
            "rho_i is the selected signature-axis obstruction count, retained with LawPolicy and source provenance",
        )
    };
    let axis_distance = measured_part4_distance_value(
        axis.value
            .saturating_mul(1000)
            .saturating_mul(profile_weight),
        "milli-signature-distance",
        provenance_refs,
        evaluator_basis_refs,
        coverage_refs,
        "axis distance scales rho_i by the selected Part IV DistanceProfile signature weight without converting missing coverage to zero",
    );
    ArchSigSignatureAxisDistanceV0 {
        signature_axis_ref: axis.signature_axis_id.clone(),
        law_ref: axis.law_ref.clone(),
        axis_ref: axis.axis_ref.clone(),
        rho_i,
        axis_distance,
        coverage_status: axis.coverage_status.clone(),
        source_refs: axis.source_refs.clone(),
        blocker_refs,
        evidence_boundary:
            "axis distance is read from selected signature axis evidence and remains coverage-relative"
                .to_string(),
    }
}

fn selected_signature_axis_weight(
    axis: &ArchSigSignatureAxisReadingV0,
    foundation: &ArchSigPart4DistanceFoundationV0,
) -> i64 {
    foundation
        .profile
        .signature_weights
        .iter()
        .find(|weight| {
            weight.axis_ref == axis.signature_axis_id
                || weight.axis_ref == axis.axis_ref
                || weight.axis_ref == axis.law_ref
        })
        .map(|weight| weight.weight)
        .unwrap_or(1)
}

fn effective_signature_axis_blockers(axis: &ArchSigSignatureAxisReadingV0) -> Vec<String> {
    axis.missing_evidence
        .iter()
        .filter(|evidence| !evidence.starts_with("no missing evidence recorded"))
        .cloned()
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect()
}

fn signature_total_distance_value(
    axis_distances: &[ArchSigSignatureAxisDistanceV0],
    blocker_refs: &[String],
    coverage_refs: &[String],
) -> ArchSigDistanceValueV0 {
    let measured_total = axis_distances
        .iter()
        .filter_map(|axis| axis.axis_distance.measured_value)
        .sum::<i64>();
    signature_aggregate_value(
        measured_total,
        "milli-signature-distance",
        axis_distances,
        blocker_refs,
        coverage_refs,
        "total measured signature distance is the selected-axis sum; coverage blockers prevent safe-region conclusion",
    )
}

fn signature_safe_region_margin_value(
    axis_distances: &[ArchSigSignatureAxisDistanceV0],
    blocker_refs: &[String],
    coverage_refs: &[String],
) -> ArchSigDistanceValueV0 {
    let measured_total = axis_distances
        .iter()
        .filter_map(|axis| axis.rho_i.measured_value)
        .sum::<i64>();
    let margin = if measured_total == 0 { 1000 } else { 0 };
    signature_aggregate_value(
        margin,
        "milli-safe-region-margin",
        axis_distances,
        blocker_refs,
        coverage_refs,
        "safe-region margin is relative to selected zero axes and selected coverage, not global lawfulness",
    )
}

fn signature_path_drift_value(
    axis_distances: &[ArchSigSignatureAxisDistanceV0],
    blocker_refs: &[String],
    coverage_refs: &[String],
) -> ArchSigDistanceValueV0 {
    let axis_count = axis_distances.len().max(1) as i64;
    let nonzero_count = axis_distances
        .iter()
        .filter(|axis| axis.rho_i.measured_value.unwrap_or(0) > 0)
        .count() as i64;
    signature_aggregate_value(
        nonzero_count * 1000 / axis_count,
        "milli-signature-drift",
        axis_distances,
        blocker_refs,
        coverage_refs,
        "path drift records selected-axis nonzero excursion density under the current LawPolicy profile",
    )
}

fn signature_endpoint_distance_value(
    axis_distances: &[ArchSigSignatureAxisDistanceV0],
    blocker_refs: &[String],
    coverage_refs: &[String],
) -> ArchSigDistanceValueV0 {
    let max_axis = axis_distances
        .iter()
        .filter_map(|axis| axis.axis_distance.measured_value)
        .max()
        .unwrap_or(0);
    signature_aggregate_value(
        max_axis,
        "milli-signature-endpoint-distance",
        axis_distances,
        blocker_refs,
        coverage_refs,
        "endpoint distance is the maximum selected-axis signature distance over the current bounded packet",
    )
}

fn signature_aggregate_value(
    measured_value: i64,
    unit: &str,
    axis_distances: &[ArchSigSignatureAxisDistanceV0],
    blocker_refs: &[String],
    coverage_refs: &[String],
    reading: &str,
) -> ArchSigDistanceValueV0 {
    let provenance_refs = axis_distances
        .iter()
        .flat_map(|axis| {
            std::iter::once(axis.signature_axis_ref.clone()).chain(axis.source_refs.iter().cloned())
        })
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect::<Vec<_>>();
    let evaluator_basis_refs = axis_distances
        .iter()
        .flat_map(|axis| {
            [
                format!("rho_i:{}", axis.signature_axis_ref),
                format!("axisDistance:{}", axis.signature_axis_ref),
            ]
        })
        .collect::<Vec<_>>();
    if !blocker_refs.is_empty() {
        return ArchSigDistanceValueV0 {
            status: "blocked".to_string(),
            measured_value: None,
            unit: unit.to_string(),
            provenance_refs,
            evaluator_basis_refs,
            coverage_refs: coverage_refs.to_vec(),
            blocker_refs: blocker_refs.to_vec(),
            reading: reading.to_string(),
        };
    }
    measured_part4_distance_value(
        measured_value,
        unit,
        provenance_refs,
        evaluator_basis_refs,
        coverage_refs,
        reading,
    )
}

fn promote_signature_geometry_supporting_distance(
    foundation: &mut ArchSigPart4DistanceFoundationV0,
    readings: &[ArchSigSignatureDistanceReadingV0],
) {
    let Some(reading) = readings.first() else {
        return;
    };
    if let Some(distance) = foundation
        .supporting_distances
        .iter_mut()
        .find(|distance| distance.distance_family == "signatureGeometry")
    {
        distance.value = ArchSigDistanceValueV0 {
            status: reading.total_measured_distance.status.clone(),
            measured_value: reading.total_measured_distance.measured_value,
            unit: reading.total_measured_distance.unit.clone(),
            provenance_refs: reading.total_measured_distance.provenance_refs.clone(),
            evaluator_basis_refs: vec![reading.signature_distance_reading_id.clone()],
            coverage_refs: reading.coverage_refs.clone(),
            blocker_refs: reading.total_measured_distance.blocker_refs.clone(),
            reading:
                "signatureGeometry is aggregated through signatureDistanceReadings with selected-axis rho_i, safe-region margin, and drift boundary"
                    .to_string(),
        };
        distance.evidence_boundary =
            "signatureGeometry is LawPolicy-profile-relative; unmeasured or blocked axes are not safety conclusions"
                .to_string();
    }
    refresh_part4_status_summary(foundation);
}
