fn build_distance_diagnosis_summary(
    foundation: &ArchSigPart4DistanceFoundationV0,
    signature_distance_readings: &[ArchSigSignatureDistanceReadingV0],
    operation_distance_readings: &[ArchSigOperationDistanceReadingV0],
    curvature_mass_readings: &[ArchSigCurvatureMassReadingV0],
    homotopy_distance_readings: &[ArchSigHomotopyDistanceReadingV0],
    representation_metric_readings: &[ArchSigRepresentationMetricReadingV0],
) -> Vec<String> {
    let mut summary = vec![
        format!(
            "distanceProfile={} measured={} blocked={} unmeasured={} schemaFoundationOnly={}",
            foundation.profile.profile_id,
            foundation.status_summary.measured_count,
            foundation.status_summary.blocked_count,
            foundation.status_summary.unmeasured_count,
            foundation.status_summary.schema_foundation_only_count
        ),
        format!(
            "diagnosticScope measuredAxes={} unmeasuredAxes={} blockers={} boundary=evaluator-synchronized",
            foundation.diagnostic_scope.measured_axis_refs.len(),
            foundation.diagnostic_scope.unmeasured_axis_refs.len(),
            foundation.diagnostic_scope.blocker_refs.len()
        ),
        "diagnostic distance is Part IV evaluator output; viewer layout distance is visual placement only"
            .to_string(),
        "blocked or unmeasured distance is not measured zero; safe margin remains coverage-qualified"
            .to_string(),
    ];
    if let Some(reading) = signature_distance_readings.first() {
        summary.push(format!(
            "{} total={} endpoint={} pathDrift={} safe={} hiddenExcursion={}",
            reading.signature_distance_reading_id,
            distance_value_summary(&reading.total_measured_distance),
            distance_value_summary(&reading.endpoint_distance),
            distance_value_summary(&reading.path_drift),
            distance_value_summary(&reading.safe_region_margin),
            reading.hidden_excursion_status
        ));
    }
    if let Some(reading) = operation_distance_readings.first() {
        summary.push(format!(
            "{} operationCost={} targetDecrease={} sideEffectBound={}",
            reading.operation_distance_reading_id,
            distance_value_summary(&reading.operation_cost),
            distance_value_summary(&reading.target_distance_decrease),
            distance_value_summary(&reading.side_effect_bound)
        ));
    }
    if let Some(reading) = curvature_mass_readings.first() {
        summary.push(format!(
            "{} curvatureMass={} transport={} targetDecrease={} protectedMovement={}",
            reading.curvature_mass_reading_id,
            distance_value_summary(&reading.curvature_mass),
            distance_value_summary(&reading.transport_distance),
            distance_value_summary(&reading.target_axis_decrease),
            distance_value_summary(&reading.protected_axis_movement)
        ));
    }
    if let Some(reading) = homotopy_distance_readings.first() {
        summary.push(format!(
            "{} homotopy={} fillingCost={} observationGapLowerBound={} selectedDehnArea={}",
            reading.homotopy_distance_reading_id,
            distance_value_summary(&reading.homotopy_distance),
            distance_value_summary(&reading.filling_cost),
            distance_value_summary(&reading.observation_gap_lower_bound),
            distance_value_summary(&reading.selected_dehn_area)
        ));
    }
    let blocked_representation_count = representation_metric_readings
        .iter()
        .filter(|reading| reading.bi_lipschitz_faithfulness.status != "measured")
        .count();
    summary.push(format!(
        "representationMetrics={} blockedFaithfulness={} boundary=selected analytic stability is not global structural faithfulness",
        representation_metric_readings.len(),
        blocked_representation_count
    ));
    summary
}

fn distance_value_summary(value: &ArchSigDistanceValueV0) -> String {
    match value.measured_value {
        Some(measured_value) => format!("{}:{}{}", value.status, measured_value, value.unit),
        None => format!("{}:{}", value.status, value.unit),
    }
}
