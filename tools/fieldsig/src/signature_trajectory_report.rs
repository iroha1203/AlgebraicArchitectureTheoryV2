use std::collections::BTreeSet;

use serde_json::json;

use crate::validation::{count_checks, generic_validation_example, validation_check};
use crate::{
    DynamicsAggregationWindowV0, DynamicsArtifactRefV0, DynamicsMeasuredValueV0,
    DynamicsMissingEvidenceV0, EXTRACTOR_VERSION, MeasurementBoundaryV0,
    PR_FORCE_REPORT_SCHEMA_VERSION, RepositoryRef, RepositoryRevisionRef,
    SIGNATURE_SNAPSHOT_STORE_SCHEMA_VERSION, SIGNATURE_TRAJECTORY_REPORT_SCHEMA_VERSION,
    SIGNATURE_TRAJECTORY_REPORT_VALIDATION_REPORT_SCHEMA_VERSION, SelectedSignatureRegionV0,
    SignatureTrajectoryPointV0, SignatureTrajectoryReportV0,
    SignatureTrajectoryReportValidationInput, SignatureTrajectoryReportValidationReportV0,
    SignatureTrajectoryReportValidationSummary, ValidationCheck, ValidationExample,
};

const ALLOWED_STATUSES: [&str; 9] = [
    "measured",
    "estimated",
    "derived",
    "advisory",
    "unmeasured",
    "unavailable",
    "private",
    "notComparable",
    "outOfScope",
];

const VALUE_REQUIRED_STATUSES: [&str; 2] = ["measured", "derived"];
const EVIDENCE_REQUIRED_STATUSES: [&str; 4] = ["measured", "estimated", "derived", "advisory"];

const REQUIRED_REGION_KINDS: [&str; 4] =
    ["safeRegion", "badRegion", "debtWell", "attractorCandidate"];

const REQUIRED_NON_CONCLUSIONS: [&str; 4] = [
    "signature trajectory report is tooling validation, not a Lean theorem claim",
    "finite observed trajectory does not prove a global attractor or basin theorem",
    "selected window evidence does not conclude behavior outside the bounded operation window",
    "endpoint safe region membership does not imply path safety",
];

pub fn static_signature_trajectory_report() -> SignatureTrajectoryReportV0 {
    let before_ref = artifact_ref(
        "signature-snapshot-store",
        "tools/archsig/tests/fixtures/minimal/signature_snapshot_before.json",
        Some(SIGNATURE_SNAPSHOT_STORE_SCHEMA_VERSION),
        Some("fixture-trajectory-before-signature"),
    );
    let middle_ref = artifact_ref(
        "signature-snapshot-store",
        "tools/archsig/tests/fixtures/minimal/signature_snapshot_middle.json",
        Some(SIGNATURE_SNAPSHOT_STORE_SCHEMA_VERSION),
        Some("fixture-trajectory-middle-signature"),
    );
    let after_ref = artifact_ref(
        "signature-snapshot-store",
        "tools/archsig/tests/fixtures/minimal/signature_snapshot_after.json",
        Some(SIGNATURE_SNAPSHOT_STORE_SCHEMA_VERSION),
        Some("fixture-trajectory-after-signature"),
    );
    let force_ref = artifact_ref(
        "pr-force-report",
        "tools/archsig/tests/fixtures/minimal/pr_force_report.json",
        Some(PR_FORCE_REPORT_SCHEMA_VERSION),
        Some("fixture-pr-force-report-v0"),
    );
    let drift_ref = artifact_ref(
        "architecture-drift-ledger",
        "tools/archsig/tests/fixtures/minimal/architecture_drift_ledger.json",
        Some("architecture-drift-ledger-v0"),
        Some("fixture-architecture-drift-ledger"),
    );

    let window = DynamicsAggregationWindowV0 {
        window_start: Some("2026-01-01T00:00:00Z".to_string()),
        window_end: Some("2026-01-31T23:59:59Z".to_string()),
        window_kind: "selected-trajectory-window".to_string(),
    };

    SignatureTrajectoryReportV0 {
        schema_version: SIGNATURE_TRAJECTORY_REPORT_SCHEMA_VERSION.to_string(),
        report_id: "fixture-signature-trajectory-report-v0".to_string(),
        repository: RepositoryRef {
            owner: "iroha1203".to_string(),
            name: "AlgebraicArchitectureTheoryV2".to_string(),
            default_branch: "main".to_string(),
        },
        window: window.clone(),
        trajectory_points: vec![
            trajectory_point(
                "fixture-trajectory-point-0",
                0,
                "2026-01-01T00:00:00Z",
                "fixture-before-sha",
                before_ref.clone(),
                vec!["fixture-safe-region"],
                None,
                vec![
                    metric(
                        "signature.boundaryViolationCount",
                        Some(json!(3)),
                        "measured",
                        None,
                        vec![before_ref.clone()],
                        boundary(
                            "signature",
                            &["boundaryViolationCount"],
                            vec![before_ref.clone()],
                            Some(window.clone()),
                            &["selected Signature snapshot is retained for the trajectory point"],
                            &["path safety outside the selected window"],
                        ),
                        &["axis value is read from the retained Signature snapshot"],
                        &["point axis value is not a single architecture quality score"],
                    ),
                    metric(
                        "signature.runtimePropagationRisk",
                        None,
                        "unmeasured",
                        None,
                        Vec::new(),
                        gap_boundary(
                            "runtime propagation extractor was not run for the trajectory point",
                            "unmeasured",
                        ),
                        &["runtime evidence is not available for this fixture point"],
                        &["unmeasured runtime point value is not zero"],
                    ),
                ],
            ),
            trajectory_point(
                "fixture-trajectory-point-1",
                1,
                "2026-01-15T12:00:00Z",
                "fixture-middle-sha",
                middle_ref.clone(),
                vec!["fixture-bad-region", "fixture-debt-well"],
                Some(force_ref.clone()),
                vec![metric(
                    "signature.boundaryViolationCount",
                    Some(json!(5)),
                    "measured",
                    None,
                    vec![middle_ref.clone(), force_ref.clone()],
                    boundary(
                        "signature",
                        &["boundaryViolationCount"],
                        vec![middle_ref.clone(), force_ref.clone()],
                        Some(window.clone()),
                        &[
                            "trajectory point records an internal excursion before the selected endpoint",
                        ],
                        &["endpoint-only safety conclusion"],
                    ),
                    &["internal trajectory point is retained"],
                    &["transient excursion is not erased by endpoint compression"],
                )],
            ),
            trajectory_point(
                "fixture-trajectory-point-2",
                2,
                "2026-01-31T23:59:59Z",
                "fixture-after-sha",
                after_ref.clone(),
                vec!["fixture-safe-region", "fixture-attractor-candidate"],
                Some(force_ref.clone()),
                vec![metric(
                    "signature.boundaryViolationCount",
                    Some(json!(1)),
                    "measured",
                    None,
                    vec![after_ref.clone(), force_ref.clone()],
                    boundary(
                        "signature",
                        &["boundaryViolationCount"],
                        vec![after_ref.clone(), force_ref.clone()],
                        Some(window.clone()),
                        &["selected endpoint Signature snapshot is retained"],
                        &["global attractor inference"],
                    ),
                    &["endpoint is inside the selected fixture safe region"],
                    &["endpoint safe region membership does not imply path safety"],
                )],
            ),
        ],
        force_refs: vec![force_ref.clone()],
        drift_signals: vec![
            metric(
                "trajectory.driftRate.boundaryViolationCount",
                Some(json!(-2)),
                "derived",
                None,
                vec![before_ref.clone(), after_ref.clone()],
                boundary(
                    "signature-trajectory",
                    &["TrajectoryDriftRate"],
                    vec![before_ref.clone(), after_ref.clone()],
                    Some(window.clone()),
                    &["drift rate is derived from comparable selected endpoint snapshots"],
                    &["path safety claim"],
                ),
                &["negative drift over endpoints does not erase internal excursion"],
                &["derived drift is a bounded-window signal, not a theorem claim"],
            ),
            metric(
                "trajectory.drift.schemaCompatibilityBoundary",
                None,
                "notComparable",
                None,
                vec![drift_ref.clone()],
                gap_boundary(
                    "schema or policy changes across a trajectory require migration boundary before comparison",
                    "notComparable",
                ),
                &["cross-version trajectory comparison is not performed in this fixture"],
                &["notComparable trajectory drift is not zero drift"],
            ),
        ],
        stability_signals: vec![metric(
            "trajectory.stability.selectedRegionRetention",
            Some(
                json!({"startRegion": "safeRegion", "endRegion": "safeRegion", "internalExcursion": true}),
            ),
            "derived",
            None,
            vec![before_ref.clone(), middle_ref.clone(), after_ref.clone()],
            boundary(
                "signature-trajectory",
                &["TrajectoryStability"],
                vec![before_ref.clone(), middle_ref.clone(), after_ref.clone()],
                Some(window.clone()),
                &["stability signal is scoped to the retained finite observed trajectory"],
                &["global convergence proof"],
            ),
            &["internal excursion is preserved instead of endpoint-compressed away"],
            &["selected region retention is not a global basin claim"],
        )],
        excursion_signals: vec![metric(
            "trajectory.excursion.selectedBadRegionVisit",
            Some(json!({"visited": true, "maxBoundaryViolationCount": 5})),
            "measured",
            None,
            vec![middle_ref.clone()],
            boundary(
                "signature-trajectory",
                &["TransientExcursionDebt"],
                vec![middle_ref.clone()],
                Some(window.clone()),
                &["bad-region visit is observed at a retained trajectory point"],
                &["selected window outside behavior"],
            ),
            &["middle trajectory point is retained"],
            &["endpoint compression must not erase selected bad-region visits"],
        )],
        endpoint_compression_signals: vec![metric(
            "trajectory.endpointCompression.pathCompressionLoss",
            Some(json!({"endpointDelta": -2, "internalMaximum": 5})),
            "derived",
            None,
            vec![before_ref.clone(), middle_ref.clone(), after_ref.clone()],
            boundary(
                "signature-trajectory",
                &["PathCompressionLoss"],
                vec![before_ref.clone(), middle_ref.clone(), after_ref.clone()],
                Some(window.clone()),
                &["endpoint delta and internal maximum are both retained"],
                &["endpoint-only architecture safety proof"],
            ),
            &["path compression loss is bounded to the selected fixture trajectory"],
            &["endpoint-improving delta does not imply path safe"],
        )],
        selected_regions: vec![
            selected_region(
                "fixture-safe-region",
                "safeRegion",
                &["boundaryViolationCount"],
                json!({"boundaryViolationCount": {"maxInclusive": 3}}),
                vec!["fixture-trajectory-point-0", "fixture-trajectory-point-2"],
                Some(window.clone()),
                &["safe region is selected by fixture policy for bounded-window analysis"],
                &["safe region membership is not a global safety theorem"],
            ),
            selected_region(
                "fixture-bad-region",
                "badRegion",
                &["boundaryViolationCount"],
                json!({"boundaryViolationCount": {"minExclusive": 3}}),
                vec!["fixture-trajectory-point-1"],
                Some(window.clone()),
                &["bad region is selected by fixture policy for excursion tracking"],
                &["bad region visit is not an incident causality proof"],
            ),
            selected_region(
                "fixture-debt-well",
                "debtWell",
                &["boundaryViolationCount"],
                json!({"boundaryViolationCount": {"minInclusive": 5}}),
                vec!["fixture-trajectory-point-1"],
                Some(window.clone()),
                &["debt well is a selected finite-region marker"],
                &["debt well label is not a proof of repair impossibility"],
            ),
            selected_region(
                "fixture-attractor-candidate",
                "attractorCandidate",
                &["boundaryViolationCount"],
                json!({"boundaryViolationCount": {"maxInclusive": 1}}),
                vec!["fixture-trajectory-point-2"],
                Some(window.clone()),
                &[
                    "attractor candidate is relative to finite observed trajectory and bounded operation window",
                ],
                &["attractor candidate is not a global attractor theorem"],
            ),
        ],
        measurement_boundary: MeasurementBoundaryV0 {
            measured_layer: "signature-trajectory".to_string(),
            measured_axes: vec![
                "trajectoryPoints".to_string(),
                "forceRefs".to_string(),
                "driftSignals".to_string(),
                "stabilitySignals".to_string(),
                "excursionSignals".to_string(),
                "endpointCompressionSignals".to_string(),
                "selectedRegions".to_string(),
            ],
            source_artifact_refs: vec![before_ref, middle_ref, after_ref, force_ref, drift_ref],
            extractor_version: Some(EXTRACTOR_VERSION.to_string()),
            policy_version: Some("fixture-policy-v0".to_string()),
            schema_version: Some(SIGNATURE_TRAJECTORY_REPORT_SCHEMA_VERSION.to_string()),
            aggregation_window: Some(window),
            selected_region_refs: vec![
                "fixture-safe-region".to_string(),
                "fixture-bad-region".to_string(),
                "fixture-debt-well".to_string(),
                "fixture-attractor-candidate".to_string(),
            ],
            assumptions: vec![
                "fixture records a finite observed Signature trajectory over one selected window"
                    .to_string(),
                "selected regions are policy-relative analysis regions".to_string(),
            ],
            unsupported_constructs: vec![
                "global attractor inference".to_string(),
                "global basin theorem".to_string(),
                "behavior outside the selected bounded operation window".to_string(),
            ],
            missing_evidence: vec![missing_evidence(
                "migration-boundary",
                "cross-version trajectory comparison requires explicit notComparable or migration boundary",
                "notComparable",
            )],
            non_conclusions: strings(&REQUIRED_NON_CONCLUSIONS),
        },
        non_conclusions: strings(&REQUIRED_NON_CONCLUSIONS),
    }
}

pub fn validate_signature_trajectory_report(
    report: &SignatureTrajectoryReportV0,
    input_path: &str,
) -> SignatureTrajectoryReportValidationReportV0 {
    let checks = vec![
        check_schema_version(report),
        check_report_identity(report),
        check_measurement_statuses(report),
        check_null_value_statuses(report),
        check_measurement_boundaries(report),
        check_selected_regions(report),
        check_comparison_boundary(report),
    ];
    let summary = SignatureTrajectoryReportValidationSummary {
        result: if checks.iter().any(|check| check.result == "fail") {
            "fail".to_string()
        } else if checks.iter().any(|check| check.result == "warn") {
            "warn".to_string()
        } else {
            "pass".to_string()
        },
        trajectory_point_count: report.trajectory_points.len(),
        force_ref_count: report.force_refs.len(),
        drift_signal_count: report.drift_signals.len(),
        stability_signal_count: report.stability_signals.len(),
        excursion_signal_count: report.excursion_signals.len(),
        endpoint_compression_signal_count: report.endpoint_compression_signals.len(),
        selected_region_count: report.selected_regions.len(),
        failed_check_count: count_checks(&checks, "fail"),
        warning_check_count: count_checks(&checks, "warn"),
    };

    SignatureTrajectoryReportValidationReportV0 {
        schema_version: SIGNATURE_TRAJECTORY_REPORT_VALIDATION_REPORT_SCHEMA_VERSION.to_string(),
        input: SignatureTrajectoryReportValidationInput {
            schema_version: report.schema_version.clone(),
            path: input_path.to_string(),
            report_id: report.report_id.clone(),
            repository: format!("{}/{}", report.repository.owner, report.repository.name),
            window_kind: report.window.window_kind.clone(),
        },
        report: report.clone(),
        summary,
        checks,
    }
}

fn trajectory_point(
    point_id: &str,
    sequence_index: usize,
    observed_at: &str,
    sha: &str,
    signature_snapshot_ref: DynamicsArtifactRefV0,
    region_refs: Vec<&str>,
    force_ref: Option<DynamicsArtifactRefV0>,
    axis_values: Vec<DynamicsMeasuredValueV0>,
) -> SignatureTrajectoryPointV0 {
    let source_refs = if let Some(force_ref) = &force_ref {
        vec![signature_snapshot_ref.clone(), force_ref.clone()]
    } else {
        vec![signature_snapshot_ref.clone()]
    };
    SignatureTrajectoryPointV0 {
        point_id: point_id.to_string(),
        sequence_index,
        observed_at: Some(observed_at.to_string()),
        revision: RepositoryRevisionRef {
            sha: sha.to_string(),
            ref_name: Some("refs/heads/main".to_string()),
            branch: Some("main".to_string()),
            committed_at: Some(observed_at.to_string()),
            parent_shas: Vec::new(),
        },
        signature_snapshot_ref,
        axis_values,
        region_refs: strings(&region_refs),
        force_ref,
        measurement_boundary: boundary(
            "signature-trajectory",
            &["trajectoryPoints"],
            source_refs,
            None,
            &["trajectory point is part of a finite selected observed path"],
            &["global trajectory completion"],
        ),
        non_conclusions: strings(&[
            "trajectory point is not a complete state-space observation",
            "point membership does not imply behavior outside the selected window",
        ]),
    }
}

fn selected_region(
    region_id: &str,
    region_kind: &str,
    defining_axes: &[&str],
    bounds: serde_json::Value,
    trajectory_point_refs: Vec<&str>,
    aggregation_window: Option<DynamicsAggregationWindowV0>,
    assumptions: &[&str],
    non_conclusions: &[&str],
) -> SelectedSignatureRegionV0 {
    SelectedSignatureRegionV0 {
        region_id: region_id.to_string(),
        region_kind: region_kind.to_string(),
        defining_axes: strings(defining_axes),
        bounds,
        trajectory_point_refs: strings(&trajectory_point_refs),
        measurement_boundary: boundary(
            "signature-trajectory-region",
            defining_axes,
            Vec::new(),
            aggregation_window,
            assumptions,
            &["global attractor inference"],
        ),
        non_conclusions: strings(non_conclusions),
    }
}

fn metric(
    metric_id: &str,
    value: Option<serde_json::Value>,
    status: &str,
    confidence: Option<&str>,
    source_refs: Vec<DynamicsArtifactRefV0>,
    measurement_boundary: MeasurementBoundaryV0,
    assumptions: &[&str],
    non_conclusions: &[&str],
) -> DynamicsMeasuredValueV0 {
    DynamicsMeasuredValueV0 {
        metric_id: metric_id.to_string(),
        value,
        status: status.to_string(),
        confidence: confidence.map(str::to_string),
        source_refs,
        measurement_boundary,
        assumptions: strings(assumptions),
        non_conclusions: strings(non_conclusions),
    }
}

fn boundary(
    measured_layer: &str,
    measured_axes: &[&str],
    source_artifact_refs: Vec<DynamicsArtifactRefV0>,
    aggregation_window: Option<DynamicsAggregationWindowV0>,
    assumptions: &[&str],
    unsupported_constructs: &[&str],
) -> MeasurementBoundaryV0 {
    MeasurementBoundaryV0 {
        measured_layer: measured_layer.to_string(),
        measured_axes: strings(measured_axes),
        source_artifact_refs,
        extractor_version: Some(EXTRACTOR_VERSION.to_string()),
        policy_version: Some("fixture-policy-v0".to_string()),
        schema_version: Some(SIGNATURE_TRAJECTORY_REPORT_SCHEMA_VERSION.to_string()),
        aggregation_window,
        selected_region_refs: vec!["fixture:selected-trajectory-window".to_string()],
        assumptions: strings(assumptions),
        unsupported_constructs: strings(unsupported_constructs),
        missing_evidence: Vec::new(),
        non_conclusions: strings(&REQUIRED_NON_CONCLUSIONS),
    }
}

fn gap_boundary(reason: &str, status: &str) -> MeasurementBoundaryV0 {
    MeasurementBoundaryV0 {
        measured_layer: "signature-trajectory".to_string(),
        measured_axes: Vec::new(),
        source_artifact_refs: Vec::new(),
        extractor_version: Some(EXTRACTOR_VERSION.to_string()),
        policy_version: None,
        schema_version: Some(SIGNATURE_TRAJECTORY_REPORT_SCHEMA_VERSION.to_string()),
        aggregation_window: None,
        selected_region_refs: Vec::new(),
        assumptions: vec![reason.to_string()],
        unsupported_constructs: Vec::new(),
        missing_evidence: vec![missing_evidence(
            "signature-trajectory-evidence",
            reason,
            status,
        )],
        non_conclusions: vec![format!(
            "{status} trajectory signal is not measured-zero evidence"
        )],
    }
}

fn artifact_ref(
    kind: &str,
    path: &str,
    schema_version: Option<&str>,
    artifact_id: Option<&str>,
) -> DynamicsArtifactRefV0 {
    DynamicsArtifactRefV0 {
        kind: kind.to_string(),
        path: path.to_string(),
        schema_version: schema_version.map(str::to_string),
        artifact_id: artifact_id.map(str::to_string),
    }
}

fn missing_evidence(
    evidence_kind: &str,
    reason: &str,
    boundary: &str,
) -> DynamicsMissingEvidenceV0 {
    DynamicsMissingEvidenceV0 {
        evidence_kind: evidence_kind.to_string(),
        reason: reason.to_string(),
        boundary: boundary.to_string(),
    }
}

fn check_schema_version(report: &SignatureTrajectoryReportV0) -> ValidationCheck {
    let mut check = validation_check(
        "signature-trajectory-report-schema-version-supported",
        "signature-trajectory-report schema version is supported",
        if report.schema_version == SIGNATURE_TRAJECTORY_REPORT_SCHEMA_VERSION {
            "pass"
        } else {
            "fail"
        },
    );
    if check.result == "fail" {
        check.reason = Some(format!(
            "unsupported signature-trajectory-report schemaVersion: {}",
            report.schema_version
        ));
    }
    check
}

fn check_report_identity(report: &SignatureTrajectoryReportV0) -> ValidationCheck {
    let mut invalid = Vec::new();
    if report.report_id.trim().is_empty() {
        invalid.push(generic_validation_example(
            "reportId",
            &report.schema_version,
            "reportId must be non-empty",
        ));
    }
    if report.repository.owner.trim().is_empty() || report.repository.name.trim().is_empty() {
        invalid.push(generic_validation_example(
            &report.report_id,
            "repository",
            "repository owner and name must be non-empty",
        ));
    }
    if report.window.window_kind.trim().is_empty() {
        invalid.push(generic_validation_example(
            &report.report_id,
            "window.windowKind",
            "aggregation window kind must be non-empty",
        ));
    }
    if report.trajectory_points.is_empty()
        || report.drift_signals.is_empty()
        || report.stability_signals.is_empty()
        || report.excursion_signals.is_empty()
        || report.endpoint_compression_signals.is_empty()
        || report.selected_regions.is_empty()
    {
        invalid.push(generic_validation_example(
            &report.report_id,
            "trajectory groups",
            "trajectory points, signal groups, and selected regions must be present",
        ));
    }
    if !is_strictly_ordered(report) {
        invalid.push(generic_validation_example(
            &report.report_id,
            "trajectoryPoints[].sequenceIndex",
            "trajectory point sequenceIndex values must be strictly increasing",
        ));
    }
    for required in REQUIRED_NON_CONCLUSIONS {
        if !report
            .non_conclusions
            .iter()
            .any(|conclusion| conclusion == required)
        {
            invalid.push(generic_validation_example(
                &report.report_id,
                "nonConclusions",
                &format!("missing required non-conclusion: {required}"),
            ));
        }
    }
    check_examples(
        "signature-trajectory-report-identity-recorded",
        "report identity, finite trajectory groups, ordering, and non-conclusions are recorded",
        invalid,
    )
}

fn check_measurement_statuses(report: &SignatureTrajectoryReportV0) -> ValidationCheck {
    let allowed = string_set(ALLOWED_STATUSES);
    let mut invalid = Vec::new();
    for metric in report_metrics(report) {
        if !allowed.contains(metric.status.as_str()) {
            invalid.push(generic_validation_example(
                &metric.metric_id,
                &metric.status,
                "unsupported MeasurementStatus",
            ));
        }
    }
    check_examples(
        "signature-trajectory-status-values-supported",
        "Signature trajectory report uses only the common dynamics MeasurementStatus vocabulary",
        invalid,
    )
}

fn check_null_value_statuses(report: &SignatureTrajectoryReportV0) -> ValidationCheck {
    let value_required = string_set(VALUE_REQUIRED_STATUSES);
    let mut invalid = Vec::new();
    for metric in report_metrics(report) {
        if value_required.contains(metric.status.as_str()) && metric.value.is_none() {
            invalid.push(generic_validation_example(
                &metric.metric_id,
                &metric.status,
                "value = null cannot be emitted as measured or derived",
            ));
        }
    }
    check_examples(
        "signature-trajectory-null-value-not-measured-or-derived",
        "null trajectory values are not promoted to measured or derived values",
        invalid,
    )
}

fn check_measurement_boundaries(report: &SignatureTrajectoryReportV0) -> ValidationCheck {
    let evidence_required = string_set(EVIDENCE_REQUIRED_STATUSES);
    let mut invalid = Vec::new();
    validate_boundary(
        &report.report_id,
        "report.measurementBoundary",
        &report.measurement_boundary,
        true,
        &mut invalid,
    );
    for point in &report.trajectory_points {
        if point.point_id.trim().is_empty()
            || point.signature_snapshot_ref.kind.trim().is_empty()
            || point.signature_snapshot_ref.path.trim().is_empty()
        {
            invalid.push(generic_validation_example(
                &point.point_id,
                "trajectoryPoints",
                "trajectory point identity and signature snapshot ref must be explicit",
            ));
        }
        validate_boundary(
            &point.point_id,
            "trajectoryPoints[].measurementBoundary",
            &point.measurement_boundary,
            true,
            &mut invalid,
        );
        if point.non_conclusions.is_empty() || has_blank(&point.non_conclusions) {
            invalid.push(generic_validation_example(
                &point.point_id,
                "nonConclusions",
                "trajectory point non-conclusions must be explicit",
            ));
        }
    }
    for metric in report_metrics(report) {
        validate_boundary(
            &metric.metric_id,
            "measurementBoundary",
            &metric.measurement_boundary,
            evidence_required.contains(metric.status.as_str()),
            &mut invalid,
        );
        if metric.assumptions.is_empty() || has_blank(&metric.assumptions) {
            invalid.push(generic_validation_example(
                &metric.metric_id,
                "assumptions",
                "metric assumptions must be explicit",
            ));
        }
        if metric.non_conclusions.is_empty() || has_blank(&metric.non_conclusions) {
            invalid.push(generic_validation_example(
                &metric.metric_id,
                "nonConclusions",
                "metric non-conclusions must be explicit",
            ));
        }
    }
    check_examples(
        "signature-trajectory-boundaries-recorded",
        "trajectory points and signals preserve measurement boundary, evidence refs, assumptions, and non-conclusions",
        invalid,
    )
}

fn check_selected_regions(report: &SignatureTrajectoryReportV0) -> ValidationCheck {
    let required = string_set(REQUIRED_REGION_KINDS);
    let mut seen = BTreeSet::new();
    let point_ids: BTreeSet<&str> = report
        .trajectory_points
        .iter()
        .map(|point| point.point_id.as_str())
        .collect();
    let mut invalid = Vec::new();

    for region in &report.selected_regions {
        if !required.contains(region.region_kind.as_str()) {
            invalid.push(generic_validation_example(
                &region.region_id,
                &region.region_kind,
                "selected region kind must be safeRegion, badRegion, debtWell, or attractorCandidate",
            ));
        } else {
            seen.insert(region.region_kind.as_str());
        }
        if region.region_id.trim().is_empty()
            || region.defining_axes.is_empty()
            || has_blank(&region.defining_axes)
            || region.trajectory_point_refs.is_empty()
            || has_blank(&region.trajectory_point_refs)
        {
            invalid.push(generic_validation_example(
                &region.region_id,
                "selectedRegions",
                "selected region id, defining axes, and trajectory point refs must be explicit",
            ));
        }
        for point_ref in &region.trajectory_point_refs {
            if !point_ids.contains(point_ref.as_str()) {
                invalid.push(generic_validation_example(
                    &region.region_id,
                    point_ref,
                    "selected region must reference retained trajectory points",
                ));
            }
        }
        validate_boundary(
            &region.region_id,
            "selectedRegions[].measurementBoundary",
            &region.measurement_boundary,
            false,
            &mut invalid,
        );
        if region.region_kind == "attractorCandidate"
            && !region.non_conclusions.iter().any(|conclusion| {
                conclusion.contains("not a global attractor")
                    || conclusion.contains("global attractor theorem")
            })
        {
            invalid.push(generic_validation_example(
                &region.region_id,
                "nonConclusions",
                "attractor candidate must explicitly reject global attractor theorem claims",
            ));
        }
    }

    for kind in REQUIRED_REGION_KINDS {
        if !seen.contains(kind) {
            invalid.push(generic_validation_example(
                &report.report_id,
                kind,
                "selectedRegions must include safe region, bad region, debt well, and attractor candidate slots",
            ));
        }
    }

    check_examples(
        "signature-trajectory-selected-regions-recorded",
        "safe region, bad region, debt well, and attractor candidate are finite selected regions",
        invalid,
    )
}

fn check_comparison_boundary(report: &SignatureTrajectoryReportV0) -> ValidationCheck {
    let mut schema_versions = BTreeSet::new();
    let mut extractor_versions = BTreeSet::new();
    let mut policy_versions = BTreeSet::new();
    for point in &report.trajectory_points {
        if let Some(schema_version) = &point.measurement_boundary.schema_version {
            schema_versions.insert(schema_version.as_str());
        }
        if let Some(extractor_version) = &point.measurement_boundary.extractor_version {
            extractor_versions.insert(extractor_version.as_str());
        }
        if let Some(policy_version) = &point.measurement_boundary.policy_version {
            policy_versions.insert(policy_version.as_str());
        }
    }

    let has_version_gap =
        schema_versions.len() > 1 || extractor_versions.len() > 1 || policy_versions.len() > 1;
    let has_not_comparable_signal = report_metrics(report)
        .iter()
        .any(|metric| metric.status == "notComparable");
    let has_migration_boundary = report
        .measurement_boundary
        .missing_evidence
        .iter()
        .any(|evidence| evidence.boundary == "notComparable")
        || report
            .measurement_boundary
            .unsupported_constructs
            .iter()
            .any(|unsupported| unsupported.contains("migration boundary"));

    let mut invalid = Vec::new();
    if has_version_gap && !has_not_comparable_signal && !has_migration_boundary {
        invalid.push(generic_validation_example(
            &report.report_id,
            "trajectoryPoints[].measurementBoundary",
            "extractor, policy, or schema version differences require notComparable or migration boundary evidence",
        ));
    }
    check_examples(
        "signature-trajectory-comparison-boundary-recorded",
        "version-different trajectory evidence records notComparable or migration boundary",
        invalid,
    )
}

fn validate_boundary(
    owner: &str,
    field: &str,
    boundary: &MeasurementBoundaryV0,
    source_refs_required: bool,
    invalid: &mut Vec<ValidationExample>,
) {
    if boundary.measured_layer.trim().is_empty() {
        invalid.push(generic_validation_example(
            owner,
            field,
            "measuredLayer must be non-empty",
        ));
    }
    if source_refs_required
        && (boundary.measured_axes.is_empty() || has_blank(&boundary.measured_axes))
    {
        invalid.push(generic_validation_example(
            owner,
            "measuredAxes",
            "measuredAxes must be explicit for measured, estimated, derived, and advisory values",
        ));
    }
    if source_refs_required
        && (boundary.source_artifact_refs.is_empty()
            || has_blank_artifact_refs(&boundary.source_artifact_refs))
    {
        invalid.push(generic_validation_example(
            owner,
            "sourceArtifactRefs",
            "sourceArtifactRefs must be explicit for measured, estimated, derived, and advisory values",
        ));
    }
    if boundary.assumptions.is_empty() || has_blank(&boundary.assumptions) {
        invalid.push(generic_validation_example(
            owner,
            "assumptions",
            "measurement boundary assumptions must be explicit",
        ));
    }
    if boundary.non_conclusions.is_empty() || has_blank(&boundary.non_conclusions) {
        invalid.push(generic_validation_example(
            owner,
            "nonConclusions",
            "measurement boundary non-conclusions must be explicit",
        ));
    }
    for evidence in &boundary.missing_evidence {
        if evidence.evidence_kind.trim().is_empty()
            || evidence.reason.trim().is_empty()
            || evidence.boundary.trim().is_empty()
        {
            invalid.push(generic_validation_example(
                owner,
                "missingEvidence",
                "missing evidence entries must record evidenceKind, reason, and boundary",
            ));
        }
    }
}

fn report_metrics(report: &SignatureTrajectoryReportV0) -> Vec<&DynamicsMeasuredValueV0> {
    report
        .trajectory_points
        .iter()
        .flat_map(|point| point.axis_values.iter())
        .chain(report.drift_signals.iter())
        .chain(report.stability_signals.iter())
        .chain(report.excursion_signals.iter())
        .chain(report.endpoint_compression_signals.iter())
        .collect()
}

fn is_strictly_ordered(report: &SignatureTrajectoryReportV0) -> bool {
    report
        .trajectory_points
        .windows(2)
        .all(|window| window[0].sequence_index < window[1].sequence_index)
}

fn check_examples(id: &str, title: &str, invalid: Vec<ValidationExample>) -> ValidationCheck {
    let mut check = validation_check(id, title, if invalid.is_empty() { "pass" } else { "fail" });
    if !invalid.is_empty() {
        check.count = Some(invalid.len());
        check.examples = invalid;
    }
    check
}

fn strings(values: &[&str]) -> Vec<String> {
    values.iter().map(|value| (*value).to_string()).collect()
}

fn has_blank(values: &[String]) -> bool {
    values.iter().any(|value| value.trim().is_empty())
}

fn has_blank_artifact_refs(refs: &[DynamicsArtifactRefV0]) -> bool {
    refs.iter().any(|artifact_ref| {
        artifact_ref.kind.trim().is_empty() || artifact_ref.path.trim().is_empty()
    })
}

fn string_set<const N: usize>(values: [&'static str; N]) -> BTreeSet<&'static str> {
    values.into_iter().collect()
}
