use std::collections::BTreeSet;

use serde_json::json;

use crate::validation::{count_checks, generic_validation_example, validation_check};
use crate::{
    ARCHITECTURE_DYNAMICS_METRICS_REPORT_SCHEMA_VERSION,
    ARCHITECTURE_DYNAMICS_METRICS_REPORT_VALIDATION_REPORT_SCHEMA_VERSION,
    ArchitectureDynamicsMetricsReportV0, ArchitectureDynamicsMetricsReportValidationInput,
    ArchitectureDynamicsMetricsReportValidationReportV0,
    ArchitectureDynamicsMetricsReportValidationSummary, DynamicsAggregationWindowV0,
    DynamicsArtifactRefV0, DynamicsMeasuredValueV0, DynamicsMissingEvidenceV0, EXTRACTOR_VERSION,
    MeasurementBoundaryV0, PR_FORCE_REPORT_SCHEMA_VERSION, RepositoryRef, ValidationCheck,
    ValidationExample,
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

const REQUIRED_NON_CONCLUSIONS: [&str; 4] = [
    "architecture dynamics metrics report is tooling validation, not a Lean theorem claim",
    "unmeasured, unavailable, notComparable, and outOfScope metrics are not measured zero",
    "Architecture Signature Dynamics is a multi-axis diagnostic, not a single score",
    "global attractor, causal proof, and incident-risk conclusions are out of scope",
];

const FORCE_CLASS_NON_CONCLUSION: &str =
    "ObservedForce, LatentForceEstimate, and DissipatedForceEstimate remain separate force classes";

pub fn static_architecture_dynamics_metrics_report() -> ArchitectureDynamicsMetricsReportV0 {
    let pr_force_ref = artifact_ref(
        "pr-force-report",
        "tools/archsig/tests/fixtures/minimal/pr_force_report.json",
        Some(PR_FORCE_REPORT_SCHEMA_VERSION),
        Some("fixture-pr-force-report-v0"),
    );
    let trajectory_ref = artifact_ref(
        "signature-trajectory-report",
        "tools/archsig/tests/fixtures/minimal/signature_trajectory_report.json",
        Some("signature-trajectory-report-v0"),
        Some("fixture-signature-trajectory-report-v0"),
    );
    let drift_ref = artifact_ref(
        "architecture-drift-ledger",
        "tools/archsig/tests/fixtures/minimal/architecture_drift_ledger.json",
        Some("architecture-drift-ledger-v0"),
        Some("fixture-architecture-drift-ledger"),
    );
    let outcome_ref = artifact_ref(
        "outcome-linkage-dataset",
        "tools/archsig/tests/fixtures/minimal/outcome_linkage_dataset.json",
        Some("outcome-linkage-dataset-v0"),
        Some("fixture-outcome-linkage-dataset"),
    );
    let policy_ref = artifact_ref(
        "policy-decision-report",
        "tools/archsig/tests/fixtures/minimal/policy_decision_report.json",
        Some("policy-decision-report-v0"),
        Some("fixture-policy-decision-report"),
    );
    let ai_ref = artifact_ref(
        "ai-provenance-log",
        "tools/archsig/tests/fixtures/minimal/ai_provenance_log.json",
        None,
        Some("fixture-ai-provenance-log"),
    );

    let window = DynamicsAggregationWindowV0 {
        window_start: Some("2026-01-01T00:00:00Z".to_string()),
        window_end: Some("2026-01-31T23:59:59Z".to_string()),
        window_kind: "selected-fixture-window".to_string(),
    };

    ArchitectureDynamicsMetricsReportV0 {
        schema_version: ARCHITECTURE_DYNAMICS_METRICS_REPORT_SCHEMA_VERSION.to_string(),
        report_id: "fixture-architecture-dynamics-metrics-report-v0".to_string(),
        repository: RepositoryRef {
            owner: "iroha1203".to_string(),
            name: "AlgebraicArchitectureTheoryV2".to_string(),
            default_branch: "main".to_string(),
        },
        window: window.clone(),
        source_refs: vec![
            pr_force_ref.clone(),
            trajectory_ref.clone(),
            drift_ref.clone(),
            outcome_ref.clone(),
            policy_ref.clone(),
            ai_ref.clone(),
        ],
        trajectory_metrics: vec![
            metric(
                "trajectory.trajectoryDriftRate",
                None,
                "unmeasured",
                None,
                Vec::new(),
                gap_boundary(
                    "trajectory drift extractor is not implemented in the MVP fixture",
                    "unmeasured",
                ),
                &["trajectory report is a future source artifact in this fixture"],
                &[
                    "unmeasured trajectory drift is not zero drift",
                    "endpoint delta does not imply path safety",
                ],
            ),
            metric(
                "trajectory.trajectoryStability",
                None,
                "unavailable",
                None,
                vec![trajectory_ref.clone()],
                boundary(
                    "signature-trajectory",
                    &["TrajectoryStability"],
                    vec![trajectory_ref.clone()],
                    Some(window.clone()),
                    &["trajectory report schema is reserved but not retained in this fixture"],
                    &["global attractor inference"],
                ),
                &["selected finite trajectory evidence is unavailable"],
                &[
                    "unavailable stability is not instability evidence",
                    "trajectory stability does not claim global convergence",
                ],
            ),
        ],
        force_metrics: vec![
            metric(
                "force.observedForce",
                Some(json!({"boundaryViolationDelta": -2})),
                "measured",
                None,
                vec![pr_force_ref.clone()],
                boundary(
                    "pr-force",
                    &["ObservedForce"],
                    vec![pr_force_ref.clone()],
                    Some(window.clone()),
                    &["accepted PR force report is retained"],
                    &["rejected raw proposal force"],
                ),
                &["ObservedForce is read only from accepted PR force reports"],
                &[
                    FORCE_CLASS_NON_CONCLUSION,
                    "ObservedForce excludes rejected raw proposal force",
                ],
            ),
            metric(
                "force.latentForceEstimate",
                None,
                "unmeasured",
                None,
                Vec::new(),
                gap_boundary(
                    "operation proposal log is not available for latent force estimation",
                    "unmeasured",
                ),
                &["latent force needs proposal or review pressure evidence"],
                &[
                    FORCE_CLASS_NON_CONCLUSION,
                    "LatentForceEstimate is not inferred from ObservedForce",
                ],
            ),
            metric(
                "force.dissipatedForceEstimate",
                None,
                "unavailable",
                None,
                vec![policy_ref.clone()],
                boundary(
                    "development-control",
                    &["DissipatedForceEstimate"],
                    vec![policy_ref.clone()],
                    Some(window.clone()),
                    &["policy decision report is retained as dissipation mechanism context"],
                    &["causal proof of force dissipation"],
                ),
                &["dissipation ledger is not retained in this MVP fixture"],
                &[
                    FORCE_CLASS_NON_CONCLUSION,
                    "DissipatedForceEstimate is not inferred from ObservedForce",
                ],
            ),
            metric(
                "force.netPrForce",
                None,
                "notComparable",
                None,
                vec![pr_force_ref.clone()],
                boundary(
                    "pr-force",
                    &["NetPRForce"],
                    vec![pr_force_ref.clone()],
                    Some(window.clone()),
                    &["only one accepted PR force report is retained"],
                    &["cross-window normalization"],
                ),
                &["net force needs comparable additive axes across the selected window"],
                &["notComparable NetPRForce is not zero net force"],
            ),
        ],
        gap_metrics: vec![
            metric(
                "gap.forceCancellationRatio",
                None,
                "notComparable",
                None,
                vec![pr_force_ref.clone(), trajectory_ref.clone()],
                boundary(
                    "architecture-dynamics-gap",
                    &["ForceCancellationRatio"],
                    vec![pr_force_ref.clone(), trajectory_ref.clone()],
                    Some(window.clone()),
                    &["trajectory delta sequence is unavailable for denominator comparison"],
                    &["force cancellation theorem"],
                ),
                &["denominator or comparable trajectory evidence is unavailable"],
                &["notComparable ForceCancellationRatio is not measured cancellation"],
            ),
            metric(
                "gap.transientExcursionDebt",
                None,
                "unmeasured",
                None,
                Vec::new(),
                gap_boundary(
                    "selected bad-axis trajectory points are not available",
                    "unmeasured",
                ),
                &["transient excursion debt needs finite trajectory points"],
                &["endpoint safe does not imply path safe"],
            ),
        ],
        field_control_metrics: vec![
            metric(
                "fieldControl.dissipationCapacity",
                None,
                "unavailable",
                None,
                vec![policy_ref.clone(), outcome_ref.clone()],
                boundary(
                    "development-control",
                    &["DissipationCapacity"],
                    vec![policy_ref.clone(), outcome_ref.clone()],
                    Some(window.clone()),
                    &["policy and outcome refs are retained but proposal-level evidence is absent"],
                    &["organization-level causal capacity proof"],
                ),
                &["dissipation capacity needs proposal, policy, and trajectory evidence"],
                &["unavailable DissipationCapacity is not zero capacity"],
            ),
            metric(
                "fieldControl.designFieldStrength",
                None,
                "outOfScope",
                None,
                Vec::new(),
                gap_boundary(
                    "development field snapshot is outside the MVP fixture scope",
                    "outOfScope",
                ),
                &["field snapshot artifact is not part of the MVP fixture"],
                &["outOfScope DesignFieldStrength is not weak design field evidence"],
            ),
        ],
        ai_dynamics_metrics: vec![
            metric(
                "aiDynamics.operationDistributionShift",
                None,
                "private",
                None,
                vec![ai_ref.clone()],
                boundary(
                    "ai-provenance",
                    &["OperationDistributionShift"],
                    vec![ai_ref.clone()],
                    Some(window.clone()),
                    &["AI provenance may be private in the selected window"],
                    &["AI behavior theorem"],
                ),
                &["AI provenance evidence is private for this fixture"],
                &["private AI dynamics evidence is not zero distribution shift"],
            ),
            metric(
                "aiDynamics.aiPatchLyapunov",
                None,
                "outOfScope",
                None,
                Vec::new(),
                gap_boundary(
                    "Lyapunov-like AI patch protocol is outside the MVP fixture scope",
                    "outOfScope",
                ),
                &["simulation protocol is not fixed in this fixture"],
                &["AI patch Lyapunov-like metric is not a formal convergence theorem"],
            ),
        ],
        measurement_boundary: MeasurementBoundaryV0 {
            measured_layer: "architecture-dynamics".to_string(),
            measured_axes: vec![
                "trajectory".to_string(),
                "force".to_string(),
                "gap".to_string(),
                "fieldControl".to_string(),
                "aiDynamics".to_string(),
            ],
            source_artifact_refs: vec![
                pr_force_ref,
                trajectory_ref,
                drift_ref,
                outcome_ref,
                policy_ref,
                ai_ref,
            ],
            extractor_version: Some(EXTRACTOR_VERSION.to_string()),
            policy_version: Some("fixture-policy-v0".to_string()),
            schema_version: Some(ARCHITECTURE_DYNAMICS_METRICS_REPORT_SCHEMA_VERSION.to_string()),
            aggregation_window: Some(window),
            selected_region_refs: vec!["fixture:selected-dynamics-window".to_string()],
            assumptions: vec![
                "fixture records Architecture Dynamics metric slots for a bounded selected window"
                    .to_string(),
                "missing, private, unavailable, and notComparable metrics remain explicit"
                    .to_string(),
            ],
            unsupported_constructs: vec![
                "global attractor inference".to_string(),
                "causal incident-risk theorem".to_string(),
                "AI behavior theorem".to_string(),
            ],
            missing_evidence: vec![
                missing_evidence(
                    "signature-trajectory-report",
                    "trajectory report is a reserved future source for this fixture",
                    "unavailable",
                ),
                missing_evidence(
                    "operation-proposal-log",
                    "proposal log is not retained in the MVP fixture",
                    "unmeasured",
                ),
            ],
            non_conclusions: strings(&REQUIRED_NON_CONCLUSIONS),
        },
        non_conclusions: strings(&REQUIRED_NON_CONCLUSIONS),
    }
}

pub fn validate_architecture_dynamics_metrics_report(
    report: &ArchitectureDynamicsMetricsReportV0,
    input_path: &str,
) -> ArchitectureDynamicsMetricsReportValidationReportV0 {
    let checks = vec![
        check_schema_version(report),
        check_report_identity(report),
        check_measurement_statuses(report),
        check_null_value_statuses(report),
        check_measurement_boundaries(report),
        check_force_class_boundaries(report),
    ];
    let summary = ArchitectureDynamicsMetricsReportValidationSummary {
        result: if checks.iter().any(|check| check.result == "fail") {
            "fail".to_string()
        } else if checks.iter().any(|check| check.result == "warn") {
            "warn".to_string()
        } else {
            "pass".to_string()
        },
        trajectory_metric_count: report.trajectory_metrics.len(),
        force_metric_count: report.force_metrics.len(),
        gap_metric_count: report.gap_metrics.len(),
        field_control_metric_count: report.field_control_metrics.len(),
        ai_dynamics_metric_count: report.ai_dynamics_metrics.len(),
        failed_check_count: count_checks(&checks, "fail"),
        warning_check_count: count_checks(&checks, "warn"),
    };

    ArchitectureDynamicsMetricsReportValidationReportV0 {
        schema_version: ARCHITECTURE_DYNAMICS_METRICS_REPORT_VALIDATION_REPORT_SCHEMA_VERSION
            .to_string(),
        input: ArchitectureDynamicsMetricsReportValidationInput {
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
        schema_version: Some(ARCHITECTURE_DYNAMICS_METRICS_REPORT_SCHEMA_VERSION.to_string()),
        aggregation_window,
        selected_region_refs: vec!["fixture:selected-dynamics-window".to_string()],
        assumptions: strings(assumptions),
        unsupported_constructs: strings(unsupported_constructs),
        missing_evidence: Vec::new(),
        non_conclusions: strings(&REQUIRED_NON_CONCLUSIONS),
    }
}

fn gap_boundary(reason: &str, status: &str) -> MeasurementBoundaryV0 {
    MeasurementBoundaryV0 {
        measured_layer: "architecture-dynamics".to_string(),
        measured_axes: Vec::new(),
        source_artifact_refs: Vec::new(),
        extractor_version: Some(EXTRACTOR_VERSION.to_string()),
        policy_version: None,
        schema_version: Some(ARCHITECTURE_DYNAMICS_METRICS_REPORT_SCHEMA_VERSION.to_string()),
        aggregation_window: None,
        selected_region_refs: Vec::new(),
        assumptions: vec![reason.to_string()],
        unsupported_constructs: Vec::new(),
        missing_evidence: vec![missing_evidence(
            "architecture-dynamics-evidence",
            reason,
            status,
        )],
        non_conclusions: vec![format!(
            "{status} dynamics metric is not measured-zero evidence"
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

fn check_schema_version(report: &ArchitectureDynamicsMetricsReportV0) -> ValidationCheck {
    let mut check = validation_check(
        "architecture-dynamics-metrics-schema-version-supported",
        "architecture-dynamics-metrics-report schema version is supported",
        if report.schema_version == ARCHITECTURE_DYNAMICS_METRICS_REPORT_SCHEMA_VERSION {
            "pass"
        } else {
            "fail"
        },
    );
    if check.result == "fail" {
        check.reason = Some(format!(
            "unsupported architecture-dynamics-metrics-report schemaVersion: {}",
            report.schema_version
        ));
    }
    check
}

fn check_report_identity(report: &ArchitectureDynamicsMetricsReportV0) -> ValidationCheck {
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
    if report.source_refs.is_empty() || has_blank_artifact_refs(&report.source_refs) {
        invalid.push(generic_validation_example(
            &report.report_id,
            "sourceRefs",
            "report source refs must be explicit",
        ));
    }
    if report.trajectory_metrics.is_empty()
        || report.force_metrics.is_empty()
        || report.gap_metrics.is_empty()
        || report.field_control_metrics.is_empty()
        || report.ai_dynamics_metrics.is_empty()
    {
        invalid.push(generic_validation_example(
            &report.report_id,
            "metric groups",
            "trajectory, force, gap, fieldControl, and aiDynamics metric groups must be present",
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
        "architecture-dynamics-metrics-report-identity-recorded",
        "report identity, metric groups, source refs, and non-conclusions are recorded",
        invalid,
    )
}

fn check_measurement_statuses(report: &ArchitectureDynamicsMetricsReportV0) -> ValidationCheck {
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
        "architecture-dynamics-metrics-status-values-supported",
        "Architecture Dynamics metrics use only the common MeasurementStatus vocabulary",
        invalid,
    )
}

fn check_null_value_statuses(report: &ArchitectureDynamicsMetricsReportV0) -> ValidationCheck {
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
        "architecture-dynamics-metrics-null-value-not-measured-or-derived",
        "null Architecture Dynamics metric values are not promoted to measured or derived values",
        invalid,
    )
}

fn check_measurement_boundaries(report: &ArchitectureDynamicsMetricsReportV0) -> ValidationCheck {
    let evidence_required = string_set(EVIDENCE_REQUIRED_STATUSES);
    let mut invalid = Vec::new();
    validate_boundary(
        &report.report_id,
        "report.measurementBoundary",
        &report.measurement_boundary,
        true,
        &mut invalid,
    );
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
        "architecture-dynamics-metrics-boundaries-recorded",
        "Architecture Dynamics metrics preserve measurement boundary, evidence refs, assumptions, and non-conclusions",
        invalid,
    )
}

fn check_force_class_boundaries(report: &ArchitectureDynamicsMetricsReportV0) -> ValidationCheck {
    let mut invalid = Vec::new();
    let mut has_observed = false;
    let mut has_latent = false;
    let mut has_dissipated = false;

    for metric in &report.force_metrics {
        let class_count = force_class_count(&metric.metric_id);
        if class_count > 1 {
            invalid.push(generic_validation_example(
                &metric.metric_id,
                "metricId",
                "force metric id must not combine ObservedForce, LatentForceEstimate, and DissipatedForceEstimate",
            ));
        }
        if is_force_class_metric(&metric.metric_id) {
            if !metric
                .non_conclusions
                .iter()
                .any(|conclusion| conclusion == FORCE_CLASS_NON_CONCLUSION)
            {
                invalid.push(generic_validation_example(
                    &metric.metric_id,
                    "nonConclusions",
                    "force metric must explicitly keep observed, latent, and dissipated classes separate",
                ));
            }
        }
        let lower = metric.metric_id.to_ascii_lowercase();
        has_observed |= lower.contains("observedforce");
        has_latent |= lower.contains("latentforceestimate");
        has_dissipated |= lower.contains("dissipatedforceestimate");
    }

    if !has_observed || !has_latent || !has_dissipated {
        invalid.push(generic_validation_example(
            &report.report_id,
            "forceMetrics",
            "force metrics must retain separate ObservedForce, LatentForceEstimate, and DissipatedForceEstimate slots",
        ));
    }

    check_examples(
        "architecture-dynamics-metrics-force-classes-separated",
        "ObservedForce, LatentForceEstimate, and DissipatedForceEstimate are not conflated",
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

fn report_metrics(report: &ArchitectureDynamicsMetricsReportV0) -> Vec<&DynamicsMeasuredValueV0> {
    report
        .trajectory_metrics
        .iter()
        .chain(report.force_metrics.iter())
        .chain(report.gap_metrics.iter())
        .chain(report.field_control_metrics.iter())
        .chain(report.ai_dynamics_metrics.iter())
        .collect()
}

fn force_class_count(metric_id: &str) -> usize {
    let lower = metric_id.to_ascii_lowercase();
    [
        lower.contains("observedforce"),
        lower.contains("latentforceestimate"),
        lower.contains("dissipatedforceestimate"),
    ]
    .into_iter()
    .filter(|present| *present)
    .count()
}

fn is_force_class_metric(metric_id: &str) -> bool {
    force_class_count(metric_id) == 1
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
