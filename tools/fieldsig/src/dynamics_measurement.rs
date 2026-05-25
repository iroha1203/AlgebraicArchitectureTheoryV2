use std::collections::BTreeSet;

use serde_json::json;

use crate::validation::{count_checks, generic_validation_example, validation_check};
use crate::{
    DYNAMICS_MEASUREMENT_CONTRACT_SCHEMA_VERSION,
    DYNAMICS_MEASUREMENT_CONTRACT_VALIDATION_REPORT_SCHEMA_VERSION, DynamicsAggregationWindowV0,
    DynamicsArtifactRefV0, DynamicsMeasuredValueV0, DynamicsMeasurementContractV0,
    DynamicsMeasurementContractValidationInput, DynamicsMeasurementContractValidationReportV0,
    DynamicsMeasurementContractValidationSummary, DynamicsMissingEvidenceV0, EXTRACTOR_VERSION,
    MeasurementBoundaryV0, ValidationCheck, ValidationExample,
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
    "dynamics measurement contract is tooling validation, not a Lean theorem",
    "unmeasured, unavailable, private, notComparable, and outOfScope values are not measured zero",
    "estimated dynamics metrics are not formal measured values",
    "dynamics artifacts do not conclude architecture lawfulness",
];

pub fn static_dynamics_measurement_contract() -> DynamicsMeasurementContractV0 {
    let source_ref = artifact_ref(
        "signature-snapshot-store",
        "tools/archsig/tests/fixtures/minimal/signature_snapshot_store.json",
        Some("signature-snapshot-store-v0"),
        Some("fixture-signature-snapshot"),
    );
    let pr_ref = artifact_ref(
        "pr-history-dataset",
        "tools/archsig/tests/fixtures/minimal/pr_history_dataset.json",
        Some("pr-history-dataset-v0"),
        Some("fixture-pr-history"),
    );

    DynamicsMeasurementContractV0 {
        schema_version: DYNAMICS_MEASUREMENT_CONTRACT_SCHEMA_VERSION.to_string(),
        artifact_id: "fixture-dynamics-measurement-contract-v0".to_string(),
        scope: "canonical Architecture Dynamics measurement status boundary fixture".to_string(),
        metrics: vec![
            metric(
                "observedForce.boundaryViolationDelta",
                Some(json!(2)),
                "measured",
                None,
                vec![source_ref.clone()],
                boundary(
                    "signature",
                    &["boundaryViolationCount"],
                    vec![source_ref.clone()],
                    &["selected PR before and after signatures are available"],
                    &[],
                ),
                &["selected Signature snapshots are comparable"],
                &[
                    "measured force delta is limited to the selected Signature axis",
                    "measured delta is not a global architecture lawfulness claim",
                ],
            ),
            metric(
                "observedForce.netDelta",
                Some(json!(2)),
                "derived",
                None,
                vec![source_ref.clone()],
                boundary(
                    "signature",
                    &["boundaryViolationCount"],
                    vec![source_ref.clone()],
                    &["derived from measured before and after Signature values"],
                    &[],
                ),
                &["source Signature axis values are measured"],
                &[
                    "derived net delta is deterministic over selected source artifacts only",
                    "derived value is not a theorem about future dynamics",
                ],
            ),
            metric(
                "latentForce.reviewPressure",
                Some(json!(0.63)),
                "estimated",
                Some("medium"),
                vec![pr_ref.clone()],
                boundary(
                    "review",
                    &["reviewPressure"],
                    vec![pr_ref.clone()],
                    &["review metadata is available for the selected PR window"],
                    &[],
                ),
                &[
                    "review pressure is estimated from bounded PR metadata",
                    "missing rejected proposals are outside this fixture",
                ],
                &[
                    "estimated review pressure is not a measured force value",
                    "estimated value is not a theorem claim",
                ],
            ),
            metric(
                "control.advisorySignal",
                None,
                "advisory",
                None,
                vec![pr_ref.clone()],
                boundary(
                    "review",
                    &["controlSignal"],
                    vec![pr_ref.clone()],
                    &["review policy signal is available"],
                    &[],
                ),
                &["advisory signal is generated for reviewer attention only"],
                &[
                    "advisory signal is not a measured value",
                    "advisory signal is not a formal claim",
                ],
            ),
            status_gap_metric(
                "field.localGrammar",
                "unmeasured",
                "local grammar extractor not run",
            ),
            status_gap_metric(
                "trajectory.incidentOutcome",
                "unavailable",
                "incident outcome source was not retained",
            ),
            status_gap_metric(
                "trajectory.privateRuntime",
                "private",
                "runtime trace is private",
            ),
            status_gap_metric(
                "trajectory.baselineDelta",
                "notComparable",
                "baseline used a different extraction policy",
            ),
            status_gap_metric(
                "field.generatedRegion",
                "outOfScope",
                "generated-code region is outside this fixture scope",
            ),
        ],
        measurement_boundary: MeasurementBoundaryV0 {
            measured_layer: "architecture-dynamics".to_string(),
            measured_axes: vec![
                "observedForce".to_string(),
                "latentForce".to_string(),
                "controlSignal".to_string(),
            ],
            source_artifact_refs: vec![source_ref, pr_ref],
            extractor_version: Some(EXTRACTOR_VERSION.to_string()),
            policy_version: Some("fixture-policy-v0".to_string()),
            schema_version: Some(DYNAMICS_MEASUREMENT_CONTRACT_SCHEMA_VERSION.to_string()),
            aggregation_window: Some(DynamicsAggregationWindowV0 {
                window_start: Some("2026-01-01T00:00:00Z".to_string()),
                window_end: Some("2026-01-31T23:59:59Z".to_string()),
                window_kind: "fixture-window".to_string(),
            }),
            selected_region_refs: vec!["fixture:selected-pr-window".to_string()],
            assumptions: vec![
                "fixture covers a selected finite PR window".to_string(),
                "source artifact refs are retained only as tooling evidence".to_string(),
            ],
            unsupported_constructs: vec![
                "proposal completeness".to_string(),
                "global attractor inference".to_string(),
            ],
            missing_evidence: vec![missing_evidence(
                "operation-proposal-log",
                "proposal log is not part of the MVP fixture",
                "unmeasured",
            )],
            non_conclusions: strings(&REQUIRED_NON_CONCLUSIONS),
        },
        non_conclusions: strings(&REQUIRED_NON_CONCLUSIONS),
    }
}

pub fn validate_dynamics_measurement_contract_report(
    contract: &DynamicsMeasurementContractV0,
    input_path: &str,
) -> DynamicsMeasurementContractValidationReportV0 {
    let checks = vec![
        check_schema_version(contract),
        check_contract_identity(contract),
        check_measurement_statuses(contract),
        check_null_value_statuses(contract),
        check_estimated_metric_evidence(contract),
        check_measurement_boundaries(contract),
    ];
    let summary = DynamicsMeasurementContractValidationSummary {
        result: if checks.iter().any(|check| check.result == "fail") {
            "fail".to_string()
        } else if checks.iter().any(|check| check.result == "warn") {
            "warn".to_string()
        } else {
            "pass".to_string()
        },
        metric_count: contract.metrics.len(),
        failed_check_count: count_checks(&checks, "fail"),
        warning_check_count: count_checks(&checks, "warn"),
    };

    DynamicsMeasurementContractValidationReportV0 {
        schema_version: DYNAMICS_MEASUREMENT_CONTRACT_VALIDATION_REPORT_SCHEMA_VERSION.to_string(),
        input: DynamicsMeasurementContractValidationInput {
            schema_version: contract.schema_version.clone(),
            path: input_path.to_string(),
            artifact_id: contract.artifact_id.clone(),
            scope: contract.scope.clone(),
        },
        contract: contract.clone(),
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

fn status_gap_metric(metric_id: &str, status: &str, reason: &str) -> DynamicsMeasuredValueV0 {
    DynamicsMeasuredValueV0 {
        metric_id: metric_id.to_string(),
        value: None,
        status: status.to_string(),
        confidence: None,
        source_refs: Vec::new(),
        measurement_boundary: MeasurementBoundaryV0 {
            measured_layer: "architecture-dynamics".to_string(),
            measured_axes: Vec::new(),
            source_artifact_refs: Vec::new(),
            extractor_version: Some(EXTRACTOR_VERSION.to_string()),
            policy_version: None,
            schema_version: Some(DYNAMICS_MEASUREMENT_CONTRACT_SCHEMA_VERSION.to_string()),
            aggregation_window: None,
            selected_region_refs: Vec::new(),
            assumptions: vec![reason.to_string()],
            unsupported_constructs: Vec::new(),
            missing_evidence: vec![missing_evidence("dynamics-evidence", reason, status)],
            non_conclusions: vec![format!("{status} dynamics evidence is not measured-zero")],
        },
        assumptions: vec![reason.to_string()],
        non_conclusions: vec![format!(
            "{status} dynamics metric is not measured-zero evidence"
        )],
    }
}

fn boundary(
    measured_layer: &str,
    measured_axes: &[&str],
    source_artifact_refs: Vec<DynamicsArtifactRefV0>,
    assumptions: &[&str],
    unsupported_constructs: &[&str],
) -> MeasurementBoundaryV0 {
    MeasurementBoundaryV0 {
        measured_layer: measured_layer.to_string(),
        measured_axes: strings(measured_axes),
        source_artifact_refs,
        extractor_version: Some(EXTRACTOR_VERSION.to_string()),
        policy_version: Some("fixture-policy-v0".to_string()),
        schema_version: Some(DYNAMICS_MEASUREMENT_CONTRACT_SCHEMA_VERSION.to_string()),
        aggregation_window: None,
        selected_region_refs: vec!["fixture:selected-pr-window".to_string()],
        assumptions: strings(assumptions),
        unsupported_constructs: strings(unsupported_constructs),
        missing_evidence: Vec::new(),
        non_conclusions: strings(&REQUIRED_NON_CONCLUSIONS),
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

fn check_schema_version(contract: &DynamicsMeasurementContractV0) -> ValidationCheck {
    let mut check = validation_check(
        "dynamics-measurement-contract-schema-version-supported",
        "dynamics measurement contract schema version is supported",
        if contract.schema_version == DYNAMICS_MEASUREMENT_CONTRACT_SCHEMA_VERSION {
            "pass"
        } else {
            "fail"
        },
    );
    if check.result == "fail" {
        check.reason = Some(format!(
            "unsupported dynamics measurement contract schemaVersion: {}",
            contract.schema_version
        ));
    }
    check
}

fn check_contract_identity(contract: &DynamicsMeasurementContractV0) -> ValidationCheck {
    let mut invalid = Vec::new();
    if contract.artifact_id.trim().is_empty() {
        invalid.push(generic_validation_example(
            "artifactId",
            &contract.scope,
            "artifact_id must be non-empty",
        ));
    }
    if contract.scope.trim().is_empty() {
        invalid.push(generic_validation_example(
            &contract.artifact_id,
            "scope",
            "scope must be non-empty",
        ));
    }
    if contract.metrics.is_empty() {
        invalid.push(generic_validation_example(
            &contract.artifact_id,
            "metrics",
            "contract must contain at least one dynamics metric",
        ));
    }
    for required in REQUIRED_NON_CONCLUSIONS {
        if !contract
            .non_conclusions
            .iter()
            .any(|conclusion| conclusion == required)
        {
            invalid.push(generic_validation_example(
                &contract.artifact_id,
                "nonConclusions",
                &format!("missing required non-conclusion: {required}"),
            ));
        }
    }
    check_examples(
        "dynamics-measurement-contract-identity-recorded",
        "artifact id, scope, metrics, and non-conclusion boundary are recorded",
        invalid,
    )
}

fn check_measurement_statuses(contract: &DynamicsMeasurementContractV0) -> ValidationCheck {
    let allowed = string_set(ALLOWED_STATUSES);
    let invalid = contract
        .metrics
        .iter()
        .filter(|metric| !allowed.contains(metric.status.as_str()))
        .map(|metric| {
            generic_validation_example(
                &metric.metric_id,
                &metric.status,
                "unsupported MeasurementStatus",
            )
        })
        .collect();
    check_examples(
        "dynamics-measurement-status-values-supported",
        "MeasurementStatus uses only the common dynamics status vocabulary",
        invalid,
    )
}

fn check_null_value_statuses(contract: &DynamicsMeasurementContractV0) -> ValidationCheck {
    let value_required = string_set(VALUE_REQUIRED_STATUSES);
    let invalid = contract
        .metrics
        .iter()
        .filter(|metric| value_required.contains(metric.status.as_str()) && metric.value.is_none())
        .map(|metric| {
            generic_validation_example(
                &metric.metric_id,
                &metric.status,
                "value = null cannot be emitted as measured or derived",
            )
        })
        .collect();
    check_examples(
        "dynamics-null-value-not-measured-or-derived",
        "null dynamics metric values are not promoted to measured or derived values",
        invalid,
    )
}

fn check_estimated_metric_evidence(contract: &DynamicsMeasurementContractV0) -> ValidationCheck {
    let mut invalid = Vec::new();
    for metric in contract
        .metrics
        .iter()
        .filter(|metric| metric.status == "estimated")
    {
        if is_blank_option(&metric.confidence) {
            invalid.push(generic_validation_example(
                &metric.metric_id,
                "confidence",
                "estimated metric must record confidence",
            ));
        }
        if metric.source_refs.is_empty() || has_blank_artifact_refs(&metric.source_refs) {
            invalid.push(generic_validation_example(
                &metric.metric_id,
                "sourceRefs",
                "estimated metric must record source refs",
            ));
        }
        if metric.assumptions.is_empty() || has_blank(&metric.assumptions) {
            invalid.push(generic_validation_example(
                &metric.metric_id,
                "assumptions",
                "estimated metric must record assumptions",
            ));
        }
        if metric.non_conclusions.is_empty() || has_blank(&metric.non_conclusions) {
            invalid.push(generic_validation_example(
                &metric.metric_id,
                "nonConclusions",
                "estimated metric must record non-conclusions",
            ));
        }
    }
    check_examples(
        "dynamics-estimated-metric-evidence-recorded",
        "estimated dynamics metrics record confidence, source refs, assumptions, and non-conclusions",
        invalid,
    )
}

fn check_measurement_boundaries(contract: &DynamicsMeasurementContractV0) -> ValidationCheck {
    let evidence_required = string_set(EVIDENCE_REQUIRED_STATUSES);
    let mut invalid = Vec::new();
    validate_boundary(
        &contract.artifact_id,
        "contract.measurementBoundary",
        &contract.measurement_boundary,
        true,
        &mut invalid,
    );
    for metric in &contract.metrics {
        validate_boundary(
            &metric.metric_id,
            "metrics[].measurementBoundary",
            &metric.measurement_boundary,
            evidence_required.contains(metric.status.as_str()),
            &mut invalid,
        );
    }
    check_examples(
        "dynamics-measurement-boundaries-recorded",
        "DynamicsMeasuredValue and MeasurementBoundary preserve measured axes, source refs, assumptions, and non-conclusions",
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
            "measuredAxes must be explicit for measured, estimated, derived, and advisory metrics",
        ));
    }
    if source_refs_required
        && (boundary.source_artifact_refs.is_empty()
            || has_blank_artifact_refs(&boundary.source_artifact_refs))
    {
        invalid.push(generic_validation_example(
            owner,
            "sourceArtifactRefs",
            "sourceArtifactRefs must be explicit for measured, estimated, derived, and advisory metrics",
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

fn is_blank_option(value: &Option<String>) -> bool {
    value.as_ref().is_none_or(|value| value.trim().is_empty())
}

fn has_blank_artifact_refs(refs: &[DynamicsArtifactRefV0]) -> bool {
    refs.iter().any(|artifact_ref| {
        artifact_ref.kind.trim().is_empty() || artifact_ref.path.trim().is_empty()
    })
}

fn string_set<const N: usize>(values: [&'static str; N]) -> BTreeSet<&'static str> {
    values.into_iter().collect()
}
