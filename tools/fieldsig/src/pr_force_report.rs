use std::collections::BTreeSet;

use serde_json::json;

use crate::validation::{count_checks, generic_validation_example, validation_check};
use crate::{
    DynamicsAggregationWindowV0, DynamicsArtifactRefV0, DynamicsMeasuredValueV0,
    DynamicsMissingEvidenceV0, EXTRACTOR_VERSION, FEATURE_EXTENSION_REPORT_SCHEMA_VERSION,
    ForceComponentV0, ForceDecompositionV0, MeasurementBoundaryV0, PR_FORCE_REPORT_SCHEMA_VERSION,
    PR_FORCE_REPORT_VALIDATION_REPORT_SCHEMA_VERSION, PrForceReportV0,
    PrForceReportValidationInput, PrForceReportValidationReportV0, PrForceReportValidationSummary,
    PullRequestRefV0, SIGNATURE_DIFF_REPORT_SCHEMA_VERSION,
    SIGNATURE_SNAPSHOT_STORE_SCHEMA_VERSION, SignedSignatureDeltaV0,
    THEOREM_PRECONDITION_CHECK_REPORT_SCHEMA_VERSION, ValidationCheck, ValidationExample,
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
    "PR force is a vector artifact, not a single score",
    "observed force excludes rejected raw proposal force",
    "force decomposition is tooling evidence, not a Lean theorem claim",
    "measured delta does not convert unmeasured semantic or runtime axes to zero",
];

pub fn static_pr_force_report() -> PrForceReportV0 {
    let before_ref = artifact_ref(
        "signature-snapshot-store",
        "tools/archsig/tests/fixtures/minimal/signature_snapshot_before.json",
        Some(SIGNATURE_SNAPSHOT_STORE_SCHEMA_VERSION),
        Some("fixture-pr-force-before-signature"),
    );
    let after_ref = artifact_ref(
        "signature-snapshot-store",
        "tools/archsig/tests/fixtures/minimal/signature_snapshot_after.json",
        Some(SIGNATURE_SNAPSHOT_STORE_SCHEMA_VERSION),
        Some("fixture-pr-force-after-signature"),
    );
    let diff_ref = artifact_ref(
        "signature-diff-report",
        "tools/archsig/tests/fixtures/minimal/signature_diff_report.json",
        Some(SIGNATURE_DIFF_REPORT_SCHEMA_VERSION),
        Some("fixture-pr-force-signature-diff"),
    );
    let empirical_ref = artifact_ref(
        "empirical-signature-dataset",
        "tools/archsig/tests/fixtures/minimal/empirical_signature_dataset.json",
        Some("empirical-signature-dataset-v0"),
        Some("fixture-pr-force-empirical-dataset"),
    );
    let feature_ref = artifact_ref(
        "feature-extension-report",
        "tools/archsig/tests/fixtures/minimal/feature_extension_report.json",
        Some(FEATURE_EXTENSION_REPORT_SCHEMA_VERSION),
        Some("fixture-feature-extension-report"),
    );
    let theorem_ref = artifact_ref(
        "theorem-precondition-check-report",
        "tools/archsig/tests/fixtures/minimal/theorem_precondition_check_report.json",
        Some(THEOREM_PRECONDITION_CHECK_REPORT_SCHEMA_VERSION),
        Some("fixture-theorem-precondition-check"),
    );

    PrForceReportV0 {
        schema_version: PR_FORCE_REPORT_SCHEMA_VERSION.to_string(),
        report_id: "fixture-pr-force-report-v0".to_string(),
        pull_request: PullRequestRefV0 {
            provider: "github".to_string(),
            repository: "iroha1203/AlgebraicArchitectureTheoryV2".to_string(),
            number: 675,
            transition_kind: "accepted".to_string(),
            merged_at: Some("2026-01-15T12:00:00Z".to_string()),
            non_conclusions: vec![
                "accepted PR transition does not include rejected proposal force".to_string(),
                "PR outcome is not an incident-risk theorem".to_string(),
            ],
        },
        signature_before_ref: before_ref.clone(),
        signature_after_ref: after_ref.clone(),
        delta_signature_signed: vec![
            signed_delta(
                "boundaryViolationCount",
                Some(json!(3)),
                Some(json!(1)),
                Some(json!(-2)),
                "measured",
                vec![before_ref.clone(), after_ref.clone(), diff_ref.clone()],
                &[
                    "selected before and after Signature snapshots are comparable",
                    "negative delta means fewer observed boundary violations in the selected axes",
                ],
            ),
            signed_delta(
                "runtimePropagationRisk",
                None,
                None,
                None,
                "unmeasured",
                Vec::new(),
                &[
                    "runtime propagation extractor was not run for this fixture",
                    "unmeasured runtime delta is not zero",
                ],
            ),
        ],
        observed_force: vec![
            measured_value(
                "observedForce.boundaryViolationDelta",
                Some(json!(-2)),
                "measured",
                None,
                vec![diff_ref.clone(), empirical_ref.clone()],
                boundary(
                    "signature",
                    &["boundaryViolationCount"],
                    vec![diff_ref.clone(), empirical_ref.clone()],
                    &[
                        "observed force is computed only from accepted before/after Signature artifacts",
                    ],
                    &["rejected proposal force"],
                ),
                &["accepted PR transition has comparable Signature snapshots"],
                &[
                    "observed force excludes rejected raw proposal force",
                    "observed force is not a single architecture quality score",
                ],
            ),
            measured_value(
                "observedForce.runtimePropagationRisk",
                None,
                "unmeasured",
                None,
                Vec::new(),
                gap_boundary(
                    "runtime propagation evidence is outside this PR force fixture",
                    "unmeasured",
                ),
                &["runtime propagation extractor was not run for this fixture"],
                &[
                    "observed force excludes rejected raw proposal force",
                    "unmeasured observed force is not measured-zero evidence",
                ],
            ),
        ],
        force_decomposition: ForceDecompositionV0 {
            decomposition_id: "fixture-pr-force-decomposition".to_string(),
            components: vec![
                force_component(
                    "fixture-feature-component",
                    "feature",
                    measured_value(
                        "forceDecomposition.feature",
                        Some(json!(-1)),
                        "advisory",
                        None,
                        vec![feature_ref.clone()],
                        boundary(
                            "feature-extension-report",
                            &["featureSplitAssessment"],
                            vec![feature_ref.clone()],
                            &["feature report is available for the accepted PR"],
                            &["formal force attribution"],
                        ),
                        &["heuristic component is reviewer guidance only"],
                        &[
                            "heuristic force decomposition remains advisory",
                            "force decomposition is tooling evidence, not a Lean theorem claim",
                        ],
                    ),
                    "heuristic",
                    vec![feature_ref.clone()],
                    Vec::new(),
                    &[
                        "heuristic force decomposition remains advisory",
                        "component does not promote a formal force theorem",
                    ],
                ),
                force_component(
                    "fixture-theorem-precondition-component",
                    "theoremPrecondition",
                    measured_value(
                        "forceDecomposition.theoremPrecondition",
                        None,
                        "unavailable",
                        None,
                        vec![theorem_ref.clone()],
                        boundary(
                            "theorem-precondition",
                            &["undischargedAssumptionRefs"],
                            vec![theorem_ref.clone()],
                            &["precondition report is retained"],
                            &["PR outcome theorem claim"],
                        ),
                        &["precondition refs are retained as tooling evidence"],
                        &["unavailable theorem-precondition force is not zero"],
                    ),
                    "source-ref",
                    vec![theorem_ref.clone()],
                    Vec::new(),
                    &["theorem precondition refs are not PR outcome theorems"],
                ),
            ],
            assumptions: vec![
                "decomposition uses only retained MVP fixture artifacts".to_string(),
                "heuristic components are reviewer guidance, not measured formal force".to_string(),
            ],
            non_conclusions: strings(&REQUIRED_NON_CONCLUSIONS),
        },
        feature_extension_report_refs: vec![feature_ref],
        theorem_precondition_refs: vec![theorem_ref],
        measurement_boundary: MeasurementBoundaryV0 {
            measured_layer: "architecture-dynamics".to_string(),
            measured_axes: vec![
                "observedForce".to_string(),
                "deltaSignatureSigned".to_string(),
                "forceDecomposition".to_string(),
            ],
            source_artifact_refs: vec![before_ref, after_ref, diff_ref, empirical_ref],
            extractor_version: Some(EXTRACTOR_VERSION.to_string()),
            policy_version: Some("fixture-policy-v0".to_string()),
            schema_version: Some(PR_FORCE_REPORT_SCHEMA_VERSION.to_string()),
            aggregation_window: Some(DynamicsAggregationWindowV0 {
                window_start: Some("2026-01-01T00:00:00Z".to_string()),
                window_end: Some("2026-01-31T23:59:59Z".to_string()),
                window_kind: "selected-pr".to_string(),
            }),
            selected_region_refs: vec!["fixture:accepted-pr-675".to_string()],
            assumptions: vec![
                "fixture records one accepted PR transition".to_string(),
                "source artifacts are retained as tooling evidence".to_string(),
            ],
            unsupported_constructs: vec![
                "rejected raw proposal force".to_string(),
                "global force field inference".to_string(),
            ],
            missing_evidence: vec![missing_evidence(
                "operation-proposal-log",
                "rejected raw proposals are outside this MVP fixture",
                "unmeasured",
            )],
            non_conclusions: strings(&REQUIRED_NON_CONCLUSIONS),
        },
        non_conclusions: strings(&REQUIRED_NON_CONCLUSIONS),
    }
}

pub fn validate_pr_force_report(
    report: &PrForceReportV0,
    input_path: &str,
) -> PrForceReportValidationReportV0 {
    let checks = vec![
        check_schema_version(report),
        check_report_identity(report),
        check_measurement_statuses(report),
        check_null_value_statuses(report),
        check_measurement_boundaries(report),
        check_observed_force_boundary(report),
        check_force_decomposition_boundary(report),
    ];
    let summary = PrForceReportValidationSummary {
        result: if checks.iter().any(|check| check.result == "fail") {
            "fail".to_string()
        } else if checks.iter().any(|check| check.result == "warn") {
            "warn".to_string()
        } else {
            "pass".to_string()
        },
        observed_force_count: report.observed_force.len(),
        decomposition_component_count: report.force_decomposition.components.len(),
        failed_check_count: count_checks(&checks, "fail"),
        warning_check_count: count_checks(&checks, "warn"),
    };

    PrForceReportValidationReportV0 {
        schema_version: PR_FORCE_REPORT_VALIDATION_REPORT_SCHEMA_VERSION.to_string(),
        input: PrForceReportValidationInput {
            schema_version: report.schema_version.clone(),
            path: input_path.to_string(),
            report_id: report.report_id.clone(),
            pull_request: format!(
                "{}/#{}",
                report.pull_request.repository, report.pull_request.number
            ),
        },
        report: report.clone(),
        summary,
        checks,
    }
}

fn signed_delta(
    axis_id: &str,
    before: Option<serde_json::Value>,
    after: Option<serde_json::Value>,
    delta: Option<serde_json::Value>,
    status: &str,
    source_refs: Vec<DynamicsArtifactRefV0>,
    non_conclusions: &[&str],
) -> SignedSignatureDeltaV0 {
    SignedSignatureDeltaV0 {
        axis_id: axis_id.to_string(),
        before,
        after,
        delta,
        status: status.to_string(),
        source_refs: source_refs.clone(),
        measurement_boundary: if source_refs.is_empty() {
            gap_boundary("delta source artifacts are unavailable", status)
        } else {
            boundary(
                "signature",
                &[axis_id],
                source_refs,
                &["delta is scoped to retained before/after Signature artifacts"],
                &[],
            )
        },
        non_conclusions: strings(non_conclusions),
    }
}

fn measured_value(
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

fn force_component(
    component_id: &str,
    component_kind: &str,
    contribution: DynamicsMeasuredValueV0,
    decomposition_method: &str,
    evidence_refs: Vec<DynamicsArtifactRefV0>,
    theorem_claim_refs: Vec<String>,
    non_conclusions: &[&str],
) -> ForceComponentV0 {
    ForceComponentV0 {
        component_id: component_id.to_string(),
        component_kind: component_kind.to_string(),
        contribution,
        decomposition_method: decomposition_method.to_string(),
        evidence_refs,
        theorem_claim_refs,
        non_conclusions: strings(non_conclusions),
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
        schema_version: Some(PR_FORCE_REPORT_SCHEMA_VERSION.to_string()),
        aggregation_window: None,
        selected_region_refs: vec!["fixture:accepted-pr-675".to_string()],
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
        schema_version: Some(PR_FORCE_REPORT_SCHEMA_VERSION.to_string()),
        aggregation_window: None,
        selected_region_refs: Vec::new(),
        assumptions: vec![reason.to_string()],
        unsupported_constructs: Vec::new(),
        missing_evidence: vec![missing_evidence("pr-force-evidence", reason, status)],
        non_conclusions: vec![format!("{status} PR force evidence is not measured-zero")],
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

fn check_schema_version(report: &PrForceReportV0) -> ValidationCheck {
    let mut check = validation_check(
        "pr-force-report-schema-version-supported",
        "pr-force-report schema version is supported",
        if report.schema_version == PR_FORCE_REPORT_SCHEMA_VERSION {
            "pass"
        } else {
            "fail"
        },
    );
    if check.result == "fail" {
        check.reason = Some(format!(
            "unsupported pr-force-report schemaVersion: {}",
            report.schema_version
        ));
    }
    check
}

fn check_report_identity(report: &PrForceReportV0) -> ValidationCheck {
    let mut invalid = Vec::new();
    if report.report_id.trim().is_empty() {
        invalid.push(generic_validation_example(
            "reportId",
            &report.schema_version,
            "reportId must be non-empty",
        ));
    }
    if report.pull_request.transition_kind != "accepted" {
        invalid.push(generic_validation_example(
            &report.report_id,
            "pullRequest.transitionKind",
            "PR force report records only accepted transitions",
        ));
    }
    if report.delta_signature_signed.is_empty() {
        invalid.push(generic_validation_example(
            &report.report_id,
            "deltaSignatureSigned",
            "report must record at least one signed Signature delta slot",
        ));
    }
    if report.observed_force.is_empty() {
        invalid.push(generic_validation_example(
            &report.report_id,
            "observedForce",
            "report must record at least one observed force slot",
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
        "pr-force-report-identity-recorded",
        "report identity, accepted transition, vector slots, and non-conclusions are recorded",
        invalid,
    )
}

fn check_measurement_statuses(report: &PrForceReportV0) -> ValidationCheck {
    let allowed = string_set(ALLOWED_STATUSES);
    let mut invalid = Vec::new();
    for delta in &report.delta_signature_signed {
        if !allowed.contains(delta.status.as_str()) {
            invalid.push(generic_validation_example(
                &delta.axis_id,
                &delta.status,
                "unsupported MeasurementStatus",
            ));
        }
    }
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
        "pr-force-measurement-status-values-supported",
        "PR force report uses only the common dynamics MeasurementStatus vocabulary",
        invalid,
    )
}

fn check_null_value_statuses(report: &PrForceReportV0) -> ValidationCheck {
    let value_required = string_set(VALUE_REQUIRED_STATUSES);
    let mut invalid = Vec::new();
    for delta in &report.delta_signature_signed {
        if value_required.contains(delta.status.as_str()) && delta.delta.is_none() {
            invalid.push(generic_validation_example(
                &delta.axis_id,
                &delta.status,
                "delta = null cannot be emitted as measured or derived",
            ));
        }
    }
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
        "pr-force-null-value-not-measured-or-derived",
        "null PR force values are not promoted to measured or derived values",
        invalid,
    )
}

fn check_measurement_boundaries(report: &PrForceReportV0) -> ValidationCheck {
    let evidence_required = string_set(EVIDENCE_REQUIRED_STATUSES);
    let mut invalid = Vec::new();
    validate_boundary(
        &report.report_id,
        "report.measurementBoundary",
        &report.measurement_boundary,
        true,
        &mut invalid,
    );
    for delta in &report.delta_signature_signed {
        validate_boundary(
            &delta.axis_id,
            "deltaSignatureSigned[].measurementBoundary",
            &delta.measurement_boundary,
            evidence_required.contains(delta.status.as_str()),
            &mut invalid,
        );
    }
    for metric in report_metrics(report) {
        validate_boundary(
            &metric.metric_id,
            "measurementBoundary",
            &metric.measurement_boundary,
            evidence_required.contains(metric.status.as_str()),
            &mut invalid,
        );
    }
    check_examples(
        "pr-force-measurement-boundaries-recorded",
        "PR force values preserve measurement boundary, evidence refs, assumptions, and non-conclusions",
        invalid,
    )
}

fn check_observed_force_boundary(report: &PrForceReportV0) -> ValidationCheck {
    let mut invalid = Vec::new();
    for metric in &report.observed_force {
        let lower_id = metric.metric_id.to_ascii_lowercase();
        if lower_id.contains("raw") || lower_id.contains("rejected") {
            invalid.push(generic_validation_example(
                &metric.metric_id,
                "observedForce",
                "ObservedForce must not encode rejected raw proposal force",
            ));
        }
        if !metric
            .non_conclusions
            .iter()
            .any(|conclusion| conclusion == "observed force excludes rejected raw proposal force")
        {
            invalid.push(generic_validation_example(
                &metric.metric_id,
                "nonConclusions",
                "ObservedForce must explicitly exclude rejected raw proposal force",
            ));
        }
        for source_ref in &metric.source_refs {
            let lower_kind = source_ref.kind.to_ascii_lowercase();
            if lower_kind.contains("rejected") || lower_kind.contains("raw-proposal") {
                invalid.push(generic_validation_example(
                    &metric.metric_id,
                    &source_ref.kind,
                    "ObservedForce source refs must not be rejected raw proposal evidence",
                ));
            }
        }
    }
    check_examples(
        "pr-force-observed-force-excludes-rejected-raw-force",
        "ObservedForce is kept separate from rejected raw proposal force",
        invalid,
    )
}

fn check_force_decomposition_boundary(report: &PrForceReportV0) -> ValidationCheck {
    let mut invalid = Vec::new();
    if report.force_decomposition.components.is_empty() {
        invalid.push(generic_validation_example(
            &report.report_id,
            "forceDecomposition.components",
            "force decomposition must keep explicit component slots",
        ));
    }
    for component in &report.force_decomposition.components {
        if component.component_kind.trim().is_empty() {
            invalid.push(generic_validation_example(
                &component.component_id,
                "componentKind",
                "force component kind must be non-empty",
            ));
        }
        if component.decomposition_method == "heuristic" {
            if component.contribution.status != "advisory" {
                invalid.push(generic_validation_example(
                    &component.component_id,
                    &component.contribution.status,
                    "heuristic force decomposition must remain advisory",
                ));
            }
            if !component.theorem_claim_refs.is_empty() {
                invalid.push(generic_validation_example(
                    &component.component_id,
                    "theoremClaimRefs",
                    "heuristic force decomposition must not promote theorem claims",
                ));
            }
            if !component.non_conclusions.iter().any(|conclusion| {
                conclusion == "heuristic force decomposition remains advisory"
                    || conclusion
                        == "force decomposition is tooling evidence, not a Lean theorem claim"
            }) {
                invalid.push(generic_validation_example(
                    &component.component_id,
                    "nonConclusions",
                    "heuristic decomposition must record advisory non-conclusion",
                ));
            }
        }
    }
    check_examples(
        "pr-force-decomposition-remains-advisory",
        "heuristic force decomposition is advisory and does not promote formal claims",
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

fn report_metrics(report: &PrForceReportV0) -> Vec<&DynamicsMeasuredValueV0> {
    report
        .observed_force
        .iter()
        .chain(
            report
                .force_decomposition
                .components
                .iter()
                .map(|component| &component.contribution),
        )
        .collect()
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
