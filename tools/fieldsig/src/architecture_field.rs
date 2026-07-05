use crate::validation::{count_checks, generic_validation_example, validation_check};
use crate::{
    ARCHITECTURE_FIELD_SNAPSHOT_SCHEMA_VERSION,
    ARCHITECTURE_FIELD_SNAPSHOT_VALIDATION_REPORT_SCHEMA_VERSION, ArchitectureFieldSnapshotV0,
    ArchitectureFieldSnapshotValidationInput, ArchitectureFieldSnapshotValidationReportV0,
    ArchitectureFieldSnapshotValidationSummary, AttractorEngineeringSignalV0,
    DynamicsAggregationWindowV0, DynamicsArtifactRefV0, EXTRACTOR_VERSION, MeasurementBoundaryV0,
    OPERATION_PROPOSAL_LOG_SCHEMA_VERSION, OPERATION_PROPOSAL_LOG_VALIDATION_REPORT_SCHEMA_VERSION,
    OperationProposalEntryV0, OperationProposalLogV0, OperationProposalLogValidationInput,
    OperationProposalLogValidationReportV0, OperationProposalLogValidationSummary, RepositoryRef,
    ValidationCheck, ValidationExample,
};

const ALLOWED_SIGNAL_STATUSES: [&str; 9] = [
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

const ALLOWED_PROPOSAL_STATUSES: [&str; 8] = [
    "proposed",
    "accepted",
    "rejected",
    "projected",
    "deferred",
    "unmeasured",
    "private",
    "outOfScope",
];

const REQUIRED_FIELD_SNAPSHOT_NON_CONCLUSIONS: [&str; 3] = [
    "architecture field snapshot is selected-window tooling evidence, not global architecture field completeness",
    "selected field signals are not causal proof of future operation outcomes",
    "missing, private, and unmeasured field evidence is not measured zero",
];

const REQUIRED_PROPOSAL_LOG_NON_CONCLUSIONS: [&str; 3] = [
    "operation proposal log is selected-window tooling evidence, not AI proposal distribution completeness",
    "proposal support weights are finite log weights, not future operation distribution completeness",
    "missing, private, and unmeasured proposal evidence is not measured zero",
];

pub fn static_architecture_field_snapshot() -> ArchitectureFieldSnapshotV0 {
    let trajectory_ref = artifact_ref(
        "signature-trajectory-report",
        "tools/fieldsig/tests/fixtures/minimal/signature_trajectory_report.json",
        Some("signature-trajectory-report-v0"),
        Some("fixture-signature-trajectory-report-v0"),
    );
    let policy_ref = artifact_ref(
        "organization-policy",
        "tools/fieldsig/tests/fixtures/minimal/organization_policy.json",
        Some("organization-policy-v0"),
        Some("fixture-b7-organization-policy"),
    );
    let law_template_ref = artifact_ref(
        "law-policy-template-registry",
        "tools/fieldsig/tests/fixtures/minimal/law_policy_templates.json",
        Some("law-policy-template-registry-v0"),
        Some("fixture-law-policy-template-registry-v0"),
    );
    let measurement_unit_ref = artifact_ref(
        "measurement-unit-registry",
        "tools/fieldsig/tests/fixtures/minimal/measurement_units.json",
        Some("measurement-unit-registry-v0"),
        Some("fixture-measurement-unit-registry-v0"),
    );
    let window = selected_window();
    let source_refs = vec![
        trajectory_ref.clone(),
        policy_ref.clone(),
        law_template_ref.clone(),
        measurement_unit_ref.clone(),
    ];
    let boundary = boundary(
        "architecture-field-snapshot",
        &["DesignFieldStrength", "SeedAttractorStrength"],
        source_refs.clone(),
        Some(window.clone()),
        &[
            "field snapshot is retained only for the selected fixture window",
            "boundary, policy, law template, and measurement unit refs delimit the field evidence",
        ],
        &[
            "global architecture field completeness",
            "future operation distribution theorem",
        ],
        &REQUIRED_FIELD_SNAPSHOT_NON_CONCLUSIONS,
        ARCHITECTURE_FIELD_SNAPSHOT_SCHEMA_VERSION,
    );

    ArchitectureFieldSnapshotV0 {
        schema_version: ARCHITECTURE_FIELD_SNAPSHOT_SCHEMA_VERSION.to_string(),
        snapshot_id: "fixture-architecture-field-snapshot-v0".to_string(),
        repository: fixture_repository(),
        window: window.clone(),
        source_refs: source_refs.clone(),
        selected_context_refs: vec![
            "fixture:selected-dynamics-window".to_string(),
            "docs/design/attractor_engineering.md#aat-dynamics-mapping".to_string(),
        ],
        field_signals: vec![
            field_signal(
                "fixture:field-boundary-signal",
                "DesignFieldStrength",
                "boundary-and-non-goal-alignment",
                vec![policy_ref, law_template_ref],
                boundary.clone(),
                &[
                    "selected policy and law template refs are read as field-shaping context",
                    "signal is advisory because it does not sample the global architecture field",
                ],
                &[
                    "selected boundary alignment signal is not causal proof",
                    REQUIRED_FIELD_SNAPSHOT_NON_CONCLUSIONS[0],
                ],
            ),
            field_signal(
                "fixture:field-observability-signal",
                "DesignFieldStrength",
                "measurement-unit-and-trajectory-visibility",
                vec![trajectory_ref, measurement_unit_ref],
                boundary.clone(),
                &[
                    "measurement unit and trajectory refs delimit observed visibility",
                    "unobserved field context remains outside the selected fixture window",
                ],
                &[
                    "selected observability signal is not architecture field completeness",
                    REQUIRED_FIELD_SNAPSHOT_NON_CONCLUSIONS[2],
                ],
            ),
        ],
        measurement_boundary: boundary,
        non_conclusions: strings(&REQUIRED_FIELD_SNAPSHOT_NON_CONCLUSIONS),
    }
}

pub fn validate_architecture_field_snapshot(
    snapshot: &ArchitectureFieldSnapshotV0,
    input_path: &str,
) -> ArchitectureFieldSnapshotValidationReportV0 {
    let checks = vec![
        check_field_snapshot_schema_version(snapshot),
        check_field_snapshot_identity(snapshot),
        check_field_snapshot_boundaries(snapshot),
    ];
    let summary = ArchitectureFieldSnapshotValidationSummary {
        result: validation_result(&checks),
        field_signal_count: snapshot.field_signals.len(),
        source_ref_count: snapshot.source_refs.len(),
        selected_context_ref_count: snapshot.selected_context_refs.len(),
        failed_check_count: count_checks(&checks, "fail"),
        warning_check_count: count_checks(&checks, "warn"),
    };

    ArchitectureFieldSnapshotValidationReportV0 {
        schema_version: ARCHITECTURE_FIELD_SNAPSHOT_VALIDATION_REPORT_SCHEMA_VERSION.to_string(),
        input: ArchitectureFieldSnapshotValidationInput {
            schema_version: snapshot.schema_version.clone(),
            path: input_path.to_string(),
            snapshot_id: snapshot.snapshot_id.clone(),
            repository: format!("{}/{}", snapshot.repository.owner, snapshot.repository.name),
            window_kind: snapshot.window.window_kind.clone(),
        },
        snapshot: snapshot.clone(),
        summary,
        checks,
    }
}

pub fn static_operation_proposal_log() -> OperationProposalLogV0 {
    let pr_ref = artifact_ref(
        "github-pr",
        "tools/fieldsig/tests/fixtures/minimal/github_pr.json",
        None,
        Some("fixture-github-pr"),
    );
    let pr_force_ref = artifact_ref(
        "pr-force-report",
        "tools/fieldsig/tests/fixtures/minimal/pr_force_report.json",
        Some("pr-force-report-v0"),
        Some("fixture-pr-force-report-v0"),
    );
    let policy_ref = artifact_ref(
        "policy-decision-report",
        "tools/fieldsig/tests/fixtures/minimal/external/policy_decision_report.json",
        Some("policy-decision-report-v0"),
        Some("fixture-policy-decision-report"),
    );
    let window = selected_window();
    let source_refs = vec![pr_ref.clone(), pr_force_ref.clone(), policy_ref.clone()];
    let proposal_boundary = boundary(
        "operation-proposal-log",
        &[
            "FiniteOperationSupport",
            "ProposalStatus",
            "SupportRiskMass",
        ],
        source_refs.clone(),
        Some(window.clone()),
        &[
            "proposal log is retained only for the selected fixture window",
            "support weights are normalized over retained proposal entries",
        ],
        &[
            "AI proposal distribution completeness",
            "future operation distribution theorem",
        ],
        &REQUIRED_PROPOSAL_LOG_NON_CONCLUSIONS,
        OPERATION_PROPOSAL_LOG_SCHEMA_VERSION,
    );

    OperationProposalLogV0 {
        schema_version: OPERATION_PROPOSAL_LOG_SCHEMA_VERSION.to_string(),
        log_id: "fixture-operation-proposal-log-v0".to_string(),
        repository: fixture_repository(),
        window,
        source_refs: source_refs.clone(),
        proposals: vec![
            proposal_entry(
                "fixture:proposal-preserve-boundary",
                "boundary-preserving-refactor",
                "human-review",
                "accepted",
                Some(0.42),
                vec![pr_ref.clone(), pr_force_ref.clone()],
                proposal_boundary.clone(),
                &[
                    "accepted proposal is observed in retained PR force evidence",
                    "support weight is scoped to this finite fixture log",
                ],
                &[
                    REQUIRED_PROPOSAL_LOG_NON_CONCLUSIONS[1],
                    "accepted proposal support does not prove future safety",
                ],
            ),
            proposal_entry(
                "fixture:proposal-runtime-bypass",
                "runtime-bypass",
                "ai-session",
                "rejected",
                Some(0.08),
                vec![pr_ref.clone(), policy_ref.clone()],
                proposal_boundary.clone(),
                &[
                    "rejected proposal is retained as latent support evidence",
                    "rejection does not remove future proposal support",
                ],
                &[
                    REQUIRED_PROPOSAL_LOG_NON_CONCLUSIONS[0],
                    "rejected proposal evidence is not an AI behavior theorem",
                ],
            ),
            proposal_entry(
                "fixture:proposal-private-framework-convention",
                "framework-convention",
                "private-ai-session",
                "private",
                None,
                vec![policy_ref],
                proposal_boundary,
                &[
                    "private proposal source is retained as a boundary, not a zero-weight entry",
                    "operation semantics remain unmeasured for this proposal",
                ],
                &[
                    REQUIRED_PROPOSAL_LOG_NON_CONCLUSIONS[2],
                    "private proposal evidence is not zero latent support",
                ],
            ),
        ],
        measurement_boundary: boundary(
            "operation-proposal-log",
            &[
                "FiniteOperationSupport",
                "ProposalStatus",
                "SupportRiskMass",
            ],
            source_refs,
            Some(selected_window()),
            &[
                "proposal log is retained only for the selected fixture window",
                "support weights are normalized over retained proposal entries",
            ],
            &[
                "AI proposal distribution completeness",
                "future operation distribution theorem",
            ],
            &REQUIRED_PROPOSAL_LOG_NON_CONCLUSIONS,
            OPERATION_PROPOSAL_LOG_SCHEMA_VERSION,
        ),
        non_conclusions: strings(&REQUIRED_PROPOSAL_LOG_NON_CONCLUSIONS),
    }
}

pub fn validate_operation_proposal_log(
    log: &OperationProposalLogV0,
    input_path: &str,
) -> OperationProposalLogValidationReportV0 {
    let checks = vec![
        check_operation_proposal_log_schema_version(log),
        check_operation_proposal_log_identity(log),
        check_operation_proposal_log_boundaries(log),
    ];
    let summary = OperationProposalLogValidationSummary {
        result: validation_result(&checks),
        proposal_count: log.proposals.len(),
        source_ref_count: log.source_refs.len(),
        failed_check_count: count_checks(&checks, "fail"),
        warning_check_count: count_checks(&checks, "warn"),
    };

    OperationProposalLogValidationReportV0 {
        schema_version: OPERATION_PROPOSAL_LOG_VALIDATION_REPORT_SCHEMA_VERSION.to_string(),
        input: OperationProposalLogValidationInput {
            schema_version: log.schema_version.clone(),
            path: input_path.to_string(),
            log_id: log.log_id.clone(),
            repository: format!("{}/{}", log.repository.owner, log.repository.name),
            window_kind: log.window.window_kind.clone(),
        },
        log: log.clone(),
        summary,
        checks,
    }
}

fn field_signal(
    signal_id: &str,
    signal_kind: &str,
    selected_signal: &str,
    source_refs: Vec<DynamicsArtifactRefV0>,
    measurement_boundary: MeasurementBoundaryV0,
    assumptions: &[&str],
    non_conclusions: &[&str],
) -> AttractorEngineeringSignalV0 {
    AttractorEngineeringSignalV0 {
        signal_id: signal_id.to_string(),
        signal_kind: signal_kind.to_string(),
        selected_signal: selected_signal.to_string(),
        status: "advisory".to_string(),
        source_refs,
        confidence: Some("selected-window-fixture-signal".to_string()),
        measurement_boundary,
        assumptions: strings(assumptions),
        non_conclusions: strings(non_conclusions),
    }
}

#[allow(clippy::too_many_arguments)]
fn proposal_entry(
    proposal_id: &str,
    operation_kind: &str,
    source_kind: &str,
    status: &str,
    support_weight: Option<f64>,
    source_refs: Vec<DynamicsArtifactRefV0>,
    measurement_boundary: MeasurementBoundaryV0,
    assumptions: &[&str],
    non_conclusions: &[&str],
) -> OperationProposalEntryV0 {
    OperationProposalEntryV0 {
        proposal_id: proposal_id.to_string(),
        operation_kind: operation_kind.to_string(),
        source_kind: source_kind.to_string(),
        status: status.to_string(),
        support_weight,
        selected_region_refs: vec!["fixture:selected-safe-region".to_string()],
        source_refs,
        measurement_boundary,
        assumptions: strings(assumptions),
        non_conclusions: strings(non_conclusions),
    }
}

fn check_field_snapshot_schema_version(snapshot: &ArchitectureFieldSnapshotV0) -> ValidationCheck {
    let mut check = validation_check(
        "architecture-field-snapshot-schema-version-supported",
        "architecture-field-snapshot schema version is supported",
        if snapshot.schema_version == ARCHITECTURE_FIELD_SNAPSHOT_SCHEMA_VERSION {
            "pass"
        } else {
            "fail"
        },
    );
    if check.result == "fail" {
        check.reason = Some(format!(
            "unsupported architecture-field-snapshot schemaVersion: {}",
            snapshot.schema_version
        ));
    }
    check
}

fn check_field_snapshot_identity(snapshot: &ArchitectureFieldSnapshotV0) -> ValidationCheck {
    let mut invalid = Vec::new();
    validate_common_identity(
        &snapshot.snapshot_id,
        &snapshot.repository,
        &snapshot.window,
        &snapshot.source_refs,
        &snapshot.non_conclusions,
        &REQUIRED_FIELD_SNAPSHOT_NON_CONCLUSIONS,
        &mut invalid,
    );
    if snapshot.selected_context_refs.is_empty() || has_blank(&snapshot.selected_context_refs) {
        invalid.push(generic_validation_example(
            &snapshot.snapshot_id,
            "selectedContextRefs",
            "architecture field snapshot must record selected context refs",
        ));
    }
    if snapshot.field_signals.is_empty() {
        invalid.push(generic_validation_example(
            &snapshot.snapshot_id,
            "fieldSignals",
            "architecture field snapshot must record selected field signals",
        ));
    }
    check_examples(
        "architecture-field-snapshot-identity-recorded",
        "snapshot identity, source refs, selected window, context refs, and non-conclusions are recorded",
        invalid,
    )
}

fn check_field_snapshot_boundaries(snapshot: &ArchitectureFieldSnapshotV0) -> ValidationCheck {
    let mut invalid = Vec::new();
    validate_boundary(
        &snapshot.snapshot_id,
        "measurementBoundary",
        &snapshot.measurement_boundary,
        ARCHITECTURE_FIELD_SNAPSHOT_SCHEMA_VERSION,
        &REQUIRED_FIELD_SNAPSHOT_NON_CONCLUSIONS,
        &mut invalid,
    );
    for signal in &snapshot.field_signals {
        if signal.signal_id.trim().is_empty()
            || signal.signal_kind.trim().is_empty()
            || signal.selected_signal.trim().is_empty()
            || signal.source_refs.is_empty()
            || has_blank_artifact_refs(&signal.source_refs)
            || signal
                .confidence
                .as_deref()
                .unwrap_or_default()
                .trim()
                .is_empty()
            || signal.assumptions.is_empty()
            || has_blank(&signal.assumptions)
            || signal.non_conclusions.is_empty()
            || has_blank(&signal.non_conclusions)
        {
            invalid.push(generic_validation_example(
                &signal.signal_id,
                "fieldSignals",
                "field signals must record selected signal, source refs, confidence, assumptions, and non-conclusions",
            ));
        }
        if !ALLOWED_SIGNAL_STATUSES.contains(&signal.status.as_str()) {
            invalid.push(generic_validation_example(
                &signal.signal_id,
                &signal.status,
                "unsupported field signal MeasurementStatus",
            ));
        }
        validate_boundary(
            &signal.signal_id,
            "measurementBoundary",
            &signal.measurement_boundary,
            ARCHITECTURE_FIELD_SNAPSHOT_SCHEMA_VERSION,
            &REQUIRED_FIELD_SNAPSHOT_NON_CONCLUSIONS,
            &mut invalid,
        );
    }
    check_examples(
        "architecture-field-snapshot-boundaries-recorded",
        "source refs, selected window, measurement boundary, and non-conclusions are preserved",
        invalid,
    )
}

fn check_operation_proposal_log_schema_version(log: &OperationProposalLogV0) -> ValidationCheck {
    let mut check = validation_check(
        "operation-proposal-log-schema-version-supported",
        "operation-proposal-log schema version is supported",
        if log.schema_version == OPERATION_PROPOSAL_LOG_SCHEMA_VERSION {
            "pass"
        } else {
            "fail"
        },
    );
    if check.result == "fail" {
        check.reason = Some(format!(
            "unsupported operation-proposal-log schemaVersion: {}",
            log.schema_version
        ));
    }
    check
}

fn check_operation_proposal_log_identity(log: &OperationProposalLogV0) -> ValidationCheck {
    let mut invalid = Vec::new();
    validate_common_identity(
        &log.log_id,
        &log.repository,
        &log.window,
        &log.source_refs,
        &log.non_conclusions,
        &REQUIRED_PROPOSAL_LOG_NON_CONCLUSIONS,
        &mut invalid,
    );
    if log.proposals.is_empty() {
        invalid.push(generic_validation_example(
            &log.log_id,
            "proposals",
            "operation proposal log must retain proposal entries or explicit missing evidence boundary",
        ));
    }
    check_examples(
        "operation-proposal-log-identity-recorded",
        "log identity, source refs, selected window, proposals, and non-conclusions are recorded",
        invalid,
    )
}

fn check_operation_proposal_log_boundaries(log: &OperationProposalLogV0) -> ValidationCheck {
    let mut invalid = Vec::new();
    validate_boundary(
        &log.log_id,
        "measurementBoundary",
        &log.measurement_boundary,
        OPERATION_PROPOSAL_LOG_SCHEMA_VERSION,
        &REQUIRED_PROPOSAL_LOG_NON_CONCLUSIONS,
        &mut invalid,
    );
    for proposal in &log.proposals {
        if proposal.proposal_id.trim().is_empty()
            || proposal.operation_kind.trim().is_empty()
            || proposal.source_kind.trim().is_empty()
            || proposal.selected_region_refs.is_empty()
            || has_blank(&proposal.selected_region_refs)
            || proposal.source_refs.is_empty()
            || has_blank_artifact_refs(&proposal.source_refs)
            || proposal.assumptions.is_empty()
            || has_blank(&proposal.assumptions)
            || proposal.non_conclusions.is_empty()
            || has_blank(&proposal.non_conclusions)
        {
            invalid.push(generic_validation_example(
                &proposal.proposal_id,
                "proposals",
                "proposal entries must record operation kind, source kind, selected region refs, source refs, assumptions, and non-conclusions",
            ));
        }
        if !ALLOWED_PROPOSAL_STATUSES.contains(&proposal.status.as_str()) {
            invalid.push(generic_validation_example(
                &proposal.proposal_id,
                &proposal.status,
                "unsupported operation proposal status",
            ));
        }
        if let Some(weight) = proposal.support_weight {
            if !(0.0..=1.0).contains(&weight) {
                invalid.push(generic_validation_example(
                    &proposal.proposal_id,
                    "supportWeight",
                    "proposal support weight must be normalized between 0 and 1",
                ));
            }
        }
        if proposal.status == "private" && proposal.support_weight == Some(0.0) {
            invalid.push(generic_validation_example(
                &proposal.proposal_id,
                "supportWeight",
                "private proposal evidence must not be emitted as zero support",
            ));
        }
        validate_boundary(
            &proposal.proposal_id,
            "measurementBoundary",
            &proposal.measurement_boundary,
            OPERATION_PROPOSAL_LOG_SCHEMA_VERSION,
            &REQUIRED_PROPOSAL_LOG_NON_CONCLUSIONS,
            &mut invalid,
        );
    }
    check_examples(
        "operation-proposal-log-boundaries-recorded",
        "source refs, selected window, measurement boundary, support boundary, and non-conclusions are preserved",
        invalid,
    )
}

fn validate_common_identity(
    artifact_id: &str,
    repository: &RepositoryRef,
    window: &DynamicsAggregationWindowV0,
    source_refs: &[DynamicsArtifactRefV0],
    non_conclusions: &[String],
    required_non_conclusions: &[&str],
    invalid: &mut Vec<ValidationExample>,
) {
    if artifact_id.trim().is_empty() {
        invalid.push(generic_validation_example(
            "artifact",
            "id",
            "artifact id must be non-empty",
        ));
    }
    if repository.owner.trim().is_empty() || repository.name.trim().is_empty() {
        invalid.push(generic_validation_example(
            artifact_id,
            "repository",
            "repository owner and name must be non-empty",
        ));
    }
    if window.window_kind.trim().is_empty()
        || window
            .window_start
            .as_deref()
            .unwrap_or_default()
            .trim()
            .is_empty()
        || window
            .window_end
            .as_deref()
            .unwrap_or_default()
            .trim()
            .is_empty()
    {
        invalid.push(generic_validation_example(
            artifact_id,
            "window",
            "selected window start, end, and kind must be explicit",
        ));
    }
    if source_refs.is_empty() || has_blank_artifact_refs(source_refs) {
        invalid.push(generic_validation_example(
            artifact_id,
            "sourceRefs",
            "source refs must be explicit",
        ));
    }
    for required in required_non_conclusions {
        if !non_conclusions
            .iter()
            .any(|conclusion| conclusion == required)
        {
            invalid.push(generic_validation_example(
                artifact_id,
                "nonConclusions",
                &format!("missing required non-conclusion: {required}"),
            ));
        }
    }
}

fn validate_boundary(
    artifact_id: &str,
    field: &str,
    boundary: &MeasurementBoundaryV0,
    expected_schema_version: &str,
    required_non_conclusions: &[&str],
    invalid: &mut Vec<ValidationExample>,
) {
    if boundary.measured_layer.trim().is_empty()
        || boundary.measured_axes.is_empty()
        || has_blank(&boundary.measured_axes)
        || boundary.source_artifact_refs.is_empty()
        || has_blank_artifact_refs(&boundary.source_artifact_refs)
        || boundary.aggregation_window.is_none()
        || boundary.selected_region_refs.is_empty()
        || has_blank(&boundary.selected_region_refs)
        || boundary.assumptions.is_empty()
        || has_blank(&boundary.assumptions)
    {
        invalid.push(generic_validation_example(
            artifact_id,
            field,
            "measurement boundary must record layer, axes, source artifact refs, selected window, selected regions, and assumptions",
        ));
    }
    if boundary.schema_version.as_deref() != Some(expected_schema_version) {
        invalid.push(generic_validation_example(
            artifact_id,
            "measurementBoundary.schemaVersion",
            "measurement boundary schemaVersion must match the artifact schema",
        ));
    }
    for required in required_non_conclusions {
        if !boundary
            .non_conclusions
            .iter()
            .any(|conclusion| conclusion == required)
        {
            invalid.push(generic_validation_example(
                artifact_id,
                "measurementBoundary.nonConclusions",
                &format!("missing required boundary non-conclusion: {required}"),
            ));
        }
    }
}

fn boundary(
    measured_layer: &str,
    measured_axes: &[&str],
    source_artifact_refs: Vec<DynamicsArtifactRefV0>,
    aggregation_window: Option<DynamicsAggregationWindowV0>,
    assumptions: &[&str],
    unsupported_constructs: &[&str],
    non_conclusions: &[&str],
    schema_version: &str,
) -> MeasurementBoundaryV0 {
    MeasurementBoundaryV0 {
        measured_layer: measured_layer.to_string(),
        measured_axes: strings(measured_axes),
        source_artifact_refs,
        extractor_version: Some(EXTRACTOR_VERSION.to_string()),
        policy_version: Some("fixture-policy-v0".to_string()),
        schema_version: Some(schema_version.to_string()),
        aggregation_window,
        selected_region_refs: vec!["fixture:selected-safe-region".to_string()],
        assumptions: strings(assumptions),
        unsupported_constructs: strings(unsupported_constructs),
        missing_evidence: Vec::new(),
        non_conclusions: strings(non_conclusions),
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

fn selected_window() -> DynamicsAggregationWindowV0 {
    DynamicsAggregationWindowV0 {
        window_start: Some("2026-01-01T00:00:00Z".to_string()),
        window_end: Some("2026-01-31T23:59:59Z".to_string()),
        window_kind: "selected-fixture-window".to_string(),
    }
}

fn fixture_repository() -> RepositoryRef {
    RepositoryRef {
        owner: "iroha1203".to_string(),
        name: "AlgebraicArchitectureTheoryV2".to_string(),
        default_branch: "main".to_string(),
    }
}

fn check_examples(id: &str, title: &str, examples: Vec<ValidationExample>) -> ValidationCheck {
    let mut check = validation_check(id, title, if examples.is_empty() { "pass" } else { "fail" });
    if !examples.is_empty() {
        check.reason = Some(format!("{} invalid example(s)", examples.len()));
        check.count = Some(examples.len());
        check.examples = examples;
    }
    check
}

fn validation_result(checks: &[ValidationCheck]) -> String {
    if checks.iter().any(|check| check.result == "fail") {
        "fail".to_string()
    } else if checks.iter().any(|check| check.result == "warn") {
        "warn".to_string()
    } else {
        "pass".to_string()
    }
}

fn has_blank(values: &[String]) -> bool {
    values.iter().any(|value| value.trim().is_empty())
}

fn has_blank_artifact_refs(refs: &[DynamicsArtifactRefV0]) -> bool {
    refs.iter()
        .any(|reference| reference.kind.trim().is_empty() || reference.path.trim().is_empty())
}

fn strings(values: &[&str]) -> Vec<String> {
    values.iter().map(|value| (*value).to_string()).collect()
}
