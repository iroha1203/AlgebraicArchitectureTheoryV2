use std::collections::BTreeSet;

use serde_json::json;

use crate::validation::{count_checks, generic_validation_example, validation_check};
use crate::{
    ARCHITECTURE_DYNAMICS_METRICS_REPORT_SCHEMA_VERSION,
    ARCHITECTURE_DYNAMICS_METRICS_REPORT_VALIDATION_REPORT_SCHEMA_VERSION,
    ARCHITECTURE_FIELD_SNAPSHOT_SCHEMA_VERSION, ArchitectureDynamicsMetricsReportV0,
    ArchitectureDynamicsMetricsReportValidationInput,
    ArchitectureDynamicsMetricsReportValidationReportV0,
    ArchitectureDynamicsMetricsReportValidationSummary, AttractorEngineeringCandidateV0,
    AttractorEngineeringMetricsV0, AttractorEngineeringSignalV0, BasinPerturbationEvidenceV0,
    BasinSimulationClassificationV0, BasinSimulationInitialStateV0, BasinSimulationScriptV0,
    BasinSimulationV0, DynamicsAggregationWindowV0, DynamicsArtifactRefV0, DynamicsMeasuredValueV0,
    DynamicsMissingEvidenceV0, EXTRACTOR_VERSION, MeasurementBoundaryV0,
    OPERATION_PROPOSAL_LOG_SCHEMA_VERSION, ObservabilityAxisEvidenceV0,
    PR_FORCE_REPORT_SCHEMA_VERSION, RepositoryRef, SelectedSignatureRegionV0,
    SupportRiskMassEntryV0, TrajectoryReturnEvidenceV0, ValidationCheck, ValidationExample,
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
    "unmeasured, unavailable, private, notComparable, and outOfScope metrics are not measured zero",
    "Architecture Signature Dynamics is a multi-axis diagnostic, not a single score",
    "global attractor, causal proof, and incident-risk conclusions are out of scope",
];

const FORCE_CLASS_NON_CONCLUSION: &str =
    "ObservedForce, LatentForceEstimate, and DissipatedForceEstimate remain separate force classes";

const REQUIRED_ATTRACTOR_NON_CONCLUSIONS: [&str; 9] = [
    "attractorEngineering is bounded tooling evidence, not a global attractor theorem",
    "unmeasured, unavailable, private, notComparable, and outOfScope Attractor Engineering metrics are not measured zero",
    "attractor and basin candidates are selected-region candidates, not global convergence claims",
    "field shaping signals are empirical tooling signals, not causal proof",
    "Attractor Engineering tooling does not conclude incident reduction",
    "Attractor Engineering tooling does not conclude an AI behavior theorem",
    "DesignFieldStrength is a selected empirical signal, not a truth claim about the architecture field",
    "architecture field snapshot refs do not conclude global architecture field completeness",
    "operation proposal log refs do not conclude AI proposal distribution completeness",
];

const ALLOWED_ATTRACTOR_CANDIDATE_STATUSES: [&str; 7] = [
    "candidate",
    "nonCandidate",
    "missingEvidence",
    "unmeasured",
    "unavailable",
    "notComparable",
    "outOfScope",
];

const ALLOWED_SUPPORT_RISK_STATES: [&str; 9] = [
    "safePreservingProved",
    "safePreservingMeasured",
    "safePreservingEstimated",
    "unsafeWitnessMeasured",
    "unmeasured",
    "unavailable",
    "private",
    "notComparable",
    "outOfScope",
];

const ALLOWED_PRESERVATION_PRECONDITION_STATUSES: [&str; 8] = [
    "proved",
    "measured",
    "estimated",
    "unmeasured",
    "unavailable",
    "private",
    "notComparable",
    "outOfScope",
];

const UNKNOWN_SUPPORT_RISK_STATES: [&str; 5] = [
    "unmeasured",
    "unavailable",
    "private",
    "notComparable",
    "outOfScope",
];

const SUPPORT_RISK_HISTORY_NON_CONCLUSION: &str =
    "accepted PR history safety does not conclude future support risk is zero";

const BASIN_BOUNDARY_FRAGILITY_NON_CONCLUSION: &str =
    "BasinBoundaryFragility is bounded perturbation evidence, not global basin stability";
const TRAJECTORY_RETURN_TIME_NON_CONCLUSION: &str =
    "TrajectoryReturnTime is bounded observed return evidence, not a global recurrence theorem";
const OBSERVABILITY_DEBT_NON_CONCLUSION: &str =
    "unmeasured, private, and unavailable required axes are not zero ObservabilityDebt";
const FIELD_SHAPING_DELTA_NON_CONCLUSION: &str =
    "FieldShapingDelta is comparable only across matching measurement boundaries";
const VIBE_CODING_READINESS_NON_CONCLUSION: &str =
    "VibeCodingReadiness is multi-axis readiness, not a single numeric score";

const REQUIRED_VIBE_CODING_READINESS_AXES: [&str; 8] = [
    "DesignFieldStrength",
    "SeedAttractorStrength",
    "SupportRiskMass",
    "GoodAttractorBasinMass",
    "BasinBoundaryFragility",
    "TrajectoryReturnTime",
    "DampingToThroughputMargin",
    "ObservabilityDebt",
];

pub fn static_architecture_dynamics_metrics_report() -> ArchitectureDynamicsMetricsReportV0 {
    let pr_force_ref = artifact_ref(
        "pr-force-report",
        "tools/fieldsig/tests/fixtures/minimal/pr_force_report.json",
        Some(PR_FORCE_REPORT_SCHEMA_VERSION),
        Some("fixture-pr-force-report/v0.5.0"),
    );
    let trajectory_ref = artifact_ref(
        "signature-trajectory-report",
        "tools/fieldsig/tests/fixtures/minimal/signature_trajectory_report.json",
        Some("signature-trajectory-report/v0.5.0"),
        Some("fixture-signature-trajectory-report/v0.5.0"),
    );
    let drift_ref = artifact_ref(
        "architecture-drift-ledger",
        "tools/fieldsig/tests/fixtures/minimal/architecture_drift_ledger.json",
        Some("architecture-drift-ledger/v0.5.0"),
        Some("fixture-architecture-drift-ledger"),
    );
    let outcome_ref = artifact_ref(
        "outcome-linkage-dataset",
        "tools/fieldsig/tests/fixtures/minimal/external/outcome_linkage_dataset.json",
        Some("outcome-linkage-dataset/v0.5.0"),
        Some("fixture-outcome-linkage-dataset"),
    );
    let policy_ref = artifact_ref(
        "policy-decision-report",
        "tools/fieldsig/tests/fixtures/minimal/external/policy_decision_report.json",
        Some("policy-decision-report/v0.5.0"),
        Some("fixture-policy-decision-report"),
    );
    let ai_ref = artifact_ref(
        "ai-provenance-log",
        "tools/fieldsig/tests/fixtures/minimal/external/ai_provenance_log.json",
        None,
        Some("fixture-ai-provenance-log"),
    );
    let field_snapshot_ref = artifact_ref(
        "architecture-field-snapshot",
        "tools/fieldsig/tests/fixtures/minimal/architecture_field_snapshot.json",
        Some(ARCHITECTURE_FIELD_SNAPSHOT_SCHEMA_VERSION),
        Some("fixture-architecture-field-snapshot/v0.5.0"),
    );
    let proposal_log_ref = artifact_ref(
        "operation-proposal-log",
        "tools/fieldsig/tests/fixtures/minimal/operation_proposal_log.json",
        Some(OPERATION_PROPOSAL_LOG_SCHEMA_VERSION),
        Some("fixture-operation-proposal-log/v0.5.0"),
    );
    let canonical_example_ref = artifact_ref(
        "canonical-example-ref",
        "tools/fieldsig/tests/fixtures/minimal/architecture_field_snapshot.json#canonicalExamples",
        Some(ARCHITECTURE_FIELD_SNAPSHOT_SCHEMA_VERSION),
        Some("fixture-canonical-example-refs"),
    );
    let patch_similarity_ref = artifact_ref(
        "patch-similarity-evidence",
        "tools/fieldsig/tests/fixtures/minimal/operation_proposal_log.json#patchSimilarityEvidence",
        Some(OPERATION_PROPOSAL_LOG_SCHEMA_VERSION),
        Some("fixture-patch-similarity-evidence"),
    );

    let window = DynamicsAggregationWindowV0 {
        window_start: Some("2026-01-01T00:00:00Z".to_string()),
        window_end: Some("2026-01-31T23:59:59Z".to_string()),
        window_kind: "selected-fixture-window".to_string(),
    };

    ArchitectureDynamicsMetricsReportV0 {
        schema_version: ARCHITECTURE_DYNAMICS_METRICS_REPORT_SCHEMA_VERSION.to_string(),
        report_id: "fixture-architecture-dynamics-metrics-report/v0.5.0".to_string(),
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
            field_snapshot_ref.clone(),
            proposal_log_ref.clone(),
            canonical_example_ref.clone(),
            patch_similarity_ref.clone(),
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
                vec![proposal_log_ref.clone()],
                gap_boundary(
                    "operation proposal log is retained but latent force estimation is not implemented",
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
                "advisory",
                None,
                vec![field_snapshot_ref.clone()],
                boundary(
                    "architecture-field-snapshot",
                    &["DesignFieldStrength"],
                    vec![field_snapshot_ref.clone()],
                    Some(window.clone()),
                    &["architecture field snapshot is retained as selected-window tooling input"],
                    &["global architecture field completeness"],
                ),
                &["field snapshot artifact is retained as advisory DesignFieldStrength input"],
                &[
                    "advisory DesignFieldStrength is not causal proof",
                    "architecture field snapshot refs do not conclude global architecture field completeness",
                ],
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
        attractor_engineering: Some(attractor_engineering_section(
            window.clone(),
            vec![
                trajectory_ref.clone(),
                pr_force_ref.clone(),
                drift_ref.clone(),
                field_snapshot_ref.clone(),
                proposal_log_ref.clone(),
            ],
            canonical_example_ref.clone(),
            patch_similarity_ref.clone(),
        )),
        measurement_boundary: MeasurementBoundaryV0 {
            measured_layer: "architecture-dynamics".to_string(),
            measured_axes: vec![
                "trajectory".to_string(),
                "force".to_string(),
                "gap".to_string(),
                "fieldControl".to_string(),
                "aiDynamics".to_string(),
                "attractorEngineering".to_string(),
            ],
            source_artifact_refs: vec![
                pr_force_ref,
                trajectory_ref,
                drift_ref,
                outcome_ref,
                policy_ref,
                ai_ref,
                field_snapshot_ref,
                proposal_log_ref,
            ],
            extractor_version: Some(EXTRACTOR_VERSION.to_string()),
            policy_version: Some("fixture-policy/v0.5.0".to_string()),
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
                    "proposal log is retained as a boundary but latent force calculator is not implemented",
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
        check_attractor_engineering_section(report),
    ];
    let attractor_selected_region_count = report
        .attractor_engineering
        .as_ref()
        .map(|section| section.selected_regions.len())
        .unwrap_or(0);
    let attractor_candidate_count = report
        .attractor_engineering
        .as_ref()
        .map(|section| section.attractor_candidates.len())
        .unwrap_or(0);
    let basin_candidate_count = report
        .attractor_engineering
        .as_ref()
        .map(|section| section.basin_candidates.len())
        .unwrap_or(0);
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
        attractor_selected_region_count,
        attractor_candidate_count,
        basin_candidate_count,
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

fn attractor_engineering_section(
    window: DynamicsAggregationWindowV0,
    source_refs: Vec<DynamicsArtifactRefV0>,
    canonical_example_ref: DynamicsArtifactRefV0,
    patch_similarity_ref: DynamicsArtifactRefV0,
) -> AttractorEngineeringMetricsV0 {
    let mut seed_source_refs = source_refs.clone();
    seed_source_refs.push(canonical_example_ref);
    seed_source_refs.push(patch_similarity_ref);
    let section_boundary = boundary(
        "attractor-engineering",
        &[
            "SupportRiskMass",
            "DesignFieldStrength",
            "SeedAttractorStrength",
            "GoodAttractorBasinMass",
            "BasinBoundaryFragility",
            "TrajectoryReturnTime",
            "DampingToThroughputMargin",
            "ObservabilityDebt",
        ],
        source_refs.clone(),
        Some(window.clone()),
        &[
            "Attractor Engineering is evaluated only for the selected fixture window",
            "candidate regions are selected finite observations, not global state-space partitions",
        ],
        &[
            "global attractor theorem",
            "complete basin decomposition",
            "future operation distribution completeness",
        ],
    );
    let support_risk_entries = support_risk_entries(section_boundary.clone());
    let support_risk_mass = support_risk_mass_metric(
        &support_risk_entries,
        source_refs.clone(),
        section_boundary.clone(),
    );
    let basin_simulations = vec![bounded_basin_simulation(
        window.clone(),
        source_refs.clone(),
        section_boundary.clone(),
    )];
    AttractorEngineeringMetricsV0 {
        selected_regions: vec![SelectedSignatureRegionV0 {
            region_id: "fixture:selected-safe-region".to_string(),
            region_kind: "safe-target-region".to_string(),
            defining_axes: vec![
                "boundaryViolation".to_string(),
                "runtimePropagation".to_string(),
            ],
            bounds: json!({
                "boundaryViolation": {"max": 0},
                "runtimePropagation": {"max": 0}
            }),
            trajectory_point_refs: vec!["trajectory:point:end".to_string()],
            measurement_boundary: section_boundary.clone(),
            non_conclusions: strings(&[
                "selected safe region does not classify the global state space",
                "endpoint membership does not prove path safety",
            ]),
        }],
        attractor_candidates: vec![attractor_candidate(
            "fixture:good-attractor-candidate",
            "good-attractor-candidate",
            "candidate",
            &["fixture:selected-safe-region"],
            &[
                "attractorEngineering.designFieldStrength",
                "attractorEngineering.seedAttractorStrength",
            ],
            section_boundary.clone(),
            &[
                "candidate is retained for bounded tooling validation",
                "seed examples are treated as evidence boundaries, not convergence proof",
            ],
            &[
                "candidate attractor status is not a global attractor theorem",
                "seed attractor evidence does not imply future patch convergence",
            ],
        )],
        basin_candidates: vec![
            attractor_candidate(
                "fixture:bounded-basin-candidate",
                "basin-candidate",
                "candidate",
                &["fixture:selected-safe-region"],
                &[
                    "attractorEngineering.basinBoundaryFragility",
                    "attractorEngineering.trajectoryReturnTime",
                ],
                section_boundary.clone(),
                &[
                    "candidate is scoped to the selected fixture window",
                    "basin membership is derived from fixture:bounded-basin-simulation",
                ],
                &[
                    "bounded basin candidate is not a global basin theorem",
                    "basin candidate status does not prove reachability for all states",
                ],
            ),
            attractor_candidate(
                "fixture:bounded-non-candidate-basin-entry",
                "basin-candidate",
                "nonCandidate",
                &["fixture:selected-safe-region"],
                &[
                    "attractorEngineering.basinBoundaryFragility",
                    "attractorEngineering.trajectoryReturnTime",
                ],
                section_boundary.clone(),
                &[
                    "selected initial state reaches a bad region or fails to return within the bounded horizon",
                    "non-candidate classification is local to fixture:bounded-basin-simulation",
                ],
                &[
                    "non-candidate basin entry is not a global non-reachability theorem",
                    "bounded simulation failure does not prove impossible repair",
                ],
            ),
            attractor_candidate(
                "fixture:missing-evidence-basin-candidate",
                "basin-candidate",
                "missingEvidence",
                &["fixture:selected-safe-region"],
                &[
                    "attractorEngineering.basinBoundaryFragility",
                    "attractorEngineering.trajectoryReturnTime",
                ],
                gap_boundary(
                    "basin membership simulation is not implemented in the MVP fixture",
                    "unmeasured",
                ),
                &["basin candidate awaits bounded simulation evidence"],
                &[
                    "unmeasured basin candidate is not empty basin evidence",
                    "basin candidate status does not prove reachability",
                ],
            ),
        ],
        basin_simulations: basin_simulations.clone(),
        support_risk_entries,
        design_field_signals: vec![
            attractor_signal(
                "fixture:design-field-boundary-signal",
                "DesignFieldStrength",
                "boundary-and-non-goal-alignment",
                source_refs.clone(),
                "advisory",
                Some("bounded-fixture-signal"),
                section_boundary.clone(),
                &[
                    "boundary, ownership, test, and non-goal refs are read as selected field-shaping signal inputs",
                    "signal is evaluated only for the selected fixture window",
                ],
                &[
                    "selected DesignFieldStrength signal is not a causal proof",
                    "DesignFieldStrength is a selected empirical signal, not a truth claim about the architecture field",
                    "architecture field snapshot refs do not conclude global architecture field completeness",
                ],
            ),
            attractor_signal(
                "fixture:design-field-observability-signal",
                "DesignFieldStrength",
                "test-and-observability-support",
                source_refs.clone(),
                "advisory",
                Some("bounded-fixture-signal"),
                section_boundary.clone(),
                &[
                    "test and observability context is retained as a selected signal, not a complete field snapshot",
                    "signal source refs delimit the measured boundary",
                ],
                &[
                    "selected DesignFieldStrength signal is not a causal proof",
                    "DesignFieldStrength is a selected empirical signal, not a truth claim about the architecture field",
                    "architecture field snapshot refs do not conclude global architecture field completeness",
                ],
            ),
        ],
        seed_attractor_signals: vec![attractor_signal(
            "fixture:seed-attractor-canonical-example-signal",
            "SeedAttractorStrength",
            "canonical-example-copyability",
            seed_source_refs.clone(),
            "advisory",
            Some("bounded-fixture-signal"),
            section_boundary.clone(),
            &[
                "canonical example refs and patch similarity evidence are retained for the selected window",
                "copyability signal is not promoted to future patch convergence",
            ],
            &[
                "selected SeedAttractorStrength signal is not a convergence theorem",
                "seed attractor signal does not prove future patch distribution completeness",
                "operation proposal log refs do not conclude AI proposal distribution completeness",
            ],
        )],
        support_risk_mass,
        design_field_strength: metric(
            "attractorEngineering.designFieldStrength",
            Some(json!({
                "protocol": "selected-design-field-signal-pilot",
                "selectedSignalIds": [
                    "fixture:design-field-boundary-signal",
                    "fixture:design-field-observability-signal"
                ],
                "sourceRefKinds": [
                    "architecture-field-snapshot",
                    "operation-proposal-log"
                ]
            })),
            "advisory",
            Some("bounded-fixture-signal"),
            source_refs.clone(),
            section_boundary.clone(),
            &["DesignFieldStrength reads selected field snapshot refs as advisory tooling input"],
            &[
                "advisory DesignFieldStrength is not causal proof",
                "DesignFieldStrength is a selected empirical signal, not a truth claim about the architecture field",
                "architecture field snapshot refs do not conclude global architecture field completeness",
            ],
        ),
        seed_attractor_strength: metric(
            "attractorEngineering.seedAttractorStrength",
            Some(json!({
                "protocol": "selected-seed-attractor-pilot",
                "selectedSignalIds": ["fixture:seed-attractor-canonical-example-signal"],
                "sourceRefKinds": [
                    "canonical-example-ref",
                    "patch-similarity-evidence"
                ]
            })),
            "advisory",
            Some("bounded-fixture-signal"),
            seed_source_refs.clone(),
            boundary(
                "attractor-engineering",
                &["SeedAttractorStrength"],
                seed_source_refs.clone(),
                Some(window.clone()),
                &[
                    "canonical example refs and patch similarity evidence are retained as selected pilot inputs",
                ],
                &[
                    "seed attractor convergence theorem",
                    "future patch distribution completeness",
                ],
            ),
            &[
                "SeedAttractorStrength reads selected canonical example refs and patch similarity evidence",
            ],
            &[
                "selected SeedAttractorStrength signal is not a convergence theorem",
                "SeedAttractorStrength pilot evidence is not a future patch distribution claim",
            ],
        ),
        field_shaping_delta: metric(
            "attractorEngineering.fieldShapingDelta",
            Some(json!({
                "comparisonStatus": "notComparable",
                "supportRiskMassDelta": null,
                "goodAttractorBasinMassDelta": null,
                "seedAttractorStrengthDelta": null
            })),
            "notComparable",
            None,
            source_refs.clone(),
            gap_boundary(
                "field update before/after windows do not share comparable measurement boundaries in the MVP fixture",
                "notComparable",
            ),
            &[
                "FieldShapingDelta compares SupportRiskMass, GoodAttractorBasinMass, and SeedAttractorStrength only across comparable before/after boundaries",
            ],
            &[
                "notComparable FieldShapingDelta is not zero field shaping effect",
                FIELD_SHAPING_DELTA_NON_CONCLUSION,
            ],
        ),
        vibe_coding_readiness_axes: vec![
            readiness_axis(
                &section_boundary,
                "DesignFieldStrength",
                "advisory",
                Some("bounded-fixture-signal"),
                source_refs.clone(),
                &[
                    "DesignFieldStrength contributes one readiness axis and is not aggregated into a score",
                ],
                &[
                    VIBE_CODING_READINESS_NON_CONCLUSION,
                    "DesignFieldStrength readiness is not a causal truth claim",
                ],
            ),
            readiness_axis(
                &section_boundary,
                "SeedAttractorStrength",
                "advisory",
                Some("bounded-fixture-signal"),
                seed_source_refs.clone(),
                &["SeedAttractorStrength is read from selected canonical-example signal refs"],
                &[
                    VIBE_CODING_READINESS_NON_CONCLUSION,
                    "seed readiness does not prove future patch convergence",
                ],
            ),
            readiness_axis(
                &section_boundary,
                "SupportRiskMass",
                "unmeasured",
                None,
                Vec::new(),
                &["SupportRiskMass readiness awaits finite operation support weights"],
                &[
                    VIBE_CODING_READINESS_NON_CONCLUSION,
                    "unmeasured support risk readiness is not low risk evidence",
                ],
            ),
            readiness_axis(
                &section_boundary,
                "GoodAttractorBasinMass",
                "notComparable",
                None,
                Vec::new(),
                &["GoodAttractorBasinMass readiness needs comparable bounded basin simulation"],
                &[
                    VIBE_CODING_READINESS_NON_CONCLUSION,
                    "notComparable basin mass readiness is not zero basin mass",
                ],
            ),
            readiness_axis(
                &section_boundary,
                "BasinBoundaryFragility",
                "unmeasured",
                None,
                Vec::new(),
                &["BasinBoundaryFragility readiness needs bounded perturbation simulation"],
                &[
                    VIBE_CODING_READINESS_NON_CONCLUSION,
                    BASIN_BOUNDARY_FRAGILITY_NON_CONCLUSION,
                ],
            ),
            readiness_axis(
                &section_boundary,
                "TrajectoryReturnTime",
                "unavailable",
                None,
                Vec::new(),
                &["TrajectoryReturnTime readiness needs selected excursion and return evidence"],
                &[
                    VIBE_CODING_READINESS_NON_CONCLUSION,
                    TRAJECTORY_RETURN_TIME_NON_CONCLUSION,
                ],
            ),
            readiness_axis(
                &section_boundary,
                "DampingToThroughputMargin",
                "outOfScope",
                None,
                Vec::new(),
                &[
                    "DampingToThroughputMargin is reserved for future proposal throughput and damping evidence",
                ],
                &[
                    VIBE_CODING_READINESS_NON_CONCLUSION,
                    "outOfScope damping margin is not zero throughput risk",
                ],
            ),
            readiness_axis(
                &section_boundary,
                "ObservabilityDebt",
                "notComparable",
                None,
                Vec::new(),
                &["ObservabilityDebt readiness needs comparable observed and latent support axes"],
                &[
                    VIBE_CODING_READINESS_NON_CONCLUSION,
                    OBSERVABILITY_DEBT_NON_CONCLUSION,
                ],
            ),
        ],
        basin_boundary_fragility: metric(
            "attractorEngineering.basinBoundaryFragility",
            Some(calculate_basin_boundary_fragility(&basin_simulations)),
            "derived",
            Some("bounded-fixture-simulation"),
            source_refs.clone(),
            section_boundary.clone(),
            &[
                "BasinBoundaryFragility is derived from selected 1-step / k-step perturbation evidence",
            ],
            &[
                "derived BasinBoundaryFragility is selected bounded evidence only",
                BASIN_BOUNDARY_FRAGILITY_NON_CONCLUSION,
            ],
        ),
        trajectory_return_time: metric(
            "attractorEngineering.trajectoryReturnTime",
            Some(calculate_trajectory_return_time(&basin_simulations)),
            "derived",
            Some("bounded-fixture-simulation"),
            source_refs.clone(),
            section_boundary.clone(),
            &[
                "TrajectoryReturnTime is derived from selected excursion and return evidence within the bounded horizon",
            ],
            &[
                "derived TrajectoryReturnTime keeps missing and non-returning evidence separate",
                TRAJECTORY_RETURN_TIME_NON_CONCLUSION,
            ],
        ),
        observability_debt: metric(
            "attractorEngineering.observabilityDebt",
            Some(calculate_observability_debt(&basin_simulations)),
            "derived",
            Some("bounded-fixture-simulation"),
            source_refs.clone(),
            section_boundary.clone(),
            &["ObservabilityDebt is derived from required axis evidence in the bounded fixture"],
            &[
                "derived ObservabilityDebt preserves unmeasured, private, and unavailable axis mass",
                OBSERVABILITY_DEBT_NON_CONCLUSION,
            ],
        ),
        measurement_boundary: section_boundary,
        non_conclusions: strings(&REQUIRED_ATTRACTOR_NON_CONCLUSIONS),
    }
}

fn bounded_basin_simulation(
    window: DynamicsAggregationWindowV0,
    source_refs: Vec<DynamicsArtifactRefV0>,
    section_boundary: MeasurementBoundaryV0,
) -> BasinSimulationV0 {
    let simulation_boundary = boundary(
        "attractor-engineering-basin-simulation",
        &[
            "selectedInitialStates",
            "finiteOperationScripts",
            "selectedRegions",
            "boundedHorizon",
            "BasinBoundaryFragility",
            "TrajectoryReturnTime",
            "ObservabilityDebt",
        ],
        source_refs.clone(),
        Some(window),
        &[
            "simulation is evaluated over selected fixture initial states and scripts only",
            "bounded horizon is finite and does not classify the global state space",
        ],
        &[
            "global basin stability",
            "global recurrence theorem",
            "complete operation distribution",
        ],
    );

    BasinSimulationV0 {
        simulation_id: "fixture:bounded-basin-simulation".to_string(),
        bounded_horizon: 4,
        selected_initial_states: vec![
            basin_initial_state(
                "fixture:state:clean-boundary",
                "selected-initial-state",
                0.5,
                "measured",
                &["fixture:selected-safe-region"],
                Vec::new(),
                section_boundary.clone(),
            ),
            basin_initial_state(
                "fixture:state:runtime-bypass",
                "selected-initial-state",
                0.3,
                "measured",
                &["fixture:selected-safe-region"],
                Vec::new(),
                section_boundary.clone(),
            ),
            basin_initial_state(
                "fixture:state:private-axis",
                "selected-initial-state",
                0.2,
                "private",
                &["fixture:selected-safe-region"],
                vec![missing_evidence(
                    "selected-initial-state-axis",
                    "private axis prevents bounded basin classification for this state",
                    "private",
                )],
                section_boundary.clone(),
            ),
        ],
        operation_scripts: vec![
            basin_script(
                "fixture:script:repair-to-safe",
                &[
                    "fixture:preserve-boundary-law",
                    "fixture:measured-policy-cleanup",
                ],
                2,
                source_refs.clone(),
                section_boundary.clone(),
            ),
            basin_script(
                "fixture:script:runtime-bypass",
                &["fixture:unsafe-runtime-bypass"],
                1,
                source_refs.clone(),
                section_boundary.clone(),
            ),
        ],
        basin_classifications: vec![
            basin_classification(
                "fixture:state:clean-boundary",
                "fixture:script:repair-to-safe",
                "candidate",
                Some("fixture:selected-safe-region"),
                Some(2),
                "measured",
                Vec::new(),
                &[
                    "selected script reaches the selected safe region within the bounded horizon",
                ],
                &[
                    "candidate classification is bounded simulation evidence only",
                    "candidate classification is not a global basin theorem",
                ],
            ),
            basin_classification(
                "fixture:state:runtime-bypass",
                "fixture:script:runtime-bypass",
                "nonCandidate",
                None,
                None,
                "measured",
                Vec::new(),
                &[
                    "selected script enters the bad runtime bypass region and has no retained return within the bounded horizon",
                ],
                &[
                    "non-candidate classification is not a global non-reachability theorem",
                    "bounded non-return does not prove impossible repair",
                ],
            ),
            basin_classification(
                "fixture:state:private-axis",
                "fixture:script:repair-to-safe",
                "missingEvidence",
                None,
                None,
                "private",
                vec![missing_evidence(
                    "selected-initial-state-axis",
                    "private axis prevents classifying this selected state as candidate or non-candidate",
                    "private",
                )],
                &["private axis evidence is retained as missing evidence"],
                &[
                    "missing-evidence classification is not empty basin evidence",
                    "private required axes are not measured zero",
                ],
            ),
        ],
        perturbation_evidence: vec![
            basin_perturbation(
                "fixture:perturbation:stable-clean-boundary",
                "fixture:state:clean-boundary",
                "one-step-preserving-operation",
                1,
                "candidate",
                "candidate",
                "measured",
                source_refs.clone(),
                section_boundary.clone(),
            ),
            basin_perturbation(
                "fixture:perturbation:runtime-bypass-flip",
                "fixture:state:runtime-bypass",
                "one-step-runtime-bypass",
                1,
                "candidate",
                "nonCandidate",
                "measured",
                source_refs.clone(),
                section_boundary.clone(),
            ),
            basin_perturbation(
                "fixture:perturbation:private-axis-missing",
                "fixture:state:private-axis",
                "private-axis-perturbation",
                1,
                "missingEvidence",
                "missingEvidence",
                "private",
                Vec::new(),
                gap_boundary(
                    "private perturbation axis is unavailable for bounded fragility classification",
                    "private",
                ),
            ),
        ],
        return_evidence: vec![
            trajectory_return_evidence(
                "fixture:return:clean-boundary",
                "fixture:state:clean-boundary",
                "fixture:selected-bad-runtime-region",
                "fixture:selected-safe-region",
                Some(2),
                "measured",
                Vec::new(),
                source_refs.clone(),
                section_boundary.clone(),
            ),
            trajectory_return_evidence(
                "fixture:return:runtime-bypass",
                "fixture:state:runtime-bypass",
                "fixture:selected-bad-runtime-region",
                "fixture:selected-safe-region",
                None,
                "unavailable",
                vec![missing_evidence(
                    "bounded-return-observation",
                    "no return observation is retained before the bounded horizon",
                    "unavailable",
                )],
                source_refs.clone(),
                section_boundary.clone(),
            ),
            trajectory_return_evidence(
                "fixture:return:private-axis",
                "fixture:state:private-axis",
                "fixture:selected-bad-runtime-region",
                "fixture:selected-safe-region",
                None,
                "private",
                vec![missing_evidence(
                    "bounded-return-observation",
                    "private axis hides the selected return observation",
                    "private",
                )],
                Vec::new(),
                gap_boundary(
                    "private return observation is not retained in this fixture",
                    "private",
                ),
            ),
        ],
        observability_axes: vec![
            observability_axis(
                "boundaryViolation",
                0.4,
                "measured",
                source_refs.clone(),
                section_boundary.clone(),
            ),
            observability_axis(
                "runtimePropagation",
                0.3,
                "measured",
                source_refs.clone(),
                section_boundary.clone(),
            ),
            observability_axis(
                "latentFrameworkConvention",
                0.15,
                "unmeasured",
                Vec::new(),
                section_boundary.clone(),
            ),
            observability_axis(
                "privateReviewContext",
                0.1,
                "private",
                Vec::new(),
                section_boundary.clone(),
            ),
            observability_axis(
                "unavailableRuntimeTrace",
                0.05,
                "unavailable",
                Vec::new(),
                section_boundary.clone(),
            ),
        ],
        source_refs,
        measurement_boundary: simulation_boundary,
        assumptions: vec![
            "selected initial states, finite scripts, selected regions, and bounded horizon are fixture inputs".to_string(),
            "simulation output is bounded tooling evidence and may be incomplete".to_string(),
        ],
        non_conclusions: vec![
            "bounded basin simulation does not prove global basin stability".to_string(),
            "bounded return evidence does not prove global recurrence".to_string(),
            "missing, private, and unavailable simulation axes are not measured zero".to_string(),
        ],
    }
}

fn basin_initial_state(
    state_id: &str,
    state_kind: &str,
    state_weight: f64,
    evidence_status: &str,
    region_refs: &[&str],
    missing_evidence: Vec<DynamicsMissingEvidenceV0>,
    measurement_boundary: MeasurementBoundaryV0,
) -> BasinSimulationInitialStateV0 {
    BasinSimulationInitialStateV0 {
        state_id: state_id.to_string(),
        state_kind: state_kind.to_string(),
        state_weight: metric(
            &format!("{state_id}.stateWeight"),
            Some(json!(state_weight)),
            "measured",
            Some("bounded-fixture-state-weight"),
            Vec::new(),
            measurement_boundary,
            &["state weight is normalized over selected fixture initial states"],
            &["selected initial-state weight is not global state-space mass"],
        ),
        region_refs: strings(region_refs),
        evidence_status: evidence_status.to_string(),
        missing_evidence,
    }
}

fn basin_script(
    script_id: &str,
    operation_ids: &[&str],
    bounded_horizon: usize,
    source_refs: Vec<DynamicsArtifactRefV0>,
    measurement_boundary: MeasurementBoundaryV0,
) -> BasinSimulationScriptV0 {
    BasinSimulationScriptV0 {
        script_id: script_id.to_string(),
        operation_ids: strings(operation_ids),
        bounded_horizon,
        source_refs,
        measurement_boundary,
        assumptions: vec![
            "script is finite and evaluated only within the selected bounded horizon".to_string(),
        ],
        non_conclusions: vec![
            "finite script evidence does not describe complete future operation support"
                .to_string(),
        ],
    }
}

#[allow(clippy::too_many_arguments)]
fn basin_classification(
    state_id: &str,
    script_id: &str,
    classification: &str,
    target_region_ref: Option<&str>,
    steps_to_target: Option<usize>,
    status: &str,
    missing_evidence: Vec<DynamicsMissingEvidenceV0>,
    assumptions: &[&str],
    non_conclusions: &[&str],
) -> BasinSimulationClassificationV0 {
    BasinSimulationClassificationV0 {
        state_id: state_id.to_string(),
        script_id: script_id.to_string(),
        classification: classification.to_string(),
        target_region_ref: target_region_ref.map(str::to_string),
        steps_to_target,
        status: status.to_string(),
        missing_evidence,
        assumptions: strings(assumptions),
        non_conclusions: strings(non_conclusions),
    }
}

#[allow(clippy::too_many_arguments)]
fn basin_perturbation(
    evidence_id: &str,
    source_state_id: &str,
    perturbation_kind: &str,
    perturbation_steps: usize,
    baseline_classification: &str,
    perturbed_classification: &str,
    status: &str,
    source_refs: Vec<DynamicsArtifactRefV0>,
    measurement_boundary: MeasurementBoundaryV0,
) -> BasinPerturbationEvidenceV0 {
    BasinPerturbationEvidenceV0 {
        evidence_id: evidence_id.to_string(),
        source_state_id: source_state_id.to_string(),
        perturbation_kind: perturbation_kind.to_string(),
        perturbation_steps,
        baseline_classification: baseline_classification.to_string(),
        perturbed_classification: perturbed_classification.to_string(),
        status: status.to_string(),
        source_refs,
        measurement_boundary,
        assumptions: vec![
            "perturbation evidence is evaluated against the selected bounded basin classification"
                .to_string(),
        ],
        non_conclusions: vec![BASIN_BOUNDARY_FRAGILITY_NON_CONCLUSION.to_string()],
    }
}

#[allow(clippy::too_many_arguments)]
fn trajectory_return_evidence(
    evidence_id: &str,
    state_id: &str,
    excursion_region_ref: &str,
    return_region_ref: &str,
    steps_to_return: Option<usize>,
    status: &str,
    missing_evidence: Vec<DynamicsMissingEvidenceV0>,
    source_refs: Vec<DynamicsArtifactRefV0>,
    measurement_boundary: MeasurementBoundaryV0,
) -> TrajectoryReturnEvidenceV0 {
    TrajectoryReturnEvidenceV0 {
        evidence_id: evidence_id.to_string(),
        state_id: state_id.to_string(),
        excursion_region_ref: excursion_region_ref.to_string(),
        return_region_ref: return_region_ref.to_string(),
        steps_to_return,
        status: status.to_string(),
        missing_evidence,
        source_refs,
        measurement_boundary,
        assumptions: vec![
            "return evidence is bounded by the selected trajectory window and horizon".to_string(),
        ],
        non_conclusions: vec![TRAJECTORY_RETURN_TIME_NON_CONCLUSION.to_string()],
    }
}

fn observability_axis(
    axis_id: &str,
    required_weight: f64,
    evidence_status: &str,
    source_refs: Vec<DynamicsArtifactRefV0>,
    measurement_boundary: MeasurementBoundaryV0,
) -> ObservabilityAxisEvidenceV0 {
    ObservabilityAxisEvidenceV0 {
        axis_id: axis_id.to_string(),
        required_weight: metric(
            &format!("attractorEngineering.observabilityDebt.{axis_id}.requiredWeight"),
            Some(json!(required_weight)),
            "measured",
            Some("bounded-fixture-required-axis-weight"),
            Vec::new(),
            measurement_boundary.clone(),
            &["required axis weight is normalized over fixture observability requirements"],
            &[OBSERVABILITY_DEBT_NON_CONCLUSION],
        ),
        evidence_status: evidence_status.to_string(),
        source_refs,
        measurement_boundary,
        assumptions: vec![
            "axis status records whether a required basin simulation axis is observable"
                .to_string(),
        ],
        non_conclusions: vec![OBSERVABILITY_DEBT_NON_CONCLUSION.to_string()],
    }
}

fn support_risk_entries(section_boundary: MeasurementBoundaryV0) -> Vec<SupportRiskMassEntryV0> {
    vec![
        support_risk_entry(
            "fixture:preserve-boundary-law",
            "boundary-preserving-refactor",
            0.32,
            "proved",
            &[
                "docs/lean_theorem_index.md#operation-role-schema",
                "Formal.Arch.OperationRoleSchema.preservesInvariant_of_discharged_preserve",
            ],
            "safePreservingProved",
            "measured",
            Some(json!(0.0)),
            Some("formal-proof"),
            section_boundary.clone(),
            &["Lean theorem package ref discharges the selected preservation precondition"],
            &[
                "proved safe-preserving support is still relative to the selected operation semantics",
                SUPPORT_RISK_HISTORY_NON_CONCLUSION,
            ],
        ),
        support_risk_entry(
            "fixture:measured-policy-cleanup",
            "policy-cleanup",
            0.21,
            "measured",
            &[],
            "safePreservingMeasured",
            "measured",
            Some(json!(0.0)),
            Some("empirical-measured"),
            section_boundary.clone(),
            &["policy report measured the selected preservation precondition"],
            &[
                "measured safe-preserving support is not a Lean proof",
                SUPPORT_RISK_HISTORY_NON_CONCLUSION,
            ],
        ),
        support_risk_entry(
            "fixture:estimated-test-hardening",
            "test-hardening",
            0.18,
            "estimated",
            &[],
            "safePreservingEstimated",
            "estimated",
            Some(json!(0.0)),
            Some("model-estimate"),
            section_boundary.clone(),
            &["preservation is estimated from bounded fixture evidence"],
            &[
                "estimated safe-preserving support has lower confidence than proof or measurement",
                SUPPORT_RISK_HISTORY_NON_CONCLUSION,
            ],
        ),
        support_risk_entry(
            "fixture:unsafe-runtime-bypass",
            "runtime-bypass",
            0.04,
            "measured",
            &[],
            "unsafeWitnessMeasured",
            "measured",
            Some(json!(0.04)),
            Some("empirical-measured"),
            section_boundary.clone(),
            &["runtime bypass witness is measured in the selected support fixture"],
            &[
                "measured unsafe witness contributes support risk for the selected support only",
                SUPPORT_RISK_HISTORY_NON_CONCLUSION,
            ],
        ),
        support_risk_entry(
            "fixture:unknown-framework-convention",
            "framework-convention",
            0.25,
            "unmeasured",
            &[],
            "unmeasured",
            "unmeasured",
            None,
            None,
            section_boundary,
            &["operation semantics ref is missing for the framework convention"],
            &[
                "unmeasured support risk entry is not zero support risk",
                SUPPORT_RISK_HISTORY_NON_CONCLUSION,
            ],
        ),
    ]
}

fn support_risk_mass_metric(
    entries: &[SupportRiskMassEntryV0],
    source_refs: Vec<DynamicsArtifactRefV0>,
    measurement_boundary: MeasurementBoundaryV0,
) -> DynamicsMeasuredValueV0 {
    metric(
        "attractorEngineering.supportRiskMass",
        Some(calculate_support_risk_mass(entries)),
        "derived",
        Some("bounded-fixture-calculation"),
        source_refs,
        measurement_boundary,
        &[
            "SupportRiskMass is calculated over the finite retained support entries",
            "unknown, unavailable, private, notComparable, and outOfScope support is retained outside measuredRiskMass",
        ],
        &[
            "derived SupportRiskMass is bounded fixture evidence, not future operation distribution completeness",
            "unknown support risk mass is not measured zero",
            SUPPORT_RISK_HISTORY_NON_CONCLUSION,
            "operation proposal log refs do not conclude AI proposal distribution completeness",
        ],
    )
}

fn calculate_support_risk_mass(entries: &[SupportRiskMassEntryV0]) -> serde_json::Value {
    let mut finite_support_weight = 0.0;
    let mut measured_risk_mass = 0.0;
    let mut estimated_risk_mass = 0.0;
    let mut unknown_support_weight = 0.0;
    let mut risk_state_support_weight = std::collections::BTreeMap::<String, f64>::new();
    let mut preservation_precondition_status_weight =
        std::collections::BTreeMap::<String, f64>::new();
    let mut theorem_precondition_refs = BTreeSet::<String>::new();

    for entry in entries {
        let support_weight = metric_number(&entry.support_weight).unwrap_or(0.0);
        finite_support_weight += support_weight;
        *risk_state_support_weight
            .entry(entry.risk_state.clone())
            .or_insert(0.0) += support_weight;
        *preservation_precondition_status_weight
            .entry(entry.preservation_precondition_status.clone())
            .or_insert(0.0) += support_weight;
        theorem_precondition_refs.extend(entry.theorem_precondition_refs.iter().cloned());

        if UNKNOWN_SUPPORT_RISK_STATES.contains(&entry.risk_state.as_str()) {
            unknown_support_weight += support_weight;
            continue;
        }

        if let Some(contribution) = metric_number(&entry.risk_mass_contribution) {
            match entry.risk_mass_contribution.status.as_str() {
                "estimated" => estimated_risk_mass += contribution,
                "measured" | "derived" => measured_risk_mass += contribution,
                _ => {}
            }
        }
    }

    json!({
        "calculationKind": "finite-support-risk-mass",
        "entryCount": entries.len(),
        "finiteSupportWeight": rounded(finite_support_weight),
        "measuredRiskMass": rounded(measured_risk_mass),
        "estimatedRiskMass": rounded(estimated_risk_mass),
        "unknownSupportWeight": rounded(unknown_support_weight),
        "riskStateSupportWeight": rounded_map(risk_state_support_weight),
        "preservationPreconditionStatusWeight": rounded_map(preservation_precondition_status_weight),
        "theoremPreconditionRefs": theorem_precondition_refs.into_iter().collect::<Vec<_>>(),
        "calculationBoundary": "unknown, unavailable, private, notComparable, and outOfScope support is retained outside measuredRiskMass"
    })
}

fn calculate_basin_boundary_fragility(simulations: &[BasinSimulationV0]) -> serde_json::Value {
    let mut observed_perturbation_count = 0usize;
    let mut classification_flip_count = 0usize;
    let mut missing_perturbation_evidence_count = 0usize;
    let mut max_perturbation_steps = 0usize;
    let mut simulation_refs = Vec::new();

    for simulation in simulations {
        simulation_refs.push(simulation.simulation_id.clone());
        for evidence in &simulation.perturbation_evidence {
            max_perturbation_steps = max_perturbation_steps.max(evidence.perturbation_steps);
            if EVIDENCE_REQUIRED_STATUSES.contains(&evidence.status.as_str()) {
                observed_perturbation_count += 1;
                if evidence.baseline_classification != evidence.perturbed_classification {
                    classification_flip_count += 1;
                }
            } else {
                missing_perturbation_evidence_count += 1;
            }
        }
    }

    let fragility_ratio = if observed_perturbation_count == 0 {
        0.0
    } else {
        classification_flip_count as f64 / observed_perturbation_count as f64
    };

    json!({
        "calculationKind": "bounded-basin-boundary-fragility",
        "simulationRefs": simulation_refs,
        "maxPerturbationSteps": max_perturbation_steps,
        "observedPerturbationCount": observed_perturbation_count,
        "classificationFlipCount": classification_flip_count,
        "fragilityRatio": rounded(fragility_ratio),
        "missingPerturbationEvidenceCount": missing_perturbation_evidence_count,
        "calculationBoundary": "classification flips are selected bounded perturbation evidence, not global basin stability"
    })
}

fn calculate_trajectory_return_time(simulations: &[BasinSimulationV0]) -> serde_json::Value {
    let mut observed_return_count = 0usize;
    let mut non_returning_within_horizon_count = 0usize;
    let mut missing_return_evidence_count = 0usize;
    let mut return_steps = Vec::<usize>::new();
    let mut max_bounded_horizon = 0usize;
    let mut simulation_refs = Vec::new();

    for simulation in simulations {
        simulation_refs.push(simulation.simulation_id.clone());
        max_bounded_horizon = max_bounded_horizon.max(simulation.bounded_horizon);
        for evidence in &simulation.return_evidence {
            if evidence.status == "measured" {
                if let Some(steps) = evidence.steps_to_return {
                    observed_return_count += 1;
                    return_steps.push(steps);
                } else {
                    non_returning_within_horizon_count += 1;
                }
            } else if evidence.status == "unavailable" && evidence.steps_to_return.is_none() {
                non_returning_within_horizon_count += 1;
                missing_return_evidence_count += evidence.missing_evidence.len().max(1);
            } else {
                missing_return_evidence_count += evidence.missing_evidence.len().max(1);
            }
        }
    }

    let min_steps_to_return = return_steps.iter().min().copied();
    let max_steps_to_return = return_steps.iter().max().copied();
    let average_steps_to_return = if return_steps.is_empty() {
        None
    } else {
        Some(rounded(
            return_steps.iter().sum::<usize>() as f64 / return_steps.len() as f64,
        ))
    };

    json!({
        "calculationKind": "bounded-trajectory-return-time",
        "simulationRefs": simulation_refs,
        "boundedHorizon": max_bounded_horizon,
        "observedReturnCount": observed_return_count,
        "minStepsToReturn": min_steps_to_return,
        "maxStepsToReturn": max_steps_to_return,
        "averageStepsToReturn": average_steps_to_return,
        "nonReturningWithinHorizonCount": non_returning_within_horizon_count,
        "missingReturnEvidenceCount": missing_return_evidence_count,
        "calculationBoundary": "return time is selected bounded evidence and missing returns are not immediate-return evidence"
    })
}

fn calculate_observability_debt(simulations: &[BasinSimulationV0]) -> serde_json::Value {
    let mut required_axis_weight = 0.0;
    let mut measured_axis_weight = 0.0;
    let mut unmeasured_axis_weight = 0.0;
    let mut private_axis_weight = 0.0;
    let mut unavailable_axis_weight = 0.0;
    let mut status_weight = std::collections::BTreeMap::<String, f64>::new();
    let mut simulation_refs = Vec::new();

    for simulation in simulations {
        simulation_refs.push(simulation.simulation_id.clone());
        for axis in &simulation.observability_axes {
            let weight = metric_number(&axis.required_weight).unwrap_or(0.0);
            required_axis_weight += weight;
            *status_weight
                .entry(axis.evidence_status.clone())
                .or_insert(0.0) += weight;
            match axis.evidence_status.as_str() {
                "measured" | "derived" => measured_axis_weight += weight,
                "unmeasured" => unmeasured_axis_weight += weight,
                "private" => private_axis_weight += weight,
                "unavailable" => unavailable_axis_weight += weight,
                _ => {}
            }
        }
    }

    let debt_weight = unmeasured_axis_weight + private_axis_weight + unavailable_axis_weight;
    let debt_ratio = if required_axis_weight == 0.0 {
        0.0
    } else {
        debt_weight / required_axis_weight
    };

    json!({
        "calculationKind": "bounded-observability-debt",
        "simulationRefs": simulation_refs,
        "requiredAxisWeight": rounded(required_axis_weight),
        "measuredAxisWeight": rounded(measured_axis_weight),
        "unmeasuredAxisWeight": rounded(unmeasured_axis_weight),
        "privateAxisWeight": rounded(private_axis_weight),
        "unavailableAxisWeight": rounded(unavailable_axis_weight),
        "debtWeight": rounded(debt_weight),
        "debtRatio": rounded(debt_ratio),
        "axisStatusWeight": rounded_map(status_weight),
        "calculationBoundary": "unmeasured, private, and unavailable required axes are retained as debt, not measured zero"
    })
}

fn metric_number(metric: &DynamicsMeasuredValueV0) -> Option<f64> {
    metric.value.as_ref()?.as_f64()
}

fn rounded(value: f64) -> f64 {
    (value * 1_000_000.0).round() / 1_000_000.0
}

fn rounded_map(
    values: std::collections::BTreeMap<String, f64>,
) -> std::collections::BTreeMap<String, f64> {
    values
        .into_iter()
        .map(|(key, value)| (key, rounded(value)))
        .collect()
}

#[allow(clippy::too_many_arguments)]
fn support_risk_entry(
    operation_id: &str,
    operation_kind: &str,
    support_weight: f64,
    preservation_precondition_status: &str,
    theorem_precondition_refs: &[&str],
    risk_state: &str,
    risk_mass_status: &str,
    risk_mass_value: Option<serde_json::Value>,
    risk_mass_confidence: Option<&str>,
    measurement_boundary: MeasurementBoundaryV0,
    assumptions: &[&str],
    non_conclusions: &[&str],
) -> SupportRiskMassEntryV0 {
    let support_weight_metric = metric(
        &format!("{operation_id}.supportWeight"),
        Some(json!(support_weight)),
        "measured",
        Some("fixture-normalized-support"),
        Vec::new(),
        measurement_boundary.clone(),
        &["support weight is normalized over the finite fixture support"],
        &["finite fixture support weight is not future distribution completeness"],
    );
    let risk_mass_contribution = metric(
        &format!("{operation_id}.riskMassContribution"),
        risk_mass_value,
        risk_mass_status,
        risk_mass_confidence,
        Vec::new(),
        measurement_boundary.clone(),
        &["risk contribution is relative to the finite support entry risk state"],
        non_conclusions,
    );
    SupportRiskMassEntryV0 {
        operation_id: operation_id.to_string(),
        operation_kind: operation_kind.to_string(),
        support_scope_refs: vec!["fixture:selected-safe-region".to_string()],
        support_weight: support_weight_metric,
        preservation_precondition_status: preservation_precondition_status.to_string(),
        theorem_precondition_refs: strings(theorem_precondition_refs),
        risk_state: risk_state.to_string(),
        risk_mass_contribution,
        measurement_boundary,
        assumptions: strings(assumptions),
        non_conclusions: strings(non_conclusions),
    }
}

fn attractor_candidate(
    candidate_id: &str,
    candidate_kind: &str,
    status: &str,
    region_refs: &[&str],
    metric_refs: &[&str],
    measurement_boundary: MeasurementBoundaryV0,
    assumptions: &[&str],
    non_conclusions: &[&str],
) -> AttractorEngineeringCandidateV0 {
    AttractorEngineeringCandidateV0 {
        candidate_id: candidate_id.to_string(),
        candidate_kind: candidate_kind.to_string(),
        status: status.to_string(),
        region_refs: strings(region_refs),
        metric_refs: strings(metric_refs),
        measurement_boundary,
        assumptions: strings(assumptions),
        non_conclusions: strings(non_conclusions),
    }
}

#[allow(clippy::too_many_arguments)]
fn attractor_signal(
    signal_id: &str,
    signal_kind: &str,
    selected_signal: &str,
    source_refs: Vec<DynamicsArtifactRefV0>,
    status: &str,
    confidence: Option<&str>,
    measurement_boundary: MeasurementBoundaryV0,
    assumptions: &[&str],
    non_conclusions: &[&str],
) -> AttractorEngineeringSignalV0 {
    AttractorEngineeringSignalV0 {
        signal_id: signal_id.to_string(),
        signal_kind: signal_kind.to_string(),
        selected_signal: selected_signal.to_string(),
        status: status.to_string(),
        source_refs,
        confidence: confidence.map(str::to_string),
        measurement_boundary,
        assumptions: strings(assumptions),
        non_conclusions: strings(non_conclusions),
    }
}

fn readiness_axis(
    measurement_boundary: &MeasurementBoundaryV0,
    axis: &str,
    status: &str,
    confidence: Option<&str>,
    source_refs: Vec<DynamicsArtifactRefV0>,
    assumptions: &[&str],
    non_conclusions: &[&str],
) -> DynamicsMeasuredValueV0 {
    metric(
        &format!("vibeCodingReadiness.{axis}"),
        None,
        status,
        confidence,
        source_refs,
        measurement_boundary.clone(),
        assumptions,
        non_conclusions,
    )
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
        policy_version: Some("fixture-policy/v0.5.0".to_string()),
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
            "unsupported architecture-dynamics-metrics-report schema: {}",
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
        || report.attractor_engineering.is_none()
    {
        invalid.push(generic_validation_example(
            &report.report_id,
            "metric groups",
            "trajectory, force, gap, fieldControl, aiDynamics, and attractorEngineering metric groups must be present",
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

fn check_attractor_engineering_section(
    report: &ArchitectureDynamicsMetricsReportV0,
) -> ValidationCheck {
    let allowed_candidate_statuses = string_set(ALLOWED_ATTRACTOR_CANDIDATE_STATUSES);
    let allowed_support_risk_states = string_set(ALLOWED_SUPPORT_RISK_STATES);
    let allowed_preservation_statuses = string_set(ALLOWED_PRESERVATION_PRECONDITION_STATUSES);
    let unknown_support_risk_states = string_set(UNKNOWN_SUPPORT_RISK_STATES);
    let mut invalid = Vec::new();
    let Some(section) = &report.attractor_engineering else {
        invalid.push(generic_validation_example(
            &report.report_id,
            "attractorEngineering",
            "attractorEngineering section must be present",
        ));
        return check_examples(
            "architecture-dynamics-metrics-attractor-engineering-section-recorded",
            "Attractor Engineering section records bounded candidates, metric slots, and non-conclusions",
            invalid,
        );
    };

    if section.selected_regions.is_empty()
        || section.attractor_candidates.is_empty()
        || section.basin_candidates.is_empty()
        || section.basin_simulations.is_empty()
        || section.support_risk_entries.is_empty()
        || section.design_field_signals.is_empty()
        || section.seed_attractor_signals.is_empty()
        || section.vibe_coding_readiness_axes.is_empty()
    {
        invalid.push(generic_validation_example(
            &report.report_id,
            "attractorEngineering",
            "selectedRegions, attractorCandidates, basinCandidates, basinSimulations, supportRiskEntries, field signals, and readiness axes must be present",
        ));
    }
    for required in REQUIRED_ATTRACTOR_NON_CONCLUSIONS {
        if !section
            .non_conclusions
            .iter()
            .any(|conclusion| conclusion == required)
        {
            invalid.push(generic_validation_example(
                &report.report_id,
                "attractorEngineering.nonConclusions",
                &format!("missing required Attractor Engineering non-conclusion: {required}"),
            ));
        }
    }
    validate_boundary(
        &report.report_id,
        "attractorEngineering.measurementBoundary",
        &section.measurement_boundary,
        true,
        &mut invalid,
    );
    if !has_artifact_kind(
        &section.measurement_boundary.source_artifact_refs,
        "architecture-field-snapshot",
    ) || !has_artifact_kind(
        &section.measurement_boundary.source_artifact_refs,
        "operation-proposal-log",
    ) {
        invalid.push(generic_validation_example(
            &report.report_id,
            "attractorEngineering.measurementBoundary.sourceArtifactRefs",
            "Attractor Engineering must reference architecture-field-snapshot and operation-proposal-log artifact refs",
        ));
    }
    for region in &section.selected_regions {
        if region.region_id.trim().is_empty()
            || region.region_kind.trim().is_empty()
            || region.defining_axes.is_empty()
            || has_blank(&region.defining_axes)
            || region.non_conclusions.is_empty()
            || has_blank(&region.non_conclusions)
        {
            invalid.push(generic_validation_example(
                &region.region_id,
                "attractorEngineering.selectedRegions",
                "selected regions must record id, kind, defining axes, and non-conclusions",
            ));
        }
        validate_boundary(
            &region.region_id,
            "measurementBoundary",
            &region.measurement_boundary,
            true,
            &mut invalid,
        );
    }
    for candidate in section
        .attractor_candidates
        .iter()
        .chain(section.basin_candidates.iter())
    {
        if candidate.candidate_id.trim().is_empty()
            || candidate.candidate_kind.trim().is_empty()
            || candidate.region_refs.is_empty()
            || has_blank(&candidate.region_refs)
            || candidate.metric_refs.is_empty()
            || has_blank(&candidate.metric_refs)
        {
            invalid.push(generic_validation_example(
                &candidate.candidate_id,
                "attractorEngineering.candidates",
                "candidates must record id, kind, region refs, and metric refs",
            ));
        }
        if !allowed_candidate_statuses.contains(candidate.status.as_str()) {
            invalid.push(generic_validation_example(
                &candidate.candidate_id,
                &candidate.status,
                "unsupported Attractor Engineering candidate status",
            ));
        }
        if candidate.assumptions.is_empty() || has_blank(&candidate.assumptions) {
            invalid.push(generic_validation_example(
                &candidate.candidate_id,
                "assumptions",
                "candidate assumptions must be explicit",
            ));
        }
        if candidate.non_conclusions.is_empty() || has_blank(&candidate.non_conclusions) {
            invalid.push(generic_validation_example(
                &candidate.candidate_id,
                "nonConclusions",
                "candidate non-conclusions must be explicit",
            ));
        }
        validate_boundary(
            &candidate.candidate_id,
            "measurementBoundary",
            &candidate.measurement_boundary,
            candidate.status == "candidate",
            &mut invalid,
        );
    }
    for signal in section
        .design_field_signals
        .iter()
        .chain(section.seed_attractor_signals.iter())
    {
        validate_field_shaping_signal(signal, &mut invalid);
    }
    validate_field_shaping_metric_protocol(section, &mut invalid);
    validate_basin_simulations(section, &mut invalid);
    for entry in &section.support_risk_entries {
        if entry.operation_id.trim().is_empty()
            || entry.operation_kind.trim().is_empty()
            || entry.support_scope_refs.is_empty()
            || has_blank(&entry.support_scope_refs)
            || entry.assumptions.is_empty()
            || has_blank(&entry.assumptions)
            || entry.non_conclusions.is_empty()
            || has_blank(&entry.non_conclusions)
        {
            invalid.push(generic_validation_example(
                &entry.operation_id,
                "attractorEngineering.supportRiskEntries",
                "support risk entries must record operation id, kind, scope refs, assumptions, and non-conclusions",
            ));
        }
        if !allowed_support_risk_states.contains(entry.risk_state.as_str()) {
            invalid.push(generic_validation_example(
                &entry.operation_id,
                &entry.risk_state,
                "unsupported SupportRiskMass risk state",
            ));
        }
        if !allowed_preservation_statuses.contains(entry.preservation_precondition_status.as_str())
        {
            invalid.push(generic_validation_example(
                &entry.operation_id,
                &entry.preservation_precondition_status,
                "unsupported operation preservation precondition status",
            ));
        }
        if entry.risk_state == "safePreservingProved" && entry.theorem_precondition_refs.is_empty()
        {
            invalid.push(generic_validation_example(
                &entry.operation_id,
                "theoremPreconditionRefs",
                "safePreservingProved support risk entries must retain Lean theorem or theorem index precondition refs",
            ));
        }
        if has_blank(&entry.theorem_precondition_refs) {
            invalid.push(generic_validation_example(
                &entry.operation_id,
                "theoremPreconditionRefs",
                "theorem precondition refs must not contain blank refs",
            ));
        }
        validate_boundary(
            &entry.operation_id,
            "measurementBoundary",
            &entry.measurement_boundary,
            true,
            &mut invalid,
        );
        validate_support_risk_metric(
            &entry.operation_id,
            "supportWeight",
            &entry.support_weight,
            &mut invalid,
        );
        validate_support_risk_metric(
            &entry.operation_id,
            "riskMassContribution",
            &entry.risk_mass_contribution,
            &mut invalid,
        );
        if unknown_support_risk_states.contains(entry.risk_state.as_str())
            && is_numeric_zero(entry.risk_mass_contribution.value.as_ref())
            && (entry.risk_mass_contribution.status == "measured"
                || entry.risk_mass_contribution.status == "derived")
        {
            invalid.push(generic_validation_example(
                &entry.operation_id,
                "riskMassContribution",
                "unmeasured, unavailable, private, notComparable, and outOfScope support risk states must not be emitted as measured numeric zero",
            ));
        }
        if !entry
            .non_conclusions
            .iter()
            .chain(entry.risk_mass_contribution.non_conclusions.iter())
            .any(|conclusion| conclusion == SUPPORT_RISK_HISTORY_NON_CONCLUSION)
        {
            invalid.push(generic_validation_example(
                &entry.operation_id,
                "nonConclusions",
                "accepted PR history and future support risk must remain separate",
            ));
        }
    }
    validate_support_risk_mass_calculation(section, &mut invalid);
    validate_safe_preserving_confidence_distinction(section, &mut invalid);
    validate_basin_return_observability_boundaries(section, &mut invalid);
    validate_field_shaping_delta(section, &mut invalid);
    validate_vibe_coding_readiness_axes(section, &mut invalid);
    if !section
        .support_risk_mass
        .non_conclusions
        .iter()
        .chain(section.non_conclusions.iter())
        .any(|conclusion| conclusion == SUPPORT_RISK_HISTORY_NON_CONCLUSION)
    {
        invalid.push(generic_validation_example(
            &report.report_id,
            "attractorEngineering.supportRiskMass.nonConclusions",
            "accepted PR history safety and future support risk must be separated",
        ));
    }
    check_examples(
        "architecture-dynamics-metrics-attractor-engineering-section-recorded",
        "Attractor Engineering section records bounded candidates, metric slots, and non-conclusions",
        invalid,
    )
}

fn validate_basin_simulations(
    section: &AttractorEngineeringMetricsV0,
    invalid: &mut Vec<ValidationExample>,
) {
    let allowed_statuses = string_set(ALLOWED_STATUSES);
    let allowed_classifications = string_set(["candidate", "nonCandidate", "missingEvidence"]);
    let mut has_candidate = false;
    let mut has_non_candidate = false;
    let mut has_missing_evidence = false;
    let mut has_fragility_flip = false;
    let mut has_return = false;
    let mut has_return_missing_evidence = false;
    let mut unknown_axis_weight = 0.0;

    for simulation in &section.basin_simulations {
        if simulation.simulation_id.trim().is_empty()
            || simulation.bounded_horizon == 0
            || simulation.selected_initial_states.is_empty()
            || simulation.operation_scripts.is_empty()
            || simulation.basin_classifications.is_empty()
            || simulation.perturbation_evidence.is_empty()
            || simulation.return_evidence.is_empty()
            || simulation.observability_axes.is_empty()
            || simulation.source_refs.is_empty()
            || has_blank_artifact_refs(&simulation.source_refs)
            || simulation.assumptions.is_empty()
            || has_blank(&simulation.assumptions)
            || simulation.non_conclusions.is_empty()
            || has_blank(&simulation.non_conclusions)
        {
            invalid.push(generic_validation_example(
                &simulation.simulation_id,
                "attractorEngineering.basinSimulations",
                "basin simulations must record selected initial states, scripts, classifications, bounded horizon, source refs, assumptions, and non-conclusions",
            ));
        }
        validate_boundary(
            &simulation.simulation_id,
            "measurementBoundary",
            &simulation.measurement_boundary,
            true,
            invalid,
        );

        for state in &simulation.selected_initial_states {
            if state.state_id.trim().is_empty()
                || state.state_kind.trim().is_empty()
                || state.region_refs.is_empty()
                || has_blank(&state.region_refs)
                || !allowed_statuses.contains(state.evidence_status.as_str())
            {
                invalid.push(generic_validation_example(
                    &state.state_id,
                    "selectedInitialStates",
                    "selected initial states must record id, kind, region refs, and supported evidence status",
                ));
            }
            validate_support_risk_metric(
                &state.state_id,
                "stateWeight",
                &state.state_weight,
                invalid,
            );
            if UNKNOWN_SUPPORT_RISK_STATES.contains(&state.evidence_status.as_str())
                && state.missing_evidence.is_empty()
            {
                invalid.push(generic_validation_example(
                    &state.state_id,
                    "missingEvidence",
                    "missing, private, unavailable, notComparable, and outOfScope initial-state evidence must be retained",
                ));
            }
        }

        for script in &simulation.operation_scripts {
            if script.script_id.trim().is_empty()
                || script.operation_ids.is_empty()
                || has_blank(&script.operation_ids)
                || script.bounded_horizon == 0
                || script.bounded_horizon > simulation.bounded_horizon
                || script.source_refs.is_empty()
                || has_blank_artifact_refs(&script.source_refs)
                || script.assumptions.is_empty()
                || has_blank(&script.assumptions)
                || script.non_conclusions.is_empty()
                || has_blank(&script.non_conclusions)
            {
                invalid.push(generic_validation_example(
                    &script.script_id,
                    "operationScripts",
                    "finite operation scripts must record operation ids, source refs, non-conclusions, and a horizon within the simulation horizon",
                ));
            }
            validate_boundary(
                &script.script_id,
                "measurementBoundary",
                &script.measurement_boundary,
                true,
                invalid,
            );
        }

        for classification in &simulation.basin_classifications {
            has_candidate |= classification.classification == "candidate";
            has_non_candidate |= classification.classification == "nonCandidate";
            has_missing_evidence |= classification.classification == "missingEvidence";
            if classification.state_id.trim().is_empty()
                || classification.script_id.trim().is_empty()
                || !allowed_classifications.contains(classification.classification.as_str())
                || !allowed_statuses.contains(classification.status.as_str())
                || classification.assumptions.is_empty()
                || has_blank(&classification.assumptions)
                || classification.non_conclusions.is_empty()
                || has_blank(&classification.non_conclusions)
            {
                invalid.push(generic_validation_example(
                    &classification.state_id,
                    "basinClassifications",
                    "basin classifications must distinguish candidate, nonCandidate, and missingEvidence entries with explicit assumptions and non-conclusions",
                ));
            }
            if classification.classification == "candidate"
                && (classification.target_region_ref.is_none()
                    || classification
                        .steps_to_target
                        .is_none_or(|steps| steps > simulation.bounded_horizon))
            {
                invalid.push(generic_validation_example(
                    &classification.state_id,
                    "stepsToTarget",
                    "candidate basin classifications must reach a selected target region within the bounded horizon",
                ));
            }
            if classification.classification == "missingEvidence"
                && classification.missing_evidence.is_empty()
            {
                invalid.push(generic_validation_example(
                    &classification.state_id,
                    "missingEvidence",
                    "missing-evidence basin classifications must retain missing evidence instead of implying a candidate or non-candidate result",
                ));
            }
        }

        for perturbation in &simulation.perturbation_evidence {
            has_fragility_flip |= EVIDENCE_REQUIRED_STATUSES
                .contains(&perturbation.status.as_str())
                && perturbation.baseline_classification != perturbation.perturbed_classification;
            if perturbation.evidence_id.trim().is_empty()
                || perturbation.source_state_id.trim().is_empty()
                || perturbation.perturbation_kind.trim().is_empty()
                || perturbation.perturbation_steps == 0
                || perturbation.perturbation_steps > simulation.bounded_horizon
                || !allowed_statuses.contains(perturbation.status.as_str())
                || perturbation.assumptions.is_empty()
                || has_blank(&perturbation.assumptions)
                || !perturbation
                    .non_conclusions
                    .iter()
                    .any(|conclusion| conclusion == BASIN_BOUNDARY_FRAGILITY_NON_CONCLUSION)
            {
                invalid.push(generic_validation_example(
                    &perturbation.evidence_id,
                    "perturbationEvidence",
                    "perturbation evidence must be bounded, status-tagged, and retain BasinBoundaryFragility non-conclusion",
                ));
            }
            validate_boundary(
                &perturbation.evidence_id,
                "measurementBoundary",
                &perturbation.measurement_boundary,
                EVIDENCE_REQUIRED_STATUSES.contains(&perturbation.status.as_str()),
                invalid,
            );
        }

        for evidence in &simulation.return_evidence {
            has_return |= evidence.status == "measured" && evidence.steps_to_return.is_some();
            has_return_missing_evidence |= !evidence.missing_evidence.is_empty();
            if evidence.evidence_id.trim().is_empty()
                || evidence.state_id.trim().is_empty()
                || evidence.excursion_region_ref.trim().is_empty()
                || evidence.return_region_ref.trim().is_empty()
                || !allowed_statuses.contains(evidence.status.as_str())
                || evidence
                    .steps_to_return
                    .is_some_and(|steps| steps > simulation.bounded_horizon)
                || evidence.assumptions.is_empty()
                || has_blank(&evidence.assumptions)
                || !evidence
                    .non_conclusions
                    .iter()
                    .any(|conclusion| conclusion == TRAJECTORY_RETURN_TIME_NON_CONCLUSION)
            {
                invalid.push(generic_validation_example(
                    &evidence.evidence_id,
                    "returnEvidence",
                    "return evidence must be bounded, status-tagged, and retain TrajectoryReturnTime non-conclusion",
                ));
            }
            if UNKNOWN_SUPPORT_RISK_STATES.contains(&evidence.status.as_str())
                && evidence.missing_evidence.is_empty()
            {
                invalid.push(generic_validation_example(
                    &evidence.evidence_id,
                    "missingEvidence",
                    "missing bounded return evidence must be retained separately from observed returns",
                ));
            }
            validate_boundary(
                &evidence.evidence_id,
                "measurementBoundary",
                &evidence.measurement_boundary,
                EVIDENCE_REQUIRED_STATUSES.contains(&evidence.status.as_str()),
                invalid,
            );
        }

        for axis in &simulation.observability_axes {
            let weight = metric_number(&axis.required_weight).unwrap_or(0.0);
            if matches!(
                axis.evidence_status.as_str(),
                "unmeasured" | "private" | "unavailable"
            ) {
                unknown_axis_weight += weight;
            }
            if axis.axis_id.trim().is_empty()
                || !allowed_statuses.contains(axis.evidence_status.as_str())
                || axis.assumptions.is_empty()
                || has_blank(&axis.assumptions)
                || !axis
                    .non_conclusions
                    .iter()
                    .any(|conclusion| conclusion == OBSERVABILITY_DEBT_NON_CONCLUSION)
            {
                invalid.push(generic_validation_example(
                    &axis.axis_id,
                    "observabilityAxes",
                    "observability axes must record required weight, supported evidence status, and ObservabilityDebt non-conclusion",
                ));
            }
            validate_support_risk_metric(
                &axis.axis_id,
                "requiredWeight",
                &axis.required_weight,
                invalid,
            );
            validate_boundary(
                &axis.axis_id,
                "measurementBoundary",
                &axis.measurement_boundary,
                EVIDENCE_REQUIRED_STATUSES.contains(&axis.evidence_status.as_str()),
                invalid,
            );
        }
    }

    if !(has_candidate && has_non_candidate && has_missing_evidence) {
        invalid.push(generic_validation_example(
            "attractorEngineering.basinSimulations",
            "basinClassifications",
            "bounded basin simulation must distinguish candidate, nonCandidate, and missingEvidence classifications",
        ));
    }
    if !has_fragility_flip {
        invalid.push(generic_validation_example(
            "attractorEngineering.basinSimulations",
            "perturbationEvidence",
            "BasinBoundaryFragility needs selected 1-step or k-step perturbation evidence with a classification flip",
        ));
    }
    if !(has_return && has_return_missing_evidence) {
        invalid.push(generic_validation_example(
            "attractorEngineering.basinSimulations",
            "returnEvidence",
            "TrajectoryReturnTime must keep observed bounded returns and missing return evidence separate",
        ));
    }
    if unknown_axis_weight == 0.0 {
        invalid.push(generic_validation_example(
            "attractorEngineering.basinSimulations",
            "observabilityAxes",
            "ObservabilityDebt must retain nonzero unmeasured, private, or unavailable required-axis weight",
        ));
    }
}

fn validate_support_risk_mass_calculation(
    section: &AttractorEngineeringMetricsV0,
    invalid: &mut Vec<ValidationExample>,
) {
    let metric = &section.support_risk_mass;
    if metric.metric_id != "attractorEngineering.supportRiskMass" {
        invalid.push(generic_validation_example(
            &metric.metric_id,
            "metricId",
            "SupportRiskMass must be recorded in the attractorEngineering supportRiskMass slot",
        ));
    }
    if metric.status != "derived" {
        invalid.push(generic_validation_example(
            &metric.metric_id,
            "status",
            "SupportRiskMass calculator output must be emitted as a derived bounded calculation",
        ));
    }
    let Some(value) = metric.value.as_ref().and_then(|value| value.as_object()) else {
        invalid.push(generic_validation_example(
            &metric.metric_id,
            "value",
            "SupportRiskMass calculator output must record aggregate calculation fields",
        ));
        return;
    };

    let expected = calculate_support_risk_mass(&section.support_risk_entries);
    let expected_object = expected
        .as_object()
        .expect("calculated SupportRiskMass value is an object");
    for field in [
        "entryCount",
        "finiteSupportWeight",
        "measuredRiskMass",
        "estimatedRiskMass",
        "unknownSupportWeight",
        "riskStateSupportWeight",
        "preservationPreconditionStatusWeight",
    ] {
        if value.get(field) != expected_object.get(field) {
            invalid.push(generic_validation_example(
                &metric.metric_id,
                field,
                "SupportRiskMass aggregate must match finite support entries",
            ));
        }
    }

    let unknown_entry_count = section
        .support_risk_entries
        .iter()
        .filter(|entry| UNKNOWN_SUPPORT_RISK_STATES.contains(&entry.risk_state.as_str()))
        .count();
    let unknown_support_weight = value
        .get("unknownSupportWeight")
        .and_then(serde_json::Value::as_f64)
        .unwrap_or(0.0);
    if unknown_entry_count > 0 && unknown_support_weight == 0.0 {
        invalid.push(generic_validation_example(
            &metric.metric_id,
            "unknownSupportWeight",
            "unknown, unavailable, private, notComparable, and outOfScope support must not be collapsed to measured zero",
        ));
    }

    let aggregate_refs = value
        .get("theoremPreconditionRefs")
        .and_then(serde_json::Value::as_array)
        .cloned()
        .unwrap_or_default();
    for entry in section
        .support_risk_entries
        .iter()
        .filter(|entry| entry.risk_state == "safePreservingProved")
    {
        for theorem_ref in &entry.theorem_precondition_refs {
            if !aggregate_refs
                .iter()
                .any(|value| value.as_str() == Some(theorem_ref.as_str()))
            {
                invalid.push(generic_validation_example(
                    &entry.operation_id,
                    "theoremPreconditionRefs",
                    "SupportRiskMass aggregate must retain safePreservingProved theorem precondition refs",
                ));
            }
        }
    }
}

fn validate_field_shaping_signal(
    signal: &AttractorEngineeringSignalV0,
    invalid: &mut Vec<ValidationExample>,
) {
    if signal.signal_id.trim().is_empty()
        || signal.signal_kind.trim().is_empty()
        || signal.selected_signal.trim().is_empty()
        || signal.status.trim().is_empty()
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
            "attractorEngineering.fieldSignals",
            "field shaping signals must record selected signal, source refs, confidence, assumptions, and non-conclusions",
        ));
    }
    if !ALLOWED_STATUSES.contains(&signal.status.as_str()) {
        invalid.push(generic_validation_example(
            &signal.signal_id,
            &signal.status,
            "unsupported field shaping signal status",
        ));
    }
    if signal.signal_kind == "DesignFieldStrength"
        && !signal
            .non_conclusions
            .iter()
            .any(|conclusion| {
                conclusion
                    == "DesignFieldStrength is a selected empirical signal, not a truth claim about the architecture field"
            })
    {
        invalid.push(generic_validation_example(
            &signal.signal_id,
            "nonConclusions",
            "DesignFieldStrength signal must not be emitted as a truth claim",
        ));
    }
    if signal.signal_kind == "DesignFieldStrength"
        && (!has_artifact_kind(&signal.source_refs, "architecture-field-snapshot")
            || !has_artifact_kind(&signal.source_refs, "operation-proposal-log"))
    {
        invalid.push(generic_validation_example(
            &signal.signal_id,
            "sourceRefs",
            "DesignFieldStrength pilot signals must retain architecture-field-snapshot and operation-proposal-log refs",
        ));
    }
    if signal.signal_kind == "SeedAttractorStrength"
        && (!has_artifact_kind(&signal.source_refs, "canonical-example-ref")
            || !has_artifact_kind(&signal.source_refs, "patch-similarity-evidence"))
    {
        invalid.push(generic_validation_example(
            &signal.signal_id,
            "sourceRefs",
            "SeedAttractorStrength pilot signals must retain canonical example refs and patch similarity evidence",
        ));
    }
    validate_boundary(
        &signal.signal_id,
        "measurementBoundary",
        &signal.measurement_boundary,
        true,
        invalid,
    );
}

fn validate_field_shaping_metric_protocol(
    section: &AttractorEngineeringMetricsV0,
    invalid: &mut Vec<ValidationExample>,
) {
    let design = &section.design_field_strength;
    if design.metric_id != "attractorEngineering.designFieldStrength" {
        invalid.push(generic_validation_example(
            &design.metric_id,
            "metricId",
            "DesignFieldStrength must be recorded in the attractorEngineering designFieldStrength slot",
        ));
    }
    if EVIDENCE_REQUIRED_STATUSES.contains(&design.status.as_str()) {
        if design
            .confidence
            .as_deref()
            .unwrap_or_default()
            .trim()
            .is_empty()
            || !has_artifact_kind(&design.source_refs, "architecture-field-snapshot")
            || !has_artifact_kind(&design.source_refs, "operation-proposal-log")
        {
            invalid.push(generic_validation_example(
                &design.metric_id,
                "sourceRefs",
                "DesignFieldStrength pilot metrics must retain selected source refs and confidence",
            ));
        }
    }
    if !design.non_conclusions.iter().any(|conclusion| {
        conclusion == "DesignFieldStrength is a selected empirical signal, not a truth claim about the architecture field"
    }) {
        invalid.push(generic_validation_example(
            &design.metric_id,
            "nonConclusions",
            "DesignFieldStrength metric must keep the selected empirical signal boundary explicit",
        ));
    }

    let seed = &section.seed_attractor_strength;
    if seed.metric_id != "attractorEngineering.seedAttractorStrength" {
        invalid.push(generic_validation_example(
            &seed.metric_id,
            "metricId",
            "SeedAttractorStrength must be recorded in the attractorEngineering seedAttractorStrength slot",
        ));
    }
    if EVIDENCE_REQUIRED_STATUSES.contains(&seed.status.as_str()) {
        if seed
            .confidence
            .as_deref()
            .unwrap_or_default()
            .trim()
            .is_empty()
            || !has_artifact_kind(&seed.source_refs, "canonical-example-ref")
            || !has_artifact_kind(&seed.source_refs, "patch-similarity-evidence")
        {
            invalid.push(generic_validation_example(
                &seed.metric_id,
                "sourceRefs",
                "SeedAttractorStrength pilot metrics must retain canonical example refs, patch similarity evidence, and confidence",
            ));
        }
        let value = seed.value.as_ref().and_then(serde_json::Value::as_object);
        let has_protocol = value
            .and_then(|object| object.get("protocol"))
            .and_then(serde_json::Value::as_str)
            == Some("selected-seed-attractor-pilot");
        if !has_protocol {
            invalid.push(generic_validation_example(
                &seed.metric_id,
                "value.protocol",
                "SeedAttractorStrength pilot metrics must record the selected empirical protocol",
            ));
        }
    }
    if !seed.non_conclusions.iter().any(|conclusion| {
        conclusion == "selected SeedAttractorStrength signal is not a convergence theorem"
    }) {
        invalid.push(generic_validation_example(
            &seed.metric_id,
            "nonConclusions",
            "SeedAttractorStrength metric must keep convergence-theorem non-conclusion explicit",
        ));
    }
}

fn validate_field_shaping_delta(
    section: &AttractorEngineeringMetricsV0,
    invalid: &mut Vec<ValidationExample>,
) {
    let metric = &section.field_shaping_delta;
    if metric.metric_id != "attractorEngineering.fieldShapingDelta" {
        invalid.push(generic_validation_example(
            &metric.metric_id,
            "metricId",
            "FieldShapingDelta must be recorded in the attractorEngineering fieldShapingDelta slot",
        ));
    }
    if metric.status == "notComparable" {
        if !metric
            .measurement_boundary
            .missing_evidence
            .iter()
            .any(|evidence| {
                evidence.boundary == "notComparable" && evidence.reason.contains("before/after")
            })
        {
            invalid.push(generic_validation_example(
                &metric.metric_id,
                "missingEvidence",
                "notComparable FieldShapingDelta must record the before/after comparability boundary",
            ));
        }
    } else if EVIDENCE_REQUIRED_STATUSES.contains(&metric.status.as_str())
        && (metric.source_refs.is_empty()
            || has_blank_artifact_refs(&metric.source_refs)
            || metric.measurement_boundary.aggregation_window.is_none())
    {
        invalid.push(generic_validation_example(
            &metric.metric_id,
            "measurementBoundary",
            "comparable FieldShapingDelta needs source refs and bounded before/after measurement boundary",
        ));
    }
    if !metric
        .non_conclusions
        .iter()
        .any(|conclusion| conclusion == FIELD_SHAPING_DELTA_NON_CONCLUSION)
    {
        invalid.push(generic_validation_example(
            &metric.metric_id,
            "nonConclusions",
            "FieldShapingDelta must keep its comparability non-conclusion explicit",
        ));
    }
}

fn validate_vibe_coding_readiness_axes(
    section: &AttractorEngineeringMetricsV0,
    invalid: &mut Vec<ValidationExample>,
) {
    for axis in REQUIRED_VIBE_CODING_READINESS_AXES {
        let expected_id = format!("vibeCodingReadiness.{axis}");
        if !section
            .vibe_coding_readiness_axes
            .iter()
            .any(|metric| metric.metric_id == expected_id)
        {
            invalid.push(generic_validation_example(
                "attractorEngineering.vibeCodingReadinessAxes",
                axis,
                "VibeCodingReadiness must record each required readiness axis separately",
            ));
        }
    }
    for metric in &section.vibe_coding_readiness_axes {
        if metric.metric_id.to_ascii_lowercase().contains("score") {
            invalid.push(generic_validation_example(
                &metric.metric_id,
                "metricId",
                "VibeCodingReadiness must not be emitted as a single numeric score",
            ));
        }
        if !metric
            .non_conclusions
            .iter()
            .any(|conclusion| conclusion == VIBE_CODING_READINESS_NON_CONCLUSION)
        {
            invalid.push(generic_validation_example(
                &metric.metric_id,
                "nonConclusions",
                "each readiness axis must preserve the multi-axis non-conclusion",
            ));
        }
        validate_boundary(
            &metric.metric_id,
            "measurementBoundary",
            &metric.measurement_boundary,
            EVIDENCE_REQUIRED_STATUSES.contains(&metric.status.as_str()),
            invalid,
        );
    }
}

fn validate_basin_return_observability_boundaries(
    section: &AttractorEngineeringMetricsV0,
    invalid: &mut Vec<ValidationExample>,
) {
    let basin_candidates = section
        .basin_candidates
        .iter()
        .filter(|candidate| candidate.candidate_kind.contains("basin"));
    if !basin_candidates.clone().any(|candidate| {
        candidate.status == "candidate"
            && candidate.measurement_boundary.aggregation_window.is_some()
            && !candidate
                .measurement_boundary
                .source_artifact_refs
                .is_empty()
            && !has_blank_artifact_refs(&candidate.measurement_boundary.source_artifact_refs)
            && !candidate
                .measurement_boundary
                .selected_region_refs
                .is_empty()
            && !has_blank(&candidate.measurement_boundary.selected_region_refs)
    }) {
        invalid.push(generic_validation_example(
            "attractorEngineering.basinCandidates",
            "candidate",
            "at least one basin candidate must be bounded by finite source refs, selected region refs, and an aggregation window",
        ));
    }
    if !basin_candidates.clone().any(|candidate| {
        (candidate.status == "missingEvidence"
            || UNKNOWN_SUPPORT_RISK_STATES.contains(&candidate.status.as_str()))
            && !candidate.measurement_boundary.missing_evidence.is_empty()
    }) {
        invalid.push(generic_validation_example(
            "attractorEngineering.basinCandidates",
            "missingEvidence",
            "at least one non-candidate basin entry must preserve missing evidence instead of implying empty basin evidence",
        ));
    }
    if !basin_candidates
        .clone()
        .any(|candidate| candidate.status == "nonCandidate")
    {
        invalid.push(generic_validation_example(
            "attractorEngineering.basinCandidates",
            "nonCandidate",
            "at least one basin entry must explicitly distinguish bounded non-candidate evidence",
        ));
    }

    for metric in [
        &section.basin_boundary_fragility,
        &section.trajectory_return_time,
        &section.observability_debt,
    ] {
        validate_bounded_attractor_metric(metric, invalid);
    }
}

fn validate_bounded_attractor_metric(
    metric: &DynamicsMeasuredValueV0,
    invalid: &mut Vec<ValidationExample>,
) {
    let Some(required_non_conclusion) = bounded_metric_non_conclusion(&metric.metric_id) else {
        invalid.push(generic_validation_example(
            &metric.metric_id,
            "metricId",
            "unsupported bounded Attractor Engineering metric slot",
        ));
        return;
    };
    if !metric
        .non_conclusions
        .iter()
        .any(|conclusion| conclusion == required_non_conclusion)
    {
        invalid.push(generic_validation_example(
            &metric.metric_id,
            "nonConclusions",
            "bounded basin / return / observability metrics must keep their non-conclusion boundary explicit",
        ));
    }

    if EVIDENCE_REQUIRED_STATUSES.contains(&metric.status.as_str()) {
        if metric.source_refs.is_empty() || has_blank_artifact_refs(&metric.source_refs) {
            invalid.push(generic_validation_example(
                &metric.metric_id,
                "sourceRefs",
                "measured, estimated, derived, and advisory bounded Attractor Engineering metrics must keep source refs",
            ));
        }
        if metric.measurement_boundary.aggregation_window.is_none()
            || metric.measurement_boundary.selected_region_refs.is_empty()
            || has_blank(&metric.measurement_boundary.selected_region_refs)
        {
            invalid.push(generic_validation_example(
                &metric.metric_id,
                "measurementBoundary",
                "finite trajectory, selected region, and bounded horizon must be explicit before emitting bounded Attractor Engineering evidence",
            ));
        }
    }

    let has_missing_evidence = !metric.measurement_boundary.missing_evidence.is_empty();
    if UNKNOWN_SUPPORT_RISK_STATES.contains(&metric.status.as_str()) && !has_missing_evidence {
        invalid.push(generic_validation_example(
            &metric.metric_id,
            "missingEvidence",
            "unmeasured, unavailable, private, notComparable, and outOfScope bounded Attractor Engineering metrics must record missing evidence",
        ));
    }
    if (metric.status == "measured" || metric.status == "derived")
        && has_missing_evidence
        && is_numeric_zero(metric.value.as_ref())
    {
        invalid.push(generic_validation_example(
            &metric.metric_id,
            "value",
            "bounded Attractor Engineering missing evidence must not be emitted as measured numeric zero",
        ));
    }
}

fn bounded_metric_non_conclusion(metric_id: &str) -> Option<&'static str> {
    match metric_id {
        "attractorEngineering.basinBoundaryFragility" => {
            Some(BASIN_BOUNDARY_FRAGILITY_NON_CONCLUSION)
        }
        "attractorEngineering.trajectoryReturnTime" => Some(TRAJECTORY_RETURN_TIME_NON_CONCLUSION),
        "attractorEngineering.observabilityDebt" => Some(OBSERVABILITY_DEBT_NON_CONCLUSION),
        _ => None,
    }
}

fn validate_support_risk_metric(
    owner: &str,
    field: &str,
    metric: &DynamicsMeasuredValueV0,
    invalid: &mut Vec<ValidationExample>,
) {
    if metric.metric_id.trim().is_empty()
        || metric.assumptions.is_empty()
        || has_blank(&metric.assumptions)
        || metric.non_conclusions.is_empty()
        || has_blank(&metric.non_conclusions)
    {
        invalid.push(generic_validation_example(
            owner,
            field,
            "support risk metric must record metric id, assumptions, and non-conclusions",
        ));
    }
    let source_refs_required = EVIDENCE_REQUIRED_STATUSES.contains(&metric.status.as_str());
    validate_boundary(
        owner,
        field,
        &metric.measurement_boundary,
        source_refs_required,
        invalid,
    );
}

fn validate_safe_preserving_confidence_distinction(
    section: &AttractorEngineeringMetricsV0,
    invalid: &mut Vec<ValidationExample>,
) {
    let required = [
        "safePreservingProved",
        "safePreservingMeasured",
        "safePreservingEstimated",
    ];
    let mut confidences = Vec::new();
    for risk_state in required {
        let Some(entry) = section
            .support_risk_entries
            .iter()
            .find(|entry| entry.risk_state == risk_state)
        else {
            invalid.push(generic_validation_example(
                "attractorEngineering.supportRiskEntries",
                risk_state,
                "safe-preserving proved, measured, and estimated risk states must all be represented",
            ));
            continue;
        };
        let Some(confidence) = &entry.risk_mass_contribution.confidence else {
            invalid.push(generic_validation_example(
                &entry.operation_id,
                "confidence",
                "safe-preserving proved, measured, and estimated states must record confidence",
            ));
            continue;
        };
        confidences.push(confidence.as_str());
    }
    if confidences.len() == required.len() {
        let distinct = confidences.iter().collect::<BTreeSet<_>>().len();
        if distinct != required.len() {
            invalid.push(generic_validation_example(
                "attractorEngineering.supportRiskEntries",
                "confidence",
                "safe-preserving proved, measured, and estimated states must not share one confidence level",
            ));
        }
    }
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
    let mut metrics: Vec<&DynamicsMeasuredValueV0> = report
        .trajectory_metrics
        .iter()
        .chain(report.force_metrics.iter())
        .chain(report.gap_metrics.iter())
        .chain(report.field_control_metrics.iter())
        .chain(report.ai_dynamics_metrics.iter())
        .collect();
    if let Some(section) = &report.attractor_engineering {
        metrics.extend([
            &section.support_risk_mass,
            &section.design_field_strength,
            &section.seed_attractor_strength,
            &section.field_shaping_delta,
            &section.basin_boundary_fragility,
            &section.trajectory_return_time,
            &section.observability_debt,
        ]);
        metrics.extend(section.vibe_coding_readiness_axes.iter());
        for entry in &section.support_risk_entries {
            metrics.push(&entry.support_weight);
            metrics.push(&entry.risk_mass_contribution);
        }
    }
    metrics
}

fn is_numeric_zero(value: Option<&serde_json::Value>) -> bool {
    match value {
        Some(serde_json::Value::Number(number)) => number.as_f64() == Some(0.0),
        Some(serde_json::Value::Object(object)) => {
            object.values().any(|nested| is_numeric_zero(Some(nested)))
        }
        _ => false,
    }
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

fn has_artifact_kind(refs: &[DynamicsArtifactRefV0], kind: &str) -> bool {
    refs.iter().any(|artifact_ref| artifact_ref.kind == kind)
}

fn string_set<const N: usize>(values: [&'static str; N]) -> BTreeSet<&'static str> {
    values.into_iter().collect()
}
