use std::collections::BTreeSet;

use serde_json::json;

use crate::validation::{count_checks, generic_validation_example, validation_check};
use crate::{
    ARCHITECTURE_DYNAMICS_METRICS_REPORT_SCHEMA_VERSION,
    ARCHITECTURE_DYNAMICS_METRICS_REPORT_VALIDATION_REPORT_SCHEMA_VERSION,
    ArchitectureDynamicsMetricsReportV0, ArchitectureDynamicsMetricsReportValidationInput,
    ArchitectureDynamicsMetricsReportValidationReportV0,
    ArchitectureDynamicsMetricsReportValidationSummary, AttractorEngineeringCandidateV0,
    AttractorEngineeringMetricsV0, AttractorEngineeringSignalV0, DynamicsAggregationWindowV0,
    DynamicsArtifactRefV0, DynamicsMeasuredValueV0, DynamicsMissingEvidenceV0, EXTRACTOR_VERSION,
    MeasurementBoundaryV0, PR_FORCE_REPORT_SCHEMA_VERSION, RepositoryRef,
    SelectedSignatureRegionV0, SupportRiskMassEntryV0, ValidationCheck, ValidationExample,
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

const REQUIRED_ATTRACTOR_NON_CONCLUSIONS: [&str; 7] = [
    "attractorEngineering is bounded tooling evidence, not a global attractor theorem",
    "unmeasured, unavailable, private, notComparable, and outOfScope Attractor Engineering metrics are not measured zero",
    "attractor and basin candidates are selected-region candidates, not global convergence claims",
    "field shaping signals are empirical tooling signals, not causal proof",
    "Attractor Engineering tooling does not conclude incident reduction",
    "Attractor Engineering tooling does not conclude an AI behavior theorem",
    "DesignFieldStrength is a selected empirical signal, not a truth claim about the architecture field",
];

const ALLOWED_ATTRACTOR_CANDIDATE_STATUSES: [&str; 5] = [
    "candidate",
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
        attractor_engineering: Some(attractor_engineering_section(
            window.clone(),
            vec![
                trajectory_ref.clone(),
                pr_force_ref.clone(),
                drift_ref.clone(),
            ],
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
) -> AttractorEngineeringMetricsV0 {
    let section_boundary = boundary(
        "attractor-engineering",
        &[
            "SupportRiskMass",
            "DesignFieldStrength",
            "SeedAttractorStrength",
            "BasinBoundaryFragility",
            "TrajectoryReturnTime",
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
                    "basin membership is finite observed tooling evidence",
                ],
                &[
                    "bounded basin candidate is not a global basin theorem",
                    "basin candidate status does not prove reachability for all states",
                ],
            ),
            attractor_candidate(
                "fixture:missing-evidence-basin-candidate",
                "basin-candidate",
                "unmeasured",
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
        support_risk_entries: support_risk_entries(section_boundary.clone()),
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
                ],
            ),
        ],
        seed_attractor_signals: vec![attractor_signal(
            "fixture:seed-attractor-canonical-example-signal",
            "SeedAttractorStrength",
            "canonical-example-copyability",
            source_refs.clone(),
            "advisory",
            Some("bounded-fixture-signal"),
            section_boundary.clone(),
            &[
                "canonical examples are treated as seed signal refs for the selected window",
                "copyability signal is not promoted to future patch convergence",
            ],
            &[
                "selected SeedAttractorStrength signal is not a convergence theorem",
                "seed attractor signal does not prove future patch distribution completeness",
            ],
        )],
        support_risk_mass: metric(
            "attractorEngineering.supportRiskMass",
            None,
            "unmeasured",
            None,
            Vec::new(),
            gap_boundary(
                "finite operation support weights are not retained in the MVP fixture",
                "unmeasured",
            ),
            &["SupportRiskMass needs finite operation support and risk labels"],
            &[
                "unmeasured SupportRiskMass is not zero support risk",
                SUPPORT_RISK_HISTORY_NON_CONCLUSION,
            ],
        ),
        design_field_strength: metric(
            "attractorEngineering.designFieldStrength",
            None,
            "outOfScope",
            None,
            Vec::new(),
            gap_boundary(
                "architecture field snapshot is outside this MVP fixture",
                "outOfScope",
            ),
            &["DesignFieldStrength needs field snapshot and policy context evidence"],
            &["outOfScope DesignFieldStrength is not weak field evidence"],
        ),
        seed_attractor_strength: metric(
            "attractorEngineering.seedAttractorStrength",
            None,
            "unavailable",
            None,
            source_refs.clone(),
            boundary(
                "attractor-engineering",
                &["SeedAttractorStrength"],
                source_refs.clone(),
                Some(window.clone()),
                &["canonical example evidence is not retained in this fixture"],
                &["seed attractor convergence theorem"],
            ),
            &["SeedAttractorStrength needs canonical examples and patch similarity evidence"],
            &["unavailable SeedAttractorStrength is not zero seed effect evidence"],
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
                source_refs.clone(),
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
            None,
            "unmeasured",
            None,
            Vec::new(),
            gap_boundary(
                "bounded perturbation simulation is not implemented in the MVP fixture",
                "unmeasured",
            ),
            &["BasinBoundaryFragility needs bounded perturbation simulation"],
            &[
                "unmeasured BasinBoundaryFragility is not stable basin evidence",
                BASIN_BOUNDARY_FRAGILITY_NON_CONCLUSION,
            ],
        ),
        trajectory_return_time: metric(
            "attractorEngineering.trajectoryReturnTime",
            None,
            "unavailable",
            None,
            Vec::new(),
            gap_boundary(
                "selected excursion and return observation are not retained in this fixture",
                "unavailable",
            ),
            &["TrajectoryReturnTime needs a selected excursion and return observation"],
            &[
                "unavailable TrajectoryReturnTime is not immediate-return evidence",
                TRAJECTORY_RETURN_TIME_NON_CONCLUSION,
            ],
        ),
        observability_debt: metric(
            "attractorEngineering.observabilityDebt",
            None,
            "notComparable",
            None,
            Vec::new(),
            gap_boundary(
                "observability coverage denominator is not comparable in this fixture",
                "notComparable",
            ),
            &["ObservabilityDebt needs comparable observed and latent support axes"],
            &[
                "notComparable ObservabilityDebt is not zero observability debt",
                OBSERVABILITY_DEBT_NON_CONCLUSION,
            ],
        ),
        measurement_boundary: section_boundary,
        non_conclusions: strings(&REQUIRED_ATTRACTOR_NON_CONCLUSIONS),
    }
}

fn support_risk_entries(section_boundary: MeasurementBoundaryV0) -> Vec<SupportRiskMassEntryV0> {
    vec![
        support_risk_entry(
            "fixture:preserve-boundary-law",
            "boundary-preserving-refactor",
            0.32,
            "proved",
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

#[allow(clippy::too_many_arguments)]
fn support_risk_entry(
    operation_id: &str,
    operation_kind: &str,
    support_weight: f64,
    preservation_precondition_status: &str,
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
        || section.support_risk_entries.is_empty()
        || section.design_field_signals.is_empty()
        || section.seed_attractor_signals.is_empty()
        || section.vibe_coding_readiness_axes.is_empty()
    {
        invalid.push(generic_validation_example(
            &report.report_id,
            "attractorEngineering",
            "selectedRegions, attractorCandidates, basinCandidates, supportRiskEntries, field signals, and readiness axes must be present",
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
    validate_boundary(
        &signal.signal_id,
        "measurementBoundary",
        &signal.measurement_boundary,
        true,
        invalid,
    );
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
        UNKNOWN_SUPPORT_RISK_STATES.contains(&candidate.status.as_str())
            && !candidate.measurement_boundary.missing_evidence.is_empty()
    }) {
        invalid.push(generic_validation_example(
            "attractorEngineering.basinCandidates",
            "missingEvidence",
            "at least one non-candidate basin entry must preserve missing evidence instead of implying empty basin evidence",
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

fn string_set<const N: usize>(values: [&'static str; N]) -> BTreeSet<&'static str> {
    values.into_iter().collect()
}
