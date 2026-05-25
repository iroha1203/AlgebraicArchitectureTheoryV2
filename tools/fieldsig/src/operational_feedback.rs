use std::collections::{BTreeMap, BTreeSet};
use std::error::Error;
use std::fs;
use std::path::Path;

use crate::{
    ARCHITECTURE_DRIFT_LEDGER_SCHEMA_VERSION, ArchitectureDriftLedgerV0, BoundaryErosionSignalV0,
    CALIBRATION_REVIEW_RECORD_SCHEMA_VERSION, CalibrationConfidenceV0, CalibrationInputV0,
    CalibrationMissingEvidenceV0, CalibrationOutcomeRefV0, CalibrationReportFindingRefV0,
    CalibrationReviewAnalysisMetadataV0, CalibrationReviewRecordV0, CalibrationReviewerDecisionV0,
    DriftLedgerAggregationWindowV0, FEATURE_EXTENSION_REPORT_SCHEMA_VERSION,
    HYPOTHESIS_REFRESH_CYCLE_SCHEMA_VERSION, HypothesisChangeReasonV0, HypothesisDispositionV0,
    HypothesisProposedUpdateV0, HypothesisRefreshAnalysisMetadataV0, HypothesisRefreshCycleV0,
    HypothesisRefreshDecisionV0, HypothesisRefreshSourceMonitorRefV0,
    INCIDENT_CORRELATION_MONITOR_SCHEMA_VERSION, IncidentCorrelationAnalysisMetadataV0,
    IncidentCorrelationConfounderNoteV0, IncidentCorrelationMetricAxisV0,
    IncidentCorrelationMissingDataBoundaryV0, IncidentCorrelationMonitorV0,
    IncidentCorrelationObservationV0, IncidentCorrelationRefreshDecisionV0,
    IncidentCorrelationSourceRefV0, OUTCOME_LINKAGE_DATASET_SCHEMA_VERSION,
    OWNERSHIP_BOUNDARY_MONITOR_SCHEMA_VERSION, OutcomeLinkageDatasetV0, OutcomeMetric,
    OwnershipBoundaryAnalysisMetadataV0, OwnershipBoundaryMissingEvidenceV0,
    OwnershipBoundaryMonitorV0, OwnershipBoundarySourceRefV0, OwnershipScopeObservationV0,
    REPAIR_ADOPTION_RECORD_SCHEMA_VERSION, REPORT_OUTCOME_DAILY_LEDGER_SCHEMA_VERSION,
    RepairAdoptionAnalysisMetadataV0, RepairAdoptionDecisionV0, RepairAdoptionMissingEvidenceV0,
    RepairAdoptionRecordV0, RepairFollowUpOutcomeRefV0, RepairSideEffectNoteV0,
    RepairSuggestionRefV0, ReportOutcomeBoundaryCountV0, ReportOutcomeDailyBatchV0,
    ReportOutcomeDailyLedgerV0, ReportOutcomeLedgerAnalysisMetadataV0,
    ReportOutcomeMetricSummaryV0, ReportOutcomeRetentionPolicyV0, ReportOutcomeSourceReportRefV0,
    SchemaArtifactCompatibilityV0, SchemaCoverageExactnessBoundaryV0, SchemaFieldMappingV0,
    SchemaRequiredAssumptionV0, TEAM_THRESHOLD_POLICY_SCHEMA_VERSION, TeamThresholdAxisPolicyV0,
    TeamThresholdCalibrationSourceRefV0, TeamThresholdEffectivePeriodV0,
    TeamThresholdPolicyAnalysisMetadataV0, TeamThresholdPolicyV0, TeamThresholdRollbackPolicyV0,
    VersionedHypothesisRefV0,
};

const COMPATIBILITY_POLICY_REF: &str = "b9-compatibility-policy-v0";

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ReportOutcomeDailyLedgerInput {
    pub ledger_id: String,
    pub generated_at: String,
    pub aggregation_window: DriftLedgerAggregationWindowV0,
    pub retention_period_days: usize,
}

pub fn build_report_outcome_daily_ledger_from_files(
    outcome_linkage_dataset_path: &Path,
    drift_ledger_path: &Path,
    input: ReportOutcomeDailyLedgerInput,
) -> Result<ReportOutcomeDailyLedgerV0, Box<dyn Error>> {
    let outcome_dataset: OutcomeLinkageDatasetV0 =
        serde_json::from_str(&fs::read_to_string(outcome_linkage_dataset_path)?)?;
    let drift_ledger: ArchitectureDriftLedgerV0 =
        serde_json::from_str(&fs::read_to_string(drift_ledger_path)?)?;

    Ok(build_report_outcome_daily_ledger(
        &outcome_dataset,
        &outcome_linkage_dataset_path.display().to_string(),
        &drift_ledger,
        &drift_ledger_path.display().to_string(),
        input,
    ))
}

pub fn build_report_outcome_daily_ledger(
    outcome_dataset: &OutcomeLinkageDatasetV0,
    outcome_dataset_path: &str,
    drift_ledger: &ArchitectureDriftLedgerV0,
    drift_ledger_path: &str,
    input: ReportOutcomeDailyLedgerInput,
) -> ReportOutcomeDailyLedgerV0 {
    let mut source_report_refs = vec![
        source_report_ref(
            "outcome-linkage-dataset",
            outcome_dataset_path,
            OUTCOME_LINKAGE_DATASET_SCHEMA_VERSION,
            None,
            "PR-level bounded outcome observations",
        ),
        source_report_ref(
            "architecture-drift-ledger",
            drift_ledger_path,
            ARCHITECTURE_DRIFT_LEDGER_SCHEMA_VERSION,
            Some(&drift_ledger.ledger_id),
            "daily drift / suppression / retention operational state",
        ),
    ];
    source_report_refs.extend(feature_report_refs(outcome_dataset));

    let mut retained_artifact_refs: BTreeSet<String> = source_report_refs
        .iter()
        .map(|source| source.path.clone())
        .collect();
    retained_artifact_refs.extend(
        drift_ledger
            .entries
            .iter()
            .flat_map(|entry| entry.evidence_refs.iter().cloned()),
    );

    let batches = vec![build_daily_batch(
        outcome_dataset,
        outcome_dataset_path,
        drift_ledger,
        drift_ledger_path,
        &source_report_refs,
        &input.aggregation_window,
    )];

    let mut ledger = ReportOutcomeDailyLedgerV0 {
        schema_version: REPORT_OUTCOME_DAILY_LEDGER_SCHEMA_VERSION.to_string(),
        schema_compatibility: None,
        ledger_id: input.ledger_id,
        generated_at: input.generated_at,
        aggregation_window: input.aggregation_window,
        source_report_refs,
        retention: ReportOutcomeRetentionPolicyV0 {
            retention_manifest_ref: drift_ledger.retention_manifest_ref.clone(),
            retention_period_days: input.retention_period_days,
            retained_artifact_refs: retained_artifact_refs.into_iter().collect(),
            private_data_policy:
                "private source artifacts remain traceability refs and are not treated as measured-zero"
                    .to_string(),
            missing_data_policy:
                "missing outcome, incident, or retained-report data is preserved as unavailable / unmeasured"
                    .to_string(),
            non_conclusions: vec![
                "retention metadata is operational audit state, not semantic preservation"
                    .to_string(),
                "private retained artifacts do not imply absence of incident or rollback evidence"
                    .to_string(),
            ],
        },
        batches,
        analysis_metadata: ReportOutcomeLedgerAnalysisMetadataV0 {
            lean_status: "empirical hypothesis / tooling validation".to_string(),
            measurement_boundary:
                "daily operational ledger joining outcome linkage observations and Architecture Drift Ledger entries"
                    .to_string(),
            source_join_keys: vec![
                "repository owner/name".to_string(),
                "pull request number where present".to_string(),
                "drift ledger aggregation window".to_string(),
            ],
            non_conclusions: vec![
                "does not infer causal effects from report warnings to outcomes".to_string(),
                "does not promote empirical correlation to a Lean theorem claim".to_string(),
                "does not treat missing / private / unmeasured data as measured-zero evidence"
                    .to_string(),
                "does not rank architecture quality with a single score".to_string(),
            ],
        },
        non_conclusions: vec![
            "report outcome daily ledger is empirical / operational signal, not a Lean theorem"
                .to_string(),
            "schema migration pass is not semantic preservation".to_string(),
            "ledger accumulation does not imply extractor completeness".to_string(),
        ],
    };
    ledger.schema_compatibility = Some(report_outcome_daily_ledger_schema_compatibility_metadata(
        &ledger,
    ));
    ledger
}

fn build_daily_batch(
    outcome_dataset: &OutcomeLinkageDatasetV0,
    outcome_dataset_path: &str,
    drift_ledger: &ArchitectureDriftLedgerV0,
    drift_ledger_path: &str,
    source_report_refs: &[ReportOutcomeSourceReportRefV0],
    aggregation_window: &DriftLedgerAggregationWindowV0,
) -> ReportOutcomeDailyBatchV0 {
    let mut metrics = BTreeMap::<String, MetricAccumulator>::new();
    for record in &outcome_dataset.records {
        let outcome = &record.outcome_observation;
        add_review_metric(
            &mut metrics,
            "reviewCost.reviewCommentCount",
            &outcome.review_cost.review_comment_count,
        );
        add_review_metric(
            &mut metrics,
            "reviewCost.reviewThreadCount",
            &outcome.review_cost.review_thread_count,
        );
        add_review_metric(
            &mut metrics,
            "reviewCost.reviewRoundCount",
            &outcome.review_cost.review_round_count,
        );
        add_review_metric(
            &mut metrics,
            "reviewCost.reviewerCount",
            &outcome.review_cost.reviewer_count,
        );
        add_review_metric(
            &mut metrics,
            "reviewCost.firstReviewLatencyHours",
            &outcome.review_cost.first_review_latency_hours,
        );
        add_review_metric(
            &mut metrics,
            "reviewCost.approvalLatencyHours",
            &outcome.review_cost.approval_latency_hours,
        );
        add_review_metric(
            &mut metrics,
            "reviewCost.mergeLatencyHours",
            &outcome.review_cost.merge_latency_hours,
        );
        add_review_metric(
            &mut metrics,
            "followUpFixCount",
            &outcome.follow_up_fix_count,
        );
        add_review_metric(&mut metrics, "rollback", &outcome.rollback);
        add_review_metric(
            &mut metrics,
            "incidentAffectedComponentCount",
            &outcome.incident_affected_component_count,
        );
        add_review_metric(&mut metrics, "mttrHours", &outcome.mttr_hours);

        if !outcome.traceability.missing_or_private_data.is_empty() {
            let accumulator = metrics
                .entry("traceability.missingOrPrivateData".to_string())
                .or_default();
            accumulator.unavailable_count += outcome.traceability.missing_or_private_data.len();
            accumulator
                .source_refs
                .extend(outcome.traceability.missing_or_private_data.iter().cloned());
            accumulator
                .non_conclusions
                .extend(outcome.traceability.non_conclusions.iter().cloned());
            accumulator.add_boundary(
                "missingOrPrivate",
                outcome.traceability.missing_or_private_data.len(),
                outcome.traceability.missing_or_private_data.iter().cloned(),
                outcome.traceability.non_conclusions.iter().cloned(),
            );
        }
    }

    for entry in &drift_ledger.entries {
        if entry.measurement_boundary != "measuredZero" && entry.measurement_boundary != "measured"
        {
            let metric_ref = format!("driftLedger.{}", entry.metric_id);
            let accumulator = metrics.entry(metric_ref).or_default();
            accumulator.unmeasured_count += 1;
            accumulator
                .source_refs
                .extend(entry.evidence_refs.iter().cloned());
            accumulator
                .non_conclusions
                .extend(entry.non_conclusions.iter().cloned());
            accumulator.add_boundary(
                &entry.measurement_boundary,
                1,
                entry.evidence_refs.iter().cloned(),
                entry.non_conclusions.iter().cloned(),
            );
        }
    }

    let outcome_metric_summaries = metrics
        .iter()
        .map(|(metric_ref, accumulator)| accumulator.summary(metric_ref))
        .collect::<Vec<_>>();
    let missing_private_unmeasured_boundaries = metrics
        .iter()
        .flat_map(|(metric_ref, accumulator)| accumulator.boundary_counts(metric_ref))
        .collect::<Vec<_>>();

    let architecture_id = drift_ledger
        .entries
        .first()
        .map(|entry| entry.architecture_id.clone())
        .or_else(|| {
            outcome_dataset
                .records
                .first()
                .map(|record| record.feature_dataset_record_ref.architecture_id.clone())
        })
        .unwrap_or_else(|| "unknown".to_string());

    ReportOutcomeDailyBatchV0 {
        batch_id: batch_id_from_window(aggregation_window),
        architecture_id,
        outcome_dataset_ref: outcome_dataset_path.to_string(),
        drift_ledger_ref: drift_ledger_path.to_string(),
        outcome_record_count: outcome_dataset.records.len(),
        drift_entry_count: drift_ledger.entries.len(),
        source_report_refs: source_report_refs
            .iter()
            .map(|source| source.path.clone())
            .collect(),
        outcome_metric_summaries,
        missing_private_unmeasured_boundaries,
        non_conclusions: vec![
            "daily batch aggregation is operational monitoring, not causal proof".to_string(),
            "missing / private / unmeasured boundaries are preserved and not rounded to zero"
                .to_string(),
        ],
    }
}

fn batch_id_from_window(aggregation_window: &DriftLedgerAggregationWindowV0) -> String {
    let suffix = aggregation_window
        .window_end
        .as_deref()
        .or(aggregation_window.window_start.as_deref())
        .map(|timestamp| timestamp.chars().take(10).collect::<String>())
        .unwrap_or_else(|| "unbounded".to_string());
    format!("{}-batch-{suffix}", aggregation_window.window_kind)
}

fn feature_report_refs(
    outcome_dataset: &OutcomeLinkageDatasetV0,
) -> Vec<ReportOutcomeSourceReportRefV0> {
    let paths = outcome_dataset
        .records
        .iter()
        .map(|record| {
            record
                .feature_dataset_record_ref
                .feature_report_path
                .clone()
        })
        .collect::<BTreeSet<_>>();
    paths
        .into_iter()
        .map(|path| {
            source_report_ref(
                "feature-extension-report",
                &path,
                FEATURE_EXTENSION_REPORT_SCHEMA_VERSION,
                None,
                "source report referenced by feature extension dataset record",
            )
        })
        .collect()
}

fn source_report_ref(
    kind: &str,
    path: &str,
    schema_version: &str,
    report_id: Option<&str>,
    boundary: &str,
) -> ReportOutcomeSourceReportRefV0 {
    ReportOutcomeSourceReportRefV0 {
        kind: kind.to_string(),
        path: path.to_string(),
        schema_version: schema_version.to_string(),
        report_id: report_id.map(str::to_string),
        boundary: boundary.to_string(),
    }
}

fn add_review_metric<T>(
    metrics: &mut BTreeMap<String, MetricAccumulator>,
    metric_ref: &str,
    metric: &OutcomeMetric<T>,
) {
    let accumulator = metrics.entry(metric_ref.to_string()).or_default();
    match metric.boundary.as_str() {
        "measured" if metric.value.is_some() => accumulator.measured_count += 1,
        "private" => accumulator.private_count += 1,
        "unmeasured" => accumulator.unmeasured_count += 1,
        "unavailable" => accumulator.unavailable_count += 1,
        _ if metric.value.is_none() => accumulator.unavailable_count += 1,
        _ => accumulator.unmeasured_count += 1,
    }
    accumulator
        .source_refs
        .extend(metric.source_refs.iter().cloned());
    accumulator
        .non_conclusions
        .extend(metric.non_conclusions.iter().cloned());
    if let Some(reason) = &metric.reason {
        accumulator.non_conclusions.insert(reason.clone());
    }
    if metric.boundary != "measured" || metric.value.is_none() {
        accumulator.add_boundary(
            &metric.boundary,
            1,
            metric.source_refs.iter().cloned(),
            metric
                .non_conclusions
                .iter()
                .cloned()
                .chain(metric.reason.iter().cloned()),
        );
    }
}

#[derive(Default)]
struct MetricAccumulator {
    measured_count: usize,
    unavailable_count: usize,
    private_count: usize,
    unmeasured_count: usize,
    source_refs: BTreeSet<String>,
    non_conclusions: BTreeSet<String>,
    boundaries: BTreeMap<String, BoundaryAccumulator>,
}

impl MetricAccumulator {
    fn add_boundary(
        &mut self,
        boundary: &str,
        count: usize,
        source_refs: impl Iterator<Item = String>,
        non_conclusions: impl Iterator<Item = String>,
    ) {
        let boundary = self.boundaries.entry(boundary.to_string()).or_default();
        boundary.count += count;
        boundary.source_refs.extend(source_refs);
        boundary.non_conclusions.extend(non_conclusions);
    }

    fn summary(&self, metric_ref: &str) -> ReportOutcomeMetricSummaryV0 {
        ReportOutcomeMetricSummaryV0 {
            metric_ref: metric_ref.to_string(),
            measured_count: self.measured_count,
            unavailable_count: self.unavailable_count,
            private_count: self.private_count,
            unmeasured_count: self.unmeasured_count,
            source_refs: self.source_refs.iter().cloned().collect(),
            non_conclusions: self.non_conclusions.iter().cloned().collect(),
        }
    }

    fn boundary_counts(&self, metric_ref: &str) -> Vec<ReportOutcomeBoundaryCountV0> {
        self.boundaries
            .iter()
            .map(|(boundary, accumulator)| ReportOutcomeBoundaryCountV0 {
                boundary: boundary.clone(),
                metric_ref: metric_ref.to_string(),
                count: accumulator.count,
                source_refs: accumulator.source_refs.iter().cloned().collect(),
                non_conclusions: accumulator.non_conclusions.iter().cloned().collect(),
            })
            .collect()
    }
}

#[derive(Default)]
struct BoundaryAccumulator {
    count: usize,
    source_refs: BTreeSet<String>,
    non_conclusions: BTreeSet<String>,
}

pub fn report_outcome_daily_ledger_schema_compatibility_metadata(
    ledger: &ReportOutcomeDailyLedgerV0,
) -> SchemaArtifactCompatibilityV0 {
    let mut boundaries = vec![
        SchemaCoverageExactnessBoundaryV0 {
            axis_or_layer: "report-outcome-ledger.aggregation-window".to_string(),
            measurement_boundary: "operationalMetadata".to_string(),
            coverage_assumptions: vec![
                "aggregationWindow.windowStart and windowEnd delimit daily batch scope".to_string(),
                "sourceReportRefs preserve the reports included in the batch".to_string(),
            ],
            exactness_assumptions: vec![
                "aggregation window metadata is not evidence of semantic preservation".to_string(),
            ],
        },
        SchemaCoverageExactnessBoundaryV0 {
            axis_or_layer: "report-outcome-ledger.retention".to_string(),
            measurement_boundary: "operationalMetadata".to_string(),
            coverage_assumptions: vec![
                "retentionManifestRef is preserved when drift ledger provides one".to_string(),
                "retainedArtifactRefs preserve source report traceability".to_string(),
            ],
            exactness_assumptions: vec![
                "retention metadata is operational audit state, not formal proof state".to_string(),
            ],
        },
        SchemaCoverageExactnessBoundaryV0 {
            axis_or_layer: "report-outcome-ledger.missing-private-unmeasured".to_string(),
            measurement_boundary: "unmeasured".to_string(),
            coverage_assumptions: vec![
                "missing outcome observations remain unavailable".to_string(),
                "private incident / retained-report refs remain private".to_string(),
                "unmeasured drift entries remain unmeasured".to_string(),
            ],
            exactness_assumptions: vec![
                "missing / private / unmeasured data is never rounded to measuredZero".to_string(),
            ],
        },
    ];
    boundaries.extend(ledger.batches.iter().flat_map(|batch| {
        batch
            .missing_private_unmeasured_boundaries
            .iter()
            .map(|boundary| SchemaCoverageExactnessBoundaryV0 {
                axis_or_layer: format!("report-outcome-ledger.metric.{}", boundary.metric_ref),
                measurement_boundary: boundary.boundary.clone(),
                coverage_assumptions: boundary.source_refs.clone(),
                exactness_assumptions: boundary.non_conclusions.clone(),
            })
    }));

    SchemaArtifactCompatibilityV0 {
        artifact_id: "report-outcome-daily-ledger".to_string(),
        schema_version_name: REPORT_OUTCOME_DAILY_LEDGER_SCHEMA_VERSION.to_string(),
        compatibility_policy_ref: COMPATIBILITY_POLICY_REF.to_string(),
        field_mappings: vec![
            field_mapping(
                "aggregationWindow",
                "aggregationWindow",
                "stable",
                "preserve daily batch scope",
            ),
            field_mapping(
                "sourceReportRefs",
                "sourceReportRefs",
                "stable",
                "preserve report traceability",
            ),
            field_mapping(
                "retention",
                "retention",
                "stable",
                "preserve retention and private / missing data policy",
            ),
            field_mapping(
                "batches[].outcomeMetricSummaries",
                "batches[].outcomeMetricSummaries",
                "stable",
                "preserve metric counts by measurement boundary",
            ),
            field_mapping(
                "batches[].missingPrivateUnmeasuredBoundaries",
                "batches[].missingPrivateUnmeasuredBoundaries",
                "stable",
                "preserve missing / private / unmeasured boundary counts",
            ),
            field_mapping(
                "nonConclusions",
                "nonConclusions",
                "stable",
                "preserve empirical / operational guardrails",
            ),
        ],
        deprecated_fields: Vec::new(),
        required_assumptions: vec![
            required_assumption(
                "daily aggregation window is preserved",
                "schema compatibility review",
            ),
            required_assumption(
                "source report refs are preserved",
                "schema compatibility review",
            ),
            required_assumption(
                "retention and private data policies are preserved",
                "schema compatibility review",
            ),
            required_assumption(
                "missing private and unmeasured outcomes remain nonzero-boundary metadata",
                "schema compatibility review",
            ),
        ],
        coverage_exactness_boundaries: boundaries,
        non_conclusions: vec![
            "report outcome ledger schema compatibility metadata does not prove semantic preservation"
                .to_string(),
            "report outcome ledger schema compatibility metadata does not imply extractor completeness"
                .to_string(),
            "compatibility pass does not promote tooling evidence to a Lean theorem claim"
                .to_string(),
            "missing / private / unmeasured evidence is not measured-zero evidence".to_string(),
        ],
    }
}

pub fn static_calibration_review_record() -> CalibrationReviewRecordV0 {
    let mut record = CalibrationReviewRecordV0 {
        schema_version: CALIBRATION_REVIEW_RECORD_SCHEMA_VERSION.to_string(),
        schema_compatibility: None,
        record_id: "fixture-b10-calibration-review-false-positive-v0".to_string(),
        reviewed_at: "2026-05-05T09:00:00Z".to_string(),
        reviewer: "architecture-reviewer@example.com".to_string(),
        report_finding_refs: vec![CalibrationReportFindingRefV0 {
            report_ref: "tools/archsig/tests/fixtures/minimal/feature_extension_report.json"
                .to_string(),
            finding_id: "finding-runtime-private-evidence-warning".to_string(),
            metric_ref: "runtime.privateEvidenceCount".to_string(),
            finding_kind: "boundary-warning".to_string(),
            severity: "warn".to_string(),
            measurement_boundary: "unmeasured".to_string(),
        }],
        witness_refs: vec![
            "witness-hidden-runtime-edge".to_string(),
            "obstruction-witness:private-runtime-evidence".to_string(),
        ],
        reviewer_decision: CalibrationReviewerDecisionV0 {
            decision: "falsePositive".to_string(),
            reviewed_finding_status: "warning did not correspond to observed incident or rollback in the bounded review window".to_string(),
            recommended_calibration_action:
                "lower CI policy from fail to advisory for this metric until more outcome evidence is available"
                    .to_string(),
            calibration_scope: "checkout-service runtime private evidence warnings".to_string(),
            decision_refs: vec!["review-thread:calibration-2026-05-05".to_string()],
        },
        outcome_refs: vec![
            CalibrationOutcomeRefV0 {
                kind: "pull-request".to_string(),
                id: "example/repo#42".to_string(),
                url: Some("https://github.com/example/repo/pull/42".to_string()),
                boundary: "boundedOutcomeObservation".to_string(),
                metric_refs: vec![
                    "reviewCost.approvalLatencyHours".to_string(),
                    "followUpFixCount".to_string(),
                ],
            },
            CalibrationOutcomeRefV0 {
                kind: "daily-ledger".to_string(),
                id: "fixture-b10-report-outcome-daily-ledger".to_string(),
                url: None,
                boundary: "operationalFeedback".to_string(),
                metric_refs: vec!["driftLedger.private_runtime_evidence_count".to_string()],
            },
        ],
        rationale:
            "The report finding preserved an unmeasured private runtime boundary, but the bounded outcome window did not include corroborating incident, rollback, or follow-up fix evidence."
                .to_string(),
        confidence: CalibrationConfidenceV0 {
            level: "medium".to_string(),
            score: 0.64,
            evidence_boundary: "bounded empirical review; missing private runtime traces remain unmeasured".to_string(),
            non_conclusions: vec![
                "medium confidence does not prove the warning was semantically wrong".to_string(),
                "absence of observed incident evidence is not measured-zero incident evidence"
                    .to_string(),
            ],
        },
        missing_evidence: vec![
            CalibrationMissingEvidenceV0 {
                evidence_kind: "private-runtime-trace".to_string(),
                reason: "runtime trace is retained as a private artifact reference only".to_string(),
                boundary: "private".to_string(),
                follow_up_ref: "evidence-request:runtime-trace-redaction-policy".to_string(),
            },
            CalibrationMissingEvidenceV0 {
                evidence_kind: "post-merge-observation-window".to_string(),
                reason: "only one daily ledger window is available for this fixture".to_string(),
                boundary: "unavailable".to_string(),
                follow_up_ref: "calibration-backlog:extend-observation-window".to_string(),
            },
        ],
        calibration_input: CalibrationInputV0 {
            metric_refs: vec![
                "runtime.privateEvidenceCount".to_string(),
                "driftLedger.private_runtime_evidence_count".to_string(),
                "reviewCost.approvalLatencyHours".to_string(),
            ],
            threshold_policy_refs: vec!["ci-policy:runtime-private-evidence-advisory-v0".to_string()],
            source_ledger_refs: vec![
                "tools/archsig/tests/fixtures/minimal/report_outcome_daily_ledger.json"
                    .to_string(),
            ],
            downstream_issue_refs: vec!["#622".to_string()],
            non_conclusions: vec![
                "calibration input is an empirical signal for policy tuning".to_string(),
                "calibration input is not theorem precondition discharge".to_string(),
            ],
        },
        analysis_metadata: CalibrationReviewAnalysisMetadataV0 {
            lean_status: "empirical hypothesis / tooling validation".to_string(),
            measurement_boundary:
                "bounded false positive / false negative review over report findings and outcome refs"
                    .to_string(),
            calibration_boundary:
                "review decision can tune warning thresholds but cannot promote formal claims"
                    .to_string(),
            non_conclusions: vec![
                "reviewer decision does not prove or refute obstruction witness existence".to_string(),
                "metric calibration does not establish architecture lawfulness".to_string(),
                "false positive / false negative labels are bounded operational review outcomes"
                    .to_string(),
            ],
        },
        non_conclusions: vec![
            "calibration review record is empirical / operational signal, not a Lean theorem"
                .to_string(),
            "false positive review does not imply absence of architecture risk".to_string(),
            "false negative review does not imply causal proof from warning to outcome".to_string(),
            "missing or private evidence is not measured-zero evidence".to_string(),
        ],
    };
    record.schema_compatibility = Some(calibration_review_schema_compatibility_metadata());
    record
}

pub fn calibration_review_schema_compatibility_metadata() -> SchemaArtifactCompatibilityV0 {
    SchemaArtifactCompatibilityV0 {
        artifact_id: "calibration-review-record".to_string(),
        schema_version_name: CALIBRATION_REVIEW_RECORD_SCHEMA_VERSION.to_string(),
        compatibility_policy_ref: COMPATIBILITY_POLICY_REF.to_string(),
        field_mappings: vec![
            field_mapping(
                "reportFindingRefs",
                "reportFindingRefs",
                "stable",
                "preserve report finding traceability",
            ),
            field_mapping(
                "witnessRefs",
                "witnessRefs",
                "stable",
                "preserve witness traceability without proving witness semantics",
            ),
            field_mapping(
                "reviewerDecision",
                "reviewerDecision",
                "stable",
                "preserve false positive / false negative review decision",
            ),
            field_mapping(
                "outcomeRefs",
                "outcomeRefs",
                "stable",
                "preserve bounded outcome observation refs",
            ),
            field_mapping(
                "confidence",
                "confidence",
                "stable",
                "preserve empirical confidence boundary",
            ),
            field_mapping(
                "missingEvidence",
                "missingEvidence",
                "stable",
                "preserve missing / private evidence boundaries",
            ),
            field_mapping(
                "calibrationInput",
                "calibrationInput",
                "stable",
                "preserve policy tuning inputs as empirical signal",
            ),
            field_mapping(
                "nonConclusions",
                "nonConclusions",
                "stable",
                "preserve empirical / formal-claim guardrails",
            ),
        ],
        deprecated_fields: Vec::new(),
        required_assumptions: vec![
            required_assumption_for(
                "calibration-review-record",
                "report finding refs are preserved",
                "metric calibration review",
            ),
            required_assumption_for(
                "calibration-review-record",
                "reviewer decision boundary is preserved",
                "metric calibration review",
            ),
            required_assumption_for(
                "calibration-review-record",
                "missing evidence remains missing or private",
                "metric calibration review",
            ),
            required_assumption_for(
                "calibration-review-record",
                "calibration input is not theorem precondition discharge",
                "metric calibration review",
            ),
        ],
        coverage_exactness_boundaries: vec![
            SchemaCoverageExactnessBoundaryV0 {
                axis_or_layer: "calibration-review.report-finding".to_string(),
                measurement_boundary: "boundedReview".to_string(),
                coverage_assumptions: vec![
                    "reportFindingRefs identify the selected report warnings".to_string(),
                    "witnessRefs preserve witness traceability without re-proving them".to_string(),
                ],
                exactness_assumptions: vec![
                    "finding review is scoped to the selected outcome refs".to_string(),
                ],
            },
            SchemaCoverageExactnessBoundaryV0 {
                axis_or_layer: "calibration-review.decision".to_string(),
                measurement_boundary: "empiricalReview".to_string(),
                coverage_assumptions: vec![
                    "reviewerDecision records false positive / false negative classification"
                        .to_string(),
                    "confidence records empirical review strength".to_string(),
                ],
                exactness_assumptions: vec![
                    "review decision can tune policy but cannot promote a formal theorem claim"
                        .to_string(),
                ],
            },
            SchemaCoverageExactnessBoundaryV0 {
                axis_or_layer: "calibration-review.missing-evidence".to_string(),
                measurement_boundary: "unmeasured".to_string(),
                coverage_assumptions: vec![
                    "missingEvidence entries preserve unavailable and private evidence refs"
                        .to_string(),
                ],
                exactness_assumptions: vec![
                    "missing or private evidence is never rounded to measuredZero".to_string(),
                ],
            },
        ],
        non_conclusions: vec![
            "calibration review schema compatibility metadata does not prove semantic preservation"
                .to_string(),
            "calibration review schema compatibility metadata does not imply extractor completeness"
                .to_string(),
            "compatibility pass does not promote tooling evidence to a Lean theorem claim"
                .to_string(),
            "false positive / false negative review is empirical policy input, not causal proof"
                .to_string(),
        ],
    }
}

pub fn static_team_threshold_policy() -> TeamThresholdPolicyV0 {
    let mut policy = TeamThresholdPolicyV0 {
        schema_version: TEAM_THRESHOLD_POLICY_SCHEMA_VERSION.to_string(),
        schema_compatibility: None,
        policy_id: "fixture-b10-checkout-team-threshold-policy-v0".to_string(),
        organization_ref: "org:example-commerce".to_string(),
        team_ref: "team:checkout-platform".to_string(),
        effective_period: TeamThresholdEffectivePeriodV0 {
            starts_at: "2026-05-05T00:00:00Z".to_string(),
            ends_at: None,
            review_cadence: "monthly".to_string(),
            decision_ref: "architecture-review:threshold-tuning-2026-05".to_string(),
        },
        axis_thresholds: vec![
            TeamThresholdAxisPolicyV0 {
                axis_ref: "runtime.privateEvidenceCount".to_string(),
                metric_ref: "runtime.privateEvidenceCount".to_string(),
                warn_threshold: Some(1.0),
                fail_threshold: None,
                advisory_threshold: Some(1.0),
                ci_mode: "advisory".to_string(),
                calibration_boundary:
                    "private runtime evidence is monitored as advisory until observation coverage improves"
                        .to_string(),
                calibration_source_refs: vec![
                    "calibration-review:fixture-b10-calibration-review-false-positive-v0"
                        .to_string(),
                    "daily-ledger:fixture-b10-report-outcome-daily-ledger".to_string(),
                ],
                rationale:
                    "bounded review did not corroborate incident or rollback evidence, while private traces remain unmeasured"
                        .to_string(),
                non_conclusions: vec![
                    "advisory mode does not prove the runtime warning is semantically false"
                        .to_string(),
                    "private runtime evidence remains unmeasured rather than measured zero".to_string(),
                ],
            },
            TeamThresholdAxisPolicyV0 {
                axis_ref: "reviewCost.approvalLatencyHours".to_string(),
                metric_ref: "reviewCost.approvalLatencyHours".to_string(),
                warn_threshold: Some(24.0),
                fail_threshold: Some(72.0),
                advisory_threshold: None,
                ci_mode: "warn".to_string(),
                calibration_boundary:
                    "latency threshold is team-local empirical calibration, not a theorem precondition"
                        .to_string(),
                calibration_source_refs: vec![
                    "daily-ledger:fixture-b10-report-outcome-daily-ledger".to_string(),
                ],
                rationale:
                    "team review cadence accepts short-term warning thresholds while retaining fail threshold for prolonged review delay"
                        .to_string(),
                non_conclusions: vec![
                    "review latency threshold does not rank architecture quality as a single score"
                        .to_string(),
                    "CI warning mode does not discharge formal claim preconditions".to_string(),
                ],
            },
        ],
        calibration_source_refs: vec![
            TeamThresholdCalibrationSourceRefV0 {
                source_ref: "calibration-review:fixture-b10-calibration-review-false-positive-v0"
                    .to_string(),
                source_kind: "calibration-review-record".to_string(),
                path: "tools/archsig/tests/fixtures/minimal/calibration_review_record.json"
                    .to_string(),
                window_ref: "bounded review window 2026-05-04/2026-05-05".to_string(),
                boundary: "boundedEmpiricalReview".to_string(),
                non_conclusions: vec![
                    "false positive review is policy input, not causal proof".to_string(),
                ],
            },
            TeamThresholdCalibrationSourceRefV0 {
                source_ref: "daily-ledger:fixture-b10-report-outcome-daily-ledger".to_string(),
                source_kind: "report-outcome-daily-ledger".to_string(),
                path: "tools/archsig/tests/fixtures/minimal/report_outcome_daily_ledger.json"
                    .to_string(),
                window_ref: "daily ledger 2026-05-04/2026-05-05".to_string(),
                boundary: "operationalFeedback".to_string(),
                non_conclusions: vec![
                    "daily ledger correlation signal is not theorem evidence".to_string(),
                    "missing private outcome data is not measured-zero evidence".to_string(),
                ],
            },
        ],
        rollback_policy: TeamThresholdRollbackPolicyV0 {
            rollback_trigger:
                "two consecutive calibration reviews show false negatives or a linked rollback / incident within the bounded window"
                    .to_string(),
            fallback_policy_ref: "ci-policy:runtime-private-evidence-warn-v0".to_string(),
            approval_refs: vec![
                "architecture-review-board".to_string(),
                "checkout-platform-owner".to_string(),
            ],
            review_after: "next monthly calibration review".to_string(),
            non_conclusions: vec![
                "rollback of the policy mode is operational governance, not semantic preservation"
                    .to_string(),
                "incident linkage alone does not prove causality".to_string(),
            ],
        },
        analysis_metadata: TeamThresholdPolicyAnalysisMetadataV0 {
            lean_status: "empirical hypothesis / tooling validation".to_string(),
            policy_boundary:
                "team-specific CI threshold and mode selection for bounded operational monitoring"
                    .to_string(),
            calibration_boundary:
                "threshold tuning consumes calibration and ledger artifacts but cannot promote formal claims"
                    .to_string(),
            non_conclusions: vec![
                "team threshold policy is not a Lean theorem".to_string(),
                "policy tuning does not establish architecture lawfulness".to_string(),
                "team-local thresholds are not global architecture invariants".to_string(),
            ],
        },
        non_conclusions: vec![
            "team threshold policy is empirical calibration, not theorem precondition discharge"
                .to_string(),
            "warn / fail / advisory mode does not prove or refute obstruction witness existence"
                .to_string(),
            "team-specific threshold tuning does not imply extractor completeness".to_string(),
            "missing or private evidence is not measured-zero evidence".to_string(),
        ],
    };
    policy.schema_compatibility = Some(team_threshold_policy_schema_compatibility_metadata());
    policy
}

pub fn team_threshold_policy_schema_compatibility_metadata() -> SchemaArtifactCompatibilityV0 {
    SchemaArtifactCompatibilityV0 {
        artifact_id: "team-threshold-policy".to_string(),
        schema_version_name: TEAM_THRESHOLD_POLICY_SCHEMA_VERSION.to_string(),
        compatibility_policy_ref: COMPATIBILITY_POLICY_REF.to_string(),
        field_mappings: vec![
            field_mapping(
                "policyId",
                "policyId",
                "stable",
                "preserve team policy identity",
            ),
            field_mapping(
                "organizationRef",
                "organizationRef",
                "stable",
                "preserve organization scope",
            ),
            field_mapping("teamRef", "teamRef", "stable", "preserve team scope"),
            field_mapping(
                "effectivePeriod",
                "effectivePeriod",
                "stable",
                "preserve effective dates and review cadence",
            ),
            field_mapping(
                "axisThresholds",
                "axisThresholds",
                "stable",
                "preserve axis thresholds and CI modes separately",
            ),
            field_mapping(
                "calibrationSourceRefs",
                "calibrationSourceRefs",
                "stable",
                "preserve calibration source traceability",
            ),
            field_mapping(
                "rollbackPolicy",
                "rollbackPolicy",
                "stable",
                "preserve operational rollback governance",
            ),
            field_mapping(
                "nonConclusions",
                "nonConclusions",
                "stable",
                "preserve empirical / formal-claim guardrails",
            ),
        ],
        deprecated_fields: Vec::new(),
        required_assumptions: vec![
            required_assumption_for(
                "team-threshold-policy",
                "team scope and effective period are preserved",
                "team threshold tuning",
            ),
            required_assumption_for(
                "team-threshold-policy",
                "axis thresholds preserve warn fail and advisory modes",
                "team threshold tuning",
            ),
            required_assumption_for(
                "team-threshold-policy",
                "calibration sources remain empirical policy inputs",
                "team threshold tuning",
            ),
            required_assumption_for(
                "team-threshold-policy",
                "policy tuning is not theorem precondition discharge",
                "team threshold tuning",
            ),
        ],
        coverage_exactness_boundaries: vec![
            SchemaCoverageExactnessBoundaryV0 {
                axis_or_layer: "team-threshold-policy.axis-threshold".to_string(),
                measurement_boundary: "teamLocalEmpiricalCalibration".to_string(),
                coverage_assumptions: vec![
                    "axisThresholds identify metric refs and warn / fail / advisory modes"
                        .to_string(),
                ],
                exactness_assumptions: vec![
                    "thresholds are scoped to the stated team and effective period".to_string(),
                    "team thresholds do not become global architecture invariants".to_string(),
                ],
            },
            SchemaCoverageExactnessBoundaryV0 {
                axis_or_layer: "team-threshold-policy.calibration-source".to_string(),
                measurement_boundary: "boundedOperationalEvidence".to_string(),
                coverage_assumptions: vec![
                    "calibrationSourceRefs identify review and ledger inputs".to_string(),
                    "source boundary preserves missing / private / unavailable data".to_string(),
                ],
                exactness_assumptions: vec![
                    "calibration source refs do not prove causal relationships".to_string(),
                ],
            },
            SchemaCoverageExactnessBoundaryV0 {
                axis_or_layer: "team-threshold-policy.rollback".to_string(),
                measurement_boundary: "operationalGovernance".to_string(),
                coverage_assumptions: vec![
                    "rollbackPolicy records trigger, fallback policy, and approvals".to_string(),
                ],
                exactness_assumptions: vec![
                    "policy rollback does not prove semantic preservation".to_string(),
                ],
            },
        ],
        non_conclusions: vec![
            "team threshold policy schema compatibility metadata does not prove semantic preservation"
                .to_string(),
            "team threshold policy schema compatibility metadata does not imply extractor completeness"
                .to_string(),
            "compatibility pass does not promote tooling evidence to a Lean theorem claim"
                .to_string(),
            "team threshold tuning is empirical calibration, not architecture lawfulness"
                .to_string(),
        ],
    }
}

pub fn static_ownership_boundary_monitor() -> OwnershipBoundaryMonitorV0 {
    let mut monitor = OwnershipBoundaryMonitorV0 {
        schema_version: OWNERSHIP_BOUNDARY_MONITOR_SCHEMA_VERSION.to_string(),
        schema_compatibility: None,
        monitor_id: "fixture-b10-ownership-boundary-monitor-v0".to_string(),
        generated_at: "2026-05-05T10:00:00Z".to_string(),
        organization_ref: "org:example-commerce".to_string(),
        team_ref: "team:checkout-platform".to_string(),
        architecture_id: "checkout-service".to_string(),
        aggregation_window: DriftLedgerAggregationWindowV0 {
            window_start: Some("2026-05-04T00:00:00Z".to_string()),
            window_end: Some("2026-05-05T00:00:00Z".to_string()),
            window_kind: "daily".to_string(),
        },
        source_refs: vec![
            OwnershipBoundarySourceRefV0 {
                source_ref: "daily-ledger:fixture-b10-report-outcome-daily-ledger".to_string(),
                source_kind: "report-outcome-daily-ledger".to_string(),
                path: "tools/archsig/tests/fixtures/minimal/report_outcome_daily_ledger.json"
                    .to_string(),
                boundary: "operationalFeedback".to_string(),
                non_conclusions: vec![
                    "daily ledger input does not prove boundary erosion causality".to_string(),
                ],
            },
            OwnershipBoundarySourceRefV0 {
                source_ref: "threshold-policy:fixture-b10-checkout-team-threshold-policy-v0"
                    .to_string(),
                source_kind: "team-threshold-policy".to_string(),
                path: "tools/archsig/tests/fixtures/minimal/team_threshold_policy.json"
                    .to_string(),
                boundary: "teamLocalEmpiricalCalibration".to_string(),
                non_conclusions: vec![
                    "team-local thresholds are policy context, not global invariants".to_string(),
                ],
            },
        ],
        ownership_scopes: vec![
            OwnershipScopeObservationV0 {
                scope_ref: "ownership-scope:checkout-api".to_string(),
                owner_ref: "team:checkout-platform".to_string(),
                component_refs: vec![
                    "component:checkout.api".to_string(),
                    "component:checkout.payment_adapter".to_string(),
                ],
                boundary_policy_refs: vec![
                    "policy:checkout-owned-api-surface".to_string(),
                    "threshold-policy:fixture-b10-checkout-team-threshold-policy-v0".to_string(),
                ],
                observation_boundary: "boundedOperationalObservation".to_string(),
                evidence_refs: vec![
                    "CODEOWNERS:checkout-platform".to_string(),
                    "feature-report:checkout-private-runtime-warning".to_string(),
                ],
                missing_evidence_refs: vec!["private-runtime-trace:redacted".to_string()],
                non_conclusions: vec![
                    "ownership scope observation does not prove semantic ownership completeness"
                        .to_string(),
                    "private runtime trace redaction is not measured-zero boundary evidence"
                        .to_string(),
                ],
            },
            OwnershipScopeObservationV0 {
                scope_ref: "ownership-scope:billing-integration".to_string(),
                owner_ref: "team:billing-platform".to_string(),
                component_refs: vec!["component:billing.gateway".to_string()],
                boundary_policy_refs: vec!["policy:billing-owned-integration".to_string()],
                observation_boundary: "partialObservation".to_string(),
                evidence_refs: vec!["architecture-drift-ledger:billing-cross-team-edge".to_string()],
                missing_evidence_refs: vec!["CODEOWNERS:generated-client-owner".to_string()],
                non_conclusions: vec![
                    "partial ownership observation cannot infer absence of boundary erosion"
                        .to_string(),
                ],
            },
        ],
        boundary_erosion_signals: vec![
            BoundaryErosionSignalV0 {
                signal_id: "boundary-erosion:checkout-to-billing-runtime-edge".to_string(),
                boundary_ref: "ownership-scope:checkout-api -> ownership-scope:billing-integration"
                    .to_string(),
                metric_ref: "runtime.privateEvidenceCount".to_string(),
                observed_value: Some(1.0),
                severity: "watch".to_string(),
                trend: "newlyObserved".to_string(),
                measurement_boundary: "unmeasuredPrivateEvidence".to_string(),
                evidence_refs: vec![
                    "drift-ledger-entry:private_runtime_evidence_count".to_string(),
                    "feature-report:finding-runtime-private-evidence-warning".to_string(),
                ],
                recommended_follow_up_refs: vec![
                    "repair-suggestion:split-runtime-adapter-boundary".to_string(),
                    "evidence-request:runtime-trace-redaction-policy".to_string(),
                ],
                non_conclusions: vec![
                    "new runtime edge signal is boundary erosion monitoring, not causal proof"
                        .to_string(),
                    "unmeasured private evidence is not measured-zero evidence".to_string(),
                ],
            },
            BoundaryErosionSignalV0 {
                signal_id: "boundary-erosion:generated-client-owner-gap".to_string(),
                boundary_ref: "ownership-scope:billing-integration".to_string(),
                metric_ref: "ownership.missingOwnerEvidenceCount".to_string(),
                observed_value: None,
                severity: "advisory".to_string(),
                trend: "unavailable".to_string(),
                measurement_boundary: "unavailable".to_string(),
                evidence_refs: vec!["CODEOWNERS:generated-client-owner".to_string()],
                recommended_follow_up_refs: vec!["ownership-review:generated-client".to_string()],
                non_conclusions: vec![
                    "missing owner evidence does not imply unowned code".to_string(),
                ],
            },
        ],
        missing_evidence: vec![
            OwnershipBoundaryMissingEvidenceV0 {
                evidence_kind: "private-runtime-trace".to_string(),
                reason: "runtime edge evidence is retained as a private artifact reference only"
                    .to_string(),
                boundary: "private".to_string(),
                follow_up_ref: "evidence-request:runtime-trace-redaction-policy".to_string(),
            },
            OwnershipBoundaryMissingEvidenceV0 {
                evidence_kind: "generated-client-owner".to_string(),
                reason: "generated client ownership is not represented in the bounded fixture"
                    .to_string(),
                boundary: "unavailable".to_string(),
                follow_up_ref: "ownership-review:generated-client".to_string(),
            },
        ],
        analysis_metadata: OwnershipBoundaryAnalysisMetadataV0 {
            lean_status: "empirical hypothesis / tooling validation".to_string(),
            measurement_boundary:
                "bounded ownership and boundary erosion monitoring over operational feedback artifacts"
                    .to_string(),
            source_join_keys: vec![
                "organizationRef/teamRef".to_string(),
                "architectureId".to_string(),
                "component refs".to_string(),
                "aggregation window".to_string(),
            ],
            non_conclusions: vec![
                "ownership monitoring does not prove architecture lawfulness".to_string(),
                "boundary erosion signal does not prove causal incident or rollback linkage"
                    .to_string(),
                "missing / private evidence is preserved instead of rounded to measured zero"
                    .to_string(),
            ],
        },
        non_conclusions: vec![
            "ownership boundary monitor is empirical / operational signal, not a Lean theorem"
                .to_string(),
            "boundary erosion monitoring does not prove repair correctness".to_string(),
            "private or unavailable ownership evidence is not measured-zero evidence".to_string(),
            "monitor output does not imply extractor completeness".to_string(),
        ],
    };
    monitor.schema_compatibility = Some(ownership_boundary_monitor_schema_compatibility_metadata());
    monitor
}

pub fn ownership_boundary_monitor_schema_compatibility_metadata() -> SchemaArtifactCompatibilityV0 {
    SchemaArtifactCompatibilityV0 {
        artifact_id: "ownership-boundary-monitor".to_string(),
        schema_version_name: OWNERSHIP_BOUNDARY_MONITOR_SCHEMA_VERSION.to_string(),
        compatibility_policy_ref: COMPATIBILITY_POLICY_REF.to_string(),
        field_mappings: vec![
            field_mapping(
                "sourceRefs",
                "sourceRefs",
                "stable",
                "preserve operational source traceability",
            ),
            field_mapping(
                "ownershipScopes",
                "ownershipScopes",
                "stable",
                "preserve owner, component, policy, evidence, and missing evidence refs",
            ),
            field_mapping(
                "boundaryErosionSignals",
                "boundaryErosionSignals",
                "stable",
                "preserve boundary erosion signal identity and measurement boundary",
            ),
            field_mapping(
                "missingEvidence",
                "missingEvidence",
                "stable",
                "preserve private / unavailable ownership evidence boundaries",
            ),
            field_mapping(
                "nonConclusions",
                "nonConclusions",
                "stable",
                "preserve empirical / formal-claim guardrails",
            ),
        ],
        deprecated_fields: Vec::new(),
        required_assumptions: vec![
            required_assumption_for(
                "ownership-boundary-monitor",
                "ownership scopes preserve owner and component refs",
                "ownership boundary monitoring",
            ),
            required_assumption_for(
                "ownership-boundary-monitor",
                "boundary erosion signals preserve measurement boundary",
                "ownership boundary monitoring",
            ),
            required_assumption_for(
                "ownership-boundary-monitor",
                "missing ownership evidence remains private or unavailable",
                "ownership boundary monitoring",
            ),
        ],
        coverage_exactness_boundaries: vec![
            SchemaCoverageExactnessBoundaryV0 {
                axis_or_layer: "ownership-boundary-monitor.ownership-scope".to_string(),
                measurement_boundary: "boundedOperationalObservation".to_string(),
                coverage_assumptions: vec![
                    "ownershipScopes identify owner, component, and policy refs".to_string(),
                    "missingEvidenceRefs preserve unavailable ownership evidence".to_string(),
                ],
                exactness_assumptions: vec![
                    "bounded ownership observation is not ownership completeness".to_string(),
                ],
            },
            SchemaCoverageExactnessBoundaryV0 {
                axis_or_layer: "ownership-boundary-monitor.boundary-erosion".to_string(),
                measurement_boundary: "unmeasuredPrivateEvidence".to_string(),
                coverage_assumptions: vec![
                    "boundaryErosionSignals preserve metric refs and evidence refs".to_string(),
                ],
                exactness_assumptions: vec![
                    "boundary erosion monitoring does not prove causal incident linkage"
                        .to_string(),
                    "private evidence is not measured-zero evidence".to_string(),
                ],
            },
            SchemaCoverageExactnessBoundaryV0 {
                axis_or_layer: "ownership-boundary-monitor.missing-evidence".to_string(),
                measurement_boundary: "unavailable".to_string(),
                coverage_assumptions: vec![
                    "missingEvidence entries preserve private and unavailable boundaries"
                        .to_string(),
                ],
                exactness_assumptions: vec![
                    "missing ownership evidence does not imply unowned or risk-free components"
                        .to_string(),
                ],
            },
        ],
        non_conclusions: vec![
            "ownership boundary monitor schema compatibility metadata does not prove semantic preservation"
                .to_string(),
            "ownership boundary monitor schema compatibility metadata does not imply extractor completeness"
                .to_string(),
            "compatibility pass does not promote tooling evidence to a Lean theorem claim"
                .to_string(),
            "boundary erosion monitoring is empirical signal, not repair correctness".to_string(),
        ],
    }
}

pub fn static_repair_adoption_record() -> RepairAdoptionRecordV0 {
    let mut record = RepairAdoptionRecordV0 {
        schema_version: REPAIR_ADOPTION_RECORD_SCHEMA_VERSION.to_string(),
        schema_compatibility: None,
        record_id: "fixture-b10-repair-adoption-record-v0".to_string(),
        reviewed_at: "2026-05-05T11:00:00Z".to_string(),
        reviewer: "architecture-reviewer@example.com".to_string(),
        suggestion_refs: vec![RepairSuggestionRefV0 {
            suggestion_ref: "repair-suggestion:split-runtime-adapter-boundary".to_string(),
            source_report_ref:
                "tools/archsig/tests/fixtures/minimal/feature_extension_report.json".to_string(),
            obstruction_witness_ref: "obstruction-witness:private-runtime-evidence".to_string(),
            repair_rule_ref: "repair-rule:extract-runtime-adapter".to_string(),
            target_component_refs: vec![
                "component:checkout.payment_adapter".to_string(),
                "component:billing.gateway".to_string(),
            ],
            evidence_boundary: "suggestionFromUnmeasuredRuntimeEvidence".to_string(),
            non_conclusions: vec![
                "repair suggestion ref does not prove obstruction witness semantics".to_string(),
                "suggested repair is not a proof of global flatness preservation".to_string(),
            ],
        }],
        adoption_decision: RepairAdoptionDecisionV0 {
            decision: "deferred".to_string(),
            reason:
                "team accepted boundary review but deferred code movement until private runtime evidence can be redacted"
                    .to_string(),
            decision_refs: vec![
                "review-thread:repair-adoption-2026-05-05".to_string(),
                "issue:#623".to_string(),
            ],
            adopted_at: None,
            deferred_until: Some("2026-06-05T00:00:00Z".to_string()),
            non_conclusions: vec![
                "deferred adoption is operational workflow state, not repair failure proof"
                    .to_string(),
                "decision does not establish cost improvement or obstruction removal".to_string(),
            ],
        },
        follow_up_outcome_refs: vec![
            RepairFollowUpOutcomeRefV0 {
                outcome_ref: "daily-ledger:fixture-b10-report-outcome-daily-ledger".to_string(),
                outcome_kind: "report-outcome-daily-ledger".to_string(),
                boundary: "operationalFeedback".to_string(),
                metric_refs: vec![
                    "driftLedger.private_runtime_evidence_count".to_string(),
                    "reviewCost.approvalLatencyHours".to_string(),
                ],
                non_conclusions: vec![
                    "follow-up ledger signal is not causal evidence of repair effect".to_string(),
                ],
            },
            RepairFollowUpOutcomeRefV0 {
                outcome_ref: "ownership-monitor:fixture-b10-ownership-boundary-monitor-v0"
                    .to_string(),
                outcome_kind: "ownership-boundary-monitor".to_string(),
                boundary: "boundedOperationalObservation".to_string(),
                metric_refs: vec!["ownership.missingOwnerEvidenceCount".to_string()],
                non_conclusions: vec![
                    "ownership monitor signal does not prove boundary repair correctness"
                        .to_string(),
                ],
            },
        ],
        side_effect_notes: vec![RepairSideEffectNoteV0 {
            note_id: "side-effect:review-latency-risk".to_string(),
            affected_axis_refs: vec![
                "reviewCost.approvalLatencyHours".to_string(),
                "ownership.missingOwnerEvidenceCount".to_string(),
            ],
            description:
                "adapter extraction may require cross-team review and temporarily increase approval latency"
                    .to_string(),
            severity: "watch".to_string(),
            evidence_refs: vec![
                "team-threshold-policy:fixture-b10-checkout-team-threshold-policy-v0".to_string(),
            ],
            non_conclusions: vec![
                "side-effect note is risk tracking, not a prediction theorem".to_string(),
            ],
        }],
        missing_evidence: vec![
            RepairAdoptionMissingEvidenceV0 {
                evidence_kind: "post-adoption-outcome-window".to_string(),
                reason: "repair is deferred, so post-adoption outcome evidence is unavailable"
                    .to_string(),
                boundary: "unavailable".to_string(),
                follow_up_ref: "repair-review:post-adoption-window".to_string(),
            },
            RepairAdoptionMissingEvidenceV0 {
                evidence_kind: "private-runtime-trace".to_string(),
                reason: "runtime trace must be redacted before deciding the exact extraction"
                    .to_string(),
                boundary: "private".to_string(),
                follow_up_ref: "evidence-request:runtime-trace-redaction-policy".to_string(),
            },
        ],
        analysis_metadata: RepairAdoptionAnalysisMetadataV0 {
            lean_status: "empirical hypothesis / tooling validation".to_string(),
            adoption_boundary:
                "repair suggestion adoption state with follow-up outcome refs and missing evidence"
                    .to_string(),
            repair_correctness_boundary:
                "adoption tracking records workflow outcome and cannot prove repair correctness"
                    .to_string(),
            non_conclusions: vec![
                "repair adoption record is not a proof that obstruction was removed".to_string(),
                "repair adoption record is not a proof of global flatness preservation".to_string(),
                "repair adoption record is not a proof of cost improvement".to_string(),
            ],
        },
        non_conclusions: vec![
            "repair adoption tracking is empirical / operational signal, not a Lean theorem"
                .to_string(),
            "adopted, rejected, or deferred decision does not prove repair correctness".to_string(),
            "follow-up outcomes do not establish causal repair success".to_string(),
            "missing or private evidence is not measured-zero evidence".to_string(),
        ],
    };
    record.schema_compatibility = Some(repair_adoption_record_schema_compatibility_metadata());
    record
}

pub fn repair_adoption_record_schema_compatibility_metadata() -> SchemaArtifactCompatibilityV0 {
    SchemaArtifactCompatibilityV0 {
        artifact_id: "repair-adoption-record".to_string(),
        schema_version_name: REPAIR_ADOPTION_RECORD_SCHEMA_VERSION.to_string(),
        compatibility_policy_ref: COMPATIBILITY_POLICY_REF.to_string(),
        field_mappings: vec![
            field_mapping(
                "suggestionRefs",
                "suggestionRefs",
                "stable",
                "preserve repair suggestion, witness, rule, component, and evidence refs",
            ),
            field_mapping(
                "adoptionDecision",
                "adoptionDecision",
                "stable",
                "preserve adopted / rejected / deferred decision and reason",
            ),
            field_mapping(
                "followUpOutcomeRefs",
                "followUpOutcomeRefs",
                "stable",
                "preserve follow-up operational outcome refs",
            ),
            field_mapping(
                "sideEffectNotes",
                "sideEffectNotes",
                "stable",
                "preserve side-effect notes as empirical risk tracking",
            ),
            field_mapping(
                "missingEvidence",
                "missingEvidence",
                "stable",
                "preserve missing / private evidence boundaries",
            ),
            field_mapping(
                "nonConclusions",
                "nonConclusions",
                "stable",
                "preserve empirical / formal-claim guardrails",
            ),
        ],
        deprecated_fields: Vec::new(),
        required_assumptions: vec![
            required_assumption_for(
                "repair-adoption-record",
                "repair suggestion refs preserve witness and rule traceability",
                "repair adoption tracking",
            ),
            required_assumption_for(
                "repair-adoption-record",
                "adoption decision preserves adopted rejected or deferred status",
                "repair adoption tracking",
            ),
            required_assumption_for(
                "repair-adoption-record",
                "follow up outcomes remain operational signal",
                "repair adoption tracking",
            ),
            required_assumption_for(
                "repair-adoption-record",
                "missing repair evidence remains private or unavailable",
                "repair adoption tracking",
            ),
        ],
        coverage_exactness_boundaries: vec![
            SchemaCoverageExactnessBoundaryV0 {
                axis_or_layer: "repair-adoption.suggestion-ref".to_string(),
                measurement_boundary: "suggestionTraceability".to_string(),
                coverage_assumptions: vec![
                    "suggestionRefs preserve source report, witness, rule, and component refs"
                        .to_string(),
                ],
                exactness_assumptions: vec![
                    "repair suggestion traceability does not prove obstruction semantics"
                        .to_string(),
                ],
            },
            SchemaCoverageExactnessBoundaryV0 {
                axis_or_layer: "repair-adoption.decision".to_string(),
                measurement_boundary: "operationalWorkflowState".to_string(),
                coverage_assumptions: vec![
                    "adoptionDecision records adopted / rejected / deferred and reason"
                        .to_string(),
                ],
                exactness_assumptions: vec![
                    "workflow decision does not prove repair correctness".to_string(),
                ],
            },
            SchemaCoverageExactnessBoundaryV0 {
                axis_or_layer: "repair-adoption.missing-evidence".to_string(),
                measurement_boundary: "unavailable".to_string(),
                coverage_assumptions: vec![
                    "missingEvidence preserves unavailable and private follow-up evidence"
                        .to_string(),
                ],
                exactness_assumptions: vec![
                    "missing follow-up outcome evidence is not measured-zero evidence"
                        .to_string(),
                ],
            },
        ],
        non_conclusions: vec![
            "repair adoption schema compatibility metadata does not prove semantic preservation"
                .to_string(),
            "repair adoption schema compatibility metadata does not imply extractor completeness"
                .to_string(),
            "compatibility pass does not promote tooling evidence to a Lean theorem claim"
                .to_string(),
            "repair adoption tracking does not prove global flatness preservation or cost improvement"
                .to_string(),
        ],
    }
}

pub fn static_incident_correlation_monitor() -> IncidentCorrelationMonitorV0 {
    let mut monitor = IncidentCorrelationMonitorV0 {
        schema_version: INCIDENT_CORRELATION_MONITOR_SCHEMA_VERSION.to_string(),
        schema_compatibility: None,
        monitor_id: "fixture-b10-incident-correlation-monitor-v0".to_string(),
        generated_at: "2026-05-05T12:00:00Z".to_string(),
        organization_ref: "org:example".to_string(),
        team_ref: "team:checkout-platform".to_string(),
        architecture_id: "checkout-service".to_string(),
        correlation_window: DriftLedgerAggregationWindowV0 {
            window_start: Some("2026-04-01T00:00:00Z".to_string()),
            window_end: Some("2026-05-01T00:00:00Z".to_string()),
            window_kind: "monthly".to_string(),
        },
        source_refs: vec![
            IncidentCorrelationSourceRefV0 {
                source_ref: "report-outcome-daily-ledger:checkout-2026-04".to_string(),
                source_kind: "report-outcome-daily-ledger".to_string(),
                path: "tools/archsig/tests/fixtures/minimal/report_outcome_daily_ledger.json"
                    .to_string(),
                schema_version: REPORT_OUTCOME_DAILY_LEDGER_SCHEMA_VERSION.to_string(),
                boundary: "operationalFeedback".to_string(),
                non_conclusions: vec![
                    "daily ledger is an operational aggregation, not causal proof".to_string(),
                ],
            },
            IncidentCorrelationSourceRefV0 {
                source_ref: "calibration-review:runtime-private-evidence".to_string(),
                source_kind: "calibration-review-record".to_string(),
                path: "tools/archsig/tests/fixtures/minimal/calibration_review_record.json"
                    .to_string(),
                schema_version: CALIBRATION_REVIEW_RECORD_SCHEMA_VERSION.to_string(),
                boundary: "boundedEmpiricalReview".to_string(),
                non_conclusions: vec![
                    "reviewer calibration remains empirical policy evidence".to_string(),
                ],
            },
        ],
        metric_axes: vec![
            IncidentCorrelationMetricAxisV0 {
                axis_ref: "signature.runtimePropagation".to_string(),
                metric_ref: "runtime.privateEvidenceCount".to_string(),
                metric_kind: "report-warning".to_string(),
                measurement_boundary: "unmeasuredPrivateEvidence".to_string(),
                source_refs: vec!["feature-extension-report:finding-runtime-private".to_string()],
                non_conclusions: vec![
                    "private runtime evidence is not measured-zero runtime safety".to_string(),
                ],
            },
            IncidentCorrelationMetricAxisV0 {
                axis_ref: "outcome.rollback".to_string(),
                metric_ref: "rollback".to_string(),
                metric_kind: "operational-outcome".to_string(),
                measurement_boundary: "boundedOutcomeObservation".to_string(),
                source_refs: vec!["incident:inc-7".to_string(), "github:pulls/43".to_string()],
                non_conclusions: vec![
                    "rollback observation is not attributed to one obstruction by this monitor"
                        .to_string(),
                ],
            },
            IncidentCorrelationMetricAxisV0 {
                axis_ref: "outcome.mttr".to_string(),
                metric_ref: "mttrHours".to_string(),
                metric_kind: "operational-outcome".to_string(),
                measurement_boundary: "boundedOutcomeObservation".to_string(),
                source_refs: vec!["incident:inc-7".to_string()],
                non_conclusions: vec![
                    "MTTR is operational observation, not semantic completeness".to_string(),
                ],
            },
        ],
        correlations: vec![
            IncidentCorrelationObservationV0 {
                correlation_id: "corr-runtime-private-vs-mttr".to_string(),
                report_metric_ref: "runtime.privateEvidenceCount".to_string(),
                outcome_metric_ref: "mttrHours".to_string(),
                observed_direction: "positive".to_string(),
                coefficient: Some(0.42),
                sample_size: 12,
                confidence_boundary: "exploratorySmallSample".to_string(),
                source_refs: vec![
                    "report-outcome-daily-ledger:checkout-2026-04".to_string(),
                    "incident:inc-7".to_string(),
                ],
                non_conclusions: vec![
                    "positive correlation is not a causal claim".to_string(),
                    "small sample correlation does not promote a formal theorem claim".to_string(),
                ],
            },
            IncidentCorrelationObservationV0 {
                correlation_id: "corr-runtime-private-vs-rollback".to_string(),
                report_metric_ref: "runtime.privateEvidenceCount".to_string(),
                outcome_metric_ref: "rollback".to_string(),
                observed_direction: "insufficientEvidence".to_string(),
                coefficient: None,
                sample_size: 3,
                confidence_boundary: "insufficientRollbackSample".to_string(),
                source_refs: vec!["github:pulls/43".to_string()],
                non_conclusions: vec![
                    "insufficient rollback sample is not evidence of no rollback risk".to_string(),
                ],
            },
        ],
        confounder_notes: vec![
            IncidentCorrelationConfounderNoteV0 {
                note_id: "confounder-release-size".to_string(),
                confounder_kind: "release-size".to_string(),
                description: "Large releases may increase incident scope independently of Architecture Signature warnings.".to_string(),
                boundary: "knownConfounder".to_string(),
                mitigation_refs: vec!["analysis-plan:control-for-release-size".to_string()],
                non_conclusions: vec![
                    "uncontrolled confounders block causal interpretation".to_string(),
                ],
            },
            IncidentCorrelationConfounderNoteV0 {
                note_id: "confounder-private-incident-redaction".to_string(),
                confounder_kind: "private-data-redaction".to_string(),
                description: "Incident timelines are redacted in the fixture source.".to_string(),
                boundary: "private".to_string(),
                mitigation_refs: vec!["evidence-request:incident-timeline-redaction".to_string()],
                non_conclusions: vec![
                    "private redaction is not absence of incident evidence".to_string(),
                ],
            },
        ],
        missing_private_data: vec![
            IncidentCorrelationMissingDataBoundaryV0 {
                evidence_kind: "incident-timeline".to_string(),
                reason: "source incident timeline is private and represented only by a traceability ref".to_string(),
                boundary: "private".to_string(),
                follow_up_ref: "evidence-request:incident-timeline-redaction".to_string(),
                non_conclusions: vec![
                    "private incident timeline cannot discharge a theorem precondition".to_string(),
                ],
            },
            IncidentCorrelationMissingDataBoundaryV0 {
                evidence_kind: "longitudinal-sample".to_string(),
                reason: "fixture has one month of bounded outcome data".to_string(),
                boundary: "unavailable".to_string(),
                follow_up_ref: "b10-backlog:extend-correlation-window".to_string(),
                non_conclusions: vec![
                    "missing longitudinal data is not measured-zero correlation".to_string(),
                ],
            },
        ],
        refresh_decision: IncidentCorrelationRefreshDecisionV0 {
            decision: "refreshHypothesis".to_string(),
            decision_reason: "runtime exposure hypothesis should be narrowed to exploratory small-sample status".to_string(),
            hypothesis_cycle_ref: "hypothesis-refresh-cycle:runtime-exposure-2026-05".to_string(),
            decision_refs: vec!["analysis-review:2026-05-runtime-exposure".to_string()],
            non_conclusions: vec![
                "refresh decision changes empirical hypothesis tracking only".to_string(),
                "refresh decision does not promote a formal claim".to_string(),
            ],
        },
        analysis_metadata: IncidentCorrelationAnalysisMetadataV0 {
            lean_status: "empirical hypothesis / tooling validation".to_string(),
            measurement_boundary: "bounded operational correlation monitoring over report warnings, rollback, incidents, and MTTR".to_string(),
            correlation_boundary: "correlations are exploratory empirical signals with explicit confounder and missing-data boundaries".to_string(),
            source_join_keys: vec![
                "repository owner/name".to_string(),
                "pull request number where present".to_string(),
                "incident id".to_string(),
                "correlation window".to_string(),
            ],
            non_conclusions: vec![
                "does not infer causal effects from report warnings to incidents".to_string(),
                "does not promote empirical correlation to a Lean theorem claim".to_string(),
                "does not treat missing / private data as measured-zero evidence".to_string(),
            ],
        },
        non_conclusions: vec![
            "incident correlation monitor is empirical / operational signal, not a Lean theorem"
                .to_string(),
            "correlation does not imply causation".to_string(),
            "incident / rollback / MTTR observations do not prove extractor completeness".to_string(),
            "monitor output does not rank architecture quality with a single score".to_string(),
        ],
    };
    monitor.schema_compatibility = Some(incident_correlation_schema_compatibility_metadata());
    monitor
}

pub fn incident_correlation_schema_compatibility_metadata() -> SchemaArtifactCompatibilityV0 {
    SchemaArtifactCompatibilityV0 {
        artifact_id: "incident-correlation-monitor".to_string(),
        schema_version_name: INCIDENT_CORRELATION_MONITOR_SCHEMA_VERSION.to_string(),
        compatibility_policy_ref: COMPATIBILITY_POLICY_REF.to_string(),
        field_mappings: vec![
            field_mapping("correlationWindow", "correlationWindow", "stable", "preserve correlation window"),
            field_mapping("sourceRefs", "sourceRefs", "stable", "preserve source traceability"),
            field_mapping("metricAxes", "metricAxes", "stable", "preserve report and outcome metric axes"),
            field_mapping("correlations", "correlations", "stable", "preserve exploratory correlation observations"),
            field_mapping("confounderNotes", "confounderNotes", "stable", "preserve confounder boundaries"),
            field_mapping("missingPrivateData", "missingPrivateData", "stable", "preserve missing / private data boundary"),
            field_mapping("refreshDecision", "refreshDecision", "stable", "preserve empirical hypothesis refresh decision"),
            field_mapping("nonConclusions", "nonConclusions", "stable", "preserve correlation non-conclusions"),
        ],
        deprecated_fields: Vec::new(),
        required_assumptions: vec![
            required_assumption_for("incident-correlation-monitor", "correlation window is preserved", "incident correlation review"),
            required_assumption_for("incident-correlation-monitor", "source refs and metric axes are preserved", "incident correlation review"),
            required_assumption_for("incident-correlation-monitor", "confounder and missing private data boundaries are preserved", "incident correlation review"),
        ],
        coverage_exactness_boundaries: vec![
            SchemaCoverageExactnessBoundaryV0 {
                axis_or_layer: "incident-correlation.correlation-window".to_string(),
                measurement_boundary: "operationalMetadata".to_string(),
                coverage_assumptions: vec![
                    "windowStart and windowEnd delimit bounded correlation scope".to_string(),
                ],
                exactness_assumptions: vec!["window metadata is not causal evidence".to_string()],
            },
            SchemaCoverageExactnessBoundaryV0 {
                axis_or_layer: "incident-correlation.metric-axes".to_string(),
                measurement_boundary: "boundedOperationalObservation".to_string(),
                coverage_assumptions: vec![
                    "metric axes preserve report warning and outcome metric refs".to_string(),
                ],
                exactness_assumptions: vec![
                    "metric axis linkage is correlation input, not theorem precondition discharge"
                        .to_string(),
                ],
            },
            SchemaCoverageExactnessBoundaryV0 {
                axis_or_layer: "incident-correlation.confounders".to_string(),
                measurement_boundary: "unmeasured".to_string(),
                coverage_assumptions: vec![
                    "confounder notes remain explicit when causal interpretation is blocked".to_string(),
                ],
                exactness_assumptions: vec![
                    "uncontrolled confounders prevent causal proof".to_string(),
                ],
            },
            SchemaCoverageExactnessBoundaryV0 {
                axis_or_layer: "incident-correlation.missing-private-data".to_string(),
                measurement_boundary: "private".to_string(),
                coverage_assumptions: vec![
                    "private incident and rollback data remain traceability refs".to_string(),
                ],
                exactness_assumptions: vec![
                    "missing or private incident data is not measured-zero evidence".to_string(),
                ],
            },
        ],
        non_conclusions: vec![
            "incident correlation schema compatibility metadata does not prove causality"
                .to_string(),
            "incident correlation schema compatibility metadata does not imply extractor completeness"
                .to_string(),
            "compatibility pass does not promote tooling evidence to a Lean theorem claim"
                .to_string(),
        ],
    }
}

pub fn static_hypothesis_refresh_cycle() -> HypothesisRefreshCycleV0 {
    let mut cycle = HypothesisRefreshCycleV0 {
        schema_version: HYPOTHESIS_REFRESH_CYCLE_SCHEMA_VERSION.to_string(),
        schema_compatibility: None,
        cycle_id: "hypothesis-refresh-cycle:runtime-exposure-2026-05".to_string(),
        generated_at: "2026-05-05T12:30:00Z".to_string(),
        organization_ref: "org:example".to_string(),
        team_ref: "team:checkout-platform".to_string(),
        source_monitor_refs: vec![HypothesisRefreshSourceMonitorRefV0 {
            monitor_ref: "fixture-b10-incident-correlation-monitor-v0".to_string(),
            source_kind: "incident-correlation-monitor".to_string(),
            path: "tools/archsig/tests/fixtures/minimal/incident_correlation_monitor.json"
                .to_string(),
            boundary: "exploratoryOperationalCorrelation".to_string(),
            non_conclusions: vec!["monitor correlation is empirical input only".to_string()],
        }],
        versioned_hypothesis_refs: vec![
            VersionedHypothesisRefV0 {
                hypothesis_ref: "H5-runtime-exposure-incident-scope".to_string(),
                hypothesis_version: "2026-04".to_string(),
                status_before: "active".to_string(),
                evidence_boundary: "empirical hypothesis".to_string(),
                source_refs: vec!["docs/proof_obligations.md#empirical-hypotheses".to_string()],
                non_conclusions: vec!["active hypothesis is not a proved theorem".to_string()],
            },
            VersionedHypothesisRefV0 {
                hypothesis_ref: "H3-hidden-interaction-review-cost".to_string(),
                hypothesis_version: "2026-04".to_string(),
                status_before: "active".to_string(),
                evidence_boundary: "empirical hypothesis".to_string(),
                source_refs: vec!["docs/design/b6_empirical_hypothesis_evaluation.md".to_string()],
                non_conclusions: vec!["retained hypothesis remains empirical".to_string()],
            },
        ],
        change_reasons: vec![
            HypothesisChangeReasonV0 {
                reason_id: "reason-small-sample-mttr-correlation".to_string(),
                reason_kind: "small-sample-correlation".to_string(),
                description: "Runtime private evidence and MTTR correlation is positive but based on a small bounded window.".to_string(),
                source_refs: vec!["corr-runtime-private-vs-mttr".to_string()],
                boundary: "exploratoryCorrelation".to_string(),
                non_conclusions: vec![
                    "small-sample correlation cannot strengthen a formal claim".to_string(),
                ],
            },
            HypothesisChangeReasonV0 {
                reason_id: "reason-private-incident-boundary".to_string(),
                reason_kind: "private-data-boundary".to_string(),
                description: "Incident timeline evidence remains private and cannot be inspected by the fixture.".to_string(),
                source_refs: vec!["evidence-request:incident-timeline-redaction".to_string()],
                boundary: "private".to_string(),
                non_conclusions: vec![
                    "private data boundary is not absence of incident evidence".to_string(),
                ],
            },
        ],
        refresh_decision: HypothesisRefreshDecisionV0 {
            decision: "reviseAndRetain".to_string(),
            decision_reason: "Narrow H5 to exploratory runtime exposure monitoring until more incident windows are available.".to_string(),
            decision_refs: vec!["analysis-review:2026-05-runtime-exposure".to_string()],
            effective_hypothesis_version: "2026-05".to_string(),
            non_conclusions: vec![
                "refresh decision is empirical hypothesis management only".to_string(),
                "refresh decision does not discharge theorem preconditions".to_string(),
            ],
        },
        retained_hypotheses: vec![HypothesisDispositionV0 {
            hypothesis_ref: "H3-hidden-interaction-review-cost".to_string(),
            from_version: "2026-04".to_string(),
            to_version: Some("2026-05".to_string()),
            disposition: "retained".to_string(),
            rationale: "No contradictory operational signal was observed in this cycle.".to_string(),
            source_refs: vec!["calibration-review:runtime-private-evidence".to_string()],
            non_conclusions: vec!["retained does not mean proved".to_string()],
        }],
        rejected_hypotheses: vec![HypothesisDispositionV0 {
            hypothesis_ref: "H5-runtime-exposure-causes-incident".to_string(),
            from_version: "2026-04".to_string(),
            to_version: None,
            disposition: "rejected".to_string(),
            rationale: "Causal phrasing is rejected because the monitor records correlation with explicit confounders.".to_string(),
            source_refs: vec!["confounder-release-size".to_string()],
            non_conclusions: vec![
                "rejecting causal phrasing does not reject exploratory monitoring".to_string(),
            ],
        }],
        proposed_updates: vec![HypothesisProposedUpdateV0 {
            hypothesis_ref: "H5-runtime-exposure-incident-scope".to_string(),
            proposed_version: "2026-05".to_string(),
            change_summary: "Track runtime exposure as an exploratory correlation with incident scope and MTTR, not as a causal claim.".to_string(),
            required_follow_up_refs: vec![
                "b10-backlog:extend-correlation-window".to_string(),
                "analysis-plan:control-for-release-size".to_string(),
            ],
            non_conclusions: vec!["proposed update is not formal claim promotion".to_string()],
        }],
        analysis_metadata: HypothesisRefreshAnalysisMetadataV0 {
            lean_status: "empirical hypothesis / tooling validation".to_string(),
            refresh_boundary: "versioned empirical hypothesis management driven by operational feedback artifacts".to_string(),
            formal_claim_boundary: "hypothesis refresh can narrow or reject empirical claims but cannot promote Lean theorem claims".to_string(),
            non_conclusions: vec![
                "does not prove runtime exposure causes incidents".to_string(),
                "does not discharge theorem package preconditions".to_string(),
                "does not imply extractor completeness".to_string(),
            ],
        },
        non_conclusions: vec![
            "hypothesis refresh cycle is empirical research tracking, not a Lean theorem".to_string(),
            "retained hypothesis is not a proved claim".to_string(),
            "rejected causal phrasing is not evidence of zero operational risk".to_string(),
            "hypothesis refresh does not rank architecture quality with a single score".to_string(),
        ],
    };
    cycle.schema_compatibility = Some(hypothesis_refresh_schema_compatibility_metadata());
    cycle
}

pub fn hypothesis_refresh_schema_compatibility_metadata() -> SchemaArtifactCompatibilityV0 {
    SchemaArtifactCompatibilityV0 {
        artifact_id: "hypothesis-refresh-cycle".to_string(),
        schema_version_name: HYPOTHESIS_REFRESH_CYCLE_SCHEMA_VERSION.to_string(),
        compatibility_policy_ref: COMPATIBILITY_POLICY_REF.to_string(),
        field_mappings: vec![
            field_mapping("sourceMonitorRefs", "sourceMonitorRefs", "stable", "preserve monitor traceability"),
            field_mapping("versionedHypothesisRefs", "versionedHypothesisRefs", "stable", "preserve hypothesis version refs"),
            field_mapping("changeReasons", "changeReasons", "stable", "preserve refresh rationale"),
            field_mapping("refreshDecision", "refreshDecision", "stable", "preserve refresh decision boundary"),
            field_mapping("retainedHypotheses", "retainedHypotheses", "stable", "preserve retained hypothesis dispositions"),
            field_mapping("rejectedHypotheses", "rejectedHypotheses", "stable", "preserve rejected hypothesis dispositions"),
            field_mapping("nonConclusions", "nonConclusions", "stable", "preserve hypothesis / theorem boundary"),
        ],
        deprecated_fields: Vec::new(),
        required_assumptions: vec![
            required_assumption_for("hypothesis-refresh-cycle", "versioned hypothesis refs are preserved", "hypothesis refresh review"),
            required_assumption_for("hypothesis-refresh-cycle", "change reasons and refresh decision are preserved", "hypothesis refresh review"),
            required_assumption_for("hypothesis-refresh-cycle", "retained and rejected hypothesis dispositions are preserved", "hypothesis refresh review"),
        ],
        coverage_exactness_boundaries: vec![
            SchemaCoverageExactnessBoundaryV0 {
                axis_or_layer: "hypothesis-refresh.versioned-refs".to_string(),
                measurement_boundary: "empiricalHypothesis".to_string(),
                coverage_assumptions: vec![
                    "hypothesis refs preserve version and previous status".to_string(),
                ],
                exactness_assumptions: vec![
                    "hypothesis versioning is research tracking, not proof state".to_string(),
                ],
            },
            SchemaCoverageExactnessBoundaryV0 {
                axis_or_layer: "hypothesis-refresh.dispositions".to_string(),
                measurement_boundary: "empiricalHypothesis".to_string(),
                coverage_assumptions: vec![
                    "retained and rejected hypotheses preserve source refs and rationale".to_string(),
                ],
                exactness_assumptions: vec![
                    "retained does not mean proved and rejected causal phrasing does not mean zero risk"
                        .to_string(),
                ],
            },
            SchemaCoverageExactnessBoundaryV0 {
                axis_or_layer: "hypothesis-refresh.formal-claim-boundary".to_string(),
                measurement_boundary: "formalClaimBlocked".to_string(),
                coverage_assumptions: vec![
                    "non-conclusions preserve theorem promotion guardrails".to_string(),
                ],
                exactness_assumptions: vec![
                    "empirical refresh does not discharge theorem preconditions".to_string(),
                ],
            },
        ],
        non_conclusions: vec![
            "hypothesis refresh schema compatibility metadata does not prove any hypothesis"
                .to_string(),
            "hypothesis refresh schema compatibility metadata does not imply extractor completeness"
                .to_string(),
            "compatibility pass does not promote empirical evidence to a Lean theorem claim"
                .to_string(),
        ],
    }
}

fn field_mapping(
    source_field: &str,
    target_field: &str,
    mapping_kind: &str,
    required_review: &str,
) -> SchemaFieldMappingV0 {
    SchemaFieldMappingV0 {
        source_field: source_field.to_string(),
        target_field: target_field.to_string(),
        mapping_kind: mapping_kind.to_string(),
        required_review: required_review.to_string(),
    }
}

fn required_assumption(assumption: &str, required_for: &str) -> SchemaRequiredAssumptionV0 {
    required_assumption_for("report-outcome-daily-ledger", assumption, required_for)
}

fn required_assumption_for(
    applies_to: &str,
    assumption: &str,
    required_for: &str,
) -> SchemaRequiredAssumptionV0 {
    SchemaRequiredAssumptionV0 {
        assumption_id: assumption
            .chars()
            .map(|ch| {
                if ch.is_ascii_alphanumeric() {
                    ch.to_ascii_lowercase()
                } else {
                    '-'
                }
            })
            .collect::<String>()
            .split('-')
            .filter(|part| !part.is_empty())
            .collect::<Vec<_>>()
            .join("-"),
        applies_to: applies_to.to_string(),
        required_for: required_for.to_string(),
        fallback_when_missing:
            "report as missing or undischarged; do not infer semantic preservation".to_string(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn report_outcome_daily_ledger_fixture_parses() {
        let fixture: ReportOutcomeDailyLedgerV0 = serde_json::from_str(include_str!(
            "../tests/fixtures/minimal/report_outcome_daily_ledger.json"
        ))
        .expect("report outcome daily ledger fixture parses");
        assert_eq!(
            fixture.schema_version,
            REPORT_OUTCOME_DAILY_LEDGER_SCHEMA_VERSION
        );
        assert!(
            fixture
                .batches
                .iter()
                .flat_map(|batch| batch.missing_private_unmeasured_boundaries.iter())
                .any(|boundary| boundary.boundary == "unmeasured")
        );
    }

    #[test]
    fn calibration_review_record_fixture_parses() {
        let fixture: CalibrationReviewRecordV0 = serde_json::from_str(include_str!(
            "../tests/fixtures/minimal/calibration_review_record.json"
        ))
        .expect("calibration review record fixture parses");
        assert_eq!(
            fixture.schema_version,
            CALIBRATION_REVIEW_RECORD_SCHEMA_VERSION
        );
        assert!(
            fixture
                .missing_evidence
                .iter()
                .any(|evidence| evidence.boundary == "private")
        );
    }

    #[test]
    fn team_threshold_policy_fixture_parses() {
        let fixture: TeamThresholdPolicyV0 = serde_json::from_str(include_str!(
            "../tests/fixtures/minimal/team_threshold_policy.json"
        ))
        .expect("team threshold policy fixture parses");
        assert_eq!(fixture.schema_version, TEAM_THRESHOLD_POLICY_SCHEMA_VERSION);
        assert!(
            fixture
                .axis_thresholds
                .iter()
                .any(|axis| axis.ci_mode == "advisory")
        );
    }

    #[test]
    fn ownership_boundary_monitor_fixture_parses() {
        let fixture: OwnershipBoundaryMonitorV0 = serde_json::from_str(include_str!(
            "../tests/fixtures/minimal/ownership_boundary_monitor.json"
        ))
        .expect("ownership boundary monitor fixture parses");
        assert_eq!(
            fixture.schema_version,
            OWNERSHIP_BOUNDARY_MONITOR_SCHEMA_VERSION
        );
        assert!(
            fixture
                .boundary_erosion_signals
                .iter()
                .any(|signal| signal.measurement_boundary == "unmeasuredPrivateEvidence")
        );
    }

    #[test]
    fn repair_adoption_record_fixture_parses() {
        let fixture: RepairAdoptionRecordV0 = serde_json::from_str(include_str!(
            "../tests/fixtures/minimal/repair_adoption_record.json"
        ))
        .expect("repair adoption record fixture parses");
        assert_eq!(
            fixture.schema_version,
            REPAIR_ADOPTION_RECORD_SCHEMA_VERSION
        );
        assert_eq!(fixture.adoption_decision.decision, "deferred");
        assert!(
            fixture
                .missing_evidence
                .iter()
                .any(|evidence| evidence.boundary == "private")
        );
    }

    #[test]
    fn incident_correlation_monitor_fixture_parses() {
        let fixture: IncidentCorrelationMonitorV0 = serde_json::from_str(include_str!(
            "../tests/fixtures/minimal/incident_correlation_monitor.json"
        ))
        .expect("incident correlation monitor fixture parses");
        assert_eq!(
            fixture.schema_version,
            INCIDENT_CORRELATION_MONITOR_SCHEMA_VERSION
        );
        assert!(
            fixture
                .missing_private_data
                .iter()
                .any(|evidence| evidence.boundary == "private")
        );
        assert_eq!(fixture.refresh_decision.decision, "refreshHypothesis");
    }

    #[test]
    fn hypothesis_refresh_cycle_fixture_parses() {
        let fixture: HypothesisRefreshCycleV0 = serde_json::from_str(include_str!(
            "../tests/fixtures/minimal/hypothesis_refresh_cycle.json"
        ))
        .expect("hypothesis refresh cycle fixture parses");
        assert_eq!(
            fixture.schema_version,
            HYPOTHESIS_REFRESH_CYCLE_SCHEMA_VERSION
        );
        assert!(
            fixture
                .rejected_hypotheses
                .iter()
                .any(|hypothesis| hypothesis.disposition == "rejected")
        );
        assert_eq!(fixture.refresh_decision.decision, "reviseAndRetain");
    }
}
