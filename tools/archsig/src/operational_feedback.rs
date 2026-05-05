use std::collections::{BTreeMap, BTreeSet};
use std::error::Error;
use std::fs;
use std::path::Path;

use crate::{
    ARCHITECTURE_DRIFT_LEDGER_SCHEMA_VERSION, ArchitectureDriftLedgerV0,
    CALIBRATION_REVIEW_RECORD_SCHEMA_VERSION, CalibrationConfidenceV0, CalibrationInputV0,
    CalibrationMissingEvidenceV0, CalibrationOutcomeRefV0, CalibrationReportFindingRefV0,
    CalibrationReviewAnalysisMetadataV0, CalibrationReviewRecordV0, CalibrationReviewerDecisionV0,
    DriftLedgerAggregationWindowV0, FEATURE_EXTENSION_REPORT_SCHEMA_VERSION,
    OUTCOME_LINKAGE_DATASET_SCHEMA_VERSION, OutcomeLinkageDatasetV0, OutcomeMetric,
    REPORT_OUTCOME_DAILY_LEDGER_SCHEMA_VERSION, ReportOutcomeBoundaryCountV0,
    ReportOutcomeDailyBatchV0, ReportOutcomeDailyLedgerV0, ReportOutcomeLedgerAnalysisMetadataV0,
    ReportOutcomeMetricSummaryV0, ReportOutcomeRetentionPolicyV0, ReportOutcomeSourceReportRefV0,
    SchemaArtifactCompatibilityV0, SchemaCoverageExactnessBoundaryV0, SchemaFieldMappingV0,
    SchemaRequiredAssumptionV0,
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
}
