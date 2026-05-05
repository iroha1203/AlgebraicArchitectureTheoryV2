use std::collections::{BTreeMap, BTreeSet};
use std::error::Error;
use std::fs;
use std::path::Path;

use crate::{
    ARCHITECTURE_DRIFT_LEDGER_SCHEMA_VERSION, ArchitectureDriftLedgerV0,
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
        applies_to: "report-outcome-daily-ledger".to_string(),
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
}
