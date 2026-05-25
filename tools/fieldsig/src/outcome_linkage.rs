use std::collections::BTreeSet;
use std::error::Error;
use std::fs;
use std::path::Path;

use crate::{
    FeatureExtensionDatasetRecordV0, FeatureExtensionDatasetV0,
    OUTCOME_LINKAGE_DATASET_SCHEMA_VERSION, OutcomeCorrelationInputs,
    OutcomeFeatureDatasetRecordRef, OutcomeLinkageAnalysisMetadata, OutcomeLinkageDatasetRecordV0,
    OutcomeLinkageDatasetV0, OutcomeLinkageInputV0, OutcomeMetric, OutcomeObservationV0,
    OutcomeTraceabilityRefs, PrHistoryArtifactRef, ReviewCostOutcome,
};

pub fn build_outcome_linkage_dataset_from_files(
    feature_dataset_path: &Path,
    outcome_input_path: &Path,
) -> Result<OutcomeLinkageDatasetV0, Box<dyn Error>> {
    let feature_dataset: FeatureExtensionDatasetV0 =
        serde_json::from_str(&fs::read_to_string(feature_dataset_path)?)?;
    let outcome_input: OutcomeLinkageInputV0 =
        serde_json::from_str(&fs::read_to_string(outcome_input_path)?)?;

    build_outcome_linkage_dataset(feature_dataset, outcome_input)
}

pub fn build_outcome_linkage_dataset(
    feature_dataset: FeatureExtensionDatasetV0,
    outcome_input: OutcomeLinkageInputV0,
) -> Result<OutcomeLinkageDatasetV0, Box<dyn Error>> {
    if feature_dataset.repository != outcome_input.repository {
        return Err("feature dataset repository does not match outcome input repository".into());
    }

    let records = feature_dataset
        .records
        .iter()
        .map(|record| {
            let observation = outcome_input
                .records
                .iter()
                .find(|observation| observation.pr_number == record.pull_request.number)
                .cloned()
                .unwrap_or_else(|| unavailable_observation(record.pull_request.number));
            build_outcome_linkage_dataset_record(record, observation)
        })
        .collect();

    Ok(OutcomeLinkageDatasetV0 {
        schema_version: OUTCOME_LINKAGE_DATASET_SCHEMA_VERSION.to_string(),
        repository: feature_dataset.repository,
        records,
        analysis_metadata: OutcomeLinkageAnalysisMetadata {
            lean_status: "empirical hypothesis / tooling validation".to_string(),
            measurement_boundary:
                "Feature extension dataset records joined with explicitly bounded outcome observations"
                    .to_string(),
            join_keys: vec![
                "repository owner/name".to_string(),
                "pull request number".to_string(),
            ],
            non_conclusions: analysis_non_conclusions(&outcome_input.analysis_metadata),
        },
    })
}

fn build_outcome_linkage_dataset_record(
    record: &FeatureExtensionDatasetRecordV0,
    outcome_observation: OutcomeObservationV0,
) -> OutcomeLinkageDatasetRecordV0 {
    OutcomeLinkageDatasetRecordV0 {
        pull_request: record.pull_request.clone(),
        feature_dataset_record_ref: OutcomeFeatureDatasetRecordRef {
            pr_number: record.pull_request.number,
            base_commit: record.pr_history_record_ref.base_commit.clone(),
            head_commit: record.pr_history_record_ref.head_commit.clone(),
            feature_report_path: record.feature_report_ref.path.clone(),
            architecture_id: record.architecture_id.clone(),
        },
        changed_components: record.changed_components.clone(),
        split_status: record.split_status.clone(),
        claim_classification: record.claim_classification.clone(),
        obstruction_witness_taxonomy: record.obstruction_witness_taxonomy.clone(),
        correlation_inputs: correlation_inputs(record),
        non_conclusions: record_non_conclusions(record, &outcome_observation),
        outcome_observation,
    }
}

fn correlation_inputs(record: &FeatureExtensionDatasetRecordV0) -> OutcomeCorrelationInputs {
    let witness_refs: BTreeSet<String> = record
        .obstruction_witness_taxonomy
        .iter()
        .flat_map(|taxon| taxon.witness_refs.iter().cloned())
        .collect();
    let witness_kinds: BTreeSet<String> = record
        .obstruction_witness_taxonomy
        .iter()
        .map(|taxon| taxon.kind.clone())
        .collect();

    OutcomeCorrelationInputs {
        obstruction_witness_refs: witness_refs.into_iter().collect(),
        obstruction_witness_kinds: witness_kinds.into_iter().collect(),
        outcome_metric_refs: vec![
            "reviewCost.reviewCommentCount".to_string(),
            "reviewCost.reviewThreadCount".to_string(),
            "reviewCost.reviewRoundCount".to_string(),
            "reviewCost.reviewerCount".to_string(),
            "reviewCost.firstReviewLatencyHours".to_string(),
            "reviewCost.approvalLatencyHours".to_string(),
            "reviewCost.mergeLatencyHours".to_string(),
            "followUpFixCount".to_string(),
            "rollback".to_string(),
            "incidentAffectedComponentCount".to_string(),
            "mttrHours".to_string(),
        ],
        measurement_boundary:
            "correlation-analysis input; outcome observations are not causal proof".to_string(),
        non_conclusions: vec![
            "does not infer obstruction witnesses caused the observed outcome".to_string(),
            "does not establish a Lean theorem claim from outcome data".to_string(),
            "does not treat unavailable outcome data as measured-zero evidence".to_string(),
        ],
    }
}

fn analysis_non_conclusions(metadata: &OutcomeLinkageAnalysisMetadata) -> Vec<String> {
    let non_conclusions: BTreeSet<String> = metadata
        .non_conclusions
        .iter()
        .cloned()
        .chain([
            "does not infer causal effects from obstruction profile to outcome".to_string(),
            "does not establish runtime, semantic, or extractor completeness".to_string(),
            "does not rank architecture quality with a single score".to_string(),
            "missing or private outcome data is not measured-zero evidence".to_string(),
        ])
        .collect();
    non_conclusions.into_iter().collect()
}

fn record_non_conclusions(
    record: &FeatureExtensionDatasetRecordV0,
    observation: &OutcomeObservationV0,
) -> Vec<String> {
    let non_conclusions: BTreeSet<String> = record
        .non_conclusions
        .iter()
        .cloned()
        .chain(observation.non_conclusions.iter().cloned())
        .chain(observation.traceability.non_conclusions.iter().cloned())
        .chain([
            "feature report classifications are linked to outcomes only as correlation inputs"
                .to_string(),
            "private or missing issue / incident refs do not imply absence of incidents"
                .to_string(),
        ])
        .collect();
    non_conclusions.into_iter().collect()
}

fn unavailable_observation(pr_number: usize) -> OutcomeObservationV0 {
    OutcomeObservationV0 {
        pr_number,
        review_cost: ReviewCostOutcome {
            review_comment_count: unavailable_metric("review comment count unavailable"),
            review_thread_count: unavailable_metric("review thread count unavailable"),
            review_round_count: unavailable_metric("review round count unavailable"),
            reviewer_count: unavailable_metric("reviewer count unavailable"),
            first_review_latency_hours: unavailable_metric("first review latency unavailable"),
            approval_latency_hours: unavailable_metric("approval latency unavailable"),
            merge_latency_hours: unavailable_metric("merge latency unavailable"),
        },
        follow_up_fix_count: unavailable_metric("follow-up fix count unavailable"),
        rollback: unavailable_metric("rollback observation unavailable"),
        incident_affected_component_count: unavailable_metric(
            "incident affected component count unavailable",
        ),
        mttr_hours: unavailable_metric("MTTR unavailable"),
        traceability: OutcomeTraceabilityRefs {
            pr_refs: Vec::new(),
            issue_refs: Vec::new(),
            incident_refs: Vec::new(),
            artifact_refs: Vec::<PrHistoryArtifactRef>::new(),
            missing_or_private_data: vec![
                "no matching outcome observation record was provided".to_string(),
            ],
            non_conclusions: vec![
                "missing outcome observation does not imply no follow-up fix, rollback, or incident"
                    .to_string(),
            ],
        },
        non_conclusions: vec![
            "unavailable outcome observation is not measured-zero evidence".to_string(),
        ],
    }
}

fn unavailable_metric<T>(reason: &str) -> OutcomeMetric<T> {
    OutcomeMetric {
        boundary: "unavailable".to_string(),
        value: None,
        reason: Some(reason.to_string()),
        source_refs: Vec::new(),
        non_conclusions: vec!["unavailable metric is not measured-zero evidence".to_string()],
    }
}
