use std::collections::{BTreeMap, BTreeSet};
use std::error::Error;
use std::fs;
use std::path::{Path, PathBuf};

use crate::{
    FEATURE_EXTENSION_DATASET_SCHEMA_VERSION, FeatureExtensionDatasetAnalysisMetadata,
    FeatureExtensionDatasetArtifactRefs, FeatureExtensionDatasetCoverageGap,
    FeatureExtensionDatasetRecordV0, FeatureExtensionDatasetV0, FeatureExtensionObstructionTaxon,
    FeatureExtensionPrHistoryRecordRef, FeatureExtensionRepairSuggestionAdoptionCandidate,
    FeatureExtensionReportV0, FeatureExtensionTheoremPreconditionBoundary, PrHistoryArtifactRef,
    PrHistoryDatasetV0, PrHistoryRecordV0, TheoremPreconditionCheck,
    TheoremPreconditionCheckReportV0, TheoremPreconditionCheckSummary,
};

pub fn build_feature_extension_dataset_from_files(
    pr_history_path: &Path,
    feature_report_paths: &[PathBuf],
    theorem_precondition_report_paths: &[PathBuf],
) -> Result<FeatureExtensionDatasetV0, Box<dyn Error>> {
    let pr_history: PrHistoryDatasetV0 =
        serde_json::from_str(&fs::read_to_string(pr_history_path)?)?;
    let feature_reports = feature_report_paths
        .iter()
        .map(|path| read_feature_report(path))
        .collect::<Result<Vec<_>, Box<dyn Error>>>()?;
    let theorem_reports = theorem_precondition_report_paths
        .iter()
        .map(|path| read_theorem_report(path))
        .collect::<Result<Vec<_>, Box<dyn Error>>>()?;

    build_feature_extension_dataset(
        pr_history,
        feature_reports,
        theorem_reports,
        theorem_precondition_report_paths,
    )
}

pub fn build_feature_extension_dataset(
    pr_history: PrHistoryDatasetV0,
    feature_reports: Vec<(String, FeatureExtensionReportV0)>,
    theorem_reports: Vec<(String, TheoremPreconditionCheckReportV0)>,
    theorem_report_paths: &[PathBuf],
) -> Result<FeatureExtensionDatasetV0, Box<dyn Error>> {
    let records = pr_history
        .records
        .iter()
        .map(|record| {
            build_feature_extension_dataset_record(
                record,
                &feature_reports,
                &theorem_reports,
                theorem_report_paths,
            )
        })
        .collect::<Result<Vec<_>, Box<dyn Error>>>()?;

    Ok(FeatureExtensionDatasetV0 {
        schema_version: FEATURE_EXTENSION_DATASET_SCHEMA_VERSION.to_string(),
        repository: pr_history.repository,
        records,
        analysis_metadata: FeatureExtensionDatasetAnalysisMetadata {
            lean_status: "empirical hypothesis / tooling validation".to_string(),
            measurement_boundary:
                "PR history records joined with Feature Extension Report and theorem precondition boundary artifacts"
                    .to_string(),
            join_keys: vec![
                "repository owner/name".to_string(),
                "pull request number".to_string(),
                "feature extension report artifact path".to_string(),
            ],
            non_conclusions: vec![
                "does not conclude architecture lawfulness".to_string(),
                "does not establish a Lean theorem claim".to_string(),
                "does not infer causal outcome effects from feature report classifications".to_string(),
                "does not treat missing or private artifacts as measured-zero evidence".to_string(),
            ],
        },
    })
}

fn build_feature_extension_dataset_record(
    record: &PrHistoryRecordV0,
    feature_reports: &[(String, FeatureExtensionReportV0)],
    theorem_reports: &[(String, TheoremPreconditionCheckReportV0)],
    theorem_report_paths: &[PathBuf],
) -> Result<FeatureExtensionDatasetRecordV0, Box<dyn Error>> {
    let (feature_report_ref, report) =
        matched_feature_report(record, feature_reports).ok_or_else(|| {
            format!(
                "no Feature Extension Report artifact matched PR #{}",
                record.pull_request.number
            )
        })?;
    let theorem_report = matched_theorem_report(report, theorem_reports);
    let theorem_report_refs =
        matched_theorem_report_refs(report, theorem_reports, theorem_report_paths);
    let (summary, checks) = theorem_report
        .map(|theorem_report| {
            (
                theorem_report.summary.clone(),
                theorem_report.checks.clone(),
            )
        })
        .unwrap_or_else(|| {
            (
                report.theorem_precondition_summary.clone(),
                report.theorem_precondition_checks.clone(),
            )
        });

    Ok(FeatureExtensionDatasetRecordV0 {
        pull_request: record.pull_request.clone(),
        pr_history_record_ref: FeatureExtensionPrHistoryRecordRef {
            pr_number: record.pull_request.number,
            base_commit: record.pull_request.base_commit.clone(),
            head_commit: record.pull_request.head_commit.clone(),
        },
        changed_components: record.changed_file_summary.changed_components.clone(),
        feature_report_ref: feature_report_ref.clone(),
        architecture_id: report.architecture_id.clone(),
        feature: report.feature.clone(),
        split_status: normalized_split_status(&report.split_status),
        claim_classification: report.review_summary.claim_classification.clone(),
        obstruction_witness_taxonomy: obstruction_taxonomy(report),
        coverage_gaps: report
            .coverage_gaps
            .iter()
            .map(|gap| FeatureExtensionDatasetCoverageGap {
                layer: gap.layer.clone(),
                measurement_boundary: gap.measurement_boundary.clone(),
                unmeasured_axes: gap.unmeasured_axes.clone(),
                unsupported_constructs: gap.unsupported_constructs.clone(),
                non_conclusions: gap.non_conclusions.clone(),
            })
            .collect(),
        repair_suggestion_adoption_candidates: report
            .repair_suggestions
            .iter()
            .map(
                |suggestion| FeatureExtensionRepairSuggestionAdoptionCandidate {
                    suggestion_id: suggestion.suggestion_id.clone(),
                    repair_rule_id: suggestion.repair_rule_id.clone(),
                    target_witness_kind: suggestion.target_witness_kind.clone(),
                    proposed_operation: suggestion.proposed_operation.clone(),
                    source_witness_refs: suggestion.source_witness_refs.clone(),
                    source_coverage_gap_refs: suggestion.source_coverage_gap_refs.clone(),
                    adoption_status: "candidate".to_string(),
                    required_preconditions: suggestion.required_preconditions.clone(),
                    traceability: suggestion.traceability.clone(),
                    non_conclusions: suggestion.non_conclusions.clone(),
                },
            )
            .collect(),
        theorem_precondition_boundary: theorem_precondition_boundary(summary, &checks),
        artifact_refs: FeatureExtensionDatasetArtifactRefs {
            signature_artifacts: record.artifact_refs.signature_artifacts.clone(),
            feature_extension_report: feature_report_ref.clone(),
            theorem_precondition_reports: theorem_report_refs,
        },
        non_conclusions: dataset_non_conclusions(report),
    })
}

fn read_feature_report(path: &Path) -> Result<(String, FeatureExtensionReportV0), Box<dyn Error>> {
    let report: FeatureExtensionReportV0 = serde_json::from_str(&fs::read_to_string(path)?)?;
    Ok((path.display().to_string(), report))
}

fn read_theorem_report(
    path: &Path,
) -> Result<(String, TheoremPreconditionCheckReportV0), Box<dyn Error>> {
    let report: TheoremPreconditionCheckReportV0 =
        serde_json::from_str(&fs::read_to_string(path)?)?;
    Ok((path.display().to_string(), report))
}

fn matched_feature_report<'a>(
    record: &'a PrHistoryRecordV0,
    feature_reports: &'a [(String, FeatureExtensionReportV0)],
) -> Option<(&'a PrHistoryArtifactRef, &'a FeatureExtensionReportV0)> {
    for artifact in &record.artifact_refs.feature_extension_reports {
        if let Some((_, report)) = feature_reports
            .iter()
            .find(|(path, _)| path == &artifact.path)
        {
            return Some((artifact, report));
        }
    }

    match (
        record.artifact_refs.feature_extension_reports.as_slice(),
        feature_reports,
    ) {
        ([artifact], [(_, report)]) => Some((artifact, report)),
        _ => None,
    }
}

fn matched_theorem_report<'a>(
    feature_report: &FeatureExtensionReportV0,
    theorem_reports: &'a [(String, TheoremPreconditionCheckReportV0)],
) -> Option<&'a TheoremPreconditionCheckReportV0> {
    theorem_reports
        .iter()
        .find(|(_, report)| {
            report.input.path == feature_report.input.path
                || report.input.architecture_id == feature_report.architecture_id
        })
        .map(|(_, report)| report)
}

fn matched_theorem_report_refs(
    feature_report: &FeatureExtensionReportV0,
    theorem_reports: &[(String, TheoremPreconditionCheckReportV0)],
    theorem_report_paths: &[PathBuf],
) -> Vec<String> {
    theorem_reports
        .iter()
        .zip(theorem_report_paths.iter())
        .filter(|((_, report), _)| {
            report.input.path == feature_report.input.path
                || report.input.architecture_id == feature_report.architecture_id
        })
        .map(|(_, path)| path.display().to_string())
        .collect()
}

fn normalized_split_status(split_status: &str) -> String {
    match split_status {
        "split" => "split".to_string(),
        "non_split" | "non-split" | "blocked" | "obstructed" => "non_split".to_string(),
        _ => "unmeasured".to_string(),
    }
}

fn obstruction_taxonomy(
    report: &FeatureExtensionReportV0,
) -> Vec<FeatureExtensionObstructionTaxon> {
    let mut grouped: BTreeMap<
        (String, String, String, String, String),
        (BTreeSet<String>, BTreeSet<String>),
    > = BTreeMap::new();
    for witness in &report.introduced_obstruction_witnesses {
        let key = (
            witness.kind.clone(),
            witness.layer.clone(),
            witness.claim_level.clone(),
            witness.claim_classification.clone(),
            witness.measurement_boundary.clone(),
        );
        let (witness_refs, components) = grouped.entry(key).or_default();
        witness_refs.insert(witness.witness_id.clone());
        components.extend(witness.components.iter().cloned());
    }

    grouped
        .into_iter()
        .map(
            |(
                (kind, layer, claim_level, claim_classification, measurement_boundary),
                (witness_refs, components),
            )| {
                let witness_refs: Vec<String> = witness_refs.into_iter().collect();
                FeatureExtensionObstructionTaxon {
                    kind,
                    layer,
                    claim_level,
                    claim_classification,
                    measurement_boundary,
                    witness_count: witness_refs.len(),
                    witness_refs,
                    components: components.into_iter().collect(),
                }
            },
        )
        .collect()
}

fn theorem_precondition_boundary(
    summary: TheoremPreconditionCheckSummary,
    checks: &[TheoremPreconditionCheck],
) -> FeatureExtensionTheoremPreconditionBoundary {
    let missing_preconditions: BTreeSet<String> = checks
        .iter()
        .flat_map(|check| check.missing_preconditions.iter().cloned())
        .collect();
    let blocked_claim_refs = checks
        .iter()
        .filter(|check| check.result == "blocked")
        .map(|check| check.claim_id.clone())
        .collect();
    let non_conclusions: BTreeSet<String> = checks
        .iter()
        .flat_map(|check| check.non_conclusions.iter().cloned())
        .chain([
            "theorem precondition checks are boundary metadata, not new Lean proofs".to_string(),
            "blocked formal claims are not treated as measured witnesses".to_string(),
        ])
        .collect();

    FeatureExtensionTheoremPreconditionBoundary {
        measured_witness_count: summary.measured_witness_count,
        formal_proved_claim_count: summary.formal_proved_claim_count,
        summary,
        missing_preconditions: missing_preconditions.into_iter().collect(),
        blocked_claim_refs,
        non_conclusions: non_conclusions.into_iter().collect(),
    }
}

fn dataset_non_conclusions(report: &FeatureExtensionReportV0) -> Vec<String> {
    let non_conclusions: BTreeSet<String> = report
        .non_conclusions
        .iter()
        .cloned()
        .chain([
            "split status is a correlation-analysis input, not a causal proof".to_string(),
            "repair suggestions are adoption candidates, not evidence of repair success"
                .to_string(),
            "coverage gaps are not measured-zero evidence".to_string(),
        ])
        .collect();
    non_conclusions.into_iter().collect()
}
