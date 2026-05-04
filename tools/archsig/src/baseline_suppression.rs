use std::collections::{BTreeMap, BTreeSet};

use crate::validation::{count_checks, generic_validation_example, validation_check};
use crate::{
    BASELINE_SUPPRESSION_REPORT_SCHEMA_VERSION, BaselineSuppressionInput,
    BaselineSuppressionReportV0, BaselineSuppressionSummary, CoverageGapDeltaEntryV0,
    CoverageGapDeltaV0, FeatureExtensionReportV0, FeatureReportCoverageGap,
    FeatureReportObstructionWitness, PolicyDecisionDeltaV0, PolicyDecisionReportV0,
    ReportArtifactRetentionManifestV0, RequiredAxisDeltaEntryV0, RequiredAxisDeltaV0,
    RiskDispositionV0, ValidationCheck, WitnessDeltaEntryV0, WitnessDeltaV0,
};

const REQUIRED_NON_CONCLUSIONS: [&str; 4] = [
    "baseline comparison is review evidence, not a Lean theorem",
    "suppressed and accepted-risk witnesses are not resolved witnesses",
    "missing baseline or private artifacts are not measured-zero evidence",
    "policy decision deltas do not approve architecture lawfulness",
];

pub fn build_baseline_suppression_report(
    baseline: &FeatureExtensionReportV0,
    baseline_path: &str,
    current: &FeatureExtensionReportV0,
    current_path: &str,
    baseline_policy_decision: Option<&PolicyDecisionReportV0>,
    baseline_policy_decision_path: Option<&str>,
    current_policy_decision: Option<&PolicyDecisionReportV0>,
    current_policy_decision_path: Option<&str>,
    retention_manifest: Option<&ReportArtifactRetentionManifestV0>,
    retention_manifest_path: Option<&str>,
    suppressions: &[RiskDispositionV0],
    accepted_risks: &[RiskDispositionV0],
) -> BaselineSuppressionReportV0 {
    let witness_delta = witness_delta(
        &baseline.introduced_obstruction_witnesses,
        &current.introduced_obstruction_witnesses,
    );
    let coverage_gap_delta = coverage_gap_delta(&baseline.coverage_gaps, &current.coverage_gaps);
    let required_axis_delta =
        required_axis_delta(baseline_policy_decision, current_policy_decision);
    let policy_decision_delta =
        policy_decision_delta(baseline_policy_decision, current_policy_decision);
    let current_witness_ids = witness_ids(&current.introduced_obstruction_witnesses);
    let normalized_suppressions =
        normalize_dispositions("suppression", suppressions, &current_witness_ids);
    let normalized_accepted_risks =
        normalize_dispositions("acceptedRisk", accepted_risks, &current_witness_ids);
    let checks = baseline_suppression_checks(
        &witness_delta,
        &coverage_gap_delta,
        &required_axis_delta,
        &policy_decision_delta,
        retention_manifest,
        &normalized_suppressions,
        &normalized_accepted_risks,
    );
    let suppressed_count = normalized_suppressions
        .iter()
        .filter(|disposition| {
            disposition.applies_to_current_witness && disposition.status == "suppressed"
        })
        .count();
    let accepted_risk_count = normalized_accepted_risks
        .iter()
        .filter(|disposition| {
            disposition.applies_to_current_witness && disposition.status == "acceptedRisk"
        })
        .count();
    let dispositioned_current_witnesses = normalized_suppressions
        .iter()
        .chain(normalized_accepted_risks.iter())
        .filter(|disposition| disposition.applies_to_current_witness)
        .map(|disposition| disposition.witness_ref.as_str())
        .collect::<BTreeSet<_>>();
    let unresolved_current_witness_count = current_witness_ids
        .iter()
        .filter(|witness_id| !dispositioned_current_witnesses.contains(witness_id.as_str()))
        .count();
    let result = if checks.iter().any(|check| check.result == "fail") {
        "fail"
    } else if checks.iter().any(|check| check.result == "warn") {
        "warn"
    } else if checks.iter().any(|check| check.result == "advisory") {
        "advisory"
    } else {
        "pass"
    }
    .to_string();

    BaselineSuppressionReportV0 {
        schema_version: BASELINE_SUPPRESSION_REPORT_SCHEMA_VERSION.to_string(),
        input: BaselineSuppressionInput {
            baseline_feature_report_schema_version: baseline.schema_version.clone(),
            baseline_feature_report_path: baseline_path.to_string(),
            current_feature_report_schema_version: current.schema_version.clone(),
            current_feature_report_path: current_path.to_string(),
            baseline_policy_decision_path: baseline_policy_decision_path.map(str::to_string),
            current_policy_decision_path: current_policy_decision_path.map(str::to_string),
            retention_manifest_ref: retention_manifest_path.map(str::to_string),
        },
        summary: BaselineSuppressionSummary {
            result,
            newly_introduced_witness_count: witness_delta.newly_introduced.len(),
            eliminated_witness_count: witness_delta.eliminated.len(),
            new_coverage_gap_count: coverage_gap_delta.newly_introduced.len(),
            eliminated_coverage_gap_count: coverage_gap_delta.eliminated.len(),
            required_axis_status_change_count: required_axis_delta.changes.len(),
            policy_decision_before: policy_decision_delta.baseline_decision.clone(),
            policy_decision_after: policy_decision_delta.current_decision.clone(),
            suppressed_count,
            accepted_risk_count,
            unresolved_current_witness_count,
            failed_check_count: count_checks(&checks, "fail"),
            warning_check_count: count_checks(&checks, "warn"),
            advisory_check_count: count_checks(&checks, "advisory"),
        },
        witness_delta,
        coverage_gap_delta,
        required_axis_delta,
        policy_decision_delta,
        suppressions: normalized_suppressions,
        accepted_risks: normalized_accepted_risks,
        checks,
        non_conclusions: REQUIRED_NON_CONCLUSIONS
            .iter()
            .map(|value| value.to_string())
            .collect(),
    }
}

fn witness_delta(
    baseline: &[FeatureReportObstructionWitness],
    current: &[FeatureReportObstructionWitness],
) -> WitnessDeltaV0 {
    let baseline_by_id = baseline
        .iter()
        .map(|witness| (witness.witness_id.as_str(), witness))
        .collect::<BTreeMap<_, _>>();
    let current_by_id = current
        .iter()
        .map(|witness| (witness.witness_id.as_str(), witness))
        .collect::<BTreeMap<_, _>>();

    WitnessDeltaV0 {
        newly_introduced: current_by_id
            .iter()
            .filter(|(witness_id, _)| !baseline_by_id.contains_key(**witness_id))
            .map(|(_, witness)| witness_delta_entry(witness, "newlyIntroduced"))
            .collect(),
        eliminated: baseline_by_id
            .iter()
            .filter(|(witness_id, _)| !current_by_id.contains_key(**witness_id))
            .map(|(_, witness)| witness_delta_entry(witness, "eliminated"))
            .collect(),
    }
}

fn witness_delta_entry(
    witness: &FeatureReportObstructionWitness,
    status: &str,
) -> WitnessDeltaEntryV0 {
    WitnessDeltaEntryV0 {
        witness_id: witness.witness_id.clone(),
        layer: witness.layer.clone(),
        kind: witness.kind.clone(),
        status: status.to_string(),
        measurement_boundary: witness.measurement_boundary.clone(),
        claim_classification: witness.claim_classification.clone(),
        reason: if status == "eliminated" {
            "witness is absent from current report".to_string()
        } else {
            "witness is absent from baseline report".to_string()
        },
    }
}

fn coverage_gap_delta(
    baseline: &[FeatureReportCoverageGap],
    current: &[FeatureReportCoverageGap],
) -> CoverageGapDeltaV0 {
    let baseline_gaps = coverage_gap_map(baseline);
    let current_gaps = coverage_gap_map(current);

    CoverageGapDeltaV0 {
        newly_introduced: current_gaps
            .iter()
            .filter(|(gap_ref, _)| !baseline_gaps.contains_key(*gap_ref))
            .map(|(_, entry)| entry.clone())
            .collect(),
        eliminated: baseline_gaps
            .iter()
            .filter(|(gap_ref, _)| !current_gaps.contains_key(*gap_ref))
            .map(|(_, entry)| {
                let mut entry = entry.clone();
                entry.status = "eliminated".to_string();
                entry.reason = "coverage gap is absent from current report".to_string();
                entry
            })
            .collect(),
    }
}

fn coverage_gap_map(
    gaps: &[FeatureReportCoverageGap],
) -> BTreeMap<String, CoverageGapDeltaEntryV0> {
    let mut entries = BTreeMap::new();
    for gap in gaps {
        for axis in &gap.unmeasured_axes {
            let gap_ref = format!("{}:{}", gap.layer, axis);
            entries.insert(
                gap_ref.clone(),
                CoverageGapDeltaEntryV0 {
                    gap_ref,
                    layer: gap.layer.clone(),
                    axis: axis.clone(),
                    status: "newlyIntroduced".to_string(),
                    measurement_boundary: gap.measurement_boundary.clone(),
                    allowed_by_policy: None,
                    reason: "coverage gap is absent from baseline report".to_string(),
                },
            );
        }
    }
    entries
}

fn required_axis_delta(
    baseline_policy_decision: Option<&PolicyDecisionReportV0>,
    current_policy_decision: Option<&PolicyDecisionReportV0>,
) -> RequiredAxisDeltaV0 {
    let baseline = baseline_policy_decision
        .map(|report| {
            report
                .required_axis_decisions
                .iter()
                .map(|decision| (decision.axis.as_str(), decision))
                .collect::<BTreeMap<_, _>>()
        })
        .unwrap_or_default();
    let current = current_policy_decision
        .map(|report| {
            report
                .required_axis_decisions
                .iter()
                .map(|decision| (decision.axis.as_str(), decision))
                .collect::<BTreeMap<_, _>>()
        })
        .unwrap_or_default();

    RequiredAxisDeltaV0 {
        changes: current
            .iter()
            .filter_map(|(axis, after)| {
                let before = baseline.get(axis);
                let changed = before
                    .map(|before| {
                        before.status != after.status
                            || before.actual_measurement_boundary
                                != after.actual_measurement_boundary
                            || before.value != after.value
                    })
                    .unwrap_or(true);
                changed.then(|| RequiredAxisDeltaEntryV0 {
                    axis: (*axis).to_string(),
                    before_status: before.map(|before| before.status.clone()),
                    after_status: after.status.clone(),
                    before_measurement_boundary: before
                        .map(|before| before.actual_measurement_boundary.clone()),
                    after_measurement_boundary: after.actual_measurement_boundary.clone(),
                    before_value: before.and_then(|before| before.value),
                    after_value: after.value,
                    reason: after.reason.clone(),
                })
            })
            .collect(),
    }
}

fn policy_decision_delta(
    baseline_policy_decision: Option<&PolicyDecisionReportV0>,
    current_policy_decision: Option<&PolicyDecisionReportV0>,
) -> PolicyDecisionDeltaV0 {
    let before = baseline_policy_decision.map(|report| &report.summary);
    let after = current_policy_decision.map(|report| &report.summary);
    let fail_delta = after.map(|summary| summary.fail_count as i64).unwrap_or(0)
        - before.map(|summary| summary.fail_count as i64).unwrap_or(0);
    let warn_delta = after.map(|summary| summary.warn_count as i64).unwrap_or(0)
        - before.map(|summary| summary.warn_count as i64).unwrap_or(0);
    let advisory_delta = after
        .map(|summary| summary.advisory_count as i64)
        .unwrap_or(0)
        - before
            .map(|summary| summary.advisory_count as i64)
            .unwrap_or(0);

    PolicyDecisionDeltaV0 {
        baseline_decision: before.map(|summary| summary.decision.clone()),
        current_decision: after.map(|summary| summary.decision.clone()),
        fail_delta,
        warn_delta,
        advisory_delta,
        required_action: if fail_delta > 0 {
            "review newly failing policy requirements before merge".to_string()
        } else if warn_delta > 0 || advisory_delta > 0 {
            "review newly visible warning or advisory signals".to_string()
        } else {
            "no policy decision worsening detected".to_string()
        },
    }
}

fn normalize_dispositions(
    kind: &str,
    dispositions: &[RiskDispositionV0],
    current_witness_ids: &BTreeSet<String>,
) -> Vec<RiskDispositionV0> {
    dispositions
        .iter()
        .map(|disposition| {
            let mut disposition = disposition.clone();
            disposition.kind = kind.to_string();
            disposition.applies_to_current_witness =
                current_witness_ids.contains(&disposition.witness_ref);
            if missing_disposition_metadata(&disposition) {
                disposition.status = "invalid".to_string();
                disposition.reviewer_status =
                    "metadata missing; reviewer cannot treat this as an approved disposition"
                        .to_string();
            } else if !disposition.applies_to_current_witness {
                disposition.status = "notApplicable".to_string();
                disposition.reviewer_status =
                    "disposition is retained for audit but does not match a current witness"
                        .to_string();
            } else if kind == "suppression" {
                disposition.status = "suppressed".to_string();
                disposition.reviewer_status =
                    "suppressed for review workflow; witness remains unresolved".to_string();
            } else {
                disposition.status = "acceptedRisk".to_string();
                disposition.reviewer_status =
                    "accepted risk for review workflow; witness remains unresolved".to_string();
            }
            ensure_disposition_non_conclusions(&mut disposition);
            disposition
        })
        .collect()
}

fn missing_disposition_metadata(disposition: &RiskDispositionV0) -> bool {
    disposition.disposition_id.trim().is_empty()
        || disposition.reason.trim().is_empty()
        || disposition.approved_by.trim().is_empty()
        || disposition.approved_at.trim().is_empty()
        || disposition.expires_at.trim().is_empty()
        || disposition.scope.trim().is_empty()
        || disposition.policy_ref.trim().is_empty()
        || disposition.witness_ref.trim().is_empty()
}

fn ensure_disposition_non_conclusions(disposition: &mut RiskDispositionV0) {
    for required in [
        "suppressed and accepted-risk witnesses are not resolved witnesses",
        "approval metadata is audit evidence, not a Lean theorem proof",
    ] {
        if !disposition
            .non_conclusions
            .iter()
            .any(|value| value == required)
        {
            disposition.non_conclusions.push(required.to_string());
        }
    }
}

fn baseline_suppression_checks(
    witness_delta: &WitnessDeltaV0,
    coverage_gap_delta: &CoverageGapDeltaV0,
    required_axis_delta: &RequiredAxisDeltaV0,
    policy_decision_delta: &PolicyDecisionDeltaV0,
    retention_manifest: Option<&ReportArtifactRetentionManifestV0>,
    suppressions: &[RiskDispositionV0],
    accepted_risks: &[RiskDispositionV0],
) -> Vec<ValidationCheck> {
    vec![
        advisory_count_check(
            "baseline-suppression-witness-delta",
            "newly introduced and eliminated witnesses are visible",
            witness_delta.newly_introduced.len() + witness_delta.eliminated.len(),
            "witness delta",
        ),
        advisory_count_check(
            "baseline-suppression-coverage-gap-delta",
            "coverage gap delta is visible",
            coverage_gap_delta.newly_introduced.len() + coverage_gap_delta.eliminated.len(),
            "coverage gap delta",
        ),
        advisory_count_check(
            "baseline-suppression-required-axis-delta",
            "required axis policy deltas are visible",
            required_axis_delta.changes.len(),
            "required axis delta",
        ),
        policy_delta_check(policy_decision_delta),
        retention_traceability_check(retention_manifest),
        disposition_metadata_check(suppressions, accepted_risks),
        disposition_non_resolution_check(suppressions, accepted_risks),
    ]
}

fn advisory_count_check(id: &str, title: &str, count: usize, target: &str) -> ValidationCheck {
    let mut check = validation_check(id, title, if count == 0 { "pass" } else { "advisory" });
    if count > 0 {
        check.count = Some(count);
        check.examples = vec![generic_validation_example(
            "baseline-current comparison",
            target,
            "delta requires reviewer attention",
        )];
    }
    check
}

fn policy_delta_check(delta: &PolicyDecisionDeltaV0) -> ValidationCheck {
    let result = if delta.fail_delta > 0 {
        "fail"
    } else if delta.warn_delta > 0 {
        "warn"
    } else if delta.advisory_delta > 0 {
        "advisory"
    } else {
        "pass"
    };
    let mut check = validation_check(
        "baseline-suppression-policy-decision-delta",
        "policy decision delta remains explicit",
        result,
    );
    if result != "pass" {
        check.examples = vec![generic_validation_example(
            delta.baseline_decision.as_deref().unwrap_or("none"),
            delta.current_decision.as_deref().unwrap_or("none"),
            &delta.required_action,
        )];
        check.count = Some(1);
    }
    check
}

fn retention_traceability_check(
    retention_manifest: Option<&ReportArtifactRetentionManifestV0>,
) -> ValidationCheck {
    let Some(manifest) = retention_manifest else {
        let mut check = validation_check(
            "baseline-suppression-retention-traceability",
            "baseline and suppression workflow refs are retained",
            "warn",
        );
        check.reason = Some("retention manifest was not provided".to_string());
        return check;
    };
    let ok = !manifest.traceability.baseline_comparison_refs.is_empty()
        && !manifest.traceability.suppression_workflow_refs.is_empty();
    let mut check = validation_check(
        "baseline-suppression-retention-traceability",
        "baseline and suppression workflow refs are retained",
        if ok { "pass" } else { "fail" },
    );
    if !ok {
        check.examples = vec![generic_validation_example(
            &manifest.retention_id,
            "traceability",
            "baselineComparisonRefs and suppressionWorkflowRefs must be present",
        )];
        check.count = Some(1);
    }
    check
}

fn disposition_metadata_check(
    suppressions: &[RiskDispositionV0],
    accepted_risks: &[RiskDispositionV0],
) -> ValidationCheck {
    let invalid = suppressions
        .iter()
        .chain(accepted_risks.iter())
        .filter(|disposition| disposition.status == "invalid")
        .map(|disposition| {
            generic_validation_example(
                &disposition.disposition_id,
                &disposition.witness_ref,
                "reason, approved_by, approved_at, expires_at, scope, policy_ref, and witness_ref are required",
            )
        })
        .collect::<Vec<_>>();
    let mut check = validation_check(
        "baseline-suppression-disposition-metadata",
        "suppression and accepted-risk metadata is complete",
        if invalid.is_empty() { "pass" } else { "fail" },
    );
    if !invalid.is_empty() {
        check.count = Some(invalid.len());
        check.examples = invalid;
    }
    check
}

fn disposition_non_resolution_check(
    suppressions: &[RiskDispositionV0],
    accepted_risks: &[RiskDispositionV0],
) -> ValidationCheck {
    let current_dispositions = suppressions
        .iter()
        .chain(accepted_risks.iter())
        .filter(|disposition| disposition.applies_to_current_witness)
        .count();
    let mut check = validation_check(
        "baseline-suppression-disposition-non-resolution",
        "suppressed and accepted-risk witnesses remain unresolved review items",
        if current_dispositions == 0 {
            "pass"
        } else {
            "advisory"
        },
    );
    if current_dispositions > 0 {
        check.count = Some(current_dispositions);
        check.examples = vec![generic_validation_example(
            "risk disposition",
            "current witness",
            "disposition changes reviewer workflow status but does not resolve the witness",
        )];
    }
    check
}

fn witness_ids(witnesses: &[FeatureReportObstructionWitness]) -> BTreeSet<String> {
    witnesses
        .iter()
        .map(|witness| witness.witness_id.clone())
        .collect()
}

#[cfg(test)]
mod tests {
    use crate::feature_report::build_feature_extension_report;
    use crate::test_support::air_fixture_document;

    use super::*;

    #[test]
    fn suppression_is_not_treated_as_resolution() {
        let baseline_air = air_fixture_document("good_extension.json");
        let current_air = air_fixture_document("hidden_interaction.json");
        let baseline = build_feature_extension_report(&baseline_air, "baseline.air.json");
        let current = build_feature_extension_report(&current_air, "current.air.json");
        let witness_ref = current.introduced_obstruction_witnesses[0]
            .witness_id
            .clone();
        let suppression = RiskDispositionV0 {
            disposition_id: "suppression-runtime-001".to_string(),
            kind: "suppression".to_string(),
            status: "requested".to_string(),
            reason: "runtime exposure reviewed in a separate rollout".to_string(),
            approved_by: "architecture-reviewer".to_string(),
            approved_at: "2026-05-05T00:00:00Z".to_string(),
            expires_at: "2026-06-05T00:00:00Z".to_string(),
            scope: "fixture runtime witness".to_string(),
            policy_ref: "aat-b7-default-organization-policy".to_string(),
            witness_ref,
            applies_to_current_witness: false,
            reviewer_status: String::new(),
            non_conclusions: Vec::new(),
        };

        let report = build_baseline_suppression_report(
            &baseline,
            "baseline.feature-report.json",
            &current,
            "current.feature-report.json",
            None,
            None,
            None,
            None,
            None,
            None,
            &[suppression],
            &[],
        );

        assert_eq!(
            report.schema_version,
            BASELINE_SUPPRESSION_REPORT_SCHEMA_VERSION
        );
        assert_eq!(report.summary.suppressed_count, 1);
        assert_eq!(report.suppressions[0].status, "suppressed");
        assert!(report.suppressions[0].non_conclusions.contains(
            &"suppressed and accepted-risk witnesses are not resolved witnesses".to_string()
        ));
        assert!(report.checks.iter().any(|check| {
            check.id == "baseline-suppression-disposition-non-resolution"
                && check.result == "advisory"
        }));
    }
}
