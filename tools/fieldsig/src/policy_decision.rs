use crate::validation::{count_checks, generic_validation_example, validation_check};
use crate::{
    CoverageGapPolicyDecisionV0, FeatureExtensionReportV0, MissingPreconditionPolicyDecisionV0,
    OrganizationPolicyV0, POLICY_DECISION_REPORT_SCHEMA_VERSION, PolicyDecisionInput,
    PolicyDecisionReportV0, PolicyDecisionSummary, RequiredAxisPolicyDecisionV0, ValidationCheck,
    WitnessPolicyDecisionV0,
};

const REQUIRED_NON_CONCLUSIONS: [&str; 4] = [
    "policy decision is CI decision support, not a Lean theorem",
    "policy decision does not approve architecture lawfulness",
    "advisory signals are not repair success evidence",
    "unmeasured axes are not treated as measured-zero risk",
];

pub fn build_policy_decision_report(
    feature_report: &FeatureExtensionReportV0,
    feature_report_path: &str,
    policy: &OrganizationPolicyV0,
    organization_policy_path: &str,
) -> PolicyDecisionReportV0 {
    let required_axis_decisions = required_axis_decisions(feature_report, policy);
    let missing_precondition_decisions = missing_precondition_decisions(feature_report, policy);
    let coverage_gap_decisions = coverage_gap_decisions(feature_report, policy);
    let witness_decisions = witness_decisions(feature_report);
    let checks = policy_decision_checks(
        &required_axis_decisions,
        &missing_precondition_decisions,
        &coverage_gap_decisions,
        &witness_decisions,
    );
    let fail_count = count_checks(&checks, "fail");
    let warn_count = count_checks(&checks, "warn");
    let advisory_count = count_checks(&checks, "advisory");
    let decision = if fail_count > 0 {
        "fail"
    } else if warn_count > 0 {
        "warn"
    } else if advisory_count > 0 {
        "advisory"
    } else {
        "pass"
    }
    .to_string();

    PolicyDecisionReportV0 {
        schema_version: POLICY_DECISION_REPORT_SCHEMA_VERSION.to_string(),
        input: PolicyDecisionInput {
            feature_report_schema_version: feature_report.schema_version.clone(),
            feature_report_path: feature_report_path.to_string(),
            organization_policy_schema_version: policy.schema_version.clone(),
            organization_policy_path: organization_policy_path.to_string(),
            policy_id: policy.policy_id.clone(),
            policy_version: policy.policy_version.clone(),
            scope: policy.scope.clone(),
        },
        summary: PolicyDecisionSummary {
            decision,
            fail_count,
            warn_count,
            advisory_count,
            required_axis_count: required_axis_decisions.len(),
            allowed_unmeasured_gap_count: coverage_gap_decisions
                .iter()
                .filter(|decision| decision.allowed_by_policy)
                .count(),
            missing_precondition_count: missing_precondition_decisions
                .iter()
                .map(|decision| decision.missing_preconditions.len())
                .sum(),
            measured_nonzero_witness_count: witness_decisions
                .iter()
                .filter(|decision| decision.measurement_boundary == "measuredNonzero")
                .count(),
        },
        required_axis_decisions,
        missing_precondition_decisions,
        coverage_gap_decisions,
        witness_decisions,
        checks,
        non_conclusions: REQUIRED_NON_CONCLUSIONS
            .iter()
            .map(|value| value.to_string())
            .collect(),
    }
}

fn required_axis_decisions(
    feature_report: &FeatureExtensionReportV0,
    policy: &OrganizationPolicyV0,
) -> Vec<RequiredAxisPolicyDecisionV0> {
    policy
        .required_axes
        .iter()
        .map(|required| {
            let observation = axis_observation(feature_report, &required.axis);
            let status = if observation.measurement_boundary != required.measurement_boundary {
                "fail"
            } else if required
                .max_allowed_value
                .zip(observation.value)
                .map(|(max_allowed, value)| value > max_allowed)
                .unwrap_or(false)
            {
                "fail"
            } else {
                "pass"
            };
            let reason = if observation.measurement_boundary == "unmeasured" {
                format!("required axis {} is unmeasured", required.axis)
            } else if observation.measurement_boundary != required.measurement_boundary {
                format!(
                    "required axis {} has measurement boundary {}, expected {}",
                    required.axis, observation.measurement_boundary, required.measurement_boundary
                )
            } else if required
                .max_allowed_value
                .zip(observation.value)
                .map(|(max_allowed, value)| value > max_allowed)
                .unwrap_or(false)
            {
                format!(
                    "required axis {} value {} exceeds maxAllowedValue {}",
                    required.axis,
                    observation.value.unwrap_or_default(),
                    required.max_allowed_value.unwrap_or_default()
                )
            } else {
                format!(
                    "required axis {} satisfies organization policy",
                    required.axis
                )
            };

            RequiredAxisPolicyDecisionV0 {
                axis: required.axis.clone(),
                status: status.to_string(),
                claim_level: required.claim_level.clone(),
                expected_measurement_boundary: required.measurement_boundary.clone(),
                actual_measurement_boundary: observation.measurement_boundary,
                value: observation.value,
                max_allowed_value: required.max_allowed_value,
                reason,
                required_preconditions: required.required_preconditions.clone(),
                non_conclusions: vec![
                    "required axis pass is not architecture lawfulness".to_string(),
                    "required axis pass is not a Lean theorem proof".to_string(),
                ],
            }
        })
        .collect()
}

fn missing_precondition_decisions(
    feature_report: &FeatureExtensionReportV0,
    policy: &OrganizationPolicyV0,
) -> Vec<MissingPreconditionPolicyDecisionV0> {
    let mut decisions = Vec::new();
    for required in &policy.required_theorem_preconditions {
        let matching_checks = feature_report
            .theorem_precondition_checks
            .iter()
            .filter(|check| {
                check.subject_ref == required.subject_ref
                    && check.claim_level == required.claim_level
            })
            .collect::<Vec<_>>();
        if matching_checks.is_empty() {
            decisions.push(MissingPreconditionPolicyDecisionV0 {
                subject_ref: required.subject_ref.clone(),
                claim_id: "missing-required-formal-claim".to_string(),
                status: "fail".to_string(),
                missing_preconditions: required.required_preconditions.clone(),
                theorem_refs: required.theorem_refs.clone(),
                reason: "required theorem precondition check is absent".to_string(),
                non_conclusions: vec![
                    "policy configuration does not discharge theorem preconditions".to_string(),
                    "absent formal claim is not promoted by CI".to_string(),
                ],
            });
            continue;
        }
        decisions.extend(
            matching_checks
                .into_iter()
                .filter_map(|check| {
                    (!check.missing_preconditions.is_empty() || check.result == "warn").then(|| {
                        MissingPreconditionPolicyDecisionV0 {
                            subject_ref: check.subject_ref.clone(),
                            claim_id: check.claim_id.clone(),
                            status: "fail".to_string(),
                            missing_preconditions: if check.missing_preconditions.is_empty() {
                                required.required_preconditions.clone()
                            } else {
                                check.missing_preconditions.clone()
                            },
                            theorem_refs: check.theorem_refs.clone(),
                            reason: "required theorem preconditions are missing".to_string(),
                            non_conclusions: vec![
                                "policy configuration does not discharge theorem preconditions"
                                    .to_string(),
                                "blocked formal claim is not promoted by CI".to_string(),
                            ],
                        }
                    })
                })
                .collect::<Vec<_>>(),
        );
    }
    decisions
}

fn coverage_gap_decisions(
    feature_report: &FeatureExtensionReportV0,
    policy: &OrganizationPolicyV0,
) -> Vec<CoverageGapPolicyDecisionV0> {
    let mut decisions = Vec::new();
    for gap in &feature_report.coverage_gaps {
        for axis in &gap.unmeasured_axes {
            let allowance = policy
                .allowed_unmeasured_gaps
                .iter()
                .find(|allowance| allowance.layer == gap.layer && allowance.axis == *axis);
            let allowed = allowance.is_some();
            decisions.push(CoverageGapPolicyDecisionV0 {
                layer: gap.layer.clone(),
                axis: axis.clone(),
                status: "warn".to_string(),
                allowed_by_policy: allowed,
                measurement_boundary: gap.measurement_boundary.clone(),
                reason: if let Some(allowance) = allowance {
                    format!("allowed unmeasured gap: {}", allowance.reason)
                } else {
                    "unmeasured coverage gap requires reviewer attention".to_string()
                },
                policy_scope: allowance.map(|allowance| allowance.scope.clone()),
                non_conclusions: if let Some(allowance) = allowance {
                    allowance.non_conclusions.clone()
                } else {
                    vec!["unmeasured gap is not measured-zero evidence".to_string()]
                },
            });
        }
    }
    decisions
}

fn witness_decisions(feature_report: &FeatureExtensionReportV0) -> Vec<WitnessPolicyDecisionV0> {
    feature_report
        .introduced_obstruction_witnesses
        .iter()
        .map(|witness| WitnessPolicyDecisionV0 {
            witness_id: witness.witness_id.clone(),
            status: "advisory".to_string(),
            layer: witness.layer.clone(),
            kind: witness.kind.clone(),
            claim_level: witness.claim_level.clone(),
            claim_classification: witness.claim_classification.clone(),
            measurement_boundary: witness.measurement_boundary.clone(),
            reason: if witness.measurement_boundary == "measuredNonzero" {
                "measured nonzero witness requires review; it is not an automatic theorem conclusion"
                    .to_string()
            } else {
                "witness is a reviewer-facing signal".to_string()
            },
            non_conclusions: witness.non_conclusions.clone(),
        })
        .collect()
}

fn policy_decision_checks(
    required_axis_decisions: &[RequiredAxisPolicyDecisionV0],
    missing_precondition_decisions: &[MissingPreconditionPolicyDecisionV0],
    coverage_gap_decisions: &[CoverageGapPolicyDecisionV0],
    witness_decisions: &[WitnessPolicyDecisionV0],
) -> Vec<ValidationCheck> {
    vec![
        decision_check(
            "policy-decision-required-axes",
            "required axes satisfy organization policy",
            required_axis_decisions
                .iter()
                .map(|decision| {
                    (
                        decision.status.as_str(),
                        decision.axis.as_str(),
                        decision.actual_measurement_boundary.as_str(),
                        decision.reason.as_str(),
                    )
                })
                .collect(),
        ),
        decision_check(
            "policy-decision-required-theorem-preconditions",
            "required theorem preconditions are discharged",
            missing_precondition_decisions
                .iter()
                .map(|decision| {
                    (
                        decision.status.as_str(),
                        decision.subject_ref.as_str(),
                        decision.claim_id.as_str(),
                        decision.reason.as_str(),
                    )
                })
                .collect(),
        ),
        decision_check(
            "policy-decision-coverage-gaps",
            "coverage gaps remain visible to reviewers",
            coverage_gap_decisions
                .iter()
                .map(|decision| {
                    (
                        decision.status.as_str(),
                        decision.axis.as_str(),
                        decision.measurement_boundary.as_str(),
                        decision.reason.as_str(),
                    )
                })
                .collect(),
        ),
        decision_check(
            "policy-decision-obstruction-witnesses",
            "measured nonzero witnesses are advisory review signals",
            witness_decisions
                .iter()
                .map(|decision| {
                    (
                        decision.status.as_str(),
                        decision.witness_id.as_str(),
                        decision.measurement_boundary.as_str(),
                        decision.reason.as_str(),
                    )
                })
                .collect(),
        ),
    ]
}

fn decision_check(
    id: &str,
    title: &str,
    decisions: Vec<(&str, &str, &str, &str)>,
) -> ValidationCheck {
    let result = if decisions.iter().any(|(status, _, _, _)| *status == "fail") {
        "fail"
    } else if decisions.iter().any(|(status, _, _, _)| *status == "warn") {
        "warn"
    } else if decisions
        .iter()
        .any(|(status, _, _, _)| *status == "advisory")
    {
        "advisory"
    } else {
        "pass"
    };
    let mut check = validation_check(id, title, result);
    if !decisions.is_empty() && result != "pass" {
        let examples: Vec<_> = decisions
            .iter()
            .filter(|(status, _, _, _)| *status == result)
            .map(|(_, source, target, evidence)| {
                generic_validation_example(source, target, evidence)
            })
            .collect();
        check.count = Some(examples.len());
        check.examples = examples;
    }
    check
}

#[derive(Debug)]
struct AxisObservation {
    value: Option<i64>,
    measurement_boundary: String,
}

fn axis_observation(feature_report: &FeatureExtensionReportV0, axis: &str) -> AxisObservation {
    if axis == "runtimePropagation" {
        return AxisObservation {
            value: feature_report.runtime_summary.runtime_propagation,
            measurement_boundary: feature_report.runtime_summary.measurement_boundary.clone(),
        };
    }
    if let Some(invariant) = feature_report
        .preserved_invariants
        .iter()
        .chain(feature_report.changed_invariants.iter())
        .find(|invariant| invariant.axis == axis)
    {
        return AxisObservation {
            value: invariant.value,
            measurement_boundary: invariant.measurement_boundary.clone(),
        };
    }
    if feature_report
        .architecture_summary
        .unmeasured_axes
        .iter()
        .any(|unmeasured| unmeasured == axis)
    {
        return AxisObservation {
            value: None,
            measurement_boundary: "unmeasured".to_string(),
        };
    }
    AxisObservation {
        value: None,
        measurement_boundary: "unmeasured".to_string(),
    }
}

#[cfg(test)]
mod tests {
    use crate::feature_report::build_feature_extension_report;
    use crate::organization_policy::static_organization_policy;
    use crate::test_support::air_fixture_document;

    use super::*;

    #[test]
    fn unmeasured_required_axis_fails_without_treating_gap_as_zero() {
        let document = air_fixture_document("good_extension.json");
        let feature_report = build_feature_extension_report(&document, "good_extension.json");
        let policy = static_organization_policy();

        let report = build_policy_decision_report(
            &feature_report,
            "good_extension.report.json",
            &policy,
            "static-organization-policy",
        );

        assert_eq!(report.schema_version, POLICY_DECISION_REPORT_SCHEMA_VERSION);
        assert_eq!(report.summary.decision, "fail");
        assert!(report.required_axis_decisions.iter().any(|decision| {
            decision.axis == "runtimePropagation"
                && decision.status == "fail"
                && decision.actual_measurement_boundary == "unmeasured"
        }));
        assert!(
            report
                .non_conclusions
                .contains(&"unmeasured axes are not treated as measured-zero risk".to_string())
        );
    }
}
