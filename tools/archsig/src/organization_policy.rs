use std::collections::BTreeSet;

use crate::validation::{count_checks, duplicates, generic_validation_example, validation_check};
use crate::{
    ORGANIZATION_POLICY_SCHEMA_VERSION, ORGANIZATION_POLICY_VALIDATION_REPORT_SCHEMA_VERSION,
    OrganizationAllowedUnmeasuredGapV0, OrganizationPolicyV0, OrganizationPolicyValidationInput,
    OrganizationPolicyValidationReportV0, OrganizationPolicyValidationSummary,
    OrganizationRequiredAxisV0, OrganizationRequiredTheoremPreconditionV0, ValidationCheck,
};

const REQUIRED_NON_CONCLUSIONS: [&str; 4] = [
    "organization policy is CI decision support, not a Lean theorem",
    "policy pass does not conclude architecture lawfulness",
    "allowed unmeasured gaps are not measured-zero evidence",
    "missing preconditions are not discharged by policy configuration",
];

const SUPPORTED_AXES: [&str; 16] = [
    "hasCycle",
    "sccMaxSize",
    "maxDepth",
    "fanoutRisk",
    "boundaryViolationCount",
    "abstractionViolationCount",
    "projectionSoundnessViolation",
    "lspViolationCount",
    "sccExcessSize",
    "maxFanout",
    "reachableConeSize",
    "weightedSccRisk",
    "runtimePropagation",
    "semanticDiagramCommutation",
    "semanticCurvature",
    "synthesisNoSolution",
];

const SUPPORTED_CLAIM_LEVELS: [&str; 4] = ["formal", "tooling", "empirical", "hypothesis"];

const SUPPORTED_MEASUREMENT_BOUNDARIES: [&str; 4] = [
    "measuredZero",
    "measuredNonzero",
    "unmeasured",
    "certificateBacked",
];

pub fn static_organization_policy() -> OrganizationPolicyV0 {
    OrganizationPolicyV0 {
        schema_version: ORGANIZATION_POLICY_SCHEMA_VERSION.to_string(),
        policy_id: "aat-b7-default-organization-policy".to_string(),
        policy_version: "2026-05-05".to_string(),
        scope: "repository default PR review policy for AAT B7 fixtures".to_string(),
        required_axes: vec![
            required_axis(
                "boundaryViolationCount",
                "tooling",
                "measuredZero",
                Some(0),
                &["boundary policy selectors cover checked static edges"],
            ),
            required_axis(
                "abstractionViolationCount",
                "tooling",
                "measuredZero",
                Some(0),
                &["abstraction policy relations cover checked static edges"],
            ),
            required_axis(
                "runtimePropagation",
                "formal",
                "measuredZero",
                Some(0),
                &[
                    "runtime edge evidence coverage is present",
                    "runtime-edge-projection-v0 exactness assumptions are recorded",
                    "runtime zero bridge theorem preconditions are discharged",
                ],
            ),
        ],
        allowed_unmeasured_gaps: vec![OrganizationAllowedUnmeasuredGapV0 {
            axis: "semanticDiagramCommutation".to_string(),
            claim_level: "tooling".to_string(),
            layer: "semantic".to_string(),
            scope: "PRs without semantic diagram fixtures".to_string(),
            reason: "semantic evidence adapters are not required for the default B7 fixture"
                .to_string(),
            expires_at: None,
            non_conclusions: REQUIRED_NON_CONCLUSIONS
                .iter()
                .map(|value| value.to_string())
                .collect(),
        }],
        required_theorem_preconditions: vec![OrganizationRequiredTheoremPreconditionV0 {
            subject_ref: "signature.runtimePropagation".to_string(),
            claim_level: "formal".to_string(),
            theorem_refs: vec![
                "ArchitectureSignature.runtimePropagationOfFinite_eq_zero_iff_noRuntimeExposureObstruction"
                    .to_string(),
                "ArchitectureSignature.v1OfFiniteWithRuntimePropagation_runtimePropagation_eq_some_zero_iff"
                    .to_string(),
            ],
            required_preconditions: vec![
                "runtimePropagation is computed over a measured 0/1 RuntimeDependencyGraph"
                    .to_string(),
                "the measured runtime graph is finite over the AIR component universe".to_string(),
            ],
        }],
        non_conclusions: REQUIRED_NON_CONCLUSIONS
            .iter()
            .map(|value| value.to_string())
            .collect(),
    }
}

pub fn validate_organization_policy_report(
    policy: &OrganizationPolicyV0,
    input_path: &str,
) -> OrganizationPolicyValidationReportV0 {
    let checks = vec![
        check_schema_version(policy),
        check_identity_and_scope(policy),
        check_required_axes(policy),
        check_allowed_unmeasured_gaps(policy),
        check_required_theorem_preconditions(policy),
        check_non_conclusion_boundary(policy),
    ];
    let summary = OrganizationPolicyValidationSummary {
        result: if checks.iter().any(|check| check.result == "fail") {
            "fail".to_string()
        } else if checks.iter().any(|check| check.result == "warn") {
            "warn".to_string()
        } else {
            "pass".to_string()
        },
        required_axis_count: policy.required_axes.len(),
        allowed_unmeasured_gap_count: policy.allowed_unmeasured_gaps.len(),
        required_theorem_precondition_count: policy.required_theorem_preconditions.len(),
        failed_check_count: count_checks(&checks, "fail"),
        warning_check_count: count_checks(&checks, "warn"),
    };

    OrganizationPolicyValidationReportV0 {
        schema_version: ORGANIZATION_POLICY_VALIDATION_REPORT_SCHEMA_VERSION.to_string(),
        input: OrganizationPolicyValidationInput {
            schema_version: policy.schema_version.clone(),
            path: input_path.to_string(),
            policy_id: policy.policy_id.clone(),
            policy_version: policy.policy_version.clone(),
            scope: policy.scope.clone(),
        },
        policy: policy.clone(),
        summary,
        checks,
    }
}

fn required_axis(
    axis: &str,
    claim_level: &str,
    measurement_boundary: &str,
    max_allowed_value: Option<i64>,
    required_preconditions: &[&str],
) -> OrganizationRequiredAxisV0 {
    OrganizationRequiredAxisV0 {
        axis: axis.to_string(),
        claim_level: claim_level.to_string(),
        measurement_boundary: measurement_boundary.to_string(),
        max_allowed_value,
        required_preconditions: required_preconditions
            .iter()
            .map(|value| value.to_string())
            .collect(),
    }
}

fn check_schema_version(policy: &OrganizationPolicyV0) -> ValidationCheck {
    let mut check = validation_check(
        "organization-policy-schema-version-supported",
        "organization policy schema version is supported",
        if policy.schema_version == ORGANIZATION_POLICY_SCHEMA_VERSION {
            "pass"
        } else {
            "fail"
        },
    );
    if check.result == "fail" {
        check.reason = Some(format!(
            "unsupported organization policy schemaVersion: {}",
            policy.schema_version
        ));
    }
    check
}

fn check_identity_and_scope(policy: &OrganizationPolicyV0) -> ValidationCheck {
    let mut invalid = Vec::new();
    if policy.policy_id.trim().is_empty() {
        invalid.push(generic_validation_example(
            "policyId",
            &policy.policy_version,
            "policy_id must be non-empty",
        ));
    }
    if policy.policy_version.trim().is_empty() {
        invalid.push(generic_validation_example(
            &policy.policy_id,
            "policyVersion",
            "policy_version must be non-empty",
        ));
    }
    if policy.scope.trim().is_empty() {
        invalid.push(generic_validation_example(
            &policy.policy_id,
            "scope",
            "scope must be non-empty",
        ));
    }
    check_examples(
        "organization-policy-scope-recorded",
        "policy id, version, and scope are recorded",
        invalid,
    )
}

fn check_required_axes(policy: &OrganizationPolicyV0) -> ValidationCheck {
    let axes = string_set(&SUPPORTED_AXES);
    let levels = string_set(&SUPPORTED_CLAIM_LEVELS);
    let boundaries = string_set(&SUPPORTED_MEASUREMENT_BOUNDARIES);
    let duplicate_axes = duplicates(policy.required_axes.iter().map(|axis| axis.axis.as_str()));
    let mut invalid = Vec::new();

    invalid.extend(
        duplicate_axes
            .into_iter()
            .map(|axis| generic_validation_example(&axis, &axis, "duplicate required axis")),
    );
    for axis in &policy.required_axes {
        if !axes.contains(axis.axis.as_str()) {
            invalid.push(generic_validation_example(
                &axis.axis,
                &axis.claim_level,
                "unknown required axis",
            ));
        }
        if !levels.contains(axis.claim_level.as_str()) {
            invalid.push(generic_validation_example(
                &axis.axis,
                &axis.claim_level,
                "unknown claim level",
            ));
        }
        if !boundaries.contains(axis.measurement_boundary.as_str()) {
            invalid.push(generic_validation_example(
                &axis.axis,
                &axis.measurement_boundary,
                "unsupported required measurement boundary",
            ));
        }
        if axis.required_preconditions.is_empty() || has_blank(&axis.required_preconditions) {
            invalid.push(generic_validation_example(
                &axis.axis,
                "requiredPreconditions",
                "required axis must record required preconditions",
            ));
        }
    }

    check_examples(
        "organization-policy-required-axes-valid",
        "required axes use known axes, claim levels, and explicit preconditions",
        invalid,
    )
}

fn check_allowed_unmeasured_gaps(policy: &OrganizationPolicyV0) -> ValidationCheck {
    let axes = string_set(&SUPPORTED_AXES);
    let levels = string_set(&SUPPORTED_CLAIM_LEVELS);
    let mut invalid = Vec::new();

    for gap in &policy.allowed_unmeasured_gaps {
        if !axes.contains(gap.axis.as_str()) {
            invalid.push(generic_validation_example(
                &gap.axis,
                &gap.scope,
                "unknown axis in allowed unmeasured gap",
            ));
        }
        if !levels.contains(gap.claim_level.as_str()) {
            invalid.push(generic_validation_example(
                &gap.axis,
                &gap.claim_level,
                "unknown claim level in allowed unmeasured gap",
            ));
        }
        if gap.layer.trim().is_empty()
            || gap.scope.trim().is_empty()
            || gap.reason.trim().is_empty()
        {
            invalid.push(generic_validation_example(
                &gap.axis,
                &gap.scope,
                "allowed unmeasured gap must record layer, scope, and reason",
            ));
        }
        if has_blank(&gap.non_conclusions) {
            invalid.push(generic_validation_example(
                &gap.axis,
                "nonConclusions",
                "allowed unmeasured gap non_conclusions must not contain blanks",
            ));
        }
    }

    check_examples(
        "organization-policy-allowed-unmeasured-gaps-valid",
        "allowed unmeasured gaps are scoped and are not measured-zero evidence",
        invalid,
    )
}

fn check_required_theorem_preconditions(policy: &OrganizationPolicyV0) -> ValidationCheck {
    let levels = string_set(&SUPPORTED_CLAIM_LEVELS);
    let mut invalid = Vec::new();

    for precondition in &policy.required_theorem_preconditions {
        if precondition.subject_ref.trim().is_empty() {
            invalid.push(generic_validation_example(
                "subjectRef",
                &precondition.claim_level,
                "required theorem precondition subject_ref must be non-empty",
            ));
        }
        if !levels.contains(precondition.claim_level.as_str()) {
            invalid.push(generic_validation_example(
                &precondition.subject_ref,
                &precondition.claim_level,
                "unknown claim level in required theorem precondition",
            ));
        }
        if precondition.theorem_refs.is_empty()
            || precondition.required_preconditions.is_empty()
            || has_blank(&precondition.theorem_refs)
            || has_blank(&precondition.required_preconditions)
        {
            invalid.push(generic_validation_example(
                &precondition.subject_ref,
                "theoremRefs",
                "required theorem preconditions must record theorem refs and preconditions",
            ));
        }
    }

    check_examples(
        "organization-policy-required-theorem-preconditions-valid",
        "required theorem preconditions are explicit and scoped to known claim levels",
        invalid,
    )
}

fn check_non_conclusion_boundary(policy: &OrganizationPolicyV0) -> ValidationCheck {
    let non_conclusions = string_set_from(policy.non_conclusions.iter().map(String::as_str));
    let invalid: Vec<_> = REQUIRED_NON_CONCLUSIONS
        .iter()
        .filter(|required| !non_conclusions.contains(**required))
        .map(|required| {
            generic_validation_example(
                &policy.policy_id,
                "nonConclusions",
                &format!("missing required non-conclusion: {required}"),
            )
        })
        .collect();

    check_examples(
        "organization-policy-non-conclusion-boundary-recorded",
        "policy records CI, lawfulness, unmeasured, and precondition non-conclusions",
        invalid,
    )
}

fn check_examples(
    id: &str,
    title: &str,
    invalid: Vec<crate::ValidationExample>,
) -> ValidationCheck {
    let mut check = validation_check(id, title, if invalid.is_empty() { "pass" } else { "fail" });
    if !invalid.is_empty() {
        check.count = Some(invalid.len());
        check.examples = invalid;
    }
    check
}

fn has_blank(values: &[String]) -> bool {
    values.iter().any(|value| value.trim().is_empty())
}

fn string_set<'a>(values: &'a [&'a str]) -> BTreeSet<&'a str> {
    values.iter().copied().collect()
}

fn string_set_from<'a>(values: impl Iterator<Item = &'a str>) -> BTreeSet<&'a str> {
    values.collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn static_policy_validates_and_records_ci_boundary() {
        let policy = static_organization_policy();
        let report = validate_organization_policy_report(&policy, "static-organization-policy");

        assert_eq!(
            report.schema_version,
            ORGANIZATION_POLICY_VALIDATION_REPORT_SCHEMA_VERSION
        );
        assert_eq!(report.summary.result, "pass");
        assert!(report.summary.required_axis_count >= 3);
        assert!(
            report
                .policy
                .non_conclusions
                .contains(&"allowed unmeasured gaps are not measured-zero evidence".to_string())
        );
    }

    #[test]
    fn invalid_axis_and_claim_level_fail_validation() {
        let mut policy = static_organization_policy();
        policy.required_axes.push(required_axis(
            "unknownAxis",
            "automatic-proof",
            "measuredZero",
            Some(0),
            &["fixture precondition"],
        ));
        policy
            .allowed_unmeasured_gaps
            .push(OrganizationAllowedUnmeasuredGapV0 {
                axis: "runtimePropagation".to_string(),
                claim_level: "automatic-proof".to_string(),
                layer: "runtime".to_string(),
                scope: String::new(),
                reason: String::new(),
                expires_at: None,
                non_conclusions: Vec::new(),
            });

        let report = validate_organization_policy_report(&policy, "invalid-policy.json");

        assert_eq!(report.summary.result, "fail");
        assert!(report.checks.iter().any(|check| check.id
            == "organization-policy-required-axes-valid"
            && check.result == "fail"));
        assert!(report.checks.iter().any(|check| check.id
            == "organization-policy-allowed-unmeasured-gaps-valid"
            && check.result == "fail"));
    }
}
