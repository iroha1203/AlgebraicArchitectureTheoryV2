use std::collections::{BTreeMap, BTreeSet};

use crate::validation::{count_checks, generic_validation_example, validation_check};
use crate::{
    ARTIFACT_DESCRIPTOR_SCHEMA_VERSION, ArtifactActionClassCandidateV0, ArtifactDescriptorV0,
    CandidateOperationFamilyV0, KnownForbiddenOperationSupportV0,
    OPERATION_SUPPORT_ESTIMATE_SCHEMA_VERSION,
    OPERATION_SUPPORT_ESTIMATE_VALIDATION_REPORT_SCHEMA_VERSION, OperationSupportDescriptorRefV0,
    OperationSupportEstimateV0, OperationSupportEstimateValidationInput,
    OperationSupportEstimateValidationReportV0, OperationSupportEstimateValidationSummary,
    OperationSupportEvidenceBoundaryV0, OperationSupportPolicyConstraintV0,
    OperationSupportUnknownRemainderV0, ValidationCheck,
};

const REQUIRED_NON_CONCLUSIONS: [&str; 5] = [
    "operation support estimate is a bounded tooling estimate, not accepted PR history",
    "operation support estimate is not actual future support",
    "unknown support is not measured zero",
    "policy constraints do not prove global policy safety",
    "operation support estimate does not prove future trajectory safety",
];

const REQUIRED_EVIDENCE_BOUNDARY_NON_CONCLUSIONS: [&str; 3] = [
    "confidence is relative to retained descriptor source refs",
    "evidence boundary does not complete extractor coverage",
    "unsupported constructs remain forecast boundary items",
];

pub fn static_operation_support_estimate() -> OperationSupportEstimateV0 {
    let source_ref_ids = vec![
        "source:issue-734".to_string(),
        "source:artifact-descriptor-fixture".to_string(),
        "source:roadmap-b12".to_string(),
        "source:sft-aat-interface".to_string(),
    ];
    let action_class_candidate_ids = vec![
        "candidate:add-schema".to_string(),
        "candidate:add-validator".to_string(),
        "candidate:add-cli-entrypoint".to_string(),
    ];

    OperationSupportEstimateV0 {
        schema_version: OPERATION_SUPPORT_ESTIMATE_SCHEMA_VERSION.to_string(),
        estimate_id: "fixture-operation-support-estimate-v0".to_string(),
        descriptor_ref: OperationSupportDescriptorRefV0 {
            descriptor_schema_version: ARTIFACT_DESCRIPTOR_SCHEMA_VERSION.to_string(),
            descriptor_id: "fixture-artifact-descriptor-v0".to_string(),
            artifact_kind: "issue".to_string(),
            source_ref_ids: source_ref_ids.clone(),
            action_class_candidate_ids: action_class_candidate_ids.clone(),
            non_conclusions: strings(&REQUIRED_NON_CONCLUSIONS),
        },
        candidate_operation_families: vec![
            candidate_family(
                "family:schema-validation-artifact",
                "schema-and-validator",
                "supported-by-selected-issue",
                &["candidate:add-schema", "candidate:add-validator"],
                &["source:issue-734", "source:roadmap-b12"],
                "high",
                "Issue #734 requests a schema and validator before downstream forecast artifacts.",
            ),
            candidate_family(
                "family:cli-fixture-validation",
                "cli-fixture-validation",
                "supported-by-selected-issue",
                &["candidate:add-cli-entrypoint"],
                &["source:issue-734", "source:artifact-descriptor-fixture"],
                "medium",
                "The estimate should be emitted and validated through an archsig CLI entrypoint.",
            ),
        ],
        policy_constraints: vec![
            policy_constraint(
                "constraint:no-theorem-promotion",
                "claim-boundary",
                &[
                    "family:schema-validation-artifact",
                    "family:cli-fixture-validation",
                ],
                &["source:sft-aat-interface"],
                "Do not promote tooling estimates to Lean theorem claims.",
                "constraint is local to selected B12 operation support evidence",
            ),
            policy_constraint(
                "constraint:no-causal-forecast",
                "forecast-boundary",
                &["family:schema-validation-artifact"],
                &["source:roadmap-b12"],
                "Do not treat support estimates as causal forecasts.",
                "constraint prevents global safety and future trajectory safety claims",
            ),
        ],
        known_forbidden_support: vec![KnownForbiddenOperationSupportV0 {
            forbidden_id: "forbidden:probability-assignment".to_string(),
            operation_family: "forecast-probability-assignment".to_string(),
            source_ref_ids: vec!["source:roadmap-b12".to_string()],
            constraint_refs: vec!["constraint:no-causal-forecast".to_string()],
            reason: "B12.2 precedes ForecastCone and does not assign probabilities.".to_string(),
            boundary: "probability and causal prediction remain outside operation support estimate"
                .to_string(),
            non_conclusions: strings(&REQUIRED_NON_CONCLUSIONS),
        }],
        unknown_remainder: vec![OperationSupportUnknownRemainderV0 {
            remainder_id: "unknown:runtime-and-private-history".to_string(),
            affected_family_ids: vec![
                "family:schema-validation-artifact".to_string(),
                "family:cli-fixture-validation".to_string(),
            ],
            source_ref_ids: vec!["source:issue-734".to_string()],
            unknown_axes: vec![
                "private PRD details".to_string(),
                "runtime traces".to_string(),
                "future accepted PR history".to_string(),
            ],
            reason: "selected sources do not contain full PRD, runtime traces, or future history"
                .to_string(),
            treatment: "retain as unknown support remainder under the selected boundary"
                .to_string(),
            non_conclusions: strings(&REQUIRED_NON_CONCLUSIONS),
        }],
        evidence_boundary: OperationSupportEvidenceBoundaryV0 {
            boundary_id: "boundary:b12.2-operation-support-estimate".to_string(),
            source_ref_ids,
            measurement_boundary_refs: vec![
                "boundary:b12.1-artifact-descriptor".to_string(),
                "docs/tool/roadmap.md#b122-operationsupportestimate".to_string(),
            ],
            confidence_boundary: "confidence values are qualitative and source-bound".to_string(),
            evidence_kinds: vec![
                "issue-body".to_string(),
                "artifact-descriptor-fixture".to_string(),
                "roadmap-boundary".to_string(),
            ],
            unsupported_constructs: vec![
                "accepted PR history completeness".to_string(),
                "actual future operation support".to_string(),
                "global policy safety proof".to_string(),
            ],
            assumptions: vec![
                "artifact descriptor source refs are retained by id".to_string(),
                "operation families are candidates under selected B12 inputs".to_string(),
            ],
            non_conclusions: strings(&REQUIRED_EVIDENCE_BOUNDARY_NON_CONCLUSIONS),
        },
        non_conclusions: strings(&REQUIRED_NON_CONCLUSIONS),
    }
}

pub fn build_operation_support_estimate_from_descriptor(
    descriptor: &ArtifactDescriptorV0,
) -> OperationSupportEstimateV0 {
    let source_ref_ids = descriptor
        .source_refs
        .iter()
        .map(|source| source.source_ref_id.clone())
        .collect::<Vec<_>>();
    let action_class_candidate_ids = descriptor
        .action_class_candidates
        .iter()
        .map(|candidate| candidate.candidate_id.clone())
        .collect::<Vec<_>>();
    let candidate_operation_families =
        candidate_families_from_descriptor(descriptor, &source_ref_ids);
    let family_ids = candidate_operation_families
        .iter()
        .map(|family| family.family_id.clone())
        .collect::<Vec<_>>();
    let policy_constraints = policy_constraints_from_descriptor(&family_ids, &source_ref_ids);
    let unknown_remainder = unknown_remainder_from_descriptor(descriptor, &family_ids);

    OperationSupportEstimateV0 {
        schema_version: OPERATION_SUPPORT_ESTIMATE_SCHEMA_VERSION.to_string(),
        estimate_id: format!("estimate:{}", descriptor.descriptor_id),
        descriptor_ref: OperationSupportDescriptorRefV0 {
            descriptor_schema_version: ARTIFACT_DESCRIPTOR_SCHEMA_VERSION.to_string(),
            descriptor_id: descriptor.descriptor_id.clone(),
            artifact_kind: descriptor.artifact_kind.clone(),
            source_ref_ids: source_ref_ids.clone(),
            action_class_candidate_ids,
            non_conclusions: strings(&REQUIRED_NON_CONCLUSIONS),
        },
        candidate_operation_families,
        policy_constraints,
        known_forbidden_support: vec![KnownForbiddenOperationSupportV0 {
            forbidden_id: "forbidden:causal-probability-assignment".to_string(),
            operation_family: "causal-probability-assignment".to_string(),
            source_ref_ids: source_ref_ids.clone(),
            constraint_refs: vec!["constraint:no-causal-forecast".to_string()],
            reason: "descriptor evidence does not establish causal prediction or outcome probability"
                .to_string(),
            boundary:
                "probability assignment and causal prediction remain outside operation support estimate"
                    .to_string(),
            non_conclusions: strings(&REQUIRED_NON_CONCLUSIONS),
        }],
        evidence_boundary: OperationSupportEvidenceBoundaryV0 {
            boundary_id: format!("boundary:{}:operation-support-estimate", descriptor.descriptor_id),
            source_ref_ids,
            measurement_boundary_refs: vec![
                descriptor.measurement_boundary.boundary_id.clone(),
                descriptor.descriptor_id.clone(),
            ],
            confidence_boundary:
                "confidence values are qualitative and relative to retained descriptor source refs"
                    .to_string(),
            evidence_kinds: evidence_kinds_from_descriptor(descriptor),
            unsupported_constructs: unsupported_constructs_from_descriptor(descriptor),
            assumptions: evidence_assumptions_from_descriptor(descriptor),
            non_conclusions: strings(&REQUIRED_EVIDENCE_BOUNDARY_NON_CONCLUSIONS),
        },
        unknown_remainder,
        non_conclusions: strings(&REQUIRED_NON_CONCLUSIONS),
    }
}

pub fn validate_operation_support_estimate(
    estimate: &OperationSupportEstimateV0,
    input_path: &str,
) -> OperationSupportEstimateValidationReportV0 {
    let checks = vec![
        check_schema_version(estimate),
        check_descriptor_ref(estimate),
        check_candidate_operation_families(estimate),
        check_policy_constraints(estimate),
        check_forbidden_support(estimate),
        check_unknown_remainder(estimate),
        check_evidence_boundary(estimate),
        check_non_conclusions(estimate),
    ];
    let summary = OperationSupportEstimateValidationSummary {
        result: validation_result(&checks),
        candidate_operation_family_count: estimate.candidate_operation_families.len(),
        policy_constraint_count: estimate.policy_constraints.len(),
        known_forbidden_support_count: estimate.known_forbidden_support.len(),
        unknown_remainder_count: estimate.unknown_remainder.len(),
        failed_check_count: count_checks(&checks, "fail"),
        warning_check_count: count_checks(&checks, "warn"),
    };

    OperationSupportEstimateValidationReportV0 {
        schema_version: OPERATION_SUPPORT_ESTIMATE_VALIDATION_REPORT_SCHEMA_VERSION.to_string(),
        input: OperationSupportEstimateValidationInput {
            schema_version: estimate.schema_version.clone(),
            path: input_path.to_string(),
            estimate_id: estimate.estimate_id.clone(),
            descriptor_id: estimate.descriptor_ref.descriptor_id.clone(),
        },
        estimate: estimate.clone(),
        summary,
        checks,
    }
}

fn candidate_families_from_descriptor(
    descriptor: &ArtifactDescriptorV0,
    descriptor_source_ref_ids: &[String],
) -> Vec<CandidateOperationFamilyV0> {
    let mut grouped = BTreeMap::<String, Vec<&ArtifactActionClassCandidateV0>>::new();
    for candidate in &descriptor.action_class_candidates {
        grouped
            .entry(operation_family_for_action_class(&candidate.action_class).to_string())
            .or_default()
            .push(candidate);
    }

    grouped
        .into_iter()
        .map(|(operation_family, candidates)| {
            let family_id = format!("family:{}", slugify(&operation_family));
            let action_class_candidate_ids = candidates
                .iter()
                .map(|candidate| candidate.candidate_id.clone())
                .collect::<Vec<_>>();
            let source_ref_ids =
                retained_candidate_source_refs(&candidates, descriptor_source_ref_ids);
            CandidateOperationFamilyV0 {
                family_id,
                operation_family,
                support_kind: "supported-by-selected-descriptor".to_string(),
                action_class_candidate_ids,
                source_ref_ids,
                confidence: merged_confidence(&candidates).to_string(),
                rationale: format!(
                    "Derived from descriptor action classes: {}.",
                    candidates
                        .iter()
                        .map(|candidate| candidate.action_class.as_str())
                        .collect::<BTreeSet<_>>()
                        .into_iter()
                        .collect::<Vec<_>>()
                        .join(", ")
                ),
                assumptions: vec![
                    "operation family is inferred only from selected descriptor refs".to_string(),
                    "support estimate does not assert actual future support".to_string(),
                ],
                non_conclusions: strings(&REQUIRED_NON_CONCLUSIONS),
            }
        })
        .collect()
}

fn policy_constraints_from_descriptor(
    family_ids: &[String],
    source_ref_ids: &[String],
) -> Vec<OperationSupportPolicyConstraintV0> {
    vec![
        OperationSupportPolicyConstraintV0 {
            constraint_id: "constraint:no-theorem-promotion".to_string(),
            constraint_kind: "claim-boundary".to_string(),
            applies_to_family_ids: family_ids.to_vec(),
            source_ref_ids: source_ref_ids.to_vec(),
            rule: "Do not promote tooling estimates to Lean theorem claims.".to_string(),
            safety_claim_boundary: "constraint is local to selected descriptor evidence"
                .to_string(),
            non_conclusions: strings(&REQUIRED_NON_CONCLUSIONS),
        },
        OperationSupportPolicyConstraintV0 {
            constraint_id: "constraint:no-causal-forecast".to_string(),
            constraint_kind: "forecast-boundary".to_string(),
            applies_to_family_ids: family_ids.to_vec(),
            source_ref_ids: source_ref_ids.to_vec(),
            rule: "Do not treat operation support estimates as causal forecasts.".to_string(),
            safety_claim_boundary: "constraint is local to selected operation support evidence"
                .to_string(),
            non_conclusions: strings(&REQUIRED_NON_CONCLUSIONS),
        },
    ]
}

fn unknown_remainder_from_descriptor(
    descriptor: &ArtifactDescriptorV0,
    family_ids: &[String],
) -> Vec<OperationSupportUnknownRemainderV0> {
    let mut unknown_axes = descriptor
        .missing_evidence
        .iter()
        .map(|evidence| format!("{}: {}", evidence.evidence_kind, evidence.reason))
        .chain(
            descriptor
                .measurement_boundary
                .unsupported_constructs
                .iter()
                .cloned(),
        )
        .collect::<Vec<_>>();
    if unknown_axes.is_empty() {
        unknown_axes.push("unmodeled implementation and runtime support".to_string());
    }
    unknown_axes.sort();
    unknown_axes.dedup();

    vec![OperationSupportUnknownRemainderV0 {
        remainder_id: "unknown:descriptor-boundary-remainder".to_string(),
        affected_family_ids: family_ids.to_vec(),
        source_ref_ids: descriptor.measurement_boundary.source_ref_ids.clone(),
        unknown_axes,
        reason: "selected descriptor evidence does not contain complete operation support, runtime traces, or accepted PR history"
            .to_string(),
        treatment: "retain as unknown support remainder under the selected descriptor boundary"
            .to_string(),
        non_conclusions: strings(&REQUIRED_NON_CONCLUSIONS),
    }]
}

fn candidate_family(
    family_id: &str,
    operation_family: &str,
    support_kind: &str,
    action_class_candidate_ids: &[&str],
    source_ref_ids: &[&str],
    confidence: &str,
    rationale: &str,
) -> CandidateOperationFamilyV0 {
    CandidateOperationFamilyV0 {
        family_id: family_id.to_string(),
        operation_family: operation_family.to_string(),
        support_kind: support_kind.to_string(),
        action_class_candidate_ids: strings(action_class_candidate_ids),
        source_ref_ids: strings(source_ref_ids),
        confidence: confidence.to_string(),
        rationale: rationale.to_string(),
        assumptions: vec![
            "operation family is inferred only from selected descriptor refs".to_string(),
            "support estimate does not assert actual future support".to_string(),
        ],
        non_conclusions: strings(&REQUIRED_NON_CONCLUSIONS),
    }
}

fn operation_family_for_action_class(action_class: &str) -> &str {
    match action_class {
        "schema-definition" | "tooling-validation" => "schema-and-validator",
        "cli-entrypoint" => "cli-fixture-validation",
        "docs-update" | "documentation" => "documentation-boundary-update",
        "api-definition" | "definition" => "api-definition",
        "test-fixture" | "fixture" => "fixture-validation",
        "pipeline" | "workflow" => "pipeline-integration",
        _ => "artifact-driven-change",
    }
}

fn retained_candidate_source_refs(
    candidates: &[&ArtifactActionClassCandidateV0],
    descriptor_source_ref_ids: &[String],
) -> Vec<String> {
    let descriptor_source_ref_ids = descriptor_source_ref_ids
        .iter()
        .map(String::as_str)
        .collect::<BTreeSet<_>>();
    let mut source_refs = candidates
        .iter()
        .flat_map(|candidate| candidate.source_ref_ids.iter())
        .filter(|source_ref_id| descriptor_source_ref_ids.contains(source_ref_id.as_str()))
        .cloned()
        .collect::<Vec<_>>();
    source_refs.sort();
    source_refs.dedup();
    if source_refs.is_empty() {
        source_refs.extend(
            descriptor_source_ref_ids
                .iter()
                .map(|source| source.to_string()),
        );
    }
    source_refs
}

fn merged_confidence(candidates: &[&ArtifactActionClassCandidateV0]) -> &'static str {
    if candidates
        .iter()
        .any(|candidate| candidate.confidence.eq_ignore_ascii_case("high"))
    {
        "high"
    } else if candidates
        .iter()
        .any(|candidate| candidate.confidence.eq_ignore_ascii_case("medium"))
    {
        "medium"
    } else {
        "low"
    }
}

fn evidence_kinds_from_descriptor(descriptor: &ArtifactDescriptorV0) -> Vec<String> {
    let mut kinds = descriptor
        .source_refs
        .iter()
        .map(|source| source.source_kind.clone())
        .collect::<Vec<_>>();
    kinds.push("artifact-descriptor".to_string());
    kinds.sort();
    kinds.dedup();
    kinds
}

fn unsupported_constructs_from_descriptor(descriptor: &ArtifactDescriptorV0) -> Vec<String> {
    let mut constructs = descriptor
        .measurement_boundary
        .unsupported_constructs
        .clone();
    constructs.extend([
        "accepted PR history completeness".to_string(),
        "actual future operation support".to_string(),
        "global policy safety proof".to_string(),
    ]);
    constructs.sort();
    constructs.dedup();
    constructs
}

fn evidence_assumptions_from_descriptor(descriptor: &ArtifactDescriptorV0) -> Vec<String> {
    let mut assumptions = descriptor.measurement_boundary.assumptions.clone();
    assumptions.extend(descriptor.scope.assumptions.clone());
    assumptions.push("artifact descriptor source refs are retained by id".to_string());
    assumptions
        .push("operation families are candidates under selected descriptor inputs".to_string());
    assumptions.sort();
    assumptions.dedup();
    assumptions
}

fn slugify(value: &str) -> String {
    let mut slug = String::new();
    let mut last_dash = false;
    for ch in value.chars() {
        if ch.is_ascii_alphanumeric() {
            slug.push(ch.to_ascii_lowercase());
            last_dash = false;
        } else if !last_dash {
            slug.push('-');
            last_dash = true;
        }
    }
    slug.trim_matches('-').to_string()
}

fn policy_constraint(
    constraint_id: &str,
    constraint_kind: &str,
    applies_to_family_ids: &[&str],
    source_ref_ids: &[&str],
    rule: &str,
    safety_claim_boundary: &str,
) -> OperationSupportPolicyConstraintV0 {
    OperationSupportPolicyConstraintV0 {
        constraint_id: constraint_id.to_string(),
        constraint_kind: constraint_kind.to_string(),
        applies_to_family_ids: strings(applies_to_family_ids),
        source_ref_ids: strings(source_ref_ids),
        rule: rule.to_string(),
        safety_claim_boundary: safety_claim_boundary.to_string(),
        non_conclusions: strings(&REQUIRED_NON_CONCLUSIONS),
    }
}

fn check_schema_version(estimate: &OperationSupportEstimateV0) -> ValidationCheck {
    let mut check = validation_check(
        "operation-support-estimate-schema-version-supported",
        "operation support estimate schema version is supported",
        if estimate.schema_version == OPERATION_SUPPORT_ESTIMATE_SCHEMA_VERSION {
            "pass"
        } else {
            "fail"
        },
    );
    if check.result == "fail" {
        check.reason = Some(format!(
            "unsupported operation support estimate schemaVersion: {}",
            estimate.schema_version
        ));
    }
    check
}

fn check_descriptor_ref(estimate: &OperationSupportEstimateV0) -> ValidationCheck {
    let descriptor = &estimate.descriptor_ref;
    let invalid = estimate.estimate_id.trim().is_empty()
        || descriptor.descriptor_schema_version != ARTIFACT_DESCRIPTOR_SCHEMA_VERSION
        || descriptor.descriptor_id.trim().is_empty()
        || descriptor.artifact_kind.trim().is_empty()
        || descriptor.source_ref_ids.is_empty()
        || descriptor.action_class_candidate_ids.is_empty();
    let mut check = validation_check(
        "operation-support-estimate-descriptor-refs-retained",
        "descriptor refs retain source refs and action class candidate ids",
        if invalid { "fail" } else { "pass" },
    );
    if invalid {
        check.reason = Some(
            "estimateId, descriptor id, descriptor schema, source refs, and action candidates are required"
                .to_string(),
        );
    }
    check.count = Some(descriptor.source_ref_ids.len());
    check
}

fn check_candidate_operation_families(estimate: &OperationSupportEstimateV0) -> ValidationCheck {
    let source_ids = source_ids(estimate);
    let candidate_ids = candidate_ids(estimate);
    let invalid = estimate
        .candidate_operation_families
        .iter()
        .filter(|family| {
            family.family_id.trim().is_empty()
                || family.operation_family.trim().is_empty()
                || family.support_kind.trim().is_empty()
                || family.action_class_candidate_ids.is_empty()
                || family.source_ref_ids.is_empty()
                || family
                    .source_ref_ids
                    .iter()
                    .any(|source_ref_id| !source_ids.contains(source_ref_id.as_str()))
                || family
                    .action_class_candidate_ids
                    .iter()
                    .any(|candidate_id| !candidate_ids.contains(candidate_id.as_str()))
        })
        .map(|family| family.family_id.clone())
        .collect::<Vec<_>>();
    let mut check = validation_check(
        "operation-support-estimate-candidate-families-bounded",
        "candidate operation families are source-bound and linked to descriptor action candidates",
        if !estimate.candidate_operation_families.is_empty() && invalid.is_empty() {
            "pass"
        } else {
            "fail"
        },
    );
    if estimate.candidate_operation_families.is_empty() {
        check.reason = Some("at least one candidate operation family is required".to_string());
    } else if !invalid.is_empty() {
        check.reason = Some(format!(
            "candidate operation families with missing fields or dangling refs: {}",
            invalid.join(", ")
        ));
    }
    check.count = Some(estimate.candidate_operation_families.len());
    check
}

fn check_policy_constraints(estimate: &OperationSupportEstimateV0) -> ValidationCheck {
    let source_ids = source_ids(estimate);
    let family_ids = family_ids(estimate);
    let invalid = estimate
        .policy_constraints
        .iter()
        .filter(|constraint| {
            constraint.constraint_id.trim().is_empty()
                || constraint.constraint_kind.trim().is_empty()
                || constraint.applies_to_family_ids.is_empty()
                || constraint.source_ref_ids.is_empty()
                || constraint.rule.trim().is_empty()
                || constraint.safety_claim_boundary.trim().is_empty()
                || overpromotes_policy_safety(&constraint.safety_claim_boundary)
                || constraint
                    .source_ref_ids
                    .iter()
                    .any(|source_ref_id| !source_ids.contains(source_ref_id.as_str()))
                || constraint
                    .applies_to_family_ids
                    .iter()
                    .any(|family_id| !family_ids.contains(family_id.as_str()))
        })
        .map(|constraint| constraint.constraint_id.clone())
        .collect::<Vec<_>>();
    let mut check = validation_check(
        "operation-support-estimate-policy-constraints-bounded",
        "policy constraints are local and do not promote to global or future safety claims",
        if invalid.is_empty() { "pass" } else { "fail" },
    );
    if !invalid.is_empty() {
        check.reason = Some(format!(
            "policy constraints with missing refs or over-promoted safety boundaries: {}",
            invalid.join(", ")
        ));
        check.examples = invalid
            .iter()
            .map(|constraint_id| {
                generic_validation_example(
                    constraint_id,
                    "safetyClaimBoundary",
                    "expected a local source-bound boundary, not a global/future safety claim",
                )
            })
            .collect();
    }
    check.count = Some(estimate.policy_constraints.len());
    check
}

fn check_forbidden_support(estimate: &OperationSupportEstimateV0) -> ValidationCheck {
    let source_ids = source_ids(estimate);
    let constraint_ids = constraint_ids(estimate);
    let invalid = estimate
        .known_forbidden_support
        .iter()
        .filter(|forbidden| {
            forbidden.forbidden_id.trim().is_empty()
                || forbidden.operation_family.trim().is_empty()
                || forbidden.source_ref_ids.is_empty()
                || forbidden.reason.trim().is_empty()
                || forbidden.boundary.trim().is_empty()
                || forbidden
                    .source_ref_ids
                    .iter()
                    .any(|source_ref_id| !source_ids.contains(source_ref_id.as_str()))
                || forbidden
                    .constraint_refs
                    .iter()
                    .any(|constraint_id| !constraint_ids.contains(constraint_id.as_str()))
        })
        .map(|forbidden| forbidden.forbidden_id.clone())
        .collect::<Vec<_>>();
    let mut check = validation_check(
        "operation-support-estimate-known-forbidden-support-bounded",
        "known forbidden support is source-bound and linked to policy constraints when provided",
        if invalid.is_empty() { "pass" } else { "fail" },
    );
    if !invalid.is_empty() {
        check.reason = Some(format!(
            "known forbidden support entries with missing fields or dangling refs: {}",
            invalid.join(", ")
        ));
    }
    check.count = Some(estimate.known_forbidden_support.len());
    check
}

fn check_unknown_remainder(estimate: &OperationSupportEstimateV0) -> ValidationCheck {
    let source_ids = source_ids(estimate);
    let family_ids = family_ids(estimate);
    let invalid = estimate
        .unknown_remainder
        .iter()
        .filter(|remainder| {
            remainder.remainder_id.trim().is_empty()
                || remainder.affected_family_ids.is_empty()
                || remainder.source_ref_ids.is_empty()
                || remainder.unknown_axes.is_empty()
                || remainder.reason.trim().is_empty()
                || remainder.treatment.trim().is_empty()
                || treats_unknown_as_zero(&remainder.treatment)
                || remainder
                    .source_ref_ids
                    .iter()
                    .any(|source_ref_id| !source_ids.contains(source_ref_id.as_str()))
                || remainder
                    .affected_family_ids
                    .iter()
                    .any(|family_id| !family_ids.contains(family_id.as_str()))
        })
        .map(|remainder| remainder.remainder_id.clone())
        .collect::<Vec<_>>();
    let mut check = validation_check(
        "operation-support-estimate-unknown-remainder-not-measured-zero",
        "unknown and unmodeled support remains explicit and is not treated as measured zero",
        if !estimate.unknown_remainder.is_empty() && invalid.is_empty() {
            "pass"
        } else {
            "fail"
        },
    );
    if estimate.unknown_remainder.is_empty() {
        check.reason = Some("at least one unknown remainder item is required".to_string());
    } else if !invalid.is_empty() {
        check.reason = Some(format!(
            "unknown remainder entries with missing refs or measured-zero treatment: {}",
            invalid.join(", ")
        ));
        check.examples = invalid
            .iter()
            .map(|remainder_id| {
                generic_validation_example(
                    remainder_id,
                    "unknownRemainder.treatment",
                    "unknown support must remain unknown/unmodeled, not safe, absent, or measured zero",
                )
            })
            .collect();
    }
    check.count = Some(estimate.unknown_remainder.len());
    check
}

fn check_evidence_boundary(estimate: &OperationSupportEstimateV0) -> ValidationCheck {
    let source_ids = source_ids(estimate);
    let boundary = &estimate.evidence_boundary;
    let dangling_source_refs = boundary
        .source_ref_ids
        .iter()
        .filter(|source_ref_id| !source_ids.contains(source_ref_id.as_str()))
        .cloned()
        .collect::<Vec<_>>();
    let invalid = boundary.boundary_id.trim().is_empty()
        || boundary.source_ref_ids.is_empty()
        || boundary.measurement_boundary_refs.is_empty()
        || boundary.confidence_boundary.trim().is_empty()
        || boundary.evidence_kinds.is_empty()
        || boundary.assumptions.is_empty()
        || boundary
            .confidence_boundary
            .to_ascii_lowercase()
            .contains("complete");
    let mut check = validation_check(
        "operation-support-estimate-evidence-boundary-retained",
        "evidence boundary keeps confidence and measurement boundary limits",
        if !invalid && dangling_source_refs.is_empty() {
            "pass"
        } else {
            "fail"
        },
    );
    if invalid {
        check.reason = Some(
            "evidence boundary requires source refs, measurement refs, evidence kinds, assumptions, and incomplete confidence"
                .to_string(),
        );
    } else if !dangling_source_refs.is_empty() {
        check.reason = Some(format!(
            "evidence boundary references unknown source refs: {}",
            dangling_source_refs.join(", ")
        ));
    }
    check.count = Some(boundary.source_ref_ids.len());
    check
}

fn check_non_conclusions(estimate: &OperationSupportEstimateV0) -> ValidationCheck {
    let missing_estimate = REQUIRED_NON_CONCLUSIONS
        .iter()
        .filter(|required| {
            !estimate
                .non_conclusions
                .iter()
                .any(|actual| actual == *required)
        })
        .copied()
        .collect::<Vec<_>>();
    let missing_boundary = REQUIRED_EVIDENCE_BOUNDARY_NON_CONCLUSIONS
        .iter()
        .filter(|required| {
            !estimate
                .evidence_boundary
                .non_conclusions
                .iter()
                .any(|actual| actual == *required)
        })
        .copied()
        .collect::<Vec<_>>();
    let mut check = validation_check(
        "operation-support-estimate-non-conclusions-preserved",
        "operation support estimate preserves actual-support, policy-safety, and future-safety boundaries",
        if missing_estimate.is_empty() && missing_boundary.is_empty() {
            "pass"
        } else {
            "fail"
        },
    );
    if !missing_estimate.is_empty() {
        check.reason = Some(format!(
            "missing estimate non-conclusions: {}",
            missing_estimate.join("; ")
        ));
    } else if !missing_boundary.is_empty() {
        check.reason = Some(format!(
            "missing evidence boundary non-conclusions: {}",
            missing_boundary.join("; ")
        ));
    }
    check
}

fn source_ids(estimate: &OperationSupportEstimateV0) -> BTreeSet<&str> {
    estimate
        .descriptor_ref
        .source_ref_ids
        .iter()
        .map(String::as_str)
        .collect()
}

fn candidate_ids(estimate: &OperationSupportEstimateV0) -> BTreeSet<&str> {
    estimate
        .descriptor_ref
        .action_class_candidate_ids
        .iter()
        .map(String::as_str)
        .collect()
}

fn family_ids(estimate: &OperationSupportEstimateV0) -> BTreeSet<&str> {
    estimate
        .candidate_operation_families
        .iter()
        .map(|family| family.family_id.as_str())
        .collect()
}

fn constraint_ids(estimate: &OperationSupportEstimateV0) -> BTreeSet<&str> {
    estimate
        .policy_constraints
        .iter()
        .map(|constraint| constraint.constraint_id.as_str())
        .collect()
}

fn overpromotes_policy_safety(value: &str) -> bool {
    let value = value.to_ascii_lowercase();
    value.contains("proves global")
        || value.contains("global safety is guaranteed")
        || value.contains("future trajectory is safe")
        || value.contains("policy is globally safe")
}

fn treats_unknown_as_zero(value: &str) -> bool {
    let value = value.to_ascii_lowercase();
    value.contains("measured zero")
        || value.contains("treated as zero")
        || value.contains("safe by default")
        || value.contains("known absent")
}

fn validation_result(checks: &[ValidationCheck]) -> String {
    if checks.iter().any(|check| check.result == "fail") {
        "fail".to_string()
    } else if checks.iter().any(|check| check.result == "warn") {
        "warn".to_string()
    } else {
        "pass".to_string()
    }
}

fn strings(values: &[&str]) -> Vec<String> {
    values.iter().map(|value| value.to_string()).collect()
}
