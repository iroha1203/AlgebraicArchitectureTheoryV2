use std::collections::BTreeSet;

use crate::validation::{count_checks, validation_check};
use crate::{
    AI_PROPOSAL_GOVERNANCE_SCHEMA_VERSION, AI_PROPOSAL_GOVERNANCE_VALIDATION_REPORT_SCHEMA_VERSION,
    ARTIFACT_DESCRIPTOR_SCHEMA_VERSION, AiProposalGovernanceEvidenceBoundaryV0,
    AiProposalGovernanceProposalRefV0, AiProposalGovernanceV0, AiProposalGovernanceValidationInput,
    AiProposalGovernanceValidationReportV0, AiProposalGovernanceValidationSummary,
    AiProposalPosteriorFieldUpdateV0, AiProposalPromptPolicyBoundaryV0,
    AiProposalReviewCiMediationV0, AiProposalShortcutWitnessV0, AiProposalSupportAssessmentV0,
    ArtifactDescriptorV0, CONSEQUENCE_ENVELOPE_REPORT_SCHEMA_VERSION,
    FORECAST_CALIBRATION_HOOK_SCHEMA_VERSION, OPERATION_SUPPORT_ESTIMATE_SCHEMA_VERSION,
    ValidationCheck,
};

const GOVERNANCE_NON_CONCLUSIONS: [&str; 5] = [
    "AI proposal governance is a reviewer-facing artifact, not an AI safety theorem",
    "policy compliance does not establish architecture lawfulness",
    "review or CI pass does not prove forecast correctness",
    "posterior field update is a bounded empirical hook, not a causal proof",
    "unknown and unavailable support is not measured zero",
];

const SUPPORT_CATEGORIES: [&str; 5] = [
    "allowed",
    "conditionallyAllowed",
    "forbidden",
    "unknown",
    "outOfScope",
];

pub fn static_ai_proposal_governance() -> AiProposalGovernanceV0 {
    let descriptor = crate::build_artifact_descriptor_from_ai_proposal_json(
        "tools/fieldsig/tests/fixtures/minimal/ai_proposal_sft_adapter.json",
        &serde_json::json!({
            "proposalId": "fixture-ai-proposal",
            "title": "Fixture AI proposal governance",
            "promptRef": "prompt:fixture-ai-proposal",
            "policyRef": "policy:fixture-ai-proposal",
            "summary": "Add bounded SFT governance surface without claiming AI safety.",
            "files": ["tools/archsig/src/sft_forecasting.rs", "tools/archsig/src/artifact_descriptor.rs"]
        }),
    );
    build_ai_proposal_governance_from_descriptor(
        &descriptor,
        Some("fixture-operation-support-estimate-v0"),
        Some("fixture-consequence-envelope-report-v0"),
    )
}

pub fn build_ai_proposal_governance_from_descriptor(
    descriptor: &ArtifactDescriptorV0,
    operation_support_estimate_id: Option<&str>,
    consequence_envelope_id: Option<&str>,
) -> AiProposalGovernanceV0 {
    let source_ref_ids = descriptor
        .source_refs
        .iter()
        .map(|source| source.source_ref_id.clone())
        .collect::<Vec<_>>();
    let proposal_source_ref_id = source_ref_ids
        .first()
        .cloned()
        .unwrap_or_else(|| format!("source:descriptor:{}", descriptor.descriptor_id));
    let prompt_ref = descriptor
        .source_refs
        .iter()
        .find(|source| {
            source
                .retained_fields
                .iter()
                .any(|field| field.contains("prompt"))
        })
        .map(|source| source.source_ref_id.clone())
        .unwrap_or_else(|| "prompt:unavailable".to_string());
    let policy_ref = descriptor
        .source_refs
        .iter()
        .find(|source| {
            source
                .retained_fields
                .iter()
                .any(|field| field.contains("policy"))
        })
        .map(|source| source.source_ref_id.clone())
        .unwrap_or_else(|| "policy:unavailable".to_string());
    let candidate_ref = descriptor
        .action_class_candidates
        .first()
        .map(|candidate| candidate.candidate_id.clone())
        .unwrap_or_else(|| descriptor.descriptor_id.clone());
    let missing_evidence_ids = descriptor
        .missing_evidence
        .iter()
        .map(|evidence| evidence.evidence_id.clone())
        .collect::<Vec<_>>();
    let retained_fields = descriptor
        .source_refs
        .iter()
        .flat_map(|source| source.retained_fields.iter().cloned())
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect::<Vec<_>>();

    AiProposalGovernanceV0 {
        schema_version: AI_PROPOSAL_GOVERNANCE_SCHEMA_VERSION.to_string(),
        governance_id: format!("governance:{}", descriptor.descriptor_id),
        proposal_ref: AiProposalGovernanceProposalRefV0 {
            proposal_source_ref_id,
            descriptor_id: descriptor.descriptor_id.clone(),
            descriptor_schema_version: ARTIFACT_DESCRIPTOR_SCHEMA_VERSION.to_string(),
            operation_support_estimate_id: operation_support_estimate_id.map(str::to_string),
            consequence_envelope_id: consequence_envelope_id.map(str::to_string),
            source_ref_ids: source_ref_ids.clone(),
            non_conclusions: strings(&GOVERNANCE_NON_CONCLUSIONS),
        },
        prompt_policy_boundary: AiProposalPromptPolicyBoundaryV0 {
            boundary_id: format!("boundary:prompt-policy:{}", descriptor.descriptor_id),
            prompt_ref,
            policy_ref,
            source_ref_ids: source_ref_ids.clone(),
            retained_fields,
            unavailable_fields: vec![
                "model-internal-reasoning".to_string(),
                "authenticated-policy-evaluation".to_string(),
                "organization-private-context".to_string(),
            ],
            boundary: "prompt and policy refs are retained as proposal context only".to_string(),
            non_conclusions: strings(&GOVERNANCE_NON_CONCLUSIONS),
        },
        support_assessments: vec![
            AiProposalSupportAssessmentV0 {
                assessment_id: "support:conditionally-allowed-review".to_string(),
                support_category: "conditionallyAllowed".to_string(),
                applies_to_ref: candidate_ref.clone(),
                source_ref_ids: source_ref_ids.clone(),
                rationale: "descriptor and SFT forecast refs are sufficient for bounded review, but human review and CI evidence remain required".to_string(),
                required_follow_up: vec![
                    "human architecture review".to_string(),
                    "CI result reference".to_string(),
                    "calibration or outcome ref if merged".to_string(),
                ],
                non_conclusions: strings(&GOVERNANCE_NON_CONCLUSIONS),
            },
            AiProposalSupportAssessmentV0 {
                assessment_id: "support:unknown-runtime".to_string(),
                support_category: "unknown".to_string(),
                applies_to_ref: "runtime-propagation".to_string(),
                source_ref_ids: source_ref_ids.clone(),
                rationale: "AI proposal descriptor does not observe runtime traces or incident history".to_string(),
                required_follow_up: vec!["runtime evidence or operational feedback hook".to_string()],
                non_conclusions: strings(&GOVERNANCE_NON_CONCLUSIONS),
            },
            AiProposalSupportAssessmentV0 {
                assessment_id: "support:forbidden-safety-upgrade".to_string(),
                support_category: "forbidden".to_string(),
                applies_to_ref: "architecture-lawfulness-claim".to_string(),
                source_ref_ids: source_ref_ids.clone(),
                rationale: "policy compliance, review, CI, and schema validation cannot be upgraded to architecture lawfulness".to_string(),
                required_follow_up: vec!["remove theorem-like or global safety claim".to_string()],
                non_conclusions: strings(&GOVERNANCE_NON_CONCLUSIONS),
            },
        ],
        shortcut_witnesses: vec![
            AiProposalShortcutWitnessV0 {
                witness_id: "shortcut:witness-boundary-skip".to_string(),
                shortcut_kind: "witness-boundary shortcut".to_string(),
                affected_ref: candidate_ref,
                source_ref_ids: source_ref_ids.clone(),
                evidence_boundary: "proposal lacks independent obstruction witness or theorem precondition evidence".to_string(),
                mediation_ref_ids: vec!["mediation:review-ci-required".to_string()],
                non_conclusions: strings(&GOVERNANCE_NON_CONCLUSIONS),
            },
            AiProposalShortcutWitnessV0 {
                witness_id: "shortcut:runtime-boundary".to_string(),
                shortcut_kind: "runtime-boundary shortcut".to_string(),
                affected_ref: "runtime-propagation".to_string(),
                source_ref_ids: source_ref_ids.clone(),
                evidence_boundary: "timeout, retry, ownership, and incident response effects are outside the proposal JSON input".to_string(),
                mediation_ref_ids: vec!["mediation:review-ci-required".to_string()],
                non_conclusions: strings(&GOVERNANCE_NON_CONCLUSIONS),
            },
        ],
        review_ci_mediation: AiProposalReviewCiMediationV0 {
            mediation_id: "mediation:review-ci-required".to_string(),
            review_refs: vec!["review:required-human-architecture-review".to_string()],
            ci_refs: vec!["ci:required-post-proposal-checks".to_string()],
            decision_boundary: "review and CI refs mediate acceptance but do not prove safety, forecast correctness, or lawfulness".to_string(),
            required_human_checks: vec![
                "claim boundary review".to_string(),
                "shortcut witness review".to_string(),
                "missing evidence review".to_string(),
            ],
            non_conclusions: strings(&GOVERNANCE_NON_CONCLUSIONS),
        },
        posterior_field_update: AiProposalPosteriorFieldUpdateV0 {
            update_id: "posterior:update-after-review-or-outcome".to_string(),
            update_kind: "bounded-calibration-hook".to_string(),
            calibration_refs: vec![
                FORECAST_CALIBRATION_HOOK_SCHEMA_VERSION.to_string(),
                "B10/B11 operational feedback refs when available".to_string(),
            ],
            retained_unknown_axes: vec![
                "future reviewer behavior".to_string(),
                "private operational context".to_string(),
                "runtime propagation".to_string(),
            ],
            field_update_boundary: "posterior update stores observed refs for later calibration without asserting causal correctness".to_string(),
            non_conclusions: strings(&GOVERNANCE_NON_CONCLUSIONS),
        },
        evidence_boundary: AiProposalGovernanceEvidenceBoundaryV0 {
            boundary_id: format!("boundary:evidence:{}", descriptor.descriptor_id),
            artifact_refs: vec![
                ARTIFACT_DESCRIPTOR_SCHEMA_VERSION.to_string(),
                OPERATION_SUPPORT_ESTIMATE_SCHEMA_VERSION.to_string(),
                CONSEQUENCE_ENVELOPE_REPORT_SCHEMA_VERSION.to_string(),
            ],
            missing_evidence_refs: missing_evidence_ids,
            unsupported_constructs: vec![
                "AI safety theorem".to_string(),
                "forecast correctness proof".to_string(),
                "architecture lawfulness proof".to_string(),
                "authenticated GitHub fetch".to_string(),
                "LLM benchmark evaluation".to_string(),
            ],
            measurement_boundary: "governance projection over supplied proposal and SFT artifact refs".to_string(),
            non_conclusions: strings(&GOVERNANCE_NON_CONCLUSIONS),
        },
        non_conclusions: strings(&GOVERNANCE_NON_CONCLUSIONS),
    }
}

pub fn validate_ai_proposal_governance(
    governance: &AiProposalGovernanceV0,
    input_path: &str,
) -> AiProposalGovernanceValidationReportV0 {
    let checks = vec![
        check_schema(governance),
        check_support_categories(governance),
        check_prompt_policy_boundary(governance),
        check_shortcut_witnesses(governance),
        check_review_ci_and_posterior(governance),
        check_required_non_conclusions(governance),
    ];
    let summary = AiProposalGovernanceValidationSummary {
        result: validation_result(&checks),
        support_assessment_count: governance.support_assessments.len(),
        shortcut_witness_count: governance.shortcut_witnesses.len(),
        failed_check_count: count_checks(&checks, "fail"),
        warning_check_count: count_checks(&checks, "warn"),
    };

    AiProposalGovernanceValidationReportV0 {
        schema_version: AI_PROPOSAL_GOVERNANCE_VALIDATION_REPORT_SCHEMA_VERSION.to_string(),
        input: AiProposalGovernanceValidationInput {
            schema_version: governance.schema_version.clone(),
            path: input_path.to_string(),
            governance_id: governance.governance_id.clone(),
            descriptor_id: governance.proposal_ref.descriptor_id.clone(),
        },
        governance: governance.clone(),
        summary,
        checks,
    }
}

fn check_schema(governance: &AiProposalGovernanceV0) -> ValidationCheck {
    let mut check = validation_check(
        "ai-governance-schema-version",
        "AI proposal governance schema version is supported",
        "pass",
    );
    if governance.schema_version != AI_PROPOSAL_GOVERNANCE_SCHEMA_VERSION {
        check.result = "fail".to_string();
        check.reason = Some(format!(
            "expected {}, found {}",
            AI_PROPOSAL_GOVERNANCE_SCHEMA_VERSION, governance.schema_version
        ));
    }
    check
}

fn check_support_categories(governance: &AiProposalGovernanceV0) -> ValidationCheck {
    let invalid = governance
        .support_assessments
        .iter()
        .filter(|assessment| !SUPPORT_CATEGORIES.contains(&assessment.support_category.as_str()))
        .map(|assessment| assessment.assessment_id.clone())
        .collect::<Vec<_>>();
    let mut check = validation_check(
        "ai-governance-support-categories",
        "Support assessments use the governance support taxonomy",
        "pass",
    );
    check.count = Some(governance.support_assessments.len());
    if governance.support_assessments.is_empty() {
        check.result = "fail".to_string();
        check.reason = Some("at least one support assessment is required".to_string());
    } else if !invalid.is_empty() {
        check.result = "fail".to_string();
        check.reason = Some(format!(
            "invalid support assessment ids: {}",
            invalid.join(", ")
        ));
    }
    check
}

fn check_prompt_policy_boundary(governance: &AiProposalGovernanceV0) -> ValidationCheck {
    let mut check = validation_check(
        "ai-governance-prompt-policy-boundary",
        "Prompt and policy boundary retains refs without claiming policy correctness",
        "pass",
    );
    if governance.prompt_policy_boundary.prompt_ref.is_empty()
        || governance.prompt_policy_boundary.policy_ref.is_empty()
        || governance.prompt_policy_boundary.boundary.is_empty()
    {
        check.result = "fail".to_string();
        check.reason = Some("prompt ref, policy ref, and boundary are required".to_string());
    }
    check
}

fn check_shortcut_witnesses(governance: &AiProposalGovernanceV0) -> ValidationCheck {
    let mut check = validation_check(
        "ai-governance-shortcut-witnesses",
        "Shortcut witness taxonomy is machine-readable",
        "pass",
    );
    check.count = Some(governance.shortcut_witnesses.len());
    if governance.shortcut_witnesses.is_empty() {
        check.result = "warn".to_string();
        check.reason = Some("no shortcut witnesses are recorded".to_string());
    } else if governance
        .shortcut_witnesses
        .iter()
        .any(|witness| witness.shortcut_kind.is_empty() || witness.evidence_boundary.is_empty())
    {
        check.result = "fail".to_string();
        check.reason =
            Some("each shortcut witness requires kind and evidence boundary".to_string());
    }
    check
}

fn check_review_ci_and_posterior(governance: &AiProposalGovernanceV0) -> ValidationCheck {
    let mut check = validation_check(
        "ai-governance-review-ci-posterior-boundary",
        "Review, CI, and posterior update boundaries are explicit",
        "pass",
    );
    if governance.review_ci_mediation.decision_boundary.is_empty()
        || governance
            .posterior_field_update
            .field_update_boundary
            .is_empty()
        || governance.evidence_boundary.measurement_boundary.is_empty()
    {
        check.result = "fail".to_string();
        check.reason =
            Some("review/CI, posterior update, and evidence boundaries are required".to_string());
    }
    check
}

fn check_required_non_conclusions(governance: &AiProposalGovernanceV0) -> ValidationCheck {
    let missing = GOVERNANCE_NON_CONCLUSIONS
        .iter()
        .filter(|required| {
            !governance
                .non_conclusions
                .iter()
                .any(|actual| actual == *required)
        })
        .copied()
        .collect::<Vec<_>>();
    let mut check = validation_check(
        "ai-governance-non-conclusions-preserved",
        "AI governance non-conclusions are preserved",
        "pass",
    );
    if !missing.is_empty() {
        check.result = "fail".to_string();
        check.reason = Some(format!("missing non-conclusions: {}", missing.join("; ")));
    }
    check
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
    values.iter().map(|value| (*value).to_string()).collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn static_governance_validates_and_records_claim_boundary() {
        let governance = static_ai_proposal_governance();
        let validation = validate_ai_proposal_governance(&governance, "static");

        assert_eq!(validation.summary.result, "pass");
        assert!(governance.support_assessments.iter().any(|assessment| {
            assessment.support_category == "forbidden"
                && assessment.applies_to_ref == "architecture-lawfulness-claim"
        }));
        assert!(
            governance
                .non_conclusions
                .iter()
                .any(|item| item.contains("not an AI safety theorem"))
        );
    }

    #[test]
    fn invalid_support_category_fails_validation() {
        let mut governance = static_ai_proposal_governance();
        governance.support_assessments[0].support_category = "safe".to_string();
        let validation = validate_ai_proposal_governance(&governance, "static");

        assert_eq!(validation.summary.result, "fail");
    }
}
