use std::collections::BTreeSet;

use crate::validation::{count_checks, duplicates, generic_validation_example, validation_check};
use crate::{
    NO_SOLUTION_CERTIFICATE_SCHEMA_VERSION,
    NO_SOLUTION_CERTIFICATE_VALIDATION_REPORT_SCHEMA_VERSION, NoSolutionCertificateCaseV0,
    NoSolutionCertificateV0, NoSolutionCertificateValidationInput,
    NoSolutionCertificateValidationReportV0, NoSolutionCertificateValidationSummary,
    ValidationCheck,
};

const REQUIRED_NON_CONCLUSIONS: [&str; 4] = [
    "valid certificate soundness is conditional on recorded assumptions",
    "solver completeness is not concluded",
    "solver no-candidate result is not a no-solution certificate",
    "candidate search exhaustion is scoped to recorded cases",
];

const REQUIRED_PROOF_OBLIGATION_REFS: [&str; 2] = [
    "ValidNoSolutionCertificate",
    "NoSolutionCertificate.sound_of_valid",
];

pub fn static_no_solution_certificate() -> NoSolutionCertificateV0 {
    NoSolutionCertificateV0 {
        schema_version: NO_SOLUTION_CERTIFICATE_SCHEMA_VERSION.to_string(),
        certificate_id: "certificate-coupon-no-solution-v0".to_string(),
        scope: "bounded no-solution certificate for selected coupon synthesis universe".to_string(),
        constraint_refs: vec![
            "constraint-static-boundary-coupon-v0".to_string(),
            "constraint-semantic-rounding-contract-v0".to_string(),
        ],
        refuted_candidate_refs: vec![
            "candidate-direct-cache-access-v0".to_string(),
            "candidate-ignore-rounding-contract-v0".to_string(),
        ],
        obstruction_witness_refs: vec![
            "witness-hidden-cache-access".to_string(),
            "witness-rounding-order-difference".to_string(),
        ],
        required_assumptions: vec![
            "candidate universe is finite and explicitly enumerated".to_string(),
            "each refuted candidate is interpreted inside the selected measurement universe"
                .to_string(),
        ],
        coverage_assumptions: vec![
            "certificate cases cover the recorded candidate refs".to_string(),
            "unsupported constructs are reported rather than discharged".to_string(),
        ],
        exactness_assumptions: vec![
            "constraint refs name the selected bounded synthesis package inputs".to_string(),
            "case evidence refs name the selected obstruction witnesses".to_string(),
        ],
        unsupported_constructs: vec![
            "unbounded candidate generation is outside no-solution-certificate-v0".to_string(),
        ],
        proof_obligation_refs: REQUIRED_PROOF_OBLIGATION_REFS
            .iter()
            .map(|value| value.to_string())
            .collect(),
        valid_certificate_claim_ref: Some("claim-valid-no-solution-certificate".to_string()),
        cases: vec![
            no_solution_case(
                "case-direct-cache-still-breaks-boundary",
                &["constraint-static-boundary-coupon-v0"],
                Some("candidate-direct-cache-access-v0"),
                &["evidence-hidden-edge"],
                &["ValidNoSolutionCertificate"],
                "candidate preserves the forbidden cache dependency in the selected static universe",
            ),
            no_solution_case(
                "case-ignore-rounding-contract-still-breaks-semantics",
                &["constraint-semantic-rounding-contract-v0"],
                Some("candidate-ignore-rounding-contract-v0"),
                &["evidence-rounding-order-difference"],
                &["NoSolutionCertificate.sound_of_valid"],
                "candidate does not discharge the selected coupon / discount observation contract",
            ),
        ],
        non_conclusions: REQUIRED_NON_CONCLUSIONS
            .iter()
            .map(|value| value.to_string())
            .collect(),
    }
}

pub fn validate_no_solution_certificate_report(
    certificate: &NoSolutionCertificateV0,
    input_path: &str,
) -> NoSolutionCertificateValidationReportV0 {
    let checks = vec![
        check_schema_version(certificate),
        check_certificate_id(certificate),
        check_case_ids_and_refs(certificate),
        check_assumption_boundary(certificate),
        check_valid_certificate_boundary(certificate),
        check_non_conclusion_boundary(certificate),
    ];
    let summary = NoSolutionCertificateValidationSummary {
        result: if checks.iter().any(|check| check.result == "fail") {
            "fail".to_string()
        } else if checks.iter().any(|check| check.result == "warn") {
            "warn".to_string()
        } else {
            "pass".to_string()
        },
        case_count: certificate.cases.len(),
        refuted_candidate_count: certificate.refuted_candidate_refs.len(),
        failed_check_count: count_checks(&checks, "fail"),
        warning_check_count: count_checks(&checks, "warn"),
    };

    NoSolutionCertificateValidationReportV0 {
        schema_version: NO_SOLUTION_CERTIFICATE_VALIDATION_REPORT_SCHEMA_VERSION.to_string(),
        input: NoSolutionCertificateValidationInput {
            schema_version: certificate.schema_version.clone(),
            path: input_path.to_string(),
            certificate_id: certificate.certificate_id.clone(),
        },
        certificate: certificate.clone(),
        summary,
        checks,
    }
}

fn no_solution_case(
    case_id: &str,
    constraint_refs: &[&str],
    refuted_candidate_ref: Option<&str>,
    evidence_refs: &[&str],
    theorem_precondition_refs: &[&str],
    reason: &str,
) -> NoSolutionCertificateCaseV0 {
    NoSolutionCertificateCaseV0 {
        case_id: case_id.to_string(),
        constraint_refs: strings(constraint_refs),
        refuted_candidate_ref: refuted_candidate_ref.map(str::to_string),
        evidence_refs: strings(evidence_refs),
        theorem_precondition_refs: strings(theorem_precondition_refs),
        reason: reason.to_string(),
    }
}

fn check_schema_version(certificate: &NoSolutionCertificateV0) -> ValidationCheck {
    let mut check = validation_check(
        "no-solution-certificate-schema-version-supported",
        "no-solution certificate schema version is supported",
        if certificate.schema_version == NO_SOLUTION_CERTIFICATE_SCHEMA_VERSION {
            "pass"
        } else {
            "fail"
        },
    );
    if check.result == "fail" {
        check.reason = Some(format!(
            "unsupported no-solution certificate schemaVersion: {}",
            certificate.schema_version
        ));
    }
    check
}

fn check_certificate_id(certificate: &NoSolutionCertificateV0) -> ValidationCheck {
    let mut invalid = Vec::new();
    if certificate.certificate_id.trim().is_empty() {
        invalid.push(generic_validation_example(
            "certificateId",
            &certificate.scope,
            "certificate_id must be non-empty",
        ));
    }
    if certificate.scope.trim().is_empty() {
        invalid.push(generic_validation_example(
            &certificate.certificate_id,
            "scope",
            "scope must be non-empty",
        ));
    }
    check_examples(
        "no-solution-certificate-id-recorded",
        "certificate id and scope are recorded",
        invalid,
    )
}

fn check_case_ids_and_refs(certificate: &NoSolutionCertificateV0) -> ValidationCheck {
    let constraint_refs = string_set_from(certificate.constraint_refs.iter().map(String::as_str));
    let refuted_candidate_refs = string_set_from(
        certificate
            .refuted_candidate_refs
            .iter()
            .map(String::as_str),
    );
    let duplicate_case_ids = duplicates(certificate.cases.iter().map(|case| case.case_id.as_str()));
    let mut invalid = Vec::new();

    invalid.extend(
        duplicate_case_ids
            .into_iter()
            .map(|id| generic_validation_example(&id, &id, "duplicate case_id")),
    );
    invalid.extend(certificate.cases.iter().filter_map(|case| {
        case.case_id.trim().is_empty().then(|| {
            generic_validation_example("caseId", &case.reason, "case_id must be non-empty")
        })
    }));
    invalid.extend(certificate.cases.iter().flat_map(|case| {
        case.constraint_refs
            .iter()
            .filter(|constraint_ref| !constraint_refs.contains(constraint_ref.as_str()))
            .map(|constraint_ref| {
                generic_validation_example(
                    &case.case_id,
                    constraint_ref,
                    "case constraint ref must resolve to certificate.constraintRefs",
                )
            })
    }));
    invalid.extend(certificate.cases.iter().filter_map(|case| {
        let candidate_ref = case.refuted_candidate_ref.as_ref()?;
        (!refuted_candidate_refs.contains(candidate_ref.as_str())).then(|| {
            generic_validation_example(
                &case.case_id,
                candidate_ref,
                "case refuted candidate must resolve to certificate.refutedCandidateRefs",
            )
        })
    }));

    check_examples(
        "no-solution-certificate-case-refs-resolve",
        "certificate cases are unique and refs resolve inside the bounded universe",
        invalid,
    )
}

fn check_assumption_boundary(certificate: &NoSolutionCertificateV0) -> ValidationCheck {
    let mut invalid = Vec::new();
    if certificate.constraint_refs.is_empty()
        || certificate.refuted_candidate_refs.is_empty()
        || certificate.required_assumptions.is_empty()
        || certificate.coverage_assumptions.is_empty()
        || certificate.exactness_assumptions.is_empty()
        || has_blank(&certificate.constraint_refs)
        || has_blank(&certificate.refuted_candidate_refs)
        || has_blank(&certificate.required_assumptions)
        || has_blank(&certificate.coverage_assumptions)
        || has_blank(&certificate.exactness_assumptions)
    {
        invalid.push(generic_validation_example(
            &certificate.certificate_id,
            &certificate.scope,
            "constraint refs, refuted candidate refs, and assumption boundaries must be recorded",
        ));
    }
    invalid.extend(
        certificate
            .cases
            .iter()
            .filter(|case| {
                case.constraint_refs.is_empty()
                    || case.evidence_refs.is_empty()
                    || case.theorem_precondition_refs.is_empty()
                    || case.reason.trim().is_empty()
                    || has_blank(&case.constraint_refs)
                    || has_blank(&case.evidence_refs)
                    || has_blank(&case.theorem_precondition_refs)
            })
            .map(|case| {
                generic_validation_example(
                    &case.case_id,
                    &case.reason,
                    "case must record constraints, evidence, theorem preconditions, and reason",
                )
            }),
    );
    check_examples(
        "no-solution-certificate-assumption-boundary-recorded",
        "bounded universe, assumptions, evidence, and theorem preconditions are recorded",
        invalid,
    )
}

fn check_valid_certificate_boundary(certificate: &NoSolutionCertificateV0) -> ValidationCheck {
    let required = string_set(REQUIRED_PROOF_OBLIGATION_REFS);
    let mut invalid = Vec::new();
    if certificate.valid_certificate_claim_ref.is_none() {
        invalid.push(generic_validation_example(
            &certificate.certificate_id,
            "validCertificateClaimRef",
            "valid certificate claim ref is required; solver failure alone is not a certificate",
        ));
    }
    if !contains_all(&certificate.proof_obligation_refs, &required) {
        invalid.push(generic_validation_example(
            &certificate.certificate_id,
            "proofObligationRefs",
            "proof obligation refs must connect to ValidNoSolutionCertificate soundness",
        ));
    }
    check_examples(
        "no-solution-certificate-validity-boundary-recorded",
        "valid certificate claim and soundness proof obligation refs are recorded",
        invalid,
    )
}

fn check_non_conclusion_boundary(certificate: &NoSolutionCertificateV0) -> ValidationCheck {
    let required = string_set(REQUIRED_NON_CONCLUSIONS);
    let invalid = if contains_all(&certificate.non_conclusions, &required) {
        Vec::new()
    } else {
        vec![generic_validation_example(
            &certificate.certificate_id,
            &certificate.scope,
            "certificate non-conclusions must include solver completeness and bounded universe boundaries",
        )]
    };
    check_examples(
        "no-solution-certificate-non-conclusion-boundary-recorded",
        "no-solution certificate non-conclusion boundary is recorded",
        invalid,
    )
}

fn check_examples(
    id: &str,
    title: &str,
    examples: Vec<crate::ValidationExample>,
) -> ValidationCheck {
    let mut check = validation_check(id, title, if examples.is_empty() { "pass" } else { "fail" });
    check.count = Some(examples.len());
    check.examples = examples;
    check
}

fn string_set<const N: usize>(values: [&'static str; N]) -> BTreeSet<&'static str> {
    values.into_iter().collect()
}

fn string_set_from<'a>(values: impl Iterator<Item = &'a str>) -> BTreeSet<&'a str> {
    values.collect()
}

fn contains_all(values: &[String], required: &BTreeSet<&str>) -> bool {
    let actual: BTreeSet<&str> = values.iter().map(String::as_str).collect();
    required.iter().all(|value| actual.contains(value))
}

fn has_blank(values: &[String]) -> bool {
    values.iter().any(|value| value.trim().is_empty())
}

fn strings(values: &[&str]) -> Vec<String> {
    values.iter().map(|value| value.to_string()).collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn static_certificate_validates_and_records_solver_boundary() {
        let certificate = static_no_solution_certificate();
        let report = validate_no_solution_certificate_report(&certificate, "static");

        assert_eq!(report.summary.result, "pass");
        assert_eq!(report.summary.case_count, 2);
        assert!(report.certificate.non_conclusions.iter().any(|boundary| {
            boundary == "solver no-candidate result is not a no-solution certificate"
        }));
    }

    #[test]
    fn validation_rejects_missing_certificate_claim() {
        let mut certificate = static_no_solution_certificate();
        certificate.valid_certificate_claim_ref = None;
        certificate.proof_obligation_refs.clear();
        certificate.non_conclusions.clear();

        let report = validate_no_solution_certificate_report(&certificate, "invalid");

        assert_eq!(report.summary.result, "fail");
        assert!(report.checks.iter().any(|check| {
            check.id == "no-solution-certificate-validity-boundary-recorded"
                && check.result == "fail"
        }));
        assert!(report.checks.iter().any(|check| {
            check.id == "no-solution-certificate-non-conclusion-boundary-recorded"
                && check.result == "fail"
        }));
    }
}
