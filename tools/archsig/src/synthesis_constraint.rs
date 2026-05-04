use std::collections::BTreeSet;

use crate::validation::{count_checks, duplicates, generic_validation_example, validation_check};
use crate::{
    SYNTHESIS_CONSTRAINT_ARTIFACT_SCHEMA_VERSION,
    SYNTHESIS_CONSTRAINT_VALIDATION_REPORT_SCHEMA_VERSION, SynthesisCandidateV0,
    SynthesisConstraintArtifactV0, SynthesisConstraintV0, SynthesisConstraintValidationInput,
    SynthesisConstraintValidationReportV0, SynthesisConstraintValidationSummary,
    SynthesisNoSolutionBoundaryV0, ValidationCheck,
};

const REQUIRED_NON_CONCLUSIONS: [&str; 4] = [
    "produced candidate soundness is conditional on recorded assumptions",
    "solver completeness is not concluded",
    "solver no-candidate result is not a no-solution certificate",
    "valid no-solution certificate is checked separately",
];

const SUPPORTED_CONSTRAINT_KINDS: [&str; 6] = [
    "static",
    "runtime",
    "semantic",
    "policy",
    "operation",
    "synthesis",
];

const SUPPORTED_SOLVER_STATUSES: [&str; 4] = [
    "not_run",
    "candidate_produced",
    "no_candidate",
    "certificate_supplied",
];

pub fn static_synthesis_constraint_artifact() -> SynthesisConstraintArtifactV0 {
    SynthesisConstraintArtifactV0 {
        schema_version: SYNTHESIS_CONSTRAINT_ARTIFACT_SCHEMA_VERSION.to_string(),
        scope: "synthesis constraint artifact v0 for selected obstruction witnesses".to_string(),
        constraint_refs: vec![
            "constraint-static-boundary-coupon-v0".to_string(),
            "constraint-semantic-rounding-contract-v0".to_string(),
        ],
        candidate_refs: vec!["candidate-split-coupon-interface-v0".to_string()],
        required_assumptions: vec![
            "selected obstruction witnesses resolve in the current Feature Extension Report"
                .to_string(),
            "candidate operations are interpreted inside the selected measurement universe"
                .to_string(),
        ],
        coverage_assumptions: vec![
            "static dependency and selected semantic diagram evidence are included".to_string(),
            "unsupported constructs are reported rather than discharged".to_string(),
        ],
        exactness_assumptions: vec![
            "constraint refs name the selected bounded synthesis package inputs".to_string(),
            "candidate refs name produced candidates, not solver completeness evidence".to_string(),
        ],
        unsupported_constructs: vec![
            "unbounded search spaces are outside synthesis artifact v0".to_string(),
        ],
        constraints: vec![
            synthesis_constraint(
                "constraint-static-boundary-coupon-v0",
                "static",
                "relation.UserService.CouponService",
                "candidate must route forbidden static edge through an allowed boundary",
                &["evidence-static-boundary-violation"],
                &["NoNewForbiddenStaticEdge", "SynthesisConstraintSystem"],
            ),
            synthesis_constraint(
                "constraint-semantic-rounding-contract-v0",
                "semantic",
                "semantic.diagram.diagram-coupon-discount-order",
                "candidate must preserve selected coupon / discount observation contract",
                &[
                    "evidence-coupon-diagram",
                    "evidence-rounding-order-difference",
                ],
                &[
                    "SynthesisSoundnessPackage.candidate_satisfies",
                    "obstructionAsNonFillability_sound",
                ],
            ),
        ],
        candidates: vec![synthesis_candidate(
            "candidate-split-coupon-interface-v0",
            "bounded synthesis prototype",
            &["operation.split.CouponPort"],
            &[
                "constraint-static-boundary-coupon-v0",
                "constraint-semantic-rounding-contract-v0",
            ],
            &[
                "SynthesisSoundnessPackage.candidate_satisfies",
                "ArchitectureCalculusLaw.synthesisCandidateSoundnessLaw_conclusion",
            ],
            &[
                "interface contract covers both selected coupon paths",
                "candidate operation refs resolve to the bounded operation package",
            ],
            &[
                "static and semantic evidence refs cover the selected constraints",
                "runtime behavior is checked separately if runtime edges are present",
            ],
            &[
                "selected observation equality assumptions are recorded",
                "unsupported constructs are not silently discharged",
            ],
            &["global semantic completeness is outside this candidate"],
        )],
        no_solution_boundary: SynthesisNoSolutionBoundaryV0 {
            solver_status: "candidate_produced".to_string(),
            candidate_refs: vec!["candidate-split-coupon-interface-v0".to_string()],
            no_solution_certificate_ref: None,
            valid_certificate_claim_ref: None,
            non_conclusions: REQUIRED_NON_CONCLUSIONS
                .iter()
                .map(|value| value.to_string())
                .collect(),
        },
        non_conclusions: REQUIRED_NON_CONCLUSIONS
            .iter()
            .map(|value| value.to_string())
            .collect(),
    }
}

pub fn validate_synthesis_constraint_artifact_report(
    artifact: &SynthesisConstraintArtifactV0,
    input_path: &str,
) -> SynthesisConstraintValidationReportV0 {
    let checks = vec![
        check_schema_version(artifact),
        check_constraint_ids_and_refs(artifact),
        check_candidate_ids_and_refs(artifact),
        check_constraint_kinds(artifact),
        check_assumption_boundary(artifact),
        check_candidate_soundness_boundary(artifact),
        check_no_solution_boundary(artifact),
        check_non_conclusion_boundary(artifact),
    ];
    let summary = SynthesisConstraintValidationSummary {
        result: if checks.iter().any(|check| check.result == "fail") {
            "fail".to_string()
        } else if checks.iter().any(|check| check.result == "warn") {
            "warn".to_string()
        } else {
            "pass".to_string()
        },
        constraint_count: artifact.constraints.len(),
        candidate_count: artifact.candidates.len(),
        failed_check_count: count_checks(&checks, "fail"),
        warning_check_count: count_checks(&checks, "warn"),
    };

    SynthesisConstraintValidationReportV0 {
        schema_version: SYNTHESIS_CONSTRAINT_VALIDATION_REPORT_SCHEMA_VERSION.to_string(),
        input: SynthesisConstraintValidationInput {
            schema_version: artifact.schema_version.clone(),
            path: input_path.to_string(),
            scope: artifact.scope.clone(),
        },
        artifact: artifact.clone(),
        summary,
        checks,
    }
}

fn synthesis_constraint(
    constraint_id: &str,
    kind: &str,
    subject_ref: &str,
    predicate: &str,
    evidence_refs: &[&str],
    theorem_precondition_refs: &[&str],
) -> SynthesisConstraintV0 {
    SynthesisConstraintV0 {
        constraint_id: constraint_id.to_string(),
        kind: kind.to_string(),
        subject_ref: subject_ref.to_string(),
        predicate: predicate.to_string(),
        evidence_refs: strings(evidence_refs),
        theorem_precondition_refs: strings(theorem_precondition_refs),
    }
}

fn synthesis_candidate(
    candidate_id: &str,
    produced_by: &str,
    operation_refs: &[&str],
    constraint_refs: &[&str],
    soundness_package_refs: &[&str],
    required_assumptions: &[&str],
    coverage_assumptions: &[&str],
    exactness_assumptions: &[&str],
    unsupported_constructs: &[&str],
) -> SynthesisCandidateV0 {
    SynthesisCandidateV0 {
        candidate_id: candidate_id.to_string(),
        produced_by: produced_by.to_string(),
        operation_refs: strings(operation_refs),
        constraint_refs: strings(constraint_refs),
        soundness_package_refs: strings(soundness_package_refs),
        required_assumptions: strings(required_assumptions),
        coverage_assumptions: strings(coverage_assumptions),
        exactness_assumptions: strings(exactness_assumptions),
        unsupported_constructs: strings(unsupported_constructs),
        non_conclusions: REQUIRED_NON_CONCLUSIONS
            .iter()
            .map(|value| value.to_string())
            .collect(),
    }
}

fn strings(values: &[&str]) -> Vec<String> {
    values.iter().map(|value| value.to_string()).collect()
}

fn check_schema_version(artifact: &SynthesisConstraintArtifactV0) -> ValidationCheck {
    let mut check = validation_check(
        "synthesis-constraint-schema-version-supported",
        "synthesis constraint artifact schema version is supported",
        if artifact.schema_version == SYNTHESIS_CONSTRAINT_ARTIFACT_SCHEMA_VERSION {
            "pass"
        } else {
            "fail"
        },
    );
    if check.result == "fail" {
        check.reason = Some(format!(
            "unsupported synthesis constraint schemaVersion: {}",
            artifact.schema_version
        ));
    }
    check
}

fn check_constraint_ids_and_refs(artifact: &SynthesisConstraintArtifactV0) -> ValidationCheck {
    let ids = string_set_from(
        artifact
            .constraints
            .iter()
            .map(|constraint| constraint.constraint_id.as_str()),
    );
    let duplicate_ids = duplicates(
        artifact
            .constraints
            .iter()
            .map(|constraint| constraint.constraint_id.as_str()),
    );
    let mut invalid = Vec::new();
    invalid.extend(
        duplicate_ids
            .into_iter()
            .map(|id| generic_validation_example(&id, &id, "duplicate constraint_id")),
    );
    invalid.extend(
        artifact
            .constraints
            .iter()
            .filter(|constraint| constraint.constraint_id.trim().is_empty())
            .map(|constraint| {
                generic_validation_example(
                    &constraint.subject_ref,
                    &constraint.kind,
                    "constraint_id must be non-empty",
                )
            }),
    );
    invalid.extend(
        artifact
            .constraint_refs
            .iter()
            .filter(|constraint_ref| !ids.contains(constraint_ref.as_str()))
            .map(|constraint_ref| {
                generic_validation_example(
                    "artifact.constraintRefs",
                    constraint_ref,
                    "constraint ref does not resolve",
                )
            }),
    );
    check_examples(
        "synthesis-constraint-refs-resolve",
        "constraint ids are unique and top-level constraint refs resolve",
        invalid,
    )
}

fn check_candidate_ids_and_refs(artifact: &SynthesisConstraintArtifactV0) -> ValidationCheck {
    let constraint_ids = string_set_from(
        artifact
            .constraints
            .iter()
            .map(|constraint| constraint.constraint_id.as_str()),
    );
    let candidate_ids = string_set_from(
        artifact
            .candidates
            .iter()
            .map(|candidate| candidate.candidate_id.as_str()),
    );
    let duplicate_ids = duplicates(
        artifact
            .candidates
            .iter()
            .map(|candidate| candidate.candidate_id.as_str()),
    );
    let mut invalid = Vec::new();
    invalid.extend(
        duplicate_ids
            .into_iter()
            .map(|id| generic_validation_example(&id, &id, "duplicate candidate_id")),
    );
    invalid.extend(
        artifact
            .candidate_refs
            .iter()
            .filter(|candidate_ref| !candidate_ids.contains(candidate_ref.as_str()))
            .map(|candidate_ref| {
                generic_validation_example(
                    "artifact.candidateRefs",
                    candidate_ref,
                    "candidate ref does not resolve",
                )
            }),
    );
    invalid.extend(artifact.candidates.iter().flat_map(|candidate| {
        candidate
            .constraint_refs
            .iter()
            .filter(|constraint_ref| !constraint_ids.contains(constraint_ref.as_str()))
            .map(|constraint_ref| {
                generic_validation_example(
                    &candidate.candidate_id,
                    constraint_ref,
                    "candidate constraint ref does not resolve",
                )
            })
    }));
    invalid.extend(
        artifact
            .no_solution_boundary
            .candidate_refs
            .iter()
            .filter(|candidate_ref| !candidate_ids.contains(candidate_ref.as_str()))
            .map(|candidate_ref| {
                generic_validation_example(
                    "noSolutionBoundary.candidateRefs",
                    candidate_ref,
                    "candidate ref does not resolve",
                )
            }),
    );
    check_examples(
        "synthesis-candidate-refs-resolve",
        "candidate ids are unique and candidate refs resolve",
        invalid,
    )
}

fn check_constraint_kinds(artifact: &SynthesisConstraintArtifactV0) -> ValidationCheck {
    let supported = string_set(SUPPORTED_CONSTRAINT_KINDS);
    let invalid = artifact
        .constraints
        .iter()
        .filter(|constraint| !supported.contains(constraint.kind.as_str()))
        .map(|constraint| {
            generic_validation_example(
                &constraint.constraint_id,
                &constraint.kind,
                "unsupported constraint kind",
            )
        })
        .collect();
    check_examples(
        "synthesis-constraint-kind-supported",
        "constraint kind is supported",
        invalid,
    )
}

fn check_assumption_boundary(artifact: &SynthesisConstraintArtifactV0) -> ValidationCheck {
    let mut invalid = Vec::new();
    if artifact.required_assumptions.is_empty()
        || artifact.coverage_assumptions.is_empty()
        || artifact.exactness_assumptions.is_empty()
        || has_blank(&artifact.required_assumptions)
        || has_blank(&artifact.coverage_assumptions)
        || has_blank(&artifact.exactness_assumptions)
    {
        invalid.push(generic_validation_example(
            "artifact",
            &artifact.scope,
            "required, coverage, and exactness assumptions must be recorded",
        ));
    }
    invalid.extend(
        artifact
            .constraints
            .iter()
            .filter(|constraint| {
                constraint.subject_ref.trim().is_empty()
                    || constraint.predicate.trim().is_empty()
                    || constraint.theorem_precondition_refs.is_empty()
                    || has_blank(&constraint.theorem_precondition_refs)
            })
            .map(|constraint| {
                generic_validation_example(
                    &constraint.constraint_id,
                    &constraint.kind,
                    "constraint subject, predicate, and theorem precondition refs must be recorded",
                )
            }),
    );
    check_examples(
        "synthesis-assumption-boundary-recorded",
        "required, coverage, exactness, and theorem precondition boundary are recorded",
        invalid,
    )
}

fn check_candidate_soundness_boundary(artifact: &SynthesisConstraintArtifactV0) -> ValidationCheck {
    let invalid = artifact
        .candidates
        .iter()
        .filter(|candidate| {
            candidate.candidate_id.trim().is_empty()
                || candidate.produced_by.trim().is_empty()
                || candidate.operation_refs.is_empty()
                || candidate.constraint_refs.is_empty()
                || candidate.soundness_package_refs.is_empty()
                || candidate.required_assumptions.is_empty()
                || candidate.coverage_assumptions.is_empty()
                || candidate.exactness_assumptions.is_empty()
                || has_blank(&candidate.operation_refs)
                || has_blank(&candidate.constraint_refs)
                || has_blank(&candidate.soundness_package_refs)
                || has_blank(&candidate.required_assumptions)
                || has_blank(&candidate.coverage_assumptions)
                || has_blank(&candidate.exactness_assumptions)
        })
        .map(|candidate| {
            generic_validation_example(
                &candidate.candidate_id,
                &candidate.produced_by,
                "candidate must record operation refs, constraint refs, soundness package refs, and assumptions",
            )
        })
        .collect();
    check_examples(
        "synthesis-candidate-soundness-boundary-recorded",
        "candidate soundness package and theorem precondition boundary are recorded",
        invalid,
    )
}

fn check_no_solution_boundary(artifact: &SynthesisConstraintArtifactV0) -> ValidationCheck {
    let supported = string_set(SUPPORTED_SOLVER_STATUSES);
    let boundary = &artifact.no_solution_boundary;
    let mut invalid = Vec::new();
    if !supported.contains(boundary.solver_status.as_str()) {
        invalid.push(generic_validation_example(
            "noSolutionBoundary.solverStatus",
            &boundary.solver_status,
            "unsupported solver status",
        ));
    }
    if boundary.solver_status == "candidate_produced" && boundary.candidate_refs.is_empty() {
        invalid.push(generic_validation_example(
            "noSolutionBoundary",
            &boundary.solver_status,
            "candidate_produced must record candidate refs",
        ));
    }
    if boundary.solver_status == "certificate_supplied"
        && (boundary.no_solution_certificate_ref.is_none()
            || boundary.valid_certificate_claim_ref.is_none())
    {
        invalid.push(generic_validation_example(
            "noSolutionBoundary",
            &boundary.solver_status,
            "certificate_supplied must record certificate and valid certificate claim refs",
        ));
    }
    if boundary.solver_status == "no_candidate"
        && boundary.no_solution_certificate_ref.is_none()
        && !boundary.non_conclusions.iter().any(|conclusion| {
            conclusion == "solver no-candidate result is not a no-solution certificate"
        })
    {
        invalid.push(generic_validation_example(
            "noSolutionBoundary",
            &boundary.solver_status,
            "no_candidate without certificate must record non-solution non-conclusion",
        ));
    }
    check_examples(
        "synthesis-no-solution-boundary-distinguished",
        "solver no-candidate result and valid no-solution certificate are distinguished",
        invalid,
    )
}

fn check_non_conclusion_boundary(artifact: &SynthesisConstraintArtifactV0) -> ValidationCheck {
    let required = string_set(REQUIRED_NON_CONCLUSIONS);
    let mut invalid = Vec::new();
    if !contains_all(&artifact.non_conclusions, &required) {
        invalid.push(generic_validation_example(
            "artifact",
            &artifact.scope,
            "artifact non-conclusions must include synthesis boundary",
        ));
    }
    if !contains_all(&artifact.no_solution_boundary.non_conclusions, &required) {
        invalid.push(generic_validation_example(
            "noSolutionBoundary",
            &artifact.no_solution_boundary.solver_status,
            "no-solution boundary non-conclusions must include solver completeness boundary",
        ));
    }
    invalid.extend(
        artifact
            .candidates
            .iter()
            .filter(|candidate| !contains_all(&candidate.non_conclusions, &required))
            .map(|candidate| {
                generic_validation_example(
                    &candidate.candidate_id,
                    &candidate.produced_by,
                    "candidate non-conclusions must include synthesis boundary",
                )
            }),
    );
    check_examples(
        "synthesis-non-conclusion-boundary-recorded",
        "synthesis non-conclusion boundary is recorded",
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn static_artifact_validates_and_records_solver_boundary() {
        let artifact = static_synthesis_constraint_artifact();
        let report = validate_synthesis_constraint_artifact_report(&artifact, "static");

        assert_eq!(report.summary.result, "pass");
        assert_eq!(report.summary.constraint_count, 2);
        assert_eq!(report.summary.candidate_count, 1);
        assert!(report.artifact.candidates.iter().any(|candidate| {
            candidate.candidate_id == "candidate-split-coupon-interface-v0"
                && candidate
                    .soundness_package_refs
                    .iter()
                    .any(|package| package == "SynthesisSoundnessPackage.candidate_satisfies")
                && candidate
                    .non_conclusions
                    .iter()
                    .any(|boundary| boundary == "solver completeness is not concluded")
        }));
    }

    #[test]
    fn validation_rejects_candidate_without_soundness_boundary() {
        let mut artifact = static_synthesis_constraint_artifact();
        artifact.candidate_refs = vec!["missing-candidate".to_string()];
        artifact.candidates[0].constraint_refs = vec!["missing-constraint".to_string()];
        artifact.candidates[0].soundness_package_refs.clear();
        artifact.candidates[0].required_assumptions.clear();
        artifact.no_solution_boundary.solver_status = "no_candidate".to_string();
        artifact.no_solution_boundary.non_conclusions.clear();
        artifact.non_conclusions.clear();

        let report = validate_synthesis_constraint_artifact_report(&artifact, "invalid");

        assert_eq!(report.summary.result, "fail");
        assert!(report.summary.failed_check_count >= 4);
        assert!(report.checks.iter().any(|check| {
            check.id == "synthesis-no-solution-boundary-distinguished" && check.result == "fail"
        }));
    }
}
