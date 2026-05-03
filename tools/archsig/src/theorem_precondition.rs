use std::collections::BTreeSet;

use crate::{
    AirClaim, AirDocumentV0, THEOREM_PRECONDITION_CHECK_REPORT_SCHEMA_VERSION,
    TheoremPackageMetadataV0, TheoremPackageRegistryV0, TheoremPreconditionCheck,
    TheoremPreconditionCheckInput, TheoremPreconditionCheckReportV0,
    TheoremPreconditionCheckSummary,
};

pub fn static_theorem_package_registry() -> TheoremPackageRegistryV0 {
    TheoremPackageRegistryV0 {
        schema_version: THEOREM_PRECONDITION_CHECK_REPORT_SCHEMA_VERSION.to_string(),
        scope: "static theorem package v0".to_string(),
        packages: vec![TheoremPackageMetadataV0 {
            package_id: "static-theorem-package-v0".to_string(),
            lean_entrypoint: "SelectedStaticSplitExtension".to_string(),
            theorem_refs: vec![
                "SelectedStaticSplitExtension".to_string(),
                "CoreEdgesPreserved".to_string(),
                "DeclaredInterfaceFactorization".to_string(),
                "NoNewForbiddenStaticEdge".to_string(),
                "EmbeddingPolicyPreserved".to_string(),
            ],
            supported_subject_refs: vec![
                "extension.embedding".to_string(),
                "extension.feature".to_string(),
                "extension.split".to_string(),
                "signature.hasCycle".to_string(),
                "signature.projectionSoundnessViolation".to_string(),
                "signature.lspViolationCount".to_string(),
                "signature.boundaryViolationCount".to_string(),
                "signature.abstractionViolationCount".to_string(),
            ],
            supported_axes: vec![
                "hasCycle".to_string(),
                "projectionSoundnessViolation".to_string(),
                "lspViolationCount".to_string(),
                "boundaryViolationCount".to_string(),
                "abstractionViolationCount".to_string(),
            ],
            claim_level: "formal".to_string(),
            claim_classification: "proved".to_string(),
            measurement_boundary: "measuredZero".to_string(),
            required_assumptions: vec![
                "core edges are preserved".to_string(),
                "feature/core interactions factor through a declared interface".to_string(),
                "no new forbidden static edge is introduced".to_string(),
                "embedding policy is preserved".to_string(),
            ],
            coverage_assumptions: vec![
                "static dependency graph is inside the measured universe".to_string(),
                "policy selector covers the checked static edges".to_string(),
            ],
            exactness_assumptions: vec![
                "AIR component and relation identifiers match the Lean package parameters"
                    .to_string(),
            ],
            missing_preconditions: Vec::new(),
            non_conclusions: vec![
                "static theorem package does not conclude runtime flatness".to_string(),
                "static theorem package does not conclude semantic flatness".to_string(),
                "static theorem package does not prove extractor completeness".to_string(),
            ],
        }],
    }
}

pub fn build_theorem_precondition_check_report(
    document: &AirDocumentV0,
    input_path: &str,
) -> TheoremPreconditionCheckReportV0 {
    let registry = static_theorem_package_registry();
    let checks = theorem_precondition_checks(document, &registry);
    let summary = theorem_precondition_check_summary(&checks, document.claims.len());

    TheoremPreconditionCheckReportV0 {
        schema_version: THEOREM_PRECONDITION_CHECK_REPORT_SCHEMA_VERSION.to_string(),
        input: TheoremPreconditionCheckInput {
            schema_version: document.schema_version.clone(),
            path: input_path.to_string(),
            architecture_id: document.architecture_id.clone(),
        },
        registry,
        summary,
        checks,
    }
}

fn theorem_precondition_checks(
    document: &AirDocumentV0,
    registry: &TheoremPackageRegistryV0,
) -> Vec<TheoremPreconditionCheck> {
    document
        .claims
        .iter()
        .map(|claim| theorem_precondition_check(claim, registry))
        .collect()
}

fn theorem_precondition_check(
    claim: &AirClaim,
    registry: &TheoremPackageRegistryV0,
) -> TheoremPreconditionCheck {
    let applicable_packages: Vec<&TheoremPackageMetadataV0> = registry
        .packages
        .iter()
        .filter(|package| theorem_package_applies_to_claim(package, claim))
        .collect();
    let known_refs: BTreeSet<String> = registry
        .packages
        .iter()
        .flat_map(|package| package.theorem_refs.iter().cloned())
        .collect();
    let unknown_theorem_refs: Vec<String> = claim
        .theorem_refs
        .iter()
        .filter(|theorem_ref| !known_refs.contains(theorem_ref.as_str()))
        .cloned()
        .collect();
    let applicable_package_refs = applicable_packages
        .iter()
        .map(|package| package.package_id.clone())
        .collect();

    let (resolved_claim_classification, result, reason) = if !unknown_theorem_refs.is_empty() {
        (
            "UNKNOWN_THEOREM_REF".to_string(),
            "warn".to_string(),
            "claim cites theorem refs outside the static theorem package registry".to_string(),
        )
    } else if claim.claim_classification == "measured" {
        (
            "MEASURED_WITNESS".to_string(),
            "pass".to_string(),
            "tooling measurement remains a measured witness, not a formal proved claim".to_string(),
        )
    } else if claim.claim_level == "formal"
        && claim.claim_classification == "proved"
        && !claim.missing_preconditions.is_empty()
    {
        (
            "BLOCKED_FORMAL_CLAIM".to_string(),
            "warn".to_string(),
            "missing preconditions block formal proved classification".to_string(),
        )
    } else if claim.claim_level == "formal"
        && claim.claim_classification == "proved"
        && !claim.theorem_refs.is_empty()
        && !applicable_packages.is_empty()
    {
        (
            "FORMAL_PROVED".to_string(),
            "pass".to_string(),
            "theorem refs are registered and missing preconditions are empty".to_string(),
        )
    } else if claim.claim_level == "formal" && claim.claim_classification == "proved" {
        (
            "BLOCKED_FORMAL_CLAIM".to_string(),
            "warn".to_string(),
            "formal proved claim needs registered theorem refs".to_string(),
        )
    } else if claim.claim_classification == "unmeasured" || !claim.missing_preconditions.is_empty()
    {
        (
            "UNMEASURED".to_string(),
            "warn".to_string(),
            "claim remains outside the measured theorem boundary".to_string(),
        )
    } else if applicable_packages.is_empty() && !claim.theorem_refs.is_empty() {
        (
            "UNKNOWN_THEOREM_REF".to_string(),
            "warn".to_string(),
            "claim has theorem refs but no applicable static theorem package".to_string(),
        )
    } else {
        (
            "TOOLING_CLAIM".to_string(),
            "pass".to_string(),
            "claim is reported at tooling level".to_string(),
        )
    };

    TheoremPreconditionCheck {
        claim_id: claim.claim_id.clone(),
        subject_ref: claim.subject_ref.clone(),
        applicable_package_refs,
        theorem_refs: claim.theorem_refs.clone(),
        unknown_theorem_refs,
        claim_level: claim.claim_level.clone(),
        input_claim_classification: claim.claim_classification.clone(),
        resolved_claim_classification,
        measurement_boundary: claim.measurement_boundary.clone(),
        required_assumptions: claim.required_assumptions.clone(),
        coverage_assumptions: claim.coverage_assumptions.clone(),
        exactness_assumptions: claim.exactness_assumptions.clone(),
        missing_preconditions: claim.missing_preconditions.clone(),
        non_conclusions: claim.non_conclusions.clone(),
        result,
        reason,
    }
}

fn theorem_precondition_check_summary(
    checks: &[TheoremPreconditionCheck],
    checked_claim_count: usize,
) -> TheoremPreconditionCheckSummary {
    let blocked_claim_count = checks
        .iter()
        .filter(|check| check.resolved_claim_classification == "BLOCKED_FORMAL_CLAIM")
        .count();
    let unknown_theorem_ref_count = checks
        .iter()
        .map(|check| check.unknown_theorem_refs.len())
        .sum();
    let result = if checks.iter().any(|check| check.result == "warn") {
        "warn"
    } else {
        "pass"
    };

    TheoremPreconditionCheckSummary {
        result: result.to_string(),
        checked_claim_count,
        applicable_claim_count: checks
            .iter()
            .filter(|check| !check.applicable_package_refs.is_empty())
            .count(),
        formal_proved_claim_count: checks
            .iter()
            .filter(|check| check.resolved_claim_classification == "FORMAL_PROVED")
            .count(),
        measured_witness_count: checks
            .iter()
            .filter(|check| check.resolved_claim_classification == "MEASURED_WITNESS")
            .count(),
        blocked_claim_count,
        unmeasured_claim_count: checks
            .iter()
            .filter(|check| check.resolved_claim_classification == "UNMEASURED")
            .count(),
        unknown_theorem_ref_count,
    }
}

fn theorem_package_applies_to_claim(package: &TheoremPackageMetadataV0, claim: &AirClaim) -> bool {
    let theorem_ref_matches = claim
        .theorem_refs
        .iter()
        .any(|theorem_ref| package.theorem_refs.contains(theorem_ref));
    let subject_matches = package
        .supported_subject_refs
        .iter()
        .any(|subject_ref| subject_ref == &claim.subject_ref);

    theorem_ref_matches || subject_matches
}

#[cfg(test)]
mod tests {
    use crate::test_support::air_fixture_document;
    use crate::{AirClaim, THEOREM_PRECONDITION_CHECK_REPORT_SCHEMA_VERSION};

    use super::build_theorem_precondition_check_report;

    #[test]
    fn theorem_check_keeps_measured_witness_out_of_formal_proved_claims() {
        let document = air_fixture_document("good_extension.json");
        let report = build_theorem_precondition_check_report(&document, "good_extension.json");

        assert_eq!(
            report.schema_version,
            THEOREM_PRECONDITION_CHECK_REPORT_SCHEMA_VERSION
        );
        assert_eq!(report.registry.scope, "static theorem package v0");
        assert!(report.registry.packages.iter().any(|package| {
            package.theorem_refs
                == vec![
                    "SelectedStaticSplitExtension".to_string(),
                    "CoreEdgesPreserved".to_string(),
                    "DeclaredInterfaceFactorization".to_string(),
                    "NoNewForbiddenStaticEdge".to_string(),
                    "EmbeddingPolicyPreserved".to_string(),
                ]
        }));

        let boundary_check = report
            .checks
            .iter()
            .find(|check| check.claim_id == "claim-boundary-zero")
            .expect("boundary claim is checked");
        assert_eq!(
            boundary_check.resolved_claim_classification,
            "MEASURED_WITNESS"
        );
        assert_eq!(report.summary.formal_proved_claim_count, 0);
        assert!(report.summary.measured_witness_count > 0);
    }

    #[test]
    fn theorem_check_blocks_formal_claims_with_missing_preconditions() {
        let mut document = air_fixture_document("good_extension.json");
        document.claims.push(AirClaim {
            claim_id: "claim-static-split-blocked".to_string(),
            subject_ref: "extension.split".to_string(),
            predicate: "selected static split theorem package applies".to_string(),
            claim_level: "formal".to_string(),
            claim_classification: "proved".to_string(),
            measurement_boundary: "measuredZero".to_string(),
            theorem_refs: vec!["SelectedStaticSplitExtension".to_string()],
            evidence_refs: Vec::new(),
            required_assumptions: vec!["core edges are preserved".to_string()],
            coverage_assumptions: vec!["static graph coverage".to_string()],
            exactness_assumptions: vec!["AIR ids match Lean parameters".to_string()],
            missing_preconditions: vec![
                "declared interface factorization not discharged".to_string(),
            ],
            non_conclusions: vec!["runtime flatness is not concluded".to_string()],
        });

        let report = build_theorem_precondition_check_report(&document, "good_extension.json");
        let check = report
            .checks
            .iter()
            .find(|check| check.claim_id == "claim-static-split-blocked")
            .expect("formal split claim is checked");

        assert_eq!(check.resolved_claim_classification, "BLOCKED_FORMAL_CLAIM");
        assert_eq!(check.result, "warn");
        assert_eq!(report.summary.blocked_claim_count, 1);
        assert_eq!(report.summary.formal_proved_claim_count, 0);
    }

    #[test]
    fn theorem_check_accepts_registered_formal_claim_without_missing_preconditions() {
        let mut document = air_fixture_document("good_extension.json");
        document.claims.push(AirClaim {
            claim_id: "claim-static-split-proved".to_string(),
            subject_ref: "extension.split".to_string(),
            predicate: "selected static split theorem package applies".to_string(),
            claim_level: "formal".to_string(),
            claim_classification: "proved".to_string(),
            measurement_boundary: "measuredZero".to_string(),
            theorem_refs: vec![
                "SelectedStaticSplitExtension".to_string(),
                "CoreEdgesPreserved".to_string(),
                "DeclaredInterfaceFactorization".to_string(),
                "NoNewForbiddenStaticEdge".to_string(),
                "EmbeddingPolicyPreserved".to_string(),
            ],
            evidence_refs: Vec::new(),
            required_assumptions: vec!["core edges are preserved".to_string()],
            coverage_assumptions: vec!["static graph coverage".to_string()],
            exactness_assumptions: vec!["AIR ids match Lean parameters".to_string()],
            missing_preconditions: Vec::new(),
            non_conclusions: vec!["runtime flatness is not concluded".to_string()],
        });

        let report = build_theorem_precondition_check_report(&document, "good_extension.json");
        let check = report
            .checks
            .iter()
            .find(|check| check.claim_id == "claim-static-split-proved")
            .expect("formal split claim is checked");

        assert_eq!(check.resolved_claim_classification, "FORMAL_PROVED");
        assert_eq!(check.result, "pass");
        assert_eq!(report.summary.formal_proved_claim_count, 1);
    }
}
