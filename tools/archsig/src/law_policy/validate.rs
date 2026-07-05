use std::collections::BTreeSet;

use super::registry::{expand_law_policy_v1, is_known_evaluator, is_known_v1_pack};
use crate::validation::{count_checks, duplicates, generic_validation_example, validation_check};
use crate::{
    LAW_POLICY_V1_SCHEMA, LawPolicyDocumentV1, LawPolicyValidationInputV1,
    LawPolicyValidationReportV1, LawPolicyValidationSummaryV1, MEASUREMENT_PROFILE_V1_SCHEMA,
    MeasurementProfileV1, ValidationCheck, ValidationExample,
};

pub fn validate_law_policy_v1_report(
    policy: &LawPolicyDocumentV1,
    input_path: &str,
    measurement_profile: Option<&MeasurementProfileV1>,
) -> LawPolicyValidationReportV1 {
    let expanded_policies = expand_law_policy_v1(policy);
    let mut checks = vec![
        check_v1_schema(policy),
        check_v1_identity(policy),
        check_v1_policy_entries(policy),
        check_v1_basis(policy),
        check_v1_pack_and_evaluator_vocabulary(policy),
        check_v1_reserved_fields(policy),
        check_v1_measurement_profile_selector(policy, measurement_profile),
        check_v1_ag_evaluators_require_profile(policy),
    ];
    if let Some(profile) = measurement_profile {
        checks.extend(measurement_profile_v1_checks(profile));
    }
    let failed_check_count = count_checks(&checks, "fail");
    let warning_check_count = count_checks(&checks, "warn");
    let result = if failed_check_count > 0 {
        "fail"
    } else if warning_check_count > 0 {
        "warn"
    } else {
        "pass"
    };
    LawPolicyValidationReportV1 {
        schema_version: "law-policy-validation-report/v0.5.0".to_string(),
        input: LawPolicyValidationInputV1 {
            schema: policy.schema.clone(),
            path: input_path.to_string(),
            id: policy.id.clone(),
        },
        expanded_policies,
        checks,
        summary: LawPolicyValidationSummaryV1 {
            result: result.to_string(),
            policy_entry_count: policy.policies.len(),
            expanded_policy_entry_count: expand_law_policy_v1(policy).len(),
            pack_entry_count: policy
                .policies
                .iter()
                .filter(|entry| entry.pack.is_some())
                .count(),
            explicit_law_entry_count: policy
                .policies
                .iter()
                .filter(|entry| entry.law.is_some())
                .count(),
            failed_check_count,
            warning_check_count,
        },
    }
}

pub fn validate_measurement_profile_v1_checks(
    profile: &MeasurementProfileV1,
) -> Vec<ValidationCheck> {
    measurement_profile_v1_checks(profile)
}

fn check_v1_schema(policy: &LawPolicyDocumentV1) -> ValidationCheck {
    let mut check = validation_check(
        "law-policy-schema050-schema",
        "LawPolicy v1 uses the selector schema discriminator",
        if policy.schema == LAW_POLICY_V1_SCHEMA {
            "pass"
        } else {
            "fail"
        },
    );
    if check.result == "fail" {
        check.reason = Some(format!(
            "expected {LAW_POLICY_V1_SCHEMA}, found {}",
            policy.schema
        ));
    }
    check
}

fn check_v1_identity(policy: &LawPolicyDocumentV1) -> ValidationCheck {
    let mut examples = Vec::new();
    if policy.id.trim().is_empty() {
        examples.push(generic_validation_example(
            "id",
            "empty",
            "LawPolicy v1 id must be non-empty",
        ));
    }
    if policy.policies.is_empty() {
        examples.push(generic_validation_example(
            "policies",
            "empty",
            "LawPolicy v1 must select at least one policy entry",
        ));
    }
    check_examples(
        "law-policy-schema050-identity",
        "LawPolicy v1 identity and selected policies are recorded",
        examples,
    )
}

fn check_v1_policy_entries(policy: &LawPolicyDocumentV1) -> ValidationCheck {
    let mut examples = Vec::new();
    for (index, entry) in policy.policies.iter().enumerate() {
        let selector_count = usize::from(entry.pack.is_some()) + usize::from(entry.law.is_some());
        if selector_count != 1 {
            examples.push(generic_validation_example(
                &format!("policies[{index}]"),
                "selector",
                "policy entry must select exactly one of pack or law",
            ));
        }
        if entry.law.is_some() && entry.evaluator.is_none() {
            examples.push(generic_validation_example(
                &format!("policies[{index}].evaluator"),
                "missing",
                "explicit law entry must name evaluator id / version",
            ));
        }
        if entry.pack.is_some() && entry.evaluator.is_some() {
            examples.push(generic_validation_example(
                &format!("policies[{index}].evaluator"),
                "present",
                "pack entry expands through registry and must not override evaluator",
            ));
        }
        if entry.profile_ref.is_some() {
            examples.push(generic_validation_example(
                &format!("policies[{index}].profileRef"),
                "reserved",
                "policies[].profileRef is reserved for Stage 2 and is not accepted in Stage 1",
            ));
        }
        if entry.severity.trim().is_empty() {
            examples.push(generic_validation_example(
                &format!("policies[{index}].severity"),
                "empty",
                "policy entry severity must be non-empty",
            ));
        }
        if entry.scope.is_empty() {
            examples.push(generic_validation_example(
                &format!("policies[{index}].scope"),
                "empty",
                "policy entry must declare source scope",
            ));
        }
    }
    check_examples(
        "law-policy-schema050-entry-shape",
        "policy entries select pack or law and carry scope / severity",
        examples,
    )
}

fn check_v1_basis(policy: &LawPolicyDocumentV1) -> ValidationCheck {
    let mut examples = Vec::new();
    let basis_ids = policy
        .basis_ledger
        .iter()
        .map(|entry| entry.basis_id.as_str())
        .collect::<BTreeSet<_>>();
    examples.extend(
        duplicates(
            policy
                .basis_ledger
                .iter()
                .map(|entry| entry.basis_id.as_str()),
        )
        .into_iter()
        .map(|duplicate| {
            generic_validation_example(
                "basisLedger[].basisId",
                &duplicate,
                "basisLedger basisId must be unique",
            )
        }),
    );
    for (index, entry) in policy.basis_ledger.iter().enumerate() {
        for (field, value) in [
            ("basisId", entry.basis_id.as_str()),
            ("kind", entry.kind.as_str()),
            ("path", entry.path.as_str()),
            ("revision", entry.revision.as_str()),
        ] {
            if value.trim().is_empty() {
                examples.push(generic_validation_example(
                    &format!("basisLedger[{index}].{field}"),
                    "empty",
                    "basisLedger fields must be non-empty",
                ));
            }
        }
        if !matches!(
            entry.kind.as_str(),
            "repo-document" | "external-standard" | "registry"
        ) {
            examples.push(generic_validation_example(
                &format!("basisLedger[{index}].kind"),
                &entry.kind,
                "basisLedger kind must be repo-document, external-standard, or registry",
            ));
        }
    }
    for (index, entry) in policy.policies.iter().enumerate() {
        if entry.basis.is_empty() {
            examples.push(generic_validation_example(
                &format!("policies[{index}].basis"),
                "empty",
                "policy entry must carry basis refs",
            ));
        }
        for basis in &entry.basis {
            if basis.trim().is_empty() {
                examples.push(generic_validation_example(
                    &format!("policies[{index}].basis"),
                    "empty",
                    "basis refs must be non-empty",
                ));
            } else if !basis_ids.contains(basis.as_str()) {
                examples.push(generic_validation_example(
                    &format!("policies[{index}].basis"),
                    basis,
                    "basis ref must resolve to basisLedger[].basisId",
                ));
            }
        }
    }
    check_examples(
        "law-policy-schema050-basis-recorded",
        "policy entries carry explicit basis refs",
        examples,
    )
}

fn check_v1_reserved_fields(policy: &LawPolicyDocumentV1) -> ValidationCheck {
    let mut examples = Vec::new();
    if policy.law_surface_ref.is_some() {
        examples.push(generic_validation_example(
            "lawSurfaceRef",
            "reserved",
            "lawSurfaceRef is reserved for Stage 2 and is not accepted in Stage 1",
        ));
    }
    check_examples(
        "law-policy-schema050-reserved-fields-fail-closed",
        "Stage 2 LawPolicy fields fail closed in Stage 1",
        examples,
    )
}

fn check_v1_pack_and_evaluator_vocabulary(policy: &LawPolicyDocumentV1) -> ValidationCheck {
    let mut examples = Vec::new();
    for (index, entry) in policy.policies.iter().enumerate() {
        if let Some(pack) = entry.pack.as_deref() {
            if !is_known_v1_pack(pack) {
                examples.push(generic_validation_example(
                    &format!("policies[{index}].pack"),
                    pack,
                    "unknown policy pack",
                ));
            }
        }
        if let Some(evaluator) = entry.evaluator.as_deref() {
            if !is_known_evaluator(evaluator) {
                examples.push(generic_validation_example(
                    &format!("policies[{index}].evaluator"),
                    evaluator,
                    "unknown evaluator id / version",
                ));
            }
        }
    }
    check_examples(
        "law-policy-schema050-registry-vocabulary",
        "policy entries resolve to known registry packs and evaluators",
        examples,
    )
}

fn check_v1_measurement_profile_selector(
    policy: &LawPolicyDocumentV1,
    measurement_profile: Option<&MeasurementProfileV1>,
) -> ValidationCheck {
    let mut examples = Vec::new();
    if let Some(profile_ref) = policy.measurement_profile_ref.as_deref() {
        if profile_ref.trim().is_empty() {
            examples.push(generic_validation_example(
                "measurementProfileRef",
                "empty",
                "measurement profile ref must be non-empty when present",
            ));
        } else if !measurement_profile.is_some_and(|profile| profile.profile_id == profile_ref) {
            examples.push(generic_validation_example(
                "measurementProfileRef",
                profile_ref,
                "measurement profile ref must resolve to the supplied --measurement-profile profileId",
            ));
        }
    }
    check_examples(
        "law-policy-schema050-measurement-profile-selector",
        "LawPolicy v1 selects an external MeasurementProfile artifact for AG evaluators",
        examples,
    )
}

fn measurement_profile_v1_checks(profile: &MeasurementProfileV1) -> Vec<ValidationCheck> {
    let mut examples = Vec::new();
    measurement_profile_errors(profile, &mut examples);
    vec![
        check_examples(
            "measurement-profile-schema050-shape",
            "MeasurementProfile v1 declares site, cover, coefficients, predicates, certificates, verdict discipline, and finite bounds",
            examples,
        ),
        check_measurement_profile_finite_bounds(profile),
    ]
}

fn measurement_profile_errors(
    profile: &MeasurementProfileV1,
    examples: &mut Vec<ValidationExample>,
) {
    if profile.schema != MEASUREMENT_PROFILE_V1_SCHEMA {
        examples.push(generic_validation_example(
            &profile.profile_id,
            &profile.schema,
            "measurement profile schema must be measurement-profile/v0.5.0",
        ));
    }
    for (field, value) in [
        ("profileId", profile.profile_id.as_str()),
        ("siteRef", profile.site_ref.as_str()),
        ("coverRef", profile.cover_ref.as_str()),
        ("coefficient", profile.coefficient.as_str()),
        ("effCoeff", profile.eff_coeff.as_str()),
        ("resolutionSelector", profile.resolution_selector.as_str()),
        ("domain", profile.domain.as_str()),
        ("zeroPredicate", profile.zero_predicate.as_str()),
        ("nonZeroPredicate", profile.non_zero_predicate.as_str()),
        ("certSelector", profile.cert_selector.as_str()),
        ("verdictDiscipline", profile.verdict_discipline.as_str()),
    ] {
        if value.trim().is_empty() {
            examples.push(generic_validation_example(
                &format!("measurementProfile.{field}"),
                "empty",
                "measurement profile field must be non-empty",
            ));
        }
    }
    if profile.verdict_discipline != "five-valued-structural-verdict@1" {
        examples.push(generic_validation_example(
            &profile.profile_id,
            &profile.verdict_discipline,
            "verdict discipline must select the v0.4.0 five-valued structural verdict rule",
        ));
    }
    for witness in &profile.witness_family {
        if witness.law.trim().is_empty() || witness.variable.trim().is_empty() {
            examples.push(generic_validation_example(
                &profile.profile_id,
                "witnessFamily",
                "witness family entries must carry law and square-free variable refs",
            ));
        }
    }
}

fn check_measurement_profile_finite_bounds(profile: &MeasurementProfileV1) -> ValidationCheck {
    let bounds = &profile.finite_bounds;
    let mut examples = Vec::new();
    for (field, value, cap) in [
        (
            "maxSquareFreeWitnessVariables",
            bounds.max_square_free_witness_variables,
            12,
        ),
        ("maxCoherenceContexts", bounds.max_coherence_contexts, 12),
        (
            "maxTorWitnessVariables",
            bounds.max_tor_witness_variables,
            12,
        ),
        (
            "maxBoundaryResidueVariables",
            bounds.max_boundary_residue_variables,
            16,
        ),
        ("maxLaplacianCells", bounds.max_laplacian_cells, 16),
        ("maxPeriodCycles", bounds.max_period_cycles, 16),
        ("maxTransferTargets", bounds.max_transfer_targets, 16),
    ] {
        if value == 0 {
            examples.push(generic_validation_example(
                &format!("finiteBounds.{field}"),
                "0",
                "finiteBounds values must be positive",
            ));
        }
        if value > cap {
            examples.push(generic_validation_example(
                &format!("finiteBounds.{field}"),
                &value.to_string(),
                "finiteBounds value exceeds the ArchSig registry hard cap",
            ));
        }
    }
    check_examples(
        "measurement-profile-schema050-finite-bounds",
        "finiteBounds can only lower the registry hard caps used by finite evaluators",
        examples,
    )
}

fn check_v1_ag_evaluators_require_profile(policy: &LawPolicyDocumentV1) -> ValidationCheck {
    let ag_evaluator_count = policy
        .policies
        .iter()
        .filter(|entry| {
            entry
                .evaluator
                .as_deref()
                .is_some_and(is_ag_measurement_evaluator)
        })
        .count();
    let mut examples = Vec::new();
    if ag_evaluator_count > 0 && policy.measurement_profile_ref.is_none() {
        examples.push(generic_validation_example(
            "measurementProfileRef",
            "missing",
            "AG evaluator execution requires a selected MeasurementProfile",
        ));
    }
    check_examples(
        "law-policy-schema050-ag-evaluator-profile-required",
        "AG evaluator selectors fail closed when MeasurementProfile is absent",
        examples,
    )
}

fn is_ag_measurement_evaluator(evaluator: &str) -> bool {
    evaluator.starts_with("ag.")
}

fn check_examples(id: &str, title: &str, examples: Vec<ValidationExample>) -> ValidationCheck {
    let mut check = validation_check(id, title, if examples.is_empty() { "pass" } else { "fail" });
    if !examples.is_empty() {
        check.count = Some(examples.len());
        check.examples = examples;
    }
    check
}
