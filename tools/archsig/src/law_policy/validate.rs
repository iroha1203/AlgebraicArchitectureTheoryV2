use std::collections::BTreeSet;

use super::registry::{
    binding_axes_for, expand_law_policy_v1, is_compatible_evaluator_condition, is_known_evaluator,
};
use crate::validation::{count_checks, duplicates, generic_validation_example, validation_check};
use crate::{
    LAW_POLICY_V1_SCHEMA, LawEquationSurfaceV1, LawPolicyDocumentV1, LawPolicyValidationInputV1,
    LawPolicyValidationReportV1, LawPolicyValidationSummaryV1, MEASUREMENT_PROFILE_V1_SCHEMA,
    MeasurementProfileV1, ValidationCheck, ValidationExample,
};
use serde_json::Value;

pub fn validate_law_policy_v1_report(
    policy: &LawPolicyDocumentV1,
    input_path: &str,
    measurement_profile: Option<&MeasurementProfileV1>,
    law_surface: Option<&LawEquationSurfaceV1>,
) -> LawPolicyValidationReportV1 {
    let expanded_policies = expand_law_policy_v1(policy);
    let mut checks = vec![
        check_v1_schema(policy),
        check_v1_identity(policy),
        check_v1_policy_entries(policy),
        check_v1_policy_profile_refs(policy, measurement_profile),
        check_v1_basis(policy),
        check_v1_pack_and_evaluator_vocabulary(policy),
        check_v1_reserved_fields(policy),
        check_v1_measurement_profile_selector(policy, measurement_profile),
        check_v1_ag_evaluators_require_profile(policy),
        check_v1_law_surface_resolution(policy, law_surface),
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
        schema_version: "law-policy-validation-report/v0.5.2".to_string(),
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
                .filter(|entry| entry.law.is_some() || entry.law_pair.is_some())
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
        "law-policy-schema052-schema",
        "LawPolicy v0.5.2 uses the selector schema discriminator",
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
            "LawPolicy v0.5.2 id must be non-empty",
        ));
    }
    if policy.policies.is_empty() {
        examples.push(generic_validation_example(
            "policies",
            "empty",
            "LawPolicy v0.5.2 must select at least one policy entry",
        ));
    }
    check_examples(
        "law-policy-schema052-identity",
        "LawPolicy v0.5.2 identity and selected policies are recorded",
        examples,
    )
}

fn check_v1_policy_entries(policy: &LawPolicyDocumentV1) -> ValidationCheck {
    let mut examples = Vec::new();
    for (index, entry) in policy.policies.iter().enumerate() {
        let selector_count = usize::from(entry.pack.is_some())
            + usize::from(entry.law.is_some())
            + usize::from(entry.law_pair.is_some());
        if selector_count != 1 {
            examples.push(generic_validation_example(
                &format!("policies[{index}]"),
                "selector",
                "policy entry must select exactly one of pack, law, or lawPair",
            ));
        }
        if (entry.law.is_some() || entry.law_pair.is_some()) && entry.evaluator.is_none() {
            examples.push(generic_validation_example(
                &format!("policies[{index}].evaluator"),
                "missing",
                "explicit law entry must name evaluator id / version",
            ));
        }
        if let Some(law_pair) = entry.law_pair.as_ref() {
            let unique_laws = law_pair.iter().collect::<BTreeSet<_>>();
            if law_pair.len() != 2
                || unique_laws.len() != 2
                || law_pair.iter().any(|law| law.trim().is_empty())
            {
                examples.push(generic_validation_example(
                    &format!("policies[{index}].lawPair"),
                    "invalid",
                    "lawPair must contain exactly two distinct non-empty law ids",
                ));
            }
            if entry.evaluator.as_deref() != Some("ag.law-conflict-tor") {
                examples.push(generic_validation_example(
                    &format!("policies[{index}].lawPair"),
                    entry.evaluator.as_deref().unwrap_or("missing"),
                    "lawPair is reserved for the ag.law-conflict-tor evaluator",
                ));
            }
        }
        if entry.evaluator.as_deref() == Some("ag.law-conflict-tor") && entry.law_pair.is_none() {
            examples.push(generic_validation_example(
                &format!("policies[{index}].lawPair"),
                "missing",
                "ag.law-conflict-tor requires an explicit lawPair declaration",
            ));
        }
        if entry.evaluator.as_deref() == Some("ag.square-free-repair") && entry.law.is_none() {
            examples.push(generic_validation_example(
                &format!("policies[{index}].law"),
                "missing",
                "ag.square-free-repair requires an explicit law selector",
            ));
        }
        if entry.pack.is_some() && entry.evaluator.is_some() {
            examples.push(generic_validation_example(
                &format!("policies[{index}].evaluator"),
                "present",
                "pack entry expands through registry and must not override evaluator",
            ));
        }
        if entry
            .profile_ref
            .as_deref()
            .is_some_and(|profile_ref| profile_ref.trim().is_empty())
        {
            examples.push(generic_validation_example(
                &format!("policies[{index}].profileRef"),
                "empty",
                "policies[].profileRef must be a non-empty profile id when supplied",
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
        "law-policy-schema052-entry-shape",
        "policy entries select pack, law, or lawPair and carry scope / severity",
        examples,
    )
}

fn check_v1_policy_profile_refs(
    policy: &LawPolicyDocumentV1,
    measurement_profile: Option<&MeasurementProfileV1>,
) -> ValidationCheck {
    let mut examples = Vec::new();
    for (index, entry) in policy.policies.iter().enumerate() {
        let Some(profile_ref) = entry.profile_ref.as_deref() else {
            continue;
        };
        if !measurement_profile.is_some_and(|profile| profile.profile_id == profile_ref) {
            examples.push(generic_validation_example(
                &format!("policies[{index}].profileRef"),
                profile_ref,
                "policies[].profileRef must resolve to one of the supplied measurement profile ids",
            ));
        }
    }
    check_examples(
        "law-policy-schema052-policy-profile-resolution",
        "policy rows resolve profileRef against the supplied measurement profile",
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
        "law-policy-schema052-basis-recorded",
        "policy entries carry explicit basis refs",
        examples,
    )
}

fn check_v1_reserved_fields(policy: &LawPolicyDocumentV1) -> ValidationCheck {
    let mut examples = Vec::new();
    if policy.law_surface_ref.is_none() {
        examples.push(generic_validation_example(
            "lawSurfaceRef",
            "missing",
            "lawSurfaceRef is required by LawPolicy v0.5.2",
        ));
    }
    check_examples(
        "law-policy-schema052-reserved-fields",
        "LawPolicy v0.5.2 declares a law surface reference",
        examples,
    )
}

fn check_v1_law_surface_resolution(
    policy: &LawPolicyDocumentV1,
    law_surface: Option<&LawEquationSurfaceV1>,
) -> ValidationCheck {
    let mut examples = Vec::new();
    let Some(surface) = law_surface else {
        examples.push(generic_validation_example(
            "--law-surface",
            "missing",
            "LawPolicy v0.5.2 requires --law-surface; witness and law declarations are supplied by that artifact",
        ));
        return check_examples(
            "law-policy-schema052-law-surface-resolution",
            "LawPolicy laws resolve against the supplied law surface",
            examples,
        );
    };

    if policy.law_surface_ref.as_deref() != Some(surface.id.as_str()) {
        examples.push(generic_validation_example(
            "lawSurfaceRef",
            policy.law_surface_ref.as_deref().unwrap_or("missing"),
            "lawSurfaceRef must equal the supplied law-equation-surface id",
        ));
    }
    for (index, entry) in policy.policies.iter().enumerate() {
        let selected_laws = if let Some(law_pair) = entry.law_pair.as_ref() {
            law_pair
                .iter()
                .enumerate()
                .map(|(law_index, law_id)| {
                    (
                        format!("policies[{index}].lawPair[{law_index}]"),
                        law_id.as_str(),
                    )
                })
                .collect::<Vec<_>>()
        } else if let Some(law_id) = entry.law.as_deref() {
            vec![(format!("policies[{index}].law"), law_id)]
        } else {
            Vec::new()
        };
        let Some(evaluator) = entry.evaluator.as_deref() else {
            continue;
        };
        for (law_path, law_id) in selected_laws {
            let Some(law) = surface.laws.iter().find(|law| law.law_id == law_id) else {
                examples.push(generic_validation_example(
                    &law_path,
                    law_id,
                    if law_path.contains(".lawPair[") {
                        "selected policy law must resolve exactly to a lawId declared by the supplied law surface"
                    } else {
                        "policies[].law must resolve exactly to a lawId declared by the supplied law surface"
                    },
                ));
                continue;
            };
            if law
                .evaluator_ref
                .as_deref()
                .is_some_and(|declared| declared != evaluator)
            {
                examples.push(generic_validation_example(
                    &format!("policies[{index}].evaluator"),
                    evaluator,
                    "policy evaluator must match the law surface evaluatorRef",
                ));
            }
            if !is_compatible_evaluator_condition(evaluator, &law.condition_type) {
                examples.push(generic_validation_example(
                    &format!("policies[{index}].evaluator"),
                    evaluator,
                    "policy evaluator must be registered for the law surface conditionType",
                ));
            }
            let expected_axes = binding_axes_for(evaluator);
            if !expected_axes.is_empty() {
                for (witness_index, witness) in law.witness_variables.iter().enumerate() {
                    let actual_axis = witness.binding.axis.as_deref().unwrap_or("missing");
                    if !expected_axes.contains(&actual_axis) {
                        examples.push(generic_validation_example(
                            &format!("{law_path}.witnessVariables[{witness_index}].binding.axis"),
                            actual_axis,
                            &format!(
                                "policy evaluator {evaluator} requires registry axis in [{}]",
                                expected_axes.join(", ")
                            ),
                        ));
                    }
                }
            }
        }
    }
    check_examples(
        "law-policy-schema052-law-surface-resolution",
        "LawPolicy laws resolve against the supplied law surface and registry mapping",
        examples,
    )
}

fn check_v1_pack_and_evaluator_vocabulary(policy: &LawPolicyDocumentV1) -> ValidationCheck {
    let mut examples = Vec::new();
    for (index, entry) in policy.policies.iter().enumerate() {
        if let Some(pack) = entry.pack.as_deref() {
            examples.push(generic_validation_example(
                &format!("policies[{index}].pack"),
                pack,
                "policy pack selectors are retired; use an explicit law/evaluator selector",
            ));
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
        "law-policy-schema052-registry-vocabulary",
        "policy entries resolve to known evaluators",
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
        "law-policy-schema052-measurement-profile-selector",
        "LawPolicy v0.5.2 selects an external MeasurementProfile artifact for AG evaluators",
        examples,
    )
}

fn measurement_profile_v1_checks(profile: &MeasurementProfileV1) -> Vec<ValidationCheck> {
    let mut examples = Vec::new();
    measurement_profile_errors(profile, &mut examples);
    vec![
        check_examples(
            "measurement-profile-schema052-shape",
            "MeasurementProfile v0.5.2 declares site, cover, coefficients, predicates, certificates, verdict discipline, and finite bounds",
            examples,
        ),
        check_measurement_profile_reserved_fields(profile),
        check_measurement_profile_finite_bounds(profile),
    ]
}

fn check_measurement_profile_reserved_fields(profile: &MeasurementProfileV1) -> ValidationCheck {
    let mut examples = Vec::new();
    if let Some(value) = profile.diagnostic_ceiling.as_ref() {
        let valid = value
            .as_ref()
            .and_then(Value::as_str)
            .is_some_and(|ceiling| {
                matches!(
                    ceiling,
                    "raw-values"
                        | "boundary-membership"
                        | "descent"
                        | "class-transfer"
                        | "law-grounded"
                )
            });
        if !valid {
            examples.push(generic_validation_example(
                "diagnosticCeiling",
                value
                    .as_ref()
                    .and_then(Value::as_str)
                    .unwrap_or("invalid"),
                "diagnosticCeiling must be one of raw-values, boundary-membership, descent, class-transfer, or law-grounded",
            ));
        }
    }
    if profile
        .diagnostic_ceiling
        .as_ref()
        .is_some_and(|value| value.is_none())
    {
        examples.push(generic_validation_example(
            "diagnosticCeiling",
            "null",
            "diagnosticCeiling must be a non-null stage name when supplied",
        ));
    }
    check_examples(
        "measurement-profile-schema052-diagnostic-ceiling",
        "MeasurementProfile v0.5.2 accepts only registered diagnostic ceiling stages",
        examples,
    )
}

fn measurement_profile_errors(
    profile: &MeasurementProfileV1,
    examples: &mut Vec<ValidationExample>,
) {
    if profile.schema != MEASUREMENT_PROFILE_V1_SCHEMA {
        examples.push(generic_validation_example(
            &profile.profile_id,
            &profile.schema,
            "measurement profile schema must be measurement-profile/v0.5.2",
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
            "verdict discipline must select the v0.5.2 five-valued structural verdict rule",
        ));
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
        "measurement-profile-schema052-finite-bounds",
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
        "law-policy-schema052-ag-evaluator-profile-required",
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
