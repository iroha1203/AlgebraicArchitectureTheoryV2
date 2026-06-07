use std::collections::{BTreeMap, BTreeSet};

use super::constants::REQUIRED_NON_CONCLUSIONS;
use super::helpers::{check_from_examples, duplicate_examples, has_blank, push_blank, set};
use super::measurement_policy::{
    check_homotopy_measurement_profile, check_measurement_policy, check_part4_distance_profile,
    check_spectrum_measurement_profile,
};
use super::registry::{
    expand_law_policy_v1, is_known_v1_basis, is_known_v1_distance_profile, is_known_v1_evaluator,
    is_known_v1_pack, static_law_evaluator_registry_v1,
};
use crate::validation::{count_checks, duplicates, generic_validation_example, validation_check};
use crate::{
    LAW_POLICY_SCHEMA_VERSION, LAW_POLICY_V1_SCHEMA, LAW_POLICY_VALIDATION_REPORT_SCHEMA_VERSION,
    LawPolicyDocumentV0, LawPolicyDocumentV1, LawPolicyValidationInputV0,
    LawPolicyValidationInputV1, LawPolicyValidationReportV0, LawPolicyValidationReportV1,
    LawPolicyValidationSummaryV0, LawPolicyValidationSummaryV1, ValidationCheck, ValidationExample,
};

pub fn validate_law_policy_v1_report(
    policy: &LawPolicyDocumentV1,
    input_path: &str,
) -> LawPolicyValidationReportV1 {
    let expanded_policies = expand_law_policy_v1(policy);
    let checks = vec![
        check_v1_schema(policy),
        check_v1_identity(policy),
        check_v1_policy_entries(policy),
        check_v1_basis(policy),
        check_v1_pack_and_evaluator_vocabulary(policy),
        check_v1_distance_profile_selector(policy),
        check_v1_replacement_registry_manifest(),
    ];
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
        schema_version: "law-policy-validation-report-v1".to_string(),
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

fn check_v1_schema(policy: &LawPolicyDocumentV1) -> ValidationCheck {
    let mut check = validation_check(
        "law-policy-v1-schema",
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
        "law-policy-v1-identity",
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
        "law-policy-v1-entry-shape",
        "policy entries select pack or law and carry scope / severity",
        examples,
    )
}

fn check_v1_basis(policy: &LawPolicyDocumentV1) -> ValidationCheck {
    let mut examples = Vec::new();
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
            } else if !is_known_v1_basis(basis) {
                examples.push(generic_validation_example(
                    &format!("policies[{index}].basis"),
                    basis,
                    "basis ref must resolve to the v1 policy basis registry",
                ));
            }
        }
    }
    check_examples(
        "law-policy-v1-basis-recorded",
        "policy entries carry explicit basis refs",
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
            if !is_known_v1_evaluator(evaluator) {
                examples.push(generic_validation_example(
                    &format!("policies[{index}].evaluator"),
                    evaluator,
                    "unknown evaluator id / version",
                ));
            }
        }
    }
    check_examples(
        "law-policy-v1-registry-vocabulary",
        "policy entries resolve to known registry packs and evaluators",
        examples,
    )
}

fn check_v1_distance_profile_selector(policy: &LawPolicyDocumentV1) -> ValidationCheck {
    let mut examples = Vec::new();
    if let Some(profile_ref) = policy.distance_profile_ref.as_deref() {
        if profile_ref.trim().is_empty() {
            examples.push(generic_validation_example(
                "distanceProfileRef",
                "empty",
                "distance profile ref must be non-empty when present",
            ));
        } else if !is_known_v1_distance_profile(profile_ref) {
            examples.push(generic_validation_example(
                "distanceProfileRef",
                profile_ref,
                "distance profile ref must resolve to the v1 distance profile registry",
            ));
        }
    }
    check_examples(
        "law-policy-v1-distance-profile-selector",
        "LawPolicy v1 selects an optional distance profile by ref instead of embedding a distance DSL",
        examples,
    )
}

fn check_v1_replacement_registry_manifest() -> ValidationCheck {
    let registry = static_law_evaluator_registry_v1();
    let mut examples = Vec::new();
    for manifest in &registry.replacement_registry {
        if manifest.replacement_id.trim().is_empty() {
            examples.push(generic_validation_example(
                "replacementRegistry[].replacementId",
                "empty",
                "replacement id must be non-empty",
            ));
        }
        if manifest.replaced_v0_field.trim().is_empty() {
            examples.push(generic_validation_example(
                &manifest.replacement_id,
                "replacedV0Field",
                "replacement manifest must identify the removed v0 field",
            ));
        }
        if manifest.typed_output_packet_refs.is_empty() {
            examples.push(generic_validation_example(
                &manifest.replacement_id,
                "typedOutputPacketRefs",
                "replacement manifest must declare typed output packet refs",
            ));
        }
        if manifest.positive_fixtures.is_empty() {
            examples.push(generic_validation_example(
                &manifest.replacement_id,
                "positiveFixtures",
                "replacement manifest must declare positive fixture coverage",
            ));
        }
        if manifest.negative_fixtures.is_empty() {
            examples.push(generic_validation_example(
                &manifest.replacement_id,
                "negativeFixtures",
                "replacement manifest must declare negative fixture coverage",
            ));
        }
    }
    check_examples(
        "law-policy-v1-replacement-registry-manifest",
        "removed v0 field replacements resolve to registry manifests with output refs and fixture coverage",
        examples,
    )
}

fn check_examples(id: &str, title: &str, examples: Vec<ValidationExample>) -> ValidationCheck {
    let mut check = validation_check(id, title, if examples.is_empty() { "pass" } else { "fail" });
    if !examples.is_empty() {
        check.count = Some(examples.len());
        check.examples = examples;
    }
    check
}

pub fn validate_law_policy_report(
    policy: &LawPolicyDocumentV0,
    input_path: &str,
) -> LawPolicyValidationReportV0 {
    let checks = vec![
        check_schema_version(policy),
        check_identity(policy),
        check_ids_unique(policy),
        check_law_refs(policy),
        check_axis_refs(policy),
        check_witness_and_obstruction_boundaries(policy),
        check_coverage_and_exactness(policy),
        check_measurement_policy(policy),
        check_part4_distance_profile(policy),
        check_spectrum_measurement_profile(policy),
        check_homotopy_measurement_profile(policy),
        check_non_conclusions(policy),
    ];
    let summary = LawPolicyValidationSummaryV0 {
        result: if checks.iter().any(|check| check.result == "fail") {
            "fail".to_string()
        } else if checks.iter().any(|check| check.result == "warn") {
            "warn".to_string()
        } else {
            "pass".to_string()
        },
        selected_law_count: policy.selected_laws.len(),
        required_zero_axis_count: policy.required_zero_axes.len(),
        witness_rule_count: policy.witness_rules.len(),
        obstruction_circuit_definition_count: policy.obstruction_circuit_definitions.len(),
        signature_axis_definition_count: policy.signature_axis_definitions.len(),
        coverage_requirement_count: policy.coverage_requirements.len(),
        failed_check_count: count_checks(&checks, "fail"),
        warning_check_count: count_checks(&checks, "warn"),
    };

    LawPolicyValidationReportV0 {
        schema_version: LAW_POLICY_VALIDATION_REPORT_SCHEMA_VERSION.to_string(),
        input: LawPolicyValidationInputV0 {
            schema_version: policy.schema_version.clone(),
            path: input_path.to_string(),
            law_policy_id: policy.law_policy_id.clone(),
            policy_version: policy.policy_version.clone(),
            archmap_schema_ref: policy.archmap_schema_ref.clone(),
        },
        policy: policy.clone(),
        summary,
        checks,
    }
}

fn check_schema_version(policy: &LawPolicyDocumentV0) -> ValidationCheck {
    let mut check = validation_check(
        "law-policy-schema-version-supported",
        "law policy schema version is supported",
        if policy.schema_version == LAW_POLICY_SCHEMA_VERSION {
            "pass"
        } else {
            "fail"
        },
    );
    if check.result == "fail" {
        check.reason = Some(format!(
            "unsupported law policy schemaVersion: {}",
            policy.schema_version
        ));
    }
    check
}

fn check_identity(policy: &LawPolicyDocumentV0) -> ValidationCheck {
    let mut examples = Vec::new();
    push_blank(&mut examples, "lawPolicyId", &policy.law_policy_id);
    push_blank(&mut examples, "policyVersion", &policy.policy_version);
    push_blank(&mut examples, "scope", &policy.scope);
    push_blank(
        &mut examples,
        "archMapSchemaRef",
        &policy.archmap_schema_ref,
    );
    check_from_examples(
        "law-policy-identity-recorded",
        "law policy identity, scope, and target ArchMap schema are recorded",
        examples,
        "fail",
    )
}

fn check_ids_unique(policy: &LawPolicyDocumentV0) -> ValidationCheck {
    let mut examples = Vec::new();
    examples.extend(duplicate_examples(
        "selectedLaws[].lawId",
        duplicates(policy.selected_laws.iter().map(|law| law.law_id.as_str())),
    ));
    examples.extend(duplicate_examples(
        "requiredZeroAxes[].axisId",
        duplicates(
            policy
                .required_zero_axes
                .iter()
                .map(|axis| axis.axis_id.as_str()),
        ),
    ));
    examples.extend(duplicate_examples(
        "optionalAxes[].axisId",
        duplicates(
            policy
                .optional_axes
                .iter()
                .map(|axis| axis.axis_id.as_str()),
        ),
    ));
    examples.extend(duplicate_examples(
        "witnessRules[].witnessRuleId",
        duplicates(
            policy
                .witness_rules
                .iter()
                .map(|rule| rule.witness_rule_id.as_str()),
        ),
    ));
    examples.extend(duplicate_examples(
        "moleculePatterns[].moleculePatternId",
        duplicates(
            policy
                .molecule_patterns
                .iter()
                .map(|pattern| pattern.molecule_pattern_id.as_str()),
        ),
    ));
    examples.extend(duplicate_examples(
        "obstructionCircuitDefinitions[].obstructionCircuitId",
        duplicates(
            policy
                .obstruction_circuit_definitions
                .iter()
                .map(|definition| definition.obstruction_circuit_id.as_str()),
        ),
    ));
    examples.extend(duplicate_examples(
        "signatureAxisDefinitions[].signatureAxisId",
        duplicates(
            policy
                .signature_axis_definitions
                .iter()
                .map(|definition| definition.signature_axis_id.as_str()),
        ),
    ));
    examples.extend(duplicate_examples(
        "coverageRequirements[].coverageRequirementId",
        duplicates(
            policy
                .coverage_requirements
                .iter()
                .map(|requirement| requirement.coverage_requirement_id.as_str()),
        ),
    ));
    check_from_examples(
        "law-policy-ids-unique",
        "law policy ids are unique within each definition family",
        examples,
        "fail",
    )
}

fn check_law_refs(policy: &LawPolicyDocumentV0) -> ValidationCheck {
    let law_ids = set(policy.selected_laws.iter().map(|law| law.law_id.as_str()));
    let axis_ids = policy
        .required_zero_axes
        .iter()
        .chain(policy.optional_axes.iter())
        .map(|axis| axis.axis_id.as_str())
        .collect::<BTreeSet<_>>();
    let witness_ids = set(policy
        .witness_rules
        .iter()
        .map(|rule| rule.witness_rule_id.as_str()));
    let witness_law_by_ref = policy
        .witness_rules
        .iter()
        .map(|rule| (rule.witness_rule_id.as_str(), rule.law_ref.as_str()))
        .collect::<BTreeMap<_, _>>();
    let signature_axis_law_by_axis_ref = policy
        .signature_axis_definitions
        .iter()
        .map(|axis| (axis.axis_ref.as_str(), axis.law_ref.as_str()))
        .collect::<BTreeMap<_, _>>();
    let mut examples = Vec::new();

    for law in &policy.selected_laws {
        if law.required_witness_refs.is_empty() {
            examples.push(generic_validation_example(
                &law.law_id,
                "requiredWitnessRefs",
                "selected law must declare witness rules",
            ));
        }
        if law.required_axis_refs.is_empty() {
            examples.push(generic_validation_example(
                &law.law_id,
                "requiredAxisRefs",
                "selected law must declare required signature axes",
            ));
        }
        for witness_ref in &law.required_witness_refs {
            if !witness_ids.contains(witness_ref.as_str()) {
                examples.push(generic_validation_example(
                    &law.law_id,
                    witness_ref,
                    "selected law references an unknown witness rule",
                ));
            } else if witness_law_by_ref
                .get(witness_ref.as_str())
                .is_some_and(|law_ref| law_ref != &law.law_id.as_str())
            {
                examples.push(generic_validation_example(
                    &law.law_id,
                    witness_ref,
                    "selected law requiredWitnessRefs must reference witness rules for the same law",
                ));
            }
        }
        for axis_ref in &law.required_axis_refs {
            if !axis_ids.contains(axis_ref.as_str()) {
                examples.push(generic_validation_example(
                    &law.law_id,
                    axis_ref,
                    "selected law references an unknown required or optional axis",
                ));
            } else if signature_axis_law_by_axis_ref
                .get(axis_ref.as_str())
                .is_none_or(|law_ref| law_ref != &law.law_id.as_str())
            {
                examples.push(generic_validation_example(
                    &law.law_id,
                    axis_ref,
                    "selected law requiredAxisRefs must have a signature axis definition for the same law",
                ));
            }
        }
    }

    for rule in &policy.witness_rules {
        if !law_ids.contains(rule.law_ref.as_str()) {
            examples.push(generic_validation_example(
                &rule.witness_rule_id,
                &rule.law_ref,
                "witness rule references an unknown selected law",
            ));
        }
    }
    for definition in &policy.obstruction_circuit_definitions {
        if !law_ids.contains(definition.law_ref.as_str()) {
            examples.push(generic_validation_example(
                &definition.obstruction_circuit_id,
                &definition.law_ref,
                "obstruction circuit definition references an unknown selected law",
            ));
        }
    }
    for axis in &policy.signature_axis_definitions {
        if !law_ids.contains(axis.law_ref.as_str()) {
            examples.push(generic_validation_example(
                &axis.signature_axis_id,
                &axis.law_ref,
                "signature axis definition references an unknown selected law",
            ));
        }
    }

    check_from_examples(
        "law-policy-law-refs-resolve",
        "selected laws, witness rules, obstruction definitions, and signature axes cross-reference each other",
        examples,
        "fail",
    )
}

fn check_axis_refs(policy: &LawPolicyDocumentV0) -> ValidationCheck {
    let axis_ids = policy
        .required_zero_axes
        .iter()
        .chain(policy.optional_axes.iter())
        .map(|axis| axis.axis_id.as_str())
        .collect::<BTreeSet<_>>();
    let mut examples = Vec::new();

    for definition in &policy.signature_axis_definitions {
        if !axis_ids.contains(definition.axis_ref.as_str()) {
            examples.push(generic_validation_example(
                &definition.signature_axis_id,
                &definition.axis_ref,
                "signature axis definition references an unknown axis",
            ));
        }
    }
    for definition in &policy.obstruction_circuit_definitions {
        if definition.signature_axis_refs.is_empty() {
            examples.push(generic_validation_example(
                &definition.obstruction_circuit_id,
                "signatureAxisRefs",
                "obstruction circuit definition should declare affected signature axes",
            ));
        }
        for axis_ref in &definition.signature_axis_refs {
            if !axis_ids.contains(axis_ref.as_str()) {
                examples.push(generic_validation_example(
                    &definition.obstruction_circuit_id,
                    axis_ref,
                    "obstruction circuit definition references an unknown axis",
                ));
            }
        }
    }
    check_from_examples(
        "law-policy-axis-refs-resolve",
        "required and optional axes are referenced explicitly by signature and obstruction definitions",
        examples,
        "fail",
    )
}

fn check_witness_and_obstruction_boundaries(policy: &LawPolicyDocumentV0) -> ValidationCheck {
    let witness_ids = set(policy
        .witness_rules
        .iter()
        .map(|rule| rule.witness_rule_id.as_str()));
    let molecule_pattern_ids = set(policy
        .molecule_patterns
        .iter()
        .map(|pattern| pattern.molecule_pattern_id.as_str()));
    let mut examples = Vec::new();

    for rule in &policy.witness_rules {
        if rule.evidence_boundary.trim().is_empty() {
            examples.push(generic_validation_example(
                &rule.witness_rule_id,
                "evidenceBoundary",
                "witness rule must declare evidence boundary",
            ));
        }
        if rule.required_atom_families.is_empty() && rule.molecule_pattern_refs.is_empty() {
            examples.push(generic_validation_example(
                &rule.witness_rule_id,
                "requiredAtomFamilies",
                "witness rule must declare atom families or molecule pattern refs",
            ));
        }
        for pattern_ref in &rule.molecule_pattern_refs {
            if !molecule_pattern_ids.contains(pattern_ref.as_str()) {
                examples.push(generic_validation_example(
                    &rule.witness_rule_id,
                    pattern_ref,
                    "witness rule references an unknown molecule pattern",
                ));
            }
        }
    }

    for definition in &policy.obstruction_circuit_definitions {
        if !witness_ids.contains(definition.witness_rule_ref.as_str()) {
            examples.push(generic_validation_example(
                &definition.obstruction_circuit_id,
                &definition.witness_rule_ref,
                "obstruction circuit definition references an unknown witness rule",
            ));
        }
        push_blank(
            &mut examples,
            &format!("{} minimalityReading", definition.obstruction_circuit_id),
            &definition.minimality_reading,
        );
        push_blank(
            &mut examples,
            &format!("{} evidenceBoundary", definition.obstruction_circuit_id),
            &definition.evidence_boundary,
        );
    }

    check_from_examples(
        "law-policy-witness-and-obstruction-boundaries",
        "witness and obstruction definitions declare evidence, minimality, and molecule boundaries",
        examples,
        "fail",
    )
}

fn check_coverage_and_exactness(policy: &LawPolicyDocumentV0) -> ValidationCheck {
    let law_ids = set(policy.selected_laws.iter().map(|law| law.law_id.as_str()));
    let mut examples = Vec::new();
    if policy.exactness_assumptions.is_empty() || has_blank(&policy.exactness_assumptions) {
        examples.push(generic_validation_example(
            &policy.law_policy_id,
            "exactnessAssumptions",
            "law policy must declare exactness assumptions",
        ));
    }
    if policy.coverage_requirements.is_empty() {
        examples.push(generic_validation_example(
            &policy.law_policy_id,
            "coverageRequirements",
            "law policy must declare coverage requirements",
        ));
    }
    for requirement in &policy.coverage_requirements {
        if requirement.applies_to_law_refs.is_empty() {
            examples.push(generic_validation_example(
                &requirement.coverage_requirement_id,
                "appliesToLawRefs",
                "coverage requirement must declare selected laws",
            ));
        }
        for law_ref in &requirement.applies_to_law_refs {
            if !law_ids.contains(law_ref.as_str()) {
                examples.push(generic_validation_example(
                    &requirement.coverage_requirement_id,
                    law_ref,
                    "coverage requirement references an unknown selected law",
                ));
            }
        }
        if requirement.required_atom_families.is_empty() {
            examples.push(generic_validation_example(
                &requirement.coverage_requirement_id,
                "requiredAtomFamilies",
                "coverage requirement must declare atom families",
            ));
        }
        if requirement.missing_coverage_behavior.trim().is_empty() {
            examples.push(generic_validation_example(
                &requirement.coverage_requirement_id,
                "missingCoverageBehavior",
                "coverage requirement must state missing coverage behavior",
            ));
        }
    }
    check_from_examples(
        "law-policy-coverage-and-exactness-declared",
        "coverage requirements and exactness assumptions are declared",
        examples,
        "fail",
    )
}

fn check_non_conclusions(policy: &LawPolicyDocumentV0) -> ValidationCheck {
    let present = policy
        .non_conclusions
        .iter()
        .map(|value| value.as_str())
        .collect::<BTreeSet<_>>();
    let examples = REQUIRED_NON_CONCLUSIONS
        .iter()
        .filter(|required| !present.contains(**required))
        .map(|required| {
            generic_validation_example(
                &policy.law_policy_id,
                required,
                "missing required law policy non-conclusion",
            )
        })
        .collect();
    check_from_examples(
        "law-policy-non-conclusion-boundary",
        "law policy keeps theory, lawfulness, atom truth, coverage, and signature-zero boundaries explicit",
        examples,
        "fail",
    )
}
