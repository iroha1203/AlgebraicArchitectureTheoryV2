use std::collections::BTreeSet;

use crate::validation::{count_checks, duplicates, generic_validation_example, validation_check};
use crate::{
    LAW_POLICY_TEMPLATE_REGISTRY_SCHEMA_VERSION,
    LAW_POLICY_TEMPLATE_REGISTRY_VALIDATION_REPORT_SCHEMA_VERSION, LawPolicyTemplateRegistryV0,
    LawPolicyTemplateRegistryValidationInput, LawPolicyTemplateRegistryValidationReportV0,
    LawPolicyTemplateRegistryValidationSummary, LawPolicyTemplateV0, ValidationCheck,
};

const REQUIRED_NON_CONCLUSIONS: [&str; 5] = [
    "law policy template registry is tooling validation, not a Lean theorem",
    "template application does not conclude architecture lawfulness",
    "template pass does not conclude a Lean theorem claim",
    "unmeasured gaps are not measured-zero evidence",
    "selector match does not prove extractor completeness",
];

const SUPPORTED_COMPONENT_KINDS: [&str; 6] = [
    "lean-module",
    "python-module",
    "path",
    "package",
    "service",
    "workflow",
];

const SUPPORTED_POLICY_FAMILIES: [&str; 6] = [
    "boundary",
    "abstraction",
    "local-contract",
    "state-transition",
    "runtime-protection",
    "distributed-convergence",
];

const SUPPORTED_SELECTOR_SEMANTICS: [&str; 3] =
    ["exact-or-prefix-star", "tag-match", "adapter-provided"];

pub fn static_law_policy_template_registry() -> LawPolicyTemplateRegistryV0 {
    LawPolicyTemplateRegistryV0 {
        schema_version: LAW_POLICY_TEMPLATE_REGISTRY_SCHEMA_VERSION.to_string(),
        registry_id: "aat-b8-law-policy-template-registry".to_string(),
        scope: "B8 policy selector templates for measured ArchSig tooling evidence".to_string(),
        explicit_assumptions: vec![
            "templates instantiate policy files for an explicitly selected measurement universe"
                .to_string(),
            "adapter registry entries record the evidence boundary for each produced policy artifact"
                .to_string(),
            "organization policy decides required axes separately from template selection".to_string(),
        ],
        templates: vec![
            law_policy_template(
                "python-boundary-allowlist-template-v0",
                "python-module",
                "boundary",
                "exact-or-prefix-star",
                &[
                    "package roots enumerate the measured Python module universe",
                    "component groups are exact or prefix-star selectors over Python module ids",
                    "unmatched components keep boundaryViolationCount unmeasured",
                ],
                &["python_import", "policy_selector"],
                &["boundaryViolationCount"],
                &["signature-policy-v0", "aat-air-v0"],
                &[
                    "AIR relation extractionRule traces to python-import-graph-v0",
                    "policy selector coverage is recorded before any formal bridge claim",
                ],
            ),
            law_policy_template(
                "python-abstraction-port-template-v0",
                "python-module",
                "abstraction",
                "exact-or-prefix-star",
                &[
                    "clients, abstraction, and implementations resolve to measured Python module ids",
                    "direct implementation dependency is the only v0 abstraction violation unit",
                    "empty or unresolved selector sets keep abstractionViolationCount unmeasured",
                ],
                &["python_import", "policy_selector"],
                &["abstractionViolationCount"],
                &["signature-policy-v0", "feature-extension-report-v0"],
                &[
                    "Projection soundness and exactness are separate Lean-side proof obligations",
                    "policy evidence does not discharge abstraction theorem assumptions",
                ],
            ),
            law_policy_template(
                "service-runtime-protection-template-v0",
                "service",
                "runtime-protection",
                "adapter-provided",
                &[
                    "service ids are supplied by a bounded runtime or framework adapter",
                    "missing traces and private telemetry are recorded as unmeasured gaps",
                    "runtimePropagation is evaluated separately from static boundary policy pass",
                ],
                &["runtime_trace", "policy_selector"],
                &["runtimePropagation"],
                &["aat-air-v0", "feature-extension-report-v0"],
                &[
                    "runtime zero bridge theorem preconditions are explicit claim-side data",
                    "runtime telemetry coverage is not inferred from template selection",
                ],
            ),
        ],
        non_conclusions: strings(&REQUIRED_NON_CONCLUSIONS),
    }
}

pub fn validate_law_policy_template_registry_report(
    registry: &LawPolicyTemplateRegistryV0,
    input_path: &str,
) -> LawPolicyTemplateRegistryValidationReportV0 {
    let checks = vec![
        check_schema_version(registry),
        check_registry_identity(registry),
        check_template_ids(registry),
        check_template_boundaries(registry),
        check_selector_assumptions(registry),
        check_evidence_and_outputs(registry),
        check_non_conclusion_boundary(registry),
    ];
    let summary = LawPolicyTemplateRegistryValidationSummary {
        result: if checks.iter().any(|check| check.result == "fail") {
            "fail".to_string()
        } else if checks.iter().any(|check| check.result == "warn") {
            "warn".to_string()
        } else {
            "pass".to_string()
        },
        template_count: registry.templates.len(),
        failed_check_count: count_checks(&checks, "fail"),
        warning_check_count: count_checks(&checks, "warn"),
    };

    LawPolicyTemplateRegistryValidationReportV0 {
        schema_version: LAW_POLICY_TEMPLATE_REGISTRY_VALIDATION_REPORT_SCHEMA_VERSION.to_string(),
        input: LawPolicyTemplateRegistryValidationInput {
            schema_version: registry.schema_version.clone(),
            path: input_path.to_string(),
            registry_id: registry.registry_id.clone(),
            scope: registry.scope.clone(),
        },
        registry: registry.clone(),
        summary,
        checks,
    }
}

fn law_policy_template(
    template_id: &str,
    target_component_kind: &str,
    law_policy_family: &str,
    selector_semantics: &str,
    selector_assumptions: &[&str],
    required_evidence_kinds: &[&str],
    default_required_axes: &[&str],
    policy_output_artifacts: &[&str],
    theorem_bridge_preconditions: &[&str],
) -> LawPolicyTemplateV0 {
    LawPolicyTemplateV0 {
        template_id: template_id.to_string(),
        target_component_kind: target_component_kind.to_string(),
        law_policy_family: law_policy_family.to_string(),
        selector_semantics: selector_semantics.to_string(),
        selector_assumptions: strings(selector_assumptions),
        required_evidence_kinds: strings(required_evidence_kinds),
        default_required_axes: strings(default_required_axes),
        policy_output_artifacts: strings(policy_output_artifacts),
        theorem_bridge_preconditions: strings(theorem_bridge_preconditions),
        non_conclusions: strings(&REQUIRED_NON_CONCLUSIONS),
    }
}

fn check_schema_version(registry: &LawPolicyTemplateRegistryV0) -> ValidationCheck {
    let mut check = validation_check(
        "law-policy-template-registry-schema-version-supported",
        "law policy template registry schema version is supported",
        if registry.schema_version == LAW_POLICY_TEMPLATE_REGISTRY_SCHEMA_VERSION {
            "pass"
        } else {
            "fail"
        },
    );
    if check.result == "fail" {
        check.reason = Some(format!(
            "unsupported law policy template registry schemaVersion: {}",
            registry.schema_version
        ));
    }
    check
}

fn check_registry_identity(registry: &LawPolicyTemplateRegistryV0) -> ValidationCheck {
    let mut invalid = Vec::new();
    if registry.registry_id.trim().is_empty() {
        invalid.push(generic_validation_example(
            "registryId",
            &registry.scope,
            "registry_id must be non-empty",
        ));
    }
    if registry.scope.trim().is_empty() {
        invalid.push(generic_validation_example(
            &registry.registry_id,
            "scope",
            "scope must be non-empty",
        ));
    }
    if registry.explicit_assumptions.is_empty() || has_blank(&registry.explicit_assumptions) {
        invalid.push(generic_validation_example(
            &registry.registry_id,
            "explicitAssumptions",
            "registry must record explicit assumptions",
        ));
    }
    check_examples(
        "law-policy-template-registry-identity-recorded",
        "registry id, scope, and explicit assumptions are recorded",
        invalid,
    )
}

fn check_template_ids(registry: &LawPolicyTemplateRegistryV0) -> ValidationCheck {
    let duplicate_ids = duplicates(
        registry
            .templates
            .iter()
            .map(|template| template.template_id.as_str()),
    );
    let invalid: Vec<_> = registry
        .templates
        .iter()
        .filter(|template| template.template_id.trim().is_empty())
        .map(|template| {
            generic_validation_example(
                "templateId",
                &template.law_policy_family,
                "template_id must be non-empty",
            )
        })
        .chain(
            duplicate_ids
                .into_iter()
                .map(|id| generic_validation_example(&id, &id, "duplicate template_id")),
        )
        .collect();
    check_examples(
        "law-policy-template-ids-valid",
        "template ids are non-empty and unique",
        invalid,
    )
}

fn check_template_boundaries(registry: &LawPolicyTemplateRegistryV0) -> ValidationCheck {
    let component_kinds = string_set(SUPPORTED_COMPONENT_KINDS);
    let policy_families = string_set(SUPPORTED_POLICY_FAMILIES);
    let selector_semantics = string_set(SUPPORTED_SELECTOR_SEMANTICS);
    let mut invalid = Vec::new();

    for template in &registry.templates {
        if !component_kinds.contains(template.target_component_kind.as_str()) {
            invalid.push(generic_validation_example(
                &template.template_id,
                &template.target_component_kind,
                "unsupported target_component_kind",
            ));
        }
        if !policy_families.contains(template.law_policy_family.as_str()) {
            invalid.push(generic_validation_example(
                &template.template_id,
                &template.law_policy_family,
                "unsupported law_policy_family",
            ));
        }
        if !selector_semantics.contains(template.selector_semantics.as_str()) {
            invalid.push(generic_validation_example(
                &template.template_id,
                &template.selector_semantics,
                "unsupported selector_semantics",
            ));
        }
    }

    check_examples(
        "law-policy-template-boundaries-supported",
        "templates use supported component kinds, policy families, and selector semantics",
        invalid,
    )
}

fn check_selector_assumptions(registry: &LawPolicyTemplateRegistryV0) -> ValidationCheck {
    let invalid = registry
        .templates
        .iter()
        .filter(|template| {
            template.selector_assumptions.is_empty() || has_blank(&template.selector_assumptions)
        })
        .map(|template| {
            generic_validation_example(
                &template.template_id,
                "selectorAssumptions",
                "selector assumptions must be explicit",
            )
        })
        .collect();
    check_examples(
        "law-policy-template-selector-assumptions-recorded",
        "selector assumptions are explicit for each template",
        invalid,
    )
}

fn check_evidence_and_outputs(registry: &LawPolicyTemplateRegistryV0) -> ValidationCheck {
    let mut invalid = Vec::new();
    for template in &registry.templates {
        if template.required_evidence_kinds.is_empty()
            || has_blank(&template.required_evidence_kinds)
        {
            invalid.push(generic_validation_example(
                &template.template_id,
                "requiredEvidenceKinds",
                "required evidence kinds must be recorded",
            ));
        }
        if template.default_required_axes.is_empty() || has_blank(&template.default_required_axes) {
            invalid.push(generic_validation_example(
                &template.template_id,
                "defaultRequiredAxes",
                "default required axes must be recorded",
            ));
        }
        if template.policy_output_artifacts.is_empty()
            || has_blank(&template.policy_output_artifacts)
        {
            invalid.push(generic_validation_example(
                &template.template_id,
                "policyOutputArtifacts",
                "policy output artifacts must be recorded",
            ));
        }
        if template.theorem_bridge_preconditions.is_empty()
            || has_blank(&template.theorem_bridge_preconditions)
        {
            invalid.push(generic_validation_example(
                &template.template_id,
                "theoremBridgePreconditions",
                "theorem bridge preconditions must stay explicit",
            ));
        }
    }

    check_examples(
        "law-policy-template-evidence-boundaries-recorded",
        "required evidence, output artifacts, axes, and theorem bridge preconditions are recorded",
        invalid,
    )
}

fn check_non_conclusion_boundary(registry: &LawPolicyTemplateRegistryV0) -> ValidationCheck {
    let mut invalid = missing_required_non_conclusions(
        &registry.registry_id,
        &registry.non_conclusions,
        "registry non_conclusions must preserve policy/template boundaries",
    );
    for template in &registry.templates {
        invalid.extend(missing_required_non_conclusions(
            &template.template_id,
            &template.non_conclusions,
            "template non_conclusions must preserve policy/template boundaries",
        ));
    }
    check_examples(
        "law-policy-template-non-conclusion-boundary-recorded",
        "template application is separated from lawfulness, Lean theorem, and measured-zero claims",
        invalid,
    )
}

fn missing_required_non_conclusions(
    source: &str,
    non_conclusions: &[String],
    evidence: &str,
) -> Vec<crate::ValidationExample> {
    REQUIRED_NON_CONCLUSIONS
        .iter()
        .filter(|required| !non_conclusions.iter().any(|value| value == **required))
        .map(|required| generic_validation_example(source, required, evidence))
        .collect()
}

fn strings(values: &[&str]) -> Vec<String> {
    values.iter().map(|value| value.to_string()).collect()
}

fn has_blank(values: &[String]) -> bool {
    values.iter().any(|value| value.trim().is_empty())
}

fn string_set<const N: usize>(values: [&'static str; N]) -> BTreeSet<&'static str> {
    values.into_iter().collect()
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
