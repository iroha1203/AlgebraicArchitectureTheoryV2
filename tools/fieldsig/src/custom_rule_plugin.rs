use std::collections::BTreeSet;

use crate::validation::{count_checks, duplicates, generic_validation_example, validation_check};
use crate::{
    CUSTOM_RULE_PLUGIN_REGISTRY_SCHEMA_VERSION,
    CUSTOM_RULE_PLUGIN_REGISTRY_VALIDATION_REPORT_SCHEMA_VERSION, CustomRulePluginRegistryV0,
    CustomRulePluginRegistryValidationInput, CustomRulePluginRegistryValidationReportV0,
    CustomRulePluginRegistryValidationSummary, CustomRulePluginV0, ValidationCheck,
};

const REQUIRED_NON_CONCLUSIONS: [&str; 5] = [
    "custom rule plugin registry is tooling validation, not a Lean theorem",
    "plugin output does not conclude architecture lawfulness",
    "plugin output does not conclude a Lean theorem claim",
    "plugin evidence does not turn unsupported gaps into measured-zero evidence",
    "formal claim promotion requires explicit theorem precondition checks",
];

const SUPPORTED_PLUGIN_KINDS: [&str; 4] = [
    "policy-rule",
    "extractor-extension",
    "runtime-evidence",
    "semantic-evidence",
];

const SUPPORTED_EVIDENCE_KINDS: [&str; 7] = [
    "policy_rule",
    "manual_annotation",
    "observation_result",
    "runtime_trace",
    "semantic_diagram",
    "test",
    "generated_patch",
];

const SUPPORTED_CONFIDENCE: [&str; 3] = ["low", "medium", "high"];
const SUPPORTED_CLAIM_LEVELS: [&str; 3] = ["tooling", "empirical", "formal"];
const SUPPORTED_FORMAL_PROMOTION: [&str; 2] =
    ["not-permitted", "requires-theorem-precondition-check"];

pub fn static_custom_rule_plugin_registry() -> CustomRulePluginRegistryV0 {
    CustomRulePluginRegistryV0 {
        schema_version: CUSTOM_RULE_PLUGIN_REGISTRY_SCHEMA_VERSION.to_string(),
        registry_id: "aat-b8-custom-rule-plugin-registry".to_string(),
        scope: "B8 custom rule plugins for bounded ArchSig tooling evidence".to_string(),
        explicit_assumptions: vec![
            "plugin input universes are selected before plugin execution".to_string(),
            "plugin evidence is traced as AIR evidence and Feature Extension Report metadata"
                .to_string(),
            "plugin validation records what the plugin cannot conclude".to_string(),
        ],
        plugins: vec![
            custom_rule_plugin(
                "python-boundary-layer-rule-plugin-v0",
                "org-python-boundary-layer-v0",
                "policy-rule",
                "policy_rule",
                "medium",
                &[
                    "input components are python-module ids from python-import-graph-v0",
                    "policy selectors are exact or prefix-star selectors",
                ],
                &[
                    "emits advisory boundary policy evidence",
                    "records matched and unmatched selectors separately",
                ],
                &[
                    "policy selector coverage is bounded by the measured Python module universe",
                    "dynamic import and plugin loading remain unsupported unless another adapter measures them",
                ],
                &["tooling", "empirical"],
                "not-permitted",
                &[],
                &[],
                &["aat-air-v0", "feature-extension-report-v0"],
            ),
            custom_rule_plugin(
                "runtime-hot-path-annotation-plugin-v0",
                "org-runtime-hot-path-v0",
                "runtime-evidence",
                "runtime_trace",
                "low",
                &[
                    "runtime trace sources are supplied by an explicit measurement unit",
                    "private or missing telemetry is recorded as unmeasured",
                ],
                &[
                    "emits runtime exposure annotations for selected relations",
                    "does not synthesize static dependency edges",
                ],
                &[
                    "runtime traces are sampled evidence and not complete execution semantics",
                    "service identity resolution is supplied by a bounded adapter registry entry",
                ],
                &["tooling", "empirical", "formal"],
                "requires-theorem-precondition-check",
                &["runtime-zero-bridge-theorem-package-v0"],
                &[
                    "AIR runtime coverage layer is measuredZero for the selected relation universe",
                    "theorem precondition checker has no missing runtime coverage preconditions",
                ],
                &["aat-air-v0", "theorem-precondition-check-report-v0"],
            ),
        ],
        non_conclusions: strings(&REQUIRED_NON_CONCLUSIONS),
    }
}

pub fn validate_custom_rule_plugin_registry_report(
    registry: &CustomRulePluginRegistryV0,
    input_path: &str,
) -> CustomRulePluginRegistryValidationReportV0 {
    let checks = vec![
        check_schema_version(registry),
        check_registry_identity(registry),
        check_plugin_ids(registry),
        check_plugin_taxonomy(registry),
        check_plugin_contracts(registry),
        check_formal_promotion_boundary(registry),
        check_non_conclusion_boundary(registry),
    ];
    let summary = CustomRulePluginRegistryValidationSummary {
        result: if checks.iter().any(|check| check.result == "fail") {
            "fail".to_string()
        } else if checks.iter().any(|check| check.result == "warn") {
            "warn".to_string()
        } else {
            "pass".to_string()
        },
        plugin_count: registry.plugins.len(),
        failed_check_count: count_checks(&checks, "fail"),
        warning_check_count: count_checks(&checks, "warn"),
    };

    CustomRulePluginRegistryValidationReportV0 {
        schema_version: CUSTOM_RULE_PLUGIN_REGISTRY_VALIDATION_REPORT_SCHEMA_VERSION.to_string(),
        input: CustomRulePluginRegistryValidationInput {
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

fn custom_rule_plugin(
    plugin_id: &str,
    rule_id: &str,
    plugin_kind: &str,
    evidence_kind: &str,
    confidence: &str,
    input_contract: &[&str],
    output_contract: &[&str],
    coverage_assumptions: &[&str],
    permitted_claim_levels: &[&str],
    formal_claim_promotion: &str,
    theorem_precondition_refs: &[&str],
    required_theorem_preconditions: &[&str],
    output_artifacts: &[&str],
) -> CustomRulePluginV0 {
    CustomRulePluginV0 {
        plugin_id: plugin_id.to_string(),
        rule_id: rule_id.to_string(),
        plugin_kind: plugin_kind.to_string(),
        evidence_kind: evidence_kind.to_string(),
        confidence: confidence.to_string(),
        input_contract: strings(input_contract),
        output_contract: strings(output_contract),
        coverage_assumptions: strings(coverage_assumptions),
        permitted_claim_levels: strings(permitted_claim_levels),
        formal_claim_promotion: formal_claim_promotion.to_string(),
        theorem_precondition_refs: strings(theorem_precondition_refs),
        required_theorem_preconditions: strings(required_theorem_preconditions),
        output_artifacts: strings(output_artifacts),
        non_conclusions: strings(&REQUIRED_NON_CONCLUSIONS),
    }
}

fn check_schema_version(registry: &CustomRulePluginRegistryV0) -> ValidationCheck {
    let mut check = validation_check(
        "custom-rule-plugin-registry-schema-version-supported",
        "custom rule plugin registry schema version is supported",
        if registry.schema_version == CUSTOM_RULE_PLUGIN_REGISTRY_SCHEMA_VERSION {
            "pass"
        } else {
            "fail"
        },
    );
    if check.result == "fail" {
        check.reason = Some(format!(
            "unsupported custom rule plugin registry schemaVersion: {}",
            registry.schema_version
        ));
    }
    check
}

fn check_registry_identity(registry: &CustomRulePluginRegistryV0) -> ValidationCheck {
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
        "custom-rule-plugin-registry-identity-recorded",
        "registry id, scope, and explicit assumptions are recorded",
        invalid,
    )
}

fn check_plugin_ids(registry: &CustomRulePluginRegistryV0) -> ValidationCheck {
    let duplicate_plugin_ids = duplicates(
        registry
            .plugins
            .iter()
            .map(|plugin| plugin.plugin_id.as_str()),
    );
    let duplicate_rule_ids = duplicates(
        registry
            .plugins
            .iter()
            .map(|plugin| plugin.rule_id.as_str()),
    );
    let invalid: Vec<_> = registry
        .plugins
        .iter()
        .filter(|plugin| plugin.plugin_id.trim().is_empty() || plugin.rule_id.trim().is_empty())
        .map(|plugin| {
            generic_validation_example(
                &plugin.plugin_id,
                &plugin.rule_id,
                "plugin_id and rule_id must be non-empty",
            )
        })
        .chain(
            duplicate_plugin_ids
                .into_iter()
                .map(|id| generic_validation_example(&id, &id, "duplicate plugin_id")),
        )
        .chain(
            duplicate_rule_ids
                .into_iter()
                .map(|id| generic_validation_example(&id, &id, "duplicate rule_id")),
        )
        .collect();
    check_examples(
        "custom-rule-plugin-ids-valid",
        "plugin ids and rule ids are non-empty and unique",
        invalid,
    )
}

fn check_plugin_taxonomy(registry: &CustomRulePluginRegistryV0) -> ValidationCheck {
    let plugin_kinds = string_set(SUPPORTED_PLUGIN_KINDS);
    let evidence_kinds = string_set(SUPPORTED_EVIDENCE_KINDS);
    let confidence = string_set(SUPPORTED_CONFIDENCE);
    let claim_levels = string_set(SUPPORTED_CLAIM_LEVELS);
    let promotion = string_set(SUPPORTED_FORMAL_PROMOTION);
    let mut invalid = Vec::new();

    for plugin in &registry.plugins {
        if !plugin_kinds.contains(plugin.plugin_kind.as_str()) {
            invalid.push(generic_validation_example(
                &plugin.plugin_id,
                &plugin.plugin_kind,
                "unsupported plugin_kind",
            ));
        }
        if !evidence_kinds.contains(plugin.evidence_kind.as_str()) {
            invalid.push(generic_validation_example(
                &plugin.plugin_id,
                &plugin.evidence_kind,
                "unsupported evidence_kind",
            ));
        }
        if !confidence.contains(plugin.confidence.as_str()) {
            invalid.push(generic_validation_example(
                &plugin.plugin_id,
                &plugin.confidence,
                "unsupported confidence",
            ));
        }
        for level in &plugin.permitted_claim_levels {
            if !claim_levels.contains(level.as_str()) {
                invalid.push(generic_validation_example(
                    &plugin.plugin_id,
                    level,
                    "unsupported permitted_claim_level",
                ));
            }
        }
        if !promotion.contains(plugin.formal_claim_promotion.as_str()) {
            invalid.push(generic_validation_example(
                &plugin.plugin_id,
                &plugin.formal_claim_promotion,
                "unsupported formal_claim_promotion",
            ));
        }
    }

    check_examples(
        "custom-rule-plugin-taxonomy-supported",
        "plugins use supported kinds, evidence kinds, confidence, claim levels, and promotion modes",
        invalid,
    )
}

fn check_plugin_contracts(registry: &CustomRulePluginRegistryV0) -> ValidationCheck {
    let mut invalid = Vec::new();
    for plugin in &registry.plugins {
        if plugin.input_contract.is_empty() || has_blank(&plugin.input_contract) {
            invalid.push(generic_validation_example(
                &plugin.plugin_id,
                "inputContract",
                "input contract must be explicit",
            ));
        }
        if plugin.output_contract.is_empty() || has_blank(&plugin.output_contract) {
            invalid.push(generic_validation_example(
                &plugin.plugin_id,
                "outputContract",
                "output contract must be explicit",
            ));
        }
        if plugin.coverage_assumptions.is_empty() || has_blank(&plugin.coverage_assumptions) {
            invalid.push(generic_validation_example(
                &plugin.plugin_id,
                "coverageAssumptions",
                "coverage assumptions must be explicit",
            ));
        }
        if plugin.permitted_claim_levels.is_empty() || has_blank(&plugin.permitted_claim_levels) {
            invalid.push(generic_validation_example(
                &plugin.plugin_id,
                "permittedClaimLevels",
                "permitted claim levels must be explicit",
            ));
        }
        if plugin.output_artifacts.is_empty() || has_blank(&plugin.output_artifacts) {
            invalid.push(generic_validation_example(
                &plugin.plugin_id,
                "outputArtifacts",
                "output artifacts must be explicit",
            ));
        }
    }

    check_examples(
        "custom-rule-plugin-contracts-recorded",
        "input/output contracts, coverage assumptions, claim levels, and output artifacts are recorded",
        invalid,
    )
}

fn check_formal_promotion_boundary(registry: &CustomRulePluginRegistryV0) -> ValidationCheck {
    let mut invalid = Vec::new();
    for plugin in &registry.plugins {
        let permits_formal = plugin
            .permitted_claim_levels
            .iter()
            .any(|level| level == "formal");
        if permits_formal && plugin.formal_claim_promotion != "requires-theorem-precondition-check"
        {
            invalid.push(generic_validation_example(
                &plugin.plugin_id,
                &plugin.formal_claim_promotion,
                "formal claim level requires theorem precondition checker promotion mode",
            ));
        }
        if plugin.formal_claim_promotion == "requires-theorem-precondition-check"
            && (plugin.theorem_precondition_refs.is_empty()
                || plugin.required_theorem_preconditions.is_empty()
                || has_blank(&plugin.theorem_precondition_refs)
                || has_blank(&plugin.required_theorem_preconditions))
        {
            invalid.push(generic_validation_example(
                &plugin.plugin_id,
                "theoremPreconditionRefs",
                "formal claim promotion requires theorem refs and required preconditions",
            ));
        }
    }

    check_examples(
        "custom-rule-plugin-formal-promotion-boundary-recorded",
        "formal claim promotion is blocked unless theorem preconditions are explicit",
        invalid,
    )
}

fn check_non_conclusion_boundary(registry: &CustomRulePluginRegistryV0) -> ValidationCheck {
    let mut invalid = missing_required_non_conclusions(
        &registry.registry_id,
        &registry.non_conclusions,
        "registry non_conclusions must preserve plugin boundaries",
    );
    for plugin in &registry.plugins {
        invalid.extend(missing_required_non_conclusions(
            &plugin.plugin_id,
            &plugin.non_conclusions,
            "plugin non_conclusions must preserve plugin boundaries",
        ));
    }
    check_examples(
        "custom-rule-plugin-non-conclusion-boundary-recorded",
        "plugin evidence is separated from lawfulness, Lean theorem, and measured-zero claims",
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
