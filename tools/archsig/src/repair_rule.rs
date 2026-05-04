use std::collections::BTreeSet;

use crate::validation::{count_checks, duplicates, generic_validation_example, validation_check};
use crate::{
    REPAIR_RULE_REGISTRY_SCHEMA_VERSION, REPAIR_RULE_REGISTRY_VALIDATION_REPORT_SCHEMA_VERSION,
    RepairRuleRegistryV0, RepairRuleRegistryValidationInput, RepairRuleRegistryValidationReportV0,
    RepairRuleRegistryValidationSummary, RepairRuleRelativeScopeV0, RepairRuleV0, ValidationCheck,
};

const REQUIRED_NON_CONCLUSIONS: [&str; 4] = [
    "repair success is not concluded",
    "all obstruction removal is not concluded",
    "global flatness preservation is not concluded",
    "empirical cost improvement is not concluded",
];

const SUPPORTED_TARGET_WITNESS_KINDS: [&str; 6] = [
    "hidden_interaction",
    "policy_violation",
    "nonfillability_witness",
    "observation_difference",
    "runtime_trace",
    "semantic_curvature",
];

const SUPPORTED_OPERATIONS: [&str; 7] = [
    "split", "isolate", "contract", "replace", "protect", "migrate", "manual",
];

const SUPPORTED_EXPECTED_EFFECTS: [&str; 5] =
    ["remove", "reduce", "localize", "translate", "transfer"];

const SUPPORTED_PATCH_STRATEGIES: [&str; 3] = ["manual", "generated", "assisted"];
const SUPPORTED_CONFIDENCE: [&str; 3] = ["low", "medium", "high"];

pub fn static_repair_rule_registry() -> RepairRuleRegistryV0 {
    RepairRuleRegistryV0 {
        schema_version: REPAIR_RULE_REGISTRY_SCHEMA_VERSION.to_string(),
        scope: "repair suggestion registry v0 for selected obstruction witnesses".to_string(),
        selected_obstruction_universe:
            "Feature Extension Report v0 introducedObstructionWitnesses and selected AIR semantic witnesses"
                .to_string(),
        explicit_assumptions: vec![
            "rules are advisory design candidates, not automatically valid patches".to_string(),
            "witnesses are interpreted inside the selected measurement universe".to_string(),
            "operation effects are checked against the same report boundary".to_string(),
        ],
        rules: vec![
            repair_rule(
                "repair-hidden-interaction-through-interface-v0",
                "hidden_interaction",
                "split",
                &[
                    "declared interface can represent the dependency contract",
                    "core edges that must be preserved are identified",
                    "policy selector covers the checked static edges",
                ],
                "localize",
                &["declared interface factorization"],
                &[
                    "runtime exposure can increase after routing through an adapter",
                    "semantic behavior can change if the interface contract is underspecified",
                ],
                &[
                    "SelectedStaticSplitExtension",
                    "RepairTransferCounterexample.selectedRepairStep_not_all_axes_nonincreasing",
                ],
                "assisted",
                "medium",
            ),
            repair_rule(
                "repair-policy-violation-isolate-boundary-v0",
                "policy_violation",
                "isolate",
                &[
                    "forbidden edge evidence resolves to measured components",
                    "target boundary group is known",
                    "replacement relation is allowed by the active policy",
                ],
                "reduce",
                &["boundary policy measurement"],
                &[
                    "abstraction violation can remain after boundary isolation",
                    "manual policy update can mask an intentional law change",
                ],
                &[
                    "NoNewForbiddenStaticEdge",
                    "ArchitectureCalculusLaw.isolateRuntimeLocalizationLaw_conclusion",
                ],
                "manual",
                "medium",
            ),
            repair_rule(
                "repair-semantic-nonfillability-add-contract-evidence-v0",
                "nonfillability_witness",
                "contract",
                &[
                    "selected semantic diagram and witness refs resolve",
                    "contract and test evidence cover both compared observations",
                    "exactness assumptions match the selected AIR path refs",
                ],
                "translate",
                &["selected semantic diagram boundary"],
                &[
                    "static obstruction can stay unchanged",
                    "new contract can reveal additional semantic witnesses",
                ],
                &[
                    "obstructionAsNonFillability_sound",
                    "DiagramFiller",
                    "RepairTransferCounterexample.staticSplitRepair_transfers_runtime",
                ],
                "manual",
                "low",
            ),
        ],
        non_conclusions: REQUIRED_NON_CONCLUSIONS
            .iter()
            .map(|value| value.to_string())
            .collect(),
    }
}

pub fn validate_repair_rule_registry_report(
    registry: &RepairRuleRegistryV0,
    input_path: &str,
) -> RepairRuleRegistryValidationReportV0 {
    let checks = vec![
        check_schema_version(registry),
        check_repair_rule_ids(registry),
        check_target_witness_kinds(registry),
        check_operation_kinds(registry),
        check_expected_effects(registry),
        check_required_preconditions(registry),
        check_side_effects(registry),
        check_patch_strategy_and_confidence(registry),
        check_selected_universe_and_assumptions(registry),
        check_non_conclusion_boundary(registry),
    ];
    let summary = RepairRuleRegistryValidationSummary {
        result: if checks.iter().any(|check| check.result == "fail") {
            "fail".to_string()
        } else if checks.iter().any(|check| check.result == "warn") {
            "warn".to_string()
        } else {
            "pass".to_string()
        },
        rule_count: registry.rules.len(),
        failed_check_count: count_checks(&checks, "fail"),
        warning_check_count: count_checks(&checks, "warn"),
    };

    RepairRuleRegistryValidationReportV0 {
        schema_version: REPAIR_RULE_REGISTRY_VALIDATION_REPORT_SCHEMA_VERSION.to_string(),
        input: RepairRuleRegistryValidationInput {
            schema_version: registry.schema_version.clone(),
            path: input_path.to_string(),
            scope: registry.scope.clone(),
        },
        registry: registry.clone(),
        summary,
        checks,
    }
}

fn repair_rule(
    repair_rule_id: &str,
    target_witness_kind: &str,
    proposed_operation: &str,
    required_preconditions: &[&str],
    expected_effect: &str,
    preserved_invariants: &[&str],
    possible_side_effects: &[&str],
    proof_obligation_refs: &[&str],
    patch_strategy: &str,
    confidence: &str,
) -> RepairRuleV0 {
    RepairRuleV0 {
        repair_rule_id: repair_rule_id.to_string(),
        target_witness_kind: target_witness_kind.to_string(),
        proposed_operation: proposed_operation.to_string(),
        required_preconditions: strings(required_preconditions),
        expected_effect: expected_effect.to_string(),
        preserved_invariants: strings(preserved_invariants),
        possible_side_effects: strings(possible_side_effects),
        proof_obligation_refs: strings(proof_obligation_refs),
        patch_strategy: patch_strategy.to_string(),
        confidence: confidence.to_string(),
        relative_to: RepairRuleRelativeScopeV0 {
            selected_obstruction_universe:
                "selected obstruction witnesses in the current Feature Extension Report".to_string(),
            explicit_assumptions: vec![
                "only the referenced witness kind is targeted".to_string(),
                "other measured and unmeasured axes are checked separately".to_string(),
            ],
        },
        non_conclusions: REQUIRED_NON_CONCLUSIONS
            .iter()
            .map(|value| value.to_string())
            .collect(),
    }
}

fn strings(values: &[&str]) -> Vec<String> {
    values.iter().map(|value| value.to_string()).collect()
}

fn check_schema_version(registry: &RepairRuleRegistryV0) -> ValidationCheck {
    let mut check = validation_check(
        "repair-rule-registry-schema-version-supported",
        "repair rule registry schema version is supported",
        if registry.schema_version == REPAIR_RULE_REGISTRY_SCHEMA_VERSION {
            "pass"
        } else {
            "fail"
        },
    );
    if check.result == "fail" {
        check.reason = Some(format!(
            "unsupported repair rule registry schemaVersion: {}",
            registry.schema_version
        ));
    }
    check
}

fn check_repair_rule_ids(registry: &RepairRuleRegistryV0) -> ValidationCheck {
    let duplicate_ids = duplicates(
        registry
            .rules
            .iter()
            .map(|rule| rule.repair_rule_id.as_str()),
    );
    let invalid_ids: Vec<String> = registry
        .rules
        .iter()
        .filter(|rule| rule.repair_rule_id.trim().is_empty())
        .map(|rule| rule.target_witness_kind.clone())
        .chain(duplicate_ids)
        .collect();
    check_invalid_examples(
        "repair-rule-ids-valid",
        "repair_rule_id values are non-empty and unique",
        invalid_ids,
        "invalid repair_rule_id",
    )
}

fn check_target_witness_kinds(registry: &RepairRuleRegistryV0) -> ValidationCheck {
    let supported = string_set(SUPPORTED_TARGET_WITNESS_KINDS);
    let invalid = registry
        .rules
        .iter()
        .filter(|rule| !supported.contains(rule.target_witness_kind.as_str()))
        .map(|rule| {
            generic_validation_example(
                &rule.repair_rule_id,
                &rule.target_witness_kind,
                "unsupported target_witness_kind",
            )
        })
        .collect();
    check_examples(
        "repair-rule-target-witness-kind-supported",
        "target witness kind is supported",
        invalid,
    )
}

fn check_operation_kinds(registry: &RepairRuleRegistryV0) -> ValidationCheck {
    let supported = string_set(SUPPORTED_OPERATIONS);
    let invalid = registry
        .rules
        .iter()
        .filter(|rule| !supported.contains(rule.proposed_operation.as_str()))
        .map(|rule| {
            generic_validation_example(
                &rule.repair_rule_id,
                &rule.proposed_operation,
                "unsupported proposed_operation",
            )
        })
        .collect();
    check_examples(
        "repair-rule-operation-kind-supported",
        "proposed operation kind is supported",
        invalid,
    )
}

fn check_expected_effects(registry: &RepairRuleRegistryV0) -> ValidationCheck {
    let supported = string_set(SUPPORTED_EXPECTED_EFFECTS);
    let invalid = registry
        .rules
        .iter()
        .filter(|rule| !supported.contains(rule.expected_effect.as_str()))
        .map(|rule| {
            generic_validation_example(
                &rule.repair_rule_id,
                &rule.expected_effect,
                "unsupported expected_effect",
            )
        })
        .collect();
    check_examples(
        "repair-rule-expected-effect-supported",
        "expected effect is supported",
        invalid,
    )
}

fn check_required_preconditions(registry: &RepairRuleRegistryV0) -> ValidationCheck {
    let invalid = registry
        .rules
        .iter()
        .filter(|rule| {
            rule.required_preconditions.is_empty()
                || rule
                    .required_preconditions
                    .iter()
                    .any(|precondition| precondition.trim().is_empty())
                || rule.proof_obligation_refs.is_empty()
        })
        .map(|rule| {
            generic_validation_example(
                &rule.repair_rule_id,
                &rule.proposed_operation,
                "required preconditions and proof obligation refs must be recorded",
            )
        })
        .collect();
    check_examples(
        "repair-rule-preconditions-recorded",
        "preconditions and proof obligation refs are recorded",
        invalid,
    )
}

fn check_side_effects(registry: &RepairRuleRegistryV0) -> ValidationCheck {
    let invalid = registry
        .rules
        .iter()
        .filter(|rule| {
            rule.possible_side_effects.is_empty()
                || rule
                    .possible_side_effects
                    .iter()
                    .any(|effect| effect.trim().is_empty())
        })
        .map(|rule| {
            generic_validation_example(
                &rule.repair_rule_id,
                &rule.expected_effect,
                "possible side effects must be recorded",
            )
        })
        .collect();
    check_examples(
        "repair-rule-side-effects-recorded",
        "possible side effects are recorded",
        invalid,
    )
}

fn check_patch_strategy_and_confidence(registry: &RepairRuleRegistryV0) -> ValidationCheck {
    let supported_patch_strategies = string_set(SUPPORTED_PATCH_STRATEGIES);
    let supported_confidence = string_set(SUPPORTED_CONFIDENCE);
    let invalid = registry
        .rules
        .iter()
        .filter(|rule| {
            !supported_patch_strategies.contains(rule.patch_strategy.as_str())
                || !supported_confidence.contains(rule.confidence.as_str())
        })
        .map(|rule| {
            generic_validation_example(
                &rule.repair_rule_id,
                &rule.patch_strategy,
                "unsupported patch_strategy or confidence",
            )
        })
        .collect();
    check_examples(
        "repair-rule-patch-strategy-confidence-supported",
        "patch strategy and confidence are supported",
        invalid,
    )
}

fn check_selected_universe_and_assumptions(registry: &RepairRuleRegistryV0) -> ValidationCheck {
    let mut invalid = Vec::new();
    if registry.selected_obstruction_universe.trim().is_empty()
        || registry.explicit_assumptions.is_empty()
        || registry
            .explicit_assumptions
            .iter()
            .any(|assumption| assumption.trim().is_empty())
    {
        invalid.push(generic_validation_example(
            "registry",
            &registry.scope,
            "registry must record selected obstruction universe and explicit assumptions",
        ));
    }
    invalid.extend(
        registry
            .rules
            .iter()
            .filter(|rule| {
                rule.relative_to
                    .selected_obstruction_universe
                    .trim()
                    .is_empty()
                    || rule.relative_to.explicit_assumptions.is_empty()
                    || rule
                        .relative_to
                        .explicit_assumptions
                        .iter()
                        .any(|assumption| assumption.trim().is_empty())
            })
            .map(|rule| {
                generic_validation_example(
                    &rule.repair_rule_id,
                    &rule.target_witness_kind,
                    "rule must be relative to a selected universe and explicit assumptions",
                )
            }),
    );
    check_examples(
        "repair-rule-relative-boundary-recorded",
        "registry and rules record selected universe and explicit assumptions",
        invalid,
    )
}

fn check_non_conclusion_boundary(registry: &RepairRuleRegistryV0) -> ValidationCheck {
    let required = string_set(REQUIRED_NON_CONCLUSIONS);
    let mut invalid = Vec::new();
    if !contains_all(&registry.non_conclusions, &required) {
        invalid.push(generic_validation_example(
            "registry",
            &registry.scope,
            "registry non-conclusions must include repair boundary",
        ));
    }
    invalid.extend(
        registry
            .rules
            .iter()
            .filter(|rule| !contains_all(&rule.non_conclusions, &required))
            .map(|rule| {
                generic_validation_example(
                    &rule.repair_rule_id,
                    &rule.target_witness_kind,
                    "rule non-conclusions must include repair boundary",
                )
            }),
    );
    check_examples(
        "repair-rule-non-conclusion-boundary-recorded",
        "repair non-conclusion boundary is recorded",
        invalid,
    )
}

fn check_invalid_examples(
    id: &str,
    title: &str,
    invalid_values: Vec<String>,
    reason: &str,
) -> ValidationCheck {
    let examples = invalid_values
        .iter()
        .map(|value| generic_validation_example(value, value, reason))
        .collect();
    check_examples(id, title, examples)
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

fn contains_all(values: &[String], required: &BTreeSet<&str>) -> bool {
    let actual: BTreeSet<&str> = values.iter().map(String::as_str).collect();
    required.iter().all(|value| actual.contains(value))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn static_registry_validates_and_records_repair_boundaries() {
        let registry = static_repair_rule_registry();
        let report = validate_repair_rule_registry_report(&registry, "static");

        assert_eq!(report.summary.result, "pass");
        assert_eq!(report.summary.rule_count, 3);
        assert!(report.registry.rules.iter().any(|rule| {
            rule.repair_rule_id == "repair-hidden-interaction-through-interface-v0"
                && rule.target_witness_kind == "hidden_interaction"
                && rule.proposed_operation == "split"
                && rule
                    .non_conclusions
                    .iter()
                    .any(|boundary| boundary == "global flatness preservation is not concluded")
        }));
    }

    #[test]
    fn validation_rejects_success_claim_without_required_boundaries() {
        let mut registry = static_repair_rule_registry();
        registry.rules[0].repair_rule_id = registry.rules[1].repair_rule_id.clone();
        registry.rules[0].target_witness_kind = "unknown_witness".to_string();
        registry.rules[0].proposed_operation = "auto_rewrite".to_string();
        registry.rules[0].required_preconditions.clear();
        registry.rules[0].possible_side_effects.clear();
        registry.rules[0].relative_to.explicit_assumptions.clear();
        registry.rules[0].non_conclusions.clear();

        let report = validate_repair_rule_registry_report(&registry, "invalid");

        assert_eq!(report.summary.result, "fail");
        assert!(report.summary.failed_check_count >= 6);
        assert!(report.checks.iter().any(|check| {
            check.id == "repair-rule-non-conclusion-boundary-recorded" && check.result == "fail"
        }));
    }
}
