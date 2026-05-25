use std::collections::{BTreeMap, BTreeSet};
use std::error::Error;
use std::fs;
use std::path::Path;

use crate::validation::{count_checks, duplicates, generic_validation_example, validation_check};
use crate::{
    ARCHITECTURE_POLICY_SCHEMA_VERSION, ARCHITECTURE_POLICY_VALIDATION_REPORT_SCHEMA_VERSION,
    ArchitectureAdoptedLawV0, ArchitecturePolicyDependencyRuleV0, ArchitecturePolicyExceptionV0,
    ArchitecturePolicyV0, ArchitecturePolicyValidationInputV0,
    ArchitecturePolicyValidationReportV0, ArchitecturePolicyValidationSummaryV0, Component, Edge,
    LAW_VIOLATION_REPORT_SCHEMA_VERSION, LawViolationExceptionFindingV0, LawViolationFindingV0,
    LawViolationPolicyRefV0, LawViolationReportV0, LawViolationSig0RefV0, LawViolationSummaryV0,
    LawViolationUnmeasuredV0, MetricStatus, PolicyViolation, Sig0Document, SrpReviewCueV0,
    ValidationCheck, measured_status, unmeasured_status,
};

const REQUIRED_NON_CONCLUSIONS: [&str; 5] = [
    "architecture policy is review evidence, not a Lean theorem",
    "LayeredArchitecture findings are deterministic over the measured selector universe only",
    "SRP findings are evidence cues for LLM review, not tool-only violation judgments",
    "unmeasured selector coverage is not measured zero",
    "policy pass does not conclude architecture lawfulness",
];

const SRP_JUDGMENT_TAXONOMY: [&str; 6] = [
    "violation",
    "probableViolation",
    "risk",
    "acceptableOrchestrator",
    "unmeasured",
    "allowedException",
];

pub fn read_architecture_policy(path: &Path) -> Result<ArchitecturePolicyV0, Box<dyn Error>> {
    let source = fs::read_to_string(path)?;
    let policy: ArchitecturePolicyV0 = serde_json::from_str(&source)?;
    Ok(policy)
}

pub fn validate_architecture_policy_report(
    policy: &ArchitecturePolicyV0,
    input_path: &str,
) -> ArchitecturePolicyValidationReportV0 {
    let checks = vec![
        check_schema_version(policy),
        check_identity(policy),
        check_adopted_laws(policy),
        check_layers(policy),
        check_dependency_rules(policy),
        check_srp_boundary(policy),
        check_sft_governance_boundary(policy),
        check_non_conclusions(policy),
    ];
    let summary = ArchitecturePolicyValidationSummaryV0 {
        result: if checks.iter().any(|check| check.result == "fail") {
            "fail".to_string()
        } else if checks.iter().any(|check| check.result == "warn") {
            "warn".to_string()
        } else {
            "pass".to_string()
        },
        adopted_law_count: policy.adopted_laws.len(),
        layer_count: policy.layers.len(),
        forbidden_dependency_count: policy.forbidden_dependencies.len(),
        exception_count: policy.exceptions.len(),
        failed_check_count: count_checks(&checks, "fail"),
        warning_check_count: count_checks(&checks, "warn"),
    };

    ArchitecturePolicyValidationReportV0 {
        schema_version: ARCHITECTURE_POLICY_VALIDATION_REPORT_SCHEMA_VERSION.to_string(),
        input: ArchitecturePolicyValidationInputV0 {
            schema_version: policy.schema_version.clone(),
            path: input_path.to_string(),
            policy_id: policy.policy_id.clone(),
            policy_version: policy.policy_version.clone(),
            component_id_kind: policy.component_id_kind.clone(),
        },
        policy: policy.clone(),
        summary,
        checks,
    }
}

pub fn build_law_violation_report(
    sig0: &Sig0Document,
    sig0_path: Option<&str>,
    policy: &ArchitecturePolicyV0,
    policy_path: Option<&str>,
) -> LawViolationReportV0 {
    let layer_lookup = resolve_layers(policy, &sig0.components);
    let deterministic_violations =
        evaluate_layered_violations(policy, &sig0.components, &sig0.edges, &layer_lookup);
    let allowed_exceptions =
        evaluate_allowed_exceptions(policy, &sig0.components, &sig0.edges, &layer_lookup);
    let unmeasured = unmeasured_layer_items(policy, &sig0.components, &layer_lookup);
    let review_actions = report_review_actions(&deterministic_violations, &unmeasured);
    let result = if !deterministic_violations.is_empty() {
        "fail"
    } else if !unmeasured.is_empty() {
        "warn"
    } else {
        "pass"
    };

    LawViolationReportV0 {
        schema_version: LAW_VIOLATION_REPORT_SCHEMA_VERSION.to_string(),
        report_id: format!("law-violation-report:{}", policy.policy_id),
        policy_ref: LawViolationPolicyRefV0 {
            policy_id: policy.policy_id.clone(),
            policy_version: policy.policy_version.clone(),
            path: policy_path.map(str::to_string),
        },
        sig0_ref: LawViolationSig0RefV0 {
            root: sig0.root.clone(),
            component_kind: sig0.component_kind.clone(),
            path: sig0_path.map(str::to_string),
        },
        summary: LawViolationSummaryV0 {
            result: result.to_string(),
            deterministic_violation_count: deterministic_violations.len(),
            allowed_exception_count: allowed_exceptions.len(),
            srp_cue_count: 0,
            unmeasured_count: unmeasured.len(),
        },
        deterministic_violations,
        allowed_exceptions,
        srp_cues: Vec::new(),
        unmeasured,
        review_actions,
        non_conclusions: REQUIRED_NON_CONCLUSIONS
            .iter()
            .map(|value| value.to_string())
            .collect(),
    }
}

pub fn apply_architecture_policy_to_sig0(
    sig0: &mut Sig0Document,
    policy: &ArchitecturePolicyV0,
    policy_path: Option<&str>,
) {
    let report = build_law_violation_report(sig0, None, policy, policy_path);
    sig0.policies.policy_id = Some(policy.policy_id.clone());
    sig0.policies.schema_version = Some(policy.schema_version.clone());
    sig0.policies.boundary_group_count = Some(policy.layers.len());
    sig0.policies.boundary_allowed = policy
        .allowed_dependencies
        .iter()
        .map(|rule| {
            format!(
                "{}:{}->{}",
                rule.rule_id, rule.source_layer, rule.target_layer
            )
        })
        .collect();
    sig0.signature.boundary_violation_count = report.deterministic_violations.len();
    sig0.policy_violations = report
        .deterministic_violations
        .iter()
        .map(|finding| PolicyViolation {
            axis: "boundaryViolationCount".to_string(),
            source: finding.source.clone(),
            target: finding.target.clone(),
            evidence: finding.evidence.clone(),
            source_group: Some(finding.source_layer.clone()),
            target_group: Some(finding.target_layer.clone()),
            relation_ids: Some(vec![finding.rule_id.clone()]),
        })
        .collect();
    let status = if report.unmeasured.is_empty() {
        measured_status(&format!("policy:{}", policy.policy_id))
    } else {
        unmeasured_status(
            "architecture-policy selector coverage is incomplete; placeholder zero is not measured zero"
                .to_string(),
        )
    };
    sig0.metric_status
        .insert("boundaryViolationCount".to_string(), status);
    sig0.metric_status.insert(
        "srpReviewCueCount".to_string(),
        MetricStatus {
            measured: false,
            reason: Some(
                "SRP review cues require ArchMap semantic evidence and LLM judgment".to_string(),
            ),
            source: policy_path.map(str::to_string),
        },
    );
}

pub fn srp_review_cue_from_archmap_item(
    item_id: &str,
    subject_ref: String,
    semantic_role: Option<String>,
    responsibility_regions: Vec<String>,
    reason_to_change: Vec<String>,
    actor_refs: Vec<String>,
    allowed_role: Option<String>,
    law_refs: Vec<String>,
    evidence_refs: Vec<String>,
    policy_refs: Vec<String>,
    missing_evidence: Vec<String>,
    non_conclusions: Vec<String>,
) -> Option<SrpReviewCueV0> {
    let has_srp_evidence = semantic_role.is_some()
        || !responsibility_regions.is_empty()
        || !reason_to_change.is_empty()
        || !actor_refs.is_empty()
        || allowed_role.is_some()
        || law_refs.iter().any(|law| law.contains("SRP"));
    has_srp_evidence.then(|| SrpReviewCueV0 {
        cue_id: format!("srp-cue:{item_id}"),
        subject_ref,
        semantic_role,
        responsibility_regions,
        reason_to_change,
        actor_refs,
        allowed_role,
        law_refs,
        judgment_taxonomy: SRP_JUDGMENT_TAXONOMY
            .iter()
            .map(|value| value.to_string())
            .collect(),
        evidence_refs,
        policy_refs,
        missing_evidence,
        review_level: "Level 3 LLM probable violation judgment".to_string(),
        review_action:
            "LLM Review Skill must cite evidence refs and policy refs before probableViolation"
                .to_string(),
        non_conclusions,
    })
}

fn check_schema_version(policy: &ArchitecturePolicyV0) -> ValidationCheck {
    let mut check = validation_check(
        "architecture-policy-schema-version-supported",
        "architecture policy schema version is supported",
        if policy.schema_version == ARCHITECTURE_POLICY_SCHEMA_VERSION {
            "pass"
        } else {
            "fail"
        },
    );
    if check.result == "fail" {
        check.reason = Some(format!(
            "unsupported architecture policy schemaVersion: {}",
            policy.schema_version
        ));
    }
    check
}

fn check_identity(policy: &ArchitecturePolicyV0) -> ValidationCheck {
    let mut invalid = Vec::new();
    for (field, value) in [
        ("policyId", &policy.policy_id),
        ("policyVersion", &policy.policy_version),
        ("componentIdKind", &policy.component_id_kind),
        ("selectorSemantics", &policy.selector_semantics),
    ] {
        if value.trim().is_empty() {
            invalid.push(generic_validation_example(
                field,
                value,
                "field must be non-empty",
            ));
        }
    }
    if policy.selector_semantics != "exact-or-prefix-star" {
        invalid.push(generic_validation_example(
            "selectorSemantics",
            &policy.selector_semantics,
            "only exact-or-prefix-star selectors are supported in v0",
        ));
    }
    check_examples(
        "architecture-policy-identity-recorded",
        "policy identity and selector semantics are recorded",
        invalid,
    )
}

fn check_adopted_laws(policy: &ArchitecturePolicyV0) -> ValidationCheck {
    let mut invalid = Vec::new();
    if policy.adopted_laws.is_empty() {
        invalid.push(generic_validation_example(
            &policy.policy_id,
            "adoptedLaws",
            "at least one adopted law is required",
        ));
    }
    for duplicate in duplicates(policy.adopted_laws.iter().map(|law| law.law_id.as_str())) {
        invalid.push(generic_validation_example(
            &duplicate,
            "adoptedLaws",
            "duplicate law id",
        ));
    }
    for law in &policy.adopted_laws {
        if law.law_id.trim().is_empty()
            || law.law_kind.trim().is_empty()
            || law.enforcement.trim().is_empty()
            || law.review_level.trim().is_empty()
        {
            invalid.push(generic_validation_example(
                &law.law_id,
                &law.law_kind,
                "adopted law fields must be non-empty",
            ));
        }
    }
    check_examples(
        "architecture-policy-adopted-laws-recorded",
        "adopted design laws are explicit",
        invalid,
    )
}

fn check_layers(policy: &ArchitecturePolicyV0) -> ValidationCheck {
    let mut invalid = Vec::new();
    for duplicate in duplicates(policy.layers.iter().map(|layer| layer.layer_id.as_str())) {
        invalid.push(generic_validation_example(
            &duplicate,
            "layers",
            "duplicate layer id",
        ));
    }
    for layer in &policy.layers {
        if layer.layer_id.trim().is_empty()
            || layer.selectors.is_empty()
            || has_blank(&layer.selectors)
        {
            invalid.push(generic_validation_example(
                &layer.layer_id,
                "selectors",
                "layer id and selectors must be non-empty",
            ));
        }
    }
    check_examples(
        "architecture-policy-layer-selectors-recorded",
        "layer selectors are explicit",
        invalid,
    )
}

fn check_dependency_rules(policy: &ArchitecturePolicyV0) -> ValidationCheck {
    let law_ids = policy
        .adopted_laws
        .iter()
        .map(|law| law.law_id.as_str())
        .collect::<BTreeSet<_>>();
    let layer_ids = policy
        .layers
        .iter()
        .map(|layer| layer.layer_id.as_str())
        .collect::<BTreeSet<_>>();
    let mut invalid = Vec::new();
    for rule in policy
        .allowed_dependencies
        .iter()
        .chain(policy.forbidden_dependencies.iter())
    {
        validate_dependency_rule(rule, &law_ids, &layer_ids, &mut invalid);
    }
    for exception in &policy.exceptions {
        validate_exception(exception, &law_ids, &mut invalid);
    }
    check_examples(
        "architecture-policy-dependency-rules-resolve",
        "dependency rules and exceptions refer to known laws and layers",
        invalid,
    )
}

fn validate_dependency_rule(
    rule: &ArchitecturePolicyDependencyRuleV0,
    law_ids: &BTreeSet<&str>,
    layer_ids: &BTreeSet<&str>,
    invalid: &mut Vec<crate::ValidationExample>,
) {
    if rule.rule_id.trim().is_empty()
        || !law_ids.contains(rule.law_ref.as_str())
        || !layer_ids.contains(rule.source_layer.as_str())
        || !layer_ids.contains(rule.target_layer.as_str())
        || rule.severity.trim().is_empty()
        || rule.review_action.trim().is_empty()
    {
        invalid.push(generic_validation_example(
            &rule.rule_id,
            &rule.law_ref,
            "dependency rule must cite known law/layers and review action",
        ));
    }
}

fn validate_exception(
    exception: &ArchitecturePolicyExceptionV0,
    law_ids: &BTreeSet<&str>,
    invalid: &mut Vec<crate::ValidationExample>,
) {
    if exception.exception_id.trim().is_empty()
        || !law_ids.contains(exception.law_ref.as_str())
        || exception.source_selector.trim().is_empty()
        || exception.target_selector.trim().is_empty()
        || exception.reason.trim().is_empty()
    {
        invalid.push(generic_validation_example(
            &exception.exception_id,
            &exception.law_ref,
            "exception must cite known law and non-empty selectors/reason",
        ));
    }
}

fn check_srp_boundary(policy: &ArchitecturePolicyV0) -> ValidationCheck {
    let srp = &policy.srp;
    let invalid = (srp.responsibility_taxonomy.is_empty()
        || srp.reason_to_change_categories.is_empty()
        || srp.allowed_orchestrator_roles.is_empty()
        || srp.required_evidence_fields.is_empty()
        || srp.judgment_boundary.trim().is_empty())
    .then(|| {
        generic_validation_example(
            &policy.policy_id,
            "srp",
            "SRP taxonomy, reason categories, allowed roles, required evidence fields, and judgment boundary are required",
        )
    })
    .into_iter()
    .collect();
    check_examples(
        "architecture-policy-srp-evidence-boundary-recorded",
        "SRP semantic evidence and LLM judgment boundary are explicit",
        invalid,
    )
}

fn check_sft_governance_boundary(policy: &ArchitecturePolicyV0) -> ValidationCheck {
    let governance = &policy.sft_governance;
    let mut invalid = Vec::new();
    for rule in governance
        .allowed_operation_families
        .iter()
        .chain(governance.conditionally_allowed_support.iter())
        .chain(governance.forbidden_future_path_classes.iter())
    {
        if rule.rule_id.trim().is_empty()
            || rule.applies_to.is_empty()
            || rule.disposition.trim().is_empty()
            || rule.reason.trim().is_empty()
            || rule.reviewer_action.trim().is_empty()
        {
            invalid.push(generic_validation_example(
                &rule.rule_id,
                "sftGovernance",
                "future policy rules require ids, targets, disposition, reason, and reviewer action",
            ));
        }
    }
    for intervention in &governance.required_governance_interventions {
        if intervention.intervention_id.trim().is_empty()
            || intervention.applies_to.is_empty()
            || intervention.required_before.trim().is_empty()
            || intervention.preservation_boundary.trim().is_empty()
        {
            invalid.push(generic_validation_example(
                &intervention.intervention_id,
                "sftGovernance.requiredGovernanceInterventions",
                "governance interventions require ids, targets, timing, and preservation boundary",
            ));
        }
    }
    check_examples(
        "architecture-policy-sft-governance-boundary-recorded",
        "SFT governance future policy is explicit when provided",
        invalid,
    )
}

fn check_non_conclusions(policy: &ArchitecturePolicyV0) -> ValidationCheck {
    let conclusions = policy
        .non_conclusions
        .iter()
        .map(String::as_str)
        .collect::<BTreeSet<_>>();
    let invalid: Vec<_> = REQUIRED_NON_CONCLUSIONS
        .iter()
        .filter(|required| !conclusions.contains(**required))
        .map(|required| generic_validation_example(&policy.policy_id, "nonConclusions", required))
        .collect();
    check_examples(
        "architecture-policy-non-conclusion-boundary-recorded",
        "non-conclusions are review guardrails",
        invalid,
    )
}

fn evaluate_layered_violations(
    policy: &ArchitecturePolicyV0,
    components: &[Component],
    edges: &[Edge],
    layer_lookup: &BTreeMap<String, LayerResolution>,
) -> Vec<LawViolationFindingV0> {
    let component_ids = components
        .iter()
        .map(|component| component.id.as_str())
        .collect::<BTreeSet<_>>();
    let mut findings = Vec::new();
    for edge in edges {
        if !component_ids.contains(edge.source.as_str())
            || !component_ids.contains(edge.target.as_str())
            || edge_has_exception(policy, &edge.source, &edge.target)
        {
            continue;
        }
        let Some(source_layer) = single_layer(layer_lookup, &edge.source) else {
            continue;
        };
        let Some(target_layer) = single_layer(layer_lookup, &edge.target) else {
            continue;
        };
        let Some(rule) = policy.forbidden_dependencies.iter().find(|rule| {
            rule.source_layer == source_layer.layer_id && rule.target_layer == target_layer.layer_id
        }) else {
            continue;
        };
        findings.push(LawViolationFindingV0 {
            finding_id: format!("layered:{}->{}", edge.source, edge.target),
            law_ref: rule.law_ref.clone(),
            law_kind: "LayeredArchitecture".to_string(),
            source: edge.source.clone(),
            target: edge.target.clone(),
            source_layer: source_layer.layer_id.to_string(),
            target_layer: target_layer.layer_id.to_string(),
            rule_id: rule.rule_id.clone(),
            severity: rule.severity.clone(),
            evidence: edge.evidence.clone(),
            review_action: rule.review_action.clone(),
            evidence_boundary:
                "deterministic over resolved layer selectors and measured static import edges"
                    .to_string(),
            non_conclusions: REQUIRED_NON_CONCLUSIONS
                .iter()
                .map(|value| value.to_string())
                .collect(),
        });
    }
    findings
}

fn evaluate_allowed_exceptions(
    policy: &ArchitecturePolicyV0,
    components: &[Component],
    edges: &[Edge],
    _layer_lookup: &BTreeMap<String, LayerResolution>,
) -> Vec<LawViolationExceptionFindingV0> {
    let component_ids = components
        .iter()
        .map(|component| component.id.as_str())
        .collect::<BTreeSet<_>>();
    let mut exceptions = Vec::new();
    for edge in edges {
        if !component_ids.contains(edge.source.as_str())
            || !component_ids.contains(edge.target.as_str())
        {
            continue;
        }
        for exception in &policy.exceptions {
            if selector_matches(&exception.source_selector, &edge.source)
                && selector_matches(&exception.target_selector, &edge.target)
            {
                exceptions.push(LawViolationExceptionFindingV0 {
                    exception_id: exception.exception_id.clone(),
                    law_ref: exception.law_ref.clone(),
                    source: edge.source.clone(),
                    target: edge.target.clone(),
                    reason: exception.reason.clone(),
                    review_action: "confirm the exception remains intentional and scoped"
                        .to_string(),
                });
            }
        }
    }
    exceptions
}

fn unmeasured_layer_items(
    policy: &ArchitecturePolicyV0,
    components: &[Component],
    layer_lookup: &BTreeMap<String, LayerResolution>,
) -> Vec<LawViolationUnmeasuredV0> {
    let mut items = Vec::new();
    let component_ids = components
        .iter()
        .map(|component| component.id.clone())
        .collect::<BTreeSet<_>>();
    for layer in &policy.layers {
        for selector in &layer.selectors {
            if !component_ids
                .iter()
                .any(|component_id| selector_matches(selector, component_id))
            {
                items.push(LawViolationUnmeasuredV0 {
                    item_id: format!("unresolved-selector:{}:{selector}", layer.layer_id),
                    category: "unresolvedSelector".to_string(),
                    subject_ref: selector.clone(),
                    reason: "layer selector matched no measured component".to_string(),
                    review_action: "fix selector or record this universe as unmeasured".to_string(),
                });
            }
        }
    }
    for component in components {
        match layer_lookup.get(&component.id) {
            Some(resolution) if resolution.layer_ids.len() == 1 => {}
            Some(resolution) if resolution.layer_ids.len() > 1 => {
                items.push(LawViolationUnmeasuredV0 {
                    item_id: format!("ambiguous-layer:{}", component.id),
                    category: "ambiguousLayerSelector".to_string(),
                    subject_ref: component.id.clone(),
                    reason: format!(
                        "component matched multiple layers: {}",
                        resolution.layer_ids.join(",")
                    ),
                    review_action:
                        "make layer selectors disjoint before reading policy zero as measured"
                            .to_string(),
                })
            }
            _ => items.push(LawViolationUnmeasuredV0 {
                item_id: format!("unclassified-layer:{}", component.id),
                category: "unclassifiedComponent".to_string(),
                subject_ref: component.id.clone(),
                reason: "component matched no architecture-policy layer".to_string(),
                review_action: "add a layer selector or keep boundaryViolationCount unmeasured"
                    .to_string(),
            }),
        }
    }
    items
}

#[derive(Debug, Clone)]
struct LayerResolution {
    layer_ids: Vec<String>,
}

fn resolve_layers(
    policy: &ArchitecturePolicyV0,
    components: &[Component],
) -> BTreeMap<String, LayerResolution> {
    components
        .iter()
        .map(|component| {
            let layer_ids = policy
                .layers
                .iter()
                .filter(|layer| {
                    layer
                        .selectors
                        .iter()
                        .any(|selector| selector_matches(selector, &component.id))
                })
                .map(|layer| layer.layer_id.clone())
                .collect();
            (component.id.clone(), LayerResolution { layer_ids })
        })
        .collect()
}

fn single_layer<'a>(
    layer_lookup: &'a BTreeMap<String, LayerResolution>,
    component_id: &str,
) -> Option<ResolvedLayer<'a>> {
    let resolution = layer_lookup.get(component_id)?;
    (resolution.layer_ids.len() == 1).then(|| ResolvedLayer {
        layer_id: &resolution.layer_ids[0],
    })
}

struct ResolvedLayer<'a> {
    layer_id: &'a str,
}

fn edge_has_exception(policy: &ArchitecturePolicyV0, source: &str, target: &str) -> bool {
    policy.exceptions.iter().any(|exception| {
        selector_matches(&exception.source_selector, source)
            && selector_matches(&exception.target_selector, target)
    })
}

fn selector_matches(selector: &str, component_id: &str) -> bool {
    selector == component_id
        || selector
            .strip_suffix(".*")
            .map(|prefix| component_id == prefix || component_id.starts_with(&format!("{prefix}.")))
            .unwrap_or(false)
}

fn report_review_actions(
    findings: &[LawViolationFindingV0],
    unmeasured: &[LawViolationUnmeasuredV0],
) -> Vec<String> {
    let mut actions = findings
        .iter()
        .map(|finding| finding.review_action.clone())
        .chain(unmeasured.iter().map(|item| item.review_action.clone()))
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect::<Vec<_>>();
    if actions.is_empty() {
        actions.push(
            "no deterministic LayeredArchitecture action over the measured selector universe"
                .to_string(),
        );
    }
    actions
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

fn has_blank(values: &[String]) -> bool {
    values.iter().any(|value| value.trim().is_empty())
}

#[allow(dead_code)]
fn _law_kind(law: &ArchitectureAdoptedLawV0) -> &str {
    &law.law_kind
}
