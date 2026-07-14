use std::collections::{BTreeMap, BTreeSet};
use std::error::Error;
use std::fmt;
use std::path::Path;

use serde_json::{Map, Value, json};
use sha2::{Digest, Sha256};

use crate::{
    ARCHSIG_COMPARISON_REPORT_V1_SCHEMA, ARCHSIG_GATE_BLOCKED_BY_GATE_POLICY,
    ARCHSIG_GATE_NOT_EVALUABLE, ARCHSIG_GATE_PASS_WITHIN_GATE_POLICY,
    ARCHSIG_GATE_POLICY_V1_SCHEMA, ARCHSIG_GATE_REPORT_V1_SCHEMA,
    ARCHSIG_MEASUREMENT_PACKET_V1_SCHEMA, ArchSigMeasurementPacketV1,
    validate_measurement_packet_value_v1,
};

const ABSOLUTE_MAPPING_KEYS: [&str; 6] = [
    "measured_zero",
    "measured_nonzero",
    "unmeasured",
    "unknown",
    "not_computed",
    "violated_assumption_dependency",
];
const INTRODUCED_MAPPING_KEYS: [&str; 5] = ["new", "cleared", "preexisting", "removed", "other"];
const ACTIONS: [&str; 3] = ["pass", "pass_with_boundary", "block"];
const COMPARISON_LEVELS: [&str; 3] = ["identical", "verdict-row", "not-comparable"];
const COMPARISON_TRANSITIONS: [&str; 5] = [
    "new_recorded_row",
    "removed_recorded_row",
    "measured_obstruction_no_longer_recorded",
    "measured_obstruction_recorded_after_change",
    "preexisting_recorded_row",
];
const COMPARISON_OTHER_TRANSITION: &str = "other_transition";
const STRUCTURAL_VERDICT_KEYS: [&str; 5] = [
    "measured_zero",
    "measured_nonzero",
    "unmeasured",
    "unknown",
    "not_computed",
];
const NON_TERMINAL_KEYS: [&str; 4] = [
    "unmeasured",
    "unknown",
    "not_computed",
    "violated_assumption_dependency",
];
const BOUNDARY_OVERRIDE_KEYS: [&str; 6] = [
    "silence_by_design",
    "out_of_selected_vocabulary",
    "unmeasured_support",
    "violated_assumption",
    "blocked_method",
    "not_applicable",
];

pub fn validate_gate_policy_v1(policy: &Value) -> Vec<Value> {
    let mut checks = Vec::new();
    let mut fail_count = 0_usize;

    push_check(
        &mut checks,
        &mut fail_count,
        "gate-policy-schema",
        policy.get("schema").and_then(Value::as_str) == Some(ARCHSIG_GATE_POLICY_V1_SCHEMA),
        "gate-policy schema must be archsig-gate-policy/v0.5.2",
    );
    let rules = policy.get("rules").and_then(Value::as_array);
    push_check(
        &mut checks,
        &mut fail_count,
        "gate-policy-rules-present",
        rules.is_some_and(|rules| !rules.is_empty()),
        "rules must be a non-empty array",
    );

    if let Some(rules) = rules {
        for (index, rule) in rules.iter().enumerate() {
            let scope = rule.get("scope").and_then(Value::as_str).unwrap_or("");
            push_check(
                &mut checks,
                &mut fail_count,
                &format!("gate-policy-rule-{index}-scope"),
                matches!(scope, "absolute" | "introduced-by-change"),
                "rule scope must be absolute or introduced-by-change",
            );
            match scope {
                "absolute" => validate_mapping(
                    &mut checks,
                    &mut fail_count,
                    index,
                    rule.get("verdictMapping"),
                    &ABSOLUTE_MAPPING_KEYS,
                    &NON_TERMINAL_KEYS,
                    "verdictMapping",
                ),
                "introduced-by-change" => validate_mapping(
                    &mut checks,
                    &mut fail_count,
                    index,
                    rule.get("introducedByChangeMapping"),
                    &INTRODUCED_MAPPING_KEYS,
                    &["removed", "other"],
                    "introducedByChangeMapping",
                ),
                _ => {}
            }
            if let Some(overrides) = rule.get("boundaryKindOverrides") {
                validate_boundary_overrides(&mut checks, &mut fail_count, index, overrides);
            }
        }
    }

    checks.push(json!({
        "id": "gate-policy-validation-summary",
        "result": if fail_count == 0 { "pass" } else { "fail" },
        "title": "Gate policy validation summary",
        "failedCheckCount": fail_count
    }));
    checks
}

pub fn build_gate_report_v1(
    packet_path: &Path,
    policy_path: &Path,
    comparison_path: Option<&Path>,
) -> Result<(Value, i32), Box<dyn Error>> {
    let packet: Value = read_json(packet_path)?;
    let policy: Value = read_json(policy_path)?;
    if packet.get("schema").and_then(Value::as_str) != Some(ARCHSIG_MEASUREMENT_PACKET_V1_SCHEMA) {
        let report = not_evaluable_report(
            packet_path,
            policy_path,
            comparison_path,
            "measurement packet schema mismatch",
        )?;
        return Ok((report, 2));
    }
    let packet_checks = validate_gate_packet_v1(&packet);
    if packet_checks.iter().any(|check| check["result"] == "fail") {
        let mut report = not_evaluable_report(
            packet_path,
            policy_path,
            comparison_path,
            "measurement packet validation failed",
        )?;
        report["packetValidation"] = Value::Array(packet_checks);
        return Ok((report, 2));
    }
    let policy_checks = validate_gate_policy_v1(&policy);
    if policy_checks.iter().any(|check| check["result"] == "fail") {
        let mut report = not_evaluable_report(
            packet_path,
            policy_path,
            comparison_path,
            "gate policy validation failed",
        )?;
        report["policyValidation"] = Value::Array(policy_checks);
        return Ok((report, 2));
    }
    let comparison_report = if let Some(comparison_path) = comparison_path {
        match read_json(comparison_path) {
            Ok(comparison) => {
                if comparison.get("schema").and_then(Value::as_str)
                    != Some(ARCHSIG_COMPARISON_REPORT_V1_SCHEMA)
                    || !comparison_report_shape_is_evaluable(&comparison)
                {
                    let report = not_evaluable_report(
                        packet_path,
                        policy_path,
                        Some(comparison_path),
                        "comparison report schema validation failed",
                    )?;
                    return Ok((report, 2));
                }
                let packet_digest = canonical_json_file_digest(packet_path)?;
                if comparison["inputDigests"]["headRun"]["measurementPacket"]["sha256"].as_str()
                    != Some(packet_digest.as_str())
                {
                    let report = not_evaluable_report(
                        packet_path,
                        policy_path,
                        Some(comparison_path),
                        "comparison report headRun measurement packet digest does not match --packet",
                    )?;
                    return Ok((report, 2));
                }
                Some(comparison)
            }
            Err(_) => {
                let report = not_evaluable_report(
                    packet_path,
                    policy_path,
                    Some(comparison_path),
                    "comparison report could not be read",
                )?;
                return Ok((report, 2));
            }
        }
    } else {
        None
    };

    let rules = policy["rules"]
        .as_array()
        .ok_or("validated gate policy unexpectedly has no rules")?;
    let verdict_rows = gate_verdict_rows(&packet);
    let boundary_statements = packet_boundary_statements_by_scope(&packet);
    let violated_assumptions = violated_assumption_ids(&packet);
    let mut rule_outcomes = Vec::new();
    let mut any_block = false;
    for rule in rules {
        let scope = rule["scope"].as_str().unwrap_or("");
        match scope {
            "absolute" => {
                let mapping = rule
                    .get("verdictMapping")
                    .and_then(Value::as_object)
                    .ok_or("absolute rule has no verdictMapping")?;
                let overrides = rule.get("boundaryKindOverrides").and_then(Value::as_object);
                let applied = verdict_rows
                    .iter()
                    .map(|row| {
                        let key = mapping_key_for_row(row, &violated_assumptions);
                        let (boundary_override, action) = if key == "violated_assumption_dependency"
                        {
                            any_block = true;
                            (None, "block".to_string())
                        } else {
                            let boundary_override =
                                override_action(row, &boundary_statements, overrides);
                            let action = boundary_override
                                .as_deref()
                                .or_else(|| mapping.get(&key).and_then(Value::as_str))
                                .unwrap_or("block")
                                .to_string();
                            (boundary_override, action)
                        };
                        if action == "block" {
                            any_block = true;
                        }
                        json!({
                            "rowRef": verdict_ref(row),
                            "verdict": row.get("verdict").cloned().unwrap_or(Value::Null),
                            "mappingKey": key,
                            "action": action,
                            "boundaryOverrideApplied": boundary_override.is_some()
                        })
                    })
                    .collect::<Vec<_>>();
                rule_outcomes.push(json!({
                    "ruleId": rule.get("ruleId").cloned().unwrap_or_else(|| json!("absolute")),
                    "scope": "absolute",
                    "status": "evaluated",
                    "appliedMapping": applied
                }));
            }
            "introduced-by-change" if comparison_report.is_some() => {
                let comparison = comparison_report
                    .as_ref()
                    .expect("comparison report was checked above");
                let mapping = rule
                    .get("introducedByChangeMapping")
                    .and_then(Value::as_object)
                    .ok_or("introduced-by-change rule has no introducedByChangeMapping")?;
                let applied = comparison["verdictTransitions"]
                    .as_array()
                    .into_iter()
                    .flatten()
                    .map(|transition| {
                        let key = transition["introducedByChangeCategory"]
                            .as_str()
                            .unwrap_or("other");
                        let action = mapping
                            .get(key)
                            .and_then(Value::as_str)
                            .unwrap_or("block")
                            .to_string();
                        if action == "block" {
                            any_block = true;
                        }
                        json!({
                            "rowKey": transition["rowKey"],
                            "baseRowRef": transition["baseRowRef"],
                            "headRowRef": transition["headRowRef"],
                            "transition": transition["transition"],
                            "mappingKey": key,
                            "action": action,
                            "deltaRefs": transition["deltaRefs"]
                        })
                    })
                    .collect::<Vec<_>>();
                rule_outcomes.push(json!({
                    "ruleId": rule.get("ruleId").cloned().unwrap_or_else(|| json!("introduced-by-change")),
                    "scope": "introduced-by-change",
                    "status": "evaluated",
                    "appliedMapping": applied
                }));
            }
            "introduced-by-change" => {
                rule_outcomes.push(json!({
                    "ruleId": rule.get("ruleId").cloned().unwrap_or_else(|| json!("introduced-by-change")),
                    "scope": "introduced-by-change",
                    "status": "not_applicable",
                    "reason": "comparison report was not supplied; introduced-by-change rules are skipped, not passed"
                }));
            }
            _ => {}
        }
    }

    let decision = if any_block {
        ARCHSIG_GATE_BLOCKED_BY_GATE_POLICY
    } else {
        ARCHSIG_GATE_PASS_WITHIN_GATE_POLICY
    };
    let exit_code = if any_block { 1 } else { 0 };
    let report = json!({
        "schema": ARCHSIG_GATE_REPORT_V1_SCHEMA,
        "decision": decision,
        "toolVersion": env!("CARGO_PKG_VERSION"),
        "inputDigests": {
            "measurementPacket": {
                "path": artifact_input_ref(packet_path),
                "sha256": canonical_json_file_digest(packet_path)?
            },
            "gatePolicy": {
                "path": artifact_input_ref(policy_path),
                "sha256": canonical_json_file_digest(policy_path)?
            },
            "comparisonReport": comparison_path.map(|path| json!({
                "path": artifact_input_ref(path),
                "sha256": canonical_json_file_digest(path).unwrap_or_default()
            })).unwrap_or(Value::Null)
        },
        "policyValidation": policy_checks,
        "ruleOutcomes": rule_outcomes,
        "nonConclusions": [
            "Gate report records institutional mapping from measurement verdicts to gate actions.",
            "Gate report does not change measurement verdicts or infer class transport.",
            "Introduced-by-change rules without a comparison report are not applicable, not pass."
        ]
    });
    Ok((report, exit_code))
}

fn validate_gate_packet_v1(packet: &Value) -> Vec<Value> {
    let mut checks = Vec::new();
    let mut fail_count = 0_usize;
    match serde_json::from_value::<ArchSigMeasurementPacketV1>(packet.clone()) {
        Ok(_) => {
            push_check(
                &mut checks,
                &mut fail_count,
                "gate-packet-typed-shape",
                true,
                "measurement packet parses as ArchSigMeasurementPacketV1",
            );
        }
        Err(error) => {
            push_check(
                &mut checks,
                &mut fail_count,
                "gate-packet-typed-shape",
                false,
                &format!("measurement packet shape is invalid: {error}"),
            );
            checks.push(json!({
                "id": "gate-packet-validation-summary",
                "result": "fail",
                "title": "Gate packet validation summary",
                "failedCheckCount": fail_count
            }));
            return checks;
        }
    }
    for check in validate_measurement_packet_value_v1(packet) {
        let passed = check.result != "fail";
        if !passed {
            fail_count += 1;
        }
        checks.push(serde_json::to_value(check).expect("validation check serializes"));
    }
    let rows = packet.get("structuralVerdict").and_then(Value::as_array);
    push_check(
        &mut checks,
        &mut fail_count,
        "gate-packet-profile-present",
        packet.get("profile").is_some(),
        "profile must be present",
    );
    push_check(
        &mut checks,
        &mut fail_count,
        "gate-packet-non-conclusions-present",
        packet
            .get("nonConclusions")
            .and_then(Value::as_array)
            .is_some(),
        "nonConclusions must be present",
    );
    push_check(
        &mut checks,
        &mut fail_count,
        "gate-packet-structural-verdict-present",
        rows.is_some(),
        "structuralVerdict must be an array",
    );
    if let Some(rows) = rows {
        push_check(
            &mut checks,
            &mut fail_count,
            "gate-packet-structural-verdict-nonempty",
            !rows.is_empty() || !supplemental_silence_rows(packet).is_empty(),
            "structuralVerdict must contain a row, or a typed silence row must be explicitly boundary-scoped for gate mapping",
        );
        for (index, row) in rows.iter().enumerate() {
            let verdict = row.get("verdict").and_then(Value::as_str);
            push_check(
                &mut checks,
                &mut fail_count,
                &format!("gate-packet-structural-verdict-{index}-verdict-vocabulary"),
                verdict.is_some_and(|verdict| STRUCTURAL_VERDICT_KEYS.contains(&verdict)),
                "structuralVerdict verdict must be one of the measurement packet verdict vocabulary values",
            );
            push_check(
                &mut checks,
                &mut fail_count,
                &format!("gate-packet-structural-verdict-{index}-verdict-data-present"),
                row.get("verdictData").is_some(),
                "structuralVerdict verdictData must be present",
            );
        }
    }
    checks.push(json!({
        "id": "gate-packet-validation-summary",
        "result": if fail_count == 0 { "pass" } else { "fail" },
        "title": "Gate packet validation summary",
        "failedCheckCount": fail_count
    }));
    checks
}

fn validate_mapping(
    checks: &mut Vec<Value>,
    fail_count: &mut usize,
    index: usize,
    mapping: Option<&Value>,
    required_keys: &[&str],
    no_plain_pass_keys: &[&str],
    field: &str,
) {
    let object = mapping.and_then(Value::as_object);
    push_check(
        checks,
        fail_count,
        &format!("gate-policy-rule-{index}-{field}-present"),
        object.is_some(),
        &format!("{field} must be an object"),
    );
    let Some(object) = object else {
        return;
    };
    for key in object.keys() {
        push_check(
            checks,
            fail_count,
            &format!("gate-policy-rule-{index}-{field}-{key}-known-key"),
            required_keys.contains(&key.as_str()),
            &format!("{field}.{key} is not in the closed mapping vocabulary"),
        );
    }
    for key in required_keys {
        let action = object.get(*key).and_then(Value::as_str);
        push_check(
            checks,
            fail_count,
            &format!("gate-policy-rule-{index}-{field}-{key}-present"),
            action.is_some(),
            &format!("{field}.{key} is required"),
        );
        push_check(
            checks,
            fail_count,
            &format!("gate-policy-rule-{index}-{field}-{key}-action"),
            action.is_some_and(|action| ACTIONS.contains(&action)),
            &format!("{field}.{key} must be pass, pass_with_boundary, or block"),
        );
    }
    for key in no_plain_pass_keys {
        push_check(
            checks,
            fail_count,
            &format!("gate-policy-rule-{index}-{field}-{key}-no-plain-pass"),
            object.get(*key).and_then(Value::as_str) != Some("pass"),
            &format!("{field}.{key} must not map to plain pass"),
        );
    }
    if field == "verdictMapping" && required_keys.contains(&"violated_assumption_dependency") {
        push_check(
            checks,
            fail_count,
            &format!("gate-policy-rule-{index}-{field}-violated_assumption_dependency-must-block"),
            object
                .get("violated_assumption_dependency")
                .and_then(Value::as_str)
                == Some("block"),
            "verdictMapping.violated_assumption_dependency must map to block",
        );
    }
}

fn validate_boundary_overrides(
    checks: &mut Vec<Value>,
    fail_count: &mut usize,
    index: usize,
    overrides: &Value,
) {
    let object = overrides.as_object();
    push_check(
        checks,
        fail_count,
        &format!("gate-policy-rule-{index}-boundary-overrides-object"),
        object.is_some(),
        "boundaryKindOverrides must be an object",
    );
    let Some(object) = object else {
        return;
    };
    for (kind, action) in object {
        push_check(
            checks,
            fail_count,
            &format!("gate-policy-rule-{index}-boundary-override-{kind}-known-key"),
            BOUNDARY_OVERRIDE_KEYS.contains(&kind.as_str()),
            "boundaryKindOverrides key must be a known boundary statement kind",
        );
        let action = action.as_str();
        push_check(
            checks,
            fail_count,
            &format!("gate-policy-rule-{index}-boundary-override-{kind}-action"),
            action.is_some_and(|action| matches!(action, "pass_with_boundary" | "block")),
            "boundaryKindOverrides may only map to pass_with_boundary or block",
        );
    }
}

fn comparison_report_shape_is_evaluable(comparison: &Value) -> bool {
    if comparison
        .get("conclusionCode")
        .and_then(Value::as_str)
        .is_none()
    {
        return false;
    }
    let Some(level) = comparison
        .get("comparability")
        .and_then(|comparability| comparability.get("level"))
        .and_then(Value::as_str)
    else {
        return false;
    };
    if !COMPARISON_LEVELS.contains(&level) {
        return false;
    }
    let Some(input_digests) = comparison.get("inputDigests") else {
        return false;
    };
    for run_key in ["baseRun", "headRun"] {
        let run = &input_digests[run_key];
        let required = [
            run["runId"].as_str(),
            run["toolVersion"].as_str(),
            run["archmap"]["sha256"].as_str(),
            run["lawPolicy"]["sha256"].as_str(),
            run["profileFingerprint"]["sha256"].as_str(),
            run["siteCoverDigest"]["sha256"].as_str(),
            run["measurementPacket"]["sha256"].as_str(),
        ];
        if required.iter().any(|value| value.is_none_or(str::is_empty)) {
            return false;
        }
    }
    if comparison["inputDigests"]["headRun"]["measurementPacket"]["sha256"]
        .as_str()
        .is_none_or(str::is_empty)
    {
        return false;
    }
    let Some(transitions) = comparison
        .get("verdictTransitions")
        .and_then(Value::as_array)
    else {
        return false;
    };
    if transitions.is_empty() {
        return false;
    }
    transitions.iter().all(|transition| {
        let category = transition["introducedByChangeCategory"].as_str();
        let transition_name = transition["transition"].as_str();
        let refs_present = transition.get("baseRowRef").is_some()
            && transition.get("headRowRef").is_some()
            && transition["rowKey"]
                .as_str()
                .is_some_and(|row| !row.is_empty());
        category.is_some_and(|category| INTRODUCED_MAPPING_KEYS.contains(&category))
            && transition_name.is_some_and(|transition_name| {
                COMPARISON_TRANSITIONS.contains(&transition_name)
                    || transition_name == COMPARISON_OTHER_TRANSITION
            })
            && refs_present
    })
}

fn push_check(
    checks: &mut Vec<Value>,
    fail_count: &mut usize,
    id: &str,
    passed: bool,
    reason: &str,
) {
    if !passed {
        *fail_count += 1;
    }
    checks.push(json!({
        "id": id,
        "result": if passed { "pass" } else { "fail" },
        "reason": reason
    }));
}

fn structural_verdict_rows(packet: &Value) -> Vec<Value> {
    packet["structuralVerdict"]
        .as_array()
        .into_iter()
        .flatten()
        .cloned()
        .collect()
}

fn analytic_silence_rows(packet: &Value) -> Vec<Value> {
    let boundaries_by_scope = packet_boundary_statements_by_scope(packet);
    packet["analyticReadings"]
        .as_array()
        .into_iter()
        .flatten()
        .filter_map(|reading| {
            let reading_id = reading["readingId"].as_str()?;
            let has_silence_boundary = boundaries_by_scope
                .get(reading_id)
                .into_iter()
                .flatten()
                .any(|kind| kind == "silence_by_design");
            has_silence_boundary.then(|| {
                json!({
                    "verdictRef": reading_id,
                    "evaluator": reading["evaluator"],
                    "law": reading["evaluator"],
                    "verdict": "not_computed",
                    "verdictData": {
                        "inScope": true,
                        "zero": false,
                        "nonZero": false,
                        "methodStatus": "analytic_reading_silence_by_design"
                    },
                    "dependsOnAssumptions": []
                })
            })
        })
        .collect()
}

fn comparison_silence_rows(packet: &Value) -> Vec<Value> {
    let boundaries_by_scope = packet_boundary_statements_by_scope(packet);
    packet["computedInvariants"]
        .as_array()
        .into_iter()
        .flatten()
        .filter_map(|invariant| {
            if invariant["evaluator"] != "ag.saga-comparison"
                || invariant["status"] != "silence_by_design"
            {
                return None;
            }
            let invariant_id = invariant["invariantId"].as_str()?;
            let has_silence_boundary = boundaries_by_scope
                .get(invariant_id)
                .into_iter()
                .flatten()
                .any(|kind| kind == "silence_by_design");
            has_silence_boundary.then(|| {
                json!({
                    "verdictRef": invariant_id,
                    "evaluator": invariant["evaluator"],
                    "law": invariant["evaluator"],
                    "verdict": "not_computed",
                    "verdictData": {
                        "inScope": true,
                        "zero": false,
                        "nonZero": false,
                        "methodStatus": invariant["reason"]
                    },
                    "dependsOnAssumptions": []
                })
            })
        })
        .collect()
}

fn supplemental_silence_rows(packet: &Value) -> Vec<Value> {
    let structural = structural_verdict_rows(packet);
    let mut rows = if structural.is_empty() {
        analytic_silence_rows(packet)
    } else {
        Vec::new()
    };
    if !structural.is_empty() || !rows.is_empty() {
        rows.extend(comparison_silence_rows(packet));
    }
    rows
}

fn gate_verdict_rows(packet: &Value) -> Vec<Value> {
    let structural = structural_verdict_rows(packet);
    let mut rows = structural;
    rows.extend(supplemental_silence_rows(packet));
    rows
}

fn violated_assumption_ids(packet: &Value) -> BTreeSet<String> {
    packet["assumptions"]
        .as_array()
        .into_iter()
        .flatten()
        .filter(|assumption| assumption["status"].as_str() == Some("violated"))
        .filter_map(|assumption| assumption["assumptionId"].as_str().map(str::to_string))
        .collect()
}

fn mapping_key_for_row(row: &Value, violated_assumptions: &BTreeSet<String>) -> String {
    let depends_on_violated = row["dependsOnAssumptions"]
        .as_array()
        .into_iter()
        .flatten()
        .filter_map(Value::as_str)
        .any(|reference| violated_assumptions.contains(reference));
    if depends_on_violated {
        "violated_assumption_dependency".to_string()
    } else {
        row["verdict"].as_str().unwrap_or("unknown").to_string()
    }
}

fn packet_boundary_statements_by_scope(packet: &Value) -> BTreeMap<String, Vec<String>> {
    let mut by_scope = BTreeMap::<String, Vec<String>>::new();
    for boundary in packet["boundaryStatements"]
        .as_array()
        .into_iter()
        .flatten()
    {
        let Some(kind) = boundary["kind"].as_str() else {
            continue;
        };
        for scope in boundary["scopeRefs"].as_array().into_iter().flatten() {
            let Some(scope) = scope.as_str() else {
                continue;
            };
            by_scope
                .entry(scope.to_string())
                .or_default()
                .push(kind.to_string());
        }
    }
    by_scope
}

fn override_action(
    row: &Value,
    boundaries_by_scope: &BTreeMap<String, Vec<String>>,
    overrides: Option<&Map<String, Value>>,
) -> Option<String> {
    // Square-free generator-level silence may qualify an all-unobserved
    // measured_zero row, but it must never turn a mixed measured_nonzero row
    // into pass_with_boundary. Other evaluator-specific boundary overrides
    // retain their existing policy semantics.
    if row["evaluator"].as_str() == Some("ag.square-free-repair")
        && row["verdict"].as_str() != Some("measured_zero")
    {
        return None;
    }
    let overrides = overrides?;
    let row_ref = verdict_ref_string(row);
    boundaries_by_scope
        .get(&row_ref)
        .into_iter()
        .flatten()
        .map(String::as_str)
        .find_map(|kind| {
            overrides
                .get(kind)
                .and_then(Value::as_str)
                .map(str::to_string)
        })
}

fn verdict_ref(row: &Value) -> Value {
    json!(verdict_ref_string(row))
}

fn verdict_ref_string(row: &Value) -> String {
    row["verdictRef"]
        .as_str()
        .or_else(|| row["structuralVerdictRef"].as_str())
        .map(str::to_string)
        .unwrap_or_else(|| {
            format!(
                "structuralVerdict/{}/{}/{}",
                gate_ref_segment(row["evaluator"].as_str().unwrap_or("unknown-evaluator")),
                gate_ref_segment(row["law"].as_str().unwrap_or("unknown-law")),
                gate_ref_segment(
                    row["verdictData"]["methodStatus"]
                        .as_str()
                        .or_else(|| row["methodStatus"].as_str())
                        .unwrap_or("unknown-status")
                )
            )
        })
}

fn gate_ref_segment(value: &str) -> String {
    value
        .chars()
        .map(|ch| if ch.is_ascii_alphanumeric() { ch } else { '-' })
        .collect()
}

fn not_evaluable_report(
    packet_path: &Path,
    policy_path: &Path,
    comparison_path: Option<&Path>,
    reason: &str,
) -> Result<Value, Box<dyn Error>> {
    Ok(json!({
        "schema": ARCHSIG_GATE_REPORT_V1_SCHEMA,
        "decision": ARCHSIG_GATE_NOT_EVALUABLE,
        "toolVersion": env!("CARGO_PKG_VERSION"),
        "inputDigests": {
            "measurementPacket": {
                "path": artifact_input_ref(packet_path),
                "sha256": canonical_json_file_digest(packet_path).unwrap_or_default()
            },
            "gatePolicy": {
                "path": artifact_input_ref(policy_path),
                "sha256": canonical_json_file_digest(policy_path).unwrap_or_default()
            },
            "comparisonReport": comparison_path.map(|path| json!({
                "path": artifact_input_ref(path),
                "sha256": canonical_json_file_digest(path).unwrap_or_default()
            })).unwrap_or(Value::Null)
        },
        "reason": reason,
        "ruleOutcomes": [],
        "nonConclusions": [
            "Not evaluable is neither pass nor block.",
            "No measurement verdict was rounded into a gate decision."
        ]
    }))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn analytic_silence_is_fallback_only_while_comparison_silence_is_supplemental() {
        let packet = json!({
            "structuralVerdict": [{
                "verdictRef": "structural:law",
                "evaluator": "ag.structural",
                "law": "law:structural",
                "verdict": "measured_zero",
                "verdictData": {},
                "dependsOnAssumptions": []
            }],
            "analyticReadings": [{
                "readingId": "analytic:cost-model",
                "evaluator": "ag.harmonic-debt"
            }],
            "computedInvariants": [{
                "invariantId": "saga-comparison:h1-transfer",
                "evaluator": "ag.saga-comparison",
                "status": "silence_by_design",
                "reason": "comparison_data_not_supplied"
            }],
            "boundaryStatements": [
                {
                    "kind": "silence_by_design",
                    "scopeRefs": ["analytic:cost-model"]
                },
                {
                    "kind": "silence_by_design",
                    "scopeRefs": ["saga-comparison:h1-transfer"]
                }
            ]
        });

        let rows = gate_verdict_rows(&packet);
        assert!(rows.iter().any(|row| row["verdictRef"] == "structural:law"));
        assert!(
            rows.iter()
                .any(|row| row["verdictRef"] == "saga-comparison:h1-transfer")
        );
        assert!(
            !rows
                .iter()
                .any(|row| row["verdictRef"] == "analytic:cost-model")
        );

        let mut fallback_packet = packet;
        fallback_packet["structuralVerdict"] = json!([]);
        let fallback_rows = gate_verdict_rows(&fallback_packet);
        assert!(
            fallback_rows
                .iter()
                .any(|row| row["verdictRef"] == "analytic:cost-model")
        );

        let mut comparison_only_packet = fallback_packet;
        comparison_only_packet["analyticReadings"] = json!([]);
        let comparison_only_rows = gate_verdict_rows(&comparison_only_packet);
        assert!(comparison_only_rows.is_empty());
    }
}

fn artifact_input_ref(path: &Path) -> String {
    path.file_name()
        .and_then(|name| name.to_str())
        .map(|name| format!("input:{name}"))
        .unwrap_or_else(|| "input:unnamed-json".to_string())
}

fn read_json(path: &Path) -> Result<Value, Box<dyn Error>> {
    let text = std::fs::read_to_string(path)?;
    let mut deserializer = serde_json::Deserializer::from_str(&text);
    serde::de::Deserializer::deserialize_any(&mut deserializer, StrictValueVisitor)?;
    Ok(serde_json::from_str(&text)?)
}

struct StrictValueSeed;

impl<'de> serde::de::DeserializeSeed<'de> for StrictValueSeed {
    type Value = ();

    fn deserialize<D>(self, deserializer: D) -> Result<Self::Value, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        deserializer.deserialize_any(StrictValueVisitor)
    }
}

struct StrictValueVisitor;

impl<'de> serde::de::Visitor<'de> for StrictValueVisitor {
    type Value = ();

    fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str("a JSON value without duplicate object keys")
    }

    fn visit_bool<E>(self, _: bool) -> Result<Self::Value, E> {
        Ok(())
    }

    fn visit_i64<E>(self, _: i64) -> Result<Self::Value, E> {
        Ok(())
    }

    fn visit_u64<E>(self, _: u64) -> Result<Self::Value, E> {
        Ok(())
    }

    fn visit_f64<E>(self, _: f64) -> Result<Self::Value, E> {
        Ok(())
    }

    fn visit_str<E>(self, _: &str) -> Result<Self::Value, E> {
        Ok(())
    }

    fn visit_string<E>(self, _: String) -> Result<Self::Value, E> {
        Ok(())
    }

    fn visit_none<E>(self) -> Result<Self::Value, E> {
        Ok(())
    }

    fn visit_unit<E>(self) -> Result<Self::Value, E> {
        Ok(())
    }

    fn visit_some<D>(self, deserializer: D) -> Result<Self::Value, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        deserializer.deserialize_any(StrictValueVisitor)
    }

    fn visit_seq<A>(self, mut sequence: A) -> Result<Self::Value, A::Error>
    where
        A: serde::de::SeqAccess<'de>,
    {
        while sequence.next_element_seed(StrictValueSeed)?.is_some() {}
        Ok(())
    }

    fn visit_map<A>(self, mut map: A) -> Result<Self::Value, A::Error>
    where
        A: serde::de::MapAccess<'de>,
    {
        let mut keys = BTreeSet::new();
        while let Some(key) = map.next_key::<String>()? {
            if !keys.insert(key.clone()) {
                return Err(serde::de::Error::custom(format!(
                    "duplicate JSON object key: {key}"
                )));
            }
            map.next_value_seed(StrictValueSeed)?;
        }
        Ok(())
    }
}

fn canonical_json_file_digest(path: &Path) -> Result<String, Box<dyn Error>> {
    let value: Value = read_json(path)?;
    Ok(sha256_hex(&canonical_json_bytes(&value)?))
}

fn canonical_json_bytes(value: &Value) -> Result<Vec<u8>, Box<dyn Error>> {
    Ok(serde_json::to_vec(&canonical_json_value(value))?)
}

fn canonical_json_value(value: &Value) -> Value {
    match value {
        Value::Array(items) => Value::Array(items.iter().map(canonical_json_value).collect()),
        Value::Object(object) => {
            let sorted = object
                .iter()
                .map(|(key, value)| (key.clone(), canonical_json_value(value)))
                .collect::<BTreeMap<_, _>>();
            let mut map = Map::new();
            for (key, value) in sorted {
                map.insert(key, value);
            }
            Value::Object(map)
        }
        _ => value.clone(),
    }
}

fn sha256_hex(bytes: &[u8]) -> String {
    let digest = Sha256::digest(bytes);
    let mut output = String::with_capacity(digest.len() * 2);
    for byte in digest {
        output.push_str(&format!("{byte:02x}"));
    }
    output
}
