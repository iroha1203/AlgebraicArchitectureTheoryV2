//! `archsig inspect --result DIR [--answer ID] [--evidence]`:
//! 保存済み `result.json` から指定回答の結論・反例・詳細・ソース位置を抽出する（Observed `nodes` 参照も自動解決）。

use super::{CommandOutput, input_status, stopped};
use crate::cli::{InspectResultArgs, emit_progress};
use crate::platform::read_reuse_result_nofollow;
use crate::run::{Signals, output};
use archsig_common::canonical::{Json, JsonObject};
use archsig_common::control::{Checkpoint, Control};
use archsig_common::issue::{Code, Details, Issue, Location};
use archsig_common::json::{JNode, JValue, parse_with_max_depth};
use archsig_common::limits::DEFAULT_MAX_JSON_DEPTH;
use archsig_input::result::ResultIssue;
use std::collections::{BTreeMap, BTreeSet};

pub fn execute(
    args: &InspectResultArgs,
    max_file_bytes: u64,
    signals: &mut dyn Signals,
    control: &Control,
) -> Result<CommandOutput, crate::run::Outcome> {
    emit_progress(&format!(
        "inspect: reading saved result from {}",
        args.result_dir.display()
    ));
    let bytes = read_reuse_result_nofollow(&args.result_dir, max_file_bytes).map_err(|err| {
        output::without_result(
            signals,
            archsig_input::result::Status::Error,
            vec![ResultIssue::Io {
                operation: "read",
                path: args
                    .result_dir
                    .join("result.json")
                    .to_string_lossy()
                    .into_owned(),
                message: format!("cannot read result.json: {err}"),
            }],
        )
    })?;

    if let Err(sig) = control.checkpoint(Checkpoint::Work) {
        return Err(stopped(signals, sig));
    }

    let root = parse_with_max_depth(&bytes, DEFAULT_MAX_JSON_DEPTH).map_err(|issue| {
        let (status, code) = input_status(issue.code);
        output::notify(
            signals,
            status,
            code,
            control.stop_reason(),
            vec![ResultIssue::Input(*issue).wire()],
        )
    })?;

    let Some(source_format) = obj_field(&root, "format").and_then(as_str) else {
        return Err(schema_error(
            signals,
            control,
            "saved result.json must be a JSON object with a string `format` field",
        ));
    };

    let nodes = collect_node_index(&root);

    let answers_arr = obj_field(&root, "answers")
        .and_then(|n| match &n.value {
            JValue::Arr(items) => Some(items.as_slice()),
            _ => None,
        })
        .unwrap_or(&[]);

    if !args.answers.is_empty() {
        let available: Vec<&str> = answers_arr
            .iter()
            .filter_map(|a| obj_field(a, "id").and_then(as_str))
            .collect();
        for requested in &args.answers {
            if !available.iter().any(|id| id == requested) {
                return Err(output::notify(
                    signals,
                    archsig_input::result::Status::Invalid,
                    65,
                    control.stop_reason(),
                    vec![
                        ResultIssue::Input(Issue {
                            code: Code::Reference,
                            message: format!(
                                "answer `{requested}` not found in saved result (available: [{}])",
                                available.join(", ")
                            ),
                            location: Location::ArchMap {
                                pointer: "/answers".to_owned(),
                                span: None,
                            },
                            details: Details::Empty,
                        })
                        .wire(),
                    ],
                ));
            }
        }
    }

    let selected: Vec<&JNode> = if args.answers.is_empty() {
        answers_arr.iter().collect()
    } else {
        let filter: BTreeSet<&str> = args.answers.iter().map(String::as_str).collect();
        answers_arr
            .iter()
            .filter(|a| {
                obj_field(a, "id")
                    .and_then(as_str)
                    .is_some_and(|id| filter.contains(id))
            })
            .collect()
    };

    let extracted_answers: Vec<Json> = selected
        .into_iter()
        .map(|ans| extract_answer(ans, &nodes, args.evidence))
        .collect();

    let mut out_obj = JsonObject::from([
        ("format".into(), Json::str("archsig.inspect-result/1")),
        ("source_format".into(), Json::str(source_format)),
        (
            "status".into(),
            Json::str(
                obj_field(&root, "status")
                    .and_then(as_str)
                    .unwrap_or("unknown"),
            ),
        ),
        (
            "exit_code".into(),
            obj_field(&root, "exit_code")
                .map(jnode_to_json)
                .unwrap_or_else(|| Json::Nat(0)),
        ),
        ("answers".into(), Json::Arr(extracted_answers)),
    ]);

    if let Some(issues) = obj_field(&root, "issues") {
        out_obj.insert("issues".into(), jnode_to_json(issues));
    }
    if let Some(warnings) = obj_field(&root, "warnings") {
        out_obj.insert("warnings".into(), jnode_to_json(warnings));
    }
    if args.evidence
        && let Some(inputs) = obj_field(&root, "inputs")
    {
        out_obj.insert("inputs".into(), jnode_to_json(inputs));
    }

    Ok(CommandOutput {
        json: Json::Obj(out_obj),
        exit_code: 0,
    })
}

fn schema_error(
    signals: &mut dyn Signals,
    control: &Control,
    message: &str,
) -> crate::run::Outcome {
    output::notify(
        signals,
        archsig_input::result::Status::Invalid,
        65,
        control.stop_reason(),
        vec![
            ResultIssue::Input(Issue {
                code: Code::Syntax,
                message: message.to_owned(),
                location: Location::ArchMap {
                    pointer: "/format".to_owned(),
                    span: None,
                },
                details: Details::Empty,
            })
            .wire(),
        ],
    )
}

fn collect_node_index(root: &JNode) -> BTreeMap<String, &JNode> {
    let mut index = BTreeMap::new();
    if let Some(JValue::Arr(items)) = obj_field(root, "nodes").map(|n| &n.value) {
        for item in items {
            if let Some(id) = obj_field(item, "id").and_then(as_str) {
                index.insert(id.to_owned(), item);
            }
        }
    }
    index
}

fn obj_field<'a>(node: &'a JNode, key: &str) -> Option<&'a JNode> {
    let JValue::Obj(entries) = &node.value else {
        return None;
    };
    entries.iter().find(|(k, _)| k == key).map(|(_, v)| v)
}

fn as_str(node: &JNode) -> Option<&str> {
    match &node.value {
        JValue::Str(s) => Some(s.as_str()),
        _ => None,
    }
}

fn exact_node_ref(node: &JNode) -> Option<&str> {
    let JValue::Obj(entries) = &node.value else {
        return None;
    };
    if entries.len() != 1 || entries[0].0 != "node" {
        return None;
    }
    as_str(&entries[0].1)
}

fn jnode_to_json(node: &JNode) -> Json {
    stacker::maybe_grow(64 * 1024, 1024 * 1024, || match &node.value {
        JValue::Null => Json::str("null"),
        JValue::Bool(b) => Json::Bool(*b),
        JValue::Num(n) => n
            .parse::<u64>()
            .map(Json::Nat)
            .unwrap_or_else(|_| Json::str(n)),
        JValue::Str(s) => Json::str(s),
        JValue::Arr(items) => Json::Arr(items.iter().map(jnode_to_json).collect()),
        JValue::Obj(entries) => Json::Obj(
            entries
                .iter()
                .map(|(k, v)| (k.clone(), jnode_to_json(v)))
                .collect(),
        ),
    })
}

fn resolve_node_refs(
    node: &JNode,
    nodes: &BTreeMap<String, &JNode>,
    visited: &mut BTreeSet<String>,
    depth: usize,
) -> Json {
    const MAX_RESOLVE_DEPTH: usize = 32;
    stacker::maybe_grow(64 * 1024, 1024 * 1024, || {
        if depth < MAX_RESOLVE_DEPTH
            && let Some(node_id) = exact_node_ref(node)
            && !visited.contains(node_id)
            && let Some(&target) = nodes.get(node_id)
        {
            visited.insert(node_id.to_owned());
            let mut resolved = resolve_node_refs(target, nodes, visited, depth + 1);
            visited.remove(node_id);
            if let Json::Obj(ref mut map) = resolved {
                map.insert("node_id".into(), Json::str(node_id));
                return resolved;
            }
            return Json::obj([("node_id", Json::str(node_id)), ("resolved", resolved)]);
        }
        match &node.value {
            JValue::Arr(items) => Json::Arr(
                items
                    .iter()
                    .map(|item| resolve_node_refs(item, nodes, visited, depth + 1))
                    .collect(),
            ),
            JValue::Obj(entries) => Json::Obj(
                entries
                    .iter()
                    .map(|(k, v)| (k.clone(), resolve_node_refs(v, nodes, visited, depth + 1)))
                    .collect(),
            ),
            _ => jnode_to_json(node),
        }
    })
}

fn extract_answer(ans: &JNode, nodes: &BTreeMap<String, &JNode>, include_evidence: bool) -> Json {
    let mut visited = BTreeSet::new();
    let resolved_outputs = obj_field(ans, "outputs")
        .map(|o| resolve_node_refs(o, nodes, &mut visited, 0))
        .unwrap_or_else(|| Json::Obj(JsonObject::new()));
    let resolved_claim =
        obj_field(ans, "claim").map(|c| resolve_node_refs(c, nodes, &mut visited, 0));
    let resolved_ans_evidence =
        obj_field(ans, "evidence").map(|e| resolve_node_refs(e, nodes, &mut visited, 0));
    let resolved_ans_counterexamples =
        obj_field(ans, "counterexamples").map(|c| resolve_node_refs(c, nodes, &mut visited, 0));

    let id = obj_field(ans, "id").and_then(as_str).unwrap_or("");
    let status = obj_field(ans, "status").and_then(as_str).unwrap_or("");

    let mut counterexamples = Vec::new();
    let mut repairs = Vec::new();
    let mut missing = Vec::new();
    let mut origins = Vec::new();
    let mut locations = Vec::new();
    if let Some(cx) = &resolved_ans_counterexamples {
        push_array_or_single(cx, &mut counterexamples);
        collect_highlights(
            cx,
            &mut counterexamples,
            &mut repairs,
            &mut missing,
            &mut origins,
            &mut locations,
        );
    }
    collect_highlights(
        &resolved_outputs,
        &mut counterexamples,
        &mut repairs,
        &mut missing,
        &mut origins,
        &mut locations,
    );
    if let Some(claim) = &resolved_claim {
        collect_highlights(
            claim,
            &mut counterexamples,
            &mut repairs,
            &mut missing,
            &mut origins,
            &mut locations,
        );
    }
    if let Some(ev) = &resolved_ans_evidence {
        collect_highlights(
            ev,
            &mut counterexamples,
            &mut repairs,
            &mut missing,
            &mut origins,
            &mut locations,
        );
    }

    if let Some(reasons) = obj_field(ans, "reasons") {
        let resolved_reasons = jnode_to_json(reasons);
        collect_highlights(
            &resolved_reasons,
            &mut counterexamples,
            &mut repairs,
            &mut missing,
            &mut origins,
            &mut locations,
        );
    }

    let conclusion = if include_evidence {
        resolved_outputs.clone()
    } else {
        trim_heavy_evidence(&resolved_outputs)
    };

    let mut out = JsonObject::from([
        ("id".into(), Json::str(id)),
        ("status".into(), Json::str(status)),
        ("conclusion".into(), conclusion),
        ("counterexamples".into(), Json::Arr(counterexamples)),
        ("repairs".into(), Json::Arr(repairs)),
        ("missing".into(), Json::Arr(missing)),
        ("origins".into(), Json::Arr(origins)),
        ("locations".into(), Json::Arr(locations)),
    ]);

    if let Some(claim) = resolved_claim {
        let trimmed_claim = if include_evidence {
            claim
        } else {
            trim_heavy_evidence(&claim)
        };
        out.insert("claim".into(), trimmed_claim);
    }

    if let Some(reasons) = obj_field(ans, "reasons") {
        out.insert("reasons".into(), jnode_to_json(reasons));
    }
    if include_evidence {
        let evidence_val = match resolved_ans_evidence {
            Some(ev) => Json::obj([("outputs", resolved_outputs), ("nodes", ev)]),
            None => resolved_outputs,
        };
        out.insert("evidence".into(), evidence_val);
        if let Some(scope) = obj_field(ans, "scope") {
            out.insert("scope".into(), jnode_to_json(scope));
        }
    }
    Json::Obj(out)
}

fn collect_highlights(
    val: &Json,
    counterexamples: &mut Vec<Json>,
    repairs: &mut Vec<Json>,
    missing: &mut Vec<Json>,
    origins: &mut Vec<Json>,
    locations: &mut Vec<Json>,
) {
    stacker::maybe_grow(64 * 1024, 1024 * 1024, || match val {
        Json::Arr(items) => {
            for item in items {
                collect_highlights(item, counterexamples, repairs, missing, origins, locations);
            }
        }
        Json::Obj(entries) => {
            for (k, v) in entries {
                match k.as_str() {
                    "counterexamples" | "contradictions" | "minimal_conflict_sets" => {
                        push_array_or_single(v, counterexamples);
                    }
                    "repairs" | "restored" | "minimal_origin_supports" => {
                        push_nonempty(v, repairs);
                    }
                    "missing" | "missing_slots" => push_array_or_single(v, missing),
                    "origins" => push_array_or_single(v, origins),
                    "origin" => push_unique(v, origins),
                    "source_locations" | "locations" => push_array_or_single(v, locations),
                    "location" | "pointer" => push_unique(v, locations),
                    _ => {
                        collect_highlights(v, counterexamples, repairs, missing, origins, locations)
                    }
                }
            }
        }
        _ => {}
    });
}

fn push_array_or_single(v: &Json, target: &mut Vec<Json>) {
    match v {
        Json::Arr(items) => {
            for item in items {
                push_unique(item, target);
            }
        }
        other => push_unique(other, target),
    }
}

fn push_nonempty(v: &Json, target: &mut Vec<Json>) {
    match v {
        Json::Arr(items) if items.is_empty() => {}
        Json::Obj(map) if map.is_empty() => {}
        other => push_unique(other, target),
    }
}

fn push_unique(v: &Json, target: &mut Vec<Json>) {
    if !target.iter().any(|existing| existing == v) {
        target.push(v.clone());
    }
}

fn trim_heavy_evidence(val: &Json) -> Json {
    const HEAVY_KEYS: &[&str] = &[
        "residual_ideal",
        "cofactors",
        "syzygy_generators",
        "provenance",
        "conditions",
        "evaluated_inputs",
    ];
    stacker::maybe_grow(64 * 1024, 1024 * 1024, || match val {
        Json::Arr(items) => Json::Arr(items.iter().map(trim_heavy_evidence).collect()),
        Json::Obj(entries) => {
            let mut out = JsonObject::new();
            for (k, v) in entries {
                if HEAVY_KEYS.contains(&k.as_str()) || k.ends_with("_verified") {
                    continue;
                }
                if k == "applicability"
                    && let Json::Arr(items) = v
                {
                    let failed: Vec<Json> = items
                        .iter()
                        .filter(|item| {
                            !matches!(
                                item,
                                Json::Obj(fields)
                                    if fields.get("satisfied") == Some(&Json::Bool(true))
                            )
                        })
                        .map(trim_heavy_evidence)
                        .collect();
                    if !failed.is_empty() {
                        out.insert(k.clone(), Json::Arr(failed));
                    }
                    continue;
                }
                out.insert(k.clone(), trim_heavy_evidence(v));
            }
            Json::Obj(out)
        }
        other => other.clone(),
    })
}
