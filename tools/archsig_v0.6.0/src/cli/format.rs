//! CLI 出力整形（`--format json|pretty|human`）。

use super::OutputFormat;
use crate::run::Outcome;
use archsig_common::canonical::Json;
use archsig_common::json::{JNode, JValue, parse_with_max_depth};
use archsig_common::limits::DEFAULT_MAX_JSON_DEPTH;
use std::fmt::Write as _;

/// `Outcome` を指定された `--format` 文字列へ整形する。
pub fn render_outcome(outcome: &Outcome, format: OutputFormat) -> String {
    match format {
        OutputFormat::Json => outcome.receipt(),
        OutputFormat::Pretty => render_raw_json_str(&outcome.receipt(), OutputFormat::Pretty),
        OutputFormat::Human => render_human_jnode(&parse_or_fallback(&outcome.receipt())),
    }
}

/// 任意の `Json` 値（`digest`, `inspect`, `inspect --result` 等）を指定フォーマットで整形する。
pub fn render_json_value(json: &Json, format: OutputFormat) -> String {
    match format {
        OutputFormat::Json => json.canonical(),
        OutputFormat::Pretty => json.pretty(),
        OutputFormat::Human => render_human_jnode(&parse_or_fallback(&json.canonical())),
    }
}

/// 既存の JSON 文字列出力（`version`, `evidence`, `law-fibers`）を指定フォーマットで整形する。
pub fn render_raw_json_str(raw: &str, format: OutputFormat) -> String {
    match format {
        OutputFormat::Json => raw.to_owned(),
        OutputFormat::Pretty => {
            match parse_with_max_depth(raw.as_bytes(), DEFAULT_MAX_JSON_DEPTH) {
                Ok(node) => pretty_jnode(&node),
                Err(_) => raw.to_owned(),
            }
        }
        OutputFormat::Human => match parse_with_max_depth(raw.as_bytes(), DEFAULT_MAX_JSON_DEPTH) {
            Ok(node) => render_human_jnode(&node),
            Err(_) => raw.to_owned(),
        },
    }
}

fn parse_or_fallback(raw: &str) -> JNode {
    parse_with_max_depth(raw.as_bytes(), DEFAULT_MAX_JSON_DEPTH).unwrap_or_else(|_| JNode {
        value: JValue::Str(raw.to_owned()),
    })
}

/// `JNode` を元の key 順と数値表現を保ったまま 2 スペース字下げ JSON へ整形する。
pub fn pretty_jnode(node: &JNode) -> String {
    fn write_indent(out: &mut String, depth: usize) {
        for _ in 0..depth {
            out.push_str("  ");
        }
    }
    fn write_node(node: &JNode, depth: usize, out: &mut String) {
        stacker::maybe_grow(64 * 1024, 1024 * 1024, || match &node.value {
            JValue::Null => out.push_str("null"),
            JValue::Bool(b) => out.push_str(if *b { "true" } else { "false" }),
            JValue::Num(n) => out.push_str(n),
            JValue::Str(s) => out.push_str(&Json::str(s).canonical()),
            JValue::Arr(items) => {
                if items.is_empty() {
                    out.push_str("[]");
                } else {
                    out.push_str("[\n");
                    for (idx, item) in items.iter().enumerate() {
                        if idx > 0 {
                            out.push_str(",\n");
                        }
                        write_indent(out, depth + 1);
                        write_node(item, depth + 1, out);
                    }
                    out.push('\n');
                    write_indent(out, depth);
                    out.push(']');
                }
            }
            JValue::Obj(entries) => {
                if entries.is_empty() {
                    out.push_str("{}");
                } else {
                    out.push_str("{\n");
                    for (idx, (k, v)) in entries.iter().enumerate() {
                        if idx > 0 {
                            out.push_str(",\n");
                        }
                        write_indent(out, depth + 1);
                        out.push_str(&Json::str(k).canonical());
                        out.push_str(": ");
                        write_node(v, depth + 1, out);
                    }
                    out.push('\n');
                    write_indent(out, depth);
                    out.push('}');
                }
            }
        });
    }
    let mut out = String::new();
    write_node(node, 0, &mut out);
    out
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

fn as_arr(node: &JNode) -> Option<&[JNode]> {
    match &node.value {
        JValue::Arr(items) => Some(items.as_slice()),
        _ => None,
    }
}

fn scalar_text(node: &JNode) -> String {
    match &node.value {
        JValue::Null => "null".to_owned(),
        JValue::Bool(b) => b.to_string(),
        JValue::Num(n) => n.clone(),
        JValue::Str(s) => s.clone(),
        JValue::Arr(items) => {
            if items.is_empty() {
                "[]".to_owned()
            } else {
                format!(
                    "[{}]",
                    items.iter().map(scalar_text).collect::<Vec<_>>().join(", ")
                )
            }
        }
        JValue::Obj(entries) => {
            if entries.is_empty() {
                "{}".to_owned()
            } else {
                format!(
                    "{{{}}}",
                    entries
                        .iter()
                        .map(|(k, v)| format!("{k}: {}", scalar_text(v)))
                        .collect::<Vec<_>>()
                        .join(", ")
                )
            }
        }
    }
}

fn render_human_jnode(node: &JNode) -> String {
    let format_tag = obj_field(node, "format").and_then(as_str);
    let mut out = String::new();
    match format_tag {
        Some("archsig.summary/1") => render_human_summary(node, &mut out),
        Some("archsig.receipt/1") => render_human_receipt(node, &mut out),
        Some("archsig.reobservation.summary/1") => render_human_reobserve(node, &mut out),
        Some("archsig.digest/1") => render_human_digest(node, &mut out),
        Some("archsig.inspect/1") => render_human_inspect(node, &mut out),
        Some("archsig.inspect-result/1") => render_human_inspect_result(node, &mut out),
        _ => render_generic_human(node, 0, &mut out),
    }
    while out.ends_with('\n') {
        out.pop();
    }
    out
}

fn render_human_receipt(node: &JNode, out: &mut String) {
    let status = obj_field(node, "status")
        .and_then(as_str)
        .unwrap_or("unknown");
    let exit_code = obj_field(node, "exit_code")
        .map(scalar_text)
        .unwrap_or_default();
    let _ = writeln!(out, "Status: {status} (exit {exit_code})");
    if let Some(result) = obj_field(node, "result").and_then(as_str) {
        let _ = writeln!(out, "Result: {result}");
    }
    if let Some(issues) = obj_field(node, "issues").and_then(as_arr)
        && !issues.is_empty()
    {
        let _ = writeln!(out, "Issues ({}):", issues.len());
        for issue in issues {
            render_issue_line(issue, "  ", out);
        }
    }
}

fn render_human_summary(node: &JNode, out: &mut String) {
    let status = obj_field(node, "status")
        .and_then(as_str)
        .unwrap_or("unknown");
    let exit_code = obj_field(node, "exit_code")
        .map(scalar_text)
        .unwrap_or_default();
    let _ = writeln!(out, "Status: {status} (exit {exit_code})");
    if let Some(result) = obj_field(node, "result").and_then(as_str) {
        let _ = writeln!(out, "Result: {result}");
    }
    if let Some(answers) = obj_field(node, "answers").and_then(as_arr) {
        let _ = writeln!(out, "Answers ({}):", answers.len());
        for ans in answers {
            render_summary_answer(ans, "  ", out);
        }
    }
    if let Some(warnings) = obj_field(node, "warnings").and_then(as_arr)
        && !warnings.is_empty()
    {
        let _ = writeln!(out, "Warnings ({}):", warnings.len());
        for w in warnings {
            render_issue_line(w, "  ", out);
        }
    }
    if let Some(issues) = obj_field(node, "issues").and_then(as_arr)
        && !issues.is_empty()
    {
        let _ = writeln!(out, "Issues ({}):", issues.len());
        for issue in issues {
            render_issue_line(issue, "  ", out);
        }
    }
}

fn render_human_reobserve(node: &JNode, out: &mut String) {
    let status = obj_field(node, "status")
        .and_then(as_str)
        .unwrap_or("unknown");
    let exit_code = obj_field(node, "exit_code")
        .map(scalar_text)
        .unwrap_or_default();
    let _ = writeln!(out, "Reobserve Status: {status} (exit {exit_code})");
    if let Some(result) = obj_field(node, "result").and_then(as_str) {
        let _ = writeln!(out, "Result: {result}");
    }
    for (label, key) in [("Previous", "previous"), ("Current", "current")] {
        if let Some(stage) = obj_field(node, key) {
            let _ = writeln!(out, "\n[{label}]");
            render_human_summary(stage, out);
        }
    }
    if let Some(asm) = obj_field(node, "assembly") {
        let _ = writeln!(out, "\n[Assembly]");
        render_generic_human(asm, 2, out);
    }
}

fn render_summary_answer(ans: &JNode, indent: &str, out: &mut String) {
    let id = obj_field(ans, "id").and_then(as_str).unwrap_or("?");
    let question = obj_field(ans, "question").and_then(as_str).unwrap_or("?");
    let status = obj_field(ans, "status").and_then(as_str).unwrap_or("?");
    let _ = writeln!(out, "{indent}- {id} [{question}]: {status}");
    for extra_key in ["applicability", "existence", "uniqueness"] {
        if let Some(val) = obj_field(ans, extra_key) {
            let _ = writeln!(out, "{indent}    {extra_key}: {}", scalar_text(val));
        }
    }
    if let Some(outputs) = obj_field(ans, "outputs") {
        if let Some(shigure) = obj_field(outputs, "shigure") {
            render_shigure_summary(shigure, &format!("{indent}    "), out);
        } else if let JValue::Obj(entries) = &outputs.value {
            for (k, v) in entries {
                let _ = writeln!(out, "{indent}    output.{k}: {}", scalar_text(v));
            }
        }
    }
    if let Some(examples) = obj_field(ans, "counterexamples").and_then(as_arr)
        && !examples.is_empty()
    {
        let total = obj_field(ans, "counterexamples_total")
            .map(scalar_text)
            .unwrap_or_else(|| examples.len().to_string());
        let _ = writeln!(
            out,
            "{indent}    counterexamples (showing {} of {total}):",
            examples.len()
        );
        for ex in examples {
            let _ = writeln!(out, "{indent}      * {}", scalar_text(ex));
        }
    }
    if let Some(reasons) = obj_field(ans, "reasons").and_then(as_arr)
        && !reasons.is_empty()
    {
        for r in reasons {
            render_issue_line(r, &format!("{indent}    reason "), out);
        }
    }
}

fn render_shigure_summary(shigure: &JNode, indent: &str, out: &mut String) {
    if let Some(verdict) = obj_field(shigure, "verdict").and_then(as_str) {
        let _ = writeln!(out, "{indent}verdict: {verdict}");
    }
    if let Some(sr) = obj_field(shigure, "silence_reason") {
        let code = obj_field(sr, "code").and_then(as_str).unwrap_or("unknown");
        let _ = writeln!(out, "{indent}silence_reason: {code} ({})", scalar_text(sr));
    }
    if let Some(passed) = obj_field(shigure, "passed_applicability_count") {
        let _ = writeln!(
            out,
            "{indent}passed_applicability_count: {}",
            scalar_text(passed)
        );
    }
    if let Some(app) = obj_field(shigure, "applicability").and_then(as_arr)
        && !app.is_empty()
    {
        let failed: Vec<_> = app
            .iter()
            .filter(|a| {
                obj_field(a, "satisfied").and_then(|v| match v.value {
                    JValue::Bool(b) => Some(b),
                    _ => None,
                }) == Some(false)
            })
            .collect();
        if !failed.is_empty() {
            let _ = writeln!(
                out,
                "{indent}failed_applicability: {}",
                failed
                    .into_iter()
                    .map(scalar_text)
                    .collect::<Vec<_>>()
                    .join("; ")
            );
        }
    }
    if let Some(witness) = obj_field(shigure, "empty_witness") {
        let _ = writeln!(out, "{indent}empty_witness: {}", scalar_text(witness));
    }
    if let Some(restored) = obj_field(shigure, "restored") {
        let _ = writeln!(out, "{indent}repairs/restored: {}", scalar_text(restored));
    }
    if let Some(res_count) = obj_field(shigure, "residual_ideal_count") {
        let _ = writeln!(
            out,
            "{indent}residual_ideal_count: {}",
            scalar_text(res_count)
        );
    }
    for key in [
        "interaction",
        "diagram",
        "path",
        "transfer",
        "robustness",
        "chevalley",
        "observations",
        "lift",
        "artin",
        "diagnostics",
        "atlas",
        "occurrence",
        "partial",
        "revision",
        "multisource",
    ] {
        if let Some(val) = obj_field(shigure, key) {
            let _ = writeln!(out, "{indent}{key}: {}", scalar_text(val));
        }
    }
    if let Some(origin_ids) = obj_field(shigure, "origin_ids").and_then(as_arr)
        && !origin_ids.is_empty()
    {
        let _ = writeln!(
            out,
            "{indent}origins: {}",
            origin_ids
                .iter()
                .map(scalar_text)
                .collect::<Vec<_>>()
                .join(", ")
        );
    }
    if let Some(prov) = obj_field(shigure, "provenance") {
        if let Some(origins) = obj_field(prov, "origins").and_then(as_arr)
            && !origins.is_empty()
        {
            let _ = writeln!(
                out,
                "{indent}origins: {}",
                origins
                    .iter()
                    .map(scalar_text)
                    .collect::<Vec<_>>()
                    .join("; ")
            );
        }
        if let Some(sources) = obj_field(prov, "source_locations").and_then(as_arr)
            && !sources.is_empty()
        {
            let _ = writeln!(
                out,
                "{indent}locations: {}",
                sources
                    .iter()
                    .map(scalar_text)
                    .collect::<Vec<_>>()
                    .join("; ")
            );
        }
    }
    if let Some(omitted) = obj_field(shigure, "omitted_fields").and_then(as_arr)
        && !omitted.is_empty()
    {
        let _ = writeln!(
            out,
            "{indent}omitted_fields: {}",
            omitted
                .iter()
                .map(scalar_text)
                .collect::<Vec<_>>()
                .join(", ")
        );
    }
    if let Some(hint) = obj_field(shigure, "detail_hint").and_then(as_str) {
        let _ = writeln!(out, "{indent}detail_hint: {hint}");
    }
}

fn render_issue_line(issue: &JNode, prefix: &str, out: &mut String) {
    let code = obj_field(issue, "code").and_then(as_str).unwrap_or("issue");
    let msg = obj_field(issue, "message").and_then(as_str).unwrap_or("");
    let _ = writeln!(out, "{prefix}[{code}] {msg}");
    if let Some(loc) = obj_field(issue, "location") {
        let _ = writeln!(out, "{prefix}  location: {}", scalar_text(loc));
    }
    if let Some(missing) = obj_field(issue, "missing").and_then(as_arr)
        && !missing.is_empty()
    {
        let _ = writeln!(
            out,
            "{prefix}  missing: {}",
            missing
                .iter()
                .map(scalar_text)
                .collect::<Vec<_>>()
                .join(", ")
        );
    }
}

fn render_human_digest(node: &JNode, out: &mut String) {
    let _ = writeln!(out, "Vocabularies:");
    if let Some(vocabs) = obj_field(node, "vocabularies").and_then(as_arr) {
        if vocabs.is_empty() {
            let _ = writeln!(out, "  (none)");
        }
        for v in vocabs {
            let ns = obj_field(v, "namespace").and_then(as_str).unwrap_or("?");
            let ver = obj_field(v, "version").and_then(as_str).unwrap_or("?");
            let digest = obj_field(v, "digest").and_then(as_str).unwrap_or("?");
            let _ = writeln!(out, "  - {ns} {ver}");
            let _ = writeln!(out, "    digest: {digest}");
            let _ = writeln!(out, "    use {ns} \"{ver}\" \"{digest}\"");
        }
    }
}

fn render_human_inspect(node: &JNode, out: &mut String) {
    if let Some(vocabs) = obj_field(node, "vocabularies").and_then(as_arr) {
        let _ = writeln!(out, "Vocabularies ({}):", vocabs.len());
        for v in vocabs {
            let _ = writeln!(out, "  - {}", scalar_text(v));
        }
    }
    if let Some(decls) = obj_field(node, "declarations").and_then(as_arr) {
        let _ = writeln!(out, "Law Declarations ({}):", decls.len());
        for d in decls {
            let name = obj_field(d, "name").and_then(as_str).unwrap_or("?");
            let kind = obj_field(d, "kind").and_then(as_str).unwrap_or("?");
            let _ = writeln!(out, "  - {kind} {name}");
        }
    }
    if let Some(shigure) = obj_field(node, "shigure_declarations") {
        let total = obj_field(shigure, "total_count")
            .map(scalar_text)
            .unwrap_or_else(|| "0".to_owned());
        let _ = writeln!(out, "SHIGURE Declarations ({total}):");
        if let JValue::Obj(entries) = &shigure.value {
            for (cat, list) in entries {
                if cat == "total_count" {
                    continue;
                }
                if let Some(items) = as_arr(list)
                    && !items.is_empty()
                {
                    let _ = writeln!(
                        out,
                        "  - {cat}: {}",
                        items.iter().map(scalar_text).collect::<Vec<_>>().join(", ")
                    );
                }
            }
        }
    }
    if let Some(snaps) = obj_field(node, "snapshots").and_then(as_arr) {
        let _ = writeln!(out, "Snapshots ({}):", snaps.len());
        for s in snaps {
            let sid = obj_field(s, "id").and_then(as_str).unwrap_or("?");
            let origin = obj_field(s, "origin").and_then(as_str).unwrap_or("?");
            let subjects = obj_field(s, "subjects").and_then(as_arr).unwrap_or(&[]);
            let _ = writeln!(
                out,
                "  - @{sid} (origin: {origin}, subjects: {})",
                subjects.len()
            );
            for subj in subjects {
                let id = obj_field(subj, "id").and_then(as_str).unwrap_or("?");
                let ty = obj_field(subj, "type").and_then(as_str).unwrap_or("?");
                let known = obj_field(subj, "known_fields")
                    .and_then(as_arr)
                    .map_or(0, |a| a.len());
                let missing = obj_field(subj, "missing_fields")
                    .and_then(as_arr)
                    .map_or(0, |a| a.len());
                let _ = writeln!(
                    out,
                    "      subject {id} : {ty} (known={known}, missing={missing})"
                );
            }
        }
    }
    if let Some(missing) = obj_field(node, "missing_slots").and_then(as_arr) {
        let _ = writeln!(out, "Missing Slots ({}):", missing.len());
        for slot in missing {
            let _ = writeln!(out, "  - {}", scalar_text(slot));
        }
    }
}

fn render_human_inspect_result(node: &JNode, out: &mut String) {
    let source_format = obj_field(node, "source_format")
        .and_then(as_str)
        .unwrap_or("?");
    let status = obj_field(node, "status").and_then(as_str).unwrap_or("?");
    let exit_code = obj_field(node, "exit_code")
        .map(scalar_text)
        .unwrap_or_default();
    let _ = writeln!(
        out,
        "Saved Result ({source_format}): {status} (exit {exit_code})"
    );
    if let Some(answers) = obj_field(node, "answers").and_then(as_arr) {
        let _ = writeln!(out, "Answers ({}):", answers.len());
        for ans in answers {
            let id = obj_field(ans, "id").and_then(as_str).unwrap_or("?");
            let status = obj_field(ans, "status").and_then(as_str).unwrap_or("?");
            let _ = writeln!(out, "  - {id}: {status}");
            for key in [
                "conclusion",
                "claim",
                "counterexamples",
                "repairs",
                "missing",
                "origins",
                "locations",
                "reasons",
                "evidence",
            ] {
                if let Some(val) = obj_field(ans, key) {
                    if let Some(items) = as_arr(val)
                        && items.is_empty()
                    {
                        continue;
                    }
                    let _ = writeln!(out, "      {key}: {}", scalar_text(val));
                }
            }
        }
    }
}

fn render_generic_human(node: &JNode, indent: usize, out: &mut String) {
    let pad = " ".repeat(indent);
    match &node.value {
        JValue::Obj(entries) => {
            for (k, v) in entries {
                match &v.value {
                    JValue::Obj(_) | JValue::Arr(_) => {
                        let _ = writeln!(out, "{pad}{k}:");
                        render_generic_human(v, indent + 2, out);
                    }
                    _ => {
                        let _ = writeln!(out, "{pad}{k}: {}", scalar_text(v));
                    }
                }
            }
        }
        JValue::Arr(items) => {
            for item in items {
                let _ = writeln!(out, "{pad}- {}", scalar_text(item));
            }
        }
        _ => {
            let _ = writeln!(out, "{pad}{}", scalar_text(node));
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn pretty_jnode_formats_with_two_space_indentation_and_preserves_numbers() {
        let parsed = parse_with_max_depth(br#"{"b":1.25,"a":[true,{}]}"#, 16).unwrap();
        assert_eq!(
            pretty_jnode(&parsed),
            "{\n  \"b\": 1.25,\n  \"a\": [\n    true,\n    {}\n  ]\n}"
        );
    }
}
