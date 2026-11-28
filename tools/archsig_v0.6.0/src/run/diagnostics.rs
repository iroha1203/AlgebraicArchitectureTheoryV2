//! パニック診断、類似候補サジェスト、`SilenceReason` 対処案内、ソース抜粋付与。

use crate::platform;
use crate::run::Outcome;
use archsig_common::canonical::{Json, JsonObject};
use archsig_common::diagnostic::{
    SourceSnippet, capture_panic_from_unwind, format_panic_backtrace_stderr, silence_reason_hint,
    suggest_identifiers,
};
use archsig_common::json::{JNode, JValue, parse_with_max_depth};
use archsig_common::limits::DEFAULT_MAX_JSON_DEPTH;
use archsig_input::input::{CheckedInputs, InputSources};
use archsig_input::result::{ResultIssue, extract_issue_snippets};
use archsig_shigure::ir::result::SilenceReason;
use std::any::Any;
use std::collections::BTreeSet;

/// `catch_unwind` のパニック情報から `ResultIssue::InternalPanic` を生成する。
pub(crate) fn panic_internal_issue(
    operation: &str,
    message: &str,
    payload: Box<dyn Any + Send>,
) -> ResultIssue {
    let info = capture_panic_from_unwind(payload);
    if let Some(bt) = format_panic_backtrace_stderr(&info) {
        let _ = platform::write_stderr_line(&bt);
    }
    ResultIssue::InternalPanic {
        operation: operation.to_owned(),
        message: message.to_owned(),
        panic_message: info.message,
        panic_location: info.location,
    }
}

/// 類似候補サジェストに用いる既知識別子プール。
#[derive(Clone, Debug, Default)]
pub(crate) struct DiagnosticContext {
    pub namespaces: Vec<String>,
    pub declarations: Vec<String>,
    pub entity_decls: Vec<String>,
    pub fields: Vec<String>,
    pub readings: Vec<String>,
    pub sources: Vec<String>,
    pub origins: Vec<String>,
}

impl DiagnosticContext {
    /// 生入力バイト列からベストエフォートで識別子候補を抽出する。
    pub(crate) fn from_raw_inputs(
        definitions: &[&[u8]],
        law: Option<&[u8]>,
        archmap: Option<&[u8]>,
    ) -> Self {
        let mut namespaces = BTreeSet::new();
        let mut declarations = BTreeSet::new();
        let mut entity_decls = BTreeSet::new();
        let mut fields = BTreeSet::new();
        let mut readings = BTreeSet::new();
        let mut sources = BTreeSet::new();
        let mut origins = BTreeSet::new();

        for def_bytes in definitions {
            if let Ok(node) = parse_with_max_depth(def_bytes, DEFAULT_MAX_JSON_DEPTH) {
                collect_from_definition_json(
                    &node,
                    &mut namespaces,
                    &mut declarations,
                    &mut entity_decls,
                    &mut fields,
                );
            }
        }
        if let Some(law_bytes) = law {
            collect_from_law_bytes(law_bytes, &mut readings, &mut declarations);
        }
        if let Some(map_bytes) = archmap
            && let Ok(node) = parse_with_max_depth(map_bytes, DEFAULT_MAX_JSON_DEPTH)
        {
            collect_from_archmap_json(&node, &mut sources, &mut origins);
        }

        Self {
            namespaces: namespaces.into_iter().collect(),
            declarations: declarations.into_iter().collect(),
            entity_decls: entity_decls.into_iter().collect(),
            fields: fields.into_iter().collect(),
            readings: readings.into_iter().collect(),
            sources: sources.into_iter().collect(),
            origins: origins.into_iter().collect(),
        }
    }

    pub(crate) fn from_input_sources(sources: &InputSources) -> Self {
        let defs: Vec<&[u8]> = sources.definitions().iter().map(|d| d.bytes()).collect();
        Self::from_raw_inputs(
            &defs,
            Some(sources.law().bytes()),
            Some(sources.archmap().bytes()),
        )
    }

    #[allow(dead_code)]
    pub(crate) fn from_checked(checked: &CheckedInputs) -> Self {
        Self::from_input_sources(checked.sources())
    }
}

fn j_field<'a>(node: &'a JNode, key: &str) -> Option<&'a JNode> {
    let JValue::Obj(entries) = &node.value else {
        return None;
    };
    entries.iter().find(|(k, _)| k == key).map(|(_, v)| v)
}

fn j_str(node: &JNode) -> Option<&str> {
    match &node.value {
        JValue::Str(s) => Some(s.as_str()),
        _ => None,
    }
}

fn j_arr(node: &JNode) -> Option<&[JNode]> {
    match &node.value {
        JValue::Arr(items) => Some(items.as_slice()),
        _ => None,
    }
}

fn collect_from_definition_json(
    node: &JNode,
    namespaces: &mut BTreeSet<String>,
    declarations: &mut BTreeSet<String>,
    entity_decls: &mut BTreeSet<String>,
    fields: &mut BTreeSet<String>,
) {
    let vocab_list: Vec<&JNode> = if let Some(arr) = j_field(node, "vocabularies").and_then(j_arr) {
        arr.iter().collect()
    } else if let Some(ns) = j_field(node, "namespace").and_then(j_str) {
        let _ = ns;
        vec![node]
    } else {
        Vec::new()
    };

    for v in vocab_list {
        let Some(ns) = j_field(v, "namespace").and_then(j_str) else {
            continue;
        };
        namespaces.insert(ns.to_owned());
        if let Some(decls) = j_field(v, "declarations").and_then(j_arr) {
            for d in decls {
                let Some(name) = j_field(d, "name").and_then(j_str) else {
                    continue;
                };
                let fq = if name.contains('.') {
                    name.to_owned()
                } else {
                    format!("{ns}.{name}")
                };
                declarations.insert(fq.clone());
                declarations.insert(name.to_owned());
                if let Some(kind) = j_field(d, "kind").and_then(j_str)
                    && matches!(kind, "entity" | "arrow" | "correspondence")
                {
                    entity_decls.insert(fq.clone());
                    entity_decls.insert(name.to_owned());
                }
                for key in ["parameters", "fields"] {
                    if let Some(items) = j_field(d, key).and_then(j_arr) {
                        for item in items {
                            if let Some(fname) = j_field(item, "name").and_then(j_str) {
                                fields.insert(fname.to_owned());
                                fields.insert(format!("{fq}.{fname}"));
                            }
                        }
                    }
                }
            }
        }
    }
}

fn collect_from_law_bytes(
    bytes: &[u8],
    readings: &mut BTreeSet<String>,
    declarations: &mut BTreeSet<String>,
) {
    let text = String::from_utf8_lossy(bytes);
    let mut words = text
        .split(|c: char| !c.is_ascii_alphanumeric() && c != '_' && c != '.')
        .filter(|w| !w.is_empty())
        .peekable();
    let mut current_reading: Option<String> = None;
    while let Some(tok) = words.next() {
        match tok {
            "reading" => {
                if let Some(&name) = words.peek()
                    && is_plain_ident(name)
                {
                    readings.insert(name.to_owned());
                    current_reading = Some(name.to_owned());
                }
            }
            "view" | "law" | "local" | "change" | "relation" => {
                if let Some(&name) = words.peek()
                    && is_plain_ident(name)
                {
                    declarations.insert(name.to_owned());
                    if let Some(r) = &current_reading {
                        declarations.insert(format!("{r}.{name}"));
                    }
                }
            }
            _ => {}
        }
    }
}

fn is_plain_ident(s: &str) -> bool {
    let mut b = s.bytes();
    b.next().is_some_and(|c| c.is_ascii_alphabetic())
        && b.all(|c| c.is_ascii_alphanumeric() || c == b'_')
}

fn collect_from_archmap_json(
    node: &JNode,
    sources: &mut BTreeSet<String>,
    origins: &mut BTreeSet<String>,
) {
    if let Some(items) = j_field(node, "sources").and_then(j_arr) {
        for s in items {
            if let Some(id) = j_field(s, "id").and_then(j_str) {
                sources.insert(id.to_owned());
            }
        }
    }
    if let Some(items) = j_field(node, "origins").and_then(j_arr) {
        for o in items {
            if let Some(id) = j_field(o, "id").and_then(j_str) {
                origins.insert(id.to_owned());
            }
        }
    }
}

/// issue 配列へ類似識別子候補と修正ヒント（`details.suggestions` / `details.hint`）を補う。
/// 候補が空の場合は既存 `details`（例: `{}`）を変更しない。
pub(crate) fn enrich_issues(issues: &mut [Json], ctx: &DiagnosticContext) {
    for issue in issues {
        enrich_issue(issue, ctx);
    }
}

fn extract_backticked(message: &str) -> Vec<&str> {
    let mut out = Vec::new();
    let mut rest = message;
    while let Some(start) = rest.find('`') {
        let after = &rest[start + 1..];
        let Some(end) = after.find('`') else {
            break;
        };
        out.push(&after[..end]);
        rest = &after[end + 1..];
    }
    out
}

fn enrich_issue(issue: &mut Json, ctx: &DiagnosticContext) {
    let Json::Obj(fields) = issue else {
        return;
    };
    let code = match fields.get("code") {
        Some(Json::Str(s)) => s.clone(),
        _ => return,
    };
    let message = match fields.get("message") {
        Some(Json::Str(s)) => s.clone(),
        _ => return,
    };

    if code == "vocabulary_mismatch" {
        if let Some(Json::Obj(details)) = fields.get_mut("details")
            && !details.contains_key("hint")
        {
            details.insert(
                "hint".to_owned(),
                Json::str(
                    "run `archsig digest --atom-definition <file>` to inspect expected namespace, version, and SHA-256 digest",
                ),
            );
        }
        return;
    }

    if code != "reference" {
        return;
    }

    let tokens = extract_backticked(&message);
    if tokens.is_empty() {
        return;
    }

    let suggestions = if message.contains("is not included") {
        suggest_identifiers(tokens[0], ctx.readings.iter().map(String::as_str), 3)
    } else if message.starts_with("source `") {
        suggest_identifiers(tokens[0], ctx.sources.iter().map(String::as_str), 3)
    } else if message.starts_with("origin `") {
        suggest_identifiers(tokens[0], ctx.origins.iter().map(String::as_str), 3)
    } else if message.starts_with("vocabulary `")
        || message.contains("missing dependency for namespace")
    {
        suggest_identifiers(tokens[0], ctx.namespaces.iter().map(String::as_str), 3)
    } else if message.contains("not an entity, arrow, or correspondence declaration") {
        suggest_identifiers(tokens[0], ctx.entity_decls.iter().map(String::as_str), 3)
    } else if message.contains("has no field `") && tokens.len() >= 2 {
        suggest_identifiers(tokens[1], ctx.fields.iter().map(String::as_str), 3)
    } else {
        let mut pool: Vec<&str> = ctx.declarations.iter().map(String::as_str).collect();
        pool.extend(ctx.fields.iter().map(String::as_str));
        pool.extend(ctx.namespaces.iter().map(String::as_str));
        suggest_identifiers(tokens[0], pool, 3)
    };

    if !suggestions.is_empty()
        && let Some(Json::Obj(details)) = fields.get_mut("details")
    {
        attach_suggestions(details, suggestions);
    }
}

pub(crate) fn attach_suggestions(details: &mut JsonObject, suggestions: Vec<String>) {
    if suggestions.is_empty() {
        return;
    }
    let formatted = suggestions
        .iter()
        .map(|s| format!("`{s}`"))
        .collect::<Vec<_>>()
        .join(", ");
    details.insert(
        "suggestions".to_owned(),
        Json::Arr(suggestions.into_iter().map(Json::str).collect()),
    );
    if !details.contains_key("hint") {
        details.insert(
            "hint".to_owned(),
            Json::str(format!("did you mean {formatted}?")),
        );
    }
}

/// `Outcome` の各 issue に対応するソース行抜粋（`SourceSnippet`）を抽出する。
pub(crate) fn extract_snippets_for_copies(
    issues: &[Json],
    copies: &[(&str, &[u8])],
) -> Vec<Option<SourceSnippet>> {
    let mut mapped: Vec<(String, &[u8])> = Vec::with_capacity(copies.len());
    for &(name, bytes) in copies {
        let input_id = if name == "inputs/law.law" {
            "law".to_owned()
        } else if name == "inputs/archmap.json" {
            "archmap".to_owned()
        } else if let Some(rest) = name.strip_prefix("inputs/definitions/")
            && let Some(idx) = rest.strip_suffix(".json")
        {
            format!("definition{idx}")
        } else {
            name.to_owned()
        };
        mapped.push((input_id, bytes));
    }
    extract_issue_snippets(issues, mapped.iter().map(|(id, b)| (id.as_str(), *b)))
}

/// `InputFailure` などの失敗 `Outcome` へ類似候補サジェストとソース抜粋を一括付与する。
pub(crate) fn decorate_outcome_with_sources(outcome: &mut Outcome, sources: &InputSources) {
    let ctx = DiagnosticContext::from_input_sources(sources);
    enrich_issues(&mut outcome.issues, &ctx);
    let mut copies: Vec<(String, &[u8])> = sources
        .definitions()
        .iter()
        .enumerate()
        .map(|(i, b)| (format!("definition{i}"), b.bytes()))
        .collect();
    copies.push(("law".to_owned(), sources.law().bytes()));
    copies.push(("archmap".to_owned(), sources.archmap().bytes()));
    let copy_refs: Vec<(&str, &[u8])> = copies.iter().map(|(k, b)| (k.as_str(), *b)).collect();
    outcome.snippets = extract_issue_snippets(&outcome.issues, copy_refs);
}

/// 21 種の `SilenceReason` に対して `details.hint`（推奨アクション）を必ず付与する。
pub(crate) fn silence_reason_details_with_hint(reason: &SilenceReason) -> Json {
    let mut json = reason.to_json();
    let (key, limit_name, slots): (&str, Option<&str>, &[String]) = match reason {
        SilenceReason::UnobservedDependency { slots } => ("unobserved_dependency", None, slots),
        SilenceReason::NonLinearRationalOrIntegerExistence { .. } => {
            ("nonlinear_rational_or_integer_existence", None, &[])
        }
        SilenceReason::InfinitePresentationNotFinitelyReducible { .. } => {
            ("infinite_presentation_not_finitely_reducible", None, &[])
        }
        SilenceReason::UnsupportedCoeffRing { .. } => ("unsupported_coeff_ring", None, &[]),
        SilenceReason::QuotientIdealOutOfScope { .. } => ("quotient_ideal_out_of_scope", None, &[]),
        SilenceReason::OpenConditionInInteraction { .. } => {
            ("open_condition_in_interaction", None, &[])
        }
        SilenceReason::UnboundedSearchOutOfScope { .. } => {
            ("unbounded_search_out_of_scope", None, &[])
        }
        SilenceReason::ConstructibleStratificationOutOfScope { .. } => {
            ("constructible_stratification_out_of_scope", None, &[])
        }
        SilenceReason::FiniteEnumerationOutOfScope { .. } => {
            ("finite_enumeration_out_of_scope", None, &[])
        }
        SilenceReason::UniversalRingOutOfScope { .. } => ("universal_ring_out_of_scope", None, &[]),
        SilenceReason::NonNoetherianInfinitePresentation { .. } => {
            ("non_noetherian_infinite_presentation", None, &[])
        }
        SilenceReason::SquareZeroConditionViolated { .. } => {
            ("square_zero_condition_violated", None, &[])
        }
        SilenceReason::SyzygyOutOfScope { .. } => ("syzygy_out_of_scope", None, &[]),
        SilenceReason::ArtinOrderOutOfScope { .. } => ("artin_order_out_of_scope", None, &[]),
        SilenceReason::DiagnosticsStratificationOutOfScope { .. } => {
            ("diagnostics_stratification_out_of_scope", None, &[])
        }
        SilenceReason::DisconnectedGraphOutOfScope { .. } => {
            ("disconnected_graph_out_of_scope", None, &[])
        }
        SilenceReason::UnsupportedCompletionClass { .. } => {
            ("unsupported_completion_class", None, &[])
        }
        SilenceReason::OperatorNotUniquelyDetermined { .. } => {
            ("operator_not_uniquely_determined", None, &[])
        }
        SilenceReason::OperatorRevisionReuseRejected { .. } => {
            ("operator_revision_reuse_rejected", None, &[])
        }
        SilenceReason::ApplicabilityConditionNotMet { .. } => {
            ("applicability_condition_not_met", None, &[])
        }
        SilenceReason::ResourceLimitExceeded { limit_name, .. } => {
            ("resource_limit_exceeded", Some(limit_name.as_str()), &[])
        }
    };
    let hint = silence_reason_hint(key, limit_name, slots);
    if let Json::Obj(fields) = &mut json {
        fields.insert("hint".to_owned(), Json::str(hint));
    }
    json
}
