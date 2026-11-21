//! `archsig run` から SHIGURE 計算（`shigure_preservation` / `shigure_solve` / `shigure_interaction`）を実行する最小入口。
//!
//! 責務:
//! - 既存の `crates/computation/src/observed/` へ一切触れずに、`archsig-input::input::check_inputs` →
//!   `archsig-shigure::convert::ShigureConverter` → `archsig-shigure::solver::execute_shigure_task` を接続する
//! - 実行仕様 §§1・5–7 に従い、`archsig.summary/1`（stdout）と `archsig.result/4`（`--out` 保存時）および終了コードを返す
//! - `Verdict::Undetermined`（沈黙）をエラーではなく正常な `partial` / exit 2 出力として返す

use super::{Io, Outcome, RunArgs, Signals, output, read};
use archsig_common::canonical::{Json, JsonObject};
use archsig_common::control::{Checkpoint, Control};
use archsig_input::input::{CheckedInputs, InputSources, InputStatus, check_inputs};
use archsig_input::result::{ResultIssue, Status, exit_code};
use archsig_shigure::convert::{ShigureConverter, ToShigureTask};
use archsig_shigure::ir::result::{ShigureOutcome, SilenceReason, Verdict};
use archsig_shigure::ir::validate::{CheckedShigureTask, ValidationError};
use archsig_shigure::solver::{ShigureQueryKind, execute_shigure_task};
use std::collections::BTreeSet;

/// `--ask` 群における SHIGURE 問いの分類。
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum AskPartition {
    /// SHIGURE 問いが 1 件もない（既存の observed 経路をそのまま使う）。
    None,
    /// 全件が SHIGURE 問い。
    AllShigure,
    /// SHIGURE 問いと既存の observed 問いが混在している。
    Mixed,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct ParsedShigureRequest {
    id: String,
    text: String,
    query_kind: ShigureQueryKind,
    task_name: String,
    snapshot: Option<String>,
}

impl ParsedShigureRequest {
    fn kind_wire(&self) -> &'static str {
        match self.query_kind {
            ShigureQueryKind::SemanticPreservation => "shigure_preservation",
            ShigureQueryKind::ConditionalSolutionSpace => "shigure_solve",
            ShigureQueryKind::InteractionAnalysis => "shigure_interaction",
        }
    }
}

struct ResolvedShigureRequest {
    parsed: ParsedShigureRequest,
    resolved_task_name: String,
    reading_name: String,
    task: CheckedShigureTask,
}

/// `--ask` 文字列列に SHIGURE 問いが含まれるかを判定する。
pub(super) fn classify_asks(asks: &[String]) -> AskPartition {
    let mut shigure_count = 0usize;
    for ask in asks {
        if looks_like_shigure_ask(ask) {
            shigure_count += 1;
        }
    }
    if shigure_count == 0 {
        AskPartition::None
    } else if shigure_count == asks.len() {
        AskPartition::AllShigure
    } else {
        AskPartition::Mixed
    }
}

fn looks_like_shigure_ask(ask: &str) -> bool {
    let rhs = match ask.find('=') {
        Some(pos) => ask[pos + 1..].trim_start(),
        None => ask.trim_start(),
    };
    for prefix in [
        "shigure_preservation",
        "shigure_solve",
        "shigure_interaction",
    ] {
        if let Some(rest) = rhs.strip_prefix(prefix)
            && (rest.is_empty()
                || !rest
                    .as_bytes()
                    .first()
                    .is_some_and(|b| b.is_ascii_alphanumeric() || *b == b'_'))
        {
            return true;
        }
    }
    false
}

/// SHIGURE 問いと既存の observed 問いを同一 `run` で混在させたときの usage エラー。
pub(super) fn mixed_asks_outcome(signals: &mut dyn Signals, control: &Control) -> Outcome {
    output::notify(
        signals,
        Status::Invalid,
        64,
        control.stop_reason(),
        vec![usage_issue(
            None,
            "SHIGURE queries (`shigure_preservation`, `shigure_solve`, `shigure_interaction`) cannot be combined with standard observed queries in the same `archsig run`; invoke them separately",
        )],
    )
}

/// 検査済み `RunArgs` に対して SHIGURE 問い列を実行し、`archsig.summary/1` / `archsig.result/4` を配送する。
pub(super) fn run_shigure_validated(
    io: &mut dyn Io,
    signals: &mut dyn Signals,
    args: &RunArgs,
    control: &Control,
) -> Outcome {
    let parsed_requests = match parse_shigure_requests(&args.asks, signals, control) {
        Ok(reqs) => reqs,
        Err(outcome) => return outcome,
    };

    let map_path = args.inputs.archmap.as_ref().expect("検査済みrunのArchMap");
    let mut io_issues = Vec::new();
    let definitions: Vec<_> = args
        .inputs
        .atom_definitions
        .iter()
        .map(|p| read(p, &mut io_issues))
        .collect();
    let law = read(&args.inputs.law, &mut io_issues);
    let map = read(map_path, &mut io_issues);
    if !io_issues.is_empty() {
        return output::without_result(signals, Status::Error, io_issues);
    }

    let sources = InputSources::from_bytes(
        definitions.into_iter().flatten().collect(),
        law.expect("読込成功を確認したLaw"),
        map.expect("読込成功を確認したArchMap"),
    );

    let checked = match check_inputs(sources, control) {
        Ok(checked) => checked,
        Err(failure) => {
            let (status, code) = match failure.status() {
                InputStatus::Invalid => (Status::Invalid, 65),
                InputStatus::Unsupported => (Status::Unsupported, 69),
                InputStatus::Interrupted => (Status::Interrupted, 75),
                InputStatus::Error => (Status::Error, 70),
            };
            return output::notify(
                signals,
                status,
                code,
                control.stop_reason(),
                failure.issues().to_vec(),
            );
        }
    };

    let resolved = match resolve_and_convert(&checked, parsed_requests, signals, control) {
        Ok(resolved) => resolved,
        Err(outcome) => return outcome,
    };

    let mut warnings = Vec::new();
    if args.reuse.is_some() {
        warnings.push(
            ResultIssue::Usage {
                argument: "--reuse".to_owned(),
                message:
                    "SHIGURE queries do not reuse cached results; recomputing from current inputs"
                        .to_owned(),
            }
            .wire(),
        );
    }

    let mut executed: Vec<(ResolvedShigureRequest, Option<ShigureOutcome>)> =
        Vec::with_capacity(resolved.len());
    let mut interrupted_reason = None;
    for req in resolved {
        if interrupted_reason.is_none()
            && let Err(reason) = control.checkpoint(Checkpoint::Work)
        {
            interrupted_reason = Some(reason);
        }
        if interrupted_reason.is_some() {
            executed.push((req, None));
        } else {
            let outcome = execute_shigure_task(&req.task, req.parsed.query_kind);
            executed.push((req, Some(outcome)));
        }
    }

    deliver_shigure(
        io,
        signals,
        args,
        &checked,
        executed,
        warnings,
        interrupted_reason,
        control,
    )
}

fn parse_shigure_requests(
    asks: &[String],
    signals: &mut dyn Signals,
    control: &Control,
) -> Result<Vec<ParsedShigureRequest>, Outcome> {
    let mut parsed = Vec::with_capacity(asks.len());
    let mut seen_ids = BTreeSet::new();
    for ask in asks {
        if let Err(signal) = control.checkpoint(Checkpoint::RequestSyntax) {
            return Err(output::notify(
                signals,
                Status::Interrupted,
                75,
                control.stop_reason(),
                vec![signal.issue()],
            ));
        }
        let req = parse_single_ask(ask).map_err(|msg| {
            output::notify(
                signals,
                Status::Invalid,
                64,
                control.stop_reason(),
                vec![usage_issue(None, &msg)],
            )
        })?;
        if !seen_ids.insert(req.id.clone()) {
            return Err(output::notify(
                signals,
                Status::Invalid,
                64,
                control.stop_reason(),
                vec![usage_issue(
                    Some(&req.id),
                    &format!("duplicate request id `{}`", req.id),
                )],
            ));
        }
        parsed.push(req);
    }
    Ok(parsed)
}

fn parse_single_ask(ask: &str) -> Result<ParsedShigureRequest, String> {
    let Some(eq_pos) = ask.find('=') else {
        return Err(format!(
            "invalid SHIGURE request `{ask}`: expected `ID=shigure_<kind>(TaskName[, snapshot=SnapshotId])`"
        ));
    };
    let id = ask[..eq_pos].trim();
    if !is_ident(id) {
        return Err(format!(
            "invalid request id `{id}` in `{ask}`: expected ASCII identifier"
        ));
    }
    let rhs = ask[eq_pos + 1..].trim();
    let Some(open_pos) = rhs.find('(') else {
        return Err(format!(
            "invalid SHIGURE request `{ask}`: expected `(` after query kind"
        ));
    };
    if !rhs.ends_with(')') {
        return Err(format!(
            "invalid SHIGURE request `{ask}`: expected closing `)`"
        ));
    }
    let kind_str = rhs[..open_pos].trim();
    let query_kind = match kind_str {
        "shigure_preservation" => ShigureQueryKind::SemanticPreservation,
        "shigure_solve" => ShigureQueryKind::ConditionalSolutionSpace,
        "shigure_interaction" => ShigureQueryKind::InteractionAnalysis,
        other => {
            return Err(format!(
                "unknown SHIGURE query kind `{other}` in `{ask}`; expected `shigure_preservation`, `shigure_solve`, or `shigure_interaction`"
            ));
        }
    };
    let inner = rhs[open_pos + 1..rhs.len() - 1].trim();
    if inner.is_empty() {
        return Err(format!(
            "missing SHIGURE task name in `{ask}`; expected `{kind_str}(TaskName[, snapshot=SnapshotId])`"
        ));
    }
    let mut parts = inner.split(',');
    let head = parts.next().expect("non-empty split").trim();
    if head.is_empty() || head.starts_with('.') || head.starts_with('[') {
        return Err(format!(
            "invalid SHIGURE task name `{head}` in `{ask}`; quote arguments if your shell expanded `$` references"
        ));
    }
    if !is_qname(head) {
        return Err(format!(
            "invalid SHIGURE task name `{head}` in `{ask}`: expected identifier or qualified `Reading.Task` name"
        ));
    }
    let mut snapshot: Option<String> = None;
    for raw_arg in parts {
        let arg = raw_arg.trim();
        if arg.is_empty() {
            return Err(format!(
                "empty argument in SHIGURE request `{ask}` (trailing or duplicate comma)"
            ));
        }
        let Some(arg_eq) = arg.find('=') else {
            return Err(format!(
                "invalid argument `{arg}` in `{ask}`: expected `snapshot=SnapshotId`"
            ));
        };
        let key = arg[..arg_eq].trim();
        let val = arg[arg_eq + 1..].trim();
        match key {
            "snapshot" => {
                if snapshot.is_some() {
                    return Err(format!("duplicate argument `snapshot` in `{ask}`"));
                }
                if !is_snapshot_id(val) {
                    return Err(format!(
                        "invalid snapshot id `{val}` in `{ask}`: expected non-empty ArchMap snapshot identifier"
                    ));
                }
                snapshot = Some(val.to_owned());
            }
            other => {
                return Err(format!(
                    "unknown argument `{other}` in SHIGURE request `{ask}`; only optional `snapshot=SnapshotId` is supported"
                ));
            }
        }
    }
    Ok(ParsedShigureRequest {
        id: id.to_owned(),
        text: ask.to_owned(),
        query_kind,
        task_name: head.to_owned(),
        snapshot,
    })
}

fn is_ident(s: &str) -> bool {
    let mut bytes = s.bytes();
    let Some(first) = bytes.next() else {
        return false;
    };
    first.is_ascii_alphabetic()
        && bytes.all(|b| b.is_ascii_alphanumeric() || b == b'_')
        && !archsig_common::names::is_reserved(s)
}

fn is_qname(s: &str) -> bool {
    !s.is_empty() && s.split('.').all(is_ident)
}

fn is_snapshot_id(s: &str) -> bool {
    let mut bytes = s.bytes();
    let Some(first) = bytes.next() else {
        return false;
    };
    first.is_ascii_alphabetic()
        && bytes.all(|b| b.is_ascii_alphanumeric() || matches!(b, b'_' | b'.' | b'-'))
}

fn resolve_and_convert(
    checked: &CheckedInputs,
    parsed_requests: Vec<ParsedShigureRequest>,
    signals: &mut dyn Signals,
    control: &Control,
) -> Result<Vec<ResolvedShigureRequest>, Outcome> {
    let shigure_decls = checked.law().shigure();
    let mut resolved = Vec::with_capacity(parsed_requests.len());

    for req in parsed_requests {
        if let Err(signal) = control.checkpoint(Checkpoint::Resolve) {
            return Err(output::notify(
                signals,
                Status::Interrupted,
                75,
                control.stop_reason(),
                vec![signal.issue()],
            ));
        }

        let resolved_task_name =
            resolve_task_name(&shigure_decls.tasks, &req.task_name).map_err(|msg| {
                output::notify(
                    signals,
                    Status::Invalid,
                    64,
                    control.stop_reason(),
                    vec![usage_issue(Some(&req.id), &msg)],
                )
            })?;

        if let Some(sid) = &req.snapshot
            && !checked.archmap().snapshots().iter().any(|s| s.id == *sid)
        {
            return Err(output::notify(
                signals,
                Status::Invalid,
                64,
                control.stop_reason(),
                vec![usage_issue(
                    Some(&req.id),
                    &format!(
                        "unknown ArchMap snapshot `{sid}` in SHIGURE request `{}`",
                        req.id
                    ),
                )],
            ));
        }

        let mut converter = ShigureConverter::for_task(&resolved_task_name);
        if let Some(sid) = &req.snapshot {
            converter = converter.with_snapshot(sid);
        }
        let task = converter.convert(checked).map_err(|err| {
            let issue = conversion_error_issue(&req.id, &err);
            output::notify(
                signals,
                Status::Invalid,
                65,
                control.stop_reason(),
                vec![issue],
            )
        })?;

        let reading_name = resolved_task_name
            .rsplit_once('.')
            .map_or_else(|| resolved_task_name.clone(), |(r, _)| r.to_owned());

        resolved.push(ResolvedShigureRequest {
            parsed: req,
            resolved_task_name,
            reading_name,
            task,
        });
    }

    Ok(resolved)
}

fn resolve_task_name(
    tasks: &std::collections::BTreeMap<String, archsig_input::law::shigure::ShigureTask>,
    requested: &str,
) -> Result<String, String> {
    if tasks.contains_key(requested) {
        return Ok(requested.to_owned());
    }
    let suffix = format!(".{requested}");
    let matches: Vec<&String> = tasks.keys().filter(|k| k.ends_with(&suffix)).collect();
    match matches.as_slice() {
        [only] => Ok((*only).clone()),
        [] => Err(format!(
            "unknown SHIGURE task `{requested}`; declared tasks: [{}]",
            tasks.keys().cloned().collect::<Vec<_>>().join(", ")
        )),
        many => Err(format!(
            "ambiguous short SHIGURE task name `{requested}`; specify full name among [{}]",
            many.iter()
                .map(|s| s.as_str())
                .collect::<Vec<_>>()
                .join(", ")
        )),
    }
}

#[allow(clippy::too_many_arguments)]
fn deliver_shigure(
    io: &mut dyn Io,
    signals: &mut dyn Signals,
    args: &RunArgs,
    checked: &CheckedInputs,
    executed: Vec<(ResolvedShigureRequest, Option<ShigureOutcome>)>,
    warnings: Vec<Json>,
    interrupted_reason: Option<archsig_input::result::Signal>,
    control: &Control,
) -> Outcome {
    let any_completed = executed.iter().any(|(_, out)| out.is_some());
    if interrupted_reason.is_some() && !any_completed {
        let mut issues = Vec::new();
        if let Some(sig) = interrupted_reason {
            issues.push(sig.issue());
        }
        return output::notify(
            signals,
            Status::Interrupted,
            75,
            control.stop_reason(),
            issues,
        );
    }

    let has_undetermined = executed
        .iter()
        .any(|(_, out)| matches!(out, Some(o) if matches!(o.verdict, Verdict::Undetermined(_))));
    let has_refuted = executed
        .iter()
        .any(|(_, out)| matches!(out, Some(o) if matches!(o.verdict, Verdict::Refuted)));

    let (mut status, mut code) = if let Some(sig) = interrupted_reason {
        (
            Status::Interrupted,
            exit_code(Status::Interrupted, Some(sig), &[]),
        )
    } else if has_undetermined {
        (Status::Partial, 2)
    } else if has_refuted {
        (Status::Complete, 1)
    } else {
        (Status::Complete, 0)
    };

    let mut top_issues: Vec<Json> = Vec::new();
    if let Some(sig) = interrupted_reason {
        top_issues.push(sig.issue());
    }

    let frozen = signals.freeze();
    if let Some(sig) = control.stop_reason().or(frozen) {
        status = Status::Interrupted;
        code = exit_code(status, Some(sig), &[]);
        let sig_issue = sig.issue();
        if !top_issues.contains(&sig_issue) {
            top_issues.push(sig_issue);
        }
    }
    output::sort_issues(&mut top_issues);

    let origin_modes: std::collections::BTreeMap<&str, &'static str> = checked
        .archmap()
        .origins()
        .iter()
        .map(|o| (o.id.as_str(), o.mode.wire()))
        .collect();

    let snapshot_ids: Vec<Json> = checked
        .archmap()
        .snapshots()
        .iter()
        .map(|s| Json::str(&s.id))
        .collect();

    let mut summary_answers = Vec::with_capacity(executed.len());
    let mut saved_requests = Vec::with_capacity(executed.len());
    let mut saved_answers = Vec::with_capacity(executed.len());
    let mut saved_nodes = Vec::with_capacity(executed.len());

    for (idx, (req, outcome_opt)) in executed.into_iter().enumerate() {
        let mut req_args = Vec::new();
        if let Some(sid) = &req.parsed.snapshot {
            req_args.push(Json::obj([
                ("name", Json::str("snapshot")),
                (
                    "value",
                    Json::obj([("kind", Json::str("enum")), ("value", Json::str(sid))]),
                ),
                ("origin", Json::str("explicit")),
            ]));
        }
        saved_requests.push(Json::obj([
            ("id", Json::str(&req.parsed.id)),
            ("text", Json::str(&req.parsed.text)),
            ("kind", Json::str(req.parsed.kind_wire())),
            (
                "head",
                Json::obj([
                    ("kind", Json::str("declaration")),
                    ("name", Json::str(&req.resolved_task_name)),
                ]),
            ),
            ("arguments", Json::Arr(req_args)),
            ("defaults", Json::Arr(vec![])),
            ("dependencies", Json::Arr(vec![])),
        ]));

        let req_snapshots = match &req.parsed.snapshot {
            Some(sid) => vec![Json::str(sid)],
            None => snapshot_ids.clone(),
        };
        let mut mode_set = BTreeSet::from(["specification"]);
        if let Some(outcome) = &outcome_opt {
            for origin_ref in &outcome.provenance.origins {
                if origin_ref.atom_ref.is_some()
                    && origin_ref.law_declaration.is_none()
                    && let Some(&mode_str) = origin_modes.get(origin_ref.origin_id.as_str())
                {
                    mode_set.insert(mode_str);
                }
            }
        }
        let modes: Vec<Json> = ["observed", "proposed", "specification"]
            .into_iter()
            .filter(|m| mode_set.contains(m))
            .map(Json::str)
            .collect();
        let scope = Json::obj([
            ("readings", Json::Arr(vec![Json::str(&req.reading_name)])),
            ("snapshots", Json::Arr(req_snapshots)),
            ("modes", Json::Arr(modes)),
            ("domain", Json::str("shigure_presentation")),
            ("quantifiers", Json::Arr(vec![])),
            ("assumptions", Json::Arr(vec![])),
        ]);

        if let Some(outcome) = outcome_opt {
            let node_id = format!("n{idx}");
            let outcome_json = outcome.to_json();
            let answer_reasons: Vec<Json> = match &outcome.verdict {
                Verdict::Undetermined(reason) => {
                    vec![silence_reason_issue(&req.parsed.id, reason)]
                }
                _ => Vec::new(),
            };

            let mut summary_answer = JsonObject::from([
                ("id".into(), Json::str(&req.parsed.id)),
                ("question".into(), Json::str(req.parsed.kind_wire())),
                ("status".into(), Json::str(outcome.verdict.wire())),
                (
                    "outputs".into(),
                    Json::obj([("shigure", outcome_json.clone())]),
                ),
            ]);
            if !answer_reasons.is_empty() {
                summary_answer.insert("reasons".into(), Json::Arr(answer_reasons.clone()));
            }
            summary_answers.push(Json::Obj(summary_answer));

            saved_nodes.push(Json::obj([
                ("id", Json::str(&node_id)),
                ("type", Json::str("ShigureOutcome")),
                ("state", Json::str("value")),
                ("value", outcome_json),
                ("conditions", Json::Arr(vec![])),
                ("reasons", Json::Arr(answer_reasons.clone())),
            ]));

            saved_answers.push(Json::obj([
                ("id", Json::str(&req.parsed.id)),
                ("status", Json::str(outcome.verdict.wire())),
                (
                    "outputs",
                    Json::obj([("shigure", Json::obj([("node", Json::str(&node_id))]))]),
                ),
                ("reasons", Json::Arr(answer_reasons)),
                ("scope", scope),
            ]));
        } else {
            let cancel_reasons = interrupted_reason
                .or(frozen)
                .map(|sig| vec![sig.issue()])
                .unwrap_or_default();
            let mut summary_answer = JsonObject::from([
                ("id".into(), Json::str(&req.parsed.id)),
                ("question".into(), Json::str(req.parsed.kind_wire())),
                ("status".into(), Json::str("undetermined")),
                ("outputs".into(), Json::Obj(JsonObject::new())),
            ]);
            if !cancel_reasons.is_empty() {
                summary_answer.insert("reasons".into(), Json::Arr(cancel_reasons.clone()));
            }
            summary_answers.push(Json::Obj(summary_answer));

            saved_answers.push(Json::obj([
                ("id", Json::str(&req.parsed.id)),
                ("status", Json::str("undetermined")),
                ("outputs", Json::Obj(JsonObject::new())),
                ("reasons", Json::Arr(cancel_reasons)),
                ("scope", scope),
            ]));
        }
    }

    let mut summary_fields = JsonObject::from([
        ("format".into(), Json::str("archsig.summary/1")),
        ("status".into(), Json::str(status.wire())),
        ("exit_code".into(), Json::Nat(u64::from(code))),
        ("answers".into(), Json::Arr(summary_answers)),
    ]);
    if !top_issues.is_empty() {
        summary_fields.insert("issues".into(), Json::Arr(top_issues.clone()));
    }
    if !warnings.is_empty() {
        summary_fields.insert("warnings".into(), Json::Arr(warnings.clone()));
    }
    let summary = Json::Obj(summary_fields);

    let Some(out) = &args.inputs.out else {
        return Outcome {
            status,
            exit_code: code,
            result: None,
            issues: top_issues,
            summary: Some(summary),
        };
    };

    let sources = checked.sources();
    let mut copies: Vec<(String, &[u8])> = sources
        .definitions()
        .iter()
        .enumerate()
        .map(|(i, b)| (format!("inputs/definitions/{i}.json"), b.bytes()))
        .collect();
    copies.push(("inputs/law.law".into(), sources.law().bytes()));
    copies.push(("inputs/archmap.json".into(), sources.archmap().bytes()));

    let mut identities = checked.inputs().to_vec();
    for identity in &mut identities {
        identity.path = Some(match identity.id.as_str() {
            "law" => "inputs/law.law".into(),
            "archmap" => "inputs/archmap.json".into(),
            id => format!(
                "inputs/definitions/{}.json",
                id.strip_prefix("definition").expect("検査済み入力ID")
            ),
        });
    }

    let mut document = JsonObject::from([
        (
            "format".into(),
            Json::str(archsig_input::result::RESULT_FORMAT),
        ),
        ("semantics".into(), Json::str(archsig_input::law::SEMANTICS)),
        ("command".into(), Json::str("run")),
        ("status".into(), Json::str(status.wire())),
        ("exit_code".into(), Json::Nat(u64::from(code))),
        (
            "inputs".into(),
            Json::Arr(identities.iter().map(|i| i.wire()).collect()),
        ),
        ("requests".into(), Json::Arr(saved_requests)),
        ("answers".into(), Json::Arr(saved_answers)),
        ("nodes".into(), Json::Arr(saved_nodes)),
        ("issues".into(), Json::Arr(top_issues.clone())),
    ]);
    if !warnings.is_empty() {
        document.insert("warnings".into(), Json::Arr(warnings));
    }

    let copies_ref: Vec<_> = copies
        .iter()
        .map(|(name, bytes)| (name.as_str(), *bytes))
        .collect();
    let receipt_issues = if matches!(status, Status::Error | Status::Interrupted) {
        top_issues
    } else {
        Vec::new()
    };

    output::publish(
        io,
        out,
        Json::Obj(document),
        &copies_ref,
        Outcome {
            status,
            exit_code: code,
            result: Some(out.join("result.json")),
            summary: Some(summary),
            issues: receipt_issues,
        },
    )
}

fn usage_issue(request_id: Option<&str>, message: &str) -> Json {
    let mut obj = JsonObject::from([
        ("code".into(), Json::str("usage")),
        ("message".into(), Json::str(message)),
        ("dependencies".into(), Json::Arr(vec![])),
        ("missing".into(), Json::Arr(vec![])),
        (
            "details".into(),
            Json::obj([("argument", Json::str("--ask"))]),
        ),
    ]);
    if let Some(req) = request_id {
        obj.insert("request".into(), Json::str(req));
    }
    Json::Obj(obj)
}

fn conversion_error_issue(request_id: &str, err: &ValidationError) -> Json {
    let code = match err {
        ValidationError::UnknownRef { .. } => "reference",
        _ => "inconsistent_observation",
    };
    Json::obj([
        ("code", Json::str(code)),
        ("message", Json::str(err.to_string())),
        ("request", Json::str(request_id)),
        ("dependencies", Json::Arr(vec![])),
        ("missing", Json::Arr(vec![])),
        ("details", Json::Obj(JsonObject::new())),
    ])
}

fn silence_reason_issue(request_id: &str, reason: &SilenceReason) -> Json {
    let (code, message) = match reason {
        SilenceReason::UnobservedDependency { slots } => (
            "unobserved",
            format!(
                "unobserved SHIGURE coordinate dependency: {}",
                slots.join(", ")
            ),
        ),
        SilenceReason::NonLinearRationalOrIntegerExistence {
            point_domain,
            detail,
        } => (
            "unsupported_algorithm",
            format!("nonlinear point existence over {point_domain} is out of scope: {detail}"),
        ),
        SilenceReason::InfinitePresentationNotFinitelyReducible { detail } => (
            "unsupported_algorithm",
            format!("presentation is not finitely reducible: {detail}"),
        ),
        SilenceReason::UnsupportedCoeffRing { domain, detail } => (
            "unsupported_algorithm",
            format!("unsupported coefficient ring {domain}: {detail}"),
        ),
        SilenceReason::QuotientIdealOutOfScope { detail } => (
            "unsupported_algorithm",
            format!("quotient ideal membership out of scope: {detail}"),
        ),
        SilenceReason::OpenConditionInInteraction { detail } => (
            "unsupported_algorithm",
            format!("open condition in interaction analysis: {detail}"),
        ),
        SilenceReason::ApplicabilityConditionNotMet { condition, detail } => (
            "unsupported_algorithm",
            format!("applicability condition `{condition}` not met: {detail}"),
        ),
    };
    Json::obj([
        ("code", Json::str(code)),
        ("message", Json::str(message)),
        ("request", Json::str(request_id)),
        ("dependencies", Json::Arr(vec![])),
        ("missing", Json::Arr(vec![])),
        ("details", reason.to_json()),
    ])
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::run::{CheckArgs, FileIo};
    use std::path::PathBuf;
    use std::sync::Arc;
    use std::sync::atomic::AtomicI32;

    struct NoFreezeSignals;
    impl Signals for NoFreezeSignals {
        fn freeze(&mut self) -> Option<archsig_input::result::Signal> {
            None
        }
    }

    #[test]
    fn deliver_shigure_records_cancelled_issue_when_signal_arrives_during_final_task() {
        let dir = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/shigure-ledger");
        let defs = vec![std::fs::read(dir.join("ledger.atoms.json")).unwrap()];
        let law = std::fs::read(dir.join("ledger.law")).unwrap();
        let map = std::fs::read(dir.join("ledger.archmap.json")).unwrap();
        let checked = check_inputs(
            InputSources::from_bytes(defs, law, map),
            &Control::unlimited(),
        )
        .unwrap();
        let task = ShigureConverter::for_task("LedgerMigration.P1AtomicMarked")
            .convert(&checked)
            .unwrap();
        let outcome = execute_shigure_task(&task, ShigureQueryKind::ConditionalSolutionSpace);

        // 最終タスク実行中に SIGINT が到着した状態（interrupted_reason=None, control.stop_reason()=Some(Int)）
        let flag = Arc::new(AtomicI32::new(2));
        let control = Control::from_signal_flag(flag, 2, 15);
        assert_eq!(
            control.stop_reason(),
            Some(archsig_input::result::Signal::Int)
        );

        let req = ResolvedShigureRequest {
            parsed: ParsedShigureRequest {
                id: "p1m".into(),
                text: "p1m=shigure_solve(LedgerMigration.P1AtomicMarked)".into(),
                query_kind: ShigureQueryKind::ConditionalSolutionSpace,
                task_name: "LedgerMigration.P1AtomicMarked".into(),
                snapshot: None,
            },
            resolved_task_name: "LedgerMigration.P1AtomicMarked".into(),
            reading_name: "LedgerMigration".into(),
            task,
        };
        let args = RunArgs {
            inputs: CheckArgs {
                atom_definitions: vec![],
                law: PathBuf::new(),
                archmap: None,
                out: None,
            },
            asks: vec![req.parsed.text.clone()],
            reuse: None,
        };
        let mut io = FileIo;
        let mut sigs = NoFreezeSignals;
        let delivered = deliver_shigure(
            &mut io,
            &mut sigs,
            &args,
            &checked,
            vec![(req, Some(outcome))],
            vec![],
            None,
            &control,
        );
        assert_eq!(delivered.status, Status::Interrupted);
        assert_eq!(delivered.exit_code, 130);
        assert_eq!(
            delivered.issues.len(),
            1,
            "interrupted outcome must carry non-empty cancelled issue"
        );
        assert_eq!(
            delivered.issues[0],
            archsig_input::result::Signal::Int.issue()
        );
        let summary = delivered.summary.expect("completed answer summary kept");
        let Json::Obj(fields) = &summary else {
            panic!("summary must be object");
        };
        let Json::Arr(summary_issues) = fields.get("issues").expect("summary must include issues")
        else {
            panic!("summary issues must be array");
        };
        assert_eq!(summary_issues.len(), 1);
    }
}
