//! SHIGURE CLI 結果の `archsig.summary/1` と `archsig.result/4` 配送・reading スコープ収集。

use super::{ResolvedShigureRequest, ShigureCliQuery};
use crate::run::{Io, Outcome, RunArgs, Signals, output};
use archsig_common::canonical::{Json, JsonObject};
use archsig_common::control::Control;
use archsig_input::input::CheckedInputs;
use archsig_input::law::shigure::{
    CheckedShigureDecls, ShigureGoodnessSpec, ShigureMorphismBody, ShigurePathQueryMode,
    ShigureRealizationSpace, ShigureTransferStepSource,
};
use archsig_input::result::{Signal, Status, exit_code};
use archsig_shigure::ir::result::{ShigureOutcome, SilenceReason, Verdict};
use archsig_shigure::ir::validate::ValidationError;
use std::collections::BTreeSet;

#[allow(clippy::too_many_arguments)]
pub(super) fn deliver_shigure(
    io: &mut dyn Io,
    signals: &mut dyn Signals,
    args: &RunArgs,
    checked: &CheckedInputs,
    executed: Vec<(ResolvedShigureRequest, Option<ShigureOutcome>)>,
    warnings: Vec<Json>,
    interrupted_reason: Option<Signal>,
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
            ("kind", Json::str(req.parsed.query.kind_wire())),
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
                if origin_ref.law_declaration.is_none()
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
        let scope_readings = collect_scope_readings(
            checked.law().shigure(),
            req.parsed.query,
            &req.resolved_task_name,
            &req.reading_name,
            outcome_opt.as_ref(),
        );
        let scope = Json::obj([
            (
                "readings",
                Json::Arr(scope_readings.into_iter().map(Json::str).collect()),
            ),
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
                ("question".into(), Json::str(req.parsed.query.kind_wire())),
                ("status".into(), Json::str(outcome.verdict.wire())),
                (
                    "outputs".into(),
                    Json::obj([(
                        "shigure",
                        if crate::cli::active_detail_level()
                            == Some(crate::cli::DetailLevel::Concise)
                        {
                            super::concise::trim_shigure_outcome_concise(&outcome_json)
                        } else {
                            outcome_json.clone()
                        },
                    )]),
                ),
            ]);
            if !answer_reasons.is_empty() {
                summary_answer.insert(
                    "reasons".into(),
                    Json::Arr(answer_reasons.iter().map(summary_issue).collect()),
                );
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
                ("question".into(), Json::str(req.parsed.query.kind_wire())),
                ("status".into(), Json::str("undetermined")),
                ("outputs".into(), Json::Obj(JsonObject::new())),
            ]);
            if !cancel_reasons.is_empty() {
                summary_answer.insert(
                    "reasons".into(),
                    Json::Arr(cancel_reasons.iter().map(summary_issue).collect()),
                );
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
        summary_fields.insert(
            "issues".into(),
            Json::Arr(top_issues.iter().map(summary_issue).collect()),
        );
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

/// `archsig.summary/1` の理由・通知から `dependencies` を除く（実行仕様 §5）。
fn summary_issue(issue: &Json) -> Json {
    let Json::Obj(fields) = issue else {
        return issue.clone();
    };
    Json::Obj(
        fields
            .iter()
            .filter(|(k, _)| k.as_str() != "dependencies")
            .map(|(k, v)| (k.clone(), v.clone()))
            .collect(),
    )
}

/// cross-reading 宣言を含め、計算に関与した全 reading 名を収集する。
fn collect_scope_readings(
    decls: &CheckedShigureDecls,
    query: ShigureCliQuery,
    task_name: &str,
    task_reading: &str,
    outcome: Option<&ShigureOutcome>,
) -> Vec<String> {
    let mut readings = BTreeSet::from([task_reading.to_owned()]);
    let push_decl = |qname: &str, out_readings: &mut BTreeSet<String>| {
        if let Some((r, _)) = qname.split_once('.') {
            out_readings.insert(r.to_owned());
        }
    };
    if let Some(out) = outcome {
        for origin_ref in &out.provenance.origins {
            if let Some(decl) = &origin_ref.law_declaration {
                push_decl(decl, &mut readings);
            }
        }
    } else {
        collect_decl_readings(decls, query, task_name, &mut readings, &push_decl);
    }
    readings.into_iter().collect()
}

fn collect_decl_readings(
    decls: &CheckedShigureDecls,
    query: ShigureCliQuery,
    task_name: &str,
    readings: &mut BTreeSet<String>,
    push_decl: &dyn Fn(&str, &mut BTreeSet<String>),
) {
    let push_cmp = |cmp_name: &str, out_r: &mut BTreeSet<String>| {
        push_decl(cmp_name, out_r);
        if let Some(cmp) = decls.comparisons.get(cmp_name) {
            push_decl(&cmp.before, out_r);
            push_decl(&cmp.after, out_r);
        }
    };
    let push_morph = |body: &ShigureMorphismBody, out_r: &mut BTreeSet<String>| {
        if let ShigureMorphismBody::Comparison(c) = body {
            push_cmp(c, out_r);
        }
    };
    let push_family = |fam_name: &str, out_r: &mut BTreeSet<String>| {
        push_decl(fam_name, out_r);
        if let Some(fam) = decls.families.get(fam_name) {
            if let ShigureRealizationSpace::FiniteMembers(members) = &fam.realizations.space {
                for m in members {
                    if let Some(pres) = &m.presentation {
                        push_decl(pres, out_r);
                    }
                }
            }
            let pres_opt = match &fam.goodness {
                ShigureGoodnessSpec::Direct { preservation, .. }
                | ShigureGoodnessSpec::Existential { preservation, .. } => preservation.as_ref(),
            };
            if let Some(p) = pres_opt {
                push_cmp(&p.comparison, out_r);
                push_decl(&p.change_spec, out_r);
            }
        }
    };
    match query {
        ShigureCliQuery::Task(_) => {
            if let Some(task) = decls.tasks.get(task_name) {
                push_cmp(&task.comparison, readings);
                push_decl(&task.change_spec, readings);
                if let Some(ec) = &task.eval_condition {
                    push_decl(ec, readings);
                }
            }
        }
        ShigureCliQuery::Diagram => {
            if let Some(d) = decls.diagrams.get(task_name) {
                push_decl(&d.change_spec, readings);
                if let Some(ec) = &d.eval_condition {
                    push_decl(ec, readings);
                }
                for ec in d.edge_eval_conditions.values() {
                    push_decl(ec, readings);
                }
                for v in &d.vertices {
                    push_decl(&v.presentation, readings);
                }
                for e in &d.edges {
                    push_morph(&e.morphism, readings);
                }
            }
        }
        ShigureCliQuery::Path => {
            if let Some(p) = decls.paths.get(task_name) {
                push_decl(&p.change_spec, readings);
                if let Some(ec) = &p.eval_condition {
                    push_decl(ec, readings);
                }
                for pres in p.vertices.values() {
                    push_decl(pres, readings);
                }
                for rule in &p.rules {
                    push_morph(&rule.morphism, readings);
                    if let Some(ec) = &rule.eval_condition {
                        push_decl(ec, readings);
                    }
                }
                if let ShigurePathQueryMode::Subdivide { target_edge } = &p.query_mode {
                    push_morph(target_edge, readings);
                }
                if let Some(proto) = &p.protocol {
                    push_cmp(&proto.comparison, readings);
                }
            }
        }
        ShigureCliQuery::Transfer => {
            if let Some(tr) = decls.transfers.get(task_name) {
                push_decl(&tr.change_spec, readings);
                if let Some(ec) = &tr.eval_condition {
                    push_decl(ec, readings);
                }
                for st in &tr.steps {
                    match &st.source {
                        ShigureTransferStepSource::Comparison(c) => push_cmp(c, readings),
                        ShigureTransferStepSource::Inline {
                            before,
                            after,
                            morphism,
                        } => {
                            push_decl(before, readings);
                            push_decl(after, readings);
                            push_morph(morphism, readings);
                        }
                    }
                }
            }
        }
        ShigureCliQuery::Robustness => {
            if let Some(rob) = decls.robustness_tasks.get(task_name) {
                push_family(&rob.family, readings);
            }
        }
        ShigureCliQuery::Chevalley => {
            if let Some(chev) = decls.chevalley_tasks.get(task_name) {
                push_family(&chev.family, readings);
            }
        }
        ShigureCliQuery::Observations => {
            if let Some(obs) = decls.observation_tasks.get(task_name) {
                push_family(&obs.family, readings);
            }
        }
        ShigureCliQuery::Lift
        | ShigureCliQuery::Artin
        | ShigureCliQuery::Diagnostics
        | ShigureCliQuery::Atlas
        | ShigureCliQuery::Occurrence
        | ShigureCliQuery::Partial
        | ShigureCliQuery::Revision
        | ShigureCliQuery::Multisource => {}
    }
}

pub(super) fn usage_issue(request_id: Option<&str>, message: &str) -> Json {
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

pub(super) fn conversion_error_issue(request_id: &str, err: &ValidationError) -> Json {
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
        SilenceReason::UnboundedSearchOutOfScope { detail } => (
            "unsupported_algorithm",
            format!("unbounded search out of scope: {detail}"),
        ),
        SilenceReason::ConstructibleStratificationOutOfScope { detail } => (
            "unsupported_algorithm",
            format!("constructible stratification out of scope: {detail}"),
        ),
        SilenceReason::FiniteEnumerationOutOfScope { detail } => (
            "unsupported_algorithm",
            format!("finite enumeration out of scope: {detail}"),
        ),
        SilenceReason::UniversalRingOutOfScope { detail } => (
            "unsupported_algorithm",
            format!("universal ring stability out of scope: {detail}"),
        ),
        SilenceReason::NonNoetherianInfinitePresentation { detail } => (
            "unsupported_algorithm",
            format!("non-Noetherian infinite presentation: {detail}"),
        ),
        SilenceReason::SquareZeroConditionViolated { detail } => (
            "unsupported_algorithm",
            format!("square-zero condition violated: {detail}"),
        ),
        SilenceReason::SyzygyOutOfScope { detail } => (
            "unsupported_algorithm",
            format!("syzygy computation out of scope: {detail}"),
        ),
        SilenceReason::ArtinOrderOutOfScope { detail } => (
            "unsupported_algorithm",
            format!("Artin order computation out of scope: {detail}"),
        ),
        SilenceReason::DiagnosticsStratificationOutOfScope { detail } => (
            "unsupported_algorithm",
            format!("diagnostics stratification out of scope: {detail}"),
        ),
        SilenceReason::DisconnectedGraphOutOfScope { detail } => (
            "unsupported_algorithm",
            format!("disconnected graph out of scope: {detail}"),
        ),
        SilenceReason::UnsupportedCompletionClass { detail } => (
            "unsupported_algorithm",
            format!("unsupported completion class: {detail}"),
        ),
        SilenceReason::OperatorNotUniquelyDetermined { detail } => (
            "unsupported_algorithm",
            format!("operator is not uniquely determined by common part: {detail}"),
        ),
        SilenceReason::OperatorRevisionReuseRejected { detail } => (
            "unsupported_algorithm",
            format!("SNF factorization reuse rejected on operator revision: {detail}"),
        ),
        SilenceReason::ApplicabilityConditionNotMet { condition, detail } => (
            "unsupported_algorithm",
            format!("applicability condition `{condition}` not met: {detail}"),
        ),
        SilenceReason::ResourceLimitExceeded {
            limit_name,
            limit,
            observed,
            detail,
        } => (
            "resource_limit_exceeded",
            format!(
                "resource limit `{limit_name}` exceeded (limit={limit}, observed={observed}): {detail}"
            ),
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
