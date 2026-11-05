//! 検査済み三入力から観測評価と公開結果の配送を接続する。

use super::{Io, Outcome, RunArgs, Signals, output, read};
use archsig_common::canonical::Json;
use archsig_common::control::Control;
use archsig_computation::observed::{
    EvaluationFailure, ObservedEvaluation, PrepareFailure, evaluate_observed, prepare_observed,
    request::{ResolveFailure, check_request_syntax},
};
use archsig_input::input::{InputSources, InputStatus};
use archsig_input::result::{ResultIssue, Status, exit_code};

pub fn run_internal_outcome(signals: &mut dyn Signals) -> Outcome {
    failure(
        signals,
        "run",
        "internal failure during computation".to_owned(),
    )
}

fn failure(signals: &mut dyn Signals, operation: &str, message: String) -> Outcome {
    output::without_result(
        signals,
        Status::Error,
        vec![ResultIssue::Internal {
            operation: operation.to_owned(),
            message,
        }],
    )
}

pub fn run_requests(
    io: &mut dyn Io,
    signals: &mut dyn Signals,
    args: &RunArgs,
    control: &Control,
) -> Outcome {
    if let Err(error) = super::args::validate_run(args) {
        return super::usage_outcome(io, signals, error);
    }
    run_requests_validated(io, signals, args, control)
}

pub(super) fn run_requests_validated(
    io: &mut dyn Io,
    signals: &mut dyn Signals,
    args: &RunArgs,
    control: &Control,
) -> Outcome {
    let texts: Vec<_> = args.asks.iter().map(String::as_str).collect();
    if let Err(error) = check_request_syntax(&texts, control) {
        return request_failure(signals, error, control);
    }
    let map_path = args.inputs.archmap.as_ref().expect("検査済みrunのArchMap");
    let mut issues = Vec::new();
    let definitions: Vec<_> = args
        .inputs
        .atom_definitions
        .iter()
        .map(|p| read(p, &mut issues))
        .collect();
    let law = read(&args.inputs.law, &mut issues);
    let map = read(map_path, &mut issues);
    if !issues.is_empty() {
        return output::without_result(signals, Status::Error, issues);
    }
    let sources = InputSources::from_bytes(
        definitions.into_iter().flatten().collect(),
        law.expect("読込成功を確認したLaw"),
        map.expect("読込成功を確認したArchMap"),
    );
    let prepared = match prepare_observed(sources, &texts, control) {
        Ok(prepared) => prepared,
        Err(PrepareFailure::Inputs(failure)) => {
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
        Err(PrepareFailure::Requests { failure: error, .. }) => {
            return request_failure(signals, error, control);
        }
    };
    let candidate = match super::reuse::inspect(args.reuse.as_deref(), control) {
        Ok(rejected) => rejected,
        Err(reason) => {
            return output::notify(
                signals,
                Status::Interrupted,
                75,
                control.stop_reason(),
                vec![reason.issue()],
            );
        }
    };
    let evaluation = match evaluate_observed(prepared, control) {
        Ok(result) => result,
        Err(EvaluationFailure::NotImplemented { partial, .. }) => *partial,
        Err(EvaluationFailure::Prepare(_)) => {
            return failure(
                signals,
                "run",
                "input preparation was repeated while evaluating checked requests".into(),
            );
        }
    };
    let verification = candidate.verify(&evaluation, control);
    deliver(io, signals, args, evaluation, verification, control)
}

fn request_failure(signals: &mut dyn Signals, error: ResolveFailure, control: &Control) -> Outcome {
    match error {
        ResolveFailure::Invalid { issues, .. } => output::notify(
            signals,
            Status::Invalid,
            64,
            control.stop_reason(),
            issues.iter().map(|i| i.wire()).collect(),
        ),
        ResolveFailure::Interrupted { reason } => output::notify(
            signals,
            Status::Interrupted,
            75,
            control.stop_reason(),
            vec![reason.issue()],
        ),
        ResolveFailure::NotApplicable {
            request,
            kind,
            architecture_environment,
        } => failure(
            signals,
            "run",
            format!(
                "computation for request `{request}` of kind `{kind}`{} is not implemented",
                if architecture_environment {
                    " (Architecture environment)"
                } else {
                    ""
                }
            ),
        ),
    }
}

fn deliver(
    io: &mut dyn Io,
    signals: &mut dyn Signals,
    args: &RunArgs,
    evaluation: ObservedEvaluation,
    verification: super::reuse::Verification,
    control: &Control,
) -> Outcome {
    let super::reuse::Verification {
        rejected,
        stop: reuse_stop,
        replay,
    } = verification;
    let (mut status, mut code) = match evaluation.status() {
        "complete" => (Status::Complete, u8::from(evaluation.has_refuted_answer())),
        "partial" => (Status::Partial, 2),
        "interrupted" => (Status::Interrupted, 75),
        _ => (Status::Error, 70),
    };
    let mut issues: Vec<Json> = evaluation.issues_wire();
    if let Some(reason) = &reuse_stop {
        status = Status::Interrupted;
        code = 75;
        issues.push(reason.issue());
    }
    let internal = evaluation.has_internal_issue();
    if ((internal || status == Status::Error) && !evaluation.has_nodes())
        || (status == Status::Interrupted && !evaluation.has_nodes())
    {
        // 保存しない計算の参照や未決理由は通知へ持ち出さず、停止原因だけを返す。
        let mut issues = evaluation.failure_notifications();
        if let Some(reason) = reuse_stop {
            issues.push(reason.issue());
        }
        return output::notify(signals, status, code, control.stop_reason(), issues);
    }
    let frozen = signals.freeze();
    if let Some(signal) = control.stop_reason().or(frozen) {
        status = Status::Interrupted;
        code = exit_code(status, Some(signal), &[]);
        if control.stop_reason().is_none() {
            issues.push(signal.issue());
        }
    }
    output::sort_issues(&mut issues);
    let mut summary = evaluation.summary_wire(status.wire(), code, &issues);
    if !rejected.is_empty()
        && let Json::Obj(fields) = &mut summary
    {
        fields.insert("warnings".into(), Json::Arr(rejected.clone()));
    }
    let Some(out) = &args.inputs.out else {
        let mut notifications = evaluation.failure_notifications();
        if let Some(signal) = control.stop_reason().or(frozen)
            && !notifications.iter().any(|issue| issue == &signal.issue())
        {
            notifications.push(signal.issue());
        }
        return Outcome {
            status,
            exit_code: code,
            result: None,
            issues: notifications,
            summary: Some(summary),
        };
    };
    let inputs = evaluation.prepared().shared_inputs();
    let sources = inputs.sources();
    let mut copies: Vec<(String, &[u8])> = sources
        .definitions()
        .iter()
        .enumerate()
        .map(|(i, b)| (format!("inputs/definitions/{i}.json"), b.bytes()))
        .collect();
    copies.push(("inputs/law.law".into(), sources.law().bytes()));
    copies.push(("inputs/archmap.json".into(), sources.archmap().bytes()));
    let mut identities = inputs.inputs().to_vec();
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
    // 型付き結果の最終表示。以後このJSONから値・命題を評価しない。
    let mut wire = replay.unwrap_or_else(|| evaluation.result_wire());
    let Json::Obj(document) = &mut wire else {
        unreachable!("結果表示はobject")
    };
    document.insert(
        "inputs".into(),
        Json::Arr(identities.iter().map(|i| i.wire()).collect()),
    );
    for (key, value) in [
        ("format", Json::str(archsig_input::result::RESULT_FORMAT)),
        ("semantics", Json::str(archsig_input::law::SEMANTICS)),
        ("command", Json::str("run")),
        ("status", Json::str(status.wire())),
        ("exit_code", Json::Nat(u64::from(code))),
    ] {
        document.insert(key.into(), value);
    }
    if !rejected.is_empty() {
        document.insert("warnings".into(), Json::Arr(rejected));
    }
    let Json::Arr(saved_issues) = document.get_mut("issues").unwrap() else {
        unreachable!()
    };
    if let Some(reason) = reuse_stop {
        saved_issues.push(reason.issue());
    }
    if control.stop_reason().is_none()
        && let Some(signal) = frozen
    {
        saved_issues.push(signal.issue());
    }
    let copies: Vec<_> = copies
        .iter()
        .map(|(name, bytes)| (name.as_str(), *bytes))
        .collect();
    let receipt_issues = if matches!(status, Status::Error | Status::Interrupted) {
        saved_issues.clone()
    } else {
        Vec::new()
    };
    let outcome = Outcome {
        status,
        exit_code: code,
        result: Some(out.join("result.json")),
        summary: Some(summary),
        issues: receipt_issues,
    };
    drop(evaluation);
    output::publish(io, out, wire, &copies, outcome)
}

#[cfg(test)]
mod tests;
