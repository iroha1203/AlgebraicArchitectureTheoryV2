//! 検査済み三入力から観測評価と公開結果の配送を接続する。

use super::{Io, Outcome, RunArgs, Signals, output, read};
use crate::canonical::Json;
use crate::observed::{
    EvaluationFailure, ObservedEvaluation, PrepareFailure,
    control::{Control, StopReason},
    evaluate_observed,
    input::{InputSources, InputStatus},
    prepare_observed,
    request::ResolveFailure,
    result::Decision,
};
use crate::result::{ResultIssue, Signal, Status, exit_code};
use std::collections::BTreeMap;
use std::time::Instant;

pub fn run_internal_outcome(signals: &mut dyn Signals) -> Outcome {
    failure(signals, "run", "計算の途中で内部障害が起きた".to_owned())
}

fn failure(signals: &mut dyn Signals, operation: &str, message: String) -> Outcome {
    output::without_result(
        signals,
        Status::Error,
        vec![ResultIssue::Internal {
            operation: operation.to_owned(),
            message,
        }],
        Vec::new(),
    )
}

fn prior_signal(control: &Control) -> Option<Signal> {
    match control.stop_reason() {
        Some(StopReason::Cancelled(s)) => Some(s),
        _ => None,
    }
}

pub fn run_requests(
    io: &mut dyn Io,
    signals: &mut dyn Signals,
    args: &RunArgs,
    started: Instant,
    control: &mut Control,
) -> Outcome {
    let usage = |argument: &str, message: String| ResultIssue::Usage {
        argument: argument.to_owned(),
        message,
    };
    if let Err(message) = output::out_ok(&args.inputs.out) {
        return output::usage_without_result(
            signals,
            usage("--out", format!("{}: {message}", args.inputs.out.display())),
            Vec::new(),
        );
    }
    let Some(map_path) = &args.inputs.archmap else {
        return output::usage_without_result(
            signals,
            usage("--archmap", "run は --archmap が必要".into()),
            Vec::new(),
        );
    };
    if args.inputs.atom_definitions.is_empty() || args.asks.is_empty() {
        let argument = if args.inputs.atom_definitions.is_empty() {
            "--atom-definition"
        } else {
            "--ask"
        };
        return output::usage_without_result(
            signals,
            usage(argument, format!("{argument} が一つ以上必要")),
            Vec::new(),
        );
    }
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
        return output::without_result(signals, Status::Error, issues, Vec::new());
    }
    let sources = InputSources::from_bytes(
        definitions.into_iter().flatten().collect(),
        law.expect("読込成功を確認したLaw"),
        map.expect("読込成功を確認したArchMap"),
    );
    let texts: Vec<_> = args.asks.iter().map(String::as_str).collect();
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
                prior_signal(control),
                failure.issues().to_vec(),
                Vec::new(),
            );
        }
        Err(PrepareFailure::Requests {
            failure: request_failure,
            ..
        }) => match request_failure {
            ResolveFailure::Invalid {
                issues,
                stop_reason,
                ..
            } => {
                let mut issues: Vec<_> = issues.iter().map(|i| i.wire()).collect();
                if let Some(reason) = stop_reason {
                    issues.push(reason.wire());
                }
                return output::notify(
                    signals,
                    Status::Invalid,
                    64,
                    prior_signal(control),
                    issues,
                    Vec::new(),
                );
            }
            ResolveFailure::Interrupted { reason } => {
                return output::notify(
                    signals,
                    Status::Interrupted,
                    75,
                    prior_signal(control),
                    vec![reason.wire()],
                    Vec::new(),
                );
            }
            ResolveFailure::NotApplicable {
                request,
                kind,
                architecture_environment,
            } => {
                return failure(
                    signals,
                    "run",
                    format!(
                        "問い `{request}` の `{kind}`{}の計算経路は未実装",
                        if architecture_environment {
                            "（Architecture環境）"
                        } else {
                            ""
                        }
                    ),
                );
            }
        },
    };
    let candidate = match super::reuse::inspect(args.reuse.as_deref(), control) {
        Ok(rejected) => rejected,
        Err(reason) => {
            return output::notify(
                signals,
                Status::Interrupted,
                75,
                prior_signal(control),
                vec![reason.wire()],
                Vec::new(),
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
                "検査済み要求の評価中に入力準備が再実行された".into(),
            );
        }
    };
    let (rejected, reuse_stop) = candidate.verify(&evaluation, control);
    deliver(
        io, signals, args, evaluation, rejected, reuse_stop, started, control,
    )
}

fn deliver(
    io: &mut dyn Io,
    signals: &mut dyn Signals,
    args: &RunArgs,
    evaluation: ObservedEvaluation,
    rejected: Vec<Json>,
    reuse_stop: Option<StopReason>,
    started: Instant,
    control: &Control,
) -> Outcome {
    let elapsed_ms = started.elapsed().as_millis();
    let peak_bytes = output::peak_rss_bytes();
    let (mut status, mut code) = match evaluation.status() {
        "complete" => (
            Status::Complete,
            u8::from(
                evaluation
                    .answers
                    .iter()
                    .any(|a| a.status == Decision::Refuted),
            ),
        ),
        "partial" => (Status::Partial, 2),
        "interrupted" => (Status::Interrupted, 75),
        _ => (Status::Error, 70),
    };
    let mut issues: Vec<Json> = evaluation.issues.iter().map(|i| i.wire()).collect();
    if let Some(reason) = reuse_stop {
        if status != Status::Error || matches!(reason, StopReason::Cancelled(_)) {
            status = Status::Interrupted;
            code = 75;
        }
        issues.push(reason.wire());
    }
    if matches!(status, Status::Interrupted | Status::Error) && evaluation.nodes.is_empty() {
        return output::notify(
            signals,
            status,
            code,
            prior_signal(control),
            issues,
            Vec::new(),
        );
    }
    let frozen = signals.freeze();
    if let Some(signal) = prior_signal(control).or(frozen) {
        status = Status::Interrupted;
        code = exit_code(status, Some(signal), &[]);
        if prior_signal(control).is_none() {
            issues.push(ResultIssue::Cancelled(signal).wire());
        }
    }
    output::sort_issues(&mut issues);
    let inputs = evaluation.prepared().inputs();
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
    let mut wire = evaluation.wire();
    let Json::Obj(document) = &mut wire else {
        unreachable!("結果表示はobject")
    };
    document.insert(
        "inputs".into(),
        Json::Arr(identities.iter().map(|i| i.wire()).collect()),
    );
    for (key, value) in [
        ("format", Json::str("archsig.result/2")),
        ("semantics", Json::str(crate::law::SEMANTICS)),
        (
            "producer",
            Json::obj([
                ("version", Json::str(env!("CARGO_PKG_VERSION"))),
                (
                    "build",
                    Json::str(concat!(
                        env!("CARGO_PKG_NAME"),
                        "-",
                        env!("CARGO_PKG_VERSION")
                    )),
                ),
            ]),
        ),
        ("command", Json::str("run")),
        ("status", Json::str(status.wire())),
        ("exit_code", Json::Nat(u64::from(code))),
        ("issues", Json::Arr(issues.clone())),
        (
            "reuse",
            Json::obj([
                ("requested", Json::Bool(args.reuse.is_some())),
                ("accepted_nodes", Json::Nat(0)),
                ("recomputed_nodes", Json::Nat(evaluation.nodes.len() as u64)),
                ("rejected", Json::Arr(rejected)),
            ]),
        ),
        (
            "usage",
            Json::obj([
                ("elapsed_ms", Json::str(elapsed_ms.to_string())),
                ("peak_bytes", Json::str(peak_bytes.to_string())),
            ]),
        ),
    ] {
        document.insert(key.into(), value);
    }
    let mut limits = BTreeMap::new();
    if let Some(n) = &args.time_ms {
        limits.insert("time_ms".into(), Json::str(n));
    }
    if let Some(n) = &args.memory_mib {
        limits.insert("memory_mib".into(), Json::str(n));
    }
    document.insert("limits".into(), Json::Obj(limits));
    let copies: Vec<_> = copies
        .iter()
        .map(|(name, bytes)| (name.as_str(), *bytes))
        .collect();
    let receipt_issues = if matches!(status, Status::Error | Status::Interrupted) {
        issues
    } else {
        Vec::new()
    };
    output::publish(
        io,
        &args.inputs.out,
        wire,
        &copies,
        Outcome {
            status,
            exit_code: code,
            result: Some(args.inputs.out.join("result.json")),
            stderr: Vec::new(),
            issues: receipt_issues,
        },
    )
}
