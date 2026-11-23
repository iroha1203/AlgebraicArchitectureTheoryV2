//! `archsig run` から SHIGURE 計算（`shigure_preservation` / `shigure_solve` / `shigure_interaction` /
//! `shigure_diagram` / `shigure_path` / `shigure_transfer` / `shigure_robustness` /
//! `shigure_chevalley` / `shigure_observations`）を実行する最小入口。
//!
//! 責務:
//! - 既存の `crates/computation/src/observed/` へ一切触れずに、`archsig-input::input::check_inputs` →
//!   `archsig-shigure::convert::ShigureConverter` → `archsig-shigure` 各計算核を接続する
//! - 実行仕様 §§1・5–7 に従い、`archsig.summary/1`（stdout）と `archsig.result/4`（`--out` 保存時）および終了コードを返す
//! - `Verdict::Undetermined`（沈黙）をエラーではなく正常な `partial` / exit 2 出力として返す

mod deliver;
mod parse;
mod resolve;

#[cfg(test)]
#[path = "shigure_tests.rs"]
mod tests;

use super::{Io, Outcome, RunArgs, Signals, output, read};
use archsig_common::control::{Checkpoint, Control};
use archsig_input::input::{InputSources, InputStatus, check_inputs};
use archsig_input::result::{ResultIssue, Status};
use archsig_shigure::ir::diagram::CheckedDiagramTask;
use archsig_shigure::ir::observation::CheckedObservationTask;
use archsig_shigure::ir::path::CheckedPathTask;
use archsig_shigure::ir::result::ShigureOutcome;
use archsig_shigure::ir::robustness::{CheckedChevalleyTask, CheckedRobustnessTask};
use archsig_shigure::ir::transfer::CheckedTransferTask;
use archsig_shigure::ir::validate::CheckedShigureTask;
use archsig_shigure::solver::{
    ShigureQueryKind, execute_shigure_task, solve_chevalley_task, solve_diagram_task,
    solve_observation_task, solve_path_task, solve_robustness_task, solve_transfer_task,
};

pub(super) use parse::classify_asks;

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

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ShigureCliQuery {
    Task(ShigureQueryKind),
    Diagram,
    Path,
    Transfer,
    Robustness,
    Chevalley,
    Observations,
}

impl ShigureCliQuery {
    fn kind_wire(self) -> &'static str {
        match self {
            ShigureCliQuery::Task(ShigureQueryKind::SemanticPreservation) => "shigure_preservation",
            ShigureCliQuery::Task(ShigureQueryKind::ConditionalSolutionSpace) => "shigure_solve",
            ShigureCliQuery::Task(ShigureQueryKind::InteractionAnalysis) => "shigure_interaction",
            ShigureCliQuery::Diagram => "shigure_diagram",
            ShigureCliQuery::Path => "shigure_path",
            ShigureCliQuery::Transfer => "shigure_transfer",
            ShigureCliQuery::Robustness => "shigure_robustness",
            ShigureCliQuery::Chevalley => "shigure_chevalley",
            ShigureCliQuery::Observations => "shigure_observations",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct ParsedShigureRequest {
    id: String,
    text: String,
    query: ShigureCliQuery,
    task_name: String,
    snapshot: Option<String>,
}

enum ResolvedShigurePayload {
    Task(CheckedShigureTask, ShigureQueryKind),
    Diagram(CheckedDiagramTask),
    Path(Box<CheckedPathTask>),
    Transfer(CheckedTransferTask),
    Robustness(Box<CheckedRobustnessTask>),
    Chevalley(Box<CheckedChevalleyTask>),
    Observations(Box<CheckedObservationTask>),
}

impl ResolvedShigurePayload {
    fn execute(&self) -> ShigureOutcome {
        match self {
            ResolvedShigurePayload::Task(task, kind) => execute_shigure_task(task, *kind),
            ResolvedShigurePayload::Diagram(task) => solve_diagram_task(task),
            ResolvedShigurePayload::Path(task) => solve_path_task(task),
            ResolvedShigurePayload::Transfer(task) => solve_transfer_task(task),
            ResolvedShigurePayload::Robustness(task) => solve_robustness_task(task),
            ResolvedShigurePayload::Chevalley(task) => solve_chevalley_task(task),
            ResolvedShigurePayload::Observations(task) => solve_observation_task(task),
        }
    }
}

struct ResolvedShigureRequest {
    parsed: ParsedShigureRequest,
    resolved_task_name: String,
    reading_name: String,
    payload: ResolvedShigurePayload,
}

/// SHIGURE 問いと既存の observed 問いを同一 `run` で混在させたときの usage エラー。
pub(super) fn mixed_asks_outcome(signals: &mut dyn Signals, control: &Control) -> Outcome {
    output::notify(
        signals,
        Status::Invalid,
        64,
        control.stop_reason(),
        vec![deliver::usage_issue(
            None,
            "SHIGURE queries (`shigure_preservation`, `shigure_solve`, `shigure_interaction`, `shigure_diagram`, `shigure_path`, `shigure_transfer`, `shigure_robustness`, `shigure_chevalley`, `shigure_observations`) cannot be combined with standard observed queries in the same `archsig run`; invoke them separately",
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
    let parsed_requests = match parse::parse_shigure_requests(&args.asks, signals, control) {
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

    let resolved = match resolve::resolve_and_convert(&checked, parsed_requests, signals, control) {
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
            let outcome = req.payload.execute();
            executed.push((req, Some(outcome)));
        }
    }

    deliver::deliver_shigure(
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
