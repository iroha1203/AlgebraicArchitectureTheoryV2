//! SHIGURE CLI 問いの宣言名解決と IR 変換。

use super::deliver::{conversion_error_issue, usage_issue};
use super::{
    ParsedShigureRequest, ResolvedShigurePayload, ResolvedShigureRequest, ShigureCliQuery,
};
use crate::run::{Outcome, Signals, output};
use archsig_common::control::{Checkpoint, Control};
use archsig_input::input::CheckedInputs;
use archsig_input::result::Status;
use archsig_shigure::convert::{
    ShigureConverter, ToShigureChevalleyTask, ToShigureDiagramTask, ToShigureObservationTask,
    ToShigurePathTask, ToShigureRobustnessTask, ToShigureTask, ToShigureTransferTask,
};
use std::collections::BTreeMap;

pub(super) fn resolve_and_convert(
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

        let name_res = match req.query {
            ShigureCliQuery::Task(_) => {
                resolve_decl_name(&shigure_decls.tasks, "shigure task", &req.task_name)
            }
            ShigureCliQuery::Diagram => {
                resolve_decl_name(&shigure_decls.diagrams, "shigure diagram", &req.task_name)
            }
            ShigureCliQuery::Path => {
                resolve_decl_name(&shigure_decls.paths, "shigure path", &req.task_name)
            }
            ShigureCliQuery::Transfer => {
                resolve_decl_name(&shigure_decls.transfers, "shigure transfer", &req.task_name)
            }
            ShigureCliQuery::Robustness => resolve_decl_name(
                &shigure_decls.robustness_tasks,
                "shigure robustness",
                &req.task_name,
            ),
            ShigureCliQuery::Chevalley => resolve_decl_name(
                &shigure_decls.chevalley_tasks,
                "shigure chevalley",
                &req.task_name,
            ),
            ShigureCliQuery::Observations => resolve_decl_name(
                &shigure_decls.observation_tasks,
                "shigure observations",
                &req.task_name,
            ),
        };
        let resolved_task_name = name_res.map_err(|msg| {
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
        let payload = match req.query {
            ShigureCliQuery::Task(kind) => converter
                .convert(checked)
                .map(|task| ResolvedShigurePayload::Task(task, kind)),
            ShigureCliQuery::Diagram => converter
                .convert_diagram(checked)
                .map(ResolvedShigurePayload::Diagram),
            ShigureCliQuery::Path => converter
                .convert_path(checked)
                .map(|p| ResolvedShigurePayload::Path(Box::new(p))),
            ShigureCliQuery::Transfer => converter
                .convert_transfer(checked)
                .map(ResolvedShigurePayload::Transfer),
            ShigureCliQuery::Robustness => converter
                .convert_robustness(checked)
                .map(|t| ResolvedShigurePayload::Robustness(Box::new(t))),
            ShigureCliQuery::Chevalley => converter
                .convert_chevalley(checked)
                .map(|t| ResolvedShigurePayload::Chevalley(Box::new(t))),
            ShigureCliQuery::Observations => converter
                .convert_observation(checked)
                .map(|t| ResolvedShigurePayload::Observations(Box::new(t))),
        }
        .map_err(|err| {
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
            payload,
        });
    }

    Ok(resolved)
}

fn resolve_decl_name<T>(
    decls: &BTreeMap<String, T>,
    kind_label: &str,
    requested: &str,
) -> Result<String, String> {
    if decls.contains_key(requested) {
        return Ok(requested.to_owned());
    }
    let suffix = format!(".{requested}");
    let matches: Vec<&String> = decls.keys().filter(|k| k.ends_with(&suffix)).collect();
    match matches.as_slice() {
        [only] => Ok((*only).clone()),
        [] => Err(format!(
            "unknown {kind_label} `{requested}`; declared names: [{}]",
            decls.keys().cloned().collect::<Vec<_>>().join(", ")
        )),
        many => Err(format!(
            "ambiguous short {kind_label} name `{requested}`; specify full name among [{}]",
            many.iter()
                .map(|s| s.as_str())
                .collect::<Vec<_>>()
                .join(", ")
        )),
    }
}
