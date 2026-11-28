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
    ShigureConverter, ToShigureArtinTask, ToShigureAtlasTask, ToShigureChevalleyTask,
    ToShigureDiagnosticsTask, ToShigureDiagramTask, ToShigureLiftTask, ToShigureMultisourceTask,
    ToShigureObservationTask, ToShigureOccurrenceTask, ToShigurePartialTask, ToShigurePathTask,
    ToShigureRevisionTask, ToShigureRobustnessTask, ToShigureTask, ToShigureTransferTask,
};
use std::collections::BTreeMap;

pub(super) fn resolve_and_convert(
    checked: &CheckedInputs,
    parsed_requests: Vec<ParsedShigureRequest>,
    signals: &mut dyn Signals,
    control: &Control,
) -> Result<Vec<ResolvedShigureRequest>, Outcome> {
    let max_errors = archsig_common::diagnostic::DEFAULT_MAX_COLLECTED_ERRORS;
    let shigure_decls = checked.law().shigure();
    let mut resolved = Vec::with_capacity(parsed_requests.len());
    let mut errors: Vec<(bool, archsig_common::canonical::Json)> = Vec::new();
    let snapshot_ids: Vec<&str> = checked
        .archmap()
        .snapshots()
        .iter()
        .map(|s| s.id.as_str())
        .collect();

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
                resolve_decl_with_suggestions(&shigure_decls.tasks, "shigure task", &req.task_name)
            }
            ShigureCliQuery::Diagram => resolve_decl_with_suggestions(
                &shigure_decls.diagrams,
                "shigure diagram",
                &req.task_name,
            ),
            ShigureCliQuery::Path => {
                resolve_decl_with_suggestions(&shigure_decls.paths, "shigure path", &req.task_name)
            }
            ShigureCliQuery::Transfer => resolve_decl_with_suggestions(
                &shigure_decls.transfers,
                "shigure transfer",
                &req.task_name,
            ),
            ShigureCliQuery::Robustness => resolve_decl_with_suggestions(
                &shigure_decls.robustness_tasks,
                "shigure robustness",
                &req.task_name,
            ),
            ShigureCliQuery::Chevalley => resolve_decl_with_suggestions(
                &shigure_decls.chevalley_tasks,
                "shigure chevalley",
                &req.task_name,
            ),
            ShigureCliQuery::Observations => resolve_decl_with_suggestions(
                &shigure_decls.observation_tasks,
                "shigure observations",
                &req.task_name,
            ),
            ShigureCliQuery::Lift => resolve_decl_with_suggestions(
                &shigure_decls.lift_tasks,
                "shigure lift",
                &req.task_name,
            ),
            ShigureCliQuery::Artin => resolve_decl_with_suggestions(
                &shigure_decls.artin_tasks,
                "shigure artin",
                &req.task_name,
            ),
            ShigureCliQuery::Diagnostics => resolve_decl_with_suggestions(
                &shigure_decls.diagnostics_tasks,
                "shigure diagnostics",
                &req.task_name,
            ),
            ShigureCliQuery::Atlas => resolve_decl_with_suggestions(
                &shigure_decls.atlas_tasks,
                "shigure atlas",
                &req.task_name,
            ),
            ShigureCliQuery::Occurrence => resolve_decl_with_suggestions(
                &shigure_decls.occurrence_tasks,
                "shigure occurrence",
                &req.task_name,
            ),
            ShigureCliQuery::Partial => resolve_decl_with_suggestions(
                &shigure_decls.partial_tasks,
                "shigure partial",
                &req.task_name,
            ),
            ShigureCliQuery::Revision => resolve_decl_with_suggestions(
                &shigure_decls.revision_tasks,
                "shigure revision",
                &req.task_name,
            ),
            ShigureCliQuery::Multisource => resolve_decl_with_suggestions(
                &shigure_decls.multisource_tasks,
                "shigure multisource",
                &req.task_name,
            ),
        };
        let resolved_task_name = match name_res {
            Ok(name) => name,
            Err((msg, suggestions)) => {
                if errors.len() < max_errors {
                    let mut issue = usage_issue(Some(&req.id), &msg);
                    if let archsig_common::canonical::Json::Obj(fields) = &mut issue
                        && let Some(archsig_common::canonical::Json::Obj(details)) =
                            fields.get_mut("details")
                    {
                        crate::run::diagnostics::attach_suggestions(details, suggestions);
                    }
                    errors.push((true, issue));
                }
                continue;
            }
        };

        if let Some(sid) = &req.snapshot
            && !checked.archmap().snapshots().iter().any(|s| s.id == *sid)
        {
            if errors.len() < max_errors {
                let mut issue = usage_issue(
                    Some(&req.id),
                    &format!(
                        "unknown ArchMap snapshot `{sid}` in SHIGURE request `{}`",
                        req.id
                    ),
                );
                let suggestions = archsig_common::diagnostic::suggest_identifiers(
                    sid,
                    snapshot_ids.iter().copied(),
                    3,
                );
                if let archsig_common::canonical::Json::Obj(fields) = &mut issue
                    && let Some(archsig_common::canonical::Json::Obj(details)) =
                        fields.get_mut("details")
                {
                    crate::run::diagnostics::attach_suggestions(details, suggestions);
                }
                errors.push((true, issue));
            }
            continue;
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
            ShigureCliQuery::Lift => converter
                .convert_lift(checked)
                .map(|t| ResolvedShigurePayload::Lift(Box::new(t))),
            ShigureCliQuery::Artin => converter
                .convert_artin(checked)
                .map(|t| ResolvedShigurePayload::Artin(Box::new(t))),
            ShigureCliQuery::Diagnostics => converter
                .convert_diagnostics(checked)
                .map(|t| ResolvedShigurePayload::Diagnostics(Box::new(t))),
            ShigureCliQuery::Atlas => converter
                .convert_atlas(checked)
                .map(|t| ResolvedShigurePayload::Atlas(Box::new(t))),
            ShigureCliQuery::Occurrence => converter
                .convert_occurrence(checked)
                .map(|t| ResolvedShigurePayload::Occurrence(Box::new(t))),
            ShigureCliQuery::Partial => converter
                .convert_partial(checked)
                .map(|t| ResolvedShigurePayload::Partial(Box::new(t))),
            ShigureCliQuery::Revision => converter
                .convert_revision(checked)
                .map(|t| ResolvedShigurePayload::Revision(Box::new(t))),
            ShigureCliQuery::Multisource => converter
                .convert_multisource(checked)
                .map(|t| ResolvedShigurePayload::Multisource(Box::new(t))),
        };
        let payload = match payload {
            Ok(payload) => payload,
            Err(err) => {
                if errors.len() < max_errors {
                    errors.push((false, conversion_error_issue(&req.id, &err)));
                }
                continue;
            }
        };

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

    if !errors.is_empty() {
        let code = if errors.iter().any(|(is_usage, _)| *is_usage) {
            64
        } else {
            65
        };
        let issues: Vec<_> = errors.into_iter().map(|(_, issue)| issue).collect();
        return Err(output::notify(
            signals,
            Status::Invalid,
            code,
            control.stop_reason(),
            issues,
        ));
    }

    Ok(resolved)
}

fn resolve_decl_with_suggestions<T>(
    decls: &BTreeMap<String, T>,
    kind_label: &str,
    requested: &str,
) -> Result<String, (String, Vec<String>)> {
    if decls.contains_key(requested) {
        return Ok(requested.to_owned());
    }
    let suffix = format!(".{requested}");
    let matches: Vec<&String> = decls.keys().filter(|k| k.ends_with(&suffix)).collect();
    match matches.as_slice() {
        [only] => Ok((*only).clone()),
        [] => {
            let mut pool: Vec<&str> = decls.keys().map(String::as_str).collect();
            for fq in decls.keys() {
                if let Some((_, short)) = fq.rsplit_once('.') {
                    pool.push(short);
                }
            }
            let suggestions = archsig_common::diagnostic::suggest_identifiers(requested, pool, 3);
            let msg = format!(
                "unknown {kind_label} `{requested}`; declared names: [{}]",
                decls.keys().cloned().collect::<Vec<_>>().join(", ")
            );
            Err((msg, suggestions))
        }
        many => Err((
            format!(
                "ambiguous short {kind_label} name `{requested}`; specify full name among [{}]",
                many.iter()
                    .map(|s| s.as_str())
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
            Vec::new(),
        )),
    }
}
