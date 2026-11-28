//! SHIGURE 宣言群の複数エラー一括収集。

use super::check::{
    DeclCategory, ShigureDeclCtx, check_change_spec, check_comparison, check_diagram,
    check_eval_condition, check_path, check_presentation, check_task, check_transfer,
};
use super::*;
use crate::law::check::{Checker, check_decl_name, duplicate, full};
use archsig_common::control::{CheckFailure, Checkpoint, Control};
use archsig_common::issue::Issue;
use std::collections::HashMap;

type E = CheckFailure<Box<Issue>>;

fn push_err(issues: &mut Vec<Issue>, max_errors: usize, err: E) -> Result<(), CheckFailure<()>> {
    match err {
        CheckFailure::Stopped(reason) => Err(CheckFailure::Stopped(reason)),
        CheckFailure::Input(issue) => {
            if issues.len() < max_errors {
                issues.push(*issue);
            }
            Ok(())
        }
    }
}

fn map_stop<T>(
    res: Result<T, E>,
    issues: &mut Vec<Issue>,
    max_errors: usize,
) -> Result<Option<T>, CheckFailure<()>> {
    match res {
        Ok(val) => Ok(Some(val)),
        Err(err) => {
            push_err(issues, max_errors, err)?;
            Ok(None)
        }
    }
}

/// 複数の SHIGURE 宣言エラーを pass 単位で最大 `max_errors` 件まで収集する。
pub(crate) fn check_shigure_decls_batch(
    checker: &mut Checker<'_, E>,
    control: &Control,
    max_errors: usize,
) -> Result<CheckedShigureDecls, CheckFailure<Vec<Issue>>> {
    let max_errors = max_errors.max(1);
    let readings = checker.ast.clone();
    let mut index: HashMap<String, (DeclCategory, Span, usize)> = HashMap::new();
    let mut shigure_edges: Vec<(usize, usize, Span)> = Vec::new();
    let mut issues: Vec<Issue> = Vec::new();

    // Pass 1: 名前衝突一括収集
    for (r_idx, r) in readings.iter().enumerate() {
        control
            .checkpoint(Checkpoint::LawSemantics)
            .map_err(CheckFailure::Stopped)?;
        for d in &r.shigure_decls {
            control
                .checkpoint(Checkpoint::LawSemantics)
                .map_err(CheckFailure::Stopped)?;
            if let Err(err) = check_decl_name::<E>(d.name()) {
                if let Err(CheckFailure::Stopped(s)) = push_err(&mut issues, max_errors, err) {
                    return Err(CheckFailure::Stopped(s));
                }
                continue;
            }
            if checker.aliases[r_idx].contains_key(&d.name().name) {
                let err = duplicate::<(), E>(
                    d.name().span,
                    format!(
                        "SHIGURE declaration `{}` conflicts with `use` alias in reading `{}`",
                        d.name().name,
                        r.name.name
                    ),
                )
                .unwrap_err();
                if let Err(CheckFailure::Stopped(s)) = push_err(&mut issues, max_errors, err) {
                    return Err(CheckFailure::Stopped(s));
                }
                continue;
            }
            let name = full(&r.name.name, &[&d.name().name]);
            match checker.primitive_identifier_exists(&name) {
                Ok(true) => {
                    let err = duplicate::<(), E>(
                        d.name().span,
                        format!(
                            "fully qualified name `{name}` conflicts with a primitive definition"
                        ),
                    )
                    .unwrap_err();
                    if let Err(CheckFailure::Stopped(s)) = push_err(&mut issues, max_errors, err) {
                        return Err(CheckFailure::Stopped(s));
                    }
                    continue;
                }
                Ok(false) => {}
                Err(CheckFailure::Stopped(s)) => return Err(CheckFailure::Stopped(s)),
                Err(CheckFailure::Input(i)) => {
                    if issues.len() < max_errors {
                        issues.push(*i);
                    }
                    continue;
                }
            }
            if checker.decl_index.contains_key(&name) || index.contains_key(&name) {
                let err =
                    duplicate::<(), E>(d.name().span, format!("duplicate declaration `{name}`"))
                        .unwrap_err();
                if let Err(CheckFailure::Stopped(s)) = push_err(&mut issues, max_errors, err) {
                    return Err(CheckFailure::Stopped(s));
                }
                continue;
            }
            let cat = match d {
                ShigureDeclAst::Presentation(_) => DeclCategory::Presentation,
                ShigureDeclAst::Comparison(_) => DeclCategory::Comparison,
                ShigureDeclAst::ChangeSpec(_) => DeclCategory::ChangeSpec,
                ShigureDeclAst::EvalCondition(_) => DeclCategory::EvalCondition,
                ShigureDeclAst::Task(_) => DeclCategory::Task,
                ShigureDeclAst::Diagram(_) => DeclCategory::Diagram,
                ShigureDeclAst::Path(_) => DeclCategory::Path,
                ShigureDeclAst::Transfer(_) => DeclCategory::Transfer,
                ShigureDeclAst::Family(_) => DeclCategory::Family,
                ShigureDeclAst::Robustness(_) => DeclCategory::Robustness,
                ShigureDeclAst::Chevalley(_) => DeclCategory::Chevalley,
                ShigureDeclAst::Observations(_) => DeclCategory::Observations,
                ShigureDeclAst::Lift(_) => DeclCategory::Lift,
                ShigureDeclAst::Artin(_) => DeclCategory::Artin,
                ShigureDeclAst::Diagnostics(_) => DeclCategory::Diagnostics,
                ShigureDeclAst::Atlas(_) => DeclCategory::Atlas,
                ShigureDeclAst::Occurrence(_) => DeclCategory::Occurrence,
                ShigureDeclAst::Partial(_) => DeclCategory::Partial,
                ShigureDeclAst::Revision(_) => DeclCategory::Revision,
                ShigureDeclAst::Multisource(_) => DeclCategory::Multisource,
            };
            index.insert(name, (cat, d.span(), r_idx));
        }
    }

    if !issues.is_empty() {
        return Err(CheckFailure::Input(issues));
    }
    if index.is_empty() {
        return Ok(CheckedShigureDecls::default());
    }

    let mut out = CheckedShigureDecls::default();

    // Pass 2: presentations（複数エラー一括収集）
    for (r_idx, r) in readings.iter().enumerate() {
        for d in &r.shigure_decls {
            if let ShigureDeclAst::Presentation(raw) = d {
                control
                    .checkpoint(Checkpoint::LawSemantics)
                    .map_err(CheckFailure::Stopped)?;
                match map_stop(
                    check_presentation(raw, r_idx, &r.name.name, checker, control),
                    &mut issues,
                    max_errors,
                ) {
                    Ok(Some(checked)) => {
                        out.presentations.insert(checked.name.clone(), checked);
                    }
                    Ok(None) => {}
                    Err(CheckFailure::Stopped(s)) => return Err(CheckFailure::Stopped(s)),
                    Err(CheckFailure::Input(())) => unreachable!(),
                }
            }
        }
    }
    if !issues.is_empty() {
        return Err(CheckFailure::Input(issues));
    }

    // Pass 3: comparisons, change_specs, eval_conditions
    for (r_idx, r) in readings.iter().enumerate() {
        for d in &r.shigure_decls {
            let res: Result<(), E> = match d {
                ShigureDeclAst::Comparison(raw) => {
                    control
                        .checkpoint(Checkpoint::LawSemantics)
                        .map_err(CheckFailure::Stopped)?;
                    let mut ctx = ShigureDeclCtx {
                        r_idx,
                        reading_name: &r.name.name,
                        checker,
                        index: &index,
                        decls: &out,
                        edges: &mut shigure_edges,
                        control,
                    };
                    check_comparison(raw, &mut ctx).map(|c| {
                        out.comparisons.insert(c.name.clone(), c);
                    })
                }
                ShigureDeclAst::ChangeSpec(raw) => {
                    control
                        .checkpoint(Checkpoint::LawSemantics)
                        .map_err(CheckFailure::Stopped)?;
                    let mut ctx = ShigureDeclCtx {
                        r_idx,
                        reading_name: &r.name.name,
                        checker,
                        index: &index,
                        decls: &out,
                        edges: &mut shigure_edges,
                        control,
                    };
                    check_change_spec(raw, &mut ctx).map(|c| {
                        out.change_specs.insert(c.name.clone(), c);
                    })
                }
                ShigureDeclAst::EvalCondition(raw) => {
                    control
                        .checkpoint(Checkpoint::LawSemantics)
                        .map_err(CheckFailure::Stopped)?;
                    check_eval_condition(raw, &r.name.name, control).map(|c| {
                        out.eval_conditions.insert(c.name.clone(), c);
                    })
                }
                _ => continue,
            };
            if let Err(err) = res
                && let Err(CheckFailure::Stopped(s)) = push_err(&mut issues, max_errors, err)
            {
                return Err(CheckFailure::Stopped(s));
            }
        }
    }
    if !issues.is_empty() {
        return Err(CheckFailure::Input(issues));
    }

    // Pass 3.5: families
    if let Err(err) = super::check_phase3_tasks::check_all_families(
        checker,
        &index,
        &mut out,
        &mut shigure_edges,
        control,
    ) {
        return match err {
            CheckFailure::Stopped(s) => Err(CheckFailure::Stopped(s)),
            CheckFailure::Input(i) => Err(CheckFailure::Input(vec![*i])),
        };
    }

    // Pass 4: tasks, diagrams, paths, transfers
    for (r_idx, r) in readings.iter().enumerate() {
        for d in &r.shigure_decls {
            let res: Result<(), E> = match d {
                ShigureDeclAst::Task(raw) => {
                    control
                        .checkpoint(Checkpoint::LawSemantics)
                        .map_err(CheckFailure::Stopped)?;
                    let mut ctx = ShigureDeclCtx {
                        r_idx,
                        reading_name: &r.name.name,
                        checker,
                        index: &index,
                        decls: &out,
                        edges: &mut shigure_edges,
                        control,
                    };
                    check_task(raw, &mut ctx).map(|c| {
                        out.tasks.insert(c.name.clone(), c);
                    })
                }
                ShigureDeclAst::Diagram(raw) => {
                    control
                        .checkpoint(Checkpoint::LawSemantics)
                        .map_err(CheckFailure::Stopped)?;
                    let mut ctx = ShigureDeclCtx {
                        r_idx,
                        reading_name: &r.name.name,
                        checker,
                        index: &index,
                        decls: &out,
                        edges: &mut shigure_edges,
                        control,
                    };
                    check_diagram(raw, &mut ctx).map(|c| {
                        out.diagrams.insert(c.name.clone(), c);
                    })
                }
                ShigureDeclAst::Path(raw) => {
                    control
                        .checkpoint(Checkpoint::LawSemantics)
                        .map_err(CheckFailure::Stopped)?;
                    let mut ctx = ShigureDeclCtx {
                        r_idx,
                        reading_name: &r.name.name,
                        checker,
                        index: &index,
                        decls: &out,
                        edges: &mut shigure_edges,
                        control,
                    };
                    check_path(raw.as_ref(), &mut ctx).map(|c| {
                        out.paths.insert(c.name.clone(), c);
                    })
                }
                ShigureDeclAst::Transfer(raw) => {
                    control
                        .checkpoint(Checkpoint::LawSemantics)
                        .map_err(CheckFailure::Stopped)?;
                    let mut ctx = ShigureDeclCtx {
                        r_idx,
                        reading_name: &r.name.name,
                        checker,
                        index: &index,
                        decls: &out,
                        edges: &mut shigure_edges,
                        control,
                    };
                    check_transfer(raw, &mut ctx).map(|c| {
                        out.transfers.insert(c.name.clone(), c);
                    })
                }
                _ => continue,
            };
            if let Err(err) = res
                && let Err(CheckFailure::Stopped(s)) = push_err(&mut issues, max_errors, err)
            {
                return Err(CheckFailure::Stopped(s));
            }
        }
    }
    if !issues.is_empty() {
        return Err(CheckFailure::Input(issues));
    }

    for sub_res in [
        super::check_phase3_tasks::check_all_phase3_tasks(
            checker,
            &index,
            &mut out,
            &mut shigure_edges,
            control,
        ),
        super::check_phase4_lift_artin::check_all_phase4_tasks(checker, &mut out, control),
        super::check_phase5_rev::check_all_phase5_tasks(checker, &mut out, control),
    ] {
        if let Err(err) = sub_res {
            return match err {
                CheckFailure::Stopped(s) => Err(CheckFailure::Stopped(s)),
                CheckFailure::Input(i) => Err(CheckFailure::Input(vec![*i])),
            };
        }
    }

    if !shigure_edges.is_empty() {
        checker.reading_edges.extend(shigure_edges);
        if let Err(err) = checker.check_reading_cycles() {
            return match err {
                CheckFailure::Stopped(s) => Err(CheckFailure::Stopped(s)),
                CheckFailure::Input(i) => Err(CheckFailure::Input(vec![*i])),
            };
        }
    }

    Ok(out)
}
