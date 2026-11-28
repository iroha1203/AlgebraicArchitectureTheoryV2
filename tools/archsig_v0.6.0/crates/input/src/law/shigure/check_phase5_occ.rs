//! `shigure occurrence` 宣言の静的意味検査（AC2）。

use super::ast_phase5_obs::*;
use super::check::CResult;
use super::check_phase4_lift_artin::{check_p4_origins, p4_type_err};
use super::check_phase5_common::check_symbolic_value;
use crate::law::check::{Checker, duplicate, full, reference};
use archsig_common::control::{Checkpoint, Control};
use archsig_common::json::InputError;
use std::collections::{HashMap, HashSet};

fn check_p5_unique_elements<E: InputError>(
    elems: &[(String, crate::law::ast::Span)],
    context: &str,
) -> CResult<(Vec<String>, HashSet<String>), E> {
    let mut seen = HashSet::new();
    let mut list = Vec::with_capacity(elems.len());
    for (name, span) in elems {
        if name.trim().is_empty() {
            return p4_type_err(*span, format!("empty element name in {context}"));
        }
        if !seen.insert(name.clone()) {
            return duplicate(*span, format!("duplicate element `{name}` in {context}"));
        }
        list.push(name.clone());
    }
    Ok((list, seen))
}

struct ReadingCheckCtx<'a, 'c, E: InputError> {
    sort_elems: &'a HashMap<String, HashSet<String>>,
    seen_names: &'a mut HashSet<String>,
    require_full_cover: bool,
    r_idx: usize,
    checker: &'a Checker<'c, E>,
    control: &'a Control,
    kind_label: &'a str,
}

fn check_occurrence_reading<E: InputError>(
    raw: &RawOccurrenceReading,
    ctx: &mut ReadingCheckCtx<'_, '_, E>,
) -> CResult<ShigureOccurrenceReading, E> {
    E::checkpoint(ctx.control, Checkpoint::LawSemantics)?;
    if raw.name.name.starts_with("__initial_readout_") {
        return p4_type_err(
            raw.name.span,
            format!(
                "{} `{}` cannot use reserved prefix `__initial_readout_`",
                ctx.kind_label, raw.name.name
            ),
        );
    }
    if !ctx.seen_names.insert(raw.name.name.clone()) {
        return duplicate(
            raw.name.span,
            format!(
                "duplicate reading name `{}` in `shigure occurrence`",
                raw.name.name
            ),
        );
    }
    let Some(elems) = ctx.sort_elems.get(&raw.sort.name) else {
        return reference(
            raw.sort.span,
            format!(
                "unknown sort `{}` in {} `{}`",
                raw.sort.name, ctx.kind_label, raw.name.name
            ),
        );
    };
    let mut seen_keys = HashSet::new();
    let mut values = Vec::with_capacity(raw.values.len());
    for ((elem, elem_span), val_opt, _) in &raw.values {
        E::checkpoint(ctx.control, Checkpoint::LawSemantics)?;
        if !elems.contains(elem) {
            return reference(
                *elem_span,
                format!(
                    "unknown element `{elem}` of sort `{}` in {} `{}`",
                    raw.sort.name, ctx.kind_label, raw.name.name
                ),
            );
        }
        if !seen_keys.insert(elem.as_str()) {
            return duplicate(
                *elem_span,
                format!(
                    "duplicate entry for element `{elem}` in {} `{}`",
                    ctx.kind_label, raw.name.name
                ),
            );
        }
        let checked_val = match val_opt {
            Some(v) => Some(check_symbolic_value(
                v,
                ctx.r_idx,
                ctx.checker,
                &format!(
                    "`shigure occurrence` {} `{}`",
                    ctx.kind_label, raw.name.name
                ),
            )?),
            None => None,
        };
        values.push((elem.clone(), checked_val));
    }
    if ctx.require_full_cover && seen_keys.len() != elems.len() {
        return p4_type_err(
            raw.span,
            format!(
                "{} `{}` must cover every element of sort `{}` under `context_closed = true`",
                ctx.kind_label, raw.name.name, raw.sort.name
            ),
        );
    }
    Ok(ShigureOccurrenceReading {
        name: raw.name.name.clone(),
        sort: raw.sort.name.clone(),
        values,
        span: raw.span,
    })
}

pub(super) fn check_occurrence<E: InputError>(
    raw: &RawOccurrenceTask,
    r_idx: usize,
    reading_name: &str,
    checker: &Checker<'_, E>,
    control: &Control,
) -> CResult<ShigureOccurrenceTask, E> {
    let context = format!("`shigure occurrence` `{}`", raw.name.name);
    let origins = check_p4_origins(&raw.origins, raw.span, &context)?;

    let mut sort_elems: HashMap<String, HashSet<String>> = HashMap::new();
    let mut sorts = Vec::with_capacity(raw.sorts.len());
    for s in &raw.sorts {
        E::checkpoint(control, Checkpoint::LawSemantics)?;
        if sort_elems.contains_key(&s.name.name) {
            return duplicate(
                s.name.span,
                format!("duplicate sort `{}` in {context}", s.name.name),
            );
        }
        let (list, set) =
            check_p5_unique_elements(&s.elements, &format!("{context} sort `{}`", s.name.name))?;
        sort_elems.insert(s.name.name.clone(), set);
        sorts.push(ShigureOccurrenceSort {
            name: s.name.name.clone(),
            elements: list,
            is_fixed_value: s.is_fixed_value,
            span: s.span,
        });
    }

    let mut ops_map: HashMap<String, (Vec<String>, String)> = HashMap::new();
    let mut operations = Vec::with_capacity(raw.operations.len());
    for op in &raw.operations {
        E::checkpoint(control, Checkpoint::LawSemantics)?;
        if ops_map.contains_key(&op.name.name) {
            return duplicate(
                op.name.span,
                format!("duplicate operation `{}` in {context}", op.name.name),
            );
        }
        let mut arg_sorts = Vec::with_capacity(op.arg_sorts.len());
        for a in &op.arg_sorts {
            if !sort_elems.contains_key(&a.name) {
                return reference(
                    a.span,
                    format!("unknown sort `{}` in operation `{}`", a.name, op.name.name),
                );
            }
            arg_sorts.push(a.name.clone());
        }
        if !sort_elems.contains_key(&op.out_sort.name) {
            return reference(
                op.out_sort.span,
                format!(
                    "unknown output sort `{}` in operation `{}`",
                    op.out_sort.name, op.name.name
                ),
            );
        }
        ops_map.insert(
            op.name.name.clone(),
            (arg_sorts.clone(), op.out_sort.name.clone()),
        );
        operations.push(ShigureOccurrenceOp {
            name: op.name.name.clone(),
            arg_sorts,
            out_sort: op.out_sort.name.clone(),
            is_total: op.is_total,
            span: op.span,
        });
    }

    let mut rels_map: HashMap<String, Vec<String>> = HashMap::new();
    let mut relations = Vec::with_capacity(raw.relations.len());
    for rel in &raw.relations {
        E::checkpoint(control, Checkpoint::LawSemantics)?;
        if rels_map.contains_key(&rel.name.name) {
            return duplicate(
                rel.name.span,
                format!("duplicate relation `{}` in {context}", rel.name.name),
            );
        }
        let mut arg_sorts = Vec::with_capacity(rel.arg_sorts.len());
        for a in &rel.arg_sorts {
            if !sort_elems.contains_key(&a.name) {
                return reference(
                    a.span,
                    format!("unknown sort `{}` in relation `{}`", a.name, rel.name.name),
                );
            }
            arg_sorts.push(a.name.clone());
        }
        rels_map.insert(rel.name.name.clone(), arg_sorts.clone());
        relations.push(ShigureOccurrenceRel {
            name: rel.name.name.clone(),
            arg_sorts,
            span: rel.span,
        });
    }

    let mut identity_requests = Vec::with_capacity(raw.identity_requests.len());
    for (s, (l, l_span), (r, r_span), _) in &raw.identity_requests {
        let Some(elems) = sort_elems.get(&s.name) else {
            return reference(
                s.span,
                format!("unknown sort `{}` in identify ({context})", s.name),
            );
        };
        if !elems.contains(l) {
            return reference(
                *l_span,
                format!("unknown element `{l}` of sort `{}` in identify", s.name),
            );
        }
        if !elems.contains(r) {
            return reference(
                *r_span,
                format!("unknown element `{r}` of sort `{}` in identify", s.name),
            );
        }
        identity_requests.push((s.name.clone(), l.clone(), r.clone()));
    }

    let mut op_records = Vec::with_capacity(raw.op_records.len());
    for rec in &raw.op_records {
        E::checkpoint(control, Checkpoint::LawSemantics)?;
        let Some((arg_sorts, out_sort)) = ops_map.get(&rec.op_name.name) else {
            return reference(
                rec.op_name.span,
                format!("unknown operation `{}` in op_record", rec.op_name.name),
            );
        };
        if rec.args.len() != arg_sorts.len() {
            return p4_type_err(
                rec.span,
                format!(
                    "op_record `{}` has {} args, expected {}",
                    rec.op_name.name,
                    rec.args.len(),
                    arg_sorts.len()
                ),
            );
        }
        let mut args = Vec::with_capacity(rec.args.len());
        for (sort_name, (arg, a_span)) in arg_sorts.iter().zip(&rec.args) {
            if !sort_elems[sort_name].contains(arg) {
                return reference(
                    *a_span,
                    format!(
                        "unknown element `{arg}` of sort `{sort_name}` in op_record `{}`",
                        rec.op_name.name
                    ),
                );
            }
            args.push(arg.clone());
        }
        let checked_out = check_symbolic_value(
            &rec.output,
            r_idx,
            checker,
            &format!("op_record `{}` output", rec.op_name.name),
        )?;
        if let ShigureSymbolicValue::Literal(ref out_lit) = checked_out
            && !sort_elems[out_sort].contains(out_lit)
        {
            return reference(
                rec.span,
                format!(
                    "unknown output element `{out_lit}` of sort `{out_sort}` in op_record `{}`",
                    rec.op_name.name
                ),
            );
        }
        op_records.push(ShigureOccurrenceOpRecord {
            op_name: rec.op_name.name.clone(),
            arg_sorts: arg_sorts.clone(),
            out_sort: out_sort.clone(),
            args,
            output: checked_out,
            span: rec.span,
        });
    }

    let mut pred_records = Vec::with_capacity(raw.pred_records.len());
    for rec in &raw.pred_records {
        E::checkpoint(control, Checkpoint::LawSemantics)?;
        let arg_sorts = match rec.kind {
            OccurrencePredKind::Domain => {
                let Some((arg_sorts, _)) = ops_map.get(&rec.name.name) else {
                    return reference(
                        rec.name.span,
                        format!("unknown operation `{}` in domain_record", rec.name.name),
                    );
                };
                arg_sorts.clone()
            }
            OccurrencePredKind::Relation => {
                let Some(arg_sorts) = rels_map.get(&rec.name.name) else {
                    return reference(
                        rec.name.span,
                        format!("unknown relation `{}` in rel_record", rec.name.name),
                    );
                };
                arg_sorts.clone()
            }
        };
        if rec.args.len() != arg_sorts.len() {
            return p4_type_err(
                rec.span,
                format!(
                    "predicate record `{}` has {} args, expected {}",
                    rec.name.name,
                    rec.args.len(),
                    arg_sorts.len()
                ),
            );
        }
        let mut args = Vec::with_capacity(rec.args.len());
        for (sort_name, (arg, a_span)) in arg_sorts.iter().zip(&rec.args) {
            if !sort_elems[sort_name].contains(arg) {
                return reference(
                    *a_span,
                    format!(
                        "unknown element `{arg}` of sort `{sort_name}` in record `{}`",
                        rec.name.name
                    ),
                );
            }
            args.push(arg.clone());
        }
        pred_records.push(ShigureOccurrencePredRecord {
            kind: rec.kind,
            name: rec.name.name.clone(),
            arg_sorts,
            args,
            holds: rec.holds,
            span: rec.span,
        });
    }

    let context_closed_17_5 = raw.context_closed_17_5.unwrap_or(true);
    let mut seen_reading_names = HashSet::new();
    let mut base_readings = Vec::with_capacity(raw.base_readings.len());
    for br in &raw.base_readings {
        let mut r_ctx = ReadingCheckCtx {
            sort_elems: &sort_elems,
            seen_names: &mut seen_reading_names,
            require_full_cover: context_closed_17_5,
            r_idx,
            checker,
            control,
            kind_label: "base_reading",
        };
        base_readings.push(check_occurrence_reading(br, &mut r_ctx)?);
    }
    let mut explicit_contexts = Vec::with_capacity(raw.explicit_contexts.len());
    for ec in &raw.explicit_contexts {
        let mut r_ctx = ReadingCheckCtx {
            sort_elems: &sort_elems,
            seen_names: &mut seen_reading_names,
            require_full_cover: false,
            r_idx,
            checker,
            control,
            kind_label: "explicit_context",
        };
        explicit_contexts.push(check_occurrence_reading(ec, &mut r_ctx)?);
    }

    let mut preserve_full_domains = Vec::with_capacity(raw.preserve_full_domains.len());
    for id in &raw.preserve_full_domains {
        if !ops_map.contains_key(&id.name) && !rels_map.contains_key(&id.name) {
            return reference(
                id.span,
                format!(
                    "unknown operation or relation `{}` in preserve_full_domain",
                    id.name
                ),
            );
        }
        preserve_full_domains.push(id.name.clone());
    }

    let mut seen_readout_sorts = HashSet::new();
    let mut initial_readouts = Vec::with_capacity(raw.initial_readouts.len());
    for ro in &raw.initial_readouts {
        let Some(elems) = sort_elems.get(&ro.sort.name) else {
            return reference(
                ro.sort.span,
                format!("unknown sort `{}` in initial_readout", ro.sort.name),
            );
        };
        if !seen_readout_sorts.insert(ro.sort.name.clone()) {
            return duplicate(
                ro.sort.span,
                format!("duplicate initial_readout for sort `{}`", ro.sort.name),
            );
        }
        let mut seen_elems = HashSet::new();
        let mut values = Vec::with_capacity(ro.values.len());
        for ((elem, elem_span), val, _) in &ro.values {
            if !elems.contains(elem) {
                return reference(
                    *elem_span,
                    format!(
                        "unknown element `{elem}` of sort `{}` in initial_readout",
                        ro.sort.name
                    ),
                );
            }
            if !seen_elems.insert(elem.as_str()) {
                return duplicate(
                    *elem_span,
                    format!(
                        "duplicate element `{elem}` in initial_readout for sort `{}`",
                        ro.sort.name
                    ),
                );
            }
            let checked = check_symbolic_value(val, r_idx, checker, "initial_readout")?;
            values.push((elem.clone(), checked));
        }
        if seen_elems.len() != elems.len() {
            return p4_type_err(
                ro.span,
                format!(
                    "initial_readout for sort `{}` must assign every element",
                    ro.sort.name
                ),
            );
        }
        initial_readouts.push(ShigureOccurrenceInitialReadout {
            sort: ro.sort.name.clone(),
            values,
            span: ro.span,
        });
    }

    Ok(ShigureOccurrenceTask {
        name: full(reading_name, &[&raw.name.name]),
        reading: reading_name.to_owned(),
        origins,
        sorts,
        operations,
        relations,
        identity_requests,
        op_records,
        pred_records,
        base_readings,
        context_closed_17_5,
        explicit_contexts,
        preserve_full_domains,
        initial_readouts,
        max_congruence_steps: raw.max_congruence_steps.unwrap_or(0),
        max_partitions: raw.max_partitions.unwrap_or(0),
        span: raw.span,
    })
}
