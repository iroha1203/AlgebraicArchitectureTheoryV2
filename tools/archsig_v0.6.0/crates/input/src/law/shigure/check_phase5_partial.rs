//! `shigure partial` 宣言の静的意味検査（有限表・アフィン表示・エントリ / AC2）。

use super::ast_phase5_obs::*;
use super::check::{CResult, CoordCheckCtx, check_coeff_domain, check_member_coord_value};
use super::check_phase4_lift_artin::{check_p4_origins, check_p4_unique_idents, p4_type_err};
use super::check_phase5_common::check_symbolic_value;
use super::check_phase5_partial_ext::{FormulaCheckScope, check_eval_law, check_open_domain};
use crate::law::ast::Span;
use crate::law::check::{Checker, duplicate, full, reference};
use archsig_common::control::{Checkpoint, Control};
use archsig_common::json::InputError;
use std::collections::{HashMap, HashSet};

struct CheckedFiniteBundle {
    finite: ShigureFinitePartial,
    op_arities: HashMap<String, usize>,
    rel_arities: HashMap<String, usize>,
    sorts: HashMap<String, HashSet<String>>,
    slots: HashSet<String>,
}

fn check_finite_partial<E: InputError>(
    raw: &RawFinitePartial,
    r_idx: usize,
    checker: &Checker<'_, E>,
    control: &Control,
) -> CResult<CheckedFiniteBundle, E> {
    let mut sort_elems: HashMap<String, HashSet<String>> = HashMap::new();
    let mut sorts = Vec::with_capacity(raw.sorts.len());
    for (s_name, elems, _) in &raw.sorts {
        if sort_elems.contains_key(&s_name.name) {
            return duplicate(s_name.span, format!("duplicate sort `{}`", s_name.name));
        }
        let mut set = HashSet::new();
        let mut list = Vec::with_capacity(elems.len());
        for (e, e_span) in elems {
            if !set.insert(e.clone()) {
                return duplicate(
                    *e_span,
                    format!("duplicate element `{e}` in `{}`", s_name.name),
                );
            }
            list.push(e.clone());
        }
        sort_elems.insert(s_name.name.clone(), set);
        sorts.push((s_name.name.clone(), list));
    }

    let mut op_sigs: HashMap<String, (Vec<String>, String)> = HashMap::new();
    let mut operations = Vec::with_capacity(raw.operations.len());
    for op in &raw.operations {
        if op_sigs.contains_key(&op.name.name) {
            return duplicate(
                op.name.span,
                format!("duplicate operation `{}`", op.name.name),
            );
        }
        let mut arg_sorts = Vec::with_capacity(op.arg_sorts.len());
        for a in &op.arg_sorts {
            if !sort_elems.contains_key(&a.name) {
                return reference(a.span, format!("unknown sort `{}`", a.name));
            }
            arg_sorts.push(a.name.clone());
        }
        if !sort_elems.contains_key(&op.out_sort.name) {
            return reference(
                op.out_sort.span,
                format!("unknown sort `{}`", op.out_sort.name),
            );
        }
        op_sigs.insert(
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

    let mut rel_sigs: HashMap<String, Vec<String>> = HashMap::new();
    let mut relations = Vec::with_capacity(raw.relations.len());
    for rel in &raw.relations {
        if rel_sigs.contains_key(&rel.name.name) {
            return duplicate(
                rel.name.span,
                format!("duplicate relation `{}`", rel.name.name),
            );
        }
        let mut arg_sorts = Vec::with_capacity(rel.arg_sorts.len());
        for a in &rel.arg_sorts {
            if !sort_elems.contains_key(&a.name) {
                return reference(a.span, format!("unknown sort `{}`", a.name));
            }
            arg_sorts.push(a.name.clone());
        }
        rel_sigs.insert(rel.name.name.clone(), arg_sorts.clone());
        relations.push(ShigureOccurrenceRel {
            name: rel.name.name.clone(),
            arg_sorts,
            span: rel.span,
        });
    }

    let mut slot_sorts: HashMap<String, String> = HashMap::new();
    let mut slot_doms: HashMap<String, HashSet<String>> = HashMap::new();
    let mut slots = Vec::with_capacity(raw.slots.len());
    for sl in &raw.slots {
        if slot_sorts.contains_key(&sl.name.name) {
            return duplicate(sl.name.span, format!("duplicate slot `{}`", sl.name.name));
        }
        let Some(carrier) = sort_elems.get(&sl.sort.name) else {
            return reference(sl.sort.span, format!("unknown sort `{}`", sl.sort.name));
        };
        if sl.domain_values.is_empty() {
            return p4_type_err(sl.span, format!("slot `{}` has empty domain", sl.name.name));
        }
        let mut dom_set = HashSet::new();
        let mut dom_list = Vec::with_capacity(sl.domain_values.len());
        for (v, v_span) in &sl.domain_values {
            if !carrier.contains(v) {
                return reference(
                    *v_span,
                    format!(
                        "unknown element `{v}` of sort `{}` in slot `{}`",
                        sl.sort.name, sl.name.name
                    ),
                );
            }
            if !dom_set.insert(v.clone()) {
                return duplicate(
                    *v_span,
                    format!("duplicate value `{v}` in slot `{}`", sl.name.name),
                );
            }
            dom_list.push(v.clone());
        }
        slot_sorts.insert(sl.name.name.clone(), sl.sort.name.clone());
        slot_doms.insert(sl.name.name.clone(), dom_set);
        slots.push(ShigurePartialSlotDecl {
            name: sl.name.name.clone(),
            sort: sl.sort.name.clone(),
            domain_values: dom_list,
            span: sl.span,
        });
    }

    let mut background_constraints = Vec::with_capacity(raw.background_constraints.len());
    for bg in &raw.background_constraints {
        match bg {
            RawBackgroundConstraint::SlotEquality(a, b, span)
            | RawBackgroundConstraint::SlotNotEqual(a, b, span) => {
                let Some(sa) = slot_sorts.get(&a.name) else {
                    return reference(a.span, format!("unknown slot `{}`", a.name));
                };
                let Some(sb) = slot_sorts.get(&b.name) else {
                    return reference(b.span, format!("unknown slot `{}`", b.name));
                };
                if sa != sb {
                    return p4_type_err(
                        *span,
                        format!(
                            "background slot constraint `{}` ({sa}) vs `{}` ({sb}) sort mismatch",
                            a.name, b.name
                        ),
                    );
                }
                background_constraints.push(match bg {
                    RawBackgroundConstraint::SlotEquality(..) => {
                        ShigureBackgroundConstraint::SlotEquality(a.name.clone(), b.name.clone())
                    }
                    _ => ShigureBackgroundConstraint::SlotNotEqual(a.name.clone(), b.name.clone()),
                });
            }
            RawBackgroundConstraint::OperationInjective(op, _) => {
                if !op_sigs.contains_key(&op.name) {
                    return reference(op.span, format!("unknown operation `{}`", op.name));
                }
                background_constraints.push(ShigureBackgroundConstraint::OperationInjective(
                    op.name.clone(),
                ));
            }
            RawBackgroundConstraint::OperationSurjective(op, _) => {
                if !op_sigs.contains_key(&op.name) {
                    return reference(op.span, format!("unknown operation `{}`", op.name));
                }
                background_constraints.push(ShigureBackgroundConstraint::OperationSurjective(
                    op.name.clone(),
                ));
            }
        }
    }

    let check_truth = |t: &RawPartialTruth| -> CResult<ShigurePartialTruth, E> {
        match t {
            RawPartialTruth::True => Ok(ShigurePartialTruth::True),
            RawPartialTruth::ExplicitAbsent => Ok(ShigurePartialTruth::ExplicitAbsent),
            RawPartialTruth::UnobservedSlot(sl) => {
                if !slot_sorts.contains_key(&sl.name) {
                    return reference(sl.span, format!("unknown slot `{}`", sl.name));
                }
                Ok(ShigurePartialTruth::UnobservedSlot(sl.name.clone()))
            }
        }
    };
    let check_typed_args = |args: &[(String, Span)],
                            expected: &[String],
                            span: Span,
                            rec_id: &str|
     -> CResult<Vec<String>, E> {
        if args.len() != expected.len() {
            return p4_type_err(
                span,
                format!(
                    "record `{rec_id}` expected {} args, got {}",
                    expected.len(),
                    args.len()
                ),
            );
        }
        let mut out = Vec::with_capacity(args.len());
        for (s, (a, a_span)) in expected.iter().zip(args) {
            if !sort_elems[s].contains(a) {
                return reference(
                    *a_span,
                    format!("unknown element `{a}` of sort `{s}` in record `{rec_id}`"),
                );
            }
            out.push(a.clone());
        }
        Ok(out)
    };

    let mut rec_ids = HashSet::new();
    let mut records = Vec::with_capacity(raw.records.len());
    for rec in &raw.records {
        E::checkpoint(control, Checkpoint::LawSemantics)?;
        if !rec_ids.insert(rec.id.name.as_str()) {
            return duplicate(rec.id.span, format!("duplicate record `{}`", rec.id.name));
        }
        let kind = match &rec.kind {
            RawPartialRecordKind::OpValue {
                op_name,
                args,
                value,
            } => {
                let Some((arg_sorts, out_sort)) = op_sigs.get(&op_name.name) else {
                    return reference(
                        op_name.span,
                        format!("unknown operation `{}`", op_name.name),
                    );
                };
                let checked_args = check_typed_args(args, arg_sorts, rec.span, &rec.id.name)?;
                let checked_val = match value {
                    RawPartialValue::Known(sym) => {
                        let sv = check_symbolic_value(sym, r_idx, checker, "partial op_value")?;
                        if let ShigureSymbolicValue::Literal(ref lit) = sv
                            && !sort_elems[out_sort].contains(lit)
                        {
                            return reference(
                                rec.span,
                                format!(
                                    "unknown element `{lit}` of sort `{out_sort}` in record `{}`",
                                    rec.id.name
                                ),
                            );
                        }
                        ShigurePartialValue::Known(sv)
                    }
                    RawPartialValue::ExplicitAbsent => ShigurePartialValue::ExplicitAbsent,
                    RawPartialValue::UnobservedSlot(sl) => {
                        let Some(ss) = slot_sorts.get(&sl.name) else {
                            return reference(sl.span, format!("unknown slot `{}`", sl.name));
                        };
                        if ss != out_sort {
                            return p4_type_err(
                                sl.span,
                                format!(
                                    "slot `{}` sort `{ss}` does not match out_sort `{out_sort}`",
                                    sl.name
                                ),
                            );
                        }
                        ShigurePartialValue::UnobservedSlot(sl.name.clone())
                    }
                };
                ShigurePartialRecordKind::OpValue {
                    op_name: op_name.name.clone(),
                    args: checked_args,
                    value: checked_val,
                }
            }
            RawPartialRecordKind::OpDomain {
                op_name,
                args,
                defined,
            } => {
                let Some((arg_sorts, _)) = op_sigs.get(&op_name.name) else {
                    return reference(
                        op_name.span,
                        format!("unknown operation `{}`", op_name.name),
                    );
                };
                ShigurePartialRecordKind::OpDomain {
                    op_name: op_name.name.clone(),
                    args: check_typed_args(args, arg_sorts, rec.span, &rec.id.name)?,
                    defined: check_truth(defined)?,
                }
            }
            RawPartialRecordKind::OpGraph {
                op_name,
                args,
                output,
                present,
            } => {
                let Some((arg_sorts, out_sort)) = op_sigs.get(&op_name.name) else {
                    return reference(
                        op_name.span,
                        format!("unknown operation `{}`", op_name.name),
                    );
                };
                let checked_args = check_typed_args(args, arg_sorts, rec.span, &rec.id.name)?;
                if !sort_elems[out_sort].contains(&output.0) {
                    return reference(
                        output.1,
                        format!("unknown element `{}` of sort `{out_sort}`", output.0),
                    );
                }
                ShigurePartialRecordKind::OpGraph {
                    op_name: op_name.name.clone(),
                    args: checked_args,
                    output: output.0.clone(),
                    present: check_truth(present)?,
                }
            }
            RawPartialRecordKind::Relation {
                rel_name,
                args,
                holds,
            } => {
                let Some(arg_sorts) = rel_sigs.get(&rel_name.name) else {
                    return reference(
                        rel_name.span,
                        format!("unknown relation `{}`", rel_name.name),
                    );
                };
                ShigurePartialRecordKind::Relation {
                    rel_name: rel_name.name.clone(),
                    args: check_typed_args(args, arg_sorts, rec.span, &rec.id.name)?,
                    holds: check_truth(holds)?,
                }
            }
            RawPartialRecordKind::SlotAssignment { slot, value } => {
                let Some(dom) = slot_doms.get(&slot.name) else {
                    return reference(slot.span, format!("unknown slot `{}`", slot.name));
                };
                if !dom.contains(&value.0) {
                    return reference(
                        value.1,
                        format!("value `{}` not in domain of slot `{}`", value.0, slot.name),
                    );
                }
                ShigurePartialRecordKind::SlotAssignment {
                    slot: slot.name.clone(),
                    value: value.0.clone(),
                }
            }
        };
        records.push(ShigurePartialRecord {
            id: rec.id.name.clone(),
            kind,
        });
    }

    let op_arities = op_sigs
        .into_iter()
        .map(|(k, (a, _))| (k, a.len()))
        .collect();
    let rel_arities = rel_sigs.into_iter().map(|(k, a)| (k, a.len())).collect();
    let slot_names = slot_sorts.into_keys().collect();
    Ok(CheckedFiniteBundle {
        finite: ShigureFinitePartial {
            sorts,
            operations,
            relations,
            slots,
            background_constraints,
            records,
            max_completions: raw.max_completions.unwrap_or(0),
        },
        op_arities,
        rel_arities,
        sorts: sort_elems,
        slots: slot_names,
    })
}

fn check_affine_partial<E: InputError>(
    raw: &RawAffinePartial,
    r_idx: usize,
    checker: &Checker<'_, E>,
    control: &Control,
) -> CResult<ShigureAffinePartial, E> {
    let coeff_domain = check_coeff_domain(&raw.domain, control)?;
    let coord_names = check_p4_unique_idents(&raw.coord_names, "coord", "`affine`")?;
    let n = coord_names.len();
    if raw.x0.len() != n {
        return p4_type_err(
            raw.span,
            format!("affine x0 length {} != {n}", raw.x0.len()),
        );
    }
    if raw.direction_t.len() != n {
        return p4_type_err(
            raw.span,
            format!("affine direction_t rows {} != {n}", raw.direction_t.len()),
        );
    }
    let ctx = CoordCheckCtx {
        coeff_domain: &coeff_domain,
        r_idx,
        checker,
        control,
    };
    let x0 = raw
        .x0
        .iter()
        .map(|v| check_member_coord_value(v, &ctx, raw.span))
        .collect::<CResult<Vec<_>, E>>()?;
    let t_cols = raw.direction_t.first().map_or(0, Vec::len);
    let mut direction_t = Vec::with_capacity(n);
    for row in &raw.direction_t {
        if row.len() != t_cols {
            return p4_type_err(
                raw.span,
                format!("affine direction_t row width {} != {t_cols}", row.len()),
            );
        }
        direction_t.push(
            row.iter()
                .map(|v| check_member_coord_value(v, &ctx, raw.span))
                .collect::<CResult<Vec<_>, E>>()?,
        );
    }
    let check_row_group =
        |rows: &[RawAffineRow], seen: &mut HashSet<String>| -> CResult<Vec<ShigureAffineRow>, E> {
            let mut out = Vec::with_capacity(rows.len());
            for row in rows {
                if !seen.insert(row.id.name.clone()) {
                    return duplicate(
                        row.id.span,
                        format!("duplicate affine row `{}`", row.id.name),
                    );
                }
                if row.coeffs.len() != n {
                    return p4_type_err(
                        row.span,
                        format!(
                            "affine row `{}` width {} != {n}",
                            row.id.name,
                            row.coeffs.len()
                        ),
                    );
                }
                let coeffs = row
                    .coeffs
                    .iter()
                    .map(|v| check_member_coord_value(v, &ctx, row.span))
                    .collect::<CResult<Vec<_>, E>>()?;
                let rhs = check_member_coord_value(&row.rhs, &ctx, row.span)?;
                out.push(ShigureAffineRow {
                    id: row.id.name.clone(),
                    coeffs,
                    rhs,
                    span: row.span,
                });
            }
            Ok(out)
        };
    let mut bg_rec_ids = HashSet::new();
    let background_rows = check_row_group(&raw.background_rows, &mut bg_rec_ids)?;
    let record_rows = check_row_group(&raw.record_rows, &mut bg_rec_ids)?;
    let mut eq_ids = HashSet::new();
    let eval_equations = check_row_group(&raw.eval_equations, &mut eq_ids)?;
    Ok(ShigureAffinePartial {
        coeff_domain,
        coord_names,
        x0,
        direction_t,
        background_rows,
        record_rows,
        eval_equations,
        span: raw.span,
    })
}

pub(super) fn check_partial<E: InputError>(
    raw: &RawPartialTask,
    r_idx: usize,
    reading_name: &str,
    checker: &Checker<'_, E>,
    control: &Control,
) -> CResult<ShigurePartialTask, E> {
    let context = format!("`shigure partial` `{}`", raw.name.name);
    let origins = check_p4_origins(&raw.origins, raw.span, &context)?;

    let (representation, op_arities, rel_arities, sorts, slots, allow_arbitrary_refs) = match &raw
        .representation
    {
        RawPartialRepresentation::FiniteTable(fin) => {
            let bundle = check_finite_partial(fin, r_idx, checker, control)?;
            (
                ShigurePartialRepresentation::FiniteTable(bundle.finite),
                bundle.op_arities,
                bundle.rel_arities,
                bundle.sorts,
                bundle.slots,
                false,
            )
        }
        RawPartialRepresentation::Affine(aff) => {
            if !raw.eval_laws.is_empty() {
                return p4_type_err(
                    raw.eval_laws[0].span,
                    "affine partial presentation must declare evaluation equations via `eval_eq` rather than `eval_law`",
                );
            }
            let checked_aff = check_affine_partial(aff, r_idx, checker, control)?;
            (
                ShigurePartialRepresentation::Affine(checked_aff),
                HashMap::new(),
                HashMap::new(),
                HashMap::new(),
                HashSet::new(),
                true,
            )
        }
        RawPartialRepresentation::UnsupportedClass { description, span } => {
            if description.trim().is_empty() {
                return p4_type_err(*span, "unsupported description must be non-empty");
            }
            (
                ShigurePartialRepresentation::UnsupportedClass {
                    description: description.clone(),
                },
                HashMap::new(),
                HashMap::new(),
                HashMap::new(),
                HashSet::new(),
                true,
            )
        }
    };

    let scope = FormulaCheckScope {
        op_arities: &op_arities,
        rel_arities: &rel_arities,
        sorts: &sorts,
        slots: &slots,
        allow_arbitrary_refs,
    };
    let mut seen_laws = HashSet::new();
    let mut eval_laws = Vec::with_capacity(raw.eval_laws.len());
    for law in &raw.eval_laws {
        if !seen_laws.insert(law.name.name.as_str()) {
            return duplicate(
                law.name.span,
                format!("duplicate eval_law `{}` in {context}", law.name.name),
            );
        }
        eval_laws.push(check_eval_law(law, &scope, control)?);
    }

    let quantifier_spec = match &raw.quantifier_spec {
        Some(q) => {
            let candidates = check_p4_unique_idents(&q.candidates, "candidate", "quantifier")?;
            let cand_set: HashSet<&str> = candidates.iter().map(String::as_str).collect();
            let mut comp_ids = HashSet::new();
            let mut completions = Vec::with_capacity(q.completions.len());
            for comp in &q.completions {
                if !comp_ids.insert(comp.id.name.as_str()) {
                    return duplicate(
                        comp.id.span,
                        format!("duplicate completion `{}`", comp.id.name),
                    );
                }
                let mut valid_candidates = Vec::with_capacity(comp.valid_candidates.len());
                for vc in &comp.valid_candidates {
                    if !cand_set.contains(vc.name.as_str()) {
                        return reference(
                            vc.span,
                            format!("unknown candidate `{}` in quantifier completion", vc.name),
                        );
                    }
                    valid_candidates.push(vc.name.clone());
                }
                let slot_values = comp
                    .slot_values
                    .iter()
                    .map(|(s, (v, _), _)| (s.name.clone(), v.clone()))
                    .collect();
                completions.push(ShigureQuantifierCompletion {
                    id: comp.id.name.clone(),
                    slot_values,
                    valid_candidates,
                    output_value: comp.output_value.0.clone(),
                });
            }
            Some(ShigureQuantifierSpec {
                candidates,
                completions,
                max_steps: q.max_steps.unwrap_or(0),
            })
        }
        None => None,
    };

    let open_domain = match &raw.open_domain {
        Some(od) => Some(check_open_domain(od, control)?),
        None => None,
    };

    Ok(ShigurePartialTask {
        name: full(reading_name, &[&raw.name.name]),
        reading: reading_name.to_owned(),
        origins,
        representation,
        eval_laws,
        quantifier_spec,
        open_domain,
        span: raw.span,
    })
}
